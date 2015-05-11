{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

-- | This module implements a renamer for graphs such that each binder
-- introduces a unique variable name.
--
-- The algorithm works as follows:
--
-- * By default, the new graph is created by traversing the expression from the
--   root and down, copying nodes from the original graph and renaming binders
--   (and corresponding variables) to be unique.
--
-- * An exception is made when visiting a node that has already been copied
--   under a compatible set of renamings. In that case, a reference to the
--   previous copy is used.
--
-- Without the exception, we would loose all sharing in the original graph (the
-- new graph would always be a tree). The exception makes sure that we retain
-- sharing where possible. However, it is generally not possible to retain all
-- sharing, since shared sub-trees may appear in contexts with incompatible
-- renamings (see e.g. example @g3@ in Paper.hs).

module Rename where



import Control.Monad.State
import Control.Monad.Writer
import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (traverse, Traversable)

import AG
import Dag.AG
import Dag.Internal
import Dag
import System.IO.Unsafe


type Name = String

data ExpF a  =  LitB' Bool   |  LitI' Int  |  Var' Name
             |  Eq' a a      |  Add' a a   |  If' a a a
             |  Iter' Name a a a
  deriving (Eq, Show, Functor, Foldable, Traversable)


data (f :&: ann) a = f a :&: ann
  deriving (Eq, Show, Functor)

getAnn :: (f :&: ann) a -> ann
getAnn (_ :&: ann) = ann

dropAnn :: (f :&: ann) a -> f a
dropAnn (f :&: _) = f

dropAnnFree :: Functor f => Free (f :&: ann) a -> Free f a
dropAnnFree (In f)  = In $ fmap dropAnnFree $ dropAnn f
dropAnnFree (Ret a) = Ret a

-- | Variable aliasing environment
type Aliases = [(Name,Name)]  -- [(oldName, newName)]

-- | Record of previously renamed nodes
type Memo = Map (Node,Aliases) Node

type VarId = Int

type St = (Node, VarId, Memo)

freshNode :: MonadState St m => m Node
freshNode = do
    (n,v,memo) <- get
    put (succ n, v, memo)
    return n

freshName :: MonadState St m => m Name
freshName = do
    (n,v,memo) <- get
    put (n, succ v, memo)
    return ('v' : show v)

getMemo :: MonadState St m => m Memo
getMemo = do
    (_,_,memo) <- get
    return memo

memorize :: MonadState St m => Node -> Aliases -> Node -> m ()
memorize n aliases n' = do
    (n_,v,memo) <- get
    put (n_, v, Map.insert (n,aliases) n' memo)

type Cxt f a = f (Free f a)

type Wr = IntMap (Cxt ExpF Node)

tellNode :: MonadWriter Wr m => Node -> Cxt ExpF Node -> m ()
tellNode n f = tell $ IntMap.singleton n f

tellVar :: MonadWriter Wr m => Name -> m ()
tellVar v = tell IntMap.empty

decorVarsM'
    :: Dag ExpF
    -> Free ExpF Node  -- ^ Current focus
    -> State
        (IntMap (Cxt (ExpF :&: Set Name) Node))
        (Free (ExpF :&: Set Name) Node, Set Name)
decorVarsM' g (In f) = do
    f' <- decorVarsM g f
    return (In f', getAnn f')
decorVarsM' g (Ret n) = do
    ns <- get
    case IntMap.lookup n ns of
        Just h -> return (Ret n, getAnn h)
        _ -> do
            let f = edges g IntMap.! n
            f' <- decorVarsM g f
            modify (IntMap.insert n f')
            return (Ret n, getAnn f')

decorVarsM
    :: Dag ExpF
    -> Cxt ExpF Node  -- ^ Current focus
    -> State
        (IntMap (Cxt (ExpF :&: Set Name) Node))
        (Cxt (ExpF :&: Set Name) Node)
decorVarsM g (Var' v) = return (Var' v :&: Set.singleton v)
decorVarsM g (Iter' v k i b) = do
    (k',kvs) <- decorVarsM' g k
    (i',ivs) <- decorVarsM' g i
    (b',bvs) <- decorVarsM' g b
    let vs = Set.unions [kvs, ivs, Set.delete v bvs]
    return (Iter' v k' i' b' :&: vs)
decorVarsM g f = do
    f' <- traverse (decorVarsM' g) f
    let vs = Set.unions . Foldable.toList $ fmap snd f'
    return (fmap fst f' :&: vs)

-- | Decorate each node with the set of free variables in the corresponding
-- sub-expression
decorVars :: Dag ExpF -> Dag (ExpF :&: Set Name)
decorVars g = g {root = r', edges = es'}
  where
    (r',es') = runState (decorVarsM g (root g)) IntMap.empty

renameM'
    :: Dag (ExpF :&: Set Name)
    -> Aliases
    -> Free (ExpF :&: Set Name) Node  -- ^ Current focus
    -> WriterT Wr (State St) (Free ExpF Node)
renameM' g aliases (In f)  = fmap In $ renameM g aliases f
renameM' g aliases (Ret n) = do
    let f = edges g IntMap.! n
        aliases' = [(v,v') | (v,v') <- aliases, v `Set.member` getAnn f]
    memo <- getMemo
    case Map.lookup (n,aliases') memo of
        Just n' -> return $ Ret n'
        Nothing -> do
            n' <- freshNode
            memorize n aliases' n'
            f' <- renameM g aliases' f
            tellNode n' f'
            return $ Ret n'

renameM
    :: Dag (ExpF :&: Set Name)
    -> Aliases
    -> Cxt (ExpF :&: Set Name) Node  -- ^ Current focus
    -> WriterT Wr (State St) (Cxt ExpF Node)
renameM g aliases (f :&: vs) = case f of
    Var' v -> case lookup v aliases of
        Just v' -> tellVar v' >> return (Var' v')
        _       -> tellVar v  >> return (Var' v)  -- Free variable
    Iter' v k i b -> do
        k' <- renameM' g aliases k
        i' <- renameM' g aliases i
        v' <- freshName
        b' <- renameM' g ((v,v'):aliases) b
        return $ Iter' v' k' i' b'
    _ -> traverse (renameM' g aliases) f

rename :: Dag ExpF -> Dag ExpF
rename g = g {root = r, edges = es, nodeCount = n}
  where
    g' = decorVars g
    ((r,es),(n,_,_))
        = flip runState (0,0,Map.empty)
        $ runWriterT
        $ renameM g' [] (root g')



--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

alphaEq' :: [(Name,Name)] -> Tree ExpF -> Tree ExpF -> Bool
alphaEq' env (In (Var' v1)) (In (Var' v2))
    | Just v <- lookup v1 env = v==v2
    | otherwise               = v1==v2
alphaEq' env (In (Iter' v1 k1 i1 b1)) (In (Iter' v2 k2 i2 b2)) =
    alphaEq' env k1 k2 && alphaEq' env i1 i2 && alphaEq' ((v1,v2):env) b1 b2
alphaEq' env (In (LitB' b1))     (In (LitB' b2))     = b1==b2
alphaEq' env (In (LitI' i1))     (In (LitI' i2))     = i1==i2
alphaEq' env (In (Eq' a1 b1))    (In (Eq' a2 b2))    = alphaEq' env a1 a2 && alphaEq' env b1 b2
alphaEq' env (In (Add' a1 b1))   (In (Add' a2 b2))   = alphaEq' env a1 a2 && alphaEq' env b1 b2
alphaEq' env (In (If' c1 t1 f1)) (In (If' c2 t2 f2)) = alphaEq' env c1 c2 && alphaEq' env t1 t2 && alphaEq' env f1 f2
alphaEq' env _ _ = False

-- | Alpha-equivalence
alphaEq :: Tree ExpF -> Tree ExpF -> Bool
alphaEq = alphaEq' []

-- | Like 'flatten' but adds the root as a node in the graph
flatten' :: Traversable f => Dag f -> (Node, IntMap (f Node), Int)
flatten' d = (n, IntMap.insert n f m, n+1)
  where
    (f,m,n) = flatten d

-- | List the variable occurrences along with their scopes. Each variable in the
-- scope is paired with the node at which it is bound.
scope :: Dag ExpF -> [(Name,Node)] -> [(Name, [(Name,Node)])]
scope g env = go env r
  where
    (r,es,_) = flatten' g

    go env n = case es IntMap.! n of
      Var' v -> [(v,env)]
      Iter' v k i b
          -> go env k
          ++ go env i
          ++ go ((v,n):[vn | vn <- env, fst vn /= v]) b
      f -> concat $ Foldable.toList $ fmap (go env) f

groups :: Ord k => [(k,a)] -> [[a]]
groups ks = Map.elems $ Map.fromListWith (++) [(k,[a]) | (k,a) <- ks]

allEq :: Eq a => [a] -> Bool
allEq []     = True
allEq (a:as) = all (==a) as

-- | Check that no single name is paired with two different nodes
checkVar :: [(Name,Node)] -> Bool
checkVar = all allEq . groups

-- | Check for well-scopedness according to the paper
isWellScoped :: Dag ExpF -> Bool
isWellScoped g = all checkVar $ fmap concat $ groups sc
  where
    sc = scope g []

prop_rename1 g = unravelDag g `alphaEq` unravelDag (rename g)

prop_rename2 g = length (IntMap.toList $ edges g) <= length (IntMap.toList $ edges $ rename g)

prop_rename3 g = isWellScoped $ rename g

main = if ok then putStrLn "All tests passed" else putStrLn "Failed"
  where
    gs = [g1,g2,g3]
    ok = all prop_rename1 gs
      && all prop_rename2 gs
      && all prop_rename3 gs


iIter n x y z = In (Iter' n x y z)
iAdd x y      = In (Add' x y)
iVar x        = In (Var' x)
iLitI l       = In (LitI' l)
iLitB l       = In (LitB' l)


gt1 :: Tree ExpF
gt1 = iIter "x" x x (iAdd (iIter "y" z z (iAdd z y)) y)
    where x = iLitI 10
          y = iVar "x"
          z = iLitI 5

g1 :: Dag ExpF
g1 = unsafePerformIO $ reifyDag gt1


gt2 :: Tree ExpF
gt2 = iIter "x" x (iIter "x" x x y) y
    where x = iLitI 0
          y = iVar "x"

g2 :: Dag ExpF
g2 = unsafePerformIO $ reifyDag gt2


gt3 :: Tree ExpF
gt3 = iAdd (iIter "x" x x z) (iIter "x" y y z)
    where x = iLitI 10
          y = iLitB False
          z = iVar "x"

g3 :: Dag ExpF
g3 = unsafePerformIO $ reifyDag gt3

