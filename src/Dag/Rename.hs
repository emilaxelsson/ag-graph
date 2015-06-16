{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

module Dag.Rename where



import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Foldable as Foldable
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Variables
import Dag.Internal
import Dag.AG



-- | Variable aliasing environment
type Aliases v = [(v,v)]  -- [(oldName, newName)]

-- | Record of previously renamed nodes
type Memo v = Map (Node, Aliases v) Node

type St v = (Node, Integer, Memo v)

freshNode :: MonadState (St v) m => m Node
freshNode = do
    (n,v,memo) <- get
    put (succ n, v, memo)
    return n

freshName :: (IsVar v, MonadState (St v) m) => m v
freshName = do
    (n,v,memo) <- get
    put (n, succ v, memo)
    return (newVar v)

getMemo :: MonadState (St v) m => m (Memo v)
getMemo = do
    (_,_,memo) <- get
    return memo

memorize :: (MonadState (St v) m, Ord v) => Node -> Aliases v -> Node -> m ()
memorize n aliases n' = do
    (n_,v,memo) <- get
    put (n_, v, Map.insert (n,aliases) n' memo)

type Cxt f a = f (Free f a)

type Wr f = IntMap (Cxt f Node)

tellNode :: MonadWriter (Wr f) m => Node -> Cxt f Node -> m ()
tellNode n f = tell $ IntMap.singleton n f

tellVar :: MonadWriter (Wr f) m => v -> m ()
tellVar v = tell IntMap.empty  -- TODO What!!??

decorVarsM'
    :: (HasVars f v, Traversable f, Ord v)
    => Dag f
    -> Free f Node  -- ^ Current focus
    -> State
        (IntMap (Cxt (f :&: Set v) Node))
        (Free (f :&: Set v) Node, Set v)
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
    :: (HasVars f v, Traversable f, Ord v)
    => Dag f
    -> Cxt f Node  -- ^ Current focus
    -> State
        (IntMap (Cxt (f :&: Set v) Node))
        (Cxt (f :&: Set v) Node)
decorVarsM _ var
    | Just v <- isVar var = return (mkVar v :&: Set.singleton v)
decorVarsM g f = do
    f' <- traverse (decorVarsM' g) f
    let vs = Set.unions
               [delVar i vs | Numbered i (_,vs) <- Foldable.toList $ number f']
    return (fmap fst f' :&: vs)
  where
    delVar i vs
        = Set.difference vs
        $ lookupNumMap Set.empty i
        $ bindsVars
        $ number f

-- | Decorate each node with the set of free variables in the corresponding
-- sub-expression
decorVars :: (HasVars f v, Traversable f, Ord v) => Dag f -> Dag (f :&: Set v)
decorVars g = g {root = r', edges = es'}
  where
    (r',es') = runState (decorVarsM g (root g)) IntMap.empty

renameM'
    :: (HasVars f v, Traversable f, Ord v)
    => Dag (f :&: Set v)
    -> Aliases v
    -> Free (f :&: Set v) Node  -- ^ Current focus
    -> WriterT (Wr f) (State (St v)) (Free f Node)
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
    :: forall f v
    .  (HasVars f v, Traversable f, Ord v)
    => Dag (f :&: Set v)
    -> Aliases v
    -> Cxt (f :&: Set v) Node  -- ^ Current focus
    -> WriterT (Wr f) (State (St v)) (Cxt f Node)
renameM g aliases (f :&: vs)
    | Just v <- isVar f = case lookup v aliases of
        Just v' -> tellVar v' >> return (mkVar v')
        _       -> tellVar v  >> return (mkVar v)  -- Free variable
renameM g aliases (f :&: vs) =
    fmap renameVars $ traverse renameGeneric $ number f
  where
    renameGeneric (Numbered i t) = do
        let vs = Set.toList $ lookupNumMap Set.empty i $ bindsVars $ number f
        vs' <- sequence [freshName | _ <- vs]
        t'  <- renameM' g (zip vs vs' ++ aliases) t
        return (t', Set.fromList vs')

rename :: forall proxy f v . (HasVars f v, Traversable f, Ord v) => proxy v -> Dag f -> Dag f
rename _ g = g {root = r, edges = es, nodeCount = n}
  where
    g' :: Dag (f :&: Set v) = decorVars g
    ((r,es),(n,_,_))
        = flip runState (0,0,Map.empty)
        $ runWriterT
        $ renameM g' [] (root g')

