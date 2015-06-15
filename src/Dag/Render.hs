{-# LANGUAGE TypeOperators #-}

module Dag.Render where



import Control.Monad.State
import qualified Data.Foldable as Foldable
import Data.IntMap

import Tree
import Dag.Internal
import Dot



numberNodesFree :: Traversable f
    => Maybe Int  -- ^ Optional number for the root
    -> Free f a
    -> State Int (Free (f :&: Int) a)
numberNodesFree _ (Ret a) = return $ Ret a
numberNodesFree k (In f)  = do
    n <- case k of
            Just k' -> return k'
            _       -> do
                k' <- get; put (k'+1)
                return k'
    f' <- traverse (numberNodesFree Nothing) f
    return $ In (f' :&: n)

numberNodes :: Traversable f => Dag f -> Dag (f :&: Int)
numberNodes (Dag r es n) = flip evalState n $ do
    r'  <- (fmap out . numberNodesFree Nothing . In) r
    es' <- traverseWithKey (\k -> fmap out . numberNodesFree (Just k) . In) es
    return $ Dag r' es' n
  where
    out (In f) = f

class ShowConstr f where
    showConstr :: f a -> String

arity :: Foldable f => f a -> Int
arity = length . Foldable.toList

nodeToGraph' :: (ShowConstr f, Functor f, Foldable f) =>
    Free (f :&: Int) Node -> ExpGraph
nodeToGraph' (Ret _) = []
nodeToGraph' (In f)  = nodeToGraph "white" f

nodeToGraph :: (ShowConstr f, Functor f, Foldable f) =>
    Color -> (f :&: Int) (Free (f :&: Int) Node) -> ExpGraph
nodeToGraph col (f :&: x) = concat
    $  [node x (showConstr f) col (arity f)]
    ++ [mkEdge x i inp | (i,inp) <- [0..] `zip` Foldable.toList f]
    ++ [Foldable.fold $ fmap nodeToGraph' f]
  where
    mkEdge x inp (Ret a)        = edge x inp a
    mkEdge x inp (In (_ :&: y)) = edge x inp y

dagToGraph :: (ShowConstr f, Traversable f) => Dag f -> ExpGraph
dagToGraph dag = concat $
    [nodeToGraph "lightgrey" $ root dag']
      ++
    [nodeToGraph "lightgrey" f | (n,f) <- assocs $ edges dag']
  where
    dag' = numberNodes dag

renderDag :: (ShowConstr f, Traversable f) => Dag f -> FilePath -> IO ()
renderDag dag file = renderGraph (dagToGraph dag) file

