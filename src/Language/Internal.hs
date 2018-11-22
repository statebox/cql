{-# LANGUAGE ViewPatterns
           , FlexibleContexts
           , FlexibleInstances
           , TypeFamilies
           , UndecidableInstances
           , MultiParamTypeClasses
           , FunctionalDependencies
#-}
module Language.Internal where

import           Prelude hiding (any)

import           Control.Arrow
import           Control.Monad
import           Control.Monad.Trans.UnionFind (Point,UnionFindT,fresh)
import qualified Control.Monad.Trans.UnionFind as U

import           Data.Ord
import qualified Data.List as L
--import           Data.Sequence (Seq)
import           Data.Maybe (fromJust)
import           Data.Map (Map)
import           Data.Foldable (traverse_)
import           Data.Traversable (traverse)
import           Data.Graph.Inductive hiding (Graph)


newtype Conjunctions t = Conjunction [Equation t]
data Equation t =  Equal (Term t) (Term t)
              | NotEqual (Term t) (Term t)
data Term t = Function t [(Term t)]
  deriving (Eq, Ord)

data Satisfiability t = Satisfiable (Model t) | Unsatisfiable
  deriving (Show, Eq)

type Model t = Map (Term t) (Term t)

(===) :: Term t -> Term t -> Equation t
(===) = Equal
infix 4 ===

(=/=) :: Term t -> Term t -> Equation t
(=/=) = NotEqual
infix 4 =/=

instance Show t => Show (Term t) where
  show (Function sym childs) =
    show sym ++ "(" ++ concat (L.intersperse "," (map show childs)) ++ ")"

class Conjunction t a | a -> t where
  (/\) :: Equation t -> a -> Conjunctions t
  infixr 3 /\

instance (Conjunction t (Equation t)) where
  (/\) e1 e2 = Conjunction [e1, e2]

instance Conjunction t (Conjunctions t) where
  (/\) e1 (Conjunction e2) = Conjunction (e1:e2)

newtype Graph t = Graph (NodeMap (Term t), Gr (t, Point (LNode t)) Int)
newtype Vert  t = Vert  (LNode (t, Point (LNode t)))

interleave :: [(a,a)] -> [a]
interleave ((x,y):rest) = x : y : interleave rest
interleave []           = []

termGraph :: (Functor m, Monad m, Ord t) => [Equation t] -> UnionFindT (LNode t) m (Graph t)
termGraph = termGraph' . interleave . terms

termGraph' :: (Functor m, Monad m, Ord t) => [Term t] -> UnionFindT (LNode t) m (Graph t)
termGraph' ts = do
  let (nodeMap, gr) = snd $ run empty $ traverse_ insertTerm ts
  vars <- traverse genVars (labNodes gr)
  return $ Graph (nodeMap, mkGraph vars (labEdges gr))
  where
    insertTerm :: Ord t => Term t -> NodeMapM (Term t) Int Gr ()
    insertTerm term@(Function name childs) = do
      insMapNodeM term
      forM_ (zip childs [1..]) $ \(child,i) -> do
        insMapNodeM child
        insMapEdgeM (term,child,i)
        insertTerm child

    genVars (node, Function name _) = do
      var <- fresh (node,name)
      return (node,(name,var))

vertex :: Ord t => Graph t -> Term t -> Vert t
vertex gr@(Graph (nodeMap,_)) term =
  let (node,_) = mkNode_ nodeMap term
  in label gr node

graph :: Graph t -> Gr (t, Point (LNode t)) Int
graph (Graph (_, gr)) = gr

vertices :: Graph t -> [Vert t]
vertices = map Vert . labNodes . graph

outDegree :: Graph t -> Vert t -> Int
outDegree (graph -> gr) (Vert (x, _)) = outdeg gr x

label :: Graph t -> Node -> Vert t
label (graph -> gr) a = Vert (a, fromJust (lab gr a))

equivalent :: (Functor m, Monad m) => Vert t -> Vert t -> UnionFindT (LNode t) m Bool
equivalent (Vert (_,(_,x))) (Vert (_,(_,y))) = U.equivalent x y

union :: (Functor m, Monad m) => Vert t -> Vert t -> UnionFindT (LNode t) m ()
union (Vert (_,(_,x))) (Vert (_,(_,y))) = U.union x y

predecessors :: Graph t -> Vert t -> [Vert t]
predecessors gr (Vert (x,_)) = label gr <$> pre (graph gr) x

successors :: Graph t -> Vert t -> [Vert t]
successors gr (Vert (x,_)) = label gr <$> suc (graph gr) x

terms :: [Equation t] -> [((Term t), (Term t))]
terms = map go
  where
    go e = case e of
      Equal    t1 t2 -> (t1,t2)
      NotEqual t1 t2 -> (t1,t2)

term :: Graph t -> Vert t -> Term t
term (Graph (_,gr)) (Vert (n,_)) = go gr n
  where
    go :: Gr (t, a) Int -> Node -> Term t
    go gr n =
      case match n gr of
        (Nothing,_) -> error "context is Nothing"
        (Just (_,_,(sym,_),out),gr') ->
          Function sym $ map (go gr') $ sortEdges out
    sortEdges out = map snd $ L.sortBy (comparing fst) out

partition :: Ord t => Graph t -> (Equation t -> Bool) -> [Equation t] -> ([(Vert t,Vert t)],[(Vert t,Vert t)])
partition gr f equations =
  let (as,bs) = L.partition f equations
  in (map (vertex gr *** vertex gr) $ terms as, map (vertex gr *** vertex gr) $ terms bs)

unless :: Monad m => m Bool -> m () -> m ()
unless mbool m = do
  b <- mbool
  if b
    then return ()
    else m

instance Show t => Show (Vert t) where
  show (Vert (n, _)) = show n

positive :: Equation t -> Bool
positive t =
  case t of
    Equal _ _    -> True
    NotEqual _ _ -> False

any :: Monad m => (a -> b -> m Bool) -> [(a,b)] -> m Bool
any _ [] = return False
any f ((a,b):abs) = do
  r <- f a b
  if r
    then return True
    else any f abs
