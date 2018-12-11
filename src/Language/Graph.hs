module Language.Graph where

import           Prelude

data Graph a = Graph { vertices :: [a], edges :: [(a, a)] } deriving Show

removeEdge :: (Eq a) => (a, a) -> Graph a -> Graph a
removeEdge x (Graph v e) = Graph v (filter (/=x) e)

connections :: (Eq a) => ((a, a) -> a) -> a -> Graph a -> [(a, a)]
connections f0 x (Graph _ e) = filter ((==x) . f0) e

outbound :: Eq b => b -> Graph b -> [(b, b)]
outbound = connections fst

inbound :: Eq a => a -> Graph a -> [(a, a)]
inbound = connections snd

-- | Topological sort.
tsort :: (Eq a) => Graph a -> Either String [a]
tsort graph  = tsort' [] (noInbound graph) graph
  where
    noInbound (Graph v e) = filter (flip notElem $ fmap snd e) v
    tsort' l []    (Graph _ []) = pure $ reverse l
    tsort' _ []    _            = Left "There is at least one cycle in the graph."
    tsort' l (n:s) g            = tsort' (n:l) s' g'
      where
        outEdges = outbound n g
        outNodes = snd <$> outEdges
        g'       = foldr removeEdge g outEdges
        s'       = s ++ filter (null . flip inbound g') outNodes
