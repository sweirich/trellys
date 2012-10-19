
module SCC where


import Lib.DepthFirstSearch
import Data.List(findIndex,union,(\\),nub,partition)
 

topSort :: (Show a,Eq a) => (d -> [a]) -> [(a,d)] -> [[(a,d)]]
topSort depends pairs = topSortP (==) depends pairs

topSortP :: Show a => (a -> p -> Bool) -> (d -> [a]) -> [(p,d)] -> [[(p,d)]]
topSortP exports depends pairs = map (map f) groups
  where zs = zipWith g pairs [0..]   -- [(("even",0,d1),(("odd"),1,d2),...]   
        g (p,d) n = (p,n,depends d)
        -- getindex "odd" ---> 1
        getindex [] s = []
        getindex ((p,n,_):xs) s = if exports s p then n:getindex xs s else getindex xs s
        edges1 = concat[ map (\ e -> (n,e)) es | (a,n,ws) <- zs, es <- map (getindex zs) ws ]
        groups = scc2 (buildG (0,length pairs -1) edges1)
        f n = pairs !! n  -- f 1 ---> (("odd"),d2)


topSortQ :: (Eq a, Show a) => (b -> [a]) -> (b -> [a]) -> [b] -> [[b]]
topSortQ definef dependf items = map (map f) (topSortS definef dependf items)
  where f (x,_,_) = x

topSortS :: Eq a => (t -> [a]) -> (t -> [a]) -> [t] -> [[(t, [a], [a])]]
topSortS exports depends pairs = map (map f) groups
  where zs = zipWith g pairs [0..]   -- [(("even",0,d1),(("odd"),1,d2),...]   
        g d n = (exports d,n,depends d)
        -- getindex "odd" ---> [1]
        getindex [] s = []
        getindex ((exs,n,_):xs) s = if elem s exs then n:getindex xs s else getindex xs s
        edges1 = concat[ map (\ e -> (n,e)) es | (a,n,ws) <- zs, es <- map (getindex zs) ws ]
        groups = scc2 (buildG (0,length pairs -1) edges1)
        -- f n = pairs !! n  -- f 1 ---> (("odd"),d2)
        f n = (pairs !! n,defines,depends) where (defines,_,depends) = zs !! n

topSortR :: (Eq a, Show a) => (b -> ([a],[a])) -> [b] -> ([[b]],[([a],[a])])
topSortR deps bs = (map (map f) groups,map project zs)
  where zs = zipWith g bs [0..]   
        g d n = let (exports,depends) = deps d in (exports,n,depends)
        -- getindex "odd" ---> 1
        getindex [] s = []
        -- getindex ((exs,n,_):xs) s = if elem s exs then [n] else getindex xs s
        getindex ((exs,n,_):xs) s = if elem s exs then n:getindex xs s else getindex xs s
        edges1 = concat[ map (\ e -> (n,e)) es | (a,n,ws) <- zs, es <- map (getindex zs) ws ]
        groups = scc2 (buildG (0,length bs -1) edges1)
        f n = bs !! n  -- f 1 ---> (("odd"),d2)
        project (exs,n,deps) = (exs,deps)



pairs :: [(String,Int)]
pairs = [("odd",1),("even",2),("id",3),("map",4),("fold",5)]

depends :: Int -> [String]
depends 1 = ["even","lib"]
depends 2 = ["odd","id"]
depends 3 = []
depends 4 = ["lib"]
depends 5 = ["map"]

ans = topSort depends pairs

exports (s,n) = [s]

ans2 = topSortQ exports (depends . snd) pairs
ans3 = topSortS exports (depends . snd) pairs
