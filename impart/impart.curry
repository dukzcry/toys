-- written by A. V. Lukyanov <lomka@gero.in>

import CLPFD
import qualified CLPR
import AllSolutions
import GraphInductive
import Unsafe
import Random
import GUI
import Float
import Maybe
import Function

gen_vars n = if n==0 then [] else var : gen_vars (n-1)  where var free

data edge_ = a | b | c | d | tvs

-- rule-o-rama
junc 1 e = case e of
  a -> a
  b -> b
  c -> c
  d -> d
junc 2 e = case e of
  a -> b
  b -> a
  c -> d
  d -> c
junc 3 e = case e of
  a -> b
  b -> d
  c -> a
  d -> c
junc 4 e = case e of
  a -> c
  b -> a
  c -> d
  d -> b
junc 5 e = case e of
  a -> c
  b -> d
  c -> a
  d -> b
junc 6 e = case e of
  a -> a
  b -> c
  c -> b
  d -> d

pat [a,b,c,d] = success
pat [d,c,b,a] = success
pat [b,d,a,c] = success
pat [c,a,d,b] = success
--pat [c,d,a,b] = success

TE e j f o
	     | (e == a || e == b) && (j == 3 || j == 5) = case e of
	       a -> f c o
	       b -> f d o
	     | (e == a || e == c) && j /= 3 && j /= 5 = case e of
	       a -> f b o
	       c -> f d o
	     | otherwise = o

hide t e
     | t == 2 || t == 5 = case e of
       b -> c
       c -> b
     | otherwise = case e of
       b -> b
       c -> c
--

hiddenedge = [b,c] !! head (take 1 (nextIntRange (unsafePerformIO getRandomSeed) 2))

-- generate random junction set that matches known pattern
juncset n = let
       l = unsafePerformIO (getAllSolutions juncset_)
       juncset_ o =
   	   jl =:= gen_vars n & domain jl 1 6 & labeling [] jl &
 	   o_ =:= map (\ junctype -> \ E -> junc junctype E) jl & jc =:= foldl1 (flip (.)) o_ & pat (map jc [a,b,c,d]) &
	   o =:= zipWith (\ jf junctype -> (jf,junctype)) o_ jl
           where jl,jc,o_ free
   in l !! head (take 1 (nextIntRange (unsafePerformIO getRandomSeed) (length l)))

-- produce equations for Es lines from generating lines
Es [[x1,y1],[x2,y2]] =
   let αβ = [2,10]
       A = y1 -. y2
       B = x2 -. x1
       C = x1*.y2 -. x2*.y1
       y C_ = \ x -> (negateFloat A CLPR.*.x CLPR.-. C_) CLPR./. B
       eq C_ = \ yf x -> A CLPR.*.x CLPR.+. B CLPR.*.(yf x) CLPR.+. C_ =:= 0
       z1 = sqrt (A^.2 +. B^.2)
       Cs d_ =
   	   let z = d_ *. z1
   	   in map (\ C_ -> (y C_,eq C_)) [C +. z, C -. z]
   in zipWith (\ edge Ei -> (edge,Ei)) [b,c,a,d] (concatMap Cs αβ)

-- solve equations to get coordinates of the corners
cross (y,_) (_,eq) = let
      	    x = fromJust (unsafePerformIO (getOneSolution (eq y))) 
      in both round (x,y x) -- direct calc of y produces suspended constraints as side effect

main = runGUI "" main_
main_ = let
      	-- todo error or support x = 0 | y = 0
	BPs = [[[-100,-90],[-70,110]],[[-70,110],[110,-100]],[[110,-100],[-100,-90]]]

     	n = length BPs
	ns = [1..n]
	ns1 = concatMap (\ n_ -> take 4 (repeat n_)) ns
	edges_ = [if i == n then (n,1,j) else (i,i+1,j) | (i,j) <- zip ns1 (concatMap Es BPs)]
	-- make a bar graph, all Es are linked to the same nodes, nodes hold junctions
     	bargraph = mkGraph (zip ns (juncset n)) []
	bargraph1 = mkGraph (map (\ n_ -> (n_,((0,0),0))) ns) edges_ -- no interest to play type games
	filteredge e l = filter (\ (_,_,(edge,_)) -> edge == e) l
	JG (_,v,(jf,junctype),_) (g,corners) =
	   let il = inn g v
	       ol = out g v
	       knot (g1,corner) (ifrom,_,iEi@(iedge,E1)) = let
	       	      oedge = jf iedge
		      [n2] = newNodes 1 g1
	       	      [(_,oto,oEi@(_,E2))] = filteredge oedge ol
		      f1 = insNode (n2,(cross E1 E2,junctype))
		      f2 = insEdges [(ifrom,n2,iEi),(n2,oto,oEi)]
	       	    in (f2 (f1 g1),n2 : corner)
	       (g2,corner1) = foldl knot (g,[]) il
	       -- leaf arcs are removed automatically
	       g4 = delNode v g2
	       corner2 = concatMap (\ v1 -> inn g4 v1) corner1
	       TE_ edge from = let
	       		     [(_,to,(_,E))] = filteredge edge corner2
			    in insEdge (from,to,(tvs,E))
	       -- transversal edges are added within each corner
	       g3 = foldl (\ g5 (_,from,(edge,_)) -> TE edge junctype (\ e -> TE_ e from) g5) g4 corner2
	      in trace (show junctype) (g3,(junctype,corner1) : corners)
	-- make a closed figure graph from bar graph by arcs relinking in accordance with junctions
	(Cg,corners1) = ufold JG (bargraph1,[]) bargraph
	HE (g6,e1) (junctype,corners)
	   | (junctype == 1 || junctype == 6) =
	     (delNode ito g6,junc junctype e1)
	   | otherwise = let
				h = hide junctype e1
				outs = concatMap (\ v1 -> out Cg v1) corners
				[(ofrom,oto,_)] = filteredge h outs
				[(_,to3,_)] = filteredge a ins
				[(tfrom,tto,_)] = filteredge tvs (out Cg to3)
	     	       	 in (delEdges [(ifrom,ito),(ofrom,oto),(tfrom,tto)] g6,h)
	   where ins = concatMap (\ v1 -> inn Cg v1) corners
	   	 [(ifrom,ito,_)] = filteredge e1 ins
	-- remove invisible edges based on randomly picked b | c edge
	(Cg1,_) = foldl HE (Cg,hiddenedge) (reverse corners1) -- most evil thing, dirs of arcs and traverse should match to close a belt
	Es1 node (cross1_,_) = case node of
      	    [(_,v1)] -> [([(cross1_,fst (fromJust (lab Cg v1)))],v1)]
	    [(_,v1),(_,v2)] -> [([(cross1_,fst (fromJust (lab Cg v1)))],v1),([(cross1_,fst (fromJust (lab Cg v2)))],v2)]
      	    [] -> []
	    x -> error (show x)
	-- assign Es segments to arcs
	Cg2 = gmap (\ (p,v,cross1,s) -> (Es1 p cross1,v,cross1,Es1 s cross1)) Cg1 --Cg
	draw ((x1,y1),(x2,y2)) gport = do
	     addCanvas cref [CLine [(x1+200,y1+200),(x2+200,y2+200)] ""] gport
	forlabs (_,_,l) gport = do
		 mapIO_ (\ ln -> (draw ln gport)) l
	forarcs gport = do
	     mapIO_ (\ arc -> forlabs arc gport) (labEdges Cg2)
     in Col [] [Canvas [WRef cref, Height 400, Width 400],
       	      Button forarcs [Text "draw"]]
	      where cref free
