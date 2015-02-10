-- Written by A. V. Lukyanov <lomka@gero.in>

--import CLPFD
import qualified CLPR
import Float
import AllSolutions
import GraphInductive
import Random
import GUI
import Function (both)
import List
import Unsafe
import Maybe

invalid = 0

rand m n = take n (nextIntRange (unsafePerformIO getRandomSeed) m)

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
excess t e
       | t == 2 || t == 3 =
       	 e == c
       | otherwise =
       	 e == b
--

hiddenedge = [b,c] !! head (rand 2 1)

-- generate random junction set that matches known pattern
juncset n = let
       l = unsafePerformIO (getOneSolution juncset_) --getAllSolutions
       juncset_ o =
   	   --jl =:= gen_vars n & domain jl 1 6 & labeling [] jl &
	   jl =:= map (+1) (rand 5 n) &
 	   o_ =:= map (\ junctype -> \ E -> junc junctype E) jl & jc =:= foldl1 (flip (.)) o_ & pat (map jc [a,b,c,d]) &
	   o =:= zipWith (\ jf junctype -> (jf,junctype)) o_ jl
           where jl,jc,o_ free
   in if isJust l then fromJust l else juncset n --!! head (take 1 (nextIntRange (unsafePerformIO getRandomSeed) (length l)))

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

main = runGUI "impart" main_
main_ = let
      	-- todo error or support lines x = 0 | y = 0
	BPs1 = [[[-100,-90],[-70,110]],[[-70,110],[110,-100]],[[110,-100],[-100,-90]]] --triangle
	--BPs = [[[-70,80],[-40,100]],[[-40,100],[70,80]],[[70,80],[0,0]],[[0,0],[70,-50]],[[70,-50],[-60,-80]],[[-60,-80],[-70,80]]] --escher
	BPs2 = [[[-100,0],[-70,80]],[[-70,80],[0,110]],[[0,110],[70,80]],[[70,80],[110,0]], --octagon
		[[110,0],[70,-80]],[[70,-80],[0,-100]],[[0,-100],[-70,-80]],[[-70,-80],[-100,0]]]
	BPs_ = [BPs1,BPs2]
	BPs = BPs_ !! head (rand (length BPs_) 1)

     	n = length BPs
	ns = [1..n]
	ns1 = concatMap (\ n_ -> take 4 (repeat n_)) ns
	edges_ = [if i == n then (n,1,j) else (i,i+1,j) | (i,j) <- zip ns1 (concatMap Es BPs)]
	-- make a closed bar graph, all Es are linked to the same nodes, nodes hold junctions
     	bargraph = mkGraph (zip ns (juncset n)) []
	bargraph1 = mkGraph (map (\ n_ -> (n_,((invalid,invalid),invalid))) ns) edges_ -- no interest to play type games
	filteredge e = filter (\ (_,_,(edge,_)) -> edge == e)
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
	       ins = concatMap (\ v1 -> inn g4 v1) corner1
	       TE_ edge from = let
	       		     [(_,to,(_,invalid_))] = filteredge edge ins
			    in insEdge (from,to,(tvs,invalid_))
	       -- transversal edges are added within each corner
	       g3 = foldl (\ g5 (_,from,(edge,_)) -> TE edge junctype (\ e -> TE_ e from) g5) g4 ins
	      in (g3,(junctype,v,corner1) : corners)
	-- make a figure graph from bar graph by arcs relinking in accordance with junctions
	(Cg,corners1) = ufold JG (bargraph1,[]) bargraph
	HE (g6,g7,e1,insl,outsl) (junctype,_,corner)
	   | (junctype == 1 || junctype == 6) =
	     trace (show junctype) (delNode ito g6,delNode ito g7,junc junctype e1,ins : insl,outs : outsl)
	   | otherwise = let
				h = hide junctype e1
				--[(ofrom,oto,_)] = filteredge h outs
				[(from,to,_)] = filteredge a ins
				[(from1,to1,_)] = filteredge a outs
				[(tfrom,tto,_)] = filteredge tvs (out Cg to)
				f1 = delEdges [(ifrom,ito){-,(ofrom,oto)-},(tfrom,tto)]
				-- remove edge with excess parts
				f2 = delEdge (if (excess junctype h) then (from1,to1) else (from,to))
	     	       	 in trace (show junctype) (f2 (f1 g6),f1 g7,h,ins : insl, outs : outsl)
	   where ins = concatMap (\ v1 -> inn Cg v1) corner
	   	 outs = concatMap (\ v1 -> out Cg v1) corner
	   	 [(ifrom,ito,_)] = filteredge e1 ins
	-- remove invisible edges based on randomly picked b or c edge
	(Cg3,Cg4,_,insl1,outsl1) = foldl HE (Cg,Cg,hiddenedge,[],[])
				 -- consistence is a must for HE to make it's work properly
				 (sortBy (\ (_,v1,_) (_,v2,_) -> v1 < v2) corners1)
	filterneigh compare l = filteredge a (head (filter (\ es -> any compare es) l))
	fin to = E where [(_,_,(_,E))] = filterneigh (\ (from,_,_) -> from == to) outsl1
	fout from = E where [(_,_,(_,E))] = filterneigh (\ (_,to,_) -> to == from) insl1
	EE g (from,to,Ei@(_,E1)) =
	   let
		matchedges e = case e of
			([],[]) -> fixedges (fout from) (fin to) -- an edge with both parts being excess is the reason of all complication
			([],_) -> fixedge (fout from) True
			(_,[]) -> fixedge (fin to) False
		fixedge E2 todir =
			let
				[n1] = newNodes 1 g
				f1 = insNode (n1,(cross E1 E2,invalid))
				f2 = insEdge (if todir then (n1,to,Ei) else (from,n1,Ei))
			in f2 (f1 g)
		fixedges E2 E3 =
			 let
				[n1,n2] = newNodes 2 g
				f1 = insNodes [(n1,(cross E1 E2,invalid)),(n2,(cross E1 E3,invalid))]
				f2 = insEdge (n1,n2,Ei)
			 in f2 (f1 g)
	   -- sides of edge not connected with other edges are excess and should be recalced
	   in matchedges (inn g from,out g to)
	-- cut excess parts
	Cg1 = foldl EE Cg3 ((labEdges Cg4) \\ (labEdges Cg3))
	Cg5 = Cg1 --Cg
	Es1 node (cross1_,_) = case node of
      	    [(_,v1)] -> [([(cross1_,fst (fromJust (lab Cg5 v1)))],v1)]
	    [(_,v1),(_,v2)] -> [([(cross1_,fst (fromJust (lab Cg5 v1)))],v1),([(cross1_,fst (fromJust (lab Cg5 v2)))],v2)]
      	    [] -> []
	    x -> error (show x)
	-- assign Es segments to arcs
	Cg2 = gmap (\ (p,v,cross1,s) -> (Es1 p cross1,v,cross1,Es1 s cross1)) Cg5
	draw ((x1,y1),(x2,y2)) gport = do
	     addCanvas cref [CLine [(x1+200,y1+200),(x2+200,y2+200)] ""] gport
	forlabs (_,_,l) gport = do
		 mapIO_ (\ ln -> (draw ln gport)) l
	forarcs gport = do
	     mapIO_ (\ arc -> forlabs arc gport) (labEdges Cg2)
     in Col [] [Canvas [WRef cref, Height 400, Width 400],
       	      Button forarcs [Text "draw"]]
	      where cref free
