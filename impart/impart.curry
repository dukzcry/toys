-- Written by A. V. Lukyanov <lomka@gero.in>

import CLPFD
import qualified CLPR
import Float
import Integer
import AllSolutions
import GraphInductive
import Random
import GUI
import Function
import List
import Unsafe
import Maybe
import Either

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

pat [a,b,c,d] = True
pat [d,c,b,a] = True
pat [b,d,a,c] = True
pat [c,a,d,b] = True

theorem1cond2 l | even (length (filter (\ x -> x == 2 || x == 5 || x == 6) l))
	      = l

TE e j
	     | (e == a || e == c) && (j == 1 || j == 6) = case e of
	       a -> Just b
	       c -> Just d
	     | e == b && (j == 3 || j == 5) = case e of
	       --a -> Just c
	       b -> Just d
	     | e == c && j /= 3 && j /= 5 = case e of
	       --a -> Just b
	       c -> Just d
	     | otherwise = Nothing

hide t e
     | t == 2 || t == 5 = case e of
       b -> c
       c -> b
     | otherwise = case e of
       b -> b
       c -> c
--

gen_vars n = if n==0 then [] else var : gen_vars (n-1)  where var free

seed = unsafePerformIO getRandomSeed
rand m = head (take 1 (nextIntRange seed m))
once x = fromJust (unsafePerformIO (getOneSolution x))

hiddenedge = [b,c] !! rand 2
inverse e = case e of
	a -> d
	b -> c
	c -> b
	d -> a

-- generate random junction set that matches known pattern
juncset n = let
       juncset_ jl =
	   jl == gen_vars n & domain jl 1 6 & labeling [RandomValue seed] jl &
 	   o_ == map (\ junctype -> \ E -> junc junctype E) jl & jc == foldl1 (flip (.)) o_ & pat (map jc [a,b,c,d])
           where jc,o_ free
       l = once juncset_
 in trace (show l) theorem1cond2 l

-- produce equations for Es lines from generating lines
Es [[x1,y1],[x2,y2]] =
   let ab = [2,10]
       A = y1 -. y2
       B = x2 -. x1
       C = x1*.y2 -. x2*.y1
       eq C_ = \ x y -> A CLPR.*.x CLPR.+. B CLPR.*.y CLPR.+. C_ == 0
       z1 = sqrt (A^.2 +. B^.2)
       Cs d_ =
   	   let z = d_ *. z1
        in map (\ C_ -> eq C_) [C +. z, C -. z]
 in zipWith (\ edge Ei -> (edge,Ei)) [b,c,a,d] (concatMap Cs ab)

-- solve equation system to get coordinates of the corners
cross eq1 eq2 = both round (once (\ (x,y) -> (eq1 x y) & (eq2 x y)))

main = runGUI "impart" main_
main_ = let
      	-- todo error or support lines x = 0 or y = 0
	BPs1 = [[[-100,-90],[-70,110]],[[-70,110],[110,-100]],[[110,-100],[-100,-90]]] --triangle
	--BPs2 = [[[-70,80],[-40,100]],[[-40,100],[70,80]],[[70,80],[0,0]],[[0,0],[70,-50]],[[70,-50],[-60,-80]],[[-60,-80],[-70,80]]] --escher
	BPs3 = [[[-100,0],[-70,80]],[[-70,80],[0,110]],[[0,110],[70,80]],[[70,80],[110,0]], --octagon
		[[110,0],[70,-80]],[[70,-80],[0,-100]],[[0,-100],[-70,-80]],[[-70,-80],[-100,0]]]
	BPs_ = [BPs1,BPs3]
	BPs = BPs_ !! rand (length BPs_)

     	n = length BPs
	ns = [1..n]
	ns1 = concatMap (\ n_ -> take 4 (repeat n_)) ns
	edges_ = [if i == n then (n,1,j) else (i,i+1,j) | (i,j) <- zip ns1 (concatMap Es BPs)]
	js = juncset n
	-- make a closed bar graph, all Es are linked to the same nodes, nodes hold junctions
     	bargraph = mkGraph (zipWith (\ n_ j -> (n_,Left j)) ns js) edges_
	filteredge e = filter (\ (_,_,(edge,_)) -> edge == e)
	filtertvs = filter (\ (_,_,(edge,_)) -> edge /= tvs)
        JG (_,v,Left junctype,_) g =
	   let il = inn g v
	       ol = out g v
               knot (g1,corner) (ifrom,_,iEi@(iedge,_)) = let
	       	      oedge = junc junctype iedge
		      [n2] = newNodes 1 g1
	       	      [(_,oto,oEi)] = filteredge oedge ol
		      f1 x = insNode (n2,Right (Just v)) x
		      f2 x = insEdges [(ifrom,n2,iEi),(n2,oto,oEi)] x
	        in (f2 (f1 g1),n2 : corner)
	       (g2,corner1) = foldl knot (g,[]) il
	       g4 = delNode v g2 -- leaf arcs are removed automatically
	       ins = concatMap (\ v1 -> inn g4 v1) corner1
               TE_ edge from x = let
	       		     [(_,to,(_,invalid))] = filteredge edge ins
                in insEdge (from,to,(tvs,invalid)) x
	       apply v1 f o = case v1 of
	       	     Just v2 -> f v2 o
		     Nothing -> o
	       g3 = foldl (\ g5 (_,from,(edge,_)) -> apply (TE {-(inverse edge)-} edge junctype) (\ e x -> TE_ {-(inverse e)-} e from x) g5) g4 ins -- transversal edges are added within each corner
         in g3
	-- make a figure graph from bar graph by arcs relinking in accordance with junctions
	Cg = ufold JG bargraph bargraph
	corners = let
		oldnewv = map (\ (v,Right (Just oldv)) -> (oldv,v)) (labNodes Cg)
		matchv x = filter (\ (oldv,_) -> oldv == x) oldnewv
	 in zipWith (\ j x -> (j,map (\ (_,newv) -> newv) (matchv x))) js
	 ns -- consistence is a must for HE to make it's work properly
	HE (g6,e1) (junctype,corner)
	   | junctype == 1 || junctype == 6 =
	     (delNode ito g6,junc junctype e1)
	   | otherwise =
	     (delEdge (ifrom,ito) g6,hide junctype e1)
	   where ins = concatMap (\ v1 -> inn Cg v1) corner
	   	 [(ifrom,ito,_)] = filteredge e1 ins
	-- remove invisible edges based on randomly picked b or c edge
	(Cg4,_) = foldl HE (Cg,hiddenedge) corners
        FO (_,v,Right (Just l),_) g = let
	    getedge oldv dirf e = head (filteredge e (dirf bargraph oldv))
	    getlab (_,_,l1) = l1
            fixnode todir =
	    	    let
			[n1] = newNodes 1 g
			f1 x = insNode (n1,Right (Nothing)) x
			l1 = getlab (getedge l (if todir then inn else out) {-d-} a) -- copy a or d edge and link orphan node to it
			f2 x = insEdge (if todir then (n1,v,l1) else (v,n1,l1)) x
             in f2 (f1 g)
	    matchnodes p g1 = case p of
	    	([],_) -> fixnode True
		(_,[]) -> fixnode False
	    	_ -> g1
	    f3 x = matchnodes (filtertvs (inn g v),filtertvs (out g v)) x
         in f3 g
	-- link orphan edges
	Cg3 = ufold FO Cg4 Cg4
        CP (s,v,_,p) = let
	    il = filtertvs (inn Cg3 v)
	    ol = filtertvs (out Cg3 v)
	    makecross [(_,_,(_,E1))] [(_,_,(_,E2))] = cross E1 E2
	    l2 = if il == [] || ol == [] then Nothing else Just (makecross il ol)
         in (s,v,l2,p)
	-- calc cross points
	Cg1 = gmap CP Cg3
	Cg5 = foldl (\ g (v,l) -> if isNothing l then delNode v g else g) Cg1 (labNodes Cg1)
	Es1 node cross1_ = case node of
      	    [(_,v1)] -> [((cross1_,cross2),v1)] where cross2 = fromJust (lab Cg5 v1)
	    [(_,v1),(_,v2)] -> [((cross1_,cross12),v1),((cross1_,cross22),v2)] where (cross12,cross22) = (fromJust (lab Cg5 v1),fromJust (lab Cg5 v2))
      	    [] -> []
	    x -> error (show x)
	-- assign Es segments to arcs
	Cg2 = gmap (\ (p,v,l,s) -> (Es1 p l,v,l,Es1 s l)) Cg5
	prepare = map (\ (_,_,(Just p1,Just p2)) -> [both (+200) p1,both (+200) p2]) (labEdges Cg2)
	draw gport = mapIO_ (\ l -> addCanvas cref [CLine l ""] gport) prepare
 in Col [] [Canvas [WRef cref, Height 400, Width 400],
       	      Button draw [Text "draw"]]
	      where cref free
