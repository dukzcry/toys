------------------------------------------------------------------------------
--- Impossible figure generator
---
--- @author Artem Lukyanov
--- @version Jule 2018
--- @category general
------------------------------------------------------------------------------

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

data edge_ = a | b | c | d | tvs deriving (Eq,Show,Enum)

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

te e j
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

-- GENERATE RANDOM JUNCTION SET THAT MATCHES KNOWN PATTERN
juncset n = let
       juncset_ jl =
           jl == gen_vars n & domain jl 1 6 & True & labeling [RandomValue seed] jl &&
           o_ =:= map (\ junctype -> \ x -> junc junctype x) jl && jc =:= foldr1 (.) o_ && pat (map jc [a .. d])
           where jc,o_ free
       l = once juncset_
 in trace (show l) theorem1cond2 l

-- PRODUCE EQUATIONS FOR ES LINES FROM GENERATING LINES
es v@[[x1,y1],[x2,y2]] | x2 -. x1 /= 0 && y2 -. y1 /= 0 =
   let ab = [2,10]
       ap = y1 -. y2
       bp = x2 -. x1
       cp = x1*.y2 -. x2*.y1
       eq cf = \ x y -> ap CLPR.*.x CLPR.+. bp CLPR.*.y CLPR.+. cf =:= 0
       z1 = sqrt (ap^.2 +. bp^.2)
       cs d_ =
           let z = d_ *. z1
        in map (\ x -> eq x) [cp +. z, cp -. z]
 in zipWith (\ edge ei -> (edge,ei,v)) [b,c,a,d] (concatMap cs ab)

-- SOLVE EQUATION SYSTEM TO GET COORDINATES OF CORNERS
cross eq1 eq2 = both round (once (\ (x,y) -> (eq1 x y) && (eq2 x y)))

-- DETERMINE CORNER DIRECTION
clockwise [[x1,y1],[x2,y2]] [_,[x3,y3]] =
          (x2 -. x1)*.(y3 -. y1) -. (y2 -. y1)*.(x3 -. x1) < 0

main = runGUI "impart" main_
main_ = let
        -- FIGURE CONTOURS UPON WHICH IMPOSSIBLE FIGURES ARE BUILT
        -- todo support lines x = 0 or y = 0
        bps1 = [[[-100,-90],[-70,110]],[[-70,110],[110,-100]],[[110,-100],[-100,-90]]] -- triangle
        bps2 = [[[-100,0],[-70,80]],[[-70,80],[0,110]],[[0,110],[70,80]],[[70,80],[110,0]], -- octagon
               [[110,0],[70,-80]],[[70,-80],[0,-100]],[[0,-100],[-70,-80]],[[-70,-80],[-100,0]]]
        bps3 = [[[-70,80],[-40,100]],[[-40,100],[70,80]],[[70,80],[0,0]],[[0,0],[70,-50]],[[70,-50],[-60,-80]],[[-60,-80],[-70,80]]] -- waterfall
        bps4 = [[[-100,-90],[-90,110]],[[-90,110],[100,-100]],[[100,-100],[110,110]],[[110,110],[-100,-90]]] -- crossed rectangle
        bps5 = [[[-70,-80],[0,110]],[[0,110],[70,-80]],[[70,-80],[-100,40]],[[-100,40],[100,30]],[[100,30],[-70,-80]]] -- crossed star
        bps6 = [[[-100,-100],[100,100]],[[100,100],[-100,0]],[[-100,0],[100,-100]],[[100,-100],[-100,100]],[[-100,100],[100,0]],[[100,0],[-100,-100]]] -- crossed double star
        bps_ = [bps1,bps2,bps3,bps4,bps5,bps6]
        bps = bps_ !! rand (length bps_)

        n = length bps
        ns = [1..n]
        ns1 = concatMap (\ n_ -> replicate 4 n_) ns
        edges_ = [if i == n then (n,1,j) else (i,i+1,j) | (i,j) <- zip ns1 (concatMap es bps)]
        js = juncset n
        -- MAKE A CLOSED BAR GRAPH, ALL ES ARE LINKED TO THE SAME NODES, NODES HOLD JUNCTIONS
        bargraph = mkGraph (zipWith (\ n_ j -> (n_,Left j)) ns js) edges_
        filteredge e x = head (filter (\ (_,_,(edge,_,_)) -> edge == e) x)
        filtertvs x = filter (\ (_,_,(edge,_,_)) -> edge /= tvs) x
        jg (_,v,Left junctype,_) g =
           let il = inn g v
               ol = out g v
               (_,_,(_,_,line1)) = filteredge a il
               (_,_,(_,_,line2)) = filteredge a ol
               orient = clockwise line1 line2
               knot (ifrom,_,iei@(iedge,_,_)) (g1,corner) = let
                      oedge = junc junctype iedge
                      [n2] = newNodes 1 g1
                      (_,oto,oei) = filteredge oedge ol
                      f1 x = insNode (n2,Right (Just (v,orient))) x
                      f2 x = insEdges [(ifrom,n2,iei),(n2,oto,oei)] x
                in (f2 (f1 g1),n2 : corner)
               (g2,corner1) = foldr knot (g,[]) il
                -- leaf arcs are removed automatically
               g4 = delNode v g2
               ins = concatMap (\ v1 -> inn g4 v1) corner1
               te_ edge from x = let
                             (_,to,(_,invalid,invalid2)) = filteredge edge ins
                in insEdge (from,to,(tvs,invalid,invalid2)) x
               apply v1 f o = case v1 of
                     Just v2 -> f v2 o
                     Nothing -> o
                -- transversal edges are added within each corner
               g3 = foldr (\ (_,from,(edge,_,_)) g5 ->
                  apply (te (if orient then edge else inverse edge) junctype)
                  (\ e x -> te_ (if orient then e else inverse e) from x) g5) g4 ins
         in g3
        -- MAKE A FIGURE GRAPH FROM BAR GRAPH BY ARCS RELINKING IN ACCORDANCE WITH JUNCTIONS
        cg = ufold jg bargraph bargraph
        matchv x l = filter (\ (oldv,_) -> oldv == x) l
        corners = let
                oldnewv = map (\ (v,Right (Just (oldv,_))) -> (oldv,v)) (labNodes cg)
         in zipWith (\ j x -> (j,map (\ (_,newv) -> newv) (matchv x oldnewv))) js ns
        he (junctype,corner) (g6,e1)
           | junctype == 1 || junctype == 6 =
             (delNode ofrom g6,junc junctype e1)
           | otherwise =
             (delEdge (ofrom,oto) g6,hide junctype e1)
           where ins = concatMap (\ v1 -> out cg v1) corner
                 (ofrom,oto,_) = filteredge e1 ins
        -- REMOVE INVISIBLE EDGES BASED ON RANDOMLY PICKED B OR C EDGE
        (cg4,_) = foldr he (cg,hiddenedge) corners
        fo (_,v,Right (Just (l,orient)),_) g = let
            getedge oldv dirf e = filteredge e (dirf bargraph oldv)
            fixnode todir =
                    let
                        [n1] = newNodes 1 g
                        f1 x = insNode (n1,Right Nothing) x
                        -- copy border edge and link orphan node to it
                        (_,_,l1) = getedge l (if todir then inn else out) (if orient then a else inverse a)
                        f2 x = insEdge (if todir then (n1,v,l1) else (v,n1,l1)) x
             in f2 (f1 g)
            matchnodes p g1 = case p of
                ([],_) -> fixnode True
                (_,[]) -> fixnode False
                _ -> g1
            f3 x = matchnodes (filtertvs (inn g v),filtertvs (out g v)) x
         in f3 g
        -- LINK ORPHAN EDGES
        cg3 = ufold fo cg4 cg4
        cp (s,v,Right l,p) = let
            il = filtertvs (inn cg3 v)
            ol = filtertvs (out cg3 v)
            makecross [(_,_,(_,e1,_))] [(_,_,(_,e2,_))] = cross e1 e2
            -- il == [] || ol == []
            isempty l_ = case l_ of
              [] -> True
              _ -> False
            l2 = if isempty il || isempty ol then Nothing else Just (fst (fromJust l),makecross il ol)
         in (s,v,l2,p)
        -- CALCULATE CROSS POINTS
        cg1 = gmap cp cg3
        cg5 = foldr (\ (v,l) g -> if isNothing l then delNode v g else g) cg1 (labNodes cg1)
        es1 node cross1_ = case node of
            [((e,_,_),v1)] -> [((e,cross1_,cross2),v1)] where cross2 = fromJust (lab cg5 v1)
            [((e1,_,_),v1),((e2,_,_),v2)] -> [((e1,cross1_,cross12),v1),((e2,cross1_,cross22),v2)] where (cross12,cross22) = (fromJust (lab cg5 v1),fromJust (lab cg5 v2))
            [] -> []
            --x -> error (show x)
        -- ASSIGN ES SEGMENTS TO ARCS
        cg2 = gmap (\ (p,v,l,s) -> (es1 p l,v,l,es1 s l)) cg5
        -- CROSSED BARS PART 1
        draworder = let
                  oldnewv = map (\ (v,Just (oldv,_)) -> (oldv,v)) (labNodes cg2)
                  randset = shuffle seed ns
                  prepare (_,_,(e,Just (_,(x1,y1)),Just (_,(x2,y2)))) = (e,[(x1+200,200-y1),(x2+200,200-y2)])
         in map (\ x -> concatMap (\ (_,newv) -> map prepare (out cg2 newv)) (matchv x oldnewv)) randset
        -- CROSSED BARS PART 2
        erase gport list = let
              filteredge2 e x = head (filter (\ (edge,_) -> edge == e) x)
              -- todo support lines x = 0
              fixdir (_,p@[(x1,_),(x2,_)]) | x2 - x1 /= 0 = if x2 - x1 > 0 then p else reverse p
              [ba,ea] = fixdir (filteredge2 a list)
              [bm,em] = fixdir (filteredge2 (b ? c) list)
              [bd,ed] = fixdir (filteredge2 d list)
         -- todo better erasing parameters, currently needs antialiasing like on osx
         in addCanvas cref [CPolygon [ba,bm,bd,ed,em,ea] "-fill white -width 0"] gport
        line gport list = mapIO_ (\ (_,l) -> addCanvas cref [CLine l "-width 1"] gport) list
        draw gport = mapIO_ (\ list -> do erase gport list
                                          line gport list) draworder
 in Col [] [Canvas [WRef cref, Height 400, Width 400, Background "white"],
              Button draw [Text "draw"]]
              where cref free
