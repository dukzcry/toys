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
import Control.AllSolutions
import Data.GraphInductive
import System.Random
import GUI
import Function
import List
import Unsafe
import Maybe
import Either

data Edge = A | B | C | D | Transverse deriving (Eq,Show,Enum)

-- rule-o-rama
juncRule 1 edge = edge
juncRule 2 edge = case edge of
  A -> B
  B -> A
  C -> D
  D -> C
juncRule 3 edge = case edge of
  A -> B
  B -> D
  C -> A
  D -> C
juncRule 4 edge = case edge of
  A -> C
  B -> A
  C -> D
  D -> B
juncRule 5 edge = case edge of
  A -> C
  B -> D
  C -> A
  D -> B
juncRule 6 edge = case edge of
  A -> A
  B -> C
  C -> B
  D -> D

juncPattern [A,B,C,D] = True
juncPattern [D,C,B,A] = True
juncPattern [B,D,A,C] = True
juncPattern [C,A,D,B] = True

theorem1Condition2 juncList
  | even (length (filter (\ junc -> junc == 2 || junc == 5 || junc == 6) juncList))
  = juncList

transverseRule edge junc
  | (edge == A || edge == C) && (junc == 1 || junc == 6) = case edge of
    A -> Just B
    C -> Just D
  | edge == B && (junc == 3 || junc == 5) = case edge of
    --A -> Just C
    B -> Just D
  | edge == C && junc /= 3 && junc /= 5 = case edge of
    --A -> Just B
    C -> Just D
  | otherwise = Nothing

hiddenRule junc edge
  | junc == 2 || junc == 5 = case edge of
    B -> C
    C -> B
  | otherwise = case edge of
    B -> B
    C -> C
--

gen_vars n = if n==0 then [] else var : gen_vars (n-1)  where var free

seed = unsafePerformIO getRandomSeed
random limit = head (take 1 (nextIntRange seed limit))
getSolution solution = fromJust (unsafePerformIO (getOneSolution solution))

hiddenEdge = [B,C] !! random 2
inverse edge = case edge of
  A -> D
  B -> C
  C -> B
  D -> A

data EsSegment = EsSegmentR { vSegF :: Int, dotF :: [Int] } | EsSegmentEmpty deriving (Show,Eq)
data GraphArc = GraphArcR { edgeF :: Edge, esLinesF :: Float -> Float -> Bool, genLineF :: [[Float]] }
                | GraphArc2R { edgeF :: Edge, esSegment1F :: EsSegment, esSegment2F :: EsSegment }
data GraphNode = GraphNode Int | GraphNodeR { vNodeF :: Int, orientF :: Bool } | GraphNodeEmpty deriving Show
data OldNewV = OldNewVR { oldVF :: Int, newVF :: Int }
matchv x l = filter (\ oldNewVR -> oldVF oldNewVR == x) l
data DrawLine = DrawLineR { edgeDrawF :: Edge, lineF :: [(Int,Int)] }

-- GENERATE RANDOM JUNCTION SET THAT MATCHES KNOWN PATTERN
juncSet numOfNodes =
  let
    solution output =
      output == gen_vars numOfNodes & domain output 1 6 & True & labeling [RandomValue seed] output &&
      var1 =:= map (\ junc -> \ edge -> juncRule junc edge) output && var2 =:= foldr1 (.) var1 && juncPattern (map var2 [A .. D])
      where var1, var2 free
    juncList = getSolution solution
  in trace (show juncList) theorem1Condition2 juncList

-- PRODUCE EQUATIONS FOR ES LINES FROM GENERATING LINES
graphArcs genLine@[[x1,y1],[x2,y2]] | x2 -. x1 /= 0 && y2 -. y1 /= 0 =
  let
    offsets = [2,10]
    a = y1 -. y2
    b = x2 -. x1
    c = x1*.y2 -. x2*.y1
    lineEquation c1 = \ x y -> a CLPR.*.x CLPR.+. b CLPR.*.y CLPR.+. c1 =:= 0
    var1 = sqrt (a^.2 +. b^.2)
    esLines offset =
      let
        shift = offset *. var1
      in map (\ c2 -> lineEquation c2) [c +. shift, c -. shift]
  in zipWith (\ edge esLines1 -> GraphArcR { edgeF = edge, esLinesF = esLines1, genLineF = genLine }) [B,C,A,D] (concatMap esLines offsets)

-- SOLVE EQUATION SYSTEM TO GET COORDINATES OF CORNERS
linesCross lineEquation1 lineEquation2 = map round (getSolution (\ [x,y] -> (lineEquation1 x y) && (lineEquation2 x y)))

-- DETERMINE CORNER DIRECTION
clockwise [[x1,y1],[x2,y2]] [_,[x3,y3]] = (x2 -. x1)*.(y3 -. y1) -. (y2 -. y1)*.(x3 -. x1) < 0

main = runGUI "impart" main'
main' = let
        -- FIGURE CONTOURS UPON WHICH IMPOSSIBLE FIGURES ARE BUILT
        -- todo support lines x = 0 or y = 0
        bps1 = [[[-100,-90],[-70,110]],[[-70,110],[110,-100]],[[110,-100],[-100,-90]]] -- triangle
        bps2 = [[[-100,0],[-70,80]],[[-70,80],[0,110]],[[0,110],[70,80]],[[70,80],[110,0]], -- octagon
               [[110,0],[70,-80]],[[70,-80],[0,-100]],[[0,-100],[-70,-80]],[[-70,-80],[-100,0]]]
        bps3 = [[[-70,80],[-40,100]],[[-40,100],[70,80]],[[70,80],[0,0]],[[0,0],[70,-50]],[[70,-50],[-60,-80]],[[-60,-80],[-70,80]]] -- waterfall
        bps4 = [[[-100,-90],[-90,110]],[[-90,110],[100,-100]],[[100,-100],[110,110]],[[110,110],[-100,-90]]] -- crossed rectangle
        bps5 = [[[-70,-80],[0,110]],[[0,110],[70,-80]],[[70,-80],[-100,40]],[[-100,40],[100,30]],[[100,30],[-70,-80]]] -- crossed star
        bps6 = [[[-100,-100],[100,100]],[[100,100],[-100,0]],[[-100,0],[100,-100]],[[100,-100],[-100,100]],[[-100,100],[100,0]],[[100,0],[-100,-100]]] -- crossed double star
        bps' = [bps1,bps2,bps3,bps4,bps5,bps6]
        bps = bps' !! random (length bps')

        n = length bps
        ns = [1..n]
        ns1 = concatMap (\ n' -> replicate 4 n') ns
        edges' = [if i == n then (n,1,j) else (i,i+1,j) | (i,j) <- zip ns1 (concatMap graphArcs bps)]
        js = juncSet n
        -- MAKE A CLOSED BAR GRAPH, ALL ES ARE LINKED TO THE SAME NODES, NODES HOLD JUNCTIONS
        bargraph = mkGraph (zipWith (\ n' j -> (n',GraphNode j)) ns js) edges'
        filteredge e x = head (filter (\ (_,_,graphArc) -> edgeF graphArc == e) x)
        filtertvs x = filter (\ (_,_,graphArc) -> edgeF graphArc /= Transverse) x
        jg (_,v,GraphNode junc,_) g =
           let il = inn g v
               ol = out g v
               (_,_,GraphArcR {genLineF = line1}) = filteredge A il
               (_,_,GraphArcR {genLineF = line2}) = filteredge A ol
               orient = clockwise line1 line2
               knot (ifrom,_,iei@GraphArcR {edgeF = iedge}) (g1,corner) = let
                      oedge = juncRule junc iedge
                      [n2] = newNodes 1 g1
                      (_,oto,oei) = filteredge oedge ol
                      f1 x = insNode (n2,GraphNodeR { vNodeF = v, orientF = orient }) x
                      f2 x = insEdges [(ifrom,n2,iei),(n2,oto,oei)] x
                in (f2 (f1 g1),n2 : corner)
               (g2,corner1) = foldr knot (g,[]) il
                -- leaf arcs are removed automatically
               g4 = delNode v g2
               ins = concatMap (\ v1 -> inn g4 v1) corner1
               te' edge from x = let
                             (_,to,graphArc) = filteredge edge ins
                in insEdge (from,to,graphArc { edgeF = Transverse }) x
                -- transversal edges are added within each corner
               g3 = foldr (\ (_,from,GraphArcR {edgeF = edge}) g5 ->
                  maybe g5 (\ e -> te' (if orient then e else inverse e) from g5)
                  (transverseRule (if orient then edge else inverse edge) junc)) g4 ins
         in g3
        -- MAKE A FIGURE GRAPH FROM BAR GRAPH BY ARCS RELINKING IN ACCORDANCE WITH JUNCTIONS
        cg = ufold jg bargraph bargraph
        corners = let
                oldnewv = map (\ (v,GraphNodeR {vNodeF = oldv}) -> OldNewVR {oldVF = oldv, newVF = v}) (labNodes cg)
         in zipWith (\ j x -> (j,map (\ oldNewVR -> newVF oldNewVR) (matchv x oldnewv))) js ns
        he (junc,corner) (g6,e1)
           | junc == 1 || junc == 6 =
             (delNode ofrom g6,juncRule junc e1)
           | otherwise =
             (delEdge (ofrom,oto) g6,hiddenRule junc e1)
           where ins = concatMap (\ v1 -> out cg v1) corner
                 (ofrom,oto,_) = filteredge e1 ins
        -- REMOVE INVISIBLE EDGES BASED ON RANDOMLY PICKED B OR C EDGE
        (cg4,_) = foldr he (cg,hiddenEdge) corners
        fo (_,v,GraphNodeR { vNodeF = l, orientF = orient },_) g = let
            getedge oldv dirf e = filteredge e (dirf bargraph oldv)
            fixnode todir =
                    let
                        [n1] = newNodes 1 g
                        f1 x = insNode (n1,GraphNodeEmpty) x
                        -- copy border edge and link orphan node to it
                        (_,_,l1) = getedge l (if todir then inn else out) (if orient then A else inverse A)
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
        cp (s,v,l,p) = let
            il = filtertvs (inn cg3 v)
            ol = filtertvs (out cg3 v)
            makecross [(_,_,GraphArcR {esLinesF = e1})] [(_,_,GraphArcR {esLinesF = e2})] = linesCross e1 e2
            l2 = if null il || null ol then EsSegmentEmpty else EsSegmentR { vSegF = vNodeF l, dotF = makecross il ol }
         in (s,v,l2,p)
        -- CALCULATE CROSS POINTS
        cg1 = gmap cp cg3
        cg5 = foldr (\ (v,l) g -> if l == EsSegmentEmpty then delNode v g else g) cg1 (labNodes cg1)
        es1 node cross1' = case node of
            [(GraphArcR {edgeF = e},v1)] -> [(GraphArc2R {edgeF = e,esSegment1F = cross1',esSegment2F = cross2},v1)] where cross2 = fromJust (lab cg5 v1)
            [(GraphArcR {edgeF = e1},v1),(GraphArcR {edgeF = e2},v2)] ->
              [(GraphArc2R {edgeF = e1,esSegment1F = cross1',esSegment2F = cross12},v1),(GraphArc2R {edgeF = e2,esSegment1F = cross1',esSegment2F = cross22},v2)]
              where (cross12,cross22) = (fromJust (lab cg5 v1),fromJust (lab cg5 v2))
            [] -> []
            --x -> error (show x)
        -- ASSIGN ES SEGMENTS TO ARCS
        cg2 = gmap (\ (p,v,l,s) -> (es1 p l,v,l,es1 s l)) cg5
        -- CROSSED BARS PART 1
        draworder = let
                  oldnewv = map (\ (v,EsSegmentR { vSegF = oldv }) -> OldNewVR { oldVF = oldv, newVF = v}) (labNodes cg2)
                  randset = shuffle seed ns
                  prepare (_,_,GraphArc2R {
                    edgeF = e,
                    esSegment1F = EsSegmentR { dotF = [x1,y1] },
                    esSegment2F = EsSegmentR { dotF = [x2,y2] }
                  }) = DrawLineR { edgeDrawF = e, lineF = [(x1+200,200-y1),(x2+200,200-y2)] }
         in map (\ x -> concatMap (\ oldNewVR -> map prepare (out cg2 (newVF oldNewVR))) (matchv x oldnewv)) randset
        -- CROSSED BARS PART 2
        erase gport list = let
              filteredge2 e x = head (filter (\ drawLineR -> edgeDrawF drawLineR == e) x)
              -- todo support lines x = 0
              fixdir DrawLineR { lineF = p@[(x1,_),(x2,_)] } | x2 - x1 /= 0 = if x2 - x1 > 0 then p else reverse p
              [ba,ea] = fixdir (filteredge2 A list)
              [bm,em] = fixdir (filteredge2 (B ? C) list)
              [bd,ed] = fixdir (filteredge2 D list)
         -- todo better erasing parameters, currently needs antialiasing like on osx
         in addCanvas cref [CPolygon [ba,bm,bd,ed,em,ea] "-fill white -width 0"] gport
        line gport list = mapIO_ (\ DrawLineR { lineF = l } -> addCanvas cref [CLine l "-width 1"] gport) list
        draw gport = mapIO_ (\ list -> do erase gport list
                                          line gport list) draworder
 in Col [] [Canvas [WRef cref, Height 400, Width 400, Background "white"],
              Button draw [Text "draw"]]
              where cref free
