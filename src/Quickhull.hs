{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# LANGUAGE TypeOperators     #-}

module Quickhull (

  Point, Line, SegmentedPoints,
  quickhull,

  -- Exported for display
  initialPartition,
  partition,

  -- Exported just for testing
  propagateL, shiftHeadFlagsL, segmentedScanl1,
  propagateR, shiftHeadFlagsR, segmentedScanr1,

) where

import Data.Array.Accelerate
import Data.Array.Accelerate.Debug.Trace
import qualified Prelude                      as P


-- Points and lines in two-dimensional space
--
type Point = (Int, Int)
type Line  = (Point, Point)

-- This algorithm will use a head-flags array to distinguish the different
-- sections of the hull (the two arrays are always the same length).
--
-- A flag value of 'True' indicates that the corresponding point is
-- definitely on the convex hull. The points after the 'True' flag until
-- the next 'True' flag correspond to the points in the same segment, and
-- where the algorithm has not yet decided whether or not those points are
-- on the convex hull.
--
type SegmentedPoints = (Vector Bool, Vector Point)


-- Core implementation
-- -------------------

-- Initialise the algorithm by first partitioning the array into two
-- segments. Locate the left-most (p₁) and right-most (p₂) points. The
-- segment descriptor then consists of the point p₁, followed by all the
-- points above the line (p₁,p₂), followed by the point p₂, and finally all
-- of the points below the line (p₁,p₂).
--
-- To make the rest of the algorithm a bit easier, the point p₁ is again
-- placed at the end of the array.
--
-- We indicate some intermediate values that you might find beneficial to
-- compute.
--
initialPartition :: Acc (Vector Point) -> Acc SegmentedPoints
initialPartition points =
  let
      p1, p2 :: Exp Point
      p1 = the $ fold leftMostPoint (T2 maxBound maxBound) points
      p2 = the $ fold rightMostPoint (T2 minBound minBound) points

      leftMostPoint :: Exp Point -> Exp Point -> Exp Point
      leftMostPoint q1@(T2 x1 y1) q2@(T2 x2 y2)  = if x1 < x2 then q1 else 
                                                    if x1 == x2 then 
                                                      if y1 < y2 then q1 else q2
                                                    else q2
      rightMostPoint q1@(T2 x1 y1) q2@(T2 x2 y2) = if x1 > x2 then q1 else 
                                                    if x1 == x2 then 
                                                      if y1 > y2 then q1 else q2
                                                    else q2

      isUpper :: Acc (Vector Bool)
      isUpper = map (\p -> p /= p1 && p /= p2 && pointIsLeftOfLine (T2 p1 p2) p) points

      isLower :: Acc (Vector Bool)
      isLower = map (\p -> p /= p1 && p /= p2 && pointIsLeftOfLine (T2 p2 p1) p) points

      offsetUpper :: Acc (Vector Int)
      countUpper  :: Acc (Scalar Int)
      T2 offsetUpper countUpper = T2 locations totalCount where
        isUpperInt = map makeInt isUpper
        locations :: Acc (Vector Int)
        locations = scanl (+) 0 isUpperInt
        totalCount = unit $ locations ! (I1 $ length locations - 1)

      offsetLower :: Acc (Vector Int)
      countLower  :: Acc (Scalar Int)
      T2 offsetLower countLower = T2 locations totalCount where
        isLowerInt = map makeInt isLower 
        locations :: Acc (Vector Int)
        locations = scanl (+) 0 isLowerInt
        totalCount = unit $ locations ! (I1 $ length locations - 1)

      destination :: Acc (Vector (Maybe DIM1))
      destination = generate (shape points) $ \idx ->
        let 
          point = points ! idx
          isUpperPoint = isUpper ! idx
          isLowerPoint = isLower ! idx
          offSetUpperPoint = offsetUpper ! idx
          offsetLowerPoint = offsetLower ! idx
          uppers = the countUpper
        in 
          if point == p1 then 
            Just_ $ I1 0 -- place p1 at the start
          else if isUpperPoint then 
            Just_ $ I1 $ 1 + offSetUpperPoint -- then place all the uppers
          else if point == p2 then 
            Just_ $ I1 $ uppers + 1 -- then place p2
          else if isLowerPoint then 
            Just_ $ I1 $ 2 + uppers + offsetLowerPoint -- then place all lowers
          else Nothing_
          
      outShape = I1 $ 1 + the countUpper + 1 + the countLower + 1

      newPoints :: Acc (Vector Point)
      newPoints = generate outShape $ \(I1 idx) -> if idx == the countUpper + the countLower + 2 then p1 else withoutLastP1 ! (I1 idx)where 
        withoutLastP1 = permute const (generate (I1 (unindex1 outShape - 1)) $ \_ -> T2 0 0) (\idx -> destination ! idx) points

      headFlags :: Acc (Vector Bool)
      headFlags = generate outShape $ \(I1 idx) -> 
        idx == 0 
        || idx == the countUpper + 1 
        || idx == the countUpper + the countLower + 2
  in
  T2 headFlags newPoints


-- The core of the algorithm processes all line segments at once in
-- data-parallel. This is similar to the previous partitioning step, except
-- now we are processing many segments at once.
--
-- For each line segment (p₁,p₂) locate the point furthest from that line
-- p₃. This point is on the convex hull. Then determine whether each point
-- p in that segment lies to the left of (p₁,p₃) or the right of (p₂,p₃).
-- These points are undecided.
--
partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) = let 
    p1s = propagateL headFlags points
    p2s = propagateR headFlags points

    distPoints = zipWith3 (\h p line ->
      if h
      then T2 (-1) p
      else T2 (abs (nonNormalizedDistance line p)) p) headFlags points (zip p1s p2s)

    maxByDist :: Exp (Int, Point) -> Exp (Int, Point) -> Exp (Int, Point)
    maxByDist (T2 d1 p1) (T2 d2 p2) =
          d1 > d2 ? ( T2 d1 p1
        , d2 > d1 ? ( T2 d2 p2
        , T2 d1 (min p1 p2) ))
    
    bestPairs = propagateL headFlags $ segmentedScanl1 maxByDist headFlags distPoints

    isFurthest = zipWith3 (\h p (T2 _ bestPoint) -> not h && p == bestPoint) headFlags points bestPairs

    newHeadFlags = zipWith (||) headFlags isFurthest -- new head flags are old headflags or the furthest points

    p3s = propagateL newHeadFlags points

    leftOfP1P3 = zipWith3 (\h p line  -> -- like isUpper in initialPartition
      not h && pointIsLeftOfLine line p) newHeadFlags points (zip p1s p3s)


    leftOfP3P2 = zipWith3 (\h p line -> -- like isLower in initialPartition
      not h && pointIsLeftOfLine line p) newHeadFlags points (zip p3s p2s)

    keep = zipWith3 (\h l r -> h || l || r) newHeadFlags leftOfP1P3 leftOfP3P2 -- only keep heads points left of line and points right of line
 
    offsets = scanl (+) 0 (map makeInt keep)
    newSize = unit (offsets ! (I1 $ length offsets - 1))

    newPoints = permute const (generate (I1 $ the newSize) (const $ T2 0 0)) 
      (\i -> if keep ! i then Just_ (I1 (offsets ! i)) else Nothing_)
      points

    newHeadFlags' = permute const (generate (I1 (the newSize)) (const False_))
      (\i -> if keep ! i then Just_ (I1 (offsets ! i)) else Nothing_)
      newHeadFlags

  in 
    T2 newHeadFlags' newPoints


-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull =
  error "TODO: quickhull"


-- Helper functions
-- ----------------

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ propagateL (use flags) (use values)
--
-- should be:
-- Vector (Z :. 9) [1,1,1,4,5,5,5,5,9]
propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL = segmentedScanl1 (\a _ -> a)

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ propagateR (use flags) (use values)
--
-- should be:
-- Vector (Z :. 9) [1,4,4,4,5,9,9,9,9]
propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR = segmentedScanr1 (\b _ -> b)

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> run $ shiftHeadFlagsL (use (fromList (Z :. 6) [False,False,False,True,False,True]))
--
-- should be:
-- Vector (Z :. 6) [False,False,True,False,True,True]
shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL =
  stencil stencilf stencilBoundary where
    stencilf :: Stencil3 Bool -> Exp Bool
    stencilf (_, _, b) = b


stencilBoundary :: Boundary (Vector Bool)
stencilBoundary = function $ const True_

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> run $ shiftHeadFlagsR (use (fromList (Z :. 6) [True,False,False,True,False,False]))
--
-- should be:
-- Vector (Z :. 6) [True,True,False,False,True,False]
shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR =
  stencil stencilf stencilBoundary where
    stencilf :: Stencil3 Bool -> Exp Bool
    stencilf (b, _, _) = b

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ segmentedScanl1 (+) (use flags) (use values)
--
-- Expected answer:
-- >>> fromList (Z :. 9) [1, 1+2, 1+2+3, 4, 5, 5+6, 5+6+7, 5+6+7+8, 9] :: Vector Int
-- Vector (Z :. 9) [1,3,6,4,5,11,18,26,9]
--
-- Mind that the interpreter evaluates scans and folds sequentially, so
-- non-associative combination functions may seem to work fine here -- only to
-- fail spectacularly when testing with a parallel backend on larger inputs. ;)
segmentedScanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 op hFlags vec = map snd $ scanl1 (segmented op) $ zip hFlags vec

-- >>> import Data.Array.Accelerate.Interpreter
-- >>> let flags  = fromList (Z :. 9) [True,False,False,True,True,False,False,False,True]
-- >>> let values = fromList (Z :. 9) [1   ,2    ,3    ,4   ,5   ,6    ,7    ,8    ,9   ] :: Vector Int
-- >>> run $ segmentedScanr1 (+) (use flags) (use values)
--
-- Expected answer:
-- >>> fromList (Z :. 9) [1, 2+3+4, 3+4, 4, 5, 6+7+8+9, 7+8+9, 8+9, 9] :: Vector Int
-- Vector (Z :. 9) [1,9,7,4,5,30,24,17,9]
segmentedScanr1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 op hFlags vec = map snd $ scanr1 (flip $ segmented op) $ zip hFlags vec


makeInt :: Exp Bool -> Exp Int
makeInt b = if b then 1 else 0

-- Given utility functions
-- -----------------------

pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

nonNormalizedDistance :: Exp Line -> Exp Point -> Exp Int
nonNormalizedDistance (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y - c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

segmented :: Elt a => (Exp a -> Exp a -> Exp a) -> Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
segmented f (T2 aF aV) (T2 bF bV) = T2 (aF || bF) (if bF then bV else f aV bV)

-- | Read a file (such as "inputs/1.dat") and return a vector of points,
-- suitable as input to 'quickhull' or 'initialPartition'. Not to be used in
-- your quickhull algorithm, but can be used to test your functions in ghci.
readInputFile :: P.FilePath -> P.IO (Vector Point)
readInputFile filename =
  (\l -> fromList (Z :. P.length l) l)
  P.. P.map (\l -> let ws = P.words l in (P.read (ws P.!! 0), P.read (ws P.!! 1)))
  P.. P.lines
  P.<$> P.readFile filename
