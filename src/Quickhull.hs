{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeOperators #-}

module Quickhull
  ( Point,
    Line,
    SegmentedPoints,
    quickhull,
    -- Exported for display
    initialPartition,
    partition,
    -- Exported just for testing
    propagateL,
    shiftHeadFlagsL,
    segmentedScanl1,
    propagateR,
    shiftHeadFlagsR,
    segmentedScanr1,
  )
where

import Data.Array.Accelerate
import Data.Array.Accelerate.Debug.Trace
import qualified Prelude as P

-- Points and lines in two-dimensional space
--
type Point = (Int, Int)
type Line = (Point, Point)

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
  let p1, p2 :: Exp Point
      p1 = the $ fold leftmost (T2 maxBound maxBound) points
      p2 = the $ fold rightmost (T2 minBound minBound) points

      leftmost :: Exp Point -> Exp Point -> Exp Point --leftmost point, rightmost point after
      leftmost q1@(T2 x1 y1) q2@(T2 x2 y2) =
        if x1 < x2
          then q1
          else
            if x1 == x2
              then if y1 < y2 then q1 else q2
              else q2

      rightmost q1@(T2 x1 y1) q2@(T2 x2 y2) =
        if x1 > x2
          then q1
          else
            if x1 == x2
              then if y1 > y2 then q1 else q2
              else q2

      isUpper :: Acc (Vector Bool)
      isUpper = map (\p -> p /= p1 && p /= p2 && pointleftline (T2 p1 p2) p) points

      isLower :: Acc (Vector Bool)
      isLower = map (\p -> p /= p1 && p /= p2 && pointleftline (T2 p2 p1) p) points

      offsetUpper :: Acc (Vector Int)
      countUpper :: Acc (Scalar Int)
      T2 offsetUpper countUpper = T2 locations totalCount
        where
          isUpperInt = map makeInt isUpper
          locations :: Acc (Vector Int)
          locations = scanl (+) 0 isUpperInt
          totalCount = fold (+) 0 isUpperInt -- fold to get total number uppers

      offsetLower :: Acc (Vector Int)
      countLower :: Acc (Scalar Int)
      T2 offsetLower countLower = T2 locations totalcount
        where
          islowerint = map makeInt isLower
          locations :: Acc (Vector Int)
          locations = scanl (+) 0 islowerint
          totalcount = fold (+) 0 islowerint -- same for lower c:

      destination :: Acc (Vector (Maybe DIM1))
      destination = generate (shape points) $ \thing ->
        let point = points ! thing
            isUpperpoint = isUpper ! thing
            isLowerpoint = isLower ! thing
            offsetUpperpoint = offsetUpper ! thing
            offsetLowerpoint = offsetLower ! thing
            uppers = the countUpper
         in if point == p1
              then Just_ $ I1 0 --p1 start
              else
                if isUpperpoint
                  then Just_ $ I1 $ 1 + offsetUpperpoint --then uppers
                  else
                    if point == p2
                      then Just_ $ I1 $ uppers + 1 --p2
                      else
                        if isLowerpoint
                          then Just_ $ I1 $ 2 + uppers + offsetLowerpoint --then lowers
                          else Nothing_

      outShape = I1 $ 1 + the countUpper + 1 + the countLower + 1

      newPoints :: Acc (Vector Point)
      newPoints = generate outShape $ \(I1 thing) ->
        if thing == the countUpper + the countLower + 2
          then p1
          else withoutLastP1 ! (I1 thing)
        where
          withoutLastP1 =
            permute
              const
              (generate (I1 (unindex1 outShape - 1)) $ \_ -> T2 0 0)
              (\thing -> destination ! thing)
              points

      headFlags :: Acc (Vector Bool)
      headFlags = generate outShape $ \(I1 thing) ->
        thing == 0 || thing == the countUpper + 1 || thing == the countUpper + the countLower + 2
   in T2 headFlags newPoints

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
partition (T2 headFlags points) =
  let
      p1s = propagateL headFlags points --p1 val

      headIndices :: Acc (Vector Int) --p2 val
      headIndices = generate (shape headFlags) $ \(I1 i) ->
        if headFlags ! I1 i then i else maxBound

      nextHeadIndices :: Acc (Vector Int)
      nextHeadIndices = scanr1 min headIndices

      p2s :: Acc (Vector Point)
      p2s = generate (shape points) $ \(I1 i) ->
        points ! I1 (nextHeadIndices ! I1 i)

      distpoints =
        zipWith4
          ( \h p p1 p2 ->
              if h || p == p1 || p == p2
                then T2 (-1) p
                else T2 (nonNormalizedDistance (T2 p1 p2) p) p
          )
          headFlags
          points
          p1s
          p2s

      maxbydist :: Exp (Int, Point) -> Exp (Int, Point) -> Exp (Int, Point)
      maxbydist (T2 d1 p1@(T2 x1 y1)) (T2 d2 p2@(T2 x2 y2)) =
        if d1 > d2
          then T2 d1 p1
          else
            if d2 > d1
              then T2 d2 p2
              else -- tie=use max
                if x2 > x1
                  then T2 d1 p2
                  else
                    if x1 > x2
                      then T2 d1 p1
                      else
                        if y2 > y1
                          then T2 d1 p2
                          else T2 d1 p1

      bestPairs = segmentedScanl1 maxbydist headFlags distpoints

      isFurthest = -- furthest=newhead
        zipWith3
          (\h p (T2 _ bestPoint) -> not h && p == bestPoint)
          headFlags
          points
          bestPairs

      newHeadFlags = zipWith (||) headFlags isFurthest

      p3s = propagateL newHeadFlags points --p3 val

      leftofP1P3 =
        zipWith3
          ( \h p line ->
          not h && pointleftline line p)
          newHeadFlags
          points
          (zip p1s p3s)

      leftofP3P2 =
        zipWith3
          ( \h p line ->
          not h && pointleftline line p)
          newHeadFlags
          points
          (zip p3s p2s)

      keep = zipWith3 (\h l r -> h || l || r) newHeadFlags leftofP1P3 leftofP3P2

      offsets = scanl (+) 0 (map makeInt keep) --new indices
      newSize = fold (+) 0 (map makeInt keep)

      newPoints =
        permute
          const
          (generate (I1 $ the newSize) (const $ T2 0 0))
          (\i -> if keep ! i then Just_ (I1 (offsets ! i)) else Nothing_)
          points

      newHeadFlags' =
        permute
          const
          (generate (I1 (the newSize)) (const False_))
          (\i -> if keep ! i then Just_ (I1 (offsets ! i)) else Nothing_)
          newHeadFlags
   in T2 newHeadFlags' newPoints

-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull points =
  let cond :: Acc SegmentedPoints -> Acc (Scalar Bool)
      -- continue while at least 1 false flag
      cond (T2 headFlags _) =
        let undecided :: Acc (Scalar Int)
            undecided = fold (+) 0 (map makeInt (map not headFlags))
         in unit (the undecided > 0)

      step = partition

      initSeg = initialPartition points

      T2 finalFlags finalPoints = awhile cond step initSeg -- run dataparallel loop

      offsets = scanl (+) 0 (map makeInt finalFlags)

      total = fold (+) 0 (map makeInt finalFlags) -- acc scalar int

      compacted :: Acc (Vector Point)
      compacted =
        permute
          const
          (generate (I1 $ the total) (const $ T2 0 0))
          (\i -> if finalFlags ! i then Just_ (I1 (offsets ! i)) else Nothing_)
          finalPoints

      outShape = I1 (the total - 1) -- drop duplicated p1,, appended from initpartition mi bomboclat
   in generate outShape $ \(I1 thing) -> compacted ! (I1 thing)

-- Helper functions
-- ----------------

propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL = segmentedScanl1 (\a _ -> a)

propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR = segmentedScanr1 (\b _ -> b)

shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL = stencil stencilf stencilBoundary
  where
    stencilf :: Stencil3 Bool -> Exp Bool
    stencilf (_, _, b) = b

    stencilBoundary :: Boundary (Vector Bool)
    stencilBoundary = function $ const True_

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR = stencil stencilf stencilBoundary
  where
    stencilf :: Stencil3 Bool -> Exp Bool
    stencilf (b, _, _) = b

    stencilBoundary :: Boundary (Vector Bool)
    stencilBoundary = function $ const True_

segmentedScanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 op hFlags vec = map snd $ scanl1 (segmented op) $ zip hFlags vec

segmentedScanr1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 op hFlags vec = map snd $ scanr1 (flip $ segmented op) $ zip hFlags vec

makeInt :: Exp Bool -> Exp Int
makeInt b = if b then 1 else 0

-- Given utility functions
-- -----------------------

pointleftline :: Exp Line -> Exp Point -> Exp Bool
pointleftline (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c = nx * x1 + ny * y1

nonNormalizedDistance :: Exp Line -> Exp Point -> Exp Int
nonNormalizedDistance (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y - c
  where
    nx = y1 - y2
    ny = x2 - x1
    c = nx * x1 + ny * y1

segmented :: Elt a => (Exp a -> Exp a -> Exp a) -> Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
segmented f (T2 aF aV) (T2 bF bV) = T2 (aF || bF) (if bF then bV else f aV bV)

readInputFile :: P.FilePath -> P.IO (Vector Point)
readInputFile filename =
  (\l -> fromList (Z :. P.length l) l)
    P.. P.map (\l -> let ws = P.words l in (P.read (ws P.!! 0), P.read (ws P.!! 1)))
    P.. P.lines
    P.<$> P.readFile filename