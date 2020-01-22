{-# LANGUAGE TypeOperators #-}

module Quickhull
    ( quickhull
    , Point
    , propagateR
    , segmentedPostscanr
    ) where

import Data.Array.Accelerate
import qualified Data.Array.Accelerate.Unsafe as Unsafe
import qualified Prelude as P

-- Accelerate backend
import Data.Array.Accelerate.Interpreter 
--import Data.Array.Accelerate.LLVM.Native
--import Data.Array.Accelerate.LLVM.PTX

type Point = (Int, Int)

type Line = (Point, Point)

type SegmentedPoints = (Vector Bool, Vector Point)

input1 :: Acc (Vector Point)
input1 = use $ fromList (Z :. 15) [(1,4),(8,19),(5,9),(7,9),(4,2),(3,9),(9,16),(1,5),(9,11),(4,0),(8,18),(8,7),(7,18),(6,18),(4,19)]

--Left == Upper?
pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c = nx * x1 + ny * y1

pointIsRightOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsRightOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y < c
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

-- * Exercise 1
--Leftmost: Laagste x
leftMostPoint :: Acc (Vector Point) -> Acc (Scalar Point)
leftMostPoint points = fold1
  (\p1 p2 -> ifThenElse ((fst p1) <= (fst p2)) p1 p2) -- '<' instead of '<=' to take first extreme point
  points

  --Rightmost: Hoogste x
rightMostPoint :: Acc (Vector Point) -> Acc (Scalar Point)
rightMostPoint points = fold1
  (\p1 p2 -> ifThenElse ((fst p1) >= (fst p2)) p1 p2) -- '>' instead of '>=' to take first extreme point
  points

initialPartition :: Acc (Vector Point) -> Acc SegmentedPoints
initialPartition points =
  let
    p1 = the $ leftMostPoint points
    p2 = the $ rightMostPoint points
    line = T2 p1 p2

    isExtreme point = (equal point p1) || (equal point p2)
    equal (T2 x1 y1) (T2 x2 y2) = (x1 == x2) && (y1 == y2)

    -- * Exercise 2
    isUpper :: Acc (Vector Bool)
    isUpper = generate 
      (shape points) 
      (\sh -> pointIsLeftOfLine line (points ! sh))

    isLower :: Acc (Vector Bool)
    isLower = 
      let notUpper sh = not (isUpper ! sh)
          notExtreme sh = not (isExtreme $ points ! sh)
      in 
        generate 
          (shape points) 
          (\sh -> notUpper sh && notExtreme sh)

    -- * Exercise 3
    lowerIndices :: Acc (Vector Int)
    lowerIndices = 
      let isLowerInt = map boolToInt isLower
      in prescanl (+) 0 isLowerInt

    -- * Exercise 4
    upperIndices :: Acc (Vector Int)
    countUpper :: Acc (Scalar Int)
    T2 upperIndices countUpper = 
      let isUpperInt = map boolToInt isUpper
      in scanl' (+) 1 isUpperInt

    -- * Exercise 5
    permutation :: Acc (Vector (Z :. Int))
    permutation =
      let
        f :: Exp Point -> Exp Bool -> Exp Int -> Exp Int -> Exp (Z :. Int)
        f p upper idxLower idxUpper = 
          ifThenElse upper
            (index1 idxUpper)
            (caseof p
              [ ((equal p1), index1 0),
                ((equal p2), index1 $ the countUpper)
              ] (index1 $ (the countUpper) + idxLower + 1))
      in
        zipWith4 f points isUpper lowerIndices upperIndices

    -- * Exercise 6
    empty :: Acc (Vector Point)
    empty = 
      let oldsh = shape points
          sh = ilift1 (1 +) oldsh
      in fill sh p1

    newPoints :: Acc (Vector Point)
    newPoints = permute const empty (permutation !) points

    -- * Exercise 7
    headFlags :: Acc (Vector Bool)
    headFlags =
      let oldsh = shape points
          sh = ilift1 (1 +) oldsh
      in generate sh (\ind -> isExtreme $ newPoints ! ind)
  in
    T2 headFlags newPoints

-- * Exercise 8
segmentedPostscanl :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedPostscanl f bools units = 
  let fs (fx, x) (fy, y) = (fx || fy, fy ? (y, f x y))
      tuples = zip bools units
      scan = postscanl (lift2 fs) (T2 (constant False) Unsafe.undef) tuples
  in P.snd $ unzip scan

segmentedPostscanr :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedPostscanr f bools units =                      
  let fs (fx, x) (fy, y) = (fx || fy, fx ? (x, f x y))  --Werkt de functie op dezelfde volgorde??
      tuples = zip bools units
      scan = postscanr (lift2 fs) (T2 (constant False) Unsafe.undef) tuples
  in P.snd $ unzip scan

-- * Exercise 9
-- As how these functions are implemented their behaviour is exactly opposite of how there behaviours are defined in the exercise.
-- Because postscanL will scan from left to right, while propagateL is defined as propagating a value from right to the left.
propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL = segmentedPostscanl const

-- Idem dito, respectively
propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR = segmentedPostscanr (P.flip const)

-- * Exercise 10
propagateLine :: Acc SegmentedPoints -> Acc (Vector Line)
propagateLine (T2 headFlags points) = zip vecP1 vecP2
  where
    vecP1 = propagateL headFlags points
    vecP2 = propagateR headFlags points

-- * Exercise 11
shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL flags = 
  let f i = 
        (i == (size flags) - 1) ? 
        ((constant False), 
        (flags !! (i + 1)))
  in generate (shape flags) (f . unindex1)

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR flags = 
  let f i = 
        (i == (0)) ?
        ((constant False),
        (flags !! (i - 1)))
  in generate (shape flags) (f . unindex1)

partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) =
  let
    vecLine :: Acc (Vector Line)
    vecLine = propagateLine (T2 headFlags points)

    equal (T2 x1 y1) (T2 x2 y2) = (x1 == x2) && (y1 == y2)

    headFlagsL = shiftHeadFlagsL headFlags
    headFlagsR = shiftHeadFlagsR headFlags

    -- * Exercise 12
    furthest :: Acc (Vector Point)
    furthest = 
      let d t = nonNormalizedDistance (fst t) (snd t)
          maxD t1 t2 = (d t1) > (d t2) ? (t1, t2)
          maxEnd = P.snd $ unzip $ segmentedPostscanl maxD headFlagsR (zip vecLine points)
      in propagateR headFlagsL maxEnd

    -- * Exercise 13
    isLeft :: Acc (Vector Bool)
    isLeft = zipWith3 (\(T2 p1 p2) pf p -> pointIsLeftOfLine (T2 p1 pf) p) vecLine furthest points

    isRight :: Acc (Vector Bool)
    isRight = zipWith3 (\(T2 p1 p2) pf p -> pointIsRightOfLine (T2 p2 pf) p) vecLine furthest points

    -- * Exercise 14
    segmentIdxLeft :: Acc (Vector Int)
    segmentIdxLeft = 
      let isLeftInt = map boolToInt isLeft
      in segmentedPostscanl (+) headFlags isLeftInt

    -- Works the same as segmentIdxLeft, however here we look if the point isRight:
    segmentIdxRight :: Acc (Vector Int)
    segmentIdxRight = 
      let isRightInt = map boolToInt isRight
      in segmentedPostscanl (+) headFlags isRightInt

    -- * Exercise 15
    countLeft :: Acc (Vector Int)
    countLeft = propagateR headFlagsL segmentIdxLeft

    -- * Exercise 16
    segmentSize :: Acc (Vector Int)
    segmentSize = zipWith3 (\hi c hfl -> hfl ? (c, hi)) headInts count headFlagsL
      where
        headInts = map boolToInt headFlags
        count = zipWith (\l r -> 1 + l + r) segmentIdxLeft segmentIdxRight

    segmentOffset :: Acc (Vector Int)
    size :: Acc (Scalar Int)
    T2 segmentOffset size = scanl' (+) 0 segmentSize

    -- * Exercise 17
    permutation :: Acc (Vector (Z :. Int))
    permutation =
      let
        f :: Exp Bool -> Exp Point -> Exp Point -> Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp Int -> Exp Int -> Exp (Z :. Int)
        f flag p furthestP left right offset cntLeft idxLeft idxRight = 
          caseof (T4 flag left right (equal p furthestP))
            [ ((\(T4 f l r p) -> f), index1 offset),
              ((\(T4 f l r p) -> l), index1 $ offset + idxLeft - 1),
              ((\(T4 f l r p) -> r), index1 $ offset + cntLeft + idxRight),
              ((\(T4 f l r p) -> p), index1 $ offset + cntLeft)
            ] ignore    
      in
        zipWith9 f headFlags points furthest isLeft isRight segmentOffset countLeft segmentIdxLeft segmentIdxRight

    -- * Exercise 18
    -- fill a vector with as shape the shape of permuation and as values the first point from points
    empty :: Elt a => Acc (Vector a)
    empty = fill (index1 $ the size) Unsafe.undef

    -- permute the values from the permuation which do not have 'ignore' to the empty list
    newPoints :: Acc (Vector Point)
    newPoints = permute const empty (permutation !) points

    -- * Exercise 19
    newHeadFlags :: Acc (Vector Bool)
    newHeadFlags = 
      let zeros = fill (index1 $ the size) (constant False)
          ones = fill (shape segmentSize) (constant True)
      in permute const zeros (\ix -> index1 $ segmentOffset!ix + (headFlags!ix ? (0, countLeft!ix))) ones
    -- --newHeadFlags = zipWith3 (\f fp p -> f || (equal fp p)) headFlags furthest newPoints
    -- newHeadFlags =
    --   let defaultFlags = fill (index1 $ the size) (constant False)
    --       toPermute = fill (shape segmentSize) (constant True)
    --   in permute const defaultFlags (\ix -> index1 (segmentOffset!ix)) toPermute

  in
    T2 newHeadFlags newPoints

-- * Exercise 20
condition :: Acc SegmentedPoints -> Acc (Scalar Bool)
condition (T2 flags points) = any not flags

-- * Exercise 21
quickhull' :: Acc (Vector Point) -> Acc (Vector Point)
quickhull' input = asnd $ awhile condition partition (initialPartition input)
--quickhull' input = awhile condition partition (initialPartition input)
--quickhull' input = asnd $ partition $ partition $ partition $ partition $ initialPartition input
--quickhull' input = asnd $ partition $ initialPartition input
--quickhull' input = afs $ partition $ partition $ initialPartition input

quickhull :: Vector Point -> Vector Point
quickhull = run1 quickhull'

-- * Bonus
quickhullSort' :: Acc (Vector Int) -> Acc (Vector Int)
quickhullSort' = undefined

quickhullSort :: Vector Int -> Vector Int
quickhullSort = run1 quickhullSort'