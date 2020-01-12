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
-- import Data.Array.Accelerate.LLVM.Native
-- import Data.Array.Accelerate.LLVM.PTX

type Point = (Int, Int)

type Line = (Point, Point)

type SegmentedPoints = (Vector Bool, Vector Point)

--Left == Upper?
pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
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
  (\p1 p2 -> ifThenElse ((fst p1) < (fst p2)) p1 p2)
  points

  --Rightmost: Hoogste x
rightMostPoint :: Acc (Vector Point) -> Acc (Scalar Point)
rightMostPoint points = fold1
  (\p1 p2 -> ifThenElse ((fst p1) > (fst p2)) p1 p2)
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
      let isLowerInt = map toInt isLower
          toInt bool = ifThenElse bool 1 0
      in prescanl (+) 0 isLowerInt

    -- * Exercise 4
    upperIndices :: Acc (Vector Int)
    countUpper :: Acc (Scalar Int)
    T2 upperIndices countUpper = 
      let
        isUpperInt = map toInt isUpper
        toInt bool = ifThenElse bool 1 0       
      in scanl' (+) 1 isUpperInt              --MOET SCAN NIET EXCLUSIEF??

    -- * Exercise 5
    permutation :: Acc (Vector (Z :. Int))
    permutation =
      let
        countUpperExp = the countUpper

        f :: Exp Point -> Exp Bool -> Exp Int -> Exp Int -> Exp (Z :. Int)
        f p upper idxLower idxUpper = 
          ifThenElse upper
            (index1 idxUpper)
            (caseof p
              [ ((\p -> equal p p1), index1 0),
                ((\p -> equal p p2), index1 countUpperExp)
              ] (index1 $ countUpperExp + idxLower + 1))
      in
        zipWith4 f points isUpper lowerIndices upperIndices

    -- * Exercise 6
    empty :: Acc (Vector Point)
    empty = 
      let oldsh = shape points
          sh = ilift1 (\x -> (x + 1)) oldsh
      in fill sh p1

    newPoints :: Acc (Vector Point)
    newPoints = permute const empty (permutation !) points

    -- * Exercise 7
    headFlags :: Acc (Vector Bool)
    headFlags =
      let oldsh = shape points
          sh = ilift1 (\x -> (x + 1)) oldsh
      in generate sh (\ind -> isExtreme $ newPoints ! ind)
  in
    T2 headFlags newPoints

-- * Exercise 8
segmentedPostscanl :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedPostscanl f bools units = 
  let fs (fx, x) (fy, y) = (fx || fy, fy ? (y, (f x y)))
      tupled = zip bools units
      scan = postscanl (lift2 fs) (T2 (constant False) Unsafe.undef) tupled
  in P.snd $ unzip scan

segmentedPostscanr :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedPostscanr f bools units =
  let fs (fx, x) (fy, y) = (fx || fy, fx ? (x, (f x y)))
      tupled = zip bools units
      scan = postscanr (lift2 fs) (T2 (constant False) Unsafe.undef) tupled
  in P.snd $ unzip scan

-- * Exercise 9
propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL = segmentedPostscanl const

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
  in generate (shape flags) (\ind -> f (unindex1 ind))

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR flags = 
  let f i = 
        (i == (0)) ?
        ((constant False),
        (flags !! (i - 1)))
  in generate (shape flags) (\ind -> f (unindex1 ind))

partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) =
  let
    vecLine :: Acc (Vector Line)
    vecLine = propagateLine (T2 headFlags points)

    headFlagsL = shiftHeadFlagsL headFlags
    headFlagsR = shiftHeadFlagsR headFlags

    -- * Exercise 12
    furthest :: Acc (Vector Point)
    furthest = undefined

    -- * Exercise 13
    isLeft :: Acc (Vector Bool)
    isLeft = undefined

    isRight :: Acc (Vector Bool)
    isRight = undefined

    -- * Exercise 14
    segmentIdxLeft :: Acc (Vector Int)
    segmentIdxLeft = undefined

    segmentIdxRight :: Acc (Vector Int)
    segmentIdxRight = undefined

    -- * Exercise 15
    countLeft :: Acc (Vector Int)
    countLeft = undefined

    -- * Exercise 16
    segmentSize :: Acc (Vector Int)
    segmentSize = undefined

    segmentOffset :: Acc (Vector Int)
    size :: Acc (Scalar Int)
    T2 segmentOffset size = undefined

    -- * Exercise 17
    permutation :: Acc (Vector (Z :. Int))
    permutation =
      let
        f :: Exp Bool -> Exp Point -> Exp Point -> Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp Int -> Exp Int -> Exp (Z :. Int)
        f flag p furthestP left right offset cntLeft idxLeft idxRight
          = undefined
      in
        zipWith9 f headFlags points furthest isLeft isRight segmentOffset countLeft segmentIdxLeft segmentIdxRight

    -- * Exercise 18
    empty :: Acc (Vector Point)
    empty = undefined

    newPoints :: Acc (Vector Point)
    newPoints = undefined

    -- * Exercise 19
    newHeadFlags :: Acc (Vector Bool)
    newHeadFlags = undefined
  in
    T2 newHeadFlags newPoints

-- * Exercise 20
condition :: Acc SegmentedPoints -> Acc (Scalar Bool)
condition = undefined

-- * Exercise 21
quickhull' :: Acc (Vector Point) -> Acc (Vector Line)
quickhull' = propagateLine . initialPartition

quickhull :: Vector Point -> Vector Line
quickhull = run1 quickhull'

-- * Bonus
quickhullSort' :: Acc (Vector Int) -> Acc (Vector Int)
quickhullSort' = undefined

quickhullSort :: Vector Int -> Vector Int
quickhullSort = run1 quickhullSort'

-- -- * Exercise 21
-- quickhull' :: Acc (Vector Point) -> Acc (Vector Point)
-- quickhull' = undefined

-- quickhull :: Vector Point -> Vector Point
-- quickhull = run1 quickhull'

-- -- * Bonus
-- quickhullSort' :: Acc (Vector Int) -> Acc (Vector Int)
-- quickhullSort' = undefined

-- quickhullSort :: Vector Int -> Vector Int
-- quickhullSort = run1 quickhullSort'
