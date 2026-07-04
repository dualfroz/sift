{-# LANGUAGE FlexibleContexts #-}
module Sift.Cdcl.Heap
  ( VarHeap
  , newHeap
  , heapInsert
  , heapIncrease
  , heapRemoveMax
  , heapInHeap
  , heapIsEmpty
  ) where

import Control.Monad (when)
import Control.Monad.ST (ST)
import Data.STRef
import Data.Array.ST

data VarHeap s = VarHeap
  { hArr  :: STUArray s Int Int
  , hPos  :: STUArray s Int Int
  , hSize :: STRef s Int
  , hAct  :: STUArray s Int Double
  }

newHeap :: Int -> STUArray s Int Double -> ST s (VarHeap s)
newHeap n act = do
  arr  <- newArray (0, n - 1) 0
  pos  <- newArray (0, n - 1) (-1)
  size <- newSTRef 0
  pure (VarHeap arr pos size act)

heapInHeap :: VarHeap s -> Int -> ST s Bool
heapInHeap h v = do
  p <- readArray (hPos h) v
  pure (p >= 0)

heapIsEmpty :: VarHeap s -> ST s Bool
heapIsEmpty h = do
  n <- readSTRef (hSize h)
  pure (n == 0)

heapInsert :: VarHeap s -> Int -> ST s ()
heapInsert h v = do
  present <- heapInHeap h v
  when (not present) $ do
    n <- readSTRef (hSize h)
    writeArray (hArr h) n v
    writeArray (hPos h) v n
    writeSTRef (hSize h) (n + 1)
    siftUp h n

heapIncrease :: VarHeap s -> Int -> ST s ()
heapIncrease h v = do
  p <- readArray (hPos h) v
  when (p >= 0) $ siftUp h p

heapRemoveMax :: VarHeap s -> ST s Int
heapRemoveMax h = do
  n    <- readSTRef (hSize h)
  top  <- readArray (hArr h) 0
  lastV <- readArray (hArr h) (n - 1)
  writeArray (hArr h) 0 lastV
  writeArray (hPos h) lastV 0
  writeArray (hPos h) top (-1)
  writeSTRef (hSize h) (n - 1)
  when (n - 1 > 0) $ siftDown h 0
  pure top

siftUp :: VarHeap s -> Int -> ST s ()
siftUp h start = do
  x  <- readArray (hArr h) start
  ax <- readArray (hAct h) x
  let go j
        | j <= 0    = finish j
        | otherwise = do
            let parent = (j - 1) `div` 2
            yp <- readArray (hArr h) parent
            ay <- readArray (hAct h) yp
            if ax > ay
              then do
                writeArray (hArr h) j yp
                writeArray (hPos h) yp j
                go parent
              else finish j
      finish j = do
        writeArray (hArr h) j x
        writeArray (hPos h) x j
  go start

siftDown :: VarHeap s -> Int -> ST s ()
siftDown h start = do
  n  <- readSTRef (hSize h)
  x  <- readArray (hArr h) start
  ax <- readArray (hAct h) x
  let go j = do
        let l = 2 * j + 1
        if l >= n
          then finish j
          else do
            let r = l + 1
            cl  <- readArray (hArr h) l
            acl <- readArray (hAct h) cl
            (childIdx, childVar, childAct) <-
              if r < n
                then do
                  cr  <- readArray (hArr h) r
                  acr <- readArray (hAct h) cr
                  if acr > acl
                    then pure (r, cr, acr)
                    else pure (l, cl, acl)
                else pure (l, cl, acl)
            if childAct > ax
              then do
                writeArray (hArr h) j childVar
                writeArray (hPos h) childVar j
                go childIdx
              else finish j
      finish j = do
        writeArray (hArr h) j x
        writeArray (hPos h) x j
  go start
