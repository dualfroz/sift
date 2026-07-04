module Sift.Stats
  ( Stats(..)
  , emptyStats
  , renderStats
  ) where

data Stats = Stats
  { statsDecisions    :: Int
  , statsConflicts    :: Int
  , statsPropagations :: Int
  , statsRestarts     :: Int
  , statsLearned      :: Int
  , statsRemoved      :: Int
  } deriving (Eq, Show)

emptyStats :: Stats
emptyStats = Stats 0 0 0 0 0 0

renderStats :: Stats -> [String]
renderStats st =
  [ "c decisions    " ++ show (statsDecisions st)
  , "c conflicts     " ++ show (statsConflicts st)
  , "c propagations  " ++ show (statsPropagations st)
  , "c restarts      " ++ show (statsRestarts st)
  , "c learned       " ++ show (statsLearned st)
  , "c removed       " ++ show (statsRemoved st)
  ]
