module Sift.Verify
  ( satisfies
  , clauseSatisfied
  , completeModel
  ) where

import Sift.Types
import qualified Data.Map.Strict as Map

clauseSatisfied :: Assignment -> Clause -> Bool
clauseSatisfied asn = any ((== Just True) . litValue asn)

satisfies :: Assignment -> CNF -> Bool
satisfies asn (CNF cs) = all (clauseSatisfied asn) cs

completeModel :: CNF -> Assignment -> Assignment
completeModel cnf asn =
  foldr insertDefault asn (allVars cnf)
  where
    insertDefault v m = if Map.member v m then m else Map.insert v True m
