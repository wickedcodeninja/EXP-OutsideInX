{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

import Prelude hiding ( )

import Data.Foldable
import Control.Monad
import Control.Applicative


import Data.Set ( Set (..), union, isSubsetOf, intersection )
import qualified Data.Set as Set



type Var = ()

-- Always associate to right? Maybe 
data Constraint = And Constraint Constraint | Empty
  deriving (Eq, Ord)
data ImplicationConstraint = Implication Constraint ExtendedConstraint Touchables
  deriving (Eq, Ord)
type ExtendedConstraint = (Constraint, [ImplicationConstraint])


simplePart :: ExtendedConstraint -> Constraint
simplePart (c, _) = c

implicationPart :: ExtendedConstraint -> [ImplicationConstraint]
implicationPart (_, i) = i

type Toplevel = ()
type Touchables = Set Var


type Subst = ()



dom :: Subst -> Set Var  
dom = undefined  
  
fuv :: Constraint -> Set Var
fuv = undefined
  
type Solver a = Either String a

oops :: String -> Solver a
oops = Left 

class SubstApply a where
  applySubst :: Subst -> a -> a

instance SubstApply ExtendedConstraint where
  applySubst subst (c, is) 
    = (applySubst subst c, map (applySubst subst) is)

instance SubstApply ImplicationConstraint where
  applySubst subst (Implication c e tch) -- assert tch # fuv(subst) ?
    = Implication (applySubst subst c) (applySubst subst e) tch

instance SubstApply Constraint where
  applySubst subst _ 
    = error "Substitutions on Constraints not implemented yet"
 
assert :: Bool -> String -> Solver ()
assert b s = if b then return () else error s
 
(#) :: Set Var -> Set Var -> Bool
a # b = Set.null (a `intersection` b) 
 

solver :: Toplevel                    --Top-level constraints
       -> Constraint                  --Q_Given
       -> Touchables                  --Touchables
       -> ExtendedConstraint          --C_Wanted                
       -> Solver (Constraint, Subst)  --(Q_Residual; Subst)
solver tl given tch wanted = do
  (residual, subst) <- simplifier tl given tch (simplePart wanted)
  
  assert (dom subst # fuv given) $ "solver: domain of substitution is not disjoint from fuv(given)" 
  assert (dom subst `isSubsetOf` tch) $ "solver: domain of substitution not a subset of touchables" 
  
  let simplifiedWanted = map (applySubst subst) (implicationPart wanted)
  
      recSolver (Implication q_i c_i tch_i) = do
        (r_i, subst_i) <- solver tl (given `And` (residual `And` q_i)) tch_i c_i
        
        when (r_i /= Empty) $ 
          oops $ "solver: could not fully discharge implication constraint because <insert reason here>"
  
  -- Recursively solve all the implication constraints, discarding generated substitutions
  -- which are internal to the implication constraint.
  _ <- traverse_ recSolver simplifiedWanted
  
  --   
  return (residual, subst)
  
  
simplifier :: Toplevel                     --Top-level constraints
           -> Constraint                   --Q_Given
           -> Touchables                   --Touchables
           -> Constraint                   --Q_Wanted
           -> Solver (Constraint, Subst)   --(Q_Residual; Subst)
simplifier = undefined

  
  

