{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

import Prelude hiding ( )

import Data.Foldable hiding ( msum )
import Control.Monad
import Control.Monad.State ( StateT (..) )
import Control.Applicative

import Text.Read

import Data.Char
import Data.Set ( Set (..), union, isSubsetOf, intersection )

import qualified Data.Set as Set


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
type Touchables = Set FUV


type Subst = ()



dom :: Subst -> Set FUV 
dom = undefined  
  
fuv :: Constraint -> Set FUV
fuv = undefined
 

data FUV = FUV String
  deriving (Show, Eq)
instance Enum FUV where
  toEnum n = if n >= 0 && n < 0 + lowercaseRange
                then FUV $ [chr (ord 'a' + n)]
                else FUV $ show (n - lowercaseRange) where
    lowercaseRange = ord 'z' - ord 'a' + 1 
  fromEnum (FUV s) = 
    let lowercaseRange = ord 'z' - ord 'a' + 1
        parseChar (x:[]) = if ord x >= ord 'a' && ord x <= ord 'z'
                              then Just $ ord x - ord 'a'
                              else Nothing
        parseChar _ = Nothing
    in case msum [ parseChar s :: Maybe Int
                 , fmap (\t -> t + lowercaseRange) . readMaybe $ s :: Maybe Int
                 ] of Just n -> n
                      _      -> error "fromEnum: invalid FUV" 
instance Ord FUV where
  compare a b = compare (fromEnum a) (fromEnum b)
       
  
  
data Error a = Error String | Value a
 deriving Show
instance Functor Error where
  fmap f (Error a) = Error a
  fmap f (Value a) = Value (f a)
instance Monad Error where
  Error a >>= f = Error a
  Value a >>= f = f a
  
  return = Value
  fail = Error
  
type Solver a = StateT FUV Error a

                                      
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
 
(#) :: Set FUV -> Set FUV -> Bool
a # b = Set.null (a `intersection` b) 
 

free :: Solver FUV
free = StateT $ \fuv -> Value (fuv, succ fuv)
 
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
          fail $ "solver: could not fully discharge implication constraint because <insert reason here>"
  
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

  
  

