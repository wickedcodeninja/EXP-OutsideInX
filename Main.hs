{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, LambdaCase #-}

import Prelude hiding ( null )

import Data.Monoid
import Data.Foldable hiding ( msum )

import Control.Monad
import Control.Monad.State ( StateT (..) )
import Control.Applicative

import Text.Read

import Data.Char
import Data.Set ( Set (..), union, isSubsetOf, intersection )

import qualified Data.Set as Set
import qualified Data.Map as Map

data Equality = Equality
  deriving (Eq, Ord)
   
data Constraint 
  = EqualityConstraint Equality 
  | TypeclassConstraint
  deriving (Eq, Ord)

data Implication 
  = Implication (Set Constraint) (Set ExtendedConstraint) Touchables
  deriving (Eq, Ord)

data ExtendedConstraint 
  = BaseConstraint Constraint 
  | ImplicationConstraint Implication
  deriving (Eq, Ord)

unionMap :: (Ord a, Ord b) => Set a -> (a -> Set b) -> Set b
unionMap m f = flatten (Set.map f m)

flatten :: Ord a => Set (Set a) -> Set a
flatten = Set.unions . toList

simplePart :: Set ExtendedConstraint -> Set Constraint
simplePart m = unionMap m $ \case BaseConstraint b        -> Set.singleton b
                                  ImplicationConstraint i -> Set.empty
                                    
implicationPart :: Set ExtendedConstraint -> Set Implication
implicationPart m = unionMap m $ \case BaseConstraint _        -> Set.empty
                                       ImplicationConstraint i -> Set.singleton i
                                    

type Toplevel = ()
type Touchables = Set FUV


data Subst = Subst (Map.Map FUV ())

instance Monoid Subst where
  mempty = Subst Map.empty
  a `mappend` b = undefined


dom :: Subst -> Set FUV 
dom = undefined  
  
fuv :: Set Constraint -> Set FUV
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
  applySubst subst (BaseConstraint b) = BaseConstraint (applySubst subst b)
  applySubst subst (ImplicationConstraint i) = ImplicationConstraint (applySubst subst i)
  

instance SubstApply Implication where
  applySubst subst (Implication c e tch) -- assert tch # fuv(subst) ?
    = Implication (applySubst subst c) (applySubst subst e) tch

instance SubstApply Constraint where
  applySubst subst _ 
    = error "Substitutions on Constraints not implemented yet"

instance SubstApply a => SubstApply (Set a) where
  applySubst = undefined
    
release_mode :: Bool
release_mode = False
 
assert :: Bool -> String -> Solver ()
assert b s = if (release_mode || b) then return () else error s
 
(#) :: Set FUV -> Set FUV -> Bool
a # b = Set.null (a `intersection` b) 
 

free :: Solver FUV
free = StateT $ \fuv -> Value (fuv, succ fuv)
 
solver :: Toplevel                    --Top-level constraints
       -> Set Constraint              --Q_Given
       -> Touchables                  --Touchables
       -> Set ExtendedConstraint      --C_Wanted                
       -> Solver (Set Constraint, Subst)  --(Q_Residual; Subst)
solver tl given tch wanted = do
  (residual, subst) <- simplifier tl given tch (simplePart wanted)
  
  assert (dom subst # fuv given) $ "solver: domain of substitution is not disjoint from fuv(given)" 
  assert (dom subst `isSubsetOf` tch) $ "solver: domain of substitution not a subset of touchables" 
  
  let simplifiedWanted = Set.map (applySubst subst) (implicationPart wanted)
  
      recSolver (Implication q_i c_i tch_i) = do
        (r_i, subst_i) <- solver tl (given `union` (residual `union` q_i)) tch_i c_i
        
        when (not $ Set.null r_i) $ 
          fail $ "solver: could not fully discharge implication constraint because <insert reason here>"
  
  -- Recursively solve all the implication constraints, discarding generated substitutions
  -- which are internal to the implication constraint.
  _ <- traverse_ recSolver simplifiedWanted
  
  --   
  return (residual, subst)
  
type Quadruple = (Touchables, Subst, Set Constraint, Set Constraint)
  
-- Rewrite the quadruple until no more rewrite steps are possible
rewriter :: Toplevel -> Quadruple -> Solver Quadruple
rewriter tl = return
  
-- page 66: 7.5, (2)
seperateEqualities :: Set Constraint -> ( Set Equality    -- Type Equalities
                                        , Set Constraint  -- Residual
                                        )
seperateEqualities = undefined



-- page 66: 7.5, (3)
extractSubstitution :: Set Equality -> Subst
extractSubstitution = undefined

-- page 66: 7.5, SIMPLES
restrictSubstitution :: Touchables -> Subst -> Subst
restrictSubstitution = undefined


simplifier :: Toplevel                         -- Top-level constraints
           -> Set Constraint                   -- Q_Given
           -> Touchables                       -- Touchables
           -> Set Constraint                   -- Q_Wanted
           -> Solver (Set Constraint, Subst)   -- (Q_Residual; Subst)
simplifier tl oldGiven oldTouch oldWanted = 
  do (newTouch, phi, newGiven, newWanted) <- rewriter tl (oldTouch, mempty, oldGiven, oldWanted)
     let (eqPart, residual) = seperateEqualities (phi `applySubst` newWanted)
         theta = restrictSubstitution oldTouch . extractSubstitution $ eqPart
         substitutedResidual = theta `applySubst` residual
         
     assert (dom theta `isSubsetOf` oldTouch) $ "simplifier: substitution concerns non-touchable variables" 
     assert (dom theta # fuv substitutedResidual) $ "simplifier: domain of final substitution should be disjoint from residual"
     
     return $ (substitutedResidual, theta)
  
  

