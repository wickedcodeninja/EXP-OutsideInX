{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, LambdaCase #-}

import Prelude hiding ( null, interact )

import Data.Monoid
import Data.Foldable hiding ( msum )
import Data.Traversable

import Control.Monad
import Control.Monad.State ( StateT (..) )
import Control.Applicative

import Text.Read

import Data.Maybe
import Data.Char
import Data.Set ( Set (..), union, singleton, isSubsetOf, intersection )

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
simplePart m = unionMap m $ \case BaseConstraint b        -> singleton b
                                  ImplicationConstraint i -> Set.empty
                                    
implicationPart :: Set ExtendedConstraint -> Set Implication
implicationPart m = unionMap m $ \case BaseConstraint _        -> Set.empty
                                       ImplicationConstraint i -> singleton i
                                    

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

disjointMerge :: Subst -> Subst -> Subst
disjointMerge (Subst a) (Subst b) = Subst $ Map.unionWith (\a b -> {- TODO: CHECK SEMANTICS -} a) a b

pick :: Int -> [a] -> [[a]]
pick 0 _ = [[]]
pick _ [] = []
pick n (x : xs) = map (x :) (pick (n - 1) xs) ++ pick n xs

data Role 
  = Wanted 
  | Given
  deriving (Eq, Show) 
type Quadruple = (Touchables, Subst, Set Constraint, Set Constraint)


pickFirst :: Monad m => [m (Maybe a)] -> m (Maybe a) 
pickFirst [] = return Nothing
pickFirst (x : xs) = do r <- x
                        case r of 
                          Nothing -> pickFirst xs
                          a@(Just _)  -> return a

                          
canon :: Role -> Constraint -> Solver (Maybe (Touchables, Subst, Set Constraint))
canon = undefined
                          
-- Try to canonicalize one atomic constraint. The atomic constraints from the given/wanted 
-- list are tried one at a time. The rule either succeeds directly after the first success
-- or returns Nothing if all constraints are already canonic.
                          
ruleCanon :: Role -> Quadruple -> Solver (Maybe Quadruple)
ruleCanon role (tch, subst, given, wanted) = pickFirst . map attempt $ choices where
      pivot = case role of 
                Given  -> given
                Wanted -> wanted
  
      choices :: [(Constraint, Set Constraint)]
      choices = map (\[q1] -> (q1, Set.difference pivot . singleton $ q1) ) . pick 1 . Set.toList $ pivot
 
      attempt :: (Constraint, Set Constraint) -> Solver (Maybe Quadruple)
      attempt (q1, rest) = (`fmap` canon role q1) $ \r ->
        do (tch', subst', q2) <- r
           let replaced = Set.union q2 rest

               (given', wanted') = case role of
                                     Given  -> (replaced, wanted)
                                     Wanted -> (given,  replaced)

           return $ ( Set.union     tch   tch'
                    , disjointMerge subst subst'
                    , given'
                    , wanted'
                    )

interact :: Role -> Constraint -> Constraint -> Solver (Maybe (Set Constraint))
interact = undefined

-- Generate all pairs of atomic constraints from the given/wanted list and try to let
-- them interact one at a time. The rule either succeeds directly after the first success 
-- or returns Nothing if no interacting pairs were found.
ruleInteract :: Role -> Quadruple -> Solver (Maybe Quadruple)
ruleInteract role (tch, subst, given, wanted) = pickFirst . map attempt $ choices where
      pivot = case role of 
                Given  -> given
                Wanted -> wanted
  
      -- Generate all possible pairs of atomic constraints from the given/wanted list
      choices :: [(Constraint, Constraint, Set Constraint)]
      choices = map (\q@[q1, q2] -> (q1, q2, Set.difference pivot . Set.fromList $ q) ) . pick 2 . Set.toList $ pivot
      
      -- Let one pair interact
      attempt :: (Constraint, Constraint, Set Constraint) -> Solver (Maybe Quadruple)
      attempt (q1, q2, rest) = (`fmap` interact role q1 q2) $ \r -> 
          do q3 <- r
             let replaced = Set.union q3 rest

                 (given', wanted') = case role of
                                      Given  -> (replaced, wanted)
                                      Wanted -> (given,  replaced)

             return $ ( tch 
                      , subst
                      , given'
                      , wanted'
                      )

topreact :: Toplevel -> Role -> Constraint -> Solver (Maybe (Touchables, Set Constraint))
topreact = undefined
                          
-- Try to canonicalize one atomic constraint. The atomic constraints from the given/wanted 
-- list are tried one at a time. The rule either succeeds directly after the first success
-- or returns Nothing if all constraints are already canonic.
                          
ruleTop :: Toplevel -> Role -> Quadruple -> Solver (Maybe Quadruple)
ruleTop tl role (tch, subst, given, wanted) = pickFirst . map attempt $ choices where
      pivot = case role of 
                Given  -> given
                Wanted -> wanted
  
      choices :: [(Constraint, Set Constraint)]
      choices = map (\[q1] -> (q1, Set.difference pivot . singleton $ q1) ) . pick 1 . toList $ pivot
 
      attempt :: (Constraint, Set Constraint) -> Solver (Maybe Quadruple)
      attempt (q1, rest) = (`fmap` topreact tl role q1) $ \r ->
        do (tch', q2) <- r
           let replaced = union q2 rest

               (given', wanted') = case role of
                                     Given  -> (replaced, wanted)
                                     Wanted -> (given,  replaced)

           if role == Given && tch' /= mempty
              then Nothing
              else return ( union tch tch'
                          , subst
                          , given'
                          , wanted'
                          )
              
simplifies :: Constraint -> Constraint -> Solver (Maybe (Set Constraint))
simplifies = undefined

-- Generate all pairs of atomic constraints from the given/wanted list and try to let
-- them interact one at a time. The rule either succeeds directly after the first success 
-- or returns Nothing if no interacting pairs were found.
ruleSimplification :: Quadruple -> Solver (Maybe Quadruple)
ruleSimplification (tch, subst, given, wanted) = pickFirst . map attempt . toList $ relevant where

      relevant = given  `unionMap` \g ->
                 wanted `unionMap` \w ->
                 singleton $ (g, w, Set.delete w wanted)
                 
      attempt (g, w, wanted') = (`fmap` simplifies g w) $ \r -> 
        do w <- r
           return (tch, subst, given,  wanted' `union` w)   
    

                      
-- Rewrite the quadruple until no more rewrite steps are possible
rewriter :: Toplevel -> Quadruple -> Solver (Maybe Quadruple)
rewriter tl quad =
  let  rules = [ ruleCanon Given
          , ruleCanon Wanted
          , ruleInteract Given
          , ruleInteract Wanted
          , ruleSimplification
          , ruleTop tl Given
          , ruleTop tl Wanted
          ]
       go q = do fired <- pickFirst $ map ($ q) rules
                 case fired of
                      Nothing -> return $ Just q
                      Just q' -> go q'
                     
  in do fired <- pickFirst $ map ($ quad) rules
        case fired of
             Nothing  -> return Nothing
             Just q'  -> go q'
          
  
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
  do let rewriter' tl q = fmap (fromMaybe q) (rewriter tl q) 
    
     (newTouch, phi, newGiven, newWanted) <- rewriter' tl (oldTouch, mempty, oldGiven, oldWanted)
     
     let (eqPart, residual) = seperateEqualities (phi `applySubst` newWanted)
         theta = restrictSubstitution oldTouch . extractSubstitution $ eqPart
         substitutedResidual = theta `applySubst` residual
         
     assert (dom theta `isSubsetOf` oldTouch) $ "simplifier: substitution concerns non-touchable variables" 
     assert (dom theta # fuv substitutedResidual) $ "simplifier: domain of final substitution should be disjoint from residual"
     
     return $ (substitutedResidual, theta)
  
  

