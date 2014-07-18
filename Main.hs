-- (C) W.L. Elsinghorst 2014, All Rights Reserved. 

{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, LambdaCase #-}

import Prelude hiding ( null, interact, concatMap, foldr )

import Data.Monoid
import Data.Foldable hiding ( msum, and, or, concat )
import Data.Traversable ( traverse )

import Control.Monad
import Control.Monad.State ( StateT (..) )
import Control.Applicative

import Text.Read

import Data.Maybe
import Data.Char
import Data.Set ( Set (..), union, singleton, difference, isSubsetOf, intersection )

import qualified Data.Set as Set
import qualified Data.Map as Map

data TypeVariable 
  = UnificationVariable UV
  | RigidVariable RV
  deriving (Eq, Ord)

newtype RV = RV { runRV :: String } 
  deriving (Show, Eq)
  
newtype UV = UV { runUV :: String }
  deriving (Show, Eq)
  
  
variableToEnum :: Int -> String  
variableToEnum n = 
  if n >= 0 && n < 0 + lowercaseRange
     then [chr (ord 'a' + n)]
     else show (n - lowercaseRange) 
  where
    lowercaseRange = ord 'z' - ord 'a' + 1 
  
variableFromEnum :: String -> Int
variableFromEnum s = 
  let lowercaseRange = ord 'z' - ord 'a' + 1
      parseChar (x:[]) = if ord x >= ord 'a' && ord x <= ord 'z'
                            then Just $ ord x - ord 'a'
                            else Nothing
      parseChar _ = Nothing
  in case msum [ parseChar s :: Maybe Int
               , fmap (\t -> t + lowercaseRange) . readMaybe $ s :: Maybe Int
               ] of Just n -> n
                    _      -> error "fromEnum: invalid parse" 

instance Enum RV where
  toEnum = RV . variableToEnum
  fromEnum = variableFromEnum . runRV
              
instance Enum UV where
  toEnum = UV . variableToEnum
  fromEnum = variableFromEnum . runUV

instance Ord RV where
  compare a b = compare (fromEnum a) (fromEnum b)
  
instance Ord UV where
  compare a b = compare (fromEnum a) (fromEnum b)


  

data Monotype 
  = TyVar TypeVariable
  | TyCon String [Monotype]
  | TyFam String [Monotype]
  deriving (Eq)

-- fig 20 page 58
instance Ord Monotype where
  TyFam nm1 tys1                `compare` TyFam nm2 tys2                = (nm1, tys1) `compare` (nm2, tys2) -- Not specified in fig 20, but shouldn't harm to orient them anyway.
  TyFam _   _                   `compare` _                             = LT
  _                             `compare` TyFam _   _                   = GT
  
  TyVar (UnificationVariable _) `compare` TyVar (RigidVariable _)       = LT
  TyVar (RigidVariable _)       `compare` TyVar (UnificationVariable _) = GT
  
  TyVar (UnificationVariable a) `compare` TyVar (UnificationVariable b) = a `compare` b
  TyVar (RigidVariable a)       `compare` TyVar (RigidVariable b)       = a `compare` b
  
  TyVar _                       `compare` t       | isTypeTypeFamilyFree t  = LT
  t                             `compare` TyVar _ | isTypeTypeFamilyFree t  = GT
  
  
  TyCon nm1 tys1                `compare` TyCon nm2 tys2                = (nm1, tys1) `compare` (nm2, tys2) -- Also not specified.
  TyCon _   _                   `compare` t                             = GT
  t                             `compare` TyCon _   _                   = LT
  
data Equality = (:~) Monotype Monotype
  deriving (Eq, Ord)
   
data Constraint 
  = Equality Equality 
  | TypeClass String [Monotype]
  deriving (Eq, Ord)

data Implication 
  = Implication (Set Constraint) (Set ExtendedConstraint) Touchables
  deriving (Eq, Ord)

data ExtendedConstraint 
  = BaseConstraint        Constraint 
  | ImplicationConstraint Implication
  deriving (Eq, Ord)
  
data Toplevel 
  -- = TopBasic Constraint
  = TopTyFam String [([Monotype], Monotype)] -- F V ~ v. List of ordered equations for closed type families.                                      
  | TopClass String (Set Constraint) [Monotype]    -- Q => D V


unionBind :: (Ord a, Ord b) => Set a -> (a -> Set b) -> Set b
unionBind = flip unionMap

unionMap :: (Ord a, Ord b) => (a -> Set b) -> Set a -> Set b
unionMap f = flatten . Set.map f

flatten :: Ord a => Set (Set a) -> Set a
flatten = Set.unions . toList

simplePart :: Set ExtendedConstraint -> Set Constraint
simplePart m = m `unionBind` \case BaseConstraint b        -> singleton b
                                   ImplicationConstraint i -> Set.empty
                                    
implicationPart :: Set ExtendedConstraint -> Set Implication
implicationPart m = m `unionBind` \case BaseConstraint _        -> Set.empty
                                        ImplicationConstraint i -> singleton i
                                    


type Touchables = Set UV

data Subst = Subst { runSubst :: Map.Map UV Monotype }

instance Monoid Subst where
  mempty = Subst $ Map.empty
  x@(Subst a) `mappend` y@(Subst b) = Subst $ Map.map (applySubst x) b `Map.union` a


dom :: Subst -> Set UV 
dom = Set.fromList . Map.keys . runSubst 

class SubstApply a where
  applySubst :: Subst -> a -> a

instance SubstApply ExtendedConstraint where
  applySubst m (BaseConstraint b) = BaseConstraint (applySubst m b)
  applySubst m (ImplicationConstraint i) = ImplicationConstraint (applySubst m i)
  

instance SubstApply Implication where
  applySubst m (Implication c e tch) -- assert tch # fuv(m) ?
    = Implication (applySubst m c) (applySubst m e) tch
    
instance SubstApply Monotype where
  applySubst m ty@(TyVar (UnificationVariable uv)) = 
    case Map.lookup uv (runSubst m) of
      Just t  -> t
      Nothing -> ty
  applySubst m ty@(TyVar (RigidVariable        _)) = ty 
  applySubst m (TyCon nm tys) = TyCon nm $ map (applySubst m) tys
  applySubst m (TyFam nm tys) = TyFam nm $ map (applySubst m) tys

instance SubstApply Equality where
  applySubst m (a :~ b) = applySubst m a :~ applySubst m b
  
instance SubstApply Constraint where
  applySubst m (Equality r) = Equality $ applySubst m r 
  
instance (Ord a, SubstApply a) => SubstApply (Set a) where
  applySubst m r = Set.map (applySubst m) r
    


class OverloadedFUV a where
  fuv :: a -> Set UV

instance OverloadedFUV Constraint where
  fuv (Equality (a :~ b)) = fuv a `union` fuv b
  fuv (TypeClass nm tys)  = unionMap fuv . Set.fromList $ tys
instance OverloadedFUV (Set Constraint) where
  fuv = unionMap fuv
instance OverloadedFUV Monotype where
  fuv (TyVar (UnificationVariable a)) = singleton a
  fuv (TyVar (RigidVariable _))       = Set.empty
  fuv (TyCon nm tys)    = unionMap fuv . Set.fromList $ tys
  fuv (TyFam nm tys)    = unionMap fuv . Set.fromList $ tys
  
instance OverloadedFUV [Monotype] where
  fuv tys = unionMap fuv . Set.fromList $ tys
  
  
-- TODO: Free Rigid Variables?? 
class OverloadedFTV a where
  ftv :: a -> Set RV

instance OverloadedFTV Constraint where
  ftv (Equality (a :~ b)) = ftv a `union` ftv b
  ftv (TypeClass nm tys)  = unionMap ftv . Set.fromList $ tys
instance OverloadedFTV (Set Constraint) where
  ftv = unionMap ftv
instance OverloadedFTV Monotype where
  ftv (TyVar (UnificationVariable _)) = Set.empty
  ftv (TyVar (RigidVariable a))       = singleton a
  ftv (TyCon nm tys)    = unionMap ftv . Set.fromList $ tys
  ftv (TyFam nm tys)    = unionMap ftv . Set.fromList $ tys
  
instance OverloadedFTV [Monotype] where
  ftv tys = unionMap ftv . Set.fromList $ tys
       
  
  
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
  
type Solver a = StateT UV Error a

                                      
release_mode :: Bool
release_mode = False
 
assert :: Bool -> String -> Solver ()
assert b s = if (release_mode || b) then return () else error s
 
(#) :: Set UV -> Set UV -> Bool
a # b = Set.null (a `intersection` b) 
 

fresh :: Solver UV
fresh = StateT $ \fuv -> Value (fuv, succ fuv)
 
solver :: Set Toplevel                --Top-level constraints
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

-- Run all calculations in the given Monad until the first one succeeds with a Just

pickFirst :: Monad m => [m (Maybe a)] -> m (Maybe a) 
pickFirst []     = return Nothing
pickFirst (x:xs) = do r <- x
                      case r of 
                        Nothing     -> pickFirst xs
                        a@(Just _)  -> return a

isTypeTypeFamilyFree :: Monotype -> Bool
isTypeTypeFamilyFree (TyVar _) = True
isTypeTypeFamilyFree (TyCon nm tys) = and $ map isTypeTypeFamilyFree tys
isTypeTypeFamilyFree (TyFam _  _  ) = False

occurs :: TypeVariable -> Monotype -> Bool
occurs (UnificationVariable uv) = check where
  check (TyVar (UnificationVariable uv')) = uv == uv'
  check (TyVar (RigidVariable _))         = False
  check (TyCon _ tys) = or $ map check tys
  check (TyFam _ tys) = or $ map check tys
occurs (RigidVariable rv) = check where
  check (TyVar (UnificationVariable _)) = False
  check (TyVar (RigidVariable rv'))     = rv == rv'
  check (TyCon _ tys) = or $ map check tys
  check (TyFam _ tys) = or $ map check tys
  
substFromList :: [(UV, Monotype)] -> Subst
substFromList = Subst . Map.fromList

isTypeFamily :: Monotype -> Bool
isTypeFamily (TyFam _ _) = True
isTypeFamily _           = False

isVariable :: Monotype -> Bool
isVariable (TyVar _) = True
isVariable _         = False

extractTypeFamily :: [Monotype] -> Maybe (Monotype -> [Monotype], Monotype)
extractTypeFamily []     = Nothing 
extractTypeFamily ( r@(TyFam nm ts) : xs ) = Just (\x -> x : xs, r)
extractTypeFamily ( r               : xs ) = case extractTypeFamily xs of
                                                  Just (f, t) -> Just (\x -> r : f x, t)
                                                  Nothing     -> Nothing
                                                  
extractRelevant :: Monotype -> Maybe ( [Monotype] -> Monotype, [Monotype] )
extractRelevant (TyFam nm ts) = Just (\ts' -> TyFam nm ts', ts)
extractRelevant (TyCon nm ts) = Just (\ts' -> TyCon nm ts', ts)
extractRelevant _             = Nothing
-- NOTE: TT := T TT | F | TT -> TT | tv | hole
--       Not sure how these other cases could arise?


canon :: Role -> Constraint -> Solver (Maybe (Touchables, Subst, Set Constraint))
canon role (Equality ec) = canonEquality ec where
  canonEquality :: Equality -> Solver (Maybe (Touchables, Subst, Set Constraint))
  canonEquality (a :~ b)                               |   a == b   = return $ Just (Set.empty, mempty, Set.empty)
  canonEquality ( (TyCon nm1 ty1) :~ (TyCon nm2 ty2) ) | nm1 == nm2 = return $ Just (Set.empty, mempty, Set.fromList . map Equality $ zipWith (:~) ty1 ty2)
  canonEquality ( (TyCon nm1 ty1) :~ (TyCon nm2 ty2) ) | nm1 /= nm2 = fail $ "canon: cannot solve equality between different type constructors" 
  canonEquality ( (TyVar tv) :~ typ ) | isTypeTypeFamilyFree typ && occurs tv typ = fail $ "canon: failed occurs check" 
  canonEquality (a :~ b)                               |   b < a    = return $ Just (Set.empty, mempty, singleton . Equality $ b :~ a)
  canonEquality ( (TyFam nm ts) :~ typ ) | and (map isTypeTypeFamilyFree ts)
                                         , Just (reconstructTypeFamily, r) <- extractTypeFamily ts
                                         =
    do beta <- fresh

       let wrappedBeta = TyVar (UnificationVariable beta)
         
           (tch, subst) = case role of
                               Given  -> (singleton beta, mempty)
                               Wanted -> (Set.empty, substFromList [(beta, r)])
     
       return $ Just (tch, subst, Set.fromList $ [Equality $ TyFam nm (reconstructTypeFamily wrappedBeta) :~ typ, Equality (r :~ wrappedBeta)]) 
  canonEquality ( typ :~ rhs ) | Just (reconstructRelevant, ts) <- extractRelevant rhs
                               , isTypeFamily typ || isVariable typ
                               , and (map isTypeTypeFamilyFree ts)
                               , Just (reconstructTypeFamily, r) <- extractTypeFamily ts 
                               = 
    do beta <- fresh
    
       let wrappedBeta = TyVar (UnificationVariable beta)
         
           (tch, subst) = case role of
                               Given  -> (singleton beta, mempty)
                               Wanted -> (Set.empty, substFromList [(beta, r)])                      
 
       return $ Just ( tch
                     , subst
                     , Set.fromList $ [Equality $ typ :~ reconstructRelevant (reconstructTypeFamily wrappedBeta), Equality (r :~ wrappedBeta)]
                     )
       
canon role (TypeClass nm ts) | and (map isTypeTypeFamilyFree ts)
                             , Just (reconstructTypeFamily, r) <- extractTypeFamily ts
                             =
  do beta <- fresh

     let wrappedBeta = TyVar (UnificationVariable beta)
         
         (tch, subst) = case role of
                             Given  -> (singleton beta, mempty)
                             Wanted -> (Set.empty, substFromList [(beta, r)])
     
     return $ Just ( tch
                   , subst
                   , Set.fromList $ [TypeClass nm (reconstructTypeFamily wrappedBeta)
                   , Equality (r :~ wrappedBeta)]
                   ) 
canon role _ = return Nothing       
  
 
                         
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
      attempt (q1, rest) = canon role q1 >>- \r ->
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

isCanonical :: Constraint -> Bool
isCanonical (Equality ( r@(TyVar a) :~ t))   | isTypeTypeFamilyFree t && r < t && not (occurs a t) = True
isCanonical (Equality ( r@(TyFam _ _) :~ t)) | isTypeTypeFamilyFree r            = True
isCanonical (TypeClass nm ts)                | and (map isTypeTypeFamilyFree ts) = True
isCanonical _ = False
 
 
interact :: Constraint -> Constraint -> Solver (Maybe (Set Constraint))
interact x@(Equality (TyVar va :~ a)) (TypeClass nm bs) | isCanonical x
                                                        , and (map isTypeTypeFamilyFree bs)
                                                        , or (map (occurs va) bs)
                                                        , UnificationVariable uva <- va
                                                        = return . Just . Set.fromList $ 
                                                            [ x
                                                            , TypeClass nm (map (applySubst $ substFromList [(uva, a)]) bs)
                                                            ]
interact x@(TypeClass nma as) y@(TypeClass nmb bs) | x == y 
                                                   = return $ Just . singleton $ x
interact (Equality a) (Equality b) = fmap (fmap (Set.map Equality)) (interactEquality a b) where
  interactEquality :: Equality -> Equality -> Solver (Maybe (Set Equality))
  interactEquality x@(TyVar va :~ a) y@(TyVar vb :~ b) | va == vb
                                                       , isCanonical (Equality x)
                                                       , isCanonical (Equality y)
                                                       = return . Just . Set.fromList $ 
                                                           [ x
                                                           , a :~ b 
                                                           ]
  interactEquality x@(TyVar va :~ a) y@(TyVar vb :~ b)  | isCanonical (Equality x)
                                                        , isCanonical (Equality y)
                                                        , occurs va b
                                                        , UnificationVariable uva <- va
                                                        = return . Just . Set.fromList $
                                                            [ x
                                                            , TyVar vb :~ applySubst (substFromList [(uva, a)]) b
                                                            ]
  interactEquality x@(TyVar va :~ a) y@(TyFam nm ts :~ b)  | isCanonical (Equality x)
                                                           , isTypeTypeFamilyFree b && and (map isTypeTypeFamilyFree ts)
                                                           , occurs va b || or (map (occurs va) ts)
                                                           , UnificationVariable uva <- va
                                                           = return . Just . Set.fromList $
                                                             [ x
                                                             , TyFam nm (map (applySubst $ substFromList [(uva, a)]) ts)
                                                                 :~ applySubst (substFromList [(uva, a)]) b
                                                             ]
  interactEquality x@(TyFam nma tsa :~ a) y@(TyFam nmb tsb :~ b) | nma == nmb
                                                                 , tsa == tsb
                                                                 = return . Just . Set.fromList  $
                                                                     [ x
                                                                     , a :~ b
                                                                     ]
  -- Missing RULE in figure 22??? 
  --   Fx ~ x `interact` tv ~ y (which is missing from simplifier)
interact _ _ = return $ Nothing
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
      attempt (q1, q2, rest) = interact q1 q2 >>- \r -> 
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

simplifies :: Constraint -> Constraint -> Solver (Maybe (Set Constraint))
simplifies x@(Equality (TyVar va :~ a)) (TypeClass nm bs) | isCanonical x
                                                          , and (map isTypeTypeFamilyFree bs)
                                                          , or (map (occurs va) bs)
                                                          , UnificationVariable uva <- va
                                                          = return . Just . Set.fromList $ 
                                                              [ TypeClass nm (map (applySubst $ substFromList [(uva, a)]) bs)
                                                              ]
simplifies x@(TypeClass nma as) y@(TypeClass nmb bs) | x == y 
                                                     = return $ Just Set.empty
simplifies (Equality a) (Equality b) = fmap (fmap (Set.map Equality)) (simplifiesEquality a b) where
  simplifiesEquality :: Equality -> Equality -> Solver (Maybe (Set Equality))
  simplifiesEquality x@(TyVar va :~ a) y@(TyVar vb :~ b) | va == vb
                                                         , isCanonical (Equality x)
                                                         = return . Just . Set.fromList $ 
                                                             [ a :~ b 
                                                             ]
  simplifiesEquality x@(TyVar va :~ a) y@(TyVar vb :~ b)  | isCanonical (Equality x)
                                                          , occurs va b
                                                          , UnificationVariable uva <- va
                                                          = return . Just . Set.fromList $
                                                              [ TyVar vb :~ applySubst (substFromList [(uva, a)]) b
                                                              ]
  simplifiesEquality x@(TyVar va :~ a) y@(TyFam nm ts :~ b)  | isCanonical (Equality x)
                                                             , isTypeTypeFamilyFree b && and (map isTypeTypeFamilyFree ts)
                                                             , or (map (occurs va) ts)
                                                             , UnificationVariable uva <- va
                                                             = return . Just . Set.fromList $
                                                                 [ TyFam nm (map (applySubst $ substFromList [(uva, a)]) ts) :~ b
                                                                 ]
  simplifiesEquality x@(TyFam nma tsa :~ a) y@(TyFam nmb tsb :~ b) | nma == nmb
                                                                   , tsa == tsb
                                                                   = return . Just . Set.fromList  $
                                                                       [ a :~ b
                                                                       ]
simplifies _ _ = return $ Nothing

-- Generate all pairs of atomic constraints from the given/wanted list and try to let
-- them interact one at a time. The rule either succeeds directly after the first success 
-- or returns Nothing if no interacting pairs were found.
ruleSimplification :: Quadruple -> Solver (Maybe Quadruple)
ruleSimplification (tch, subst, given, wanted) = pickFirst . map attempt . toList $ relevant where

      relevant = given  `unionBind` \g ->
                 wanted `unionBind` \w ->
                 singleton $ (g, w, Set.delete w wanted)
                 
      attempt (g, w, wanted') = simplifies g w >>- \r -> 
        do w <- r
           return ( tch
                  , subst
                  , given
                  , wanted' `union` w
                  )   
    

    
(>>-) :: Functor f => f a -> (a -> b) -> f b
(>>-) = flip fmap

newtype RigidSubst = RigidSubst { runRigidSubst :: Map.Map RV Monotype }

instance Monoid RigidSubst where
  mempty = RigidSubst $ Map.empty
  x@(RigidSubst a) `mappend` y@(RigidSubst b) = RigidSubst $ Map.map (instantiate x) b `Map.union` a

-- Apply an `instantiation` substitution on a type scheme, instantiating the universally quantified variables to
-- unification variables.
class Instantiate r where
  instantiate :: RigidSubst -> r -> r
  
instance Instantiate Monotype where
  instantiate m ty@(TyVar (RigidVariable rv)) = 
    case Map.lookup rv (runRigidSubst m) of
      Just t  -> t
      Nothing -> ty
  instantiate m ty@(TyVar (UnificationVariable _)) = ty 
  instantiate m (TyCon nm tys) = TyCon nm $ map (instantiate m) tys
  instantiate m (TyFam nm tys) = TyFam nm $ map (instantiate m) tys

instance Instantiate Constraint where
  instantiate m (Equality (a :~ b)) = Equality (instantiate m a :~ instantiate m b)
  instantiate m (TypeClass nm tys) = TypeClass nm (map (instantiate m) tys)

instance Instantiate (Set Constraint) where
  instantiate m = Set.map (instantiate m)


data TypeFamilyFree = TypeFamilyFree | TypeFamiliesAllowed


-- Try to find a 'Rigid` substitution which instantiated the left Monotype to the right Monotype.
-- When such an substitution is found, the axiom scheme for the left Monotype can be used to simplify
-- the right (wanted/given) Monotype.
findInstantiation :: TypeFamilyFree -> Monotype -> Monotype -> Maybe RigidSubst
findInstantiation ff (TyVar (UnificationVariable a)) _                         = Nothing -- LHS shouldn't contain unification variables
findInstantiation ff _                               (TyVar (RigidVariable b)) = Nothing -- RHS should already be instantiated
findInstantiation TypeFamilyFree  (TyVar (RigidVariable a)) r | isTypeTypeFamilyFree r = Just $ RigidSubst . Map.fromList $ [(a, r)]
findInstantiation TypeFamiliesAllowed (TyVar (RigidVariable a)) r                      = Just $ RigidSubst . Map.fromList $ [(a, r)]


findInstantiation ff (TyCon nm1 tys1) (TyCon nm2 tys2) = if nm1 == nm2
                                                           then findInstantiationChained ff tys1 tys2 mempty
                                                           else Nothing
findInstantiation ff (TyFam nm1 tys1) (TyFam nm2 tys2) = if nm1 == nm2
                                                           then findInstantiationChained ff tys1 tys2 mempty
                                                           else Nothing
findInstantiation ff _ _                               = Nothing
 
-- Same as above, but with lists of Monotypes handled in bulk. 
 
findInstantiationChained :: TypeFamilyFree -> [Monotype] -> [Monotype] -> RigidSubst -> Maybe RigidSubst
findInstantiationChained ff []     []     s0 = Just s0
findInstantiationChained ff (x:xs) (y:ys) s0 = 
  do s1 <- findInstantiation ff (instantiate s0 x) (instantiate s0 y)
     findInstantiationChained ff xs ys (s1 <> s0) 
findInstantiationChained ff _ _ _            = Nothing

  
type Equation = ([Monotype], Monotype)
 
-- Type variables come in two flavours: rigid and unification. Rigid variables are
-- part of a type scheme and need to be instantiated into unification variables before
-- solving.
 
unifyRigid :: [Monotype] -> [Monotype] -> Maybe RigidSubst
unifyRigid xs ys = unifyRigid xs ys mempty where
  unifyRigid [] [] s0         = Just s0
  unifyRigid (x:xs) (y:ys) s0 = do s1 <- unify (instantiate s0 x) (instantiate s0 y)
                                   unifyRigid xs ys (s1 <> s0)
  unify (TyVar (RigidVariable rv)) y = Just $ RigidSubst . Map.fromList $ [(rv, y)]                              
  unify x (TyVar (RigidVariable rv)) = Just $ RigidSubst . Map.fromList $ [(rv, x)]    
  unify (TyVar (UnificationVariable x)) (TyVar (UnificationVariable y)) = if x == y 
                                                                             then Just $ RigidSubst . Map.fromList $ []
                                                                             else Nothing
  unify (TyCon nm1 tys1) (TyCon nm2 tys2) = unifyRigid tys1 tys2 mempty
  unify (TyFam nm1 tys1) (TyFam nm2 tys2) = unifyRigid tys1 tys2 mempty
  unify _                _                = Nothing
  
-- Equations p, q are compatible if S lhs_p == S lhs_q ==> S rhs_p == S rhs_q
-- for a unifying substitution S
compat :: Equation -> Equation -> Bool
compat (tys1, ty1) (tys2, ty2) = 
  case unifyRigid tys1 tys2 of
       Just s0 -> instantiate s0 ty1 == instantiate s0 ty2
       Nothing -> True


-- Check if two equations are apart by flattening one of the equations and making 
-- sure the the flattened equation doesn't unify with the other equation.
apart :: Equation -> Equation -> Bool
apart (tys1, _) (tys2, _) =
  case unifyRigid tys1 (flatten tys2) of
       Just _  -> False
       Nothing -> True
  where -- NOTE: `flatten` cannot be used outside `apart` due to the non-uniqueness of generated names.
    flatten :: [Monotype] -> [Monotype]
    flatten tys = case sharpen tys Map.empty . map RV . map ("$@"++) . map show $ [0..] of
                       (t, _, _) -> t
    
    sharpen []                 prevs fresh = ([], fresh, prevs)
    sharpen (t@(TyVar _)  :ts) prevs fresh = let (ts', fresh', prevs') = sharpen ts prevs fresh        
                                             in (t : ts', fresh', prevs')
    sharpen (t@(TyFam _ _):ts) prevs fresh = 
                                case Map.lookup t prevs of
                                  Just f  -> let (ts', fresh', prevs') = sharpen ts prevs fresh        
                                             in (f : ts', fresh', prevs')
                                  Nothing -> let plat = TyVar (RigidVariable $ head fresh)
                                                 (ts', fresh', prevs') = sharpen ts (prevs `Map.union` Map.fromList [(t, plat)]) (tail fresh) 
                                             in (plat : ts', fresh', prevs')
    sharpen (t@(TyCon nm tys):ts) prevs fresh = 
      let (newTys, fresh' , prevs' ) = sharpen tys prevs  fresh
          (ts'   , fresh'', prevs'') = sharpen ts  prevs' fresh'
      in (TyCon nm newTys : ts', fresh'', prevs'')
      
-- Choose the correct equation from a closed type family. Not optimized! See paper.
-- The equations are tried one-by-one until the first one succeeds. Every equation
-- is checked with all previous equations to check if it's either apart from or compatible 
-- with the previous equation.
chooseInstantiatedEquation :: [Equation] -- List of equations still to check
                           -> [Equation] -- Previous tried and failed equations
                           -> [Monotype] -> RigidSubst -> Maybe (RigidSubst, Equation)
chooseInstantiatedEquation []                 prevs tys s0 = Nothing
chooseInstantiatedEquation (q@(tys0, ty0):xs) prevs tys s0 | Just s1 <- findInstantiationChained TypeFamiliesAllowed tys0 tys s0
                                                           , and $ map (\p -> compat p q || apart p q) prevs
                                                           = Just (s1, q)
                                                           | otherwise 
                                                           = chooseInstantiatedEquation xs (q:prevs) tys s0
  
topreact :: Set Toplevel -> Role -> Constraint -> Solver (Maybe (Touchables, Set Constraint))
topreact tl role (Equality ((TyFam nm tys) :~ ty)) | isTypeTypeFamilyFree ty
                                                   , and $ map isTypeTypeFamilyFree tys 
                                                   = fmap msum . traverse tryReaction . toList $ tl where
  tryReaction (TopTyFam nm0 eqs) | nm == nm0 
                                 , Just (s0, (tys0, ty0)) <- chooseInstantiatedEquation eqs [] tys mempty -- The top-level axiom scheme can be instantiated to
                                 = do let a = ftv (ty0 : tys0)                                            -- solve the equation
                                  
                                          b = ftv ty0
                                          c = Set.toList $ a `difference` b
                      
                                      (s1, delta) <- do (subst, tch) <- fmap unzip . forM c $ \c -> 
                                                                                        do gamma <- fresh
                                                                                           return ( (c, TyVar . UnificationVariable $ gamma), gamma)
                                                        return $ ( RigidSubst . Map.fromList $ subst
                                                                 , case role of
                                                                     Wanted -> Set.fromList $ tch
                                                                     Given  -> Set.empty
                                                                 )
                                    
                                      return $ Just ( delta
                                                    , Set.singleton . Equality $ instantiate (s1 <> s0) ty0 :~ ty
                                                    )
  tryReaction _ | otherwise = return $ Nothing
  
topreact tl Wanted (TypeClass nm tys) | and $ map isTypeTypeFamilyFree tys 
                                      = fmap msum . traverse tryReaction . toList $ tl where
  tryReaction (TopClass nm0 q0 tys0) | nm == nm0 
                                     , Just s0 <- findInstantiationChained TypeFamilyFree tys0 tys mempty -- The top-level axiom scheme can be instantiated to
                                     = do let a = ftv tys0 `union` ftv q0                                 -- solve the equation
                                 
                                              b = ftv tys0
                                              c = Set.toList $ a `difference` b
                                
                                          (s1, delta) <- do (subst, tch) <- fmap unzip . forM c $ \c ->      -- Create fresh unification variables for rigid variables 
                                                                                           do gamma <- fresh -- in ty0 but not in tys0
                                                                                              return ( (c, TyVar . UnificationVariable $ gamma), gamma)
                                                            return $ ( RigidSubst . Map.fromList $ subst
                                                                     , Set.fromList $ tch
                                                                     )
                                  

                                          return $ Just ( delta
                                                        , instantiate (s1 <> s0) q0
                                                        )
  tryReaction _ | otherwise = return $ Nothing
topreact tl Given (TypeClass nm tys) | and $ map isTypeTypeFamilyFree tys 
                                     = fmap msum . traverse tryReaction . toList $ tl where
  tryReaction (TopClass nm0 q0 tys0) | nm == nm0 
                                     , Just s0 <- findInstantiationChained TypeFamilyFree tys0 tys mempty
                                     = fail $ "DINSTG: top level axiom overlaps with given constraint."
                                     
-- Try to canonicalize one atomic constraint. The atomic constraints from the given/wanted 
-- list are tried one at a time. The rule either succeeds directly after the first success
-- or returns Nothing if all constraints are already canonic.
                          
ruleTop :: Set Toplevel -> Role -> Quadruple -> Solver (Maybe Quadruple)
ruleTop tl role (tch, subst, given, wanted) = pickFirst . map attempt $ choices where
      pivot = case role of 
                Given  -> given
                Wanted -> wanted
  
      choices :: [(Constraint, Set Constraint)]
      choices = map (\[q1] -> (q1, Set.difference pivot . singleton $ q1) ) . pick 1 . toList $ pivot
 
      attempt :: (Constraint, Set Constraint) -> Solver (Maybe Quadruple)
      attempt (q1, rest) = topreact tl role q1 >>- \r ->
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

                      
-- Rewrite the quadruple until no more rewrite steps are possible. Returns Nothing
-- if no rewrite was applicable.
rewriter :: Set Toplevel -> Quadruple -> Solver (Maybe Quadruple)
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
          
  
-- 


-- page 66: 7.5, (4)
extractSubstitution :: Set (UV, Monotype) -> (Subst, Set Constraint)
extractSubstitution assocList = 
  let magicMap = Map.fromListWith (\(a, as) (b, bs) -> (a, as ++ b : bs) ) . map (\(uv, t) -> (uv, (t, []))) . Set.toList $ assocList
      residual = join . map (\(t, xs) -> map (\x -> (t, x)) xs) . Map.toList $ Map.map snd magicMap
      
  in ( Subst $ Map.map fst magicMap
     , Set.fromList $ residual >>- \(b, t) -> Equality $ TyVar (UnificationVariable b) :~ t
     )  

simplifier :: Set Toplevel                     -- Top-level constraints
           -> Set Constraint                   -- Q_Given
           -> Touchables                       -- Touchables
           -> Set Constraint                   -- Q_Wanted
           -> Solver (Set Constraint, Subst)   -- (Q_Residual; Subst)
simplifier tl oldGiven oldTouch oldWanted = 
  do let rewriter' tl q = fmap (fromMaybe q) (rewriter tl q) 
    
     (newTouch, phi, newGiven, newWanted) <- rewriter' tl (oldTouch, mempty, oldGiven, oldWanted)
     
     let -- Page 66: 7.5, (3)
         seperated = Set.toList (phi `applySubst` newWanted) >>- \case
                                      r@(Equality (TyVar (UnificationVariable b) :~ t)) -> if (b `Set.member` newTouch) && not (b `Set.member` fuv t)
                                                                                              then (Just (b, t), Nothing)
                                                                                              else (Nothing    , Just r )
                                      r@(Equality (t :~ TyVar (UnificationVariable b))) -> if (b `Set.member` newTouch) && not (b `Set.member` fuv t)
                                                                                              then (Just (b, t), Nothing)
                                                                                              else (Nothing    , Just r )
                                      r                                                 ->         (Nothing    , Just r )   
         
         (eqPart, residualPart) = ( Set.fromList . catMaybes $ map fst seperated -- Substitutions b ~> t
                                  , Set.fromList . catMaybes $ map snd seperated -- List of remaining equalities b ~> t' with t' /= t
                                  )
         
         -- Page 66: 7.5, (4) 
         (theta, remainingEqualities) = extractSubstitution $ eqPart
         
         -- Page 66: 7.5, below (4) 
         restrictedTheta = Subst . Map.mapMaybeWithKey selector . runSubst $ theta where
           selector k a | k `Set.member` oldTouch = Just a   -- Restrict the domain of the generated substitution 
           selector k _ | otherwise               = Nothing  -- to the original touchables list
         substitutedResidual = theta `applySubst` (residualPart `union` remainingEqualities)
         
     assert (dom restrictedTheta `isSubsetOf` oldTouch) $ "simplifier: substitution concerns non-touchable variables" 
     assert (dom restrictedTheta # fuv substitutedResidual) $ "simplifier: domain of final substitution should be disjoint from residual"
     
     return $ (substitutedResidual, restrictedTheta)
  
  

