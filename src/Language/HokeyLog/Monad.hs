{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, TypeSynonymInstances,
             OverloadedStrings, UndecidableInstances,
             FunctionalDependencies #-}

module Language.HokeyLog.Monad where

import Control.Applicative
import Control.Monad.State
import Control.Unification
import Control.Unification.IntVar
import Control.Monad.Error
import Control.Monad.Logic

import qualified Data.HashMap.Strict as M
import qualified Data.ListTrie.Patricia.Set.Ord as P
import Data.List (intercalate)
import Data.ListTrie.Patricia.Set.Ord (TrieSet)
import Data.Monoid

import Language.HokeyLog.Syntax

-- | The underlying interpreter state mapping predicate names to their
-- implementations.
type Table v =  Map Predicate (Relation v)

-- | The map implementation for the 'Table'.
type Map  = M.HashMap
-- | The implementation for sets of facts.
type Rows = TrieSet

-- | The HokeyLog Monad.  Uncharitably, \"HokeyMon\"
newtype HM v a = HM {
      runHM :: IntBindingT (Atom v) (StateT (Table v) Logic) a
    } deriving (Monad, MonadPlus, Applicative, Functor,
                BindingMonad (Atom v) IntVar, MonadLogic)

-- | 'applyBindings' or fail trying.
ab :: Eq v => HM v (ATerm v) -> HM v (ATerm v)
ab u = u >>= runErrorT . applyBindings >>= meither

-- | Transform an error into a failure, succeed otherwise.
meither :: MonadPlus m => Either a b -> m b
meither = either (const mzero) return

-- | 'unify' or fail trying
unify' :: Eq v => ATerm v -> ATerm v -> HM v (ATerm v)
unify' p q = runErrorT (p =:= q) >>= meither

-- | This instance can't be newtype-derived, and the monad won't work
-- without it.
instance MonadState (Table v) (HM v) where
    get = HM . lift $ get
    put = HM . lift . put

-- | The thing that gets stored in runtime state.  It could be rows,
-- or a function, or some other awesome thing.
data Relation v = Relation {
  facts :: Rows v,            -- ^ 'Row's of ground values.
  rules :: [Rule v (ATerm v)] -- ^ Deduction 'Rule's.
} | Function (ATerm v -> HM v (ATerm v))

instance Ord v => Monoid (Relation v) where
  (Relation f r) `mappend` (Relation f' r') = Relation (f <> f') (r <> r')
  mappend _ _ = error $ "cannot smash these relations"
  mempty = Relation mempty mempty

-- | Make a one-element 'Relation' entry.
singleton :: Ord v => Row v -> Rows v
singleton = P.singleton

instance (Show v, Ord v) => Show (Relation v) where
  show (Relation vs _) =
      mconcat ["{", intercalate ", " (fmap show $ P.toList vs), "}"]
  show (Function _)    = "#<function>"

succeed :: HM v (ATerm v)
succeed = return $ UTerm (Atom "true" [])

succg :: In Value -> Out Value -> HMTerm Value
succg (In (Num n)) (Out x) = unify' (UTerm (Val (Num $ succ n))) x

eveng :: In Value -> HMTerm Value
eveng (In (Num n)) | even n = succeed
                   | otherwise = mzero

data In  v = In v
data Out v = Out (ATerm v)

type HMTerm v = HM v (ATerm v)

class Moded f v | f -> v where
    moded :: f -> (ATerm v) -> HMTerm v

instance Moded (HMTerm v) v where
    moded = const

instance (Eq v, Moded f v) => Moded (In v -> f) v where
    moded f q@(UTerm (Atom a (v:vs))) = do (UTerm (Val v')) <- ab (return v)
                                           moded (f $ In v') (UTerm (Atom a vs))
                                           return q

instance Moded f v => Moded (Out v -> f) v where
    moded f q@(UTerm (Atom a (v:vs))) = do moded (f $ Out v) (UTerm (Atom a vs))
                                           return q
