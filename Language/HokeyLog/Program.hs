{-# LANGUAGE NoMonomorphismRestriction, ExistentialQuantification,
             FlexibleContexts, TypeFamilies, GeneralizedNewtypeDeriving,
             StandaloneDeriving, FlexibleInstances, MultiParamTypeClasses #-}

module Language.HokeyLog.Program where

import Control.Applicative
import Control.Monad.Error hiding (msum)
import Control.Monad.State hiding (msum)
import Control.Unification
import Control.Unification.IntVar
import Data.Foldable
import Data.Hashable
import qualified Data.HashMap.Strict as M
import Data.List (intercalate)
import Data.Maybe
import Data.Monoid
import Data.Traversable
import qualified Data.Sequence as S
import Language.HokeyLog.Syntax
import Language.HokeyLog.Parser

import Control.Monad.Logic hiding (msum)
import Control.Monad.Identity hiding (msum)

import Debug.Trace

type Map = M.HashMap
type Seq = S.Seq

data Predicate = P String Int
               deriving (Eq, Ord, Read)

instance Show Predicate where
  show (P f n) = mconcat [f,"/",show n]

instance Hashable Predicate where
  hashWithSalt s (P f n) = hashWithSalt s (f,n)

data Relation v = Relation (Seq [v])
                | forall t x m. BindingMonad t x m =>
                  Function ([v] -> m [v])

instance Monoid (Relation v) where
  (Relation a) `mappend` (Relation b) = Relation (a <> b)
  mappend a b = error $ "cannot smash these relations"
  mempty = Relation mempty

singleton = Relation . S.singleton

instance Show v => Show (Relation v) where
  show (Relation vs) = "{" ++ intercalate ", " (fmap show $ toList vs) ++  "}"
  show (Function _)    = "#<function>"

insert_atom (UTerm (Atom f n _)) v = modify (M.insertWith (flip (<>)) (P f n) v)
insert_atom _ _ = return ()

init_rule :: MonadState (Table x v) m =>
             Rule v (ATerm x v) -> m ()
init_rule (a@(Atom _ _ as) :- []) =
  insert_atom (UTerm a) (mempty, singleton $ devalue as)
init_rule r@(a :- bs) = insert_atom (UTerm a) ([r], mempty)

init_table :: (BindingMonad (Atom v) x m) =>
              m [(Rule v (ATerm x v))] -> m (Table x v)
init_table = fmap $ flip execState mempty . traverse_ init_rule

type Table x v =  Map Predicate ([Rule v (ATerm x v)], Relation v)

unify' p q = either (const mzero) return <$> e
  where e = runErrorT $ p =:= q
ab :: Eq v => HM v (ATerm IntVar v) -> HM v (ATerm IntVar v)
ab u = u >>= runErrorT . applyBindings >>= either (const mzero) return

lookup_atom :: Atom v a -> HM v ([Rule v (ATerm IntVar v)], Relation v)
lookup_atom (Atom f n _) = HM . lift $ gets (M.! P f n)
-- lookup_rules = fmap fst . rules_and_facts
-- lookup_facts = fmap snd . rules_and_facts
rules_and_facts :: Atom v a -> HM v ([Rule v (ATerm IntVar v)], Seq (ATerm IntVar v))
rules_and_facts q@(Atom f n _) =
    do (rs, Relation fs) <- lookup_atom q
       return (rs, fmap (UTerm . Atom f n . fmap (UTerm . Val)) fs)

-- go :: Eq v => Atom v (ATerm IntVar v) -> HM v (ATerm IntVar v)
-- go q = HM $ lookup_facts q >>= join . msum . fmap (unify' (UTerm q))

sld :: (Eq v, Show v) => Atom v (ATerm IntVar v) -> HM v (ATerm IntVar v)
sld q = do (rs,fs) <- rules_and_facts q
           let rfs = join . msum . fmap (unify' $ UTerm q) $ fs
               rrs = msum . fmap (sld_rule q) $ rs
           rfs `mplus` rrs

sld_rule :: (Eq v, Show v) =>
           Atom v (ATerm IntVar v)
           -> Rule v (ATerm IntVar v)
           -> HM v (ATerm IntVar v)
sld_rule q (h :- bs) = do u <- unify' (UTerm q) (UTerm h)
                          traverse_ resolve_lit bs
                          u
  where resolve_lit (Pos a) = sld a
        resolve_lit (Neg a) = ifte (sld a) (const mzero) (return $ UTerm a)

ground = fmap null . getFreeVars

t :: HM Integer (Table IntVar Integer)
t = init_table pv

newtype HM v a = HM {
      runHM :: IntBindingT (Atom v) (StateT (Table IntVar v) Logic) a
    } deriving (Monad, MonadPlus, Applicative, Functor,
                BindingMonad (Atom v) IntVar, MonadLogic)

instance MonadState (Table IntVar v) (HM v) where
    get = HM . lift $ get
    put = HM . lift . put


eval :: HM v (Table IntVar v) -> HM v a -> [a]
eval t hm = observeAll . flip evalStateT mempty . evalIntBindingT . runHM $ thing
    where thing = do t' <- t
                     put t'
                     hm

