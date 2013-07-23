{-# LANGUAGE NoMonomorphismRestriction, ExistentialQuantification,
             FlexibleContexts, TypeFamilies, GeneralizedNewtypeDeriving,
             StandaloneDeriving, FlexibleInstances, MultiParamTypeClasses,
             ViewPatterns #-}

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

data Predicate = PredName :/: Int
               deriving (Eq, Ord, Read)

instance Show Predicate where
  show (f :/: n) = mconcat [show f,"/",show n]

instance Hashable Predicate where
  hashWithSalt s (f :/: n) = hashWithSalt s (f,n)

data Relation v = Relation {
  facts :: Seq [v],
  rules :: [Rule v (ATerm v)]
}

                | Function (Atom v (ATerm v) -> HM v (ATerm v))

instance Monoid (Relation v) where
  (Relation f r) `mappend` (Relation f' r') = Relation (f <> f') (r <> r')
  mappend a b = error $ "cannot smash these relations"
  mempty = Relation mempty mempty

singleton = S.singleton

instance Show v => Show (Relation v) where
  show (Relation vs _) =
      mconcat ["{", intercalate ", " (fmap show $ toList vs), "}"]
  show (Function _)    = "#<function>"

insert_atom (UTerm (Atom f n _)) v = modify (M.insertWith (flip (<>)) (f :/: n) v)
insert_atom _ _ = return ()

init_rule :: MonadState (Table v) m => Rule v (ATerm v) -> m ()
init_rule (a@(Atom _ _ as) :- []) =
  insert_atom (UTerm a) $ Relation (singleton $ devalue as) mempty
init_rule r@(a :- bs) = insert_atom (UTerm a) $ Relation mempty [r]

init_table :: (BindingMonad (Atom v) x m) =>
              m [(Rule v (ATerm v))] -> m (Table v)
init_table = fmap $ flip execState mempty . traverse_ init_rule

type Table v =  Map Predicate (Relation v)

unify' p q = either (const mzero) return <$> e
  where e = runErrorT $ p =:= q
ab :: Eq v => HM v (ATerm v) -> HM v (ATerm v)
ab u = u >>= runErrorT . applyBindings >>= either (const mzero) return

lookup_atom :: Atom v a -> HM v (Relation v)
lookup_atom (Atom f n _) = HM . lift $ gets (M.! (f :/: n))
lookup_rules = fmap fst . rules_and_facts
lookup_facts = fmap snd . rules_and_facts
rules_and_facts :: Atom v a -> HM v ([Rule v (ATerm v)], Seq (ATerm v))
rules_and_facts q = do Relation fs rs <- lookup_atom q
                       return (rs, termify q fs)

termify (Atom f n _) = fmap (UTerm . Atom f n . fmap (UTerm . Val))

sld :: (Eq v, Show v) => Atom v (ATerm v) -> HM v (ATerm v)
sld q = do r <- lookup_atom q
           case r of
             Relation fs rs ->
               do let rfs = join . msum . fmap (unify' $ UTerm q) $ termify q fs
                      rrs = msum . fmap (sld_rule q) $ rs
                  rfs `mplus` rrs
             Function f -> f q

sld_rule :: (Eq v, Show v) => Atom v (ATerm v) -> Rule v (ATerm v) -> HM v (ATerm v)
sld_rule q (h :- bs) = do u <- unify' (UTerm q) (UTerm h)
                          traverse_ resolve_lit bs
                          u
  where resolve_lit (Pos a) = sld a
        resolve_lit (Neg a) = ifte (sld a) (const mzero) (return $ UTerm a)

eveng :: Atom Integer (ATerm Integer) -> HM Integer (ATerm Integer)
eveng q@(Atom _ _ [UTerm (Val v)]) = if even v then return (UTerm q) else mzero
eveng q@(Atom _ _ [x]) = do UVar x' <- semiprune x
                            mv <- lookupVar x'
                            case mv of
                              Just (UTerm (Val v)) | even v -> return . UTerm $ q
                              _ -> mzero


ground = fmap null . getFreeVars

t :: HM Value (Table Value)
t = init_table pv

newtype HM v a = HM {
      runHM :: IntBindingT (Atom v) (StateT (Table v) Logic) a
    } deriving (Monad, MonadPlus, Applicative, Functor,
                BindingMonad (Atom v) IntVar, MonadLogic)

instance MonadState (Table v) (HM v) where
    get = HM . lift $ get
    put = HM . lift . put


-- eval :: HM v (Table v) -> HM v a -> [a]
eval t hm = observeAll . flip evalStateT mempty . evalIntBindingT . runHM $ thing
    where thing = t >>= put >> hm
          -- otherthing = modify (M.insert (P "even" 1) (Function eveng))

