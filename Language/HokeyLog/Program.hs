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

                | Function (ATerm v -> HM v (ATerm v))

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

init_table :: (BindingMonad (Atom v) x m) => m [Term Rule v] -> m (Table v)
init_table = fmap $ flip execState mempty . traverse_ init_rule

type Term c v = c v (ATerm v)

type Table v =  Map Predicate (Relation v)

-- | Transform an error into a failure, succeed otherwise.
meither :: MonadPlus m => Either a b -> m b
meither = either (const mzero) return

-- | 'unify' or fail trying
unify' p q = meither <$> runErrorT (p =:= q)

-- | 'applyBindings' or fail trying.
ab :: Eq v => HM v (ATerm v) -> HM v (ATerm v)
ab u = u >>= runErrorT . applyBindings >>= meither

-- | Look up the 'Relation' corresponding to this 'Atom' in the state.
-- Currently throws if you give an atom isn't present in the state, so
-- (until I remember to fix both the bug and this documentation) Don't
-- Do That Thing.
lookup_atom :: ATerm v -> HM v (Relation v)
lookup_atom (UTerm (Atom f n _)) = HM . lift $ gets (M.! (f :/: n))

-- | Turn a row in the database into a nice, unifiable 'ATerm'.
termify (UTerm (Atom f n _)) = fmap (UTerm . Atom f n . fmap (UTerm . Val))

-- | Standard, prolog style evaluation.  Search the database for
-- instances of a query, unify it with the head of any rules we find,
-- then recur (sorta) on the body of said rules.  Negation is failure.
-- If there's a 'Show' constraint in the context, it's an artifact of
-- debugging, and probably shouldn't actually be here.
sld :: (Eq v, Show v) => ATerm v -> HM v (ATerm v)
sld q = do r <- lookup_atom q
           case r of
             Relation fs rs ->
               do let rfs = join . msum . fmap (unify' q) $ termify q fs
                      rrs = msum . fmap (sld_rule q) $ rs
                  rfs `mplus` rrs
             Function f -> f q

sld_rule :: (Eq v, Show v) => ATerm v -> Rule v (ATerm v) -> HM v (ATerm v)
sld_rule q (h :- bs) = do u <- unify' q (UTerm h)
                          traverse_ resolve_lit bs
                          u
  where resolve_lit (Pos a) = sld $ UTerm a
        resolve_lit (Neg a) = ifte (sld $ UTerm a) (const mzero) (return $ UTerm a)

eveng :: Atom Integer (ATerm Integer) -> HM Integer (ATerm Integer)
eveng q@(Atom _ _ [UTerm (Val v)]) = if even v then return (UTerm q) else mzero
eveng q@(Atom _ _ [x]) = do UVar x' <- semiprune x
                            mv <- lookupVar x'
                            case mv of
                              Just (UTerm (Val v)) | even v -> return . UTerm $ q
                              _ -> mzero


-- | Is this term ground?
ground = fmap null . getFreeVars

t :: HM Value (Table Value)
t = init_table pv

-- | The HokeyLog Monad.  Uncharitably, "HokeyMon"
newtype HM v a = HM {
      runHM :: IntBindingT (Atom v) (StateT (Table v) Logic) a
    } deriving (Monad, MonadPlus, Applicative, Functor,
                BindingMonad (Atom v) IntVar, MonadLogic)

instance MonadState (Table v) (HM v) where
    get = HM . lift $ get
    put = HM . lift . put

-- | Run the computation to make a 'Table', shove it into the state,
-- and eval the computation proper.  We need the effectful computation
-- of the table to preserve the binding state of any variables
-- therein.
eval :: HM v (Table v) -> HM v a -> [a]
eval t hm = observeAll . flip evalStateT mempty . evalIntBindingT . runHM $ thing
    where thing = t >>= put >> hm
          -- otherthing = modify (M.insert (P "even" 1) (Function eveng))

