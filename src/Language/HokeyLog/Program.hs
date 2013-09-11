{-# LANGUAGE NoMonomorphismRestriction, ExistentialQuantification,
             FlexibleContexts, TypeFamilies, GeneralizedNewtypeDeriving,
             StandaloneDeriving, FlexibleInstances, MultiParamTypeClasses,
             ViewPatterns, ScopedTypeVariables #-}

-- | This module is where code related to full programs is intended to
-- reside.
module Language.HokeyLog.Program where

import Control.Applicative
import Control.Monad.Error hiding (msum)
import Control.Monad.State hiding (msum)
import Control.Unification
import Control.Unification.IntVar
import Data.Foldable
import qualified Data.HashMap.Strict as M
import Data.List (intercalate)
import Data.Monoid
import Language.HokeyLog.Syntax

import Control.Monad.Logic hiding (msum)

import Data.ListTrie.Patricia.Set.Ord (TrieSet)
import qualified Data.ListTrie.Patricia.Set.Ord as P
import qualified Data.ListTrie.Base.Map as LM

-- import Debug.Trace

-- | The map implementation for the 'Table'.
type Map  = M.HashMap
-- | The implementation for sets of facts.
type Rows = TrieSet

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

-- | Insert a 'Relation' for this term into the interpreter state.
insert_atom :: (Ord v, MonadState (Table v) m) => ATerm v -> Relation v -> m ()
insert_atom (UTerm a) v = modify (M.insertWith (flip (<>)) (predicated a) v)
insert_atom _ _ = return ()

-- | Initialize a 'Rule' in the rule table.
init_rule :: (Ord v, MonadState (Table v) m) => Rule v (ATerm v) -> m ()
init_rule (a@(Atom _ as) :- []) =
  insert_atom (UTerm a) $ Relation (singleton . toList $ devalue as) mempty
init_rule r@(a :- _) = insert_atom (UTerm a) $ Relation mempty [r]

-- | Initialize the rule table.
init_table :: (Ord v, BindingMonad (Atom v) x m) =>
             m [Rule v (ATerm v)] -> m (Table v)
init_table = fmap $ flip execState mempty . traverse_ init_rule

-- | The underlying interpreter state mapping predicate names to their
-- implementations.
type Table v =  Map Predicate (Relation v)

-- | Transform an error into a failure, succeed otherwise.
meither :: MonadPlus m => Either a b -> m b
meither = either (const mzero) return

-- | 'unify' or fail trying
unify' :: Eq v => ATerm v -> ATerm v -> HM v (ATerm v)
unify' p q = runErrorT (p =:= q) >>= meither

-- | 'applyBindings' or fail trying.
ab :: Eq v => HM v (ATerm v) -> HM v (ATerm v)
ab u = u >>= runErrorT . applyBindings >>= meither

-- | Look up the 'Relation' corresponding to this 'Atom' in the state.
-- Currently throws if you give an atom isn't present in the state, so
-- (until I remember to fix both the bug and this documentation) Don't
-- Do That Thing.
lookup_atom :: ATerm v -> HM v (Relation v)
lookup_atom (UTerm (Atom f as)) = HM . lift $ gets (M.! (f :/: rowSize as))
lookup_atom (UTerm (Val _)) = error "tried to lookup_atom a value"
lookup_atom _ = error "tried to lookup_atom a variable"

-- | Turn a row in the database into a nice, unifiable 'ATerm'.
termify :: (Ord v, Functor f) => ATerm v -> f (Row v) -> f (ATerm v)
termify (UTerm (Atom f _)) = fmap (UTerm . Atom f . fmap (UTerm . Val))
termify (UTerm (Val _)) = error "tried to termify a value"
termify _ = error "tried to termify a variable"

-- | Standard prolog-ish evaluation.  Search the database for
-- instances of a query, unify it with the head of any rules we find,
-- then recur (sorta) on the body of said rules.  Negation as failure
-- is handled by 'sld_rule'.  If there's a 'Show' constraint in the
-- context, it's an artifact of debugging, and probably shouldn't
-- actually be here.
sld :: (Ord v, Show v) => ATerm v -> HM v (ATerm v)
sld q = do r <- lookup_atom q
           case r of
             Relation fs rs ->
               do let -- rfs = msum . fmap (unify' q) $ termify q fs
                      UTerm (Atom f as) = q
                      rfs = UTerm . atom f <$> search_facts (toList as) fs
                      rrs = msum . fmap (sld_rule q) $ rs
                  rfs `mplus` rrs
             Function f -> f q

-- | Unify the query with the head, then evaluate the body.
sld_rule :: (Ord v, Show v) => ATerm v -> Rule v (ATerm v) -> HM v (ATerm v)
sld_rule q (h :- bs) = do u <- unify' q (UTerm h)
                          traverse_ resolve_lit bs
                          return u
  where resolve_lit (Pos a) = sld $ UTerm a
        resolve_lit (Neg a) = ifte (sld $ UTerm a) (const mzero) (return $ UTerm a)

-- eveng :: Atom Integer (ATerm Integer) -> HM Integer (ATerm Integer)
-- eveng q@(Atom _ _ [UTerm (Val v)]) = if even v then return (UTerm q) else mzero
-- eveng q@(Atom _ _ [x]) = do UVar x' <- semiprune x
--                             mv <- lookupVar x'
--                             case mv of
--                               Just (UTerm (Val v)) | even v -> return . UTerm $ q
--                               _ -> mzero


-- | Is this term ground?
ground :: BindingMonad t a f => UTerm t a -> f Bool
ground = fmap null . getFreeVars

-- | The HokeyLog Monad.  Uncharitably, \"HokeyMon\"
newtype HM v a = HM {
      runHM :: IntBindingT (Atom v) (StateT (Table v) Logic) a
    } deriving (Monad, MonadPlus, Applicative, Functor,
                BindingMonad (Atom v) IntVar, MonadLogic)

-- | This instance can't be newtype-derived, and the monad won't work
-- without it.
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

-- | Search for all elements of a 'TrieSet' that unify with a list of
-- 'ATerm's.
search_facts :: (Show v, Ord v) => [ATerm v] -> TrieSet v -> HM v [ATerm v]
search_facts [] s | P.toList s == [[]] = return []
                  | otherwise         = mzero
search_facts (t@(UTerm (Val v)):xs) s = do cdr <- search_facts xs (P.deletePrefix [v] s)
                                           return $ t : cdr
search_facts (x@(UVar _):xs) s = do (v, ts) <- msum $ fmap return cs
                                    u <- unify' x (UTerm $ Val v)
                                    cdr <- search_facts xs ts
                                    return (u : cdr)
  where cs = LM.toList . P.children1 $ s
search_facts _ _ = error "search facts saw an atom"

