{-# LANGUAGE NoMonomorphismRestriction, ExistentialQuantification,
             FlexibleContexts, TypeFamilies, GeneralizedNewtypeDeriving,
             StandaloneDeriving, FlexibleInstances, MultiParamTypeClasses,
             ViewPatterns, ScopedTypeVariables #-}

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
import qualified Data.Vector as V
import Language.HokeyLog.Syntax
import Language.HokeyLog.Parser

import Control.Monad.Logic hiding (msum)
import Control.Monad.Identity hiding (msum)

import qualified Data.ListTrie.Patricia.Set.Ord as P
import qualified Data.ListTrie.Base.Map as LM

import Debug.Trace

type Map = M.HashMap
type Seq = S.Seq

-- | Prolog functor notation---name/arity.
data Predicate = {-# UNPACK #-} !PredName :/: {-# UNPACK #-} !Int
               deriving (Eq, Ord)

instance Show Predicate where
  show (f :/: n) = mconcat [show f,"/",show n]

instance Hashable Predicate where
  hashWithSalt s (f :/: n) = hashWithSalt s (f,n)

predicated :: Atomic t => t v a -> Predicate
predicated (toAtom -> Atom f as) = f :/: V.length as

data Relation v = Relation {
  facts :: Seq (Tuple v),
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

insert_atom (UTerm a@(Atom f as)) v = modify (M.insertWith (flip (<>)) (predicated a) v)
insert_atom _ _ = return ()

init_rule :: MonadState (Table v) m => Rule v (ATerm v) -> m ()
init_rule (a@(Atom _ as) :- []) =
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
lookup_atom (UTerm (Atom f as)) = HM . lift $ gets (M.! (f :/: V.length as))

-- | Turn a row in the database into a nice, unifiable 'ATerm'.
termify (UTerm (Atom f _)) = fmap (UTerm . Atom f . fmap (UTerm . Val))

-- | Standard prolog-ish evaluation.  Search the database for
-- instances of a query, unify it with the head of any rules we find,
-- then recur (sorta) on the body of said rules.  Negation as failure
-- is handled by 'sld_rule'.  If there's a 'Show' constraint in the
-- context, it's an artifact of debugging, and probably shouldn't
-- actually be here.
sld :: (Eq v, Show v) => ATerm v -> HM v (ATerm v)
sld q = do r <- lookup_atom q
           case r of
             Relation fs rs ->
               do let rfs = join . msum . fmap (unify' q) $ termify q fs
                      rrs = msum . fmap (sld_rule q) $ rs
                  rfs `mplus` rrs
             Function f -> f q

-- | Unify the query with the head, then evaluate the body.
sld_rule :: (Eq v, Show v) => ATerm v -> Rule v (ATerm v) -> HM v (ATerm v)
sld_rule q (h :- bs) = do u <- unify' q (UTerm h)
                          traverse_ resolve_lit bs
                          u
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
ground = fmap null . getFreeVars

t :: HM Value (Table Value)
t = init_table pv

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


search_set :: (Show a, Ord a, MonadPlus m) => [Maybe a] -> P.TrieSet a -> m [a]
search_set [] s = return []
search_set xs s = case rs of
                    [] -> P.foldr (mplus . return) mzero s'
                    (Nothing:rs') -> do (x, ts) <- msum $ fmap return cs
                                        cdr <- search_set rs' ts
                                        return $ pfx ++ x:cdr
    where (catMaybes -> pfx,rs) = span isJust xs
          s' = P.lookupPrefix pfx s
          cs = LM.toList . P.children1 . P.deletePrefix pfx $ s'

search_facts :: Ord v => [ATerm v] -> P.TrieSet v -> HM v [ATerm v]
search_facts [] s | P.null s = mzero
                  | otherwise = return []
search_facts (t@(UTerm (Val v)):xs) s = do cdr <- search_facts xs (P.deletePrefix [v] s)
                                           return $ t : cdr
search_facts (x@(UVar _):xs) s = do (v, ts) <- msum $ fmap return cs
                                    u <- unify' x (UTerm $ Val v)
                                    cdr <- search_facts xs ts
                                    return $ u : cdr
  where cs = LM.toList . P.children1 $ s
                                    
