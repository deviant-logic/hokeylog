{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable,
             FlexibleContexts, NoMonomorphismRestriction,
             OverloadedStrings, MultiParamTypeClasses, TypeSynonymInstances,
             FlexibleInstances, ViewPatterns #-}

module Language.HokeyLog.Syntax where

import Control.Monad.State
import Control.Unification
import Control.Unification.IntVar
import qualified Data.ByteString.Char8 as B
import Data.Foldable
import Data.Hashable
import Data.List (intercalate)
import qualified Data.Map as M
import Data.Monoid
import Data.Traversable

import Data.Interned
import Data.Interned.ByteString

import qualified Data.Vector as V

type ByteString = InternedByteString
type PredName = ByteString
type Vector = V.Vector
type Row v = [v]


-- instance Hashable InternedByteString where
--     hashWithSalt s = hashWithSalt s . unintern

data Atom v a = Atom {-# UNPACK #-} !PredName (Row a)
              | Val v
              deriving (Eq, Ord, Functor, Foldable, Traversable)

class Foldable t => Rowlike t where
    row :: [v] -> t v

    nullRow :: t v -> Bool
    nullRow = null . toList

    rowSize :: t v -> Int
    rowSize = length . toList

    rowZip :: t v -> t v' -> t (v, v')
    rowZip t t' = row $ zip (toList t) (toList t')

instance Rowlike [] where
    row = id

instance Rowlike V.Vector where
    row = V.fromList
    rowSize = V.length
    rowZip = V.zip

class Atomic t where
    toAtom :: t v a -> Atom v a

instance Atomic Atom where
    toAtom = id

atom :: (Foldable t, Rowlike t) => PredName -> t a -> Atom v a
atom f = Atom f . row . toList

instance (Show v, Show a) => Show (Atom v a) where
  show (Atom f as) | nullRow as = B.unpack . unintern $ f
                   | otherwise = mconcat [B.unpack . unintern $ f,
                                          "(",
                                          intercalate ", " $
                                                      toList (fmap show as),
                                          ")"]
  show (Val v)     = show v

data Lit v a = Pos (Atom v a)
             | Neg (Atom v a)
             deriving (Eq, Ord, Functor, Foldable, Traversable)

instance (Show v, Show a) => Show (Lit v a) where
  show (Pos a) = show a
  show (Neg a) = "not " <> show a

instance Atomic Lit where
    toAtom (Pos a) = a
    toAtom (Neg a) = a

data Rule v a = Atom v a :- [Lit v a]
              deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Atomic Rule where
    toAtom (a :- _) = a

instance Eq v => Unifiable (Atom v) where
  zipMatch (Val v) (Val v') | v == v' = Just (Val v)
  zipMatch (Atom f as) (Atom g bs) | rowSize as /= rowSize bs
                                     || f /= g = Nothing
  zipMatch (Atom f as) (Atom _ bs) = return . Atom f . fmap Right $ rowZip as bs
  zipMatch _ _ = Nothing

type ATerm v = UTerm (Atom v) IntVar

varicate :: (Eq v, BindingMonad (Atom v) IntVar m) =>
            Either String v -> StateT (M.Map String IntVar) m (ATerm v)
varicate (Right v) = return $ UTerm (Val v)
varicate (Left x)  = do mv <- gets (M.lookup x)
                        case mv of
                          Just v -> return $ UVar v
                          Nothing -> do v <- lift freeVar
                                        modify (M.insert x v)
                                        return $ UVar v

data Value = Str {-# UNPACK #-} !ByteString
           | Num {-# UNPACK #-} !Int
   deriving (Eq, Ord)

instance Show Value where
    show (Str s) = show s
    show (Num i) = show i

-- | Prolog functor notation---name/arity.
data Predicate = {-# UNPACK #-} !PredName :/: {-# UNPACK #-} !Int
               deriving (Eq, Ord)

instance Show Predicate where
  show (f :/: n) = mconcat [show f,"/",show n]

instance Hashable Predicate where
  hashWithSalt s (f :/: n) = hashWithSalt s (unintern f,n)

predicated :: Atomic t => t v a -> Predicate
predicated (toAtom -> Atom f as) = f :/: rowSize as
predicated _ = error "predicated a value"


postvaricate :: (Eq v, Traversable t, BindingMonad (Atom v) IntVar m) =>
               t (Either String v) -> m (t (ATerm v))
postvaricate = flip evalStateT M.empty . traverse varicate

devalue :: Functor f => f (ATerm v) -> f v
devalue = fmap devalue'
    where devalue' (UTerm (Val v)) = v
          devalue' _ = error "tried to devalue a not-value"
