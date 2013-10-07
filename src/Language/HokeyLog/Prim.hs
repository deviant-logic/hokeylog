{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.HokeyLog.Prim where

import Control.Monad
import Control.Unification
import Data.Interned
import Language.HokeyLog.Monad
import Language.HokeyLog.Syntax

import qualified Data.ByteString as B

import Text.Regex.Base
import Text.Regex.PCRE.ByteString.Lazy

succeed :: HM v (ATerm v)
succeed = return $ UTerm (Atom "true" [])

succg :: In Value -> Out Value -> HMTerm Value
succg (In (Num n)) (Out x) = unify' (UTerm (Val (Num $ succ n))) x

eveng :: In Value -> HMTerm Value
eveng (In (Num n)) | even n = succeed
                   | otherwise = mzero

matchg :: In Value -> In Value -> HMTerm Value
matchg (In (Str re)) (In (Str s)) | matchTest (makeRegex $ unintern re :: Regex) (unintern s) = succeed
matchg _ _ = mzero

matchn :: Value -> Value -> [ATerm Value] -> HMTerm Value
matchn (Str re) (Str s) out | (not . null $ captures) =
    sequence [ unify' m x | (m,x) <- zip (tail captures) out] >> succeed
  where captures = fmap (UTerm . Val . Str . intern) submatches
        submatches = getAllTextSubmatches $ (makeRegex $ unintern re :: Regex) `match` (unintern s)
matchn _ _ _ = mzero

match1g (In re) (In s) (Out cap1) =
  matchn re s [cap1]
match2g (In re) (In s) (Out cap1) (Out cap2) =
  matchn re s [cap1, cap2]
match3g (In re) (In s) (Out cap1) (Out cap2) (Out cap3) =
  matchn re s [cap1, cap2, cap3]
match4g (In re) (In s) (Out cap1) (Out cap2) (Out cap3) (Out cap4) =
  matchn re s [cap1, cap2, cap3, cap4]
match5g (In re) (In s) (Out cap1) (Out cap2) (Out cap3) (Out cap4) (Out cap5) =
  matchn re s [cap1, cap2, cap3, cap4, cap5]

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
