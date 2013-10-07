{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, TypeSynonymInstances #-}

module Language.HokeyLog.Prim where

import Control.Monad
import Control.Unification
import Language.HokeyLog.Monad
import Language.HokeyLog.Syntax

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
