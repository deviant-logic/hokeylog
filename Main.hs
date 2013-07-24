{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Data.ByteString.Char8 as B
import Language.HokeyLog.Parser as P
import Language.HokeyLog.Program
import Language.HokeyLog.Syntax

import System.Remote.Monitoring
import System.Environment

main = do -- forkServer "localhost" 8000
          (file:_) <- getArgs
          w <- parseFile (program value) file
          putStrLn $ concat ["loaded ", show $ length w]
          qs <- getContents >>= return . lines
          let w' = init_table $ mapM postvaricate w
              qs' = fmap (postvaricate . parse (query value)) qs
              as = fmap (eval w' . ab . (>>=sld)) qs'
          mapM (mapM $ putStrLn . show) as

