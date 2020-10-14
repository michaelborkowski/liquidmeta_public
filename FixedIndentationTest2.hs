{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module FixedIndentationTest2 where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

import BasicsTest1

{-@ simple' :: g:FEnv -> { a:Vname | in_envF a g } -> { k:Kind | tv_bound_inF a k g }
                -> { g':FEnv | not (in_envF a g') } @-}
simple' :: FEnv -> Vname -> Kind -> FEnv
simple' g a k  = case g of
  (FCons y s g')    -> case ( a == y ) of   
        (False)     -> simple' g' a k
  (FConsT a' k' g') -> case ( a == a' ) of
        (True)      -> g'      
        (False)     -> simple' g' a k
