{-# LANGUAGE GADTs #-}

{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module BasicsTest1 where

import Prelude hiding (max)
import Language.Haskell.Liquid.ProofCombinators hiding (withProof)
import qualified Data.Set as S

{-@ measure propOf :: a -> b @-}
{-@ type ProofOf E = { proofObj:_ | propOf proofObj = E } @-}

---------------------------------------------------------------------------
----- | TERMS of our language
---------------------------------------------------------------------------
type Vname = Int

data Basic = TBool         -- Bool
           | TInt          -- Int
           | BTV     Vname   -- a                    -- NEW!
           | FTV     Vname   -- a                    -- NEW!
  deriving (Eq, Show)

data Kind = Base         -- B, base kind
          | Star         -- *, star kind
  deriving (Eq, Show)

data FType = FTBasic Basic               -- b: Bool, Int, FTV a, BTV a
  deriving (Eq, Show)

  --- TYPING ENVIRONMENTS

data FEnv = FEmpty                       -- type FEnv = [(Vname, FType) or Vname]
          | FCons  Vname FType FEnv
          | FConsT Vname Kind  FEnv
  deriving (Show) 
{-@ data FEnv where
    FEmpty :: FEnv
    FCons  :: x:Vname -> t:FType -> { g:FEnv | not (in_envF x g) } -> FEnv
    FConsT :: a:Vname -> k:Kind  -> { g:FEnv | not (in_envF a g) } -> FEnv @-}

{-@ reflect in_envF @-}
in_envF :: Vname -> FEnv -> Bool
in_envF x g = S.member x (bindsF g) 

{-@ reflect tv_bound_inF @-}         -- type variables only
tv_bound_inF :: Vname -> Kind -> FEnv -> Bool
tv_bound_inF a k FEmpty                                   = False
tv_bound_inF a k (FCons x t g)    | (a == x)              = False
                                  | otherwise             = tv_bound_inF a k g
tv_bound_inF a k (FConsT a' k' g) | (a == a')             = (k == k')
                                  | otherwise             = tv_bound_inF a k g
{-@ reflect bindsF @-}
bindsF :: FEnv -> S.Set Vname
bindsF FEmpty         = S.empty
bindsF (FCons  x t g) = S.union (S.singleton x) (bindsF g)
bindsF (FConsT a k g) = S.union (S.singleton a) (bindsF g)

{-@ simple :: g:FEnv -> { a:Vname | in_envF a g } -> { k:Kind | tv_bound_inF a k g }
                -> { g':FEnv | not (in_envF a g') } @-}
simple :: FEnv -> Vname -> Kind -> FEnv
simple g a k  = case g of
  (FCons y s g')    -> case ( a == y ) of   
        (False)     -> simple g' a k
  (FConsT a' k' g') -> case ( a == a' ) of
        (True)      -> g'      
        (False)     -> simple g' a k
