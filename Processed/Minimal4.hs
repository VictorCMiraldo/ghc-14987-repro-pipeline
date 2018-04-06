{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PatternSynonyms        #-}
module Minimal where

import GHC.TypeLits (TypeError, ErrorMessage (..))
import Data.Proxy

data Nat = S Nat | Z
  deriving (Eq , Show)

data SNat :: Nat -> * where
  SZ ::           SNat Z
  SS :: SNat n -> SNat (S n)

type family Lkup (n :: Nat) (ks :: [k]) :: k where
  Lkup Z     (k : ks) = k
  Lkup (S n) (k : ks) = Lkup n ks
  Lkup _     '[]      = TypeError (Text "Lkup index too big")

data El :: [*] -> Nat -> * where
  El ::  {unEl :: Lkup ix fam} -> El fam ix

data NS :: (k -> *) -> [k] -> * where
  T :: NS p xs -> NS p (x : xs)
  H  :: p x     -> NS p (x : xs)

infixr 5 :*
data NP :: (k -> *) -> [k] -> * where
  NP0  :: NP p '[]
  (:*) :: p x -> NP p xs -> NP p (x : xs)

data Atom kon
  = K kon
  | I Nat
  deriving (Eq, Show)

data NA  :: (kon -> *) -> (Nat -> *) -> Atom kon -> * where
  NA_I :: phi k -> NA ki phi (I k) 
  NA_K :: ki  k -> NA ki phi (K k)

data Kon
  = KInt
  | KInteger
  | KFloat
  | KDouble
  | KBool
  | KChar
  | KString
  deriving (Eq , Show)


data Singl (kon :: Kon) :: * where
  SInt     :: Int     -> Singl KInt
  SInteger :: Integer -> Singl KInteger
  SFloat   :: Float   -> Singl KFloat
  SDouble  :: Double  -> Singl KDouble
  SBool    :: Bool    -> Singl KBool
  SChar    :: Char    -> Singl KChar
  SString  :: String  -> Singl KString

deriving instance Show (Singl k)
deriving instance Eq   (Singl k)

eqSingl :: Singl k -> Singl k -> Bool
eqSingl = (==)

class Family (ki :: kon -> *) (fam :: [*]) (codes :: [[[Atom kon]]])
      | fam -> ki codes , ki codes -> fam
  where
    sto'   :: SNat ix -> Rep ki (El fam) (Lkup ix codes) -> El fam ix
    sfrom' :: SNat ix -> El fam ix -> Rep ki (El fam) (Lkup ix codes)

newtype Rep (ki :: kon -> *) (phi :: Nat -> *) (code :: [[Atom kon]])
  = Rep { unRep :: NS (PoA ki phi) code }

type PoA (ki :: kon -> *) (phi :: Nat -> *) = NP (NA ki phi)

--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------
--------------------------------------------------------

data A 
   = A1 A B C D E F G
   | A2 A B C D E F G
   | A3 A B C D E F G
   | A4 A B C D E F G
   | A5 A B C D E F G
   | A6 A B C D E F G
   | A7 A B C D E F G
   | A8 A B C D E F G
   | A9 A B C D E F G
   | AA A B C D E F G
   | AB A B C D E F G
   | AC A B C D E F G
   | AD A B C D E F G
   | AE A B C D E F G
   | AF A B C D E F G
data B 
   = B1 A B C D E F G
   | B2 A B C D E F G
   | B3 A B C D E F G
   | B4 A B C D E F G
   | B5 A B C D E F G
   | B6 A B C D E F G
   | B7 A B C D E F G
   | B8 A B C D E F G
   | B9 A B C D E F G
   | BA A B C D E F G
   | BB A B C D E F G
   | BC A B C D E F G
   | BD A B C D E F G
   | BE A B C D E F G
   | BF A B C D E F G
data C
   = C1 A B C D E F G
   | C2 A B C D E F G
   | C3 A B C D E F G
   | C4 A B C D E F G
   | C5 A B C D E F G
   | C6 A B C D E F G
   | C7 A B C D E F G
   | C8 A B C D E F G
   | C9 A B C D E F G
   | CA A B C D E F G
   | CB A B C D E F G
   | CC A B C D E F G
   | CD A B C D E F G
   | CE A B C D E F G
   | CF A B C D E F G
data D
   = D1 A B C D E F G
   | D2 A B C D E F G
   | D3 A B C D E F G
   | D4 A B C D E F G
   | D5 A B C D E F G
   | D6 A B C D E F G
   | D7 A B C D E F G
   | D8 A B C D E F G
   | D9 A B C D E F G
   | DA A B C D E F G
   | DB A B C D E F G
   | DC A B C D E F G
   | DD A B C D E F G
   | DE A B C D E F G
   | DF A B C D E F G
data E
   = E1 A B C D E F G
   | E2 A B C D E F G
   | E3 A B C D E F G
   | E4 A B C D E F G
   | E5 A B C D E F G
   | E6 A B C D E F G
   | E7 A B C D E F G
   | E8 A B C D E F G
   | E9 A B C D E F G
   | EA A B C D E F G
   | EB A B C D E F G
   | EC A B C D E F G
   | ED A B C D E F G
   | EE A B C D E F G
   | EF A B C D E F G

data F {-
   = F1 A B C D E F G
   | F2 A B C D E F G
   | F3 A B C D E F G
   | F4 A B C D E F G
   | F5 A B C D E F G
   | F6 A B C D E F G
   | F7 A B C D E F G
   | F8 A B C D E F G
   | F9 A B C D E F G
   | FA A B C D E F G
   | FB A B C D E F G
   | FC A B C D E F G
   | FD A B C D E F G
   | FE A B C D E F G
   | FF A B C D E F G -}
data G {-
   = G1 A B C D E F G
   | G2 A B C D E F G
   | G3 A B C D E F G
   | G4 A B C D E F G
   | G5 A B C D E F G
   | G6 A B C D E F G
   | G7 A B C D E F G
   | G8 A B C D E F G
   | G9 A B C D E F G
   | GA A B C D E F G
   | GB A B C D E F G
   | GC A B C D E F G
   | GD A B C D E F G
   | GE A B C D E F G
   | GF A B C D E F G -}
type D0_ = Z
type D1_ = S Z
type D2_ = S (S Z)
type D3_ = S (S (S Z))
type D4_ = S (S (S (S Z)))
type D5_ = S (S (S (S (S Z))))
type D6_ = S (S (S (S (S (S Z)))))
type FamA = '[A, B, C, D, E, F, G]
type CodesA =
    '[ '[ '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]],
      '[ '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]],
      '[ '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]],
      '[ '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]],
      '[ '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]],
      '[],
      '[]]
pattern IdxA = SZ
pattern IdxB = SS SZ
pattern IdxC = SS (SS SZ)
pattern IdxD = SS (SS (SS SZ))
pattern IdxE = SS (SS (SS (SS SZ)))
pattern IdxF = SS (SS (SS (SS (SS SZ))))
pattern IdxG = SS (SS (SS (SS (SS (SS SZ)))))
pattern Pat4EF ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4EF d_aEs7 = T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEs7))))))))))))))
pattern Pat4EE ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4EE d_aEs6 = T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEs6)))))))))))))
pattern Pat4ED ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4ED d_aEs5 = T (T (T (T (T (T (T (T (T (T (T (T (H d_aEs5))))))))))))
pattern Pat4EC ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4EC d_aEs4 = T (T (T (T (T (T (T (T (T (T (T (H d_aEs4)))))))))))
pattern Pat4EB ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4EB d_aEs3 = T (T (T (T (T (T (T (T (T (T (H d_aEs3))))))))))
pattern Pat4EA ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4EA d_aEs2 = T (T (T (T (T (T (T (T (T (H d_aEs2)))))))))
pattern Pat4E9 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4E9 d_aEs1 = T (T (T (T (T (T (T (T (H d_aEs1))))))))
pattern Pat4E8 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4E8 d_aEs0 = T (T (T (T (T (T (T (H d_aEs0)))))))
pattern Pat4E7 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4E7 d_aErZ = T (T (T (T (T (T (H d_aErZ))))))
pattern Pat4E6 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4E6 d_aErY = T (T (T (T (T (H d_aErY)))))
pattern Pat4E5 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4E5 d_aErX = T (T (T (T (H d_aErX))))
pattern Pat4E4 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4E4 d_aErW = T (T (T (H d_aErW)))
pattern Pat4E3 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4E3 d_aErV = T (T (H d_aErV))
pattern Pat4E2 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4E2 d_aErU = T (H d_aErU)
pattern Pat4E1 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat4E1 d_aErT = H d_aErT
pattern Pat3DF ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3DF d_aErS = T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aErS))))))))))))))
pattern Pat3DE ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3DE d_aErR = T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aErR)))))))))))))
pattern Pat3DD ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3DD d_aErQ = T (T (T (T (T (T (T (T (T (T (T (T (H d_aErQ))))))))))))
pattern Pat3DC ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3DC d_aErP = T (T (T (T (T (T (T (T (T (T (T (H d_aErP)))))))))))
pattern Pat3DB ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3DB d_aErO = T (T (T (T (T (T (T (T (T (T (H d_aErO))))))))))
pattern Pat3DA ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3DA d_aErN = T (T (T (T (T (T (T (T (T (H d_aErN)))))))))
pattern Pat3D9 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3D9 d_aErM = T (T (T (T (T (T (T (T (H d_aErM))))))))
pattern Pat3D8 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3D8 d_aErL = T (T (T (T (T (T (T (H d_aErL)))))))
pattern Pat3D7 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3D7 d_aErK = T (T (T (T (T (T (H d_aErK))))))
pattern Pat3D6 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3D6 d_aErJ = T (T (T (T (T (H d_aErJ)))))
pattern Pat3D5 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3D5 d_aErI = T (T (T (T (H d_aErI))))
pattern Pat3D4 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3D4 d_aErH = T (T (T (H d_aErH)))
pattern Pat3D3 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3D3 d_aErG = T (T (H d_aErG))
pattern Pat3D2 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3D2 d_aErF = T (H d_aErF)
pattern Pat3D1 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat3D1 d_aErE = H d_aErE
pattern Pat2CF ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2CF d_aErD = T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aErD))))))))))))))
pattern Pat2CE ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2CE d_aErC = T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aErC)))))))))))))
pattern Pat2CD ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2CD d_aErB = T (T (T (T (T (T (T (T (T (T (T (T (H d_aErB))))))))))))
pattern Pat2CC ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2CC d_aErA = T (T (T (T (T (T (T (T (T (T (T (H d_aErA)))))))))))
pattern Pat2CB ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2CB d_aErz = T (T (T (T (T (T (T (T (T (T (H d_aErz))))))))))
pattern Pat2CA ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2CA d_aEry = T (T (T (T (T (T (T (T (T (H d_aEry)))))))))
pattern Pat2C9 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2C9 d_aErx = T (T (T (T (T (T (T (T (H d_aErx))))))))
pattern Pat2C8 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2C8 d_aErw = T (T (T (T (T (T (T (H d_aErw)))))))
pattern Pat2C7 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2C7 d_aErv = T (T (T (T (T (T (H d_aErv))))))
pattern Pat2C6 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2C6 d_aEru = T (T (T (T (T (H d_aEru)))))
pattern Pat2C5 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2C5 d_aErt = T (T (T (T (H d_aErt))))
pattern Pat2C4 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2C4 d_aErs = T (T (T (H d_aErs)))
pattern Pat2C3 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2C3 d_aErr = T (T (H d_aErr))
pattern Pat2C2 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2C2 d_aErq = T (H d_aErq)
pattern Pat2C1 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat2C1 d_aErp = H d_aErp
pattern Pat1BF ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1BF d_aEro = T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEro))))))))))))))
pattern Pat1BE ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1BE d_aErn = T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aErn)))))))))))))
pattern Pat1BD ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1BD d_aErm = T (T (T (T (T (T (T (T (T (T (T (T (H d_aErm))))))))))))
pattern Pat1BC ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1BC d_aErl = T (T (T (T (T (T (T (T (T (T (T (H d_aErl)))))))))))
pattern Pat1BB ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1BB d_aErk = T (T (T (T (T (T (T (T (T (T (H d_aErk))))))))))
pattern Pat1BA ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1BA d_aErj = T (T (T (T (T (T (T (T (T (H d_aErj)))))))))
pattern Pat1B9 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1B9 d_aEri = T (T (T (T (T (T (T (T (H d_aEri))))))))
pattern Pat1B8 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1B8 d_aErh = T (T (T (T (T (T (T (H d_aErh)))))))
pattern Pat1B7 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1B7 d_aErg = T (T (T (T (T (T (H d_aErg))))))
pattern Pat1B6 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1B6 d_aErf = T (T (T (T (T (H d_aErf)))))
pattern Pat1B5 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1B5 d_aEre = T (T (T (T (H d_aEre))))
pattern Pat1B4 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1B4 d_aErd = T (T (T (H d_aErd)))
pattern Pat1B3 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1B3 d_aErc = T (T (H d_aErc))
pattern Pat1B2 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1B2 d_aErb = T (H d_aErb)
pattern Pat1B1 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat1B1 d_aEra = H d_aEra
pattern Pat0AF ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0AF d_aEr9 = T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEr9))))))))))))))
pattern Pat0AE ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0AE d_aEr8 = T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEr8)))))))))))))
pattern Pat0AD ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0AD d_aEr7 = T (T (T (T (T (T (T (T (T (T (T (T (H d_aEr7))))))))))))
pattern Pat0AC ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0AC d_aEr6 = T (T (T (T (T (T (T (T (T (T (T (H d_aEr6)))))))))))
pattern Pat0AB ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0AB d_aEr5 = T (T (T (T (T (T (T (T (T (T (H d_aEr5))))))))))
pattern Pat0AA ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0AA d_aEr4 = T (T (T (T (T (T (T (T (T (H d_aEr4)))))))))
pattern Pat0A9 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0A9 d_aEr3 = T (T (T (T (T (T (T (T (H d_aEr3))))))))
pattern Pat0A8 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0A8 d_aEr2 = T (T (T (T (T (T (T (H d_aEr2)))))))
pattern Pat0A7 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0A7 d_aEr1 = T (T (T (T (T (T (H d_aEr1))))))
pattern Pat0A6 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0A6 d_aEr0 = T (T (T (T (T (H d_aEr0)))))
pattern Pat0A5 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0A5 d_aEqZ = T (T (T (T (H d_aEqZ))))
pattern Pat0A4 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0A4 d_aEqY = T (T (T (H d_aEqY)))
pattern Pat0A3 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0A3 d_aEqX = T (T (H d_aEqX))
pattern Pat0A2 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0A2 d_aEqW = T (H d_aEqW)
pattern Pat0A1 ::
          PoA Singl (El FamA) '[I D0_,
                                I D1_,
                                I D2_,
                                I D3_,
                                I D4_,
                                I D5_,
                                I D6_]
          -> NS (PoA Singl (El FamA)) '[ '[I D0_,
                                          I D1_,
                                          I D2_,
                                          I D3_,
                                          I D4_,
                                          I D5_,
                                          I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_],
                                        '[I D0_, I D1_, I D2_, I D3_, I D4_, I D5_, I D6_]]
pattern Pat0A1 d_aEqV = H d_aEqV
instance Family Singl FamA CodesA where
  sfrom'
    = \case
        IdxA
          -> \case
               (El (A1 x_aEs8 x_aEs9 x_aEsa x_aEsb x_aEsc x_aEsd x_aEse))
                 -> Rep
                      (Pat0A1
                         ((NA_I (El x_aEs8))
                            :*
                              ((NA_I (El x_aEs9))
                                 :*
                                   ((NA_I (El x_aEsa))
                                      :*
                                        ((NA_I (El x_aEsb))
                                           :*
                                             ((NA_I (El x_aEsc))
                                                :*
                                                  ((NA_I (El x_aEsd))
                                                     :* ((NA_I (El x_aEse)) :* NP0))))))))
               (El (A2 x_aEsf x_aEsg x_aEsh x_aEsi x_aEsj x_aEsk x_aEsl))
                 -> Rep
                      (Pat0A2
                         ((NA_I (El x_aEsf))
                            :*
                              ((NA_I (El x_aEsg))
                                 :*
                                   ((NA_I (El x_aEsh))
                                      :*
                                        ((NA_I (El x_aEsi))
                                           :*
                                             ((NA_I (El x_aEsj))
                                                :*
                                                  ((NA_I (El x_aEsk))
                                                     :* ((NA_I (El x_aEsl)) :* NP0))))))))
               (El (A3 x_aEsm x_aEsn x_aEso x_aEsp x_aEsq x_aEsr x_aEss))
                 -> Rep
                      (Pat0A3
                         ((NA_I (El x_aEsm))
                            :*
                              ((NA_I (El x_aEsn))
                                 :*
                                   ((NA_I (El x_aEso))
                                      :*
                                        ((NA_I (El x_aEsp))
                                           :*
                                             ((NA_I (El x_aEsq))
                                                :*
                                                  ((NA_I (El x_aEsr))
                                                     :* ((NA_I (El x_aEss)) :* NP0))))))))
               (El (A4 x_aEst x_aEsu x_aEsv x_aEsw x_aEsx x_aEsy x_aEsz))
                 -> Rep
                      (Pat0A4
                         ((NA_I (El x_aEst))
                            :*
                              ((NA_I (El x_aEsu))
                                 :*
                                   ((NA_I (El x_aEsv))
                                      :*
                                        ((NA_I (El x_aEsw))
                                           :*
                                             ((NA_I (El x_aEsx))
                                                :*
                                                  ((NA_I (El x_aEsy))
                                                     :* ((NA_I (El x_aEsz)) :* NP0))))))))
               (El (A5 x_aEsA x_aEsB x_aEsC x_aEsD x_aEsE x_aEsF x_aEsG))
                 -> Rep
                      (Pat0A5
                         ((NA_I (El x_aEsA))
                            :*
                              ((NA_I (El x_aEsB))
                                 :*
                                   ((NA_I (El x_aEsC))
                                      :*
                                        ((NA_I (El x_aEsD))
                                           :*
                                             ((NA_I (El x_aEsE))
                                                :*
                                                  ((NA_I (El x_aEsF))
                                                     :* ((NA_I (El x_aEsG)) :* NP0))))))))
               (El (A6 x_aEsH x_aEsI x_aEsJ x_aEsK x_aEsL x_aEsM x_aEsN))
                 -> Rep
                      (Pat0A6
                         ((NA_I (El x_aEsH))
                            :*
                              ((NA_I (El x_aEsI))
                                 :*
                                   ((NA_I (El x_aEsJ))
                                      :*
                                        ((NA_I (El x_aEsK))
                                           :*
                                             ((NA_I (El x_aEsL))
                                                :*
                                                  ((NA_I (El x_aEsM))
                                                     :* ((NA_I (El x_aEsN)) :* NP0))))))))
               (El (A7 x_aEsO x_aEsP x_aEsQ x_aEsR x_aEsS x_aEsT x_aEsU))
                 -> Rep
                      (Pat0A7
                         ((NA_I (El x_aEsO))
                            :*
                              ((NA_I (El x_aEsP))
                                 :*
                                   ((NA_I (El x_aEsQ))
                                      :*
                                        ((NA_I (El x_aEsR))
                                           :*
                                             ((NA_I (El x_aEsS))
                                                :*
                                                  ((NA_I (El x_aEsT))
                                                     :* ((NA_I (El x_aEsU)) :* NP0))))))))
               (El (A8 x_aEsV x_aEsW x_aEsX x_aEsY x_aEsZ x_aEt0 x_aEt1))
                 -> Rep
                      (Pat0A8
                         ((NA_I (El x_aEsV))
                            :*
                              ((NA_I (El x_aEsW))
                                 :*
                                   ((NA_I (El x_aEsX))
                                      :*
                                        ((NA_I (El x_aEsY))
                                           :*
                                             ((NA_I (El x_aEsZ))
                                                :*
                                                  ((NA_I (El x_aEt0))
                                                     :* ((NA_I (El x_aEt1)) :* NP0))))))))
               (El (A9 x_aEt2 x_aEt3 x_aEt4 x_aEt5 x_aEt6 x_aEt7 x_aEt8))
                 -> Rep
                      (Pat0A9
                         ((NA_I (El x_aEt2))
                            :*
                              ((NA_I (El x_aEt3))
                                 :*
                                   ((NA_I (El x_aEt4))
                                      :*
                                        ((NA_I (El x_aEt5))
                                           :*
                                             ((NA_I (El x_aEt6))
                                                :*
                                                  ((NA_I (El x_aEt7))
                                                     :* ((NA_I (El x_aEt8)) :* NP0))))))))
               (El (AA x_aEt9 x_aEta x_aEtb x_aEtc x_aEtd x_aEte x_aEtf))
                 -> Rep
                      (Pat0AA
                         ((NA_I (El x_aEt9))
                            :*
                              ((NA_I (El x_aEta))
                                 :*
                                   ((NA_I (El x_aEtb))
                                      :*
                                        ((NA_I (El x_aEtc))
                                           :*
                                             ((NA_I (El x_aEtd))
                                                :*
                                                  ((NA_I (El x_aEte))
                                                     :* ((NA_I (El x_aEtf)) :* NP0))))))))
               (El (AB x_aEtg x_aEth x_aEti x_aEtj x_aEtk x_aEtl x_aEtm))
                 -> Rep
                      (Pat0AB
                         ((NA_I (El x_aEtg))
                            :*
                              ((NA_I (El x_aEth))
                                 :*
                                   ((NA_I (El x_aEti))
                                      :*
                                        ((NA_I (El x_aEtj))
                                           :*
                                             ((NA_I (El x_aEtk))
                                                :*
                                                  ((NA_I (El x_aEtl))
                                                     :* ((NA_I (El x_aEtm)) :* NP0))))))))
               (El (AC x_aEtn x_aEto x_aEtp x_aEtq x_aEtr x_aEts x_aEtt))
                 -> Rep
                      (Pat0AC
                         ((NA_I (El x_aEtn))
                            :*
                              ((NA_I (El x_aEto))
                                 :*
                                   ((NA_I (El x_aEtp))
                                      :*
                                        ((NA_I (El x_aEtq))
                                           :*
                                             ((NA_I (El x_aEtr))
                                                :*
                                                  ((NA_I (El x_aEts))
                                                     :* ((NA_I (El x_aEtt)) :* NP0))))))))
               (El (AD x_aEtu x_aEtv x_aEtw x_aEtx x_aEty x_aEtz x_aEtA))
                 -> Rep
                      (Pat0AD
                         ((NA_I (El x_aEtu))
                            :*
                              ((NA_I (El x_aEtv))
                                 :*
                                   ((NA_I (El x_aEtw))
                                      :*
                                        ((NA_I (El x_aEtx))
                                           :*
                                             ((NA_I (El x_aEty))
                                                :*
                                                  ((NA_I (El x_aEtz))
                                                     :* ((NA_I (El x_aEtA)) :* NP0))))))))
               (El (AE x_aEtB x_aEtC x_aEtD x_aEtE x_aEtF x_aEtG x_aEtH))
                 -> Rep
                      (Pat0AE
                         ((NA_I (El x_aEtB))
                            :*
                              ((NA_I (El x_aEtC))
                                 :*
                                   ((NA_I (El x_aEtD))
                                      :*
                                        ((NA_I (El x_aEtE))
                                           :*
                                             ((NA_I (El x_aEtF))
                                                :*
                                                  ((NA_I (El x_aEtG))
                                                     :* ((NA_I (El x_aEtH)) :* NP0))))))))
               (El (AF x_aEtI x_aEtJ x_aEtK x_aEtL x_aEtM x_aEtN x_aEtO))
                 -> Rep
                      (Pat0AF
                         ((NA_I (El x_aEtI))
                            :*
                              ((NA_I (El x_aEtJ))
                                 :*
                                   ((NA_I (El x_aEtK))
                                      :*
                                        ((NA_I (El x_aEtL))
                                           :*
                                             ((NA_I (El x_aEtM))
                                                :*
                                                  ((NA_I (El x_aEtN))
                                                     :* ((NA_I (El x_aEtO)) :* NP0))))))))
        IdxB
          -> \case
               (El (B1 x_aEtP x_aEtQ x_aEtR x_aEtS x_aEtT x_aEtU x_aEtV))
                 -> Rep
                      (Pat1B1
                         ((NA_I (El x_aEtP))
                            :*
                              ((NA_I (El x_aEtQ))
                                 :*
                                   ((NA_I (El x_aEtR))
                                      :*
                                        ((NA_I (El x_aEtS))
                                           :*
                                             ((NA_I (El x_aEtT))
                                                :*
                                                  ((NA_I (El x_aEtU))
                                                     :* ((NA_I (El x_aEtV)) :* NP0))))))))
               (El (B2 x_aEtW x_aEtX x_aEtY x_aEtZ x_aEu0 x_aEu1 x_aEu2))
                 -> Rep
                      (Pat1B2
                         ((NA_I (El x_aEtW))
                            :*
                              ((NA_I (El x_aEtX))
                                 :*
                                   ((NA_I (El x_aEtY))
                                      :*
                                        ((NA_I (El x_aEtZ))
                                           :*
                                             ((NA_I (El x_aEu0))
                                                :*
                                                  ((NA_I (El x_aEu1))
                                                     :* ((NA_I (El x_aEu2)) :* NP0))))))))
               (El (B3 x_aEu3 x_aEu4 x_aEu5 x_aEu6 x_aEu7 x_aEu8 x_aEu9))
                 -> Rep
                      (Pat1B3
                         ((NA_I (El x_aEu3))
                            :*
                              ((NA_I (El x_aEu4))
                                 :*
                                   ((NA_I (El x_aEu5))
                                      :*
                                        ((NA_I (El x_aEu6))
                                           :*
                                             ((NA_I (El x_aEu7))
                                                :*
                                                  ((NA_I (El x_aEu8))
                                                     :* ((NA_I (El x_aEu9)) :* NP0))))))))
               (El (B4 x_aEua x_aEub x_aEuc x_aEud x_aEue x_aEuf x_aEug))
                 -> Rep
                      (Pat1B4
                         ((NA_I (El x_aEua))
                            :*
                              ((NA_I (El x_aEub))
                                 :*
                                   ((NA_I (El x_aEuc))
                                      :*
                                        ((NA_I (El x_aEud))
                                           :*
                                             ((NA_I (El x_aEue))
                                                :*
                                                  ((NA_I (El x_aEuf))
                                                     :* ((NA_I (El x_aEug)) :* NP0))))))))
               (El (B5 x_aEuh x_aEui x_aEuj x_aEuk x_aEul x_aEum x_aEun))
                 -> Rep
                      (Pat1B5
                         ((NA_I (El x_aEuh))
                            :*
                              ((NA_I (El x_aEui))
                                 :*
                                   ((NA_I (El x_aEuj))
                                      :*
                                        ((NA_I (El x_aEuk))
                                           :*
                                             ((NA_I (El x_aEul))
                                                :*
                                                  ((NA_I (El x_aEum))
                                                     :* ((NA_I (El x_aEun)) :* NP0))))))))
               (El (B6 x_aEuo x_aEup x_aEuq x_aEur x_aEus x_aEut x_aEuu))
                 -> Rep
                      (Pat1B6
                         ((NA_I (El x_aEuo))
                            :*
                              ((NA_I (El x_aEup))
                                 :*
                                   ((NA_I (El x_aEuq))
                                      :*
                                        ((NA_I (El x_aEur))
                                           :*
                                             ((NA_I (El x_aEus))
                                                :*
                                                  ((NA_I (El x_aEut))
                                                     :* ((NA_I (El x_aEuu)) :* NP0))))))))
               (El (B7 x_aEuv x_aEuw x_aEux x_aEuy x_aEuz x_aEuA x_aEuB))
                 -> Rep
                      (Pat1B7
                         ((NA_I (El x_aEuv))
                            :*
                              ((NA_I (El x_aEuw))
                                 :*
                                   ((NA_I (El x_aEux))
                                      :*
                                        ((NA_I (El x_aEuy))
                                           :*
                                             ((NA_I (El x_aEuz))
                                                :*
                                                  ((NA_I (El x_aEuA))
                                                     :* ((NA_I (El x_aEuB)) :* NP0))))))))
               (El (B8 x_aEuC x_aEuD x_aEuE x_aEuF x_aEuG x_aEuH x_aEuI))
                 -> Rep
                      (Pat1B8
                         ((NA_I (El x_aEuC))
                            :*
                              ((NA_I (El x_aEuD))
                                 :*
                                   ((NA_I (El x_aEuE))
                                      :*
                                        ((NA_I (El x_aEuF))
                                           :*
                                             ((NA_I (El x_aEuG))
                                                :*
                                                  ((NA_I (El x_aEuH))
                                                     :* ((NA_I (El x_aEuI)) :* NP0))))))))
               (El (B9 x_aEuJ x_aEuK x_aEuL x_aEuM x_aEuN x_aEuO x_aEuP))
                 -> Rep
                      (Pat1B9
                         ((NA_I (El x_aEuJ))
                            :*
                              ((NA_I (El x_aEuK))
                                 :*
                                   ((NA_I (El x_aEuL))
                                      :*
                                        ((NA_I (El x_aEuM))
                                           :*
                                             ((NA_I (El x_aEuN))
                                                :*
                                                  ((NA_I (El x_aEuO))
                                                     :* ((NA_I (El x_aEuP)) :* NP0))))))))
               (El (BA x_aEuQ x_aEuR x_aEuS x_aEuT x_aEuU x_aEuV x_aEuW))
                 -> Rep
                      (Pat1BA
                         ((NA_I (El x_aEuQ))
                            :*
                              ((NA_I (El x_aEuR))
                                 :*
                                   ((NA_I (El x_aEuS))
                                      :*
                                        ((NA_I (El x_aEuT))
                                           :*
                                             ((NA_I (El x_aEuU))
                                                :*
                                                  ((NA_I (El x_aEuV))
                                                     :* ((NA_I (El x_aEuW)) :* NP0))))))))
               (El (BB x_aEuX x_aEuY x_aEuZ x_aEv0 x_aEv1 x_aEv2 x_aEv3))
                 -> Rep
                      (Pat1BB
                         ((NA_I (El x_aEuX))
                            :*
                              ((NA_I (El x_aEuY))
                                 :*
                                   ((NA_I (El x_aEuZ))
                                      :*
                                        ((NA_I (El x_aEv0))
                                           :*
                                             ((NA_I (El x_aEv1))
                                                :*
                                                  ((NA_I (El x_aEv2))
                                                     :* ((NA_I (El x_aEv3)) :* NP0))))))))
               (El (BC x_aEv4 x_aEv5 x_aEv6 x_aEv7 x_aEv8 x_aEv9 x_aEva))
                 -> Rep
                      (Pat1BC
                         ((NA_I (El x_aEv4))
                            :*
                              ((NA_I (El x_aEv5))
                                 :*
                                   ((NA_I (El x_aEv6))
                                      :*
                                        ((NA_I (El x_aEv7))
                                           :*
                                             ((NA_I (El x_aEv8))
                                                :*
                                                  ((NA_I (El x_aEv9))
                                                     :* ((NA_I (El x_aEva)) :* NP0))))))))
               (El (BD x_aEvb x_aEvc x_aEvd x_aEve x_aEvf x_aEvg x_aEvh))
                 -> Rep
                      (Pat1BD
                         ((NA_I (El x_aEvb))
                            :*
                              ((NA_I (El x_aEvc))
                                 :*
                                   ((NA_I (El x_aEvd))
                                      :*
                                        ((NA_I (El x_aEve))
                                           :*
                                             ((NA_I (El x_aEvf))
                                                :*
                                                  ((NA_I (El x_aEvg))
                                                     :* ((NA_I (El x_aEvh)) :* NP0))))))))
               (El (BE x_aEvi x_aEvj x_aEvk x_aEvl x_aEvm x_aEvn x_aEvo))
                 -> Rep
                      (Pat1BE
                         ((NA_I (El x_aEvi))
                            :*
                              ((NA_I (El x_aEvj))
                                 :*
                                   ((NA_I (El x_aEvk))
                                      :*
                                        ((NA_I (El x_aEvl))
                                           :*
                                             ((NA_I (El x_aEvm))
                                                :*
                                                  ((NA_I (El x_aEvn))
                                                     :* ((NA_I (El x_aEvo)) :* NP0))))))))
               (El (BF x_aEvp x_aEvq x_aEvr x_aEvs x_aEvt x_aEvu x_aEvv))
                 -> Rep
                      (Pat1BF
                         ((NA_I (El x_aEvp))
                            :*
                              ((NA_I (El x_aEvq))
                                 :*
                                   ((NA_I (El x_aEvr))
                                      :*
                                        ((NA_I (El x_aEvs))
                                           :*
                                             ((NA_I (El x_aEvt))
                                                :*
                                                  ((NA_I (El x_aEvu))
                                                     :* ((NA_I (El x_aEvv)) :* NP0))))))))
        IdxC
          -> \case
               (El (C1 x_aEvw x_aEvx x_aEvy x_aEvz x_aEvA x_aEvB x_aEvC))
                 -> Rep
                      (Pat2C1
                         ((NA_I (El x_aEvw))
                            :*
                              ((NA_I (El x_aEvx))
                                 :*
                                   ((NA_I (El x_aEvy))
                                      :*
                                        ((NA_I (El x_aEvz))
                                           :*
                                             ((NA_I (El x_aEvA))
                                                :*
                                                  ((NA_I (El x_aEvB))
                                                     :* ((NA_I (El x_aEvC)) :* NP0))))))))
               (El (C2 x_aEvD x_aEvE x_aEvF x_aEvG x_aEvH x_aEvI x_aEvJ))
                 -> Rep
                      (Pat2C2
                         ((NA_I (El x_aEvD))
                            :*
                              ((NA_I (El x_aEvE))
                                 :*
                                   ((NA_I (El x_aEvF))
                                      :*
                                        ((NA_I (El x_aEvG))
                                           :*
                                             ((NA_I (El x_aEvH))
                                                :*
                                                  ((NA_I (El x_aEvI))
                                                     :* ((NA_I (El x_aEvJ)) :* NP0))))))))
               (El (C3 x_aEvK x_aEvL x_aEvM x_aEvN x_aEvO x_aEvP x_aEvQ))
                 -> Rep
                      (Pat2C3
                         ((NA_I (El x_aEvK))
                            :*
                              ((NA_I (El x_aEvL))
                                 :*
                                   ((NA_I (El x_aEvM))
                                      :*
                                        ((NA_I (El x_aEvN))
                                           :*
                                             ((NA_I (El x_aEvO))
                                                :*
                                                  ((NA_I (El x_aEvP))
                                                     :* ((NA_I (El x_aEvQ)) :* NP0))))))))
               (El (C4 x_aEvR x_aEvS x_aEvT x_aEvU x_aEvV x_aEvW x_aEvX))
                 -> Rep
                      (Pat2C4
                         ((NA_I (El x_aEvR))
                            :*
                              ((NA_I (El x_aEvS))
                                 :*
                                   ((NA_I (El x_aEvT))
                                      :*
                                        ((NA_I (El x_aEvU))
                                           :*
                                             ((NA_I (El x_aEvV))
                                                :*
                                                  ((NA_I (El x_aEvW))
                                                     :* ((NA_I (El x_aEvX)) :* NP0))))))))
               (El (C5 x_aEvY x_aEvZ x_aEw0 x_aEw1 x_aEw2 x_aEw3 x_aEw4))
                 -> Rep
                      (Pat2C5
                         ((NA_I (El x_aEvY))
                            :*
                              ((NA_I (El x_aEvZ))
                                 :*
                                   ((NA_I (El x_aEw0))
                                      :*
                                        ((NA_I (El x_aEw1))
                                           :*
                                             ((NA_I (El x_aEw2))
                                                :*
                                                  ((NA_I (El x_aEw3))
                                                     :* ((NA_I (El x_aEw4)) :* NP0))))))))
               (El (C6 x_aEw5 x_aEw6 x_aEw7 x_aEw8 x_aEw9 x_aEwa x_aEwb))
                 -> Rep
                      (Pat2C6
                         ((NA_I (El x_aEw5))
                            :*
                              ((NA_I (El x_aEw6))
                                 :*
                                   ((NA_I (El x_aEw7))
                                      :*
                                        ((NA_I (El x_aEw8))
                                           :*
                                             ((NA_I (El x_aEw9))
                                                :*
                                                  ((NA_I (El x_aEwa))
                                                     :* ((NA_I (El x_aEwb)) :* NP0))))))))
               (El (C7 x_aEwc x_aEwd x_aEwe x_aEwf x_aEwg x_aEwh x_aEwi))
                 -> Rep
                      (Pat2C7
                         ((NA_I (El x_aEwc))
                            :*
                              ((NA_I (El x_aEwd))
                                 :*
                                   ((NA_I (El x_aEwe))
                                      :*
                                        ((NA_I (El x_aEwf))
                                           :*
                                             ((NA_I (El x_aEwg))
                                                :*
                                                  ((NA_I (El x_aEwh))
                                                     :* ((NA_I (El x_aEwi)) :* NP0))))))))
               (El (C8 x_aEwj x_aEwk x_aEwl x_aEwm x_aEwn x_aEwo x_aEwp))
                 -> Rep
                      (Pat2C8
                         ((NA_I (El x_aEwj))
                            :*
                              ((NA_I (El x_aEwk))
                                 :*
                                   ((NA_I (El x_aEwl))
                                      :*
                                        ((NA_I (El x_aEwm))
                                           :*
                                             ((NA_I (El x_aEwn))
                                                :*
                                                  ((NA_I (El x_aEwo))
                                                     :* ((NA_I (El x_aEwp)) :* NP0))))))))
               (El (C9 x_aEwq x_aEwr x_aEws x_aEwt x_aEwu x_aEwv x_aEww))
                 -> Rep
                      (Pat2C9
                         ((NA_I (El x_aEwq))
                            :*
                              ((NA_I (El x_aEwr))
                                 :*
                                   ((NA_I (El x_aEws))
                                      :*
                                        ((NA_I (El x_aEwt))
                                           :*
                                             ((NA_I (El x_aEwu))
                                                :*
                                                  ((NA_I (El x_aEwv))
                                                     :* ((NA_I (El x_aEww)) :* NP0))))))))
               (El (CA x_aEwx x_aEwy x_aEwz x_aEwA x_aEwB x_aEwC x_aEwD))
                 -> Rep
                      (Pat2CA
                         ((NA_I (El x_aEwx))
                            :*
                              ((NA_I (El x_aEwy))
                                 :*
                                   ((NA_I (El x_aEwz))
                                      :*
                                        ((NA_I (El x_aEwA))
                                           :*
                                             ((NA_I (El x_aEwB))
                                                :*
                                                  ((NA_I (El x_aEwC))
                                                     :* ((NA_I (El x_aEwD)) :* NP0))))))))
               (El (CB x_aEwE x_aEwF x_aEwG x_aEwH x_aEwI x_aEwJ x_aEwK))
                 -> Rep
                      (Pat2CB
                         ((NA_I (El x_aEwE))
                            :*
                              ((NA_I (El x_aEwF))
                                 :*
                                   ((NA_I (El x_aEwG))
                                      :*
                                        ((NA_I (El x_aEwH))
                                           :*
                                             ((NA_I (El x_aEwI))
                                                :*
                                                  ((NA_I (El x_aEwJ))
                                                     :* ((NA_I (El x_aEwK)) :* NP0))))))))
               (El (CC x_aEwL x_aEwM x_aEwN x_aEwO x_aEwP x_aEwQ x_aEwR))
                 -> Rep
                      (Pat2CC
                         ((NA_I (El x_aEwL))
                            :*
                              ((NA_I (El x_aEwM))
                                 :*
                                   ((NA_I (El x_aEwN))
                                      :*
                                        ((NA_I (El x_aEwO))
                                           :*
                                             ((NA_I (El x_aEwP))
                                                :*
                                                  ((NA_I (El x_aEwQ))
                                                     :* ((NA_I (El x_aEwR)) :* NP0))))))))
               (El (CD x_aEwS x_aEwT x_aEwU x_aEwV x_aEwW x_aEwX x_aEwY))
                 -> Rep
                      (Pat2CD
                         ((NA_I (El x_aEwS))
                            :*
                              ((NA_I (El x_aEwT))
                                 :*
                                   ((NA_I (El x_aEwU))
                                      :*
                                        ((NA_I (El x_aEwV))
                                           :*
                                             ((NA_I (El x_aEwW))
                                                :*
                                                  ((NA_I (El x_aEwX))
                                                     :* ((NA_I (El x_aEwY)) :* NP0))))))))
               (El (CE x_aEwZ x_aEx0 x_aEx1 x_aEx2 x_aEx3 x_aEx4 x_aEx5))
                 -> Rep
                      (Pat2CE
                         ((NA_I (El x_aEwZ))
                            :*
                              ((NA_I (El x_aEx0))
                                 :*
                                   ((NA_I (El x_aEx1))
                                      :*
                                        ((NA_I (El x_aEx2))
                                           :*
                                             ((NA_I (El x_aEx3))
                                                :*
                                                  ((NA_I (El x_aEx4))
                                                     :* ((NA_I (El x_aEx5)) :* NP0))))))))
               (El (CF x_aEx6 x_aEx7 x_aEx8 x_aEx9 x_aExa x_aExb x_aExc))
                 -> Rep
                      (Pat2CF
                         ((NA_I (El x_aEx6))
                            :*
                              ((NA_I (El x_aEx7))
                                 :*
                                   ((NA_I (El x_aEx8))
                                      :*
                                        ((NA_I (El x_aEx9))
                                           :*
                                             ((NA_I (El x_aExa))
                                                :*
                                                  ((NA_I (El x_aExb))
                                                     :* ((NA_I (El x_aExc)) :* NP0))))))))
        IdxD
          -> \case
               (El (D1 x_aExd x_aExe x_aExf x_aExg x_aExh x_aExi x_aExj))
                 -> Rep
                      (Pat3D1
                         ((NA_I (El x_aExd))
                            :*
                              ((NA_I (El x_aExe))
                                 :*
                                   ((NA_I (El x_aExf))
                                      :*
                                        ((NA_I (El x_aExg))
                                           :*
                                             ((NA_I (El x_aExh))
                                                :*
                                                  ((NA_I (El x_aExi))
                                                     :* ((NA_I (El x_aExj)) :* NP0))))))))
               (El (D2 x_aExk x_aExl x_aExm x_aExn x_aExo x_aExp x_aExq))
                 -> Rep
                      (Pat3D2
                         ((NA_I (El x_aExk))
                            :*
                              ((NA_I (El x_aExl))
                                 :*
                                   ((NA_I (El x_aExm))
                                      :*
                                        ((NA_I (El x_aExn))
                                           :*
                                             ((NA_I (El x_aExo))
                                                :*
                                                  ((NA_I (El x_aExp))
                                                     :* ((NA_I (El x_aExq)) :* NP0))))))))
               (El (D3 x_aExr x_aExs x_aExt x_aExu x_aExv x_aExw x_aExx))
                 -> Rep
                      (Pat3D3
                         ((NA_I (El x_aExr))
                            :*
                              ((NA_I (El x_aExs))
                                 :*
                                   ((NA_I (El x_aExt))
                                      :*
                                        ((NA_I (El x_aExu))
                                           :*
                                             ((NA_I (El x_aExv))
                                                :*
                                                  ((NA_I (El x_aExw))
                                                     :* ((NA_I (El x_aExx)) :* NP0))))))))
               (El (D4 x_aExy x_aExz x_aExA x_aExB x_aExC x_aExD x_aExE))
                 -> Rep
                      (Pat3D4
                         ((NA_I (El x_aExy))
                            :*
                              ((NA_I (El x_aExz))
                                 :*
                                   ((NA_I (El x_aExA))
                                      :*
                                        ((NA_I (El x_aExB))
                                           :*
                                             ((NA_I (El x_aExC))
                                                :*
                                                  ((NA_I (El x_aExD))
                                                     :* ((NA_I (El x_aExE)) :* NP0))))))))
               (El (D5 x_aExF x_aExG x_aExH x_aExI x_aExJ x_aExK x_aExL))
                 -> Rep
                      (Pat3D5
                         ((NA_I (El x_aExF))
                            :*
                              ((NA_I (El x_aExG))
                                 :*
                                   ((NA_I (El x_aExH))
                                      :*
                                        ((NA_I (El x_aExI))
                                           :*
                                             ((NA_I (El x_aExJ))
                                                :*
                                                  ((NA_I (El x_aExK))
                                                     :* ((NA_I (El x_aExL)) :* NP0))))))))
               (El (D6 x_aExM x_aExN x_aExO x_aExP x_aExQ x_aExR x_aExS))
                 -> Rep
                      (Pat3D6
                         ((NA_I (El x_aExM))
                            :*
                              ((NA_I (El x_aExN))
                                 :*
                                   ((NA_I (El x_aExO))
                                      :*
                                        ((NA_I (El x_aExP))
                                           :*
                                             ((NA_I (El x_aExQ))
                                                :*
                                                  ((NA_I (El x_aExR))
                                                     :* ((NA_I (El x_aExS)) :* NP0))))))))
               (El (D7 x_aExT x_aExU x_aExV x_aExW x_aExX x_aExY x_aExZ))
                 -> Rep
                      (Pat3D7
                         ((NA_I (El x_aExT))
                            :*
                              ((NA_I (El x_aExU))
                                 :*
                                   ((NA_I (El x_aExV))
                                      :*
                                        ((NA_I (El x_aExW))
                                           :*
                                             ((NA_I (El x_aExX))
                                                :*
                                                  ((NA_I (El x_aExY))
                                                     :* ((NA_I (El x_aExZ)) :* NP0))))))))
               (El (D8 x_aEy0 x_aEy1 x_aEy2 x_aEy3 x_aEy4 x_aEy5 x_aEy6))
                 -> Rep
                      (Pat3D8
                         ((NA_I (El x_aEy0))
                            :*
                              ((NA_I (El x_aEy1))
                                 :*
                                   ((NA_I (El x_aEy2))
                                      :*
                                        ((NA_I (El x_aEy3))
                                           :*
                                             ((NA_I (El x_aEy4))
                                                :*
                                                  ((NA_I (El x_aEy5))
                                                     :* ((NA_I (El x_aEy6)) :* NP0))))))))
               (El (D9 x_aEy7 x_aEy8 x_aEy9 x_aEya x_aEyb x_aEyc x_aEyd))
                 -> Rep
                      (Pat3D9
                         ((NA_I (El x_aEy7))
                            :*
                              ((NA_I (El x_aEy8))
                                 :*
                                   ((NA_I (El x_aEy9))
                                      :*
                                        ((NA_I (El x_aEya))
                                           :*
                                             ((NA_I (El x_aEyb))
                                                :*
                                                  ((NA_I (El x_aEyc))
                                                     :* ((NA_I (El x_aEyd)) :* NP0))))))))
               (El (DA x_aEye x_aEyf x_aEyg x_aEyh x_aEyi x_aEyj x_aEyk))
                 -> Rep
                      (Pat3DA
                         ((NA_I (El x_aEye))
                            :*
                              ((NA_I (El x_aEyf))
                                 :*
                                   ((NA_I (El x_aEyg))
                                      :*
                                        ((NA_I (El x_aEyh))
                                           :*
                                             ((NA_I (El x_aEyi))
                                                :*
                                                  ((NA_I (El x_aEyj))
                                                     :* ((NA_I (El x_aEyk)) :* NP0))))))))
               (El (DB x_aEyl x_aEym x_aEyn x_aEyo x_aEyp x_aEyq x_aEyr))
                 -> Rep
                      (Pat3DB
                         ((NA_I (El x_aEyl))
                            :*
                              ((NA_I (El x_aEym))
                                 :*
                                   ((NA_I (El x_aEyn))
                                      :*
                                        ((NA_I (El x_aEyo))
                                           :*
                                             ((NA_I (El x_aEyp))
                                                :*
                                                  ((NA_I (El x_aEyq))
                                                     :* ((NA_I (El x_aEyr)) :* NP0))))))))
               (El (DC x_aEys x_aEyt x_aEyu x_aEyv x_aEyw x_aEyx x_aEyy))
                 -> Rep
                      (Pat3DC
                         ((NA_I (El x_aEys))
                            :*
                              ((NA_I (El x_aEyt))
                                 :*
                                   ((NA_I (El x_aEyu))
                                      :*
                                        ((NA_I (El x_aEyv))
                                           :*
                                             ((NA_I (El x_aEyw))
                                                :*
                                                  ((NA_I (El x_aEyx))
                                                     :* ((NA_I (El x_aEyy)) :* NP0))))))))
               (El (DD x_aEyz x_aEyA x_aEyB x_aEyC x_aEyD x_aEyE x_aEyF))
                 -> Rep
                      (Pat3DD
                         ((NA_I (El x_aEyz))
                            :*
                              ((NA_I (El x_aEyA))
                                 :*
                                   ((NA_I (El x_aEyB))
                                      :*
                                        ((NA_I (El x_aEyC))
                                           :*
                                             ((NA_I (El x_aEyD))
                                                :*
                                                  ((NA_I (El x_aEyE))
                                                     :* ((NA_I (El x_aEyF)) :* NP0))))))))
               (El (DE x_aEyG x_aEyH x_aEyI x_aEyJ x_aEyK x_aEyL x_aEyM))
                 -> Rep
                      (Pat3DE
                         ((NA_I (El x_aEyG))
                            :*
                              ((NA_I (El x_aEyH))
                                 :*
                                   ((NA_I (El x_aEyI))
                                      :*
                                        ((NA_I (El x_aEyJ))
                                           :*
                                             ((NA_I (El x_aEyK))
                                                :*
                                                  ((NA_I (El x_aEyL))
                                                     :* ((NA_I (El x_aEyM)) :* NP0))))))))
               (El (DF x_aEyN x_aEyO x_aEyP x_aEyQ x_aEyR x_aEyS x_aEyT))
                 -> Rep
                      (Pat3DF
                         ((NA_I (El x_aEyN))
                            :*
                              ((NA_I (El x_aEyO))
                                 :*
                                   ((NA_I (El x_aEyP))
                                      :*
                                        ((NA_I (El x_aEyQ))
                                           :*
                                             ((NA_I (El x_aEyR))
                                                :*
                                                  ((NA_I (El x_aEyS))
                                                     :* ((NA_I (El x_aEyT)) :* NP0))))))))
        IdxE
          -> \case
               (El (E1 x_aEyU x_aEyV x_aEyW x_aEyX x_aEyY x_aEyZ x_aEz0))
                 -> Rep
                      (Pat4E1
                         ((NA_I (El x_aEyU))
                            :*
                              ((NA_I (El x_aEyV))
                                 :*
                                   ((NA_I (El x_aEyW))
                                      :*
                                        ((NA_I (El x_aEyX))
                                           :*
                                             ((NA_I (El x_aEyY))
                                                :*
                                                  ((NA_I (El x_aEyZ))
                                                     :* ((NA_I (El x_aEz0)) :* NP0))))))))
               (El (E2 x_aEz1 x_aEz2 x_aEz3 x_aEz4 x_aEz5 x_aEz6 x_aEz7))
                 -> Rep
                      (Pat4E2
                         ((NA_I (El x_aEz1))
                            :*
                              ((NA_I (El x_aEz2))
                                 :*
                                   ((NA_I (El x_aEz3))
                                      :*
                                        ((NA_I (El x_aEz4))
                                           :*
                                             ((NA_I (El x_aEz5))
                                                :*
                                                  ((NA_I (El x_aEz6))
                                                     :* ((NA_I (El x_aEz7)) :* NP0))))))))
               (El (E3 x_aEz8 x_aEz9 x_aEza x_aEzb x_aEzc x_aEzd x_aEze))
                 -> Rep
                      (Pat4E3
                         ((NA_I (El x_aEz8))
                            :*
                              ((NA_I (El x_aEz9))
                                 :*
                                   ((NA_I (El x_aEza))
                                      :*
                                        ((NA_I (El x_aEzb))
                                           :*
                                             ((NA_I (El x_aEzc))
                                                :*
                                                  ((NA_I (El x_aEzd))
                                                     :* ((NA_I (El x_aEze)) :* NP0))))))))
               (El (E4 x_aEzf x_aEzg x_aEzh x_aEzi x_aEzj x_aEzk x_aEzl))
                 -> Rep
                      (Pat4E4
                         ((NA_I (El x_aEzf))
                            :*
                              ((NA_I (El x_aEzg))
                                 :*
                                   ((NA_I (El x_aEzh))
                                      :*
                                        ((NA_I (El x_aEzi))
                                           :*
                                             ((NA_I (El x_aEzj))
                                                :*
                                                  ((NA_I (El x_aEzk))
                                                     :* ((NA_I (El x_aEzl)) :* NP0))))))))
               (El (E5 x_aEzm x_aEzn x_aEzo x_aEzp x_aEzq x_aEzr x_aEzs))
                 -> Rep
                      (Pat4E5
                         ((NA_I (El x_aEzm))
                            :*
                              ((NA_I (El x_aEzn))
                                 :*
                                   ((NA_I (El x_aEzo))
                                      :*
                                        ((NA_I (El x_aEzp))
                                           :*
                                             ((NA_I (El x_aEzq))
                                                :*
                                                  ((NA_I (El x_aEzr))
                                                     :* ((NA_I (El x_aEzs)) :* NP0))))))))
               (El (E6 x_aEzt x_aEzu x_aEzv x_aEzw x_aEzx x_aEzy x_aEzz))
                 -> Rep
                      (Pat4E6
                         ((NA_I (El x_aEzt))
                            :*
                              ((NA_I (El x_aEzu))
                                 :*
                                   ((NA_I (El x_aEzv))
                                      :*
                                        ((NA_I (El x_aEzw))
                                           :*
                                             ((NA_I (El x_aEzx))
                                                :*
                                                  ((NA_I (El x_aEzy))
                                                     :* ((NA_I (El x_aEzz)) :* NP0))))))))
               (El (E7 x_aEzA x_aEzB x_aEzC x_aEzD x_aEzE x_aEzF x_aEzG))
                 -> Rep
                      (Pat4E7
                         ((NA_I (El x_aEzA))
                            :*
                              ((NA_I (El x_aEzB))
                                 :*
                                   ((NA_I (El x_aEzC))
                                      :*
                                        ((NA_I (El x_aEzD))
                                           :*
                                             ((NA_I (El x_aEzE))
                                                :*
                                                  ((NA_I (El x_aEzF))
                                                     :* ((NA_I (El x_aEzG)) :* NP0))))))))
               (El (E8 x_aEzH x_aEzI x_aEzJ x_aEzK x_aEzL x_aEzM x_aEzN))
                 -> Rep
                      (Pat4E8
                         ((NA_I (El x_aEzH))
                            :*
                              ((NA_I (El x_aEzI))
                                 :*
                                   ((NA_I (El x_aEzJ))
                                      :*
                                        ((NA_I (El x_aEzK))
                                           :*
                                             ((NA_I (El x_aEzL))
                                                :*
                                                  ((NA_I (El x_aEzM))
                                                     :* ((NA_I (El x_aEzN)) :* NP0))))))))
               (El (E9 x_aEzO x_aEzP x_aEzQ x_aEzR x_aEzS x_aEzT x_aEzU))
                 -> Rep
                      (Pat4E9
                         ((NA_I (El x_aEzO))
                            :*
                              ((NA_I (El x_aEzP))
                                 :*
                                   ((NA_I (El x_aEzQ))
                                      :*
                                        ((NA_I (El x_aEzR))
                                           :*
                                             ((NA_I (El x_aEzS))
                                                :*
                                                  ((NA_I (El x_aEzT))
                                                     :* ((NA_I (El x_aEzU)) :* NP0))))))))
               (El (EA x_aEzV x_aEzW x_aEzX x_aEzY x_aEzZ x_aEA0 x_aEA1))
                 -> Rep
                      (Pat4EA
                         ((NA_I (El x_aEzV))
                            :*
                              ((NA_I (El x_aEzW))
                                 :*
                                   ((NA_I (El x_aEzX))
                                      :*
                                        ((NA_I (El x_aEzY))
                                           :*
                                             ((NA_I (El x_aEzZ))
                                                :*
                                                  ((NA_I (El x_aEA0))
                                                     :* ((NA_I (El x_aEA1)) :* NP0))))))))
               (El (EB x_aEA2 x_aEA3 x_aEA4 x_aEA5 x_aEA6 x_aEA7 x_aEA8))
                 -> Rep
                      (Pat4EB
                         ((NA_I (El x_aEA2))
                            :*
                              ((NA_I (El x_aEA3))
                                 :*
                                   ((NA_I (El x_aEA4))
                                      :*
                                        ((NA_I (El x_aEA5))
                                           :*
                                             ((NA_I (El x_aEA6))
                                                :*
                                                  ((NA_I (El x_aEA7))
                                                     :* ((NA_I (El x_aEA8)) :* NP0))))))))
               (El (EC x_aEA9 x_aEAa x_aEAb x_aEAc x_aEAd x_aEAe x_aEAf))
                 -> Rep
                      (Pat4EC
                         ((NA_I (El x_aEA9))
                            :*
                              ((NA_I (El x_aEAa))
                                 :*
                                   ((NA_I (El x_aEAb))
                                      :*
                                        ((NA_I (El x_aEAc))
                                           :*
                                             ((NA_I (El x_aEAd))
                                                :*
                                                  ((NA_I (El x_aEAe))
                                                     :* ((NA_I (El x_aEAf)) :* NP0))))))))
               (El (ED x_aEAg x_aEAh x_aEAi x_aEAj x_aEAk x_aEAl x_aEAm))
                 -> Rep
                      (Pat4ED
                         ((NA_I (El x_aEAg))
                            :*
                              ((NA_I (El x_aEAh))
                                 :*
                                   ((NA_I (El x_aEAi))
                                      :*
                                        ((NA_I (El x_aEAj))
                                           :*
                                             ((NA_I (El x_aEAk))
                                                :*
                                                  ((NA_I (El x_aEAl))
                                                     :* ((NA_I (El x_aEAm)) :* NP0))))))))
               (El (EE x_aEAn x_aEAo x_aEAp x_aEAq x_aEAr x_aEAs x_aEAt))
                 -> Rep
                      (Pat4EE
                         ((NA_I (El x_aEAn))
                            :*
                              ((NA_I (El x_aEAo))
                                 :*
                                   ((NA_I (El x_aEAp))
                                      :*
                                        ((NA_I (El x_aEAq))
                                           :*
                                             ((NA_I (El x_aEAr))
                                                :*
                                                  ((NA_I (El x_aEAs))
                                                     :* ((NA_I (El x_aEAt)) :* NP0))))))))
               (El (EF x_aEAu x_aEAv x_aEAw x_aEAx x_aEAy x_aEAz x_aEAA))
                 -> Rep
                      (Pat4EF
                         ((NA_I (El x_aEAu))
                            :*
                              ((NA_I (El x_aEAv))
                                 :*
                                   ((NA_I (El x_aEAw))
                                      :*
                                        ((NA_I (El x_aEAx))
                                           :*
                                             ((NA_I (El x_aEAy))
                                                :*
                                                  ((NA_I (El x_aEAz))
                                                     :* ((NA_I (El x_aEAA)) :* NP0))))))))
        IdxF -> \case
        IdxG -> \case
  sto'
    = \case
        IdxA
          -> \case
               (Rep (Pat0A1 (NA_I (El y_aEAB) :* (NA_I (El y_aEAC) :* (NA_I (El y_aEAD) :* (NA_I (El y_aEAE) :* (NA_I (El y_aEAF) :* (NA_I (El y_aEAG) :* (NA_I (El y_aEAH) :* NP0)))))))))
                 -> El
                      (((((((A1 y_aEAB) y_aEAC) y_aEAD) y_aEAE) y_aEAF) y_aEAG) y_aEAH)
               (Rep (Pat0A2 (NA_I (El y_aEAI) :* (NA_I (El y_aEAJ) :* (NA_I (El y_aEAK) :* (NA_I (El y_aEAL) :* (NA_I (El y_aEAM) :* (NA_I (El y_aEAN) :* (NA_I (El y_aEAO) :* NP0)))))))))
                 -> El
                      (((((((A2 y_aEAI) y_aEAJ) y_aEAK) y_aEAL) y_aEAM) y_aEAN) y_aEAO)
               (Rep (Pat0A3 (NA_I (El y_aEAP) :* (NA_I (El y_aEAQ) :* (NA_I (El y_aEAR) :* (NA_I (El y_aEAS) :* (NA_I (El y_aEAT) :* (NA_I (El y_aEAU) :* (NA_I (El y_aEAV) :* NP0)))))))))
                 -> El
                      (((((((A3 y_aEAP) y_aEAQ) y_aEAR) y_aEAS) y_aEAT) y_aEAU) y_aEAV)
               (Rep (Pat0A4 (NA_I (El y_aEAW) :* (NA_I (El y_aEAX) :* (NA_I (El y_aEAY) :* (NA_I (El y_aEAZ) :* (NA_I (El y_aEB0) :* (NA_I (El y_aEB1) :* (NA_I (El y_aEB2) :* NP0)))))))))
                 -> El
                      (((((((A4 y_aEAW) y_aEAX) y_aEAY) y_aEAZ) y_aEB0) y_aEB1) y_aEB2)
               (Rep (Pat0A5 (NA_I (El y_aEB3) :* (NA_I (El y_aEB4) :* (NA_I (El y_aEB5) :* (NA_I (El y_aEB6) :* (NA_I (El y_aEB7) :* (NA_I (El y_aEB8) :* (NA_I (El y_aEB9) :* NP0)))))))))
                 -> El
                      (((((((A5 y_aEB3) y_aEB4) y_aEB5) y_aEB6) y_aEB7) y_aEB8) y_aEB9)
               (Rep (Pat0A6 (NA_I (El y_aEBa) :* (NA_I (El y_aEBb) :* (NA_I (El y_aEBc) :* (NA_I (El y_aEBd) :* (NA_I (El y_aEBe) :* (NA_I (El y_aEBf) :* (NA_I (El y_aEBg) :* NP0)))))))))
                 -> El
                      (((((((A6 y_aEBa) y_aEBb) y_aEBc) y_aEBd) y_aEBe) y_aEBf) y_aEBg)
               (Rep (Pat0A7 (NA_I (El y_aEBh) :* (NA_I (El y_aEBi) :* (NA_I (El y_aEBj) :* (NA_I (El y_aEBk) :* (NA_I (El y_aEBl) :* (NA_I (El y_aEBm) :* (NA_I (El y_aEBn) :* NP0)))))))))
                 -> El
                      (((((((A7 y_aEBh) y_aEBi) y_aEBj) y_aEBk) y_aEBl) y_aEBm) y_aEBn)
               (Rep (Pat0A8 (NA_I (El y_aEBo) :* (NA_I (El y_aEBp) :* (NA_I (El y_aEBq) :* (NA_I (El y_aEBr) :* (NA_I (El y_aEBs) :* (NA_I (El y_aEBt) :* (NA_I (El y_aEBu) :* NP0)))))))))
                 -> El
                      (((((((A8 y_aEBo) y_aEBp) y_aEBq) y_aEBr) y_aEBs) y_aEBt) y_aEBu)
               (Rep (Pat0A9 (NA_I (El y_aEBv) :* (NA_I (El y_aEBw) :* (NA_I (El y_aEBx) :* (NA_I (El y_aEBy) :* (NA_I (El y_aEBz) :* (NA_I (El y_aEBA) :* (NA_I (El y_aEBB) :* NP0)))))))))
                 -> El
                      (((((((A9 y_aEBv) y_aEBw) y_aEBx) y_aEBy) y_aEBz) y_aEBA) y_aEBB)
               (Rep (Pat0AA (NA_I (El y_aEBC) :* (NA_I (El y_aEBD) :* (NA_I (El y_aEBE) :* (NA_I (El y_aEBF) :* (NA_I (El y_aEBG) :* (NA_I (El y_aEBH) :* (NA_I (El y_aEBI) :* NP0)))))))))
                 -> El
                      (((((((AA y_aEBC) y_aEBD) y_aEBE) y_aEBF) y_aEBG) y_aEBH) y_aEBI)
               (Rep (Pat0AB (NA_I (El y_aEBJ) :* (NA_I (El y_aEBK) :* (NA_I (El y_aEBL) :* (NA_I (El y_aEBM) :* (NA_I (El y_aEBN) :* (NA_I (El y_aEBO) :* (NA_I (El y_aEBP) :* NP0)))))))))
                 -> El
                      (((((((AB y_aEBJ) y_aEBK) y_aEBL) y_aEBM) y_aEBN) y_aEBO) y_aEBP)
               (Rep (Pat0AC (NA_I (El y_aEBQ) :* (NA_I (El y_aEBR) :* (NA_I (El y_aEBS) :* (NA_I (El y_aEBT) :* (NA_I (El y_aEBU) :* (NA_I (El y_aEBV) :* (NA_I (El y_aEBW) :* NP0)))))))))
                 -> El
                      (((((((AC y_aEBQ) y_aEBR) y_aEBS) y_aEBT) y_aEBU) y_aEBV) y_aEBW)
               (Rep (Pat0AD (NA_I (El y_aEBX) :* (NA_I (El y_aEBY) :* (NA_I (El y_aEBZ) :* (NA_I (El y_aEC0) :* (NA_I (El y_aEC1) :* (NA_I (El y_aEC2) :* (NA_I (El y_aEC3) :* NP0)))))))))
                 -> El
                      (((((((AD y_aEBX) y_aEBY) y_aEBZ) y_aEC0) y_aEC1) y_aEC2) y_aEC3)
               (Rep (Pat0AE (NA_I (El y_aEC4) :* (NA_I (El y_aEC5) :* (NA_I (El y_aEC6) :* (NA_I (El y_aEC7) :* (NA_I (El y_aEC8) :* (NA_I (El y_aEC9) :* (NA_I (El y_aECa) :* NP0)))))))))
                 -> El
                      (((((((AE y_aEC4) y_aEC5) y_aEC6) y_aEC7) y_aEC8) y_aEC9) y_aECa)
               (Rep (Pat0AF (NA_I (El y_aECb) :* (NA_I (El y_aECc) :* (NA_I (El y_aECd) :* (NA_I (El y_aECe) :* (NA_I (El y_aECf) :* (NA_I (El y_aECg) :* (NA_I (El y_aECh) :* NP0)))))))))
                 -> El
                      (((((((AF y_aECb) y_aECc) y_aECd) y_aECe) y_aECf) y_aECg) y_aECh)
               _ -> error "matchAll"
        IdxB
          -> \case
               (Rep (Pat1B1 (NA_I (El y_aECi) :* (NA_I (El y_aECj) :* (NA_I (El y_aECk) :* (NA_I (El y_aECl) :* (NA_I (El y_aECm) :* (NA_I (El y_aECn) :* (NA_I (El y_aECo) :* NP0)))))))))
                 -> El
                      (((((((B1 y_aECi) y_aECj) y_aECk) y_aECl) y_aECm) y_aECn) y_aECo)
               (Rep (Pat1B2 (NA_I (El y_aECp) :* (NA_I (El y_aECq) :* (NA_I (El y_aECr) :* (NA_I (El y_aECs) :* (NA_I (El y_aECt) :* (NA_I (El y_aECu) :* (NA_I (El y_aECv) :* NP0)))))))))
                 -> El
                      (((((((B2 y_aECp) y_aECq) y_aECr) y_aECs) y_aECt) y_aECu) y_aECv)
               (Rep (Pat1B3 (NA_I (El y_aECw) :* (NA_I (El y_aECx) :* (NA_I (El y_aECy) :* (NA_I (El y_aECz) :* (NA_I (El y_aECA) :* (NA_I (El y_aECB) :* (NA_I (El y_aECC) :* NP0)))))))))
                 -> El
                      (((((((B3 y_aECw) y_aECx) y_aECy) y_aECz) y_aECA) y_aECB) y_aECC)
               (Rep (Pat1B4 (NA_I (El y_aECD) :* (NA_I (El y_aECE) :* (NA_I (El y_aECF) :* (NA_I (El y_aECG) :* (NA_I (El y_aECH) :* (NA_I (El y_aECI) :* (NA_I (El y_aECJ) :* NP0)))))))))
                 -> El
                      (((((((B4 y_aECD) y_aECE) y_aECF) y_aECG) y_aECH) y_aECI) y_aECJ)
               (Rep (Pat1B5 (NA_I (El y_aECK) :* (NA_I (El y_aECL) :* (NA_I (El y_aECM) :* (NA_I (El y_aECN) :* (NA_I (El y_aECO) :* (NA_I (El y_aECP) :* (NA_I (El y_aECQ) :* NP0)))))))))
                 -> El
                      (((((((B5 y_aECK) y_aECL) y_aECM) y_aECN) y_aECO) y_aECP) y_aECQ)
               (Rep (Pat1B6 (NA_I (El y_aECR) :* (NA_I (El y_aECS) :* (NA_I (El y_aECT) :* (NA_I (El y_aECU) :* (NA_I (El y_aECV) :* (NA_I (El y_aECW) :* (NA_I (El y_aECX) :* NP0)))))))))
                 -> El
                      (((((((B6 y_aECR) y_aECS) y_aECT) y_aECU) y_aECV) y_aECW) y_aECX)
               (Rep (Pat1B7 (NA_I (El y_aECY) :* (NA_I (El y_aECZ) :* (NA_I (El y_aED0) :* (NA_I (El y_aED1) :* (NA_I (El y_aED2) :* (NA_I (El y_aED3) :* (NA_I (El y_aED4) :* NP0)))))))))
                 -> El
                      (((((((B7 y_aECY) y_aECZ) y_aED0) y_aED1) y_aED2) y_aED3) y_aED4)
               (Rep (Pat1B8 (NA_I (El y_aED5) :* (NA_I (El y_aED6) :* (NA_I (El y_aED7) :* (NA_I (El y_aED8) :* (NA_I (El y_aED9) :* (NA_I (El y_aEDa) :* (NA_I (El y_aEDb) :* NP0)))))))))
                 -> El
                      (((((((B8 y_aED5) y_aED6) y_aED7) y_aED8) y_aED9) y_aEDa) y_aEDb)
               (Rep (Pat1B9 (NA_I (El y_aEDc) :* (NA_I (El y_aEDd) :* (NA_I (El y_aEDe) :* (NA_I (El y_aEDf) :* (NA_I (El y_aEDg) :* (NA_I (El y_aEDh) :* (NA_I (El y_aEDi) :* NP0)))))))))
                 -> El
                      (((((((B9 y_aEDc) y_aEDd) y_aEDe) y_aEDf) y_aEDg) y_aEDh) y_aEDi)
               (Rep (Pat1BA (NA_I (El y_aEDj) :* (NA_I (El y_aEDk) :* (NA_I (El y_aEDl) :* (NA_I (El y_aEDm) :* (NA_I (El y_aEDn) :* (NA_I (El y_aEDo) :* (NA_I (El y_aEDp) :* NP0)))))))))
                 -> El
                      (((((((BA y_aEDj) y_aEDk) y_aEDl) y_aEDm) y_aEDn) y_aEDo) y_aEDp)
               (Rep (Pat1BB (NA_I (El y_aEDq) :* (NA_I (El y_aEDr) :* (NA_I (El y_aEDs) :* (NA_I (El y_aEDt) :* (NA_I (El y_aEDu) :* (NA_I (El y_aEDv) :* (NA_I (El y_aEDw) :* NP0)))))))))
                 -> El
                      (((((((BB y_aEDq) y_aEDr) y_aEDs) y_aEDt) y_aEDu) y_aEDv) y_aEDw)
               (Rep (Pat1BC (NA_I (El y_aEDx) :* (NA_I (El y_aEDy) :* (NA_I (El y_aEDz) :* (NA_I (El y_aEDA) :* (NA_I (El y_aEDB) :* (NA_I (El y_aEDC) :* (NA_I (El y_aEDD) :* NP0)))))))))
                 -> El
                      (((((((BC y_aEDx) y_aEDy) y_aEDz) y_aEDA) y_aEDB) y_aEDC) y_aEDD)
               (Rep (Pat1BD (NA_I (El y_aEDE) :* (NA_I (El y_aEDF) :* (NA_I (El y_aEDG) :* (NA_I (El y_aEDH) :* (NA_I (El y_aEDI) :* (NA_I (El y_aEDJ) :* (NA_I (El y_aEDK) :* NP0)))))))))
                 -> El
                      (((((((BD y_aEDE) y_aEDF) y_aEDG) y_aEDH) y_aEDI) y_aEDJ) y_aEDK)
               (Rep (Pat1BE (NA_I (El y_aEDL) :* (NA_I (El y_aEDM) :* (NA_I (El y_aEDN) :* (NA_I (El y_aEDO) :* (NA_I (El y_aEDP) :* (NA_I (El y_aEDQ) :* (NA_I (El y_aEDR) :* NP0)))))))))
                 -> El
                      (((((((BE y_aEDL) y_aEDM) y_aEDN) y_aEDO) y_aEDP) y_aEDQ) y_aEDR)
               (Rep (Pat1BF (NA_I (El y_aEDS) :* (NA_I (El y_aEDT) :* (NA_I (El y_aEDU) :* (NA_I (El y_aEDV) :* (NA_I (El y_aEDW) :* (NA_I (El y_aEDX) :* (NA_I (El y_aEDY) :* NP0)))))))))
                 -> El
                      (((((((BF y_aEDS) y_aEDT) y_aEDU) y_aEDV) y_aEDW) y_aEDX) y_aEDY)
               _ -> error "matchAll"
        IdxC
          -> \case
               (Rep (Pat2C1 (NA_I (El y_aEDZ) :* (NA_I (El y_aEE0) :* (NA_I (El y_aEE1) :* (NA_I (El y_aEE2) :* (NA_I (El y_aEE3) :* (NA_I (El y_aEE4) :* (NA_I (El y_aEE5) :* NP0)))))))))
                 -> El
                      (((((((C1 y_aEDZ) y_aEE0) y_aEE1) y_aEE2) y_aEE3) y_aEE4) y_aEE5)
               (Rep (Pat2C2 (NA_I (El y_aEE6) :* (NA_I (El y_aEE7) :* (NA_I (El y_aEE8) :* (NA_I (El y_aEE9) :* (NA_I (El y_aEEa) :* (NA_I (El y_aEEb) :* (NA_I (El y_aEEc) :* NP0)))))))))
                 -> El
                      (((((((C2 y_aEE6) y_aEE7) y_aEE8) y_aEE9) y_aEEa) y_aEEb) y_aEEc)
               (Rep (Pat2C3 (NA_I (El y_aEEd) :* (NA_I (El y_aEEe) :* (NA_I (El y_aEEf) :* (NA_I (El y_aEEg) :* (NA_I (El y_aEEh) :* (NA_I (El y_aEEi) :* (NA_I (El y_aEEj) :* NP0)))))))))
                 -> El
                      (((((((C3 y_aEEd) y_aEEe) y_aEEf) y_aEEg) y_aEEh) y_aEEi) y_aEEj)
               (Rep (Pat2C4 (NA_I (El y_aEEk) :* (NA_I (El y_aEEl) :* (NA_I (El y_aEEm) :* (NA_I (El y_aEEn) :* (NA_I (El y_aEEo) :* (NA_I (El y_aEEp) :* (NA_I (El y_aEEq) :* NP0)))))))))
                 -> El
                      (((((((C4 y_aEEk) y_aEEl) y_aEEm) y_aEEn) y_aEEo) y_aEEp) y_aEEq)
               (Rep (Pat2C5 (NA_I (El y_aEEr) :* (NA_I (El y_aEEs) :* (NA_I (El y_aEEt) :* (NA_I (El y_aEEu) :* (NA_I (El y_aEEv) :* (NA_I (El y_aEEw) :* (NA_I (El y_aEEx) :* NP0)))))))))
                 -> El
                      (((((((C5 y_aEEr) y_aEEs) y_aEEt) y_aEEu) y_aEEv) y_aEEw) y_aEEx)
               (Rep (Pat2C6 (NA_I (El y_aEEy) :* (NA_I (El y_aEEz) :* (NA_I (El y_aEEA) :* (NA_I (El y_aEEB) :* (NA_I (El y_aEEC) :* (NA_I (El y_aEED) :* (NA_I (El y_aEEE) :* NP0)))))))))
                 -> El
                      (((((((C6 y_aEEy) y_aEEz) y_aEEA) y_aEEB) y_aEEC) y_aEED) y_aEEE)
               (Rep (Pat2C7 (NA_I (El y_aEEF) :* (NA_I (El y_aEEG) :* (NA_I (El y_aEEH) :* (NA_I (El y_aEEI) :* (NA_I (El y_aEEJ) :* (NA_I (El y_aEEK) :* (NA_I (El y_aEEL) :* NP0)))))))))
                 -> El
                      (((((((C7 y_aEEF) y_aEEG) y_aEEH) y_aEEI) y_aEEJ) y_aEEK) y_aEEL)
               (Rep (Pat2C8 (NA_I (El y_aEEM) :* (NA_I (El y_aEEN) :* (NA_I (El y_aEEO) :* (NA_I (El y_aEEP) :* (NA_I (El y_aEEQ) :* (NA_I (El y_aEER) :* (NA_I (El y_aEES) :* NP0)))))))))
                 -> El
                      (((((((C8 y_aEEM) y_aEEN) y_aEEO) y_aEEP) y_aEEQ) y_aEER) y_aEES)
               (Rep (Pat2C9 (NA_I (El y_aEET) :* (NA_I (El y_aEEU) :* (NA_I (El y_aEEV) :* (NA_I (El y_aEEW) :* (NA_I (El y_aEEX) :* (NA_I (El y_aEEY) :* (NA_I (El y_aEEZ) :* NP0)))))))))
                 -> El
                      (((((((C9 y_aEET) y_aEEU) y_aEEV) y_aEEW) y_aEEX) y_aEEY) y_aEEZ)
               (Rep (Pat2CA (NA_I (El y_aEF0) :* (NA_I (El y_aEF1) :* (NA_I (El y_aEF2) :* (NA_I (El y_aEF3) :* (NA_I (El y_aEF4) :* (NA_I (El y_aEF5) :* (NA_I (El y_aEF6) :* NP0)))))))))
                 -> El
                      (((((((CA y_aEF0) y_aEF1) y_aEF2) y_aEF3) y_aEF4) y_aEF5) y_aEF6)
               (Rep (Pat2CB (NA_I (El y_aEF7) :* (NA_I (El y_aEF8) :* (NA_I (El y_aEF9) :* (NA_I (El y_aEFa) :* (NA_I (El y_aEFb) :* (NA_I (El y_aEFc) :* (NA_I (El y_aEFd) :* NP0)))))))))
                 -> El
                      (((((((CB y_aEF7) y_aEF8) y_aEF9) y_aEFa) y_aEFb) y_aEFc) y_aEFd)
               (Rep (Pat2CC (NA_I (El y_aEFe) :* (NA_I (El y_aEFf) :* (NA_I (El y_aEFg) :* (NA_I (El y_aEFh) :* (NA_I (El y_aEFi) :* (NA_I (El y_aEFj) :* (NA_I (El y_aEFk) :* NP0)))))))))
                 -> El
                      (((((((CC y_aEFe) y_aEFf) y_aEFg) y_aEFh) y_aEFi) y_aEFj) y_aEFk)
               (Rep (Pat2CD (NA_I (El y_aEFl) :* (NA_I (El y_aEFm) :* (NA_I (El y_aEFn) :* (NA_I (El y_aEFo) :* (NA_I (El y_aEFp) :* (NA_I (El y_aEFq) :* (NA_I (El y_aEFr) :* NP0)))))))))
                 -> El
                      (((((((CD y_aEFl) y_aEFm) y_aEFn) y_aEFo) y_aEFp) y_aEFq) y_aEFr)
               (Rep (Pat2CE (NA_I (El y_aEFs) :* (NA_I (El y_aEFt) :* (NA_I (El y_aEFu) :* (NA_I (El y_aEFv) :* (NA_I (El y_aEFw) :* (NA_I (El y_aEFx) :* (NA_I (El y_aEFy) :* NP0)))))))))
                 -> El
                      (((((((CE y_aEFs) y_aEFt) y_aEFu) y_aEFv) y_aEFw) y_aEFx) y_aEFy)
               (Rep (Pat2CF (NA_I (El y_aEFz) :* (NA_I (El y_aEFA) :* (NA_I (El y_aEFB) :* (NA_I (El y_aEFC) :* (NA_I (El y_aEFD) :* (NA_I (El y_aEFE) :* (NA_I (El y_aEFF) :* NP0)))))))))
                 -> El
                      (((((((CF y_aEFz) y_aEFA) y_aEFB) y_aEFC) y_aEFD) y_aEFE) y_aEFF)
               _ -> error "matchAll"
        IdxD
          -> \case
               (Rep (Pat3D1 (NA_I (El y_aEFG) :* (NA_I (El y_aEFH) :* (NA_I (El y_aEFI) :* (NA_I (El y_aEFJ) :* (NA_I (El y_aEFK) :* (NA_I (El y_aEFL) :* (NA_I (El y_aEFM) :* NP0)))))))))
                 -> El
                      (((((((D1 y_aEFG) y_aEFH) y_aEFI) y_aEFJ) y_aEFK) y_aEFL) y_aEFM)
               (Rep (Pat3D2 (NA_I (El y_aEFN) :* (NA_I (El y_aEFO) :* (NA_I (El y_aEFP) :* (NA_I (El y_aEFQ) :* (NA_I (El y_aEFR) :* (NA_I (El y_aEFS) :* (NA_I (El y_aEFT) :* NP0)))))))))
                 -> El
                      (((((((D2 y_aEFN) y_aEFO) y_aEFP) y_aEFQ) y_aEFR) y_aEFS) y_aEFT)
               (Rep (Pat3D3 (NA_I (El y_aEFU) :* (NA_I (El y_aEFV) :* (NA_I (El y_aEFW) :* (NA_I (El y_aEFX) :* (NA_I (El y_aEFY) :* (NA_I (El y_aEFZ) :* (NA_I (El y_aEG0) :* NP0)))))))))
                 -> El
                      (((((((D3 y_aEFU) y_aEFV) y_aEFW) y_aEFX) y_aEFY) y_aEFZ) y_aEG0)
               (Rep (Pat3D4 (NA_I (El y_aEG1) :* (NA_I (El y_aEG2) :* (NA_I (El y_aEG3) :* (NA_I (El y_aEG4) :* (NA_I (El y_aEG5) :* (NA_I (El y_aEG6) :* (NA_I (El y_aEG7) :* NP0)))))))))
                 -> El
                      (((((((D4 y_aEG1) y_aEG2) y_aEG3) y_aEG4) y_aEG5) y_aEG6) y_aEG7)
               (Rep (Pat3D5 (NA_I (El y_aEG8) :* (NA_I (El y_aEG9) :* (NA_I (El y_aEGa) :* (NA_I (El y_aEGb) :* (NA_I (El y_aEGc) :* (NA_I (El y_aEGd) :* (NA_I (El y_aEGe) :* NP0)))))))))
                 -> El
                      (((((((D5 y_aEG8) y_aEG9) y_aEGa) y_aEGb) y_aEGc) y_aEGd) y_aEGe)
               (Rep (Pat3D6 (NA_I (El y_aEGf) :* (NA_I (El y_aEGg) :* (NA_I (El y_aEGh) :* (NA_I (El y_aEGi) :* (NA_I (El y_aEGj) :* (NA_I (El y_aEGk) :* (NA_I (El y_aEGl) :* NP0)))))))))
                 -> El
                      (((((((D6 y_aEGf) y_aEGg) y_aEGh) y_aEGi) y_aEGj) y_aEGk) y_aEGl)
               (Rep (Pat3D7 (NA_I (El y_aEGm) :* (NA_I (El y_aEGn) :* (NA_I (El y_aEGo) :* (NA_I (El y_aEGp) :* (NA_I (El y_aEGq) :* (NA_I (El y_aEGr) :* (NA_I (El y_aEGs) :* NP0)))))))))
                 -> El
                      (((((((D7 y_aEGm) y_aEGn) y_aEGo) y_aEGp) y_aEGq) y_aEGr) y_aEGs)
               (Rep (Pat3D8 (NA_I (El y_aEGt) :* (NA_I (El y_aEGu) :* (NA_I (El y_aEGv) :* (NA_I (El y_aEGw) :* (NA_I (El y_aEGx) :* (NA_I (El y_aEGy) :* (NA_I (El y_aEGz) :* NP0)))))))))
                 -> El
                      (((((((D8 y_aEGt) y_aEGu) y_aEGv) y_aEGw) y_aEGx) y_aEGy) y_aEGz)
               (Rep (Pat3D9 (NA_I (El y_aEGA) :* (NA_I (El y_aEGB) :* (NA_I (El y_aEGC) :* (NA_I (El y_aEGD) :* (NA_I (El y_aEGE) :* (NA_I (El y_aEGF) :* (NA_I (El y_aEGG) :* NP0)))))))))
                 -> El
                      (((((((D9 y_aEGA) y_aEGB) y_aEGC) y_aEGD) y_aEGE) y_aEGF) y_aEGG)
               (Rep (Pat3DA (NA_I (El y_aEGH) :* (NA_I (El y_aEGI) :* (NA_I (El y_aEGJ) :* (NA_I (El y_aEGK) :* (NA_I (El y_aEGL) :* (NA_I (El y_aEGM) :* (NA_I (El y_aEGN) :* NP0)))))))))
                 -> El
                      (((((((DA y_aEGH) y_aEGI) y_aEGJ) y_aEGK) y_aEGL) y_aEGM) y_aEGN)
               (Rep (Pat3DB (NA_I (El y_aEGO) :* (NA_I (El y_aEGP) :* (NA_I (El y_aEGQ) :* (NA_I (El y_aEGR) :* (NA_I (El y_aEGS) :* (NA_I (El y_aEGT) :* (NA_I (El y_aEGU) :* NP0)))))))))
                 -> El
                      (((((((DB y_aEGO) y_aEGP) y_aEGQ) y_aEGR) y_aEGS) y_aEGT) y_aEGU)
               (Rep (Pat3DC (NA_I (El y_aEGV) :* (NA_I (El y_aEGW) :* (NA_I (El y_aEGX) :* (NA_I (El y_aEGY) :* (NA_I (El y_aEGZ) :* (NA_I (El y_aEH0) :* (NA_I (El y_aEH1) :* NP0)))))))))
                 -> El
                      (((((((DC y_aEGV) y_aEGW) y_aEGX) y_aEGY) y_aEGZ) y_aEH0) y_aEH1)
               (Rep (Pat3DD (NA_I (El y_aEH2) :* (NA_I (El y_aEH3) :* (NA_I (El y_aEH4) :* (NA_I (El y_aEH5) :* (NA_I (El y_aEH6) :* (NA_I (El y_aEH7) :* (NA_I (El y_aEH8) :* NP0)))))))))
                 -> El
                      (((((((DD y_aEH2) y_aEH3) y_aEH4) y_aEH5) y_aEH6) y_aEH7) y_aEH8)
               (Rep (Pat3DE (NA_I (El y_aEH9) :* (NA_I (El y_aEHa) :* (NA_I (El y_aEHb) :* (NA_I (El y_aEHc) :* (NA_I (El y_aEHd) :* (NA_I (El y_aEHe) :* (NA_I (El y_aEHf) :* NP0)))))))))
                 -> El
                      (((((((DE y_aEH9) y_aEHa) y_aEHb) y_aEHc) y_aEHd) y_aEHe) y_aEHf)
               (Rep (Pat3DF (NA_I (El y_aEHg) :* (NA_I (El y_aEHh) :* (NA_I (El y_aEHi) :* (NA_I (El y_aEHj) :* (NA_I (El y_aEHk) :* (NA_I (El y_aEHl) :* (NA_I (El y_aEHm) :* NP0)))))))))
                 -> El
                      (((((((DF y_aEHg) y_aEHh) y_aEHi) y_aEHj) y_aEHk) y_aEHl) y_aEHm)
               _ -> error "matchAll"
        IdxE
          -> \case
               (Rep (Pat4E1 (NA_I (El y_aEHn) :* (NA_I (El y_aEHo) :* (NA_I (El y_aEHp) :* (NA_I (El y_aEHq) :* (NA_I (El y_aEHr) :* (NA_I (El y_aEHs) :* (NA_I (El y_aEHt) :* NP0)))))))))
                 -> El
                      (((((((E1 y_aEHn) y_aEHo) y_aEHp) y_aEHq) y_aEHr) y_aEHs) y_aEHt)
               (Rep (Pat4E2 (NA_I (El y_aEHu) :* (NA_I (El y_aEHv) :* (NA_I (El y_aEHw) :* (NA_I (El y_aEHx) :* (NA_I (El y_aEHy) :* (NA_I (El y_aEHz) :* (NA_I (El y_aEHA) :* NP0)))))))))
                 -> El
                      (((((((E2 y_aEHu) y_aEHv) y_aEHw) y_aEHx) y_aEHy) y_aEHz) y_aEHA)
               (Rep (Pat4E3 (NA_I (El y_aEHB) :* (NA_I (El y_aEHC) :* (NA_I (El y_aEHD) :* (NA_I (El y_aEHE) :* (NA_I (El y_aEHF) :* (NA_I (El y_aEHG) :* (NA_I (El y_aEHH) :* NP0)))))))))
                 -> El
                      (((((((E3 y_aEHB) y_aEHC) y_aEHD) y_aEHE) y_aEHF) y_aEHG) y_aEHH)
               (Rep (Pat4E4 (NA_I (El y_aEHI) :* (NA_I (El y_aEHJ) :* (NA_I (El y_aEHK) :* (NA_I (El y_aEHL) :* (NA_I (El y_aEHM) :* (NA_I (El y_aEHN) :* (NA_I (El y_aEHO) :* NP0)))))))))
                 -> El
                      (((((((E4 y_aEHI) y_aEHJ) y_aEHK) y_aEHL) y_aEHM) y_aEHN) y_aEHO)
               (Rep (Pat4E5 (NA_I (El y_aEHP) :* (NA_I (El y_aEHQ) :* (NA_I (El y_aEHR) :* (NA_I (El y_aEHS) :* (NA_I (El y_aEHT) :* (NA_I (El y_aEHU) :* (NA_I (El y_aEHV) :* NP0)))))))))
                 -> El
                      (((((((E5 y_aEHP) y_aEHQ) y_aEHR) y_aEHS) y_aEHT) y_aEHU) y_aEHV)
               (Rep (Pat4E6 (NA_I (El y_aEHW) :* (NA_I (El y_aEHX) :* (NA_I (El y_aEHY) :* (NA_I (El y_aEHZ) :* (NA_I (El y_aEI0) :* (NA_I (El y_aEI1) :* (NA_I (El y_aEI2) :* NP0)))))))))
                 -> El
                      (((((((E6 y_aEHW) y_aEHX) y_aEHY) y_aEHZ) y_aEI0) y_aEI1) y_aEI2)
               (Rep (Pat4E7 (NA_I (El y_aEI3) :* (NA_I (El y_aEI4) :* (NA_I (El y_aEI5) :* (NA_I (El y_aEI6) :* (NA_I (El y_aEI7) :* (NA_I (El y_aEI8) :* (NA_I (El y_aEI9) :* NP0)))))))))
                 -> El
                      (((((((E7 y_aEI3) y_aEI4) y_aEI5) y_aEI6) y_aEI7) y_aEI8) y_aEI9)
               (Rep (Pat4E8 (NA_I (El y_aEIa) :* (NA_I (El y_aEIb) :* (NA_I (El y_aEIc) :* (NA_I (El y_aEId) :* (NA_I (El y_aEIe) :* (NA_I (El y_aEIf) :* (NA_I (El y_aEIg) :* NP0)))))))))
                 -> El
                      (((((((E8 y_aEIa) y_aEIb) y_aEIc) y_aEId) y_aEIe) y_aEIf) y_aEIg)
               (Rep (Pat4E9 (NA_I (El y_aEIh) :* (NA_I (El y_aEIi) :* (NA_I (El y_aEIj) :* (NA_I (El y_aEIk) :* (NA_I (El y_aEIl) :* (NA_I (El y_aEIm) :* (NA_I (El y_aEIn) :* NP0)))))))))
                 -> El
                      (((((((E9 y_aEIh) y_aEIi) y_aEIj) y_aEIk) y_aEIl) y_aEIm) y_aEIn)
               (Rep (Pat4EA (NA_I (El y_aEIo) :* (NA_I (El y_aEIp) :* (NA_I (El y_aEIq) :* (NA_I (El y_aEIr) :* (NA_I (El y_aEIs) :* (NA_I (El y_aEIt) :* (NA_I (El y_aEIu) :* NP0)))))))))
                 -> El
                      (((((((EA y_aEIo) y_aEIp) y_aEIq) y_aEIr) y_aEIs) y_aEIt) y_aEIu)
               (Rep (Pat4EB (NA_I (El y_aEIv) :* (NA_I (El y_aEIw) :* (NA_I (El y_aEIx) :* (NA_I (El y_aEIy) :* (NA_I (El y_aEIz) :* (NA_I (El y_aEIA) :* (NA_I (El y_aEIB) :* NP0)))))))))
                 -> El
                      (((((((EB y_aEIv) y_aEIw) y_aEIx) y_aEIy) y_aEIz) y_aEIA) y_aEIB)
               (Rep (Pat4EC (NA_I (El y_aEIC) :* (NA_I (El y_aEID) :* (NA_I (El y_aEIE) :* (NA_I (El y_aEIF) :* (NA_I (El y_aEIG) :* (NA_I (El y_aEIH) :* (NA_I (El y_aEII) :* NP0)))))))))
                 -> El
                      (((((((EC y_aEIC) y_aEID) y_aEIE) y_aEIF) y_aEIG) y_aEIH) y_aEII)
               (Rep (Pat4ED (NA_I (El y_aEIJ) :* (NA_I (El y_aEIK) :* (NA_I (El y_aEIL) :* (NA_I (El y_aEIM) :* (NA_I (El y_aEIN) :* (NA_I (El y_aEIO) :* (NA_I (El y_aEIP) :* NP0)))))))))
                 -> El
                      (((((((ED y_aEIJ) y_aEIK) y_aEIL) y_aEIM) y_aEIN) y_aEIO) y_aEIP)
               (Rep (Pat4EE (NA_I (El y_aEIQ) :* (NA_I (El y_aEIR) :* (NA_I (El y_aEIS) :* (NA_I (El y_aEIT) :* (NA_I (El y_aEIU) :* (NA_I (El y_aEIV) :* (NA_I (El y_aEIW) :* NP0)))))))))
                 -> El
                      (((((((EE y_aEIQ) y_aEIR) y_aEIS) y_aEIT) y_aEIU) y_aEIV) y_aEIW)
               (Rep (Pat4EF (NA_I (El y_aEIX) :* (NA_I (El y_aEIY) :* (NA_I (El y_aEIZ) :* (NA_I (El y_aEJ0) :* (NA_I (El y_aEJ1) :* (NA_I (El y_aEJ2) :* (NA_I (El y_aEJ3) :* NP0)))))))))
                 -> El
                      (((((((EF y_aEIX) y_aEIY) y_aEIZ) y_aEJ0) y_aEJ1) y_aEJ2) y_aEJ3)
               _ -> error "matchAll"
        IdxF -> \case _ -> error "matchAll"
        IdxG -> \case _ -> error "matchAll"
        _ -> error "matchAll"
