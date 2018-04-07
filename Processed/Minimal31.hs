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
{-# LANGUAGE EmptyCase              #-}
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
pattern Pat4EF d_aEAQ = T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEAQ))))))))))))))
pattern Pat4EE d_aEAP = T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEAP)))))))))))))
pattern Pat4ED d_aEAO = T (T (T (T (T (T (T (T (T (T (T (T (H d_aEAO))))))))))))
pattern Pat4EC d_aEAN = T (T (T (T (T (T (T (T (T (T (T (H d_aEAN)))))))))))
pattern Pat4EB d_aEAM = T (T (T (T (T (T (T (T (T (T (H d_aEAM))))))))))
pattern Pat4EA d_aEAL = T (T (T (T (T (T (T (T (T (H d_aEAL)))))))))
pattern Pat4E9 d_aEAK = T (T (T (T (T (T (T (T (H d_aEAK))))))))
pattern Pat4E8 d_aEAJ = T (T (T (T (T (T (T (H d_aEAJ)))))))
pattern Pat4E7 d_aEAI = T (T (T (T (T (T (H d_aEAI))))))
pattern Pat4E6 d_aEAH = T (T (T (T (T (H d_aEAH)))))
pattern Pat4E5 d_aEAG = T (T (T (T (H d_aEAG))))
pattern Pat4E4 d_aEAF = T (T (T (H d_aEAF)))
pattern Pat4E3 d_aEAE = T (T (H d_aEAE))
pattern Pat4E2 d_aEAD = T (H d_aEAD)
pattern Pat4E1 d_aEAC = H d_aEAC
pattern Pat3DF d_aEAB = T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEAB))))))))))))))
pattern Pat3DE d_aEAA = T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEAA)))))))))))))
pattern Pat3DD d_aEAz = T (T (T (T (T (T (T (T (T (T (T (T (H d_aEAz))))))))))))
pattern Pat3DC d_aEAy = T (T (T (T (T (T (T (T (T (T (T (H d_aEAy)))))))))))
pattern Pat3DB d_aEAx = T (T (T (T (T (T (T (T (T (T (H d_aEAx))))))))))
pattern Pat3DA d_aEAw = T (T (T (T (T (T (T (T (T (H d_aEAw)))))))))
pattern Pat3D9 d_aEAv = T (T (T (T (T (T (T (T (H d_aEAv))))))))
pattern Pat3D8 d_aEAu = T (T (T (T (T (T (T (H d_aEAu)))))))
pattern Pat3D7 d_aEAt = T (T (T (T (T (T (H d_aEAt))))))
pattern Pat3D6 d_aEAs = T (T (T (T (T (H d_aEAs)))))
pattern Pat3D5 d_aEAr = T (T (T (T (H d_aEAr))))
pattern Pat3D4 d_aEAq = T (T (T (H d_aEAq)))
pattern Pat3D3 d_aEAp = T (T (H d_aEAp))
pattern Pat3D2 d_aEAo = T (H d_aEAo)
pattern Pat3D1 d_aEAn = H d_aEAn
pattern Pat2CF d_aEAm = T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEAm))))))))))))))
pattern Pat2CE d_aEAl = T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEAl)))))))))))))
pattern Pat2CD d_aEAk = T (T (T (T (T (T (T (T (T (T (T (T (H d_aEAk))))))))))))
pattern Pat2CC d_aEAj = T (T (T (T (T (T (T (T (T (T (T (H d_aEAj)))))))))))
pattern Pat2CB d_aEAi = T (T (T (T (T (T (T (T (T (T (H d_aEAi))))))))))
pattern Pat2CA d_aEAh = T (T (T (T (T (T (T (T (T (H d_aEAh)))))))))
pattern Pat2C9 d_aEAg = T (T (T (T (T (T (T (T (H d_aEAg))))))))
pattern Pat2C8 d_aEAf = T (T (T (T (T (T (T (H d_aEAf)))))))
pattern Pat2C7 d_aEAe = T (T (T (T (T (T (H d_aEAe))))))
pattern Pat2C6 d_aEAd = T (T (T (T (T (H d_aEAd)))))
pattern Pat2C5 d_aEAc = T (T (T (T (H d_aEAc))))
pattern Pat2C4 d_aEAb = T (T (T (H d_aEAb)))
pattern Pat2C3 d_aEAa = T (T (H d_aEAa))
pattern Pat2C2 d_aEA9 = T (H d_aEA9)
pattern Pat2C1 d_aEA8 = H d_aEA8
pattern Pat1BF d_aEA7 = T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEA7))))))))))))))
pattern Pat1BE d_aEA6 = T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEA6)))))))))))))
pattern Pat1BD d_aEA5 = T (T (T (T (T (T (T (T (T (T (T (T (H d_aEA5))))))))))))
pattern Pat1BC d_aEA4 = T (T (T (T (T (T (T (T (T (T (T (H d_aEA4)))))))))))
pattern Pat1BB d_aEA3 = T (T (T (T (T (T (T (T (T (T (H d_aEA3))))))))))
pattern Pat1BA d_aEA2 = T (T (T (T (T (T (T (T (T (H d_aEA2)))))))))
pattern Pat1B9 d_aEA1 = T (T (T (T (T (T (T (T (H d_aEA1))))))))
pattern Pat1B8 d_aEA0 = T (T (T (T (T (T (T (H d_aEA0)))))))
pattern Pat1B7 d_aEzZ = T (T (T (T (T (T (H d_aEzZ))))))
pattern Pat1B6 d_aEzY = T (T (T (T (T (H d_aEzY)))))
pattern Pat1B5 d_aEzX = T (T (T (T (H d_aEzX))))
pattern Pat1B4 d_aEzW = T (T (T (H d_aEzW)))
pattern Pat1B3 d_aEzV = T (T (H d_aEzV))
pattern Pat1B2 d_aEzU = T (H d_aEzU)
pattern Pat1B1 d_aEzT = H d_aEzT
pattern Pat0AF d_aEzS = T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEzS))))))))))))))
pattern Pat0AE d_aEzR = T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aEzR)))))))))))))
pattern Pat0AD d_aEzQ = T (T (T (T (T (T (T (T (T (T (T (T (H d_aEzQ))))))))))))
pattern Pat0AC d_aEzP = T (T (T (T (T (T (T (T (T (T (T (H d_aEzP)))))))))))
pattern Pat0AB d_aEzO = T (T (T (T (T (T (T (T (T (T (H d_aEzO))))))))))
pattern Pat0AA d_aEzN = T (T (T (T (T (T (T (T (T (H d_aEzN)))))))))
pattern Pat0A9 d_aEzM = T (T (T (T (T (T (T (T (H d_aEzM))))))))
pattern Pat0A8 d_aEzL = T (T (T (T (T (T (T (H d_aEzL)))))))
pattern Pat0A7 d_aEzK = T (T (T (T (T (T (H d_aEzK))))))
pattern Pat0A6 d_aEzJ = T (T (T (T (T (H d_aEzJ)))))
pattern Pat0A5 d_aEzI = T (T (T (T (H d_aEzI))))
pattern Pat0A4 d_aEzH = T (T (T (H d_aEzH)))
pattern Pat0A3 d_aEzG = T (T (H d_aEzG))
pattern Pat0A2 d_aEzF = T (H d_aEzF)
pattern Pat0A1 d_aEzE = H d_aEzE
instance Family Singl FamA CodesA where
  sfrom'
    = \case
        IdxA
          -> \case
               (El (A1 x_aEAR x_aEAS x_aEAT x_aEAU x_aEAV x_aEAW x_aEAX))
                 -> Rep
                      (Pat0A1
                         ((NA_I (El x_aEAR))
                            :*
                              ((NA_I (El x_aEAS))
                                 :*
                                   ((NA_I (El x_aEAT))
                                      :*
                                        ((NA_I (El x_aEAU))
                                           :*
                                             ((NA_I (El x_aEAV))
                                                :*
                                                  ((NA_I (El x_aEAW))
                                                     :* ((NA_I (El x_aEAX)) :* NP0))))))))
               (El (A2 x_aEAY x_aEAZ x_aEB0 x_aEB1 x_aEB2 x_aEB3 x_aEB4))
                 -> Rep
                      (Pat0A2
                         ((NA_I (El x_aEAY))
                            :*
                              ((NA_I (El x_aEAZ))
                                 :*
                                   ((NA_I (El x_aEB0))
                                      :*
                                        ((NA_I (El x_aEB1))
                                           :*
                                             ((NA_I (El x_aEB2))
                                                :*
                                                  ((NA_I (El x_aEB3))
                                                     :* ((NA_I (El x_aEB4)) :* NP0))))))))
               (El (A3 x_aEB5 x_aEB6 x_aEB7 x_aEB8 x_aEB9 x_aEBa x_aEBb))
                 -> Rep
                      (Pat0A3
                         ((NA_I (El x_aEB5))
                            :*
                              ((NA_I (El x_aEB6))
                                 :*
                                   ((NA_I (El x_aEB7))
                                      :*
                                        ((NA_I (El x_aEB8))
                                           :*
                                             ((NA_I (El x_aEB9))
                                                :*
                                                  ((NA_I (El x_aEBa))
                                                     :* ((NA_I (El x_aEBb)) :* NP0))))))))
               (El (A4 x_aEBc x_aEBd x_aEBe x_aEBf x_aEBg x_aEBh x_aEBi))
                 -> Rep
                      (Pat0A4
                         ((NA_I (El x_aEBc))
                            :*
                              ((NA_I (El x_aEBd))
                                 :*
                                   ((NA_I (El x_aEBe))
                                      :*
                                        ((NA_I (El x_aEBf))
                                           :*
                                             ((NA_I (El x_aEBg))
                                                :*
                                                  ((NA_I (El x_aEBh))
                                                     :* ((NA_I (El x_aEBi)) :* NP0))))))))
               (El (A5 x_aEBj x_aEBk x_aEBl x_aEBm x_aEBn x_aEBo x_aEBp))
                 -> Rep
                      (Pat0A5
                         ((NA_I (El x_aEBj))
                            :*
                              ((NA_I (El x_aEBk))
                                 :*
                                   ((NA_I (El x_aEBl))
                                      :*
                                        ((NA_I (El x_aEBm))
                                           :*
                                             ((NA_I (El x_aEBn))
                                                :*
                                                  ((NA_I (El x_aEBo))
                                                     :* ((NA_I (El x_aEBp)) :* NP0))))))))
               (El (A6 x_aEBq x_aEBr x_aEBs x_aEBt x_aEBu x_aEBv x_aEBw))
                 -> Rep
                      (Pat0A6
                         ((NA_I (El x_aEBq))
                            :*
                              ((NA_I (El x_aEBr))
                                 :*
                                   ((NA_I (El x_aEBs))
                                      :*
                                        ((NA_I (El x_aEBt))
                                           :*
                                             ((NA_I (El x_aEBu))
                                                :*
                                                  ((NA_I (El x_aEBv))
                                                     :* ((NA_I (El x_aEBw)) :* NP0))))))))
               (El (A7 x_aEBx x_aEBy x_aEBz x_aEBA x_aEBB x_aEBC x_aEBD))
                 -> Rep
                      (Pat0A7
                         ((NA_I (El x_aEBx))
                            :*
                              ((NA_I (El x_aEBy))
                                 :*
                                   ((NA_I (El x_aEBz))
                                      :*
                                        ((NA_I (El x_aEBA))
                                           :*
                                             ((NA_I (El x_aEBB))
                                                :*
                                                  ((NA_I (El x_aEBC))
                                                     :* ((NA_I (El x_aEBD)) :* NP0))))))))
               (El (A8 x_aEBE x_aEBF x_aEBG x_aEBH x_aEBI x_aEBJ x_aEBK))
                 -> Rep
                      (Pat0A8
                         ((NA_I (El x_aEBE))
                            :*
                              ((NA_I (El x_aEBF))
                                 :*
                                   ((NA_I (El x_aEBG))
                                      :*
                                        ((NA_I (El x_aEBH))
                                           :*
                                             ((NA_I (El x_aEBI))
                                                :*
                                                  ((NA_I (El x_aEBJ))
                                                     :* ((NA_I (El x_aEBK)) :* NP0))))))))
               (El (A9 x_aEBL x_aEBM x_aEBN x_aEBO x_aEBP x_aEBQ x_aEBR))
                 -> Rep
                      (Pat0A9
                         ((NA_I (El x_aEBL))
                            :*
                              ((NA_I (El x_aEBM))
                                 :*
                                   ((NA_I (El x_aEBN))
                                      :*
                                        ((NA_I (El x_aEBO))
                                           :*
                                             ((NA_I (El x_aEBP))
                                                :*
                                                  ((NA_I (El x_aEBQ))
                                                     :* ((NA_I (El x_aEBR)) :* NP0))))))))
               (El (AA x_aEBS x_aEBT x_aEBU x_aEBV x_aEBW x_aEBX x_aEBY))
                 -> Rep
                      (Pat0AA
                         ((NA_I (El x_aEBS))
                            :*
                              ((NA_I (El x_aEBT))
                                 :*
                                   ((NA_I (El x_aEBU))
                                      :*
                                        ((NA_I (El x_aEBV))
                                           :*
                                             ((NA_I (El x_aEBW))
                                                :*
                                                  ((NA_I (El x_aEBX))
                                                     :* ((NA_I (El x_aEBY)) :* NP0))))))))
               (El (AB x_aEBZ x_aEC0 x_aEC1 x_aEC2 x_aEC3 x_aEC4 x_aEC5))
                 -> Rep
                      (Pat0AB
                         ((NA_I (El x_aEBZ))
                            :*
                              ((NA_I (El x_aEC0))
                                 :*
                                   ((NA_I (El x_aEC1))
                                      :*
                                        ((NA_I (El x_aEC2))
                                           :*
                                             ((NA_I (El x_aEC3))
                                                :*
                                                  ((NA_I (El x_aEC4))
                                                     :* ((NA_I (El x_aEC5)) :* NP0))))))))
               (El (AC x_aEC6 x_aEC7 x_aEC8 x_aEC9 x_aECa x_aECb x_aECc))
                 -> Rep
                      (Pat0AC
                         ((NA_I (El x_aEC6))
                            :*
                              ((NA_I (El x_aEC7))
                                 :*
                                   ((NA_I (El x_aEC8))
                                      :*
                                        ((NA_I (El x_aEC9))
                                           :*
                                             ((NA_I (El x_aECa))
                                                :*
                                                  ((NA_I (El x_aECb))
                                                     :* ((NA_I (El x_aECc)) :* NP0))))))))
               (El (AD x_aECd x_aECe x_aECf x_aECg x_aECh x_aECi x_aECj))
                 -> Rep
                      (Pat0AD
                         ((NA_I (El x_aECd))
                            :*
                              ((NA_I (El x_aECe))
                                 :*
                                   ((NA_I (El x_aECf))
                                      :*
                                        ((NA_I (El x_aECg))
                                           :*
                                             ((NA_I (El x_aECh))
                                                :*
                                                  ((NA_I (El x_aECi))
                                                     :* ((NA_I (El x_aECj)) :* NP0))))))))
               (El (AE x_aECk x_aECl x_aECm x_aECn x_aECo x_aECp x_aECq))
                 -> Rep
                      (Pat0AE
                         ((NA_I (El x_aECk))
                            :*
                              ((NA_I (El x_aECl))
                                 :*
                                   ((NA_I (El x_aECm))
                                      :*
                                        ((NA_I (El x_aECn))
                                           :*
                                             ((NA_I (El x_aECo))
                                                :*
                                                  ((NA_I (El x_aECp))
                                                     :* ((NA_I (El x_aECq)) :* NP0))))))))
               (El (AF x_aECr x_aECs x_aECt x_aECu x_aECv x_aECw x_aECx))
                 -> Rep
                      (Pat0AF
                         ((NA_I (El x_aECr))
                            :*
                              ((NA_I (El x_aECs))
                                 :*
                                   ((NA_I (El x_aECt))
                                      :*
                                        ((NA_I (El x_aECu))
                                           :*
                                             ((NA_I (El x_aECv))
                                                :*
                                                  ((NA_I (El x_aECw))
                                                     :* ((NA_I (El x_aECx)) :* NP0))))))))
        IdxB
          -> \case
               (El (B1 x_aECy x_aECz x_aECA x_aECB x_aECC x_aECD x_aECE))
                 -> Rep
                      (Pat1B1
                         ((NA_I (El x_aECy))
                            :*
                              ((NA_I (El x_aECz))
                                 :*
                                   ((NA_I (El x_aECA))
                                      :*
                                        ((NA_I (El x_aECB))
                                           :*
                                             ((NA_I (El x_aECC))
                                                :*
                                                  ((NA_I (El x_aECD))
                                                     :* ((NA_I (El x_aECE)) :* NP0))))))))
               (El (B2 x_aECF x_aECG x_aECH x_aECI x_aECJ x_aECK x_aECL))
                 -> Rep
                      (Pat1B2
                         ((NA_I (El x_aECF))
                            :*
                              ((NA_I (El x_aECG))
                                 :*
                                   ((NA_I (El x_aECH))
                                      :*
                                        ((NA_I (El x_aECI))
                                           :*
                                             ((NA_I (El x_aECJ))
                                                :*
                                                  ((NA_I (El x_aECK))
                                                     :* ((NA_I (El x_aECL)) :* NP0))))))))
               (El (B3 x_aECM x_aECN x_aECO x_aECP x_aECQ x_aECR x_aECS))
                 -> Rep
                      (Pat1B3
                         ((NA_I (El x_aECM))
                            :*
                              ((NA_I (El x_aECN))
                                 :*
                                   ((NA_I (El x_aECO))
                                      :*
                                        ((NA_I (El x_aECP))
                                           :*
                                             ((NA_I (El x_aECQ))
                                                :*
                                                  ((NA_I (El x_aECR))
                                                     :* ((NA_I (El x_aECS)) :* NP0))))))))
               (El (B4 x_aECT x_aECU x_aECV x_aECW x_aECX x_aECY x_aECZ))
                 -> Rep
                      (Pat1B4
                         ((NA_I (El x_aECT))
                            :*
                              ((NA_I (El x_aECU))
                                 :*
                                   ((NA_I (El x_aECV))
                                      :*
                                        ((NA_I (El x_aECW))
                                           :*
                                             ((NA_I (El x_aECX))
                                                :*
                                                  ((NA_I (El x_aECY))
                                                     :* ((NA_I (El x_aECZ)) :* NP0))))))))
               (El (B5 x_aED0 x_aED1 x_aED2 x_aED3 x_aED4 x_aED5 x_aED6))
                 -> Rep
                      (Pat1B5
                         ((NA_I (El x_aED0))
                            :*
                              ((NA_I (El x_aED1))
                                 :*
                                   ((NA_I (El x_aED2))
                                      :*
                                        ((NA_I (El x_aED3))
                                           :*
                                             ((NA_I (El x_aED4))
                                                :*
                                                  ((NA_I (El x_aED5))
                                                     :* ((NA_I (El x_aED6)) :* NP0))))))))
               (El (B6 x_aED7 x_aED8 x_aED9 x_aEDa x_aEDb x_aEDc x_aEDd))
                 -> Rep
                      (Pat1B6
                         ((NA_I (El x_aED7))
                            :*
                              ((NA_I (El x_aED8))
                                 :*
                                   ((NA_I (El x_aED9))
                                      :*
                                        ((NA_I (El x_aEDa))
                                           :*
                                             ((NA_I (El x_aEDb))
                                                :*
                                                  ((NA_I (El x_aEDc))
                                                     :* ((NA_I (El x_aEDd)) :* NP0))))))))
               (El (B7 x_aEDe x_aEDf x_aEDg x_aEDh x_aEDi x_aEDj x_aEDk))
                 -> Rep
                      (Pat1B7
                         ((NA_I (El x_aEDe))
                            :*
                              ((NA_I (El x_aEDf))
                                 :*
                                   ((NA_I (El x_aEDg))
                                      :*
                                        ((NA_I (El x_aEDh))
                                           :*
                                             ((NA_I (El x_aEDi))
                                                :*
                                                  ((NA_I (El x_aEDj))
                                                     :* ((NA_I (El x_aEDk)) :* NP0))))))))
               (El (B8 x_aEDl x_aEDm x_aEDn x_aEDo x_aEDp x_aEDq x_aEDr))
                 -> Rep
                      (Pat1B8
                         ((NA_I (El x_aEDl))
                            :*
                              ((NA_I (El x_aEDm))
                                 :*
                                   ((NA_I (El x_aEDn))
                                      :*
                                        ((NA_I (El x_aEDo))
                                           :*
                                             ((NA_I (El x_aEDp))
                                                :*
                                                  ((NA_I (El x_aEDq))
                                                     :* ((NA_I (El x_aEDr)) :* NP0))))))))
               (El (B9 x_aEDs x_aEDt x_aEDu x_aEDv x_aEDw x_aEDx x_aEDy))
                 -> Rep
                      (Pat1B9
                         ((NA_I (El x_aEDs))
                            :*
                              ((NA_I (El x_aEDt))
                                 :*
                                   ((NA_I (El x_aEDu))
                                      :*
                                        ((NA_I (El x_aEDv))
                                           :*
                                             ((NA_I (El x_aEDw))
                                                :*
                                                  ((NA_I (El x_aEDx))
                                                     :* ((NA_I (El x_aEDy)) :* NP0))))))))
               (El (BA x_aEDz x_aEDA x_aEDB x_aEDC x_aEDD x_aEDE x_aEDF))
                 -> Rep
                      (Pat1BA
                         ((NA_I (El x_aEDz))
                            :*
                              ((NA_I (El x_aEDA))
                                 :*
                                   ((NA_I (El x_aEDB))
                                      :*
                                        ((NA_I (El x_aEDC))
                                           :*
                                             ((NA_I (El x_aEDD))
                                                :*
                                                  ((NA_I (El x_aEDE))
                                                     :* ((NA_I (El x_aEDF)) :* NP0))))))))
               (El (BB x_aEDG x_aEDH x_aEDI x_aEDJ x_aEDK x_aEDL x_aEDM))
                 -> Rep
                      (Pat1BB
                         ((NA_I (El x_aEDG))
                            :*
                              ((NA_I (El x_aEDH))
                                 :*
                                   ((NA_I (El x_aEDI))
                                      :*
                                        ((NA_I (El x_aEDJ))
                                           :*
                                             ((NA_I (El x_aEDK))
                                                :*
                                                  ((NA_I (El x_aEDL))
                                                     :* ((NA_I (El x_aEDM)) :* NP0))))))))
               (El (BC x_aEDN x_aEDO x_aEDP x_aEDQ x_aEDR x_aEDS x_aEDT))
                 -> Rep
                      (Pat1BC
                         ((NA_I (El x_aEDN))
                            :*
                              ((NA_I (El x_aEDO))
                                 :*
                                   ((NA_I (El x_aEDP))
                                      :*
                                        ((NA_I (El x_aEDQ))
                                           :*
                                             ((NA_I (El x_aEDR))
                                                :*
                                                  ((NA_I (El x_aEDS))
                                                     :* ((NA_I (El x_aEDT)) :* NP0))))))))
               (El (BD x_aEDU x_aEDV x_aEDW x_aEDX x_aEDY x_aEDZ x_aEE0))
                 -> Rep
                      (Pat1BD
                         ((NA_I (El x_aEDU))
                            :*
                              ((NA_I (El x_aEDV))
                                 :*
                                   ((NA_I (El x_aEDW))
                                      :*
                                        ((NA_I (El x_aEDX))
                                           :*
                                             ((NA_I (El x_aEDY))
                                                :*
                                                  ((NA_I (El x_aEDZ))
                                                     :* ((NA_I (El x_aEE0)) :* NP0))))))))
               (El (BE x_aEE1 x_aEE2 x_aEE3 x_aEE4 x_aEE5 x_aEE6 x_aEE7))
                 -> Rep
                      (Pat1BE
                         ((NA_I (El x_aEE1))
                            :*
                              ((NA_I (El x_aEE2))
                                 :*
                                   ((NA_I (El x_aEE3))
                                      :*
                                        ((NA_I (El x_aEE4))
                                           :*
                                             ((NA_I (El x_aEE5))
                                                :*
                                                  ((NA_I (El x_aEE6))
                                                     :* ((NA_I (El x_aEE7)) :* NP0))))))))
               (El (BF x_aEE8 x_aEE9 x_aEEa x_aEEb x_aEEc x_aEEd x_aEEe))
                 -> Rep
                      (Pat1BF
                         ((NA_I (El x_aEE8))
                            :*
                              ((NA_I (El x_aEE9))
                                 :*
                                   ((NA_I (El x_aEEa))
                                      :*
                                        ((NA_I (El x_aEEb))
                                           :*
                                             ((NA_I (El x_aEEc))
                                                :*
                                                  ((NA_I (El x_aEEd))
                                                     :* ((NA_I (El x_aEEe)) :* NP0))))))))
        IdxC
          -> \case
               (El (C1 x_aEEf x_aEEg x_aEEh x_aEEi x_aEEj x_aEEk x_aEEl))
                 -> Rep
                      (Pat2C1
                         ((NA_I (El x_aEEf))
                            :*
                              ((NA_I (El x_aEEg))
                                 :*
                                   ((NA_I (El x_aEEh))
                                      :*
                                        ((NA_I (El x_aEEi))
                                           :*
                                             ((NA_I (El x_aEEj))
                                                :*
                                                  ((NA_I (El x_aEEk))
                                                     :* ((NA_I (El x_aEEl)) :* NP0))))))))
               (El (C2 x_aEEm x_aEEn x_aEEo x_aEEp x_aEEq x_aEEr x_aEEs))
                 -> Rep
                      (Pat2C2
                         ((NA_I (El x_aEEm))
                            :*
                              ((NA_I (El x_aEEn))
                                 :*
                                   ((NA_I (El x_aEEo))
                                      :*
                                        ((NA_I (El x_aEEp))
                                           :*
                                             ((NA_I (El x_aEEq))
                                                :*
                                                  ((NA_I (El x_aEEr))
                                                     :* ((NA_I (El x_aEEs)) :* NP0))))))))
               (El (C3 x_aEEt x_aEEu x_aEEv x_aEEw x_aEEx x_aEEy x_aEEz))
                 -> Rep
                      (Pat2C3
                         ((NA_I (El x_aEEt))
                            :*
                              ((NA_I (El x_aEEu))
                                 :*
                                   ((NA_I (El x_aEEv))
                                      :*
                                        ((NA_I (El x_aEEw))
                                           :*
                                             ((NA_I (El x_aEEx))
                                                :*
                                                  ((NA_I (El x_aEEy))
                                                     :* ((NA_I (El x_aEEz)) :* NP0))))))))
               (El (C4 x_aEEA x_aEEB x_aEEC x_aEED x_aEEE x_aEEF x_aEEG))
                 -> Rep
                      (Pat2C4
                         ((NA_I (El x_aEEA))
                            :*
                              ((NA_I (El x_aEEB))
                                 :*
                                   ((NA_I (El x_aEEC))
                                      :*
                                        ((NA_I (El x_aEED))
                                           :*
                                             ((NA_I (El x_aEEE))
                                                :*
                                                  ((NA_I (El x_aEEF))
                                                     :* ((NA_I (El x_aEEG)) :* NP0))))))))
               (El (C5 x_aEEH x_aEEI x_aEEJ x_aEEK x_aEEL x_aEEM x_aEEN))
                 -> Rep
                      (Pat2C5
                         ((NA_I (El x_aEEH))
                            :*
                              ((NA_I (El x_aEEI))
                                 :*
                                   ((NA_I (El x_aEEJ))
                                      :*
                                        ((NA_I (El x_aEEK))
                                           :*
                                             ((NA_I (El x_aEEL))
                                                :*
                                                  ((NA_I (El x_aEEM))
                                                     :* ((NA_I (El x_aEEN)) :* NP0))))))))
               (El (C6 x_aEEO x_aEEP x_aEEQ x_aEER x_aEES x_aEET x_aEEU))
                 -> Rep
                      (Pat2C6
                         ((NA_I (El x_aEEO))
                            :*
                              ((NA_I (El x_aEEP))
                                 :*
                                   ((NA_I (El x_aEEQ))
                                      :*
                                        ((NA_I (El x_aEER))
                                           :*
                                             ((NA_I (El x_aEES))
                                                :*
                                                  ((NA_I (El x_aEET))
                                                     :* ((NA_I (El x_aEEU)) :* NP0))))))))
               (El (C7 x_aEEV x_aEEW x_aEEX x_aEEY x_aEEZ x_aEF0 x_aEF1))
                 -> Rep
                      (Pat2C7
                         ((NA_I (El x_aEEV))
                            :*
                              ((NA_I (El x_aEEW))
                                 :*
                                   ((NA_I (El x_aEEX))
                                      :*
                                        ((NA_I (El x_aEEY))
                                           :*
                                             ((NA_I (El x_aEEZ))
                                                :*
                                                  ((NA_I (El x_aEF0))
                                                     :* ((NA_I (El x_aEF1)) :* NP0))))))))
               (El (C8 x_aEF2 x_aEF3 x_aEF4 x_aEF5 x_aEF6 x_aEF7 x_aEF8))
                 -> Rep
                      (Pat2C8
                         ((NA_I (El x_aEF2))
                            :*
                              ((NA_I (El x_aEF3))
                                 :*
                                   ((NA_I (El x_aEF4))
                                      :*
                                        ((NA_I (El x_aEF5))
                                           :*
                                             ((NA_I (El x_aEF6))
                                                :*
                                                  ((NA_I (El x_aEF7))
                                                     :* ((NA_I (El x_aEF8)) :* NP0))))))))
               (El (C9 x_aEF9 x_aEFa x_aEFb x_aEFc x_aEFd x_aEFe x_aEFf))
                 -> Rep
                      (Pat2C9
                         ((NA_I (El x_aEF9))
                            :*
                              ((NA_I (El x_aEFa))
                                 :*
                                   ((NA_I (El x_aEFb))
                                      :*
                                        ((NA_I (El x_aEFc))
                                           :*
                                             ((NA_I (El x_aEFd))
                                                :*
                                                  ((NA_I (El x_aEFe))
                                                     :* ((NA_I (El x_aEFf)) :* NP0))))))))
               (El (CA x_aEFg x_aEFh x_aEFi x_aEFj x_aEFk x_aEFl x_aEFm))
                 -> Rep
                      (Pat2CA
                         ((NA_I (El x_aEFg))
                            :*
                              ((NA_I (El x_aEFh))
                                 :*
                                   ((NA_I (El x_aEFi))
                                      :*
                                        ((NA_I (El x_aEFj))
                                           :*
                                             ((NA_I (El x_aEFk))
                                                :*
                                                  ((NA_I (El x_aEFl))
                                                     :* ((NA_I (El x_aEFm)) :* NP0))))))))
               (El (CB x_aEFn x_aEFo x_aEFp x_aEFq x_aEFr x_aEFs x_aEFt))
                 -> Rep
                      (Pat2CB
                         ((NA_I (El x_aEFn))
                            :*
                              ((NA_I (El x_aEFo))
                                 :*
                                   ((NA_I (El x_aEFp))
                                      :*
                                        ((NA_I (El x_aEFq))
                                           :*
                                             ((NA_I (El x_aEFr))
                                                :*
                                                  ((NA_I (El x_aEFs))
                                                     :* ((NA_I (El x_aEFt)) :* NP0))))))))
               (El (CC x_aEFu x_aEFv x_aEFw x_aEFx x_aEFy x_aEFz x_aEFA))
                 -> Rep
                      (Pat2CC
                         ((NA_I (El x_aEFu))
                            :*
                              ((NA_I (El x_aEFv))
                                 :*
                                   ((NA_I (El x_aEFw))
                                      :*
                                        ((NA_I (El x_aEFx))
                                           :*
                                             ((NA_I (El x_aEFy))
                                                :*
                                                  ((NA_I (El x_aEFz))
                                                     :* ((NA_I (El x_aEFA)) :* NP0))))))))
               (El (CD x_aEFB x_aEFC x_aEFD x_aEFE x_aEFF x_aEFG x_aEFH))
                 -> Rep
                      (Pat2CD
                         ((NA_I (El x_aEFB))
                            :*
                              ((NA_I (El x_aEFC))
                                 :*
                                   ((NA_I (El x_aEFD))
                                      :*
                                        ((NA_I (El x_aEFE))
                                           :*
                                             ((NA_I (El x_aEFF))
                                                :*
                                                  ((NA_I (El x_aEFG))
                                                     :* ((NA_I (El x_aEFH)) :* NP0))))))))
               (El (CE x_aEFI x_aEFJ x_aEFK x_aEFL x_aEFM x_aEFN x_aEFO))
                 -> Rep
                      (Pat2CE
                         ((NA_I (El x_aEFI))
                            :*
                              ((NA_I (El x_aEFJ))
                                 :*
                                   ((NA_I (El x_aEFK))
                                      :*
                                        ((NA_I (El x_aEFL))
                                           :*
                                             ((NA_I (El x_aEFM))
                                                :*
                                                  ((NA_I (El x_aEFN))
                                                     :* ((NA_I (El x_aEFO)) :* NP0))))))))
               (El (CF x_aEFP x_aEFQ x_aEFR x_aEFS x_aEFT x_aEFU x_aEFV))
                 -> Rep
                      (Pat2CF
                         ((NA_I (El x_aEFP))
                            :*
                              ((NA_I (El x_aEFQ))
                                 :*
                                   ((NA_I (El x_aEFR))
                                      :*
                                        ((NA_I (El x_aEFS))
                                           :*
                                             ((NA_I (El x_aEFT))
                                                :*
                                                  ((NA_I (El x_aEFU))
                                                     :* ((NA_I (El x_aEFV)) :* NP0))))))))
        IdxD
          -> \case
               (El (D1 x_aEFW x_aEFX x_aEFY x_aEFZ x_aEG0 x_aEG1 x_aEG2))
                 -> Rep
                      (Pat3D1
                         ((NA_I (El x_aEFW))
                            :*
                              ((NA_I (El x_aEFX))
                                 :*
                                   ((NA_I (El x_aEFY))
                                      :*
                                        ((NA_I (El x_aEFZ))
                                           :*
                                             ((NA_I (El x_aEG0))
                                                :*
                                                  ((NA_I (El x_aEG1))
                                                     :* ((NA_I (El x_aEG2)) :* NP0))))))))
               (El (D2 x_aEG3 x_aEG4 x_aEG5 x_aEG6 x_aEG7 x_aEG8 x_aEG9))
                 -> Rep
                      (Pat3D2
                         ((NA_I (El x_aEG3))
                            :*
                              ((NA_I (El x_aEG4))
                                 :*
                                   ((NA_I (El x_aEG5))
                                      :*
                                        ((NA_I (El x_aEG6))
                                           :*
                                             ((NA_I (El x_aEG7))
                                                :*
                                                  ((NA_I (El x_aEG8))
                                                     :* ((NA_I (El x_aEG9)) :* NP0))))))))
               (El (D3 x_aEGa x_aEGb x_aEGc x_aEGd x_aEGe x_aEGf x_aEGg))
                 -> Rep
                      (Pat3D3
                         ((NA_I (El x_aEGa))
                            :*
                              ((NA_I (El x_aEGb))
                                 :*
                                   ((NA_I (El x_aEGc))
                                      :*
                                        ((NA_I (El x_aEGd))
                                           :*
                                             ((NA_I (El x_aEGe))
                                                :*
                                                  ((NA_I (El x_aEGf))
                                                     :* ((NA_I (El x_aEGg)) :* NP0))))))))
               (El (D4 x_aEGh x_aEGi x_aEGj x_aEGk x_aEGl x_aEGm x_aEGn))
                 -> Rep
                      (Pat3D4
                         ((NA_I (El x_aEGh))
                            :*
                              ((NA_I (El x_aEGi))
                                 :*
                                   ((NA_I (El x_aEGj))
                                      :*
                                        ((NA_I (El x_aEGk))
                                           :*
                                             ((NA_I (El x_aEGl))
                                                :*
                                                  ((NA_I (El x_aEGm))
                                                     :* ((NA_I (El x_aEGn)) :* NP0))))))))
               (El (D5 x_aEGo x_aEGp x_aEGq x_aEGr x_aEGs x_aEGt x_aEGu))
                 -> Rep
                      (Pat3D5
                         ((NA_I (El x_aEGo))
                            :*
                              ((NA_I (El x_aEGp))
                                 :*
                                   ((NA_I (El x_aEGq))
                                      :*
                                        ((NA_I (El x_aEGr))
                                           :*
                                             ((NA_I (El x_aEGs))
                                                :*
                                                  ((NA_I (El x_aEGt))
                                                     :* ((NA_I (El x_aEGu)) :* NP0))))))))
               (El (D6 x_aEGv x_aEGw x_aEGx x_aEGy x_aEGz x_aEGA x_aEGB))
                 -> Rep
                      (Pat3D6
                         ((NA_I (El x_aEGv))
                            :*
                              ((NA_I (El x_aEGw))
                                 :*
                                   ((NA_I (El x_aEGx))
                                      :*
                                        ((NA_I (El x_aEGy))
                                           :*
                                             ((NA_I (El x_aEGz))
                                                :*
                                                  ((NA_I (El x_aEGA))
                                                     :* ((NA_I (El x_aEGB)) :* NP0))))))))
               (El (D7 x_aEGC x_aEGD x_aEGE x_aEGF x_aEGG x_aEGH x_aEGI))
                 -> Rep
                      (Pat3D7
                         ((NA_I (El x_aEGC))
                            :*
                              ((NA_I (El x_aEGD))
                                 :*
                                   ((NA_I (El x_aEGE))
                                      :*
                                        ((NA_I (El x_aEGF))
                                           :*
                                             ((NA_I (El x_aEGG))
                                                :*
                                                  ((NA_I (El x_aEGH))
                                                     :* ((NA_I (El x_aEGI)) :* NP0))))))))
               (El (D8 x_aEGJ x_aEGK x_aEGL x_aEGM x_aEGN x_aEGO x_aEGP))
                 -> Rep
                      (Pat3D8
                         ((NA_I (El x_aEGJ))
                            :*
                              ((NA_I (El x_aEGK))
                                 :*
                                   ((NA_I (El x_aEGL))
                                      :*
                                        ((NA_I (El x_aEGM))
                                           :*
                                             ((NA_I (El x_aEGN))
                                                :*
                                                  ((NA_I (El x_aEGO))
                                                     :* ((NA_I (El x_aEGP)) :* NP0))))))))
               (El (D9 x_aEGQ x_aEGR x_aEGS x_aEGT x_aEGU x_aEGV x_aEGW))
                 -> Rep
                      (Pat3D9
                         ((NA_I (El x_aEGQ))
                            :*
                              ((NA_I (El x_aEGR))
                                 :*
                                   ((NA_I (El x_aEGS))
                                      :*
                                        ((NA_I (El x_aEGT))
                                           :*
                                             ((NA_I (El x_aEGU))
                                                :*
                                                  ((NA_I (El x_aEGV))
                                                     :* ((NA_I (El x_aEGW)) :* NP0))))))))
               (El (DA x_aEGX x_aEGY x_aEGZ x_aEH0 x_aEH1 x_aEH2 x_aEH3))
                 -> Rep
                      (Pat3DA
                         ((NA_I (El x_aEGX))
                            :*
                              ((NA_I (El x_aEGY))
                                 :*
                                   ((NA_I (El x_aEGZ))
                                      :*
                                        ((NA_I (El x_aEH0))
                                           :*
                                             ((NA_I (El x_aEH1))
                                                :*
                                                  ((NA_I (El x_aEH2))
                                                     :* ((NA_I (El x_aEH3)) :* NP0))))))))
               (El (DB x_aEH4 x_aEH5 x_aEH6 x_aEH7 x_aEH8 x_aEH9 x_aEHa))
                 -> Rep
                      (Pat3DB
                         ((NA_I (El x_aEH4))
                            :*
                              ((NA_I (El x_aEH5))
                                 :*
                                   ((NA_I (El x_aEH6))
                                      :*
                                        ((NA_I (El x_aEH7))
                                           :*
                                             ((NA_I (El x_aEH8))
                                                :*
                                                  ((NA_I (El x_aEH9))
                                                     :* ((NA_I (El x_aEHa)) :* NP0))))))))
               (El (DC x_aEHb x_aEHc x_aEHd x_aEHe x_aEHf x_aEHg x_aEHh))
                 -> Rep
                      (Pat3DC
                         ((NA_I (El x_aEHb))
                            :*
                              ((NA_I (El x_aEHc))
                                 :*
                                   ((NA_I (El x_aEHd))
                                      :*
                                        ((NA_I (El x_aEHe))
                                           :*
                                             ((NA_I (El x_aEHf))
                                                :*
                                                  ((NA_I (El x_aEHg))
                                                     :* ((NA_I (El x_aEHh)) :* NP0))))))))
               (El (DD x_aEHi x_aEHj x_aEHk x_aEHl x_aEHm x_aEHn x_aEHo))
                 -> Rep
                      (Pat3DD
                         ((NA_I (El x_aEHi))
                            :*
                              ((NA_I (El x_aEHj))
                                 :*
                                   ((NA_I (El x_aEHk))
                                      :*
                                        ((NA_I (El x_aEHl))
                                           :*
                                             ((NA_I (El x_aEHm))
                                                :*
                                                  ((NA_I (El x_aEHn))
                                                     :* ((NA_I (El x_aEHo)) :* NP0))))))))
               (El (DE x_aEHp x_aEHq x_aEHr x_aEHs x_aEHt x_aEHu x_aEHv))
                 -> Rep
                      (Pat3DE
                         ((NA_I (El x_aEHp))
                            :*
                              ((NA_I (El x_aEHq))
                                 :*
                                   ((NA_I (El x_aEHr))
                                      :*
                                        ((NA_I (El x_aEHs))
                                           :*
                                             ((NA_I (El x_aEHt))
                                                :*
                                                  ((NA_I (El x_aEHu))
                                                     :* ((NA_I (El x_aEHv)) :* NP0))))))))
               (El (DF x_aEHw x_aEHx x_aEHy x_aEHz x_aEHA x_aEHB x_aEHC))
                 -> Rep
                      (Pat3DF
                         ((NA_I (El x_aEHw))
                            :*
                              ((NA_I (El x_aEHx))
                                 :*
                                   ((NA_I (El x_aEHy))
                                      :*
                                        ((NA_I (El x_aEHz))
                                           :*
                                             ((NA_I (El x_aEHA))
                                                :*
                                                  ((NA_I (El x_aEHB))
                                                     :* ((NA_I (El x_aEHC)) :* NP0))))))))
        IdxE
          -> \case
               (El (E1 x_aEHD x_aEHE x_aEHF x_aEHG x_aEHH x_aEHI x_aEHJ))
                 -> Rep
                      (Pat4E1
                         ((NA_I (El x_aEHD))
                            :*
                              ((NA_I (El x_aEHE))
                                 :*
                                   ((NA_I (El x_aEHF))
                                      :*
                                        ((NA_I (El x_aEHG))
                                           :*
                                             ((NA_I (El x_aEHH))
                                                :*
                                                  ((NA_I (El x_aEHI))
                                                     :* ((NA_I (El x_aEHJ)) :* NP0))))))))
               (El (E2 x_aEHK x_aEHL x_aEHM x_aEHN x_aEHO x_aEHP x_aEHQ))
                 -> Rep
                      (Pat4E2
                         ((NA_I (El x_aEHK))
                            :*
                              ((NA_I (El x_aEHL))
                                 :*
                                   ((NA_I (El x_aEHM))
                                      :*
                                        ((NA_I (El x_aEHN))
                                           :*
                                             ((NA_I (El x_aEHO))
                                                :*
                                                  ((NA_I (El x_aEHP))
                                                     :* ((NA_I (El x_aEHQ)) :* NP0))))))))
               (El (E3 x_aEHR x_aEHS x_aEHT x_aEHU x_aEHV x_aEHW x_aEHX))
                 -> Rep
                      (Pat4E3
                         ((NA_I (El x_aEHR))
                            :*
                              ((NA_I (El x_aEHS))
                                 :*
                                   ((NA_I (El x_aEHT))
                                      :*
                                        ((NA_I (El x_aEHU))
                                           :*
                                             ((NA_I (El x_aEHV))
                                                :*
                                                  ((NA_I (El x_aEHW))
                                                     :* ((NA_I (El x_aEHX)) :* NP0))))))))
               (El (E4 x_aEHY x_aEHZ x_aEI0 x_aEI1 x_aEI2 x_aEI3 x_aEI4))
                 -> Rep
                      (Pat4E4
                         ((NA_I (El x_aEHY))
                            :*
                              ((NA_I (El x_aEHZ))
                                 :*
                                   ((NA_I (El x_aEI0))
                                      :*
                                        ((NA_I (El x_aEI1))
                                           :*
                                             ((NA_I (El x_aEI2))
                                                :*
                                                  ((NA_I (El x_aEI3))
                                                     :* ((NA_I (El x_aEI4)) :* NP0))))))))
               (El (E5 x_aEI5 x_aEI6 x_aEI7 x_aEI8 x_aEI9 x_aEIa x_aEIb))
                 -> Rep
                      (Pat4E5
                         ((NA_I (El x_aEI5))
                            :*
                              ((NA_I (El x_aEI6))
                                 :*
                                   ((NA_I (El x_aEI7))
                                      :*
                                        ((NA_I (El x_aEI8))
                                           :*
                                             ((NA_I (El x_aEI9))
                                                :*
                                                  ((NA_I (El x_aEIa))
                                                     :* ((NA_I (El x_aEIb)) :* NP0))))))))
               (El (E6 x_aEIc x_aEId x_aEIe x_aEIf x_aEIg x_aEIh x_aEIi))
                 -> Rep
                      (Pat4E6
                         ((NA_I (El x_aEIc))
                            :*
                              ((NA_I (El x_aEId))
                                 :*
                                   ((NA_I (El x_aEIe))
                                      :*
                                        ((NA_I (El x_aEIf))
                                           :*
                                             ((NA_I (El x_aEIg))
                                                :*
                                                  ((NA_I (El x_aEIh))
                                                     :* ((NA_I (El x_aEIi)) :* NP0))))))))
               (El (E7 x_aEIj x_aEIk x_aEIl x_aEIm x_aEIn x_aEIo x_aEIp))
                 -> Rep
                      (Pat4E7
                         ((NA_I (El x_aEIj))
                            :*
                              ((NA_I (El x_aEIk))
                                 :*
                                   ((NA_I (El x_aEIl))
                                      :*
                                        ((NA_I (El x_aEIm))
                                           :*
                                             ((NA_I (El x_aEIn))
                                                :*
                                                  ((NA_I (El x_aEIo))
                                                     :* ((NA_I (El x_aEIp)) :* NP0))))))))
               (El (E8 x_aEIq x_aEIr x_aEIs x_aEIt x_aEIu x_aEIv x_aEIw))
                 -> Rep
                      (Pat4E8
                         ((NA_I (El x_aEIq))
                            :*
                              ((NA_I (El x_aEIr))
                                 :*
                                   ((NA_I (El x_aEIs))
                                      :*
                                        ((NA_I (El x_aEIt))
                                           :*
                                             ((NA_I (El x_aEIu))
                                                :*
                                                  ((NA_I (El x_aEIv))
                                                     :* ((NA_I (El x_aEIw)) :* NP0))))))))
               (El (E9 x_aEIx x_aEIy x_aEIz x_aEIA x_aEIB x_aEIC x_aEID))
                 -> Rep
                      (Pat4E9
                         ((NA_I (El x_aEIx))
                            :*
                              ((NA_I (El x_aEIy))
                                 :*
                                   ((NA_I (El x_aEIz))
                                      :*
                                        ((NA_I (El x_aEIA))
                                           :*
                                             ((NA_I (El x_aEIB))
                                                :*
                                                  ((NA_I (El x_aEIC))
                                                     :* ((NA_I (El x_aEID)) :* NP0))))))))
               (El (EA x_aEIE x_aEIF x_aEIG x_aEIH x_aEII x_aEIJ x_aEIK))
                 -> Rep
                      (Pat4EA
                         ((NA_I (El x_aEIE))
                            :*
                              ((NA_I (El x_aEIF))
                                 :*
                                   ((NA_I (El x_aEIG))
                                      :*
                                        ((NA_I (El x_aEIH))
                                           :*
                                             ((NA_I (El x_aEII))
                                                :*
                                                  ((NA_I (El x_aEIJ))
                                                     :* ((NA_I (El x_aEIK)) :* NP0))))))))
               (El (EB x_aEIL x_aEIM x_aEIN x_aEIO x_aEIP x_aEIQ x_aEIR))
                 -> Rep
                      (Pat4EB
                         ((NA_I (El x_aEIL))
                            :*
                              ((NA_I (El x_aEIM))
                                 :*
                                   ((NA_I (El x_aEIN))
                                      :*
                                        ((NA_I (El x_aEIO))
                                           :*
                                             ((NA_I (El x_aEIP))
                                                :*
                                                  ((NA_I (El x_aEIQ))
                                                     :* ((NA_I (El x_aEIR)) :* NP0))))))))
               (El (EC x_aEIS x_aEIT x_aEIU x_aEIV x_aEIW x_aEIX x_aEIY))
                 -> Rep
                      (Pat4EC
                         ((NA_I (El x_aEIS))
                            :*
                              ((NA_I (El x_aEIT))
                                 :*
                                   ((NA_I (El x_aEIU))
                                      :*
                                        ((NA_I (El x_aEIV))
                                           :*
                                             ((NA_I (El x_aEIW))
                                                :*
                                                  ((NA_I (El x_aEIX))
                                                     :* ((NA_I (El x_aEIY)) :* NP0))))))))
               (El (ED x_aEIZ x_aEJ0 x_aEJ1 x_aEJ2 x_aEJ3 x_aEJ4 x_aEJ5))
                 -> Rep
                      (Pat4ED
                         ((NA_I (El x_aEIZ))
                            :*
                              ((NA_I (El x_aEJ0))
                                 :*
                                   ((NA_I (El x_aEJ1))
                                      :*
                                        ((NA_I (El x_aEJ2))
                                           :*
                                             ((NA_I (El x_aEJ3))
                                                :*
                                                  ((NA_I (El x_aEJ4))
                                                     :* ((NA_I (El x_aEJ5)) :* NP0))))))))
               (El (EE x_aEJ6 x_aEJ7 x_aEJ8 x_aEJ9 x_aEJa x_aEJb x_aEJc))
                 -> Rep
                      (Pat4EE
                         ((NA_I (El x_aEJ6))
                            :*
                              ((NA_I (El x_aEJ7))
                                 :*
                                   ((NA_I (El x_aEJ8))
                                      :*
                                        ((NA_I (El x_aEJ9))
                                           :*
                                             ((NA_I (El x_aEJa))
                                                :*
                                                  ((NA_I (El x_aEJb))
                                                     :* ((NA_I (El x_aEJc)) :* NP0))))))))
               (El (EF x_aEJd x_aEJe x_aEJf x_aEJg x_aEJh x_aEJi x_aEJj))
                 -> Rep
                      (Pat4EF
                         ((NA_I (El x_aEJd))
                            :*
                              ((NA_I (El x_aEJe))
                                 :*
                                   ((NA_I (El x_aEJf))
                                      :*
                                        ((NA_I (El x_aEJg))
                                           :*
                                             ((NA_I (El x_aEJh))
                                                :*
                                                  ((NA_I (El x_aEJi))
                                                     :* ((NA_I (El x_aEJj)) :* NP0))))))))
        IdxF -> \case
        IdxG -> \case
  sto'
    = \case
        IdxA
          -> \case
               (Rep (Pat0A1 (NA_I (El y_aEJk) :* (NA_I (El y_aEJl) :* (NA_I (El y_aEJm) :* (NA_I (El y_aEJn) :* (NA_I (El y_aEJo) :* (NA_I (El y_aEJp) :* (NA_I (El y_aEJq) :* NP0)))))))))
                 -> El
                      (((((((A1 y_aEJk) y_aEJl) y_aEJm) y_aEJn) y_aEJo) y_aEJp) y_aEJq)
               (Rep (Pat0A2 (NA_I (El y_aEJr) :* (NA_I (El y_aEJs) :* (NA_I (El y_aEJt) :* (NA_I (El y_aEJu) :* (NA_I (El y_aEJv) :* (NA_I (El y_aEJw) :* (NA_I (El y_aEJx) :* NP0)))))))))
                 -> El
                      (((((((A2 y_aEJr) y_aEJs) y_aEJt) y_aEJu) y_aEJv) y_aEJw) y_aEJx)
               (Rep (Pat0A3 (NA_I (El y_aEJy) :* (NA_I (El y_aEJz) :* (NA_I (El y_aEJA) :* (NA_I (El y_aEJB) :* (NA_I (El y_aEJC) :* (NA_I (El y_aEJD) :* (NA_I (El y_aEJE) :* NP0)))))))))
                 -> El
                      (((((((A3 y_aEJy) y_aEJz) y_aEJA) y_aEJB) y_aEJC) y_aEJD) y_aEJE)
               (Rep (Pat0A4 (NA_I (El y_aEJF) :* (NA_I (El y_aEJG) :* (NA_I (El y_aEJH) :* (NA_I (El y_aEJI) :* (NA_I (El y_aEJJ) :* (NA_I (El y_aEJK) :* (NA_I (El y_aEJL) :* NP0)))))))))
                 -> El
                      (((((((A4 y_aEJF) y_aEJG) y_aEJH) y_aEJI) y_aEJJ) y_aEJK) y_aEJL)
               (Rep (Pat0A5 (NA_I (El y_aEJM) :* (NA_I (El y_aEJN) :* (NA_I (El y_aEJO) :* (NA_I (El y_aEJP) :* (NA_I (El y_aEJQ) :* (NA_I (El y_aEJR) :* (NA_I (El y_aEJS) :* NP0)))))))))
                 -> El
                      (((((((A5 y_aEJM) y_aEJN) y_aEJO) y_aEJP) y_aEJQ) y_aEJR) y_aEJS)
               (Rep (Pat0A6 (NA_I (El y_aEJT) :* (NA_I (El y_aEJU) :* (NA_I (El y_aEJV) :* (NA_I (El y_aEJW) :* (NA_I (El y_aEJX) :* (NA_I (El y_aEJY) :* (NA_I (El y_aEJZ) :* NP0)))))))))
                 -> El
                      (((((((A6 y_aEJT) y_aEJU) y_aEJV) y_aEJW) y_aEJX) y_aEJY) y_aEJZ)
               (Rep (Pat0A7 (NA_I (El y_aEK0) :* (NA_I (El y_aEK1) :* (NA_I (El y_aEK2) :* (NA_I (El y_aEK3) :* (NA_I (El y_aEK4) :* (NA_I (El y_aEK5) :* (NA_I (El y_aEK6) :* NP0)))))))))
                 -> El
                      (((((((A7 y_aEK0) y_aEK1) y_aEK2) y_aEK3) y_aEK4) y_aEK5) y_aEK6)
               (Rep (Pat0A8 (NA_I (El y_aEK7) :* (NA_I (El y_aEK8) :* (NA_I (El y_aEK9) :* (NA_I (El y_aEKa) :* (NA_I (El y_aEKb) :* (NA_I (El y_aEKc) :* (NA_I (El y_aEKd) :* NP0)))))))))
                 -> El
                      (((((((A8 y_aEK7) y_aEK8) y_aEK9) y_aEKa) y_aEKb) y_aEKc) y_aEKd)
               (Rep (Pat0A9 (NA_I (El y_aEKe) :* (NA_I (El y_aEKf) :* (NA_I (El y_aEKg) :* (NA_I (El y_aEKh) :* (NA_I (El y_aEKi) :* (NA_I (El y_aEKj) :* (NA_I (El y_aEKk) :* NP0)))))))))
                 -> El
                      (((((((A9 y_aEKe) y_aEKf) y_aEKg) y_aEKh) y_aEKi) y_aEKj) y_aEKk)
               (Rep (Pat0AA (NA_I (El y_aEKl) :* (NA_I (El y_aEKm) :* (NA_I (El y_aEKn) :* (NA_I (El y_aEKo) :* (NA_I (El y_aEKp) :* (NA_I (El y_aEKq) :* (NA_I (El y_aEKr) :* NP0)))))))))
                 -> El
                      (((((((AA y_aEKl) y_aEKm) y_aEKn) y_aEKo) y_aEKp) y_aEKq) y_aEKr)
               (Rep (Pat0AB (NA_I (El y_aEKs) :* (NA_I (El y_aEKt) :* (NA_I (El y_aEKu) :* (NA_I (El y_aEKv) :* (NA_I (El y_aEKw) :* (NA_I (El y_aEKx) :* (NA_I (El y_aEKy) :* NP0)))))))))
                 -> El
                      (((((((AB y_aEKs) y_aEKt) y_aEKu) y_aEKv) y_aEKw) y_aEKx) y_aEKy)
               (Rep (Pat0AC (NA_I (El y_aEKz) :* (NA_I (El y_aEKA) :* (NA_I (El y_aEKB) :* (NA_I (El y_aEKC) :* (NA_I (El y_aEKD) :* (NA_I (El y_aEKE) :* (NA_I (El y_aEKF) :* NP0)))))))))
                 -> El
                      (((((((AC y_aEKz) y_aEKA) y_aEKB) y_aEKC) y_aEKD) y_aEKE) y_aEKF)
               (Rep (Pat0AD (NA_I (El y_aEKG) :* (NA_I (El y_aEKH) :* (NA_I (El y_aEKI) :* (NA_I (El y_aEKJ) :* (NA_I (El y_aEKK) :* (NA_I (El y_aEKL) :* (NA_I (El y_aEKM) :* NP0)))))))))
                 -> El
                      (((((((AD y_aEKG) y_aEKH) y_aEKI) y_aEKJ) y_aEKK) y_aEKL) y_aEKM)
               (Rep (Pat0AE (NA_I (El y_aEKN) :* (NA_I (El y_aEKO) :* (NA_I (El y_aEKP) :* (NA_I (El y_aEKQ) :* (NA_I (El y_aEKR) :* (NA_I (El y_aEKS) :* (NA_I (El y_aEKT) :* NP0)))))))))
                 -> El
                      (((((((AE y_aEKN) y_aEKO) y_aEKP) y_aEKQ) y_aEKR) y_aEKS) y_aEKT)
               (Rep (Pat0AF (NA_I (El y_aEKU) :* (NA_I (El y_aEKV) :* (NA_I (El y_aEKW) :* (NA_I (El y_aEKX) :* (NA_I (El y_aEKY) :* (NA_I (El y_aEKZ) :* (NA_I (El y_aEL0) :* NP0)))))))))
                 -> El
                      (((((((AF y_aEKU) y_aEKV) y_aEKW) y_aEKX) y_aEKY) y_aEKZ) y_aEL0)
               _ -> error "matchAll"
        IdxB
          -> \case
               (Rep (Pat1B1 (NA_I (El y_aEL1) :* (NA_I (El y_aEL2) :* (NA_I (El y_aEL3) :* (NA_I (El y_aEL4) :* (NA_I (El y_aEL5) :* (NA_I (El y_aEL6) :* (NA_I (El y_aEL7) :* NP0)))))))))
                 -> El
                      (((((((B1 y_aEL1) y_aEL2) y_aEL3) y_aEL4) y_aEL5) y_aEL6) y_aEL7)
               (Rep (Pat1B2 (NA_I (El y_aEL8) :* (NA_I (El y_aEL9) :* (NA_I (El y_aELa) :* (NA_I (El y_aELb) :* (NA_I (El y_aELc) :* (NA_I (El y_aELd) :* (NA_I (El y_aELe) :* NP0)))))))))
                 -> El
                      (((((((B2 y_aEL8) y_aEL9) y_aELa) y_aELb) y_aELc) y_aELd) y_aELe)
               (Rep (Pat1B3 (NA_I (El y_aELf) :* (NA_I (El y_aELg) :* (NA_I (El y_aELh) :* (NA_I (El y_aELi) :* (NA_I (El y_aELj) :* (NA_I (El y_aELk) :* (NA_I (El y_aELl) :* NP0)))))))))
                 -> El
                      (((((((B3 y_aELf) y_aELg) y_aELh) y_aELi) y_aELj) y_aELk) y_aELl)
               (Rep (Pat1B4 (NA_I (El y_aELm) :* (NA_I (El y_aELn) :* (NA_I (El y_aELo) :* (NA_I (El y_aELp) :* (NA_I (El y_aELq) :* (NA_I (El y_aELr) :* (NA_I (El y_aELs) :* NP0)))))))))
                 -> El
                      (((((((B4 y_aELm) y_aELn) y_aELo) y_aELp) y_aELq) y_aELr) y_aELs)
               (Rep (Pat1B5 (NA_I (El y_aELt) :* (NA_I (El y_aELu) :* (NA_I (El y_aELv) :* (NA_I (El y_aELw) :* (NA_I (El y_aELx) :* (NA_I (El y_aELy) :* (NA_I (El y_aELz) :* NP0)))))))))
                 -> El
                      (((((((B5 y_aELt) y_aELu) y_aELv) y_aELw) y_aELx) y_aELy) y_aELz)
               (Rep (Pat1B6 (NA_I (El y_aELA) :* (NA_I (El y_aELB) :* (NA_I (El y_aELC) :* (NA_I (El y_aELD) :* (NA_I (El y_aELE) :* (NA_I (El y_aELF) :* (NA_I (El y_aELG) :* NP0)))))))))
                 -> El
                      (((((((B6 y_aELA) y_aELB) y_aELC) y_aELD) y_aELE) y_aELF) y_aELG)
               (Rep (Pat1B7 (NA_I (El y_aELH) :* (NA_I (El y_aELI) :* (NA_I (El y_aELJ) :* (NA_I (El y_aELK) :* (NA_I (El y_aELL) :* (NA_I (El y_aELM) :* (NA_I (El y_aELN) :* NP0)))))))))
                 -> El
                      (((((((B7 y_aELH) y_aELI) y_aELJ) y_aELK) y_aELL) y_aELM) y_aELN)
               (Rep (Pat1B8 (NA_I (El y_aELO) :* (NA_I (El y_aELP) :* (NA_I (El y_aELQ) :* (NA_I (El y_aELR) :* (NA_I (El y_aELS) :* (NA_I (El y_aELT) :* (NA_I (El y_aELU) :* NP0)))))))))
                 -> El
                      (((((((B8 y_aELO) y_aELP) y_aELQ) y_aELR) y_aELS) y_aELT) y_aELU)
               (Rep (Pat1B9 (NA_I (El y_aELV) :* (NA_I (El y_aELW) :* (NA_I (El y_aELX) :* (NA_I (El y_aELY) :* (NA_I (El y_aELZ) :* (NA_I (El y_aEM0) :* (NA_I (El y_aEM1) :* NP0)))))))))
                 -> El
                      (((((((B9 y_aELV) y_aELW) y_aELX) y_aELY) y_aELZ) y_aEM0) y_aEM1)
               (Rep (Pat1BA (NA_I (El y_aEM2) :* (NA_I (El y_aEM3) :* (NA_I (El y_aEM4) :* (NA_I (El y_aEM5) :* (NA_I (El y_aEM6) :* (NA_I (El y_aEM7) :* (NA_I (El y_aEM8) :* NP0)))))))))
                 -> El
                      (((((((BA y_aEM2) y_aEM3) y_aEM4) y_aEM5) y_aEM6) y_aEM7) y_aEM8)
               (Rep (Pat1BB (NA_I (El y_aEM9) :* (NA_I (El y_aEMa) :* (NA_I (El y_aEMb) :* (NA_I (El y_aEMc) :* (NA_I (El y_aEMd) :* (NA_I (El y_aEMe) :* (NA_I (El y_aEMf) :* NP0)))))))))
                 -> El
                      (((((((BB y_aEM9) y_aEMa) y_aEMb) y_aEMc) y_aEMd) y_aEMe) y_aEMf)
               (Rep (Pat1BC (NA_I (El y_aEMg) :* (NA_I (El y_aEMh) :* (NA_I (El y_aEMi) :* (NA_I (El y_aEMj) :* (NA_I (El y_aEMk) :* (NA_I (El y_aEMl) :* (NA_I (El y_aEMm) :* NP0)))))))))
                 -> El
                      (((((((BC y_aEMg) y_aEMh) y_aEMi) y_aEMj) y_aEMk) y_aEMl) y_aEMm)
               (Rep (Pat1BD (NA_I (El y_aEMn) :* (NA_I (El y_aEMo) :* (NA_I (El y_aEMp) :* (NA_I (El y_aEMq) :* (NA_I (El y_aEMr) :* (NA_I (El y_aEMs) :* (NA_I (El y_aEMt) :* NP0)))))))))
                 -> El
                      (((((((BD y_aEMn) y_aEMo) y_aEMp) y_aEMq) y_aEMr) y_aEMs) y_aEMt)
               (Rep (Pat1BE (NA_I (El y_aEMu) :* (NA_I (El y_aEMv) :* (NA_I (El y_aEMw) :* (NA_I (El y_aEMx) :* (NA_I (El y_aEMy) :* (NA_I (El y_aEMz) :* (NA_I (El y_aEMA) :* NP0)))))))))
                 -> El
                      (((((((BE y_aEMu) y_aEMv) y_aEMw) y_aEMx) y_aEMy) y_aEMz) y_aEMA)
               (Rep (Pat1BF (NA_I (El y_aEMB) :* (NA_I (El y_aEMC) :* (NA_I (El y_aEMD) :* (NA_I (El y_aEME) :* (NA_I (El y_aEMF) :* (NA_I (El y_aEMG) :* (NA_I (El y_aEMH) :* NP0)))))))))
                 -> El
                      (((((((BF y_aEMB) y_aEMC) y_aEMD) y_aEME) y_aEMF) y_aEMG) y_aEMH)
               _ -> error "matchAll"
        IdxC
          -> \case
               (Rep (Pat2C1 (NA_I (El y_aEMI) :* (NA_I (El y_aEMJ) :* (NA_I (El y_aEMK) :* (NA_I (El y_aEML) :* (NA_I (El y_aEMM) :* (NA_I (El y_aEMN) :* (NA_I (El y_aEMO) :* NP0)))))))))
                 -> El
                      (((((((C1 y_aEMI) y_aEMJ) y_aEMK) y_aEML) y_aEMM) y_aEMN) y_aEMO)
               (Rep (Pat2C2 (NA_I (El y_aEMP) :* (NA_I (El y_aEMQ) :* (NA_I (El y_aEMR) :* (NA_I (El y_aEMS) :* (NA_I (El y_aEMT) :* (NA_I (El y_aEMU) :* (NA_I (El y_aEMV) :* NP0)))))))))
                 -> El
                      (((((((C2 y_aEMP) y_aEMQ) y_aEMR) y_aEMS) y_aEMT) y_aEMU) y_aEMV)
               (Rep (Pat2C3 (NA_I (El y_aEMW) :* (NA_I (El y_aEMX) :* (NA_I (El y_aEMY) :* (NA_I (El y_aEMZ) :* (NA_I (El y_aEN0) :* (NA_I (El y_aEN1) :* (NA_I (El y_aEN2) :* NP0)))))))))
                 -> El
                      (((((((C3 y_aEMW) y_aEMX) y_aEMY) y_aEMZ) y_aEN0) y_aEN1) y_aEN2)
               (Rep (Pat2C4 (NA_I (El y_aEN3) :* (NA_I (El y_aEN4) :* (NA_I (El y_aEN5) :* (NA_I (El y_aEN6) :* (NA_I (El y_aEN7) :* (NA_I (El y_aEN8) :* (NA_I (El y_aEN9) :* NP0)))))))))
                 -> El
                      (((((((C4 y_aEN3) y_aEN4) y_aEN5) y_aEN6) y_aEN7) y_aEN8) y_aEN9)
               (Rep (Pat2C5 (NA_I (El y_aENa) :* (NA_I (El y_aENb) :* (NA_I (El y_aENc) :* (NA_I (El y_aENd) :* (NA_I (El y_aENe) :* (NA_I (El y_aENf) :* (NA_I (El y_aENg) :* NP0)))))))))
                 -> El
                      (((((((C5 y_aENa) y_aENb) y_aENc) y_aENd) y_aENe) y_aENf) y_aENg)
               (Rep (Pat2C6 (NA_I (El y_aENh) :* (NA_I (El y_aENi) :* (NA_I (El y_aENj) :* (NA_I (El y_aENk) :* (NA_I (El y_aENl) :* (NA_I (El y_aENm) :* (NA_I (El y_aENn) :* NP0)))))))))
                 -> El
                      (((((((C6 y_aENh) y_aENi) y_aENj) y_aENk) y_aENl) y_aENm) y_aENn)
               (Rep (Pat2C7 (NA_I (El y_aENo) :* (NA_I (El y_aENp) :* (NA_I (El y_aENq) :* (NA_I (El y_aENr) :* (NA_I (El y_aENs) :* (NA_I (El y_aENt) :* (NA_I (El y_aENu) :* NP0)))))))))
                 -> El
                      (((((((C7 y_aENo) y_aENp) y_aENq) y_aENr) y_aENs) y_aENt) y_aENu)
               (Rep (Pat2C8 (NA_I (El y_aENv) :* (NA_I (El y_aENw) :* (NA_I (El y_aENx) :* (NA_I (El y_aENy) :* (NA_I (El y_aENz) :* (NA_I (El y_aENA) :* (NA_I (El y_aENB) :* NP0)))))))))
                 -> El
                      (((((((C8 y_aENv) y_aENw) y_aENx) y_aENy) y_aENz) y_aENA) y_aENB)
               (Rep (Pat2C9 (NA_I (El y_aENC) :* (NA_I (El y_aEND) :* (NA_I (El y_aENE) :* (NA_I (El y_aENF) :* (NA_I (El y_aENG) :* (NA_I (El y_aENH) :* (NA_I (El y_aENI) :* NP0)))))))))
                 -> El
                      (((((((C9 y_aENC) y_aEND) y_aENE) y_aENF) y_aENG) y_aENH) y_aENI)
               (Rep (Pat2CA (NA_I (El y_aENJ) :* (NA_I (El y_aENK) :* (NA_I (El y_aENL) :* (NA_I (El y_aENM) :* (NA_I (El y_aENN) :* (NA_I (El y_aENO) :* (NA_I (El y_aENP) :* NP0)))))))))
                 -> El
                      (((((((CA y_aENJ) y_aENK) y_aENL) y_aENM) y_aENN) y_aENO) y_aENP)
               (Rep (Pat2CB (NA_I (El y_aENQ) :* (NA_I (El y_aENR) :* (NA_I (El y_aENS) :* (NA_I (El y_aENT) :* (NA_I (El y_aENU) :* (NA_I (El y_aENV) :* (NA_I (El y_aENW) :* NP0)))))))))
                 -> El
                      (((((((CB y_aENQ) y_aENR) y_aENS) y_aENT) y_aENU) y_aENV) y_aENW)
               (Rep (Pat2CC (NA_I (El y_aENX) :* (NA_I (El y_aENY) :* (NA_I (El y_aENZ) :* (NA_I (El y_aEO0) :* (NA_I (El y_aEO1) :* (NA_I (El y_aEO2) :* (NA_I (El y_aEO3) :* NP0)))))))))
                 -> El
                      (((((((CC y_aENX) y_aENY) y_aENZ) y_aEO0) y_aEO1) y_aEO2) y_aEO3)
               (Rep (Pat2CD (NA_I (El y_aEO4) :* (NA_I (El y_aEO5) :* (NA_I (El y_aEO6) :* (NA_I (El y_aEO7) :* (NA_I (El y_aEO8) :* (NA_I (El y_aEO9) :* (NA_I (El y_aEOa) :* NP0)))))))))
                 -> El
                      (((((((CD y_aEO4) y_aEO5) y_aEO6) y_aEO7) y_aEO8) y_aEO9) y_aEOa)
               (Rep (Pat2CE (NA_I (El y_aEOb) :* (NA_I (El y_aEOc) :* (NA_I (El y_aEOd) :* (NA_I (El y_aEOe) :* (NA_I (El y_aEOf) :* (NA_I (El y_aEOg) :* (NA_I (El y_aEOh) :* NP0)))))))))
                 -> El
                      (((((((CE y_aEOb) y_aEOc) y_aEOd) y_aEOe) y_aEOf) y_aEOg) y_aEOh)
               (Rep (Pat2CF (NA_I (El y_aEOi) :* (NA_I (El y_aEOj) :* (NA_I (El y_aEOk) :* (NA_I (El y_aEOl) :* (NA_I (El y_aEOm) :* (NA_I (El y_aEOn) :* (NA_I (El y_aEOo) :* NP0)))))))))
                 -> El
                      (((((((CF y_aEOi) y_aEOj) y_aEOk) y_aEOl) y_aEOm) y_aEOn) y_aEOo)
               _ -> error "matchAll"
        IdxD
          -> \case
               (Rep (Pat3D1 (NA_I (El y_aEOp) :* (NA_I (El y_aEOq) :* (NA_I (El y_aEOr) :* (NA_I (El y_aEOs) :* (NA_I (El y_aEOt) :* (NA_I (El y_aEOu) :* (NA_I (El y_aEOv) :* NP0)))))))))
                 -> El
                      (((((((D1 y_aEOp) y_aEOq) y_aEOr) y_aEOs) y_aEOt) y_aEOu) y_aEOv)
               (Rep (Pat3D2 (NA_I (El y_aEOw) :* (NA_I (El y_aEOx) :* (NA_I (El y_aEOy) :* (NA_I (El y_aEOz) :* (NA_I (El y_aEOA) :* (NA_I (El y_aEOB) :* (NA_I (El y_aEOC) :* NP0)))))))))
                 -> El
                      (((((((D2 y_aEOw) y_aEOx) y_aEOy) y_aEOz) y_aEOA) y_aEOB) y_aEOC)
               (Rep (Pat3D3 (NA_I (El y_aEOD) :* (NA_I (El y_aEOE) :* (NA_I (El y_aEOF) :* (NA_I (El y_aEOG) :* (NA_I (El y_aEOH) :* (NA_I (El y_aEOI) :* (NA_I (El y_aEOJ) :* NP0)))))))))
                 -> El
                      (((((((D3 y_aEOD) y_aEOE) y_aEOF) y_aEOG) y_aEOH) y_aEOI) y_aEOJ)
               (Rep (Pat3D4 (NA_I (El y_aEOK) :* (NA_I (El y_aEOL) :* (NA_I (El y_aEOM) :* (NA_I (El y_aEON) :* (NA_I (El y_aEOO) :* (NA_I (El y_aEOP) :* (NA_I (El y_aEOQ) :* NP0)))))))))
                 -> El
                      (((((((D4 y_aEOK) y_aEOL) y_aEOM) y_aEON) y_aEOO) y_aEOP) y_aEOQ)
               (Rep (Pat3D5 (NA_I (El y_aEOR) :* (NA_I (El y_aEOS) :* (NA_I (El y_aEOT) :* (NA_I (El y_aEOU) :* (NA_I (El y_aEOV) :* (NA_I (El y_aEOW) :* (NA_I (El y_aEOX) :* NP0)))))))))
                 -> El
                      (((((((D5 y_aEOR) y_aEOS) y_aEOT) y_aEOU) y_aEOV) y_aEOW) y_aEOX)
               (Rep (Pat3D6 (NA_I (El y_aEOY) :* (NA_I (El y_aEOZ) :* (NA_I (El y_aEP0) :* (NA_I (El y_aEP1) :* (NA_I (El y_aEP2) :* (NA_I (El y_aEP3) :* (NA_I (El y_aEP4) :* NP0)))))))))
                 -> El
                      (((((((D6 y_aEOY) y_aEOZ) y_aEP0) y_aEP1) y_aEP2) y_aEP3) y_aEP4)
               (Rep (Pat3D7 (NA_I (El y_aEP5) :* (NA_I (El y_aEP6) :* (NA_I (El y_aEP7) :* (NA_I (El y_aEP8) :* (NA_I (El y_aEP9) :* (NA_I (El y_aEPa) :* (NA_I (El y_aEPb) :* NP0)))))))))
                 -> El
                      (((((((D7 y_aEP5) y_aEP6) y_aEP7) y_aEP8) y_aEP9) y_aEPa) y_aEPb)
               (Rep (Pat3D8 (NA_I (El y_aEPc) :* (NA_I (El y_aEPd) :* (NA_I (El y_aEPe) :* (NA_I (El y_aEPf) :* (NA_I (El y_aEPg) :* (NA_I (El y_aEPh) :* (NA_I (El y_aEPi) :* NP0)))))))))
                 -> El
                      (((((((D8 y_aEPc) y_aEPd) y_aEPe) y_aEPf) y_aEPg) y_aEPh) y_aEPi)
               (Rep (Pat3D9 (NA_I (El y_aEPj) :* (NA_I (El y_aEPk) :* (NA_I (El y_aEPl) :* (NA_I (El y_aEPm) :* (NA_I (El y_aEPn) :* (NA_I (El y_aEPo) :* (NA_I (El y_aEPp) :* NP0)))))))))
                 -> El
                      (((((((D9 y_aEPj) y_aEPk) y_aEPl) y_aEPm) y_aEPn) y_aEPo) y_aEPp)
               (Rep (Pat3DA (NA_I (El y_aEPq) :* (NA_I (El y_aEPr) :* (NA_I (El y_aEPs) :* (NA_I (El y_aEPt) :* (NA_I (El y_aEPu) :* (NA_I (El y_aEPv) :* (NA_I (El y_aEPw) :* NP0)))))))))
                 -> El
                      (((((((DA y_aEPq) y_aEPr) y_aEPs) y_aEPt) y_aEPu) y_aEPv) y_aEPw)
               (Rep (Pat3DB (NA_I (El y_aEPx) :* (NA_I (El y_aEPy) :* (NA_I (El y_aEPz) :* (NA_I (El y_aEPA) :* (NA_I (El y_aEPB) :* (NA_I (El y_aEPC) :* (NA_I (El y_aEPD) :* NP0)))))))))
                 -> El
                      (((((((DB y_aEPx) y_aEPy) y_aEPz) y_aEPA) y_aEPB) y_aEPC) y_aEPD)
               (Rep (Pat3DC (NA_I (El y_aEPE) :* (NA_I (El y_aEPF) :* (NA_I (El y_aEPG) :* (NA_I (El y_aEPH) :* (NA_I (El y_aEPI) :* (NA_I (El y_aEPJ) :* (NA_I (El y_aEPK) :* NP0)))))))))
                 -> El
                      (((((((DC y_aEPE) y_aEPF) y_aEPG) y_aEPH) y_aEPI) y_aEPJ) y_aEPK)
               (Rep (Pat3DD (NA_I (El y_aEPL) :* (NA_I (El y_aEPM) :* (NA_I (El y_aEPN) :* (NA_I (El y_aEPO) :* (NA_I (El y_aEPP) :* (NA_I (El y_aEPQ) :* (NA_I (El y_aEPR) :* NP0)))))))))
                 -> El
                      (((((((DD y_aEPL) y_aEPM) y_aEPN) y_aEPO) y_aEPP) y_aEPQ) y_aEPR)
               (Rep (Pat3DE (NA_I (El y_aEPS) :* (NA_I (El y_aEPT) :* (NA_I (El y_aEPU) :* (NA_I (El y_aEPV) :* (NA_I (El y_aEPW) :* (NA_I (El y_aEPX) :* (NA_I (El y_aEPY) :* NP0)))))))))
                 -> El
                      (((((((DE y_aEPS) y_aEPT) y_aEPU) y_aEPV) y_aEPW) y_aEPX) y_aEPY)
               (Rep (Pat3DF (NA_I (El y_aEPZ) :* (NA_I (El y_aEQ0) :* (NA_I (El y_aEQ1) :* (NA_I (El y_aEQ2) :* (NA_I (El y_aEQ3) :* (NA_I (El y_aEQ4) :* (NA_I (El y_aEQ5) :* NP0)))))))))
                 -> El
                      (((((((DF y_aEPZ) y_aEQ0) y_aEQ1) y_aEQ2) y_aEQ3) y_aEQ4) y_aEQ5)
               _ -> error "matchAll"
        IdxE
          -> \case
               (Rep (Pat4E1 (NA_I (El y_aEQ6) :* (NA_I (El y_aEQ7) :* (NA_I (El y_aEQ8) :* (NA_I (El y_aEQ9) :* (NA_I (El y_aEQa) :* (NA_I (El y_aEQb) :* (NA_I (El y_aEQc) :* NP0)))))))))
                 -> El
                      (((((((E1 y_aEQ6) y_aEQ7) y_aEQ8) y_aEQ9) y_aEQa) y_aEQb) y_aEQc)
               (Rep (Pat4E2 (NA_I (El y_aEQd) :* (NA_I (El y_aEQe) :* (NA_I (El y_aEQf) :* (NA_I (El y_aEQg) :* (NA_I (El y_aEQh) :* (NA_I (El y_aEQi) :* (NA_I (El y_aEQj) :* NP0)))))))))
                 -> El
                      (((((((E2 y_aEQd) y_aEQe) y_aEQf) y_aEQg) y_aEQh) y_aEQi) y_aEQj)
               (Rep (Pat4E3 (NA_I (El y_aEQk) :* (NA_I (El y_aEQl) :* (NA_I (El y_aEQm) :* (NA_I (El y_aEQn) :* (NA_I (El y_aEQo) :* (NA_I (El y_aEQp) :* (NA_I (El y_aEQq) :* NP0)))))))))
                 -> El
                      (((((((E3 y_aEQk) y_aEQl) y_aEQm) y_aEQn) y_aEQo) y_aEQp) y_aEQq)
               (Rep (Pat4E4 (NA_I (El y_aEQr) :* (NA_I (El y_aEQs) :* (NA_I (El y_aEQt) :* (NA_I (El y_aEQu) :* (NA_I (El y_aEQv) :* (NA_I (El y_aEQw) :* (NA_I (El y_aEQx) :* NP0)))))))))
                 -> El
                      (((((((E4 y_aEQr) y_aEQs) y_aEQt) y_aEQu) y_aEQv) y_aEQw) y_aEQx)
               (Rep (Pat4E5 (NA_I (El y_aEQy) :* (NA_I (El y_aEQz) :* (NA_I (El y_aEQA) :* (NA_I (El y_aEQB) :* (NA_I (El y_aEQC) :* (NA_I (El y_aEQD) :* (NA_I (El y_aEQE) :* NP0)))))))))
                 -> El
                      (((((((E5 y_aEQy) y_aEQz) y_aEQA) y_aEQB) y_aEQC) y_aEQD) y_aEQE)
               (Rep (Pat4E6 (NA_I (El y_aEQF) :* (NA_I (El y_aEQG) :* (NA_I (El y_aEQH) :* (NA_I (El y_aEQI) :* (NA_I (El y_aEQJ) :* (NA_I (El y_aEQK) :* (NA_I (El y_aEQL) :* NP0)))))))))
                 -> El
                      (((((((E6 y_aEQF) y_aEQG) y_aEQH) y_aEQI) y_aEQJ) y_aEQK) y_aEQL)
               (Rep (Pat4E7 (NA_I (El y_aEQM) :* (NA_I (El y_aEQN) :* (NA_I (El y_aEQO) :* (NA_I (El y_aEQP) :* (NA_I (El y_aEQQ) :* (NA_I (El y_aEQR) :* (NA_I (El y_aEQS) :* NP0)))))))))
                 -> El
                      (((((((E7 y_aEQM) y_aEQN) y_aEQO) y_aEQP) y_aEQQ) y_aEQR) y_aEQS)
               (Rep (Pat4E8 (NA_I (El y_aEQT) :* (NA_I (El y_aEQU) :* (NA_I (El y_aEQV) :* (NA_I (El y_aEQW) :* (NA_I (El y_aEQX) :* (NA_I (El y_aEQY) :* (NA_I (El y_aEQZ) :* NP0)))))))))
                 -> El
                      (((((((E8 y_aEQT) y_aEQU) y_aEQV) y_aEQW) y_aEQX) y_aEQY) y_aEQZ)
               (Rep (Pat4E9 (NA_I (El y_aER0) :* (NA_I (El y_aER1) :* (NA_I (El y_aER2) :* (NA_I (El y_aER3) :* (NA_I (El y_aER4) :* (NA_I (El y_aER5) :* (NA_I (El y_aER6) :* NP0)))))))))
                 -> El
                      (((((((E9 y_aER0) y_aER1) y_aER2) y_aER3) y_aER4) y_aER5) y_aER6)
               (Rep (Pat4EA (NA_I (El y_aER7) :* (NA_I (El y_aER8) :* (NA_I (El y_aER9) :* (NA_I (El y_aERa) :* (NA_I (El y_aERb) :* (NA_I (El y_aERc) :* (NA_I (El y_aERd) :* NP0)))))))))
                 -> El
                      (((((((EA y_aER7) y_aER8) y_aER9) y_aERa) y_aERb) y_aERc) y_aERd)
               (Rep (Pat4EB (NA_I (El y_aERe) :* (NA_I (El y_aERf) :* (NA_I (El y_aERg) :* (NA_I (El y_aERh) :* (NA_I (El y_aERi) :* (NA_I (El y_aERj) :* (NA_I (El y_aERk) :* NP0)))))))))
                 -> El
                      (((((((EB y_aERe) y_aERf) y_aERg) y_aERh) y_aERi) y_aERj) y_aERk)
               (Rep (Pat4EC (NA_I (El y_aERl) :* (NA_I (El y_aERm) :* (NA_I (El y_aERn) :* (NA_I (El y_aERo) :* (NA_I (El y_aERp) :* (NA_I (El y_aERq) :* (NA_I (El y_aERr) :* NP0)))))))))
                 -> El
                      (((((((EC y_aERl) y_aERm) y_aERn) y_aERo) y_aERp) y_aERq) y_aERr)
               (Rep (Pat4ED (NA_I (El y_aERs) :* (NA_I (El y_aERt) :* (NA_I (El y_aERu) :* (NA_I (El y_aERv) :* (NA_I (El y_aERw) :* (NA_I (El y_aERx) :* (NA_I (El y_aERy) :* NP0)))))))))
                 -> El
                      (((((((ED y_aERs) y_aERt) y_aERu) y_aERv) y_aERw) y_aERx) y_aERy)
               (Rep (Pat4EE (NA_I (El y_aERz) :* (NA_I (El y_aERA) :* (NA_I (El y_aERB) :* (NA_I (El y_aERC) :* (NA_I (El y_aERD) :* (NA_I (El y_aERE) :* (NA_I (El y_aERF) :* NP0)))))))))
                 -> El
                      (((((((EE y_aERz) y_aERA) y_aERB) y_aERC) y_aERD) y_aERE) y_aERF)
               (Rep (Pat4EF (NA_I (El y_aERG) :* (NA_I (El y_aERH) :* (NA_I (El y_aERI) :* (NA_I (El y_aERJ) :* (NA_I (El y_aERK) :* (NA_I (El y_aERL) :* (NA_I (El y_aERM) :* NP0)))))))))
                 -> El
                      (((((((EF y_aERG) y_aERH) y_aERI) y_aERJ) y_aERK) y_aERL) y_aERM)
               _ -> error "matchAll"
        IdxF -> \case _ -> error "matchAll"
        IdxG -> \case _ -> error "matchAll"
        _ -> error "matchAll"
