ype D0_ = Z
type D1_ = S Z

type FamRoseInt = '[Rose Int, [Rose Int]]
type CodesRoseInt =
    '['['[K KInt, I D1_], '[K KInt]], '['[], '[I D0_, I D1_]]]

pattern IdxRoseInt = SZ
pattern IdxListRoseInt = SS SZ

pattern HT0_0_ d_awsz = Here d_awsz
pattern HT0_1_ d_awsA = There (Here d_awsA)

pattern HT1_0_ d_awsC = Here d_awsC
pattern HT1_1_ d_awsD = There (Here d_awsD)

instance Family Singl FamRoseInt CodesRoseInt where
  sfrom'
    = \case
        \ IdxRoseInt
          -> \case
               \ (El ((:>:) x_awsF x_awsG))
                 -> Rep
                      (HT0_0_ ((NA_K (SInt x_awsF)) :* ((NA_I (El x_awsG)) :* NP0)))
               \ (El (Leaf x_awsH)) -> Rep (HT0_1_ ((NA_K (SInt x_awsH)) :* NP0))
        \ IdxListRoseInt
          -> \case
               \ (El ghc-prim-0.5.2.0:GHC.Types.[]) -> Rep (HT1_0_ NP0)
               \ (El ((ghc-prim-0.5.2.0:GHC.Types.:) x_awsI x_awsJ))
                 -> Rep (HT1_1_ ((NA_I (El x_awsI)) :* ((NA_I (El x_awsJ)) :* NP0)))
  sto'
    = \case
        \ IdxRoseInt
          -> \case
               \ (Rep (HT0_0_ (NA_K (SInt y_awsK) :* (NA_I (El y_awsL) :* NP0))))
                 -> El (((:>:) y_awsK) y_awsL)
               \ (Rep (HT0_1_ (NA_K (SInt y_awsM) :* NP0))) -> El (Leaf y_awsM)
               \ _ -> error "matchAll"
        \ IdxListRoseInt
          -> \case
               \ (Rep (HT1_0_ NP0)) -> El ghc-prim-0.5.2.0:GHC.Types.[]
               \ (Rep (HT1_1_ (NA_I (El y_awsN) :* (NA_I (El y_awsO) :* NP0))))
                 -> El (((ghc-prim-0.5.2.0:GHC.Types.:) y_awsN) y_awsO)
               \ _ -> error "matchAll"
        \ _ -> error "matchAll"