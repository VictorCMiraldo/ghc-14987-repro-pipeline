type D0_ = Z
type D1_ = S Z

type FamRoseInt = '[Rose Int, [Rose Int]]

type CodesRoseInt =
    '['['[K KInt, I D1_], '[K KInt]], '['[], '[I D0_, I D1_]]]

pattern IdxRoseInt = SZ
pattern IdxListRoseInt = SS SZ

pattern Pat158 ::
          PoA Singl (El FamRoseInt) '[I D0_, I D1_]
          -> NS (PoA Singl (El FamRoseInt)) '['[], '[I D0_, I D1_]]
pattern Pat158 d_axMo = There (Here d_axMo)

pattern Pat19193 ::
          PoA Singl (El FamRoseInt) '[]
          -> NS (PoA Singl (El FamRoseInt)) '['[], '[I D0_, I D1_]]
pattern Pat19193 d_axMn = Here d_axMn

pattern Pat0Leaf ::
          PoA Singl (El FamRoseInt) '[K KInt]
          -> NS (PoA Singl (El FamRoseInt)) '['[K KInt, I D1_], '[K KInt]]
pattern Pat0Leaf d_axMm = There (Here d_axMm)

pattern Pat0586258 ::
          PoA Singl (El FamRoseInt) '[K KInt, I D1_]
          -> NS (PoA Singl (El FamRoseInt)) '['[K KInt, I D1_], '[K KInt]]
pattern Pat0586258 d_axMl = Here d_axMl

instance Family Singl FamRoseInt CodesRoseInt where
  sfrom'
    = \case
        \ IdxRoseInt
          -> \case
               \ (El ((:>:) x_axMp x_axMq))
                 -> Rep
                      (Pat0586258 ((NA_K (SInt x_axMp)) :* ((NA_I (El x_axMq)) :* NP0)))
                   \ (El (Leaf x_axMr))
                     -> Rep (Pat0Leaf ((NA_K (SInt x_axMr)) :* NP0))
            \ IdxListRoseInt
              -> \case
                   \ (El ghc-prim-0.5.2.0:GHC.Types.[]) -> Rep (Pat19193 NP0)
                   \ (El ((ghc-prim-0.5.2.0:GHC.Types.:) x_axMs x_axMt))
                     -> Rep (Pat158 ((NA_I (El x_axMs)) :* ((NA_I (El x_axMt)) :* NP0)))
      sto'
        = \case
            \ IdxRoseInt
              -> \case
                   \ (Rep (Pat0586258 (NA_K (SInt y_axMu) :* (NA_I (El y_axMv) :* NP0))))
                     -> El (((:>:) y_axMu) y_axMv)
                   \ (Rep (Pat0Leaf (NA_K (SInt y_axMw) :* NP0))) -> El (Leaf y_axMw)
                   \ _ -> error "matchAll"
            \ IdxListRoseInt
              -> \case
                   \ (Rep (Pat19193 NP0)) -> El ghc-prim-0.5.2.0:GHC.Types.[]
                   \ (Rep (Pat158 (NA_I (El y_axMx) :* (NA_I (El y_axMy) :* NP0))))
                     -> El (((ghc-prim-0.5.2.0:GHC.Types.:) y_axMx) y_axMy)
                   \ _ -> error "matchAll"
            \ _ -> error "matchAll"
