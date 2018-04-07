type D0_ = Z
type D1_ = S Z

type FamRoseInt = '[Rose Int, [Rose Int]]
type CodesRoseInt =
    '['['[K KInt, I D1_], '[K KInt]], '['[], '[I D0_, I D1_]]]

pattern IdxRoseInt = SZ
pattern IdxListRoseInt = SS SZ

instance Family Singl FamRoseInt CodesRoseInt where
  sfrom'
    = \case
        \ IdxRoseInt
          -> \case
               \ (El ((:>:) x_avK9 x_avKa))
                 -> Rep (Here ((NA_K (SInt x_avK9)) :* ((NA_I (El x_avKa)) :* NP0)))
               \ (El (Leaf x_avKb))
                 -> Rep (There (Here ((NA_K (SInt x_avKb)) :* NP0)))
        \ IdxListRoseInt
          -> \case
               \ (El ghc-prim-0.5.2.0:GHC.Types.[]) -> Rep (Here NP0)
               \ (El ((ghc-prim-0.5.2.0:GHC.Types.:) x_avKc x_avKd))
                 -> Rep
                      (There (Here ((NA_I (El x_avKc)) :* ((NA_I (El x_avKd)) :* NP0))))
  sto'
    = \case
        \ IdxRoseInt
          -> \case
               \ (Rep (Here (NA_K (SInt y_avKe) :* (NA_I (El y_avKf) :* NP0))))
                 -> El (((:>:) y_avKe) y_avKf)
               \ (Rep (There (Here (NA_K (SInt y_avKg) :* NP0))))
                 -> El (Leaf y_avKg)
               \ _ -> error "matchAll"
        \ IdxListRoseInt
          -> \case
               \ (Rep (Here NP0)) -> El ghc-prim-0.5.2.0:GHC.Types.[]
               \ (Rep (There (Here (NA_I (El y_avKh) :* (NA_I (El y_avKi) :* NP0)))))
                 -> El (((ghc-prim-0.5.2.0:GHC.Types.:) y_avKh) y_avKi)
               \ _ -> error "matchAll"
        \ _ -> error "matchAll"    type D0_ = Z
type D1_ = S Z

type FamRoseInt = '[Rose Int, [Rose Int]]
type CodesRoseInt =
    '['['[K KInt, I D1_], '[K KInt]], '['[], '[I D0_, I D1_]]]

pattern IdxRoseInt = SZ
pattern IdxListRoseInt = SS SZ

instance Family Singl FamRoseInt CodesRoseInt where
  sfrom'
    = \case
        \ IdxRoseInt
          -> \case
               \ (El ((:>:) x_avK9 x_avKa))
                 -> Rep (Here ((NA_K (SInt x_avK9)) :* ((NA_I (El x_avKa)) :* NP0)))
               \ (El (Leaf x_avKb))
                 -> Rep (There (Here ((NA_K (SInt x_avKb)) :* NP0)))
        \ IdxListRoseInt
          -> \case
               \ (El ghc-prim-0.5.2.0:GHC.Types.[]) -> Rep (Here NP0)
               \ (El ((ghc-prim-0.5.2.0:GHC.Types.:) x_avKc x_avKd))
                 -> Rep
                      (There (Here ((NA_I (El x_avKc)) :* ((NA_I (El x_avKd)) :* NP0))))
  sto'
    = \case
        \ IdxRoseInt
          -> \case
               \ (Rep (Here (NA_K (SInt y_avKe) :* (NA_I (El y_avKf) :* NP0))))
                 -> El (((:>:) y_avKe) y_avKf)
               \ (Rep (There (Here (NA_K (SInt y_avKg) :* NP0))))
                 -> El (Leaf y_avKg)
               \ _ -> error "matchAll"
        \ IdxListRoseInt
          -> \case
               \ (Rep (Here NP0)) -> El ghc-prim-0.5.2.0:GHC.Types.[]
               \ (Rep (There (Here (NA_I (El y_avKh) :* (NA_I (El y_avKi) :* NP0)))))
                 -> El (((ghc-prim-0.5.2.0:GHC.Types.:) y_avKh) y_avKi)
               \ _ -> error "matchAll"
        \ _ -> error "matchAll"
