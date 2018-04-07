type Z = Z
type (S Z) = S Z

type FamRoseInt = '[Rose Int, [Rose Int]]
type CodesRoseInt =
    '['['[K KInt, I (S Z)], '[K KInt]], '['[], '[I Z, I (S Z)]]]

pattern SZ = SZ
pattern SS SZ = SS SZ

instance Family Singl FamRoseInt CodesRoseInt where
  sfrom'
    = \case
        \ SZ
          -> \case
               \ (El ((:>:) x_avK9 x_avKa))
                 -> Rep (Here ((NA_K (SInt x_avK9)) :* ((NA_I (El x_avKa)) :* NP0)))
               \ (El (Leaf x_avKb))
                 -> Rep (There (Here ((NA_K (SInt x_avKb)) :* NP0)))
        \ SS SZ
          -> \case
               \ (El ghc-prim-0.5.2.0:GHC.Types.[]) -> Rep (Here NP0)
               \ (El ((ghc-prim-0.5.2.0:GHC.Types.:) x_avKc x_avKd))
                 -> Rep
                      (There (Here ((NA_I (El x_avKc)) :* ((NA_I (El x_avKd)) :* NP0))))
  sto'
    = \case
        \ SZ
          -> \case
               \ (Rep (Here (NA_K (SInt y_avKe) :* (NA_I (El y_avKf) :* NP0))))
                 -> El (((:>:) y_avKe) y_avKf)
               \ (Rep (There (Here (NA_K (SInt y_avKg) :* NP0))))
                 -> El (Leaf y_avKg)
               \ _ -> error "matchAll"
        \ SS SZ
          -> \case
               \ (Rep (Here NP0)) -> El ghc-prim-0.5.2.0:GHC.Types.[]
               \ (Rep (There (Here (NA_I (El y_avKh) :* (NA_I (El y_avKi) :* NP0)))))
                 -> El (((ghc-prim-0.5.2.0:GHC.Types.:) y_avKh) y_avKi)
               \ _ -> error "matchAll"
        \ _ -> error "matchAll"    type Z = Z
type (S Z) = S Z

type FamRoseInt = '[Rose Int, [Rose Int]]
type CodesRoseInt =
    '['['[K KInt, I (S Z)], '[K KInt]], '['[], '[I Z, I (S Z)]]]

pattern SZ = SZ
pattern SS SZ = SS SZ

instance Family Singl FamRoseInt CodesRoseInt where
  sfrom'
    = \case
        \ SZ
          -> \case
               \ (El ((:>:) x_avK9 x_avKa))
                 -> Rep (Here ((NA_K (SInt x_avK9)) :* ((NA_I (El x_avKa)) :* NP0)))
               \ (El (Leaf x_avKb))
                 -> Rep (There (Here ((NA_K (SInt x_avKb)) :* NP0)))
        \ SS SZ
          -> \case
               \ (El ghc-prim-0.5.2.0:GHC.Types.[]) -> Rep (Here NP0)
               \ (El ((ghc-prim-0.5.2.0:GHC.Types.:) x_avKc x_avKd))
                 -> Rep
                      (There (Here ((NA_I (El x_avKc)) :* ((NA_I (El x_avKd)) :* NP0))))
  sto'
    = \case
        \ SZ
          -> \case
               \ (Rep (Here (NA_K (SInt y_avKe) :* (NA_I (El y_avKf) :* NP0))))
                 -> El (((:>:) y_avKe) y_avKf)
               \ (Rep (There (Here (NA_K (SInt y_avKg) :* NP0))))
                 -> El (Leaf y_avKg)
               \ _ -> error "matchAll"
        \ SS SZ
          -> \case
               \ (Rep (Here NP0)) -> El ghc-prim-0.5.2.0:GHC.Types.[]
               \ (Rep (There (Here (NA_I (El y_avKh) :* (NA_I (El y_avKi) :* NP0)))))
                 -> El (((ghc-prim-0.5.2.0:GHC.Types.:) y_avKh) y_avKi)
               \ _ -> error "matchAll"
        \ _ -> error "matchAll"
