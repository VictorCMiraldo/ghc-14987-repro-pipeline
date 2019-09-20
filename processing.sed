1,3d
s/^    //
/tyInfo/,+1d
s/There/T/g
s/Here/H/g
s/\\ //g
s/\['/\[ '/g
s/ghc-prim-.*:GHC\.Types\.//g
s/sop-core-.\..\..\..:Data.SOP.NS.Z/H/g
s/sop-core-.\..\..\..:Data.SOP.NS.S/T/g
s/Nil/NP0/g
s/SGo/S/g
s/GoSingl/Singl/g
s/'Go/'K/g
/instance HasDatatypeInfo/,$d
