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



-- | Go Language source start
data GoSource = GoSource {
      getPackage      :: GoId,
      getTopLevelPrel :: [GoPrel],
      getTopLevelDecl :: [GoDecl]}
        deriving (Eq , Read , Show)

data GoPrel = GoImportDecl [GoImpSpec]
            | GoPragma String
            | GoDefine
            | GoIfPrel
                deriving (Eq, Read, Show)

data GoDecl = GoConst [GoCVSpec]
            | GoType  [GoTypeSpec]
            | GoVar   [GoCVSpec]
            | GoFunc   GoFuncDecl
            | GoMeth   GoMethDecl
                deriving (Eq, Read, Show)

data GoImpSpec = GoImpSpec GoImpType String
                deriving (Eq, Read, Show)

data GoImpType = GoImp
               | GoImpDot  GoOp
               | GoImpQual GoId
                deriving (Eq, Read, Show)

data GoCVSpec = GoCVSpec [GoId] (Maybe GoType) [GoExpr]
                deriving (Eq, Read, Show)

data GoTypeSpec  = GoTypeSpec GoId GoType
                deriving (Eq, Read, Show)

data GoFuncExpr  = GoFuncExpr            GoSig GoBlock
                deriving (Eq, Read, Show)

data GoFuncDecl  = GoFuncDecl       GoId GoSig GoBlock
                deriving (Eq, Read, Show)

data GoMethDecl  = GoMethDecl GoRec GoId GoSig GoBlock
                deriving (Eq, Read, Show)

data GoMethSpec  = GoMethSpec       GoId GoSig
                 | GoInterface      GoId
                deriving (Eq, Read, Show)

-- GoId (= 'identifier')
data GoId = GoId String
                deriving (Eq, Read, Show)

-- GoOp (= 'unary_op' = 'binary_op')
data GoOp = GoOp String
                deriving (Eq, Read, Show)

-- GoRec (= 'Receiver' = 'ReceiverType')
data GoRec = GoRec Bool (Maybe GoId) GoType
                deriving (Eq, Read, Show)

-- GoSig (= 'Signature')
data GoSig = GoSig [GoParam] [GoParam]
                deriving (Eq, Read, Show)

-- GoParam (= 'Parameters')
data GoParam = GoParam [GoId] GoType
                deriving (Eq, Read, Show)

-- GoType (= 'Type' = 'TypeLit' = 'LiteralType')
data GoType = GoTypeName [GoId] GoId
            | GoArrayType GoExpr GoType
            | GoChannelType GoChanKind GoType  -- only in Decls
            | GoElipsisType GoType  -- only in Literals
            | GoFunctionType GoSig
            | GoInterfaceType [GoMethSpec] -- only in Decls
            | GoMapType GoType GoType
            | GoPointerType GoType   -- only in Decls
            | GoSliceType GoType
            | GoStructType [GoFieldType]
                deriving (Eq, Read, Show)


--data GoChannelKind = GoIChan
--                   | GoOChan
--                   | GoIOChan

data GoChanKind = GoIChan  -- 1
                | GoOChan  -- 2
                | GoIOChan -- 3
                deriving (Eq, Read, Show)

-- GoFieldType
data GoFieldType = GoFieldType { 
      getFieldTag  :: String, 
      getFieldId   :: [GoId], 
      getFieldType :: GoType }
                 | GoFieldAnon { 
      getFieldTag  :: String, 
      getFieldPtr  :: Bool,
      getFieldType :: GoType } -- MUST be typename
                deriving (Eq, Read, Show)

{-  In the phrases below the symbol / means "is the only production which uses"
In the phrases below the symbol - means "is NOT the only production which uses"
InterfaceType 

PrimaryExpr/Operand
PrimaryExpr/Conversion
PrimaryExpr/BuiltinCall
PrimaryExpr/Selector
PrimaryExpr/Index
PrimaryExpr/Slice
PrimaryExpr/TypeAssertion
PrimaryExpr/Call/ArgumentList

LiteralType - ArrayType
FunctionType - Signature
FunctionDecl - Signature
MethodSpec - Signature
MethodDecl - Signature
-}

-- GoExpr (= 'Expression')
data GoExpr = GoPrim GoPrim           -- 'PrimaryExpr'
            | Go1Op GoOp GoExpr       -- 'Expression/UnaryExpr[2]'
            | Go2Op GoOp GoExpr GoExpr -- 'Expression[2]'
              deriving (Eq, Read, Show)

-- GoPrimExpr (= 'PrimaryExpr')
data GoPrim = GoLiteral GoLit         -- 'PrimaryExpr/Operand/Literal'
            | GoQual  [GoId] GoId     -- 'PrimaryExpr/Operand/QualifiedIdent'
            | GoMethod GoRec GoId     -- 'PrimaryExpr/Operand/MethodExpr'
            | GoParen GoExpr          -- 'PrimaryExpr/Operand/MethodExpr'
            | GoCast GoType GoExpr    -- 'PrimaryExpr/Conversion'
            | GoNew  GoType           -- 'PrimaryExpr/BuiltinCall/new'
            | GoMake GoType [GoExpr]  -- 'PrimaryExpr/BuiltinCall/make'
--            | GoBI GoId GoType [GoExpr]  -- 'PrimaryExpr/BuiltinCall'
            | GoSelect GoPrim GoId    -- 'PrimaryExpr/Selector'
            | GoIndex GoPrim GoExpr   -- 'PrimaryExpr/Index'
            | GoSlice GoPrim [GoExpr] -- 'PrimaryExpr/Slice'
            | GoTA    GoPrim GoType   -- 'PrimaryExpr/TypeAssertion'
            | GoCall  GoPrim [GoExpr] Bool -- 'PrimaryExpr/Call'
              deriving (Eq, Read, Show)

-- TODO merge Lit with Prim
-- GoLit (= 'Literal') is only used in one place, operands
data GoLit = GoLitInt  String Integer -- 'Literal/BasicLit/int_lit'
           | GoLitReal String Float   -- 'Literal/BasicLit/float_lit'
           | GoLitImag String Float   -- 'Literal/BasicLit/imaginary_lit'
           | GoLitChar String Char    -- 'Literal/BasicLit/char_lit'
           | GoLitStr  String String  -- 'Literal/BasicLit/string_lit'
           | GoLitComp GoType GoComp  -- 'Literal/CompositeLit'
           | GoLitFunc GoFuncExpr     -- 'Literal/FunctionLit'
             deriving (Eq, Read, Show)

-- GoComp (= 'CompositeLit/LiteralValue') is used in 2 places
data GoComp = GoComp [GoElement]
              deriving (Eq, Read, Show)

data GoElement = GoElement GoKey GoValue
                deriving (Eq, Read, Show)

data GoKey = GoKeyNone
           | GoKeyField GoId
           | GoKeyIndex GoExpr
                deriving (Eq, Read, Show)

data GoValue = GoValueExpr GoExpr -- 'Value/Expression'
             | GoValueComp GoComp -- 'Value/LiteralValue'
                deriving (Eq, Read, Show)

data GoBlock = GoBlock { getStmt::[GoStmt] }
             | GoNoBlock
                deriving (Eq, Read, Show)

data GoForClause = GoForWhile GoExpr
                 | GoForThree GoSimp (Maybe GoExpr) GoSimp
                 | GoForRange [GoExpr] GoExpr
                deriving (Eq, Read, Show)

data GoStmt = GoStmtDecl GoDecl -- 'Statement/Declaration'
            | GoStmtLabeled GoId GoStmt
            | GoStmtSimple GoSimp
            | GoStmtGo GoExpr
            | GoStmtReturn [GoExpr]
            | GoStmtBreak    (Maybe GoId)
            | GoStmtContinue (Maybe GoId)
            | GoStmtGoto GoId
            | GoStmtFallthrough
            | GoStmtBlock GoBlock
            | GoStmtIf GoCond GoBlock (Maybe GoStmt)
            | GoStmtSelect            [GoCase GoChan]
            | GoStmtSwitch     GoCond [GoCase GoExpr]
            | GoStmtTypeSwitch GoCond [GoCase GoType] (Maybe GoId)
            | GoStmtFor GoForClause GoBlock
            | GoStmtDefer GoExpr
              deriving (Eq, Read, Show)

data GoSimp = GoSimpEmpty
            | GoSimpRecv GoExpr        -- SelectStmt/RecvStmt
            | GoSimpSend GoExpr GoExpr -- SimpleStmt/SendStmt
            | GoSimpExpr GoExpr        -- SimpleStmt/ExpressionStmt
            | GoSimpInc  GoExpr        -- SimpleStmt/IncDecStmt[1]
            | GoSimpDec  GoExpr        -- SimpleStmt/IncDecStmt[2]
            | GoSimpAsn [GoExpr] GoOp [GoExpr] -- Assignment
            | GoSimpVar [GoId] [GoExpr]      -- ShortVarDecl
              deriving (Eq, Read, Show)

data GoChanInner = GoChanInner GoExpr GoOp
  deriving (Eq, Read , Show)

data GoChan = GoChanRecv (Maybe GoChanInner) GoExpr
            | GoChanSend GoExpr GoExpr
              deriving (Eq, Read, Show)

data GoCond = GoCond (Maybe GoSimp) (Maybe GoExpr)
              deriving (Eq, Read, Show)
data GoCase a = GoCase [a] [GoStmt]
              | GoDefault  [GoStmt]
                deriving (Eq, Read, Show)

type D0_ = Z
type D1_ = S Z
type D2_ = S (S Z)
type D3_ = S (S (S Z))
type D4_ = S (S (S (S Z)))
type D5_ = S (S (S (S (S Z))))
type D6_ = S (S (S (S (S (S Z)))))
type D7_ = S (S (S (S (S (S (S Z))))))
type D8_ = S (S (S (S (S (S (S (S Z)))))))
type D9_ = S (S (S (S (S (S (S (S (S Z))))))))
type D10_ = S (S (S (S (S (S (S (S (S (S Z)))))))))
type D11_ = S (S (S (S (S (S (S (S (S (S (S Z))))))))))
type D12_ = S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))
type D13_ = S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))
type D14_ = S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))
type D15_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))
type D16_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))
type D17_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))
type D18_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))
type D19_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))
type D20_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))
type D21_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))
type D22_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))
type D23_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))
type D24_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))
type D25_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))
type D26_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))
type D27_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))
type D28_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))
type D29_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))
type D30_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))
type D31_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))
type D32_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))
type D33_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))
type D34_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))
type D35_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))
type D36_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))
type D37_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))
type D38_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))
type D39_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))
type D40_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))
type D41_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))
type D42_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))
type D43_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))
type D44_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))
type D45_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))
type D46_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))
type D47_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))
type D48_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))
type D49_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))))
type D50_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))))
type D51_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))))))
type D52_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))))))
type D53_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))))))))
type D54_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))))))))
type D55_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))))))))))
type D56_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))
type D57_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z))))))))))))))))))))))))))))))))))))))))))))))))))))))))
type D58_ =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
type FamGoSource =
    '[GoSource,
      GoId,
      [GoPrel],
      [GoDecl],
      GoPrel,
      [GoImpSpec],
      GoImpSpec,
      GoImpType,
      GoOp,
      GoDecl,
      [GoCVSpec],
      [GoTypeSpec],
      GoFuncDecl,
      GoMethDecl,
      GoCVSpec,
      [GoId],
      Maybe GoType,
      [GoExpr],
      GoType,
      GoExpr,
      GoChanKind,
      GoSig,
      [GoMethSpec],
      [GoFieldType],
      GoPrim,
      GoLit,
      GoRec,
      GoComp,
      GoFuncExpr,
      [GoElement],
      GoElement,
      GoKey,
      GoValue,
      GoBlock,
      [GoParam],
      GoParam,
      [GoStmt],
      GoStmt,
      GoSimp,
      Maybe GoId,
      GoCond,
      Maybe GoStmt,
      [GoCase GoChan],
      [GoCase GoExpr],
      [GoCase GoType],
      GoForClause,
      Maybe GoSimp,
      Maybe GoExpr,
      GoCase GoChan,
      [GoChan],
      GoChan,
      Maybe GoChanInner,
      GoChanInner,
      GoCase GoExpr,
      GoCase GoType,
      [GoType],
      GoMethSpec,
      GoFieldType,
      GoTypeSpec]
type CodesGoSource =
    '[ '[ '[I D1_, I D2_, I D3_]],
      '[ '[K KString]],
      '[ '[], '[I D4_, I D2_]],
      '[ '[], '[I D9_, I D3_]],
      '[ '[I D5_], '[K KString], '[], '[]],
      '[ '[], '[I D6_, I D5_]],
      '[ '[I D7_, K KString]],
      '[ '[], '[I D8_], '[I D1_]],
      '[ '[K KString]],
      '[ '[I D10_], '[I D11_], '[I D10_], '[I D12_], '[I D13_]],
      '[ '[], '[I D14_, I D10_]],
      '[ '[], '[I D58_, I D11_]],
      '[ '[I D1_, I D21_, I D33_]],
      '[ '[I D26_, I D1_, I D21_, I D33_]],
      '[ '[I D15_, I D16_, I D17_]],
      '[ '[], '[I D1_, I D15_]],
      '[ '[], '[I D18_]],
      '[ '[], '[I D19_, I D17_]],
      '[ '[I D15_, I D1_],
        '[I D19_, I D18_],
        '[I D20_, I D18_],
        '[I D18_],
        '[I D21_],
        '[I D22_],
        '[I D18_, I D18_],
        '[I D18_],
        '[I D18_],
        '[I D23_]],
      '[ '[I D24_], '[I D8_, I D19_], '[I D8_, I D19_, I D19_]],
      '[ '[], '[], '[]],
      '[ '[I D34_, I D34_]],
      '[ '[], '[I D56_, I D22_]],
      '[ '[], '[I D57_, I D23_]],
      '[ '[I D25_],
        '[I D15_, I D1_],
        '[I D26_, I D1_],
        '[I D19_],
        '[I D18_, I D19_],
        '[I D18_],
        '[I D18_, I D17_],
        '[I D24_, I D1_],
        '[I D24_, I D19_],
        '[I D24_, I D17_],
        '[I D24_, I D18_],
        '[I D24_, I D17_, K KBool]],
      '[ '[K KString, K KInteger],
        '[K KString, K KFloat],
        '[K KString, K KFloat],
        '[K KString, K KChar],
        '[K KString, K KString],
        '[I D18_, I D27_],
        '[I D28_]],
      '[ '[K KBool, I D39_, I D18_]],
      '[ '[I D29_]],
      '[ '[I D21_, I D33_]],
      '[ '[], '[I D30_, I D29_]],
      '[ '[I D31_, I D32_]],
      '[ '[], '[I D1_], '[I D19_]],
      '[ '[I D19_], '[I D27_]],
      '[ '[I D36_], '[]],
      '[ '[], '[I D35_, I D34_]],
      '[ '[I D15_, I D18_]],
      '[ '[], '[I D37_, I D36_]],
      '[ '[I D9_],
        '[I D1_, I D37_],
        '[I D38_],
        '[I D19_],
        '[I D17_],
        '[I D39_],
        '[I D39_],
        '[I D1_],
        '[],
        '[I D33_],
        '[I D40_, I D33_, I D41_],
        '[I D42_],
        '[I D40_, I D43_],
        '[I D40_, I D44_, I D39_],
        '[I D45_, I D33_],
        '[I D19_]],
      '[ '[],
        '[I D19_],
        '[I D19_, I D19_],
        '[I D19_],
        '[I D19_],
        '[I D19_],
        '[I D17_, I D8_, I D17_],
        '[I D15_, I D17_]],
      '[ '[], '[I D1_]],
      '[ '[I D46_, I D47_]],
      '[ '[], '[I D37_]],
      '[ '[], '[I D48_, I D42_]],
      '[ '[], '[I D53_, I D43_]],
      '[ '[], '[I D54_, I D44_]],
      '[ '[I D19_], '[I D38_, I D47_, I D38_], '[I D17_, I D19_]],
      '[ '[], '[I D38_]],
      '[ '[], '[I D19_]],
      '[ '[I D49_, I D36_], '[I D36_]],
      '[ '[], '[I D50_, I D49_]],
      '[ '[I D51_, I D19_], '[I D19_, I D19_]],
      '[ '[], '[I D52_]],
      '[ '[I D19_, I D8_]],
      '[ '[I D17_, I D36_], '[I D36_]],
      '[ '[I D55_, I D36_], '[I D36_]],
      '[ '[], '[I D18_, I D55_]],
      '[ '[I D1_, I D21_], '[I D1_]],
      '[ '[K KString, I D15_, I D18_], '[K KString, K KBool, I D18_]],
      '[ '[I D1_, I D18_]]]
pattern IdxGoSource = SZ
pattern IdxGoId = SS SZ
pattern IdxListGoPrel = SS (SS SZ)
pattern IdxListGoDecl = SS (SS (SS SZ))
pattern IdxGoPrel = SS (SS (SS (SS SZ)))
pattern IdxListGoImpSpec = SS (SS (SS (SS (SS SZ))))
pattern IdxGoImpSpec = SS (SS (SS (SS (SS (SS SZ)))))
pattern IdxGoImpType = SS (SS (SS (SS (SS (SS (SS SZ))))))
pattern IdxGoOp = SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))
pattern IdxGoDecl = SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))
pattern IdxListGoCVSpec = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))
pattern IdxListGoTypeSpec = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))
pattern IdxGoFuncDecl = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))
pattern IdxGoMethDecl = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))
pattern IdxGoCVSpec = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))
pattern IdxListGoId = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))
pattern IdxMaybeGoType = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))
pattern IdxListGoExpr = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))
pattern IdxGoType = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))
pattern IdxGoExpr = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))
pattern IdxGoChanKind = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))
pattern IdxGoSig = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))
pattern IdxListGoMethSpec = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))
pattern IdxListGoFieldType = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))
pattern IdxGoPrim = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))
pattern IdxGoLit = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))
pattern IdxGoRec = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))
pattern IdxGoComp = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))
pattern IdxGoFuncExpr = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))
pattern IdxListGoElement = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))
pattern IdxGoElement = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))
pattern IdxGoKey = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))
pattern IdxGoValue = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))
pattern IdxGoBlock = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))
pattern IdxListGoParam = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))
pattern IdxGoParam = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))
pattern IdxListGoStmt = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))
pattern IdxGoStmt = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))
pattern IdxGoSimp = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))
pattern IdxMaybeGoId = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))
pattern IdxGoCond = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))
pattern IdxMaybeGoStmt = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))
pattern IdxListGoCaseGoChan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))
pattern IdxListGoCaseGoExpr = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))
pattern IdxListGoCaseGoType = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoForClause = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))
pattern IdxMaybeGoSimp = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))
pattern IdxMaybeGoExpr = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoCaseGoChan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxListGoChan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoChan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxMaybeGoChanInner = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoChanInner = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoCaseGoExpr = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoCaseGoType = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxListGoType = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoMethSpec = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoFieldType = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoTypeSpec = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern Pat58GoTypeSpec d_abTp = H d_abTp
pattern Pat57GoFieldAnon d_abTo = T (H d_abTo)
pattern Pat57GoFieldType d_abTn = H d_abTn
pattern Pat56GoInterface d_abTm = T (H d_abTm)
pattern Pat56GoMethSpec d_abTl = H d_abTl
pattern Pat5558 d_abTk = T (H d_abTk)
pattern Pat559193 d_abTj = H d_abTj
pattern Pat54GoDefault d_abTi = T (H d_abTi)
pattern Pat54GoCase d_abTh = H d_abTh
pattern Pat53GoDefault d_abTg = T (H d_abTg)
pattern Pat53GoCase d_abTf = H d_abTf
pattern Pat52GoChanInner d_abTe = H d_abTe
pattern Pat51Just d_abTd = T (H d_abTd)
pattern Pat51Nothing d_abTc = H d_abTc
pattern Pat50GoChanSend d_abTb = T (H d_abTb)
pattern Pat50GoChanRecv d_abTa = H d_abTa
pattern Pat4958 d_abT9 = T (H d_abT9)
pattern Pat499193 d_abT8 = H d_abT8
pattern Pat48GoDefault d_abT7 = T (H d_abT7)
pattern Pat48GoCase d_abT6 = H d_abT6
pattern Pat47Just d_abT5 = T (H d_abT5)
pattern Pat47Nothing d_abT4 = H d_abT4
pattern Pat46Just d_abT3 = T (H d_abT3)
pattern Pat46Nothing d_abT2 = H d_abT2
pattern Pat45GoForRange d_abT1 = T (T (H d_abT1))
pattern Pat45GoForThree d_abT0 = T (H d_abT0)
pattern Pat45GoForWhile d_abSZ = H d_abSZ
pattern Pat4458 d_abSY = T (H d_abSY)
pattern Pat449193 d_abSX = H d_abSX
pattern Pat4358 d_abSW = T (H d_abSW)
pattern Pat439193 d_abSV = H d_abSV
pattern Pat4258 d_abSU = T (H d_abSU)
pattern Pat429193 d_abST = H d_abST
pattern Pat41Just d_abSS = T (H d_abSS)
pattern Pat41Nothing d_abSR = H d_abSR
pattern Pat40GoCond d_abSQ = H d_abSQ
pattern Pat39Just d_abSP = T (H d_abSP)
pattern Pat39Nothing d_abSO = H d_abSO
pattern Pat38GoSimpVar d_abSN = T (T (T (T (T (T (T (H d_abSN)))))))
pattern Pat38GoSimpAsn d_abSM = T (T (T (T (T (T (H d_abSM))))))
pattern Pat38GoSimpDec d_abSL = T (T (T (T (T (H d_abSL)))))
pattern Pat38GoSimpInc d_abSK = T (T (T (T (H d_abSK))))
pattern Pat38GoSimpExpr d_abSJ = T (T (T (H d_abSJ)))
pattern Pat38GoSimpSend d_abSI = T (T (H d_abSI))
pattern Pat38GoSimpRecv d_abSH = T (H d_abSH)
pattern Pat38GoSimpEmpty d_abSG = H d_abSG
pattern Pat37GoStmtDefer d_abSF = T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_abSF)))))))))))))))
pattern Pat37GoStmtFor d_abSE = T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_abSE))))))))))))))
pattern Pat37GoStmtTypeSwitch d_abSD = T (T (T (T (T (T (T (T (T (T (T (T (T (H d_abSD)))))))))))))
pattern Pat37GoStmtSwitch d_abSC = T (T (T (T (T (T (T (T (T (T (T (T (H d_abSC))))))))))))
pattern Pat37GoStmtSelect d_abSB = T (T (T (T (T (T (T (T (T (T (T (H d_abSB)))))))))))
pattern Pat37GoStmtIf d_abSA = T (T (T (T (T (T (T (T (T (T (H d_abSA))))))))))
pattern Pat37GoStmtBlock d_abSz = T (T (T (T (T (T (T (T (T (H d_abSz)))))))))
pattern Pat37GoStmtFallthrough d_abSy = T (T (T (T (T (T (T (T (H d_abSy))))))))
pattern Pat37GoStmtGoto d_abSx = T (T (T (T (T (T (T (H d_abSx)))))))
pattern Pat37GoStmtContinue d_abSw = T (T (T (T (T (T (H d_abSw))))))
pattern Pat37GoStmtBreak d_abSv = T (T (T (T (T (H d_abSv)))))
pattern Pat37GoStmtReturn d_abSu = T (T (T (T (H d_abSu))))
pattern Pat37GoStmtGo d_abSt = T (T (T (H d_abSt)))
pattern Pat37GoStmtSimple d_abSs = T (T (H d_abSs))
pattern Pat37GoStmtLabeled d_abSr = T (H d_abSr)
pattern Pat37GoStmtDecl d_abSq = H d_abSq
pattern Pat3658 d_abSp = T (H d_abSp)
pattern Pat369193 d_abSo = H d_abSo
pattern Pat35GoParam d_abSn = H d_abSn
pattern Pat3458 d_abSm = T (H d_abSm)
pattern Pat349193 d_abSl = H d_abSl
pattern Pat33GoNoBlock d_abSk = T (H d_abSk)
pattern Pat33GoBlock d_abSj = H d_abSj
pattern Pat32GoValueComp d_abSi = T (H d_abSi)
pattern Pat32GoValueExpr d_abSh = H d_abSh
pattern Pat31GoKeyIndex d_abSg = T (T (H d_abSg))
pattern Pat31GoKeyField d_abSf = T (H d_abSf)
pattern Pat31GoKeyNone d_abSe = H d_abSe
pattern Pat30GoElement d_abSd = H d_abSd
pattern Pat2958 d_abSc = T (H d_abSc)
pattern Pat299193 d_abSb = H d_abSb
pattern Pat28GoFuncExpr d_abSa = H d_abSa
pattern Pat27GoComp d_abS9 = H d_abS9
pattern Pat26GoRec d_abS8 = H d_abS8
pattern Pat25GoLitFunc d_abS7 = T (T (T (T (T (T (H d_abS7))))))
pattern Pat25GoLitComp d_abS6 = T (T (T (T (T (H d_abS6)))))
pattern Pat25GoLitStr d_abS5 = T (T (T (T (H d_abS5))))
pattern Pat25GoLitChar d_abS4 = T (T (T (H d_abS4)))
pattern Pat25GoLitImag d_abS3 = T (T (H d_abS3))
pattern Pat25GoLitReal d_abS2 = T (H d_abS2)
pattern Pat25GoLitInt d_abS1 = H d_abS1
pattern Pat24GoCall d_abS0 = T (T (T (T (T (T (T (T (T (T (T (H d_abS0)))))))))))
pattern Pat24GoTA d_abRZ = T (T (T (T (T (T (T (T (T (T (H d_abRZ))))))))))
pattern Pat24GoSlice d_abRY = T (T (T (T (T (T (T (T (T (H d_abRY)))))))))
pattern Pat24GoIndex d_abRX = T (T (T (T (T (T (T (T (H d_abRX))))))))
pattern Pat24GoSelect d_abRW = T (T (T (T (T (T (T (H d_abRW)))))))
pattern Pat24GoMake d_abRV = T (T (T (T (T (T (H d_abRV))))))
pattern Pat24GoNew d_abRU = T (T (T (T (T (H d_abRU)))))
pattern Pat24GoCast d_abRT = T (T (T (T (H d_abRT))))
pattern Pat24GoParen d_abRS = T (T (T (H d_abRS)))
pattern Pat24GoMethod d_abRR = T (T (H d_abRR))
pattern Pat24GoQual d_abRQ = T (H d_abRQ)
pattern Pat24GoLiteral d_abRP = H d_abRP
pattern Pat2358 d_abRO = T (H d_abRO)
pattern Pat239193 d_abRN = H d_abRN
pattern Pat2258 d_abRM = T (H d_abRM)
pattern Pat229193 d_abRL = H d_abRL
pattern Pat21GoSig d_abRK = H d_abRK
pattern Pat20GoIOChan d_abRJ = T (T (H d_abRJ))
pattern Pat20GoOChan d_abRI = T (H d_abRI)
pattern Pat20GoIChan d_abRH = H d_abRH
pattern Pat19Go2Op d_abRG = T (T (H d_abRG))
pattern Pat19Go1Op d_abRF = T (H d_abRF)
pattern Pat19GoPrim d_abRE = H d_abRE
pattern Pat18GoStructType d_abRD = T (T (T (T (T (T (T (T (T (H d_abRD)))))))))
pattern Pat18GoSliceType d_abRC = T (T (T (T (T (T (T (T (H d_abRC))))))))
pattern Pat18GoPointerType d_abRB = T (T (T (T (T (T (T (H d_abRB)))))))
pattern Pat18GoMapType d_abRA = T (T (T (T (T (T (H d_abRA))))))
pattern Pat18GoInterfaceType d_abRz = T (T (T (T (T (H d_abRz)))))
pattern Pat18GoFunctionType d_abRy = T (T (T (T (H d_abRy))))
pattern Pat18GoElipsisType d_abRx = T (T (T (H d_abRx)))
pattern Pat18GoChannelType d_abRw = T (T (H d_abRw))
pattern Pat18GoArrayType d_abRv = T (H d_abRv)
pattern Pat18GoTypeName d_abRu = H d_abRu
pattern Pat1758 d_abRt = T (H d_abRt)
pattern Pat179193 d_abRs = H d_abRs
pattern Pat16Just d_abRr = T (H d_abRr)
pattern Pat16Nothing d_abRq = H d_abRq
pattern Pat1558 d_abRp = T (H d_abRp)
pattern Pat159193 d_abRo = H d_abRo
pattern Pat14GoCVSpec d_abRn = H d_abRn
pattern Pat13GoMethDecl d_abRm = H d_abRm
pattern Pat12GoFuncDecl d_abRl = H d_abRl
pattern Pat1158 d_abRk = T (H d_abRk)
pattern Pat119193 d_abRj = H d_abRj
pattern Pat1058 d_abRi = T (H d_abRi)
pattern Pat109193 d_abRh = H d_abRh
pattern Pat9GoMeth d_abRg = T (T (T (T (H d_abRg))))
pattern Pat9GoFunc d_abRf = T (T (T (H d_abRf)))
pattern Pat9GoVar d_abRe = T (T (H d_abRe))
pattern Pat9GoType d_abRd = T (H d_abRd)
pattern Pat9GoConst d_abRc = H d_abRc
pattern Pat8GoOp d_abRb = H d_abRb
pattern Pat7GoImpQual d_abRa = T (T (H d_abRa))
pattern Pat7GoImpDot d_abR9 = T (H d_abR9)
pattern Pat7GoImp d_abR8 = H d_abR8
pattern Pat6GoImpSpec d_abR7 = H d_abR7
pattern Pat558 d_abR6 = T (H d_abR6)
pattern Pat59193 d_abR5 = H d_abR5
pattern Pat4GoIfPrel d_abR4 = T (T (T (H d_abR4)))
pattern Pat4GoDefine d_abR3 = T (T (H d_abR3))
pattern Pat4GoPragma d_abR2 = T (H d_abR2)
pattern Pat4GoImportDecl d_abR1 = H d_abR1
pattern Pat358 d_abR0 = T (H d_abR0)
pattern Pat39193 d_abQZ = H d_abQZ
pattern Pat258 d_abQY = T (H d_abQY)
pattern Pat29193 d_abQX = H d_abQX
pattern Pat1GoId d_abQW = H d_abQW
pattern Pat0GoSource d_abQV = H d_abQV
instance Family Singl FamGoSource CodesGoSource where
  sfrom'
    = \case
        IdxGoSource
          -> \case
               (El (GoSource x_abTq x_abTr x_abTs))
                 -> Rep
                      (Pat0GoSource
                         ((NA_I (El x_abTq))
                            :* ((NA_I (El x_abTr)) :* ((NA_I (El x_abTs)) :* NP0))))
        IdxGoId
          -> \case
               (El (GoId x_abTt))
                 -> Rep (Pat1GoId ((NA_K (SString x_abTt)) :* NP0))
        IdxListGoPrel
          -> \case
               (El []) -> Rep (Pat29193 NP0)
               (El ((:) x_abTu x_abTv))
                 -> Rep (Pat258 ((NA_I (El x_abTu)) :* ((NA_I (El x_abTv)) :* NP0)))
        IdxListGoDecl
          -> \case
               (El []) -> Rep (Pat39193 NP0)
               (El ((:) x_abTw x_abTx))
                 -> Rep (Pat358 ((NA_I (El x_abTw)) :* ((NA_I (El x_abTx)) :* NP0)))
        IdxGoPrel
          -> \case
               (El (GoImportDecl x_abTy))
                 -> Rep (Pat4GoImportDecl ((NA_I (El x_abTy)) :* NP0))
               (El (GoPragma x_abTz))
                 -> Rep (Pat4GoPragma ((NA_K (SString x_abTz)) :* NP0))
               (El GoDefine) -> Rep (Pat4GoDefine NP0)
               (El GoIfPrel) -> Rep (Pat4GoIfPrel NP0)
        IdxListGoImpSpec
          -> \case
               (El []) -> Rep (Pat59193 NP0)
               (El ((:) x_abTA x_abTB))
                 -> Rep (Pat558 ((NA_I (El x_abTA)) :* ((NA_I (El x_abTB)) :* NP0)))
        IdxGoImpSpec
          -> \case
               (El (GoImpSpec x_abTC x_abTD))
                 -> Rep
                      (Pat6GoImpSpec
                         ((NA_I (El x_abTC)) :* ((NA_K (SString x_abTD)) :* NP0)))
        IdxGoImpType
          -> \case
               (El GoImp) -> Rep (Pat7GoImp NP0)
               (El (GoImpDot x_abTE))
                 -> Rep (Pat7GoImpDot ((NA_I (El x_abTE)) :* NP0))
               (El (GoImpQual x_abTF))
                 -> Rep (Pat7GoImpQual ((NA_I (El x_abTF)) :* NP0))
        IdxGoOp
          -> \case
               (El (GoOp x_abTG))
                 -> Rep (Pat8GoOp ((NA_K (SString x_abTG)) :* NP0))
        IdxGoDecl
          -> \case
               (El (GoConst x_abTH))
                 -> Rep (Pat9GoConst ((NA_I (El x_abTH)) :* NP0))
               (El (GoType x_abTI))
                 -> Rep (Pat9GoType ((NA_I (El x_abTI)) :* NP0))
               (El (GoVar x_abTJ))
                 -> Rep (Pat9GoVar ((NA_I (El x_abTJ)) :* NP0))
               (El (GoFunc x_abTK))
                 -> Rep (Pat9GoFunc ((NA_I (El x_abTK)) :* NP0))
               (El (GoMeth x_abTL))
                 -> Rep (Pat9GoMeth ((NA_I (El x_abTL)) :* NP0))
        IdxListGoCVSpec
          -> \case
               (El []) -> Rep (Pat109193 NP0)
               (El ((:) x_abTM x_abTN))
                 -> Rep
                      (Pat1058 ((NA_I (El x_abTM)) :* ((NA_I (El x_abTN)) :* NP0)))
        IdxListGoTypeSpec
          -> \case
               (El []) -> Rep (Pat119193 NP0)
               (El ((:) x_abTO x_abTP))
                 -> Rep
                      (Pat1158 ((NA_I (El x_abTO)) :* ((NA_I (El x_abTP)) :* NP0)))
        IdxGoFuncDecl
          -> \case
               (El (GoFuncDecl x_abTQ x_abTR x_abTS))
                 -> Rep
                      (Pat12GoFuncDecl
                         ((NA_I (El x_abTQ))
                            :* ((NA_I (El x_abTR)) :* ((NA_I (El x_abTS)) :* NP0))))
        IdxGoMethDecl
          -> \case
               (El (GoMethDecl x_abTT x_abTU x_abTV x_abTW))
                 -> Rep
                      (Pat13GoMethDecl
                         ((NA_I (El x_abTT))
                            :*
                              ((NA_I (El x_abTU))
                                 :* ((NA_I (El x_abTV)) :* ((NA_I (El x_abTW)) :* NP0)))))
        IdxGoCVSpec
          -> \case
               (El (GoCVSpec x_abTX x_abTY x_abTZ))
                 -> Rep
                      (Pat14GoCVSpec
                         ((NA_I (El x_abTX))
                            :* ((NA_I (El x_abTY)) :* ((NA_I (El x_abTZ)) :* NP0))))
        IdxListGoId
          -> \case
               (El []) -> Rep (Pat159193 NP0)
               (El ((:) x_abU0 x_abU1))
                 -> Rep
                      (Pat1558 ((NA_I (El x_abU0)) :* ((NA_I (El x_abU1)) :* NP0)))
        IdxMaybeGoType
          -> \case
               (El Nothing) -> Rep (Pat16Nothing NP0)
               (El (Just x_abU2)) -> Rep (Pat16Just ((NA_I (El x_abU2)) :* NP0))
        IdxListGoExpr
          -> \case
               (El []) -> Rep (Pat179193 NP0)
               (El ((:) x_abU3 x_abU4))
                 -> Rep
                      (Pat1758 ((NA_I (El x_abU3)) :* ((NA_I (El x_abU4)) :* NP0)))
        IdxGoType
          -> \case
               (El (GoTypeName x_abU5 x_abU6))
                 -> Rep
                      (Pat18GoTypeName
                         ((NA_I (El x_abU5)) :* ((NA_I (El x_abU6)) :* NP0)))
               (El (GoArrayType x_abU7 x_abU8))
                 -> Rep
                      (Pat18GoArrayType
                         ((NA_I (El x_abU7)) :* ((NA_I (El x_abU8)) :* NP0)))
               (El (GoChannelType x_abU9 x_abUa))
                 -> Rep
                      (Pat18GoChannelType
                         ((NA_I (El x_abU9)) :* ((NA_I (El x_abUa)) :* NP0)))
               (El (GoElipsisType x_abUb))
                 -> Rep (Pat18GoElipsisType ((NA_I (El x_abUb)) :* NP0))
               (El (GoFunctionType x_abUc))
                 -> Rep (Pat18GoFunctionType ((NA_I (El x_abUc)) :* NP0))
               (El (GoInterfaceType x_abUd))
                 -> Rep (Pat18GoInterfaceType ((NA_I (El x_abUd)) :* NP0))
               (El (GoMapType x_abUe x_abUf))
                 -> Rep
                      (Pat18GoMapType
                         ((NA_I (El x_abUe)) :* ((NA_I (El x_abUf)) :* NP0)))
               (El (GoPointerType x_abUg))
                 -> Rep (Pat18GoPointerType ((NA_I (El x_abUg)) :* NP0))
               (El (GoSliceType x_abUh))
                 -> Rep (Pat18GoSliceType ((NA_I (El x_abUh)) :* NP0))
               (El (GoStructType x_abUi))
                 -> Rep (Pat18GoStructType ((NA_I (El x_abUi)) :* NP0))
        IdxGoExpr
          -> \case
               (El (GoPrim x_abUj))
                 -> Rep (Pat19GoPrim ((NA_I (El x_abUj)) :* NP0))
               (El (Go1Op x_abUk x_abUl))
                 -> Rep
                      (Pat19Go1Op ((NA_I (El x_abUk)) :* ((NA_I (El x_abUl)) :* NP0)))
               (El (Go2Op x_abUm x_abUn x_abUo))
                 -> Rep
                      (Pat19Go2Op
                         ((NA_I (El x_abUm))
                            :* ((NA_I (El x_abUn)) :* ((NA_I (El x_abUo)) :* NP0))))
        IdxGoChanKind
          -> \case
               (El GoIChan) -> Rep (Pat20GoIChan NP0)
               (El GoOChan) -> Rep (Pat20GoOChan NP0)
               (El GoIOChan) -> Rep (Pat20GoIOChan NP0)
        IdxGoSig
          -> \case
               (El (GoSig x_abUp x_abUq))
                 -> Rep
                      (Pat21GoSig ((NA_I (El x_abUp)) :* ((NA_I (El x_abUq)) :* NP0)))
        IdxListGoMethSpec
          -> \case
               (El []) -> Rep (Pat229193 NP0)
               (El ((:) x_abUr x_abUs))
                 -> Rep
                      (Pat2258 ((NA_I (El x_abUr)) :* ((NA_I (El x_abUs)) :* NP0)))
        IdxListGoFieldType
          -> \case
               (El []) -> Rep (Pat239193 NP0)
               (El ((:) x_abUt x_abUu))
                 -> Rep
                      (Pat2358 ((NA_I (El x_abUt)) :* ((NA_I (El x_abUu)) :* NP0)))
        IdxGoPrim
          -> \case
               (El (GoLiteral x_abUv))
                 -> Rep (Pat24GoLiteral ((NA_I (El x_abUv)) :* NP0))
               (El (GoQual x_abUw x_abUx))
                 -> Rep
                      (Pat24GoQual ((NA_I (El x_abUw)) :* ((NA_I (El x_abUx)) :* NP0)))
               (El (GoMethod x_abUy x_abUz))
                 -> Rep
                      (Pat24GoMethod ((NA_I (El x_abUy)) :* ((NA_I (El x_abUz)) :* NP0)))
               (El (GoParen x_abUA))
                 -> Rep (Pat24GoParen ((NA_I (El x_abUA)) :* NP0))
               (El (GoCast x_abUB x_abUC))
                 -> Rep
                      (Pat24GoCast ((NA_I (El x_abUB)) :* ((NA_I (El x_abUC)) :* NP0)))
               (El (GoNew x_abUD))
                 -> Rep (Pat24GoNew ((NA_I (El x_abUD)) :* NP0))
               (El (GoMake x_abUE x_abUF))
                 -> Rep
                      (Pat24GoMake ((NA_I (El x_abUE)) :* ((NA_I (El x_abUF)) :* NP0)))
               (El (GoSelect x_abUG x_abUH))
                 -> Rep
                      (Pat24GoSelect ((NA_I (El x_abUG)) :* ((NA_I (El x_abUH)) :* NP0)))
               (El (GoIndex x_abUI x_abUJ))
                 -> Rep
                      (Pat24GoIndex ((NA_I (El x_abUI)) :* ((NA_I (El x_abUJ)) :* NP0)))
               (El (GoSlice x_abUK x_abUL))
                 -> Rep
                      (Pat24GoSlice ((NA_I (El x_abUK)) :* ((NA_I (El x_abUL)) :* NP0)))
               (El (GoTA x_abUM x_abUN))
                 -> Rep
                      (Pat24GoTA ((NA_I (El x_abUM)) :* ((NA_I (El x_abUN)) :* NP0)))
               (El (GoCall x_abUO x_abUP x_abUQ))
                 -> Rep
                      (Pat24GoCall
                         ((NA_I (El x_abUO))
                            :* ((NA_I (El x_abUP)) :* ((NA_K (SBool x_abUQ)) :* NP0))))
        IdxGoLit
          -> \case
               (El (GoLitInt x_abUR x_abUS))
                 -> Rep
                      (Pat25GoLitInt
                         ((NA_K (SString x_abUR)) :* ((NA_K (SInteger x_abUS)) :* NP0)))
               (El (GoLitReal x_abUT x_abUU))
                 -> Rep
                      (Pat25GoLitReal
                         ((NA_K (SString x_abUT)) :* ((NA_K (SFloat x_abUU)) :* NP0)))
               (El (GoLitImag x_abUV x_abUW))
                 -> Rep
                      (Pat25GoLitImag
                         ((NA_K (SString x_abUV)) :* ((NA_K (SFloat x_abUW)) :* NP0)))
               (El (GoLitChar x_abUX x_abUY))
                 -> Rep
                      (Pat25GoLitChar
                         ((NA_K (SString x_abUX)) :* ((NA_K (SChar x_abUY)) :* NP0)))
               (El (GoLitStr x_abUZ x_abV0))
                 -> Rep
                      (Pat25GoLitStr
                         ((NA_K (SString x_abUZ)) :* ((NA_K (SString x_abV0)) :* NP0)))
               (El (GoLitComp x_abV1 x_abV2))
                 -> Rep
                      (Pat25GoLitComp
                         ((NA_I (El x_abV1)) :* ((NA_I (El x_abV2)) :* NP0)))
               (El (GoLitFunc x_abV3))
                 -> Rep (Pat25GoLitFunc ((NA_I (El x_abV3)) :* NP0))
        IdxGoRec
          -> \case
               (El (GoRec x_abV4 x_abV5 x_abV6))
                 -> Rep
                      (Pat26GoRec
                         ((NA_K (SBool x_abV4))
                            :* ((NA_I (El x_abV5)) :* ((NA_I (El x_abV6)) :* NP0))))
        IdxGoComp
          -> \case
               (El (GoComp x_abV7))
                 -> Rep (Pat27GoComp ((NA_I (El x_abV7)) :* NP0))
        IdxGoFuncExpr
          -> \case
               (El (GoFuncExpr x_abV8 x_abV9))
                 -> Rep
                      (Pat28GoFuncExpr
                         ((NA_I (El x_abV8)) :* ((NA_I (El x_abV9)) :* NP0)))
        IdxListGoElement
          -> \case
               (El []) -> Rep (Pat299193 NP0)
               (El ((:) x_abVa x_abVb))
                 -> Rep
                      (Pat2958 ((NA_I (El x_abVa)) :* ((NA_I (El x_abVb)) :* NP0)))
        IdxGoElement
          -> \case
               (El (GoElement x_abVc x_abVd))
                 -> Rep
                      (Pat30GoElement
                         ((NA_I (El x_abVc)) :* ((NA_I (El x_abVd)) :* NP0)))
        IdxGoKey
          -> \case
               (El GoKeyNone) -> Rep (Pat31GoKeyNone NP0)
               (El (GoKeyField x_abVe))
                 -> Rep (Pat31GoKeyField ((NA_I (El x_abVe)) :* NP0))
               (El (GoKeyIndex x_abVf))
                 -> Rep (Pat31GoKeyIndex ((NA_I (El x_abVf)) :* NP0))
        IdxGoValue
          -> \case
               (El (GoValueExpr x_abVg))
                 -> Rep (Pat32GoValueExpr ((NA_I (El x_abVg)) :* NP0))
               (El (GoValueComp x_abVh))
                 -> Rep (Pat32GoValueComp ((NA_I (El x_abVh)) :* NP0))
        IdxGoBlock
          -> \case
               (El (GoBlock x_abVi))
                 -> Rep (Pat33GoBlock ((NA_I (El x_abVi)) :* NP0))
               (El GoNoBlock) -> Rep (Pat33GoNoBlock NP0)
        IdxListGoParam
          -> \case
               (El []) -> Rep (Pat349193 NP0)
               (El ((:) x_abVj x_abVk))
                 -> Rep
                      (Pat3458 ((NA_I (El x_abVj)) :* ((NA_I (El x_abVk)) :* NP0)))
        IdxGoParam
          -> \case
               (El (GoParam x_abVl x_abVm))
                 -> Rep
                      (Pat35GoParam ((NA_I (El x_abVl)) :* ((NA_I (El x_abVm)) :* NP0)))
        IdxListGoStmt
          -> \case
               (El []) -> Rep (Pat369193 NP0)
               (El ((:) x_abVn x_abVo))
                 -> Rep
                      (Pat3658 ((NA_I (El x_abVn)) :* ((NA_I (El x_abVo)) :* NP0)))
        IdxGoStmt
          -> \case
               (El (GoStmtDecl x_abVp))
                 -> Rep (Pat37GoStmtDecl ((NA_I (El x_abVp)) :* NP0))
               (El (GoStmtLabeled x_abVq x_abVr))
                 -> Rep
                      (Pat37GoStmtLabeled
                         ((NA_I (El x_abVq)) :* ((NA_I (El x_abVr)) :* NP0)))
               (El (GoStmtSimple x_abVs))
                 -> Rep (Pat37GoStmtSimple ((NA_I (El x_abVs)) :* NP0))
               (El (GoStmtGo x_abVt))
                 -> Rep (Pat37GoStmtGo ((NA_I (El x_abVt)) :* NP0))
               (El (GoStmtReturn x_abVu))
                 -> Rep (Pat37GoStmtReturn ((NA_I (El x_abVu)) :* NP0))
               (El (GoStmtBreak x_abVv))
                 -> Rep (Pat37GoStmtBreak ((NA_I (El x_abVv)) :* NP0))
               (El (GoStmtContinue x_abVw))
                 -> Rep (Pat37GoStmtContinue ((NA_I (El x_abVw)) :* NP0))
               (El (GoStmtGoto x_abVx))
                 -> Rep (Pat37GoStmtGoto ((NA_I (El x_abVx)) :* NP0))
               (El GoStmtFallthrough) -> Rep (Pat37GoStmtFallthrough NP0)
               (El (GoStmtBlock x_abVy))
                 -> Rep (Pat37GoStmtBlock ((NA_I (El x_abVy)) :* NP0))
               (El (GoStmtIf x_abVz x_abVA x_abVB))
                 -> Rep
                      (Pat37GoStmtIf
                         ((NA_I (El x_abVz))
                            :* ((NA_I (El x_abVA)) :* ((NA_I (El x_abVB)) :* NP0))))
               (El (GoStmtSelect x_abVC))
                 -> Rep (Pat37GoStmtSelect ((NA_I (El x_abVC)) :* NP0))
               (El (GoStmtSwitch x_abVD x_abVE))
                 -> Rep
                      (Pat37GoStmtSwitch
                         ((NA_I (El x_abVD)) :* ((NA_I (El x_abVE)) :* NP0)))
               (El (GoStmtTypeSwitch x_abVF x_abVG x_abVH))
                 -> Rep
                      (Pat37GoStmtTypeSwitch
                         ((NA_I (El x_abVF))
                            :* ((NA_I (El x_abVG)) :* ((NA_I (El x_abVH)) :* NP0))))
               (El (GoStmtFor x_abVI x_abVJ))
                 -> Rep
                      (Pat37GoStmtFor
                         ((NA_I (El x_abVI)) :* ((NA_I (El x_abVJ)) :* NP0)))
               (El (GoStmtDefer x_abVK))
                 -> Rep (Pat37GoStmtDefer ((NA_I (El x_abVK)) :* NP0))
        IdxGoSimp
          -> \case
               (El GoSimpEmpty) -> Rep (Pat38GoSimpEmpty NP0)
               (El (GoSimpRecv x_abVL))
                 -> Rep (Pat38GoSimpRecv ((NA_I (El x_abVL)) :* NP0))
               (El (GoSimpSend x_abVM x_abVN))
                 -> Rep
                      (Pat38GoSimpSend
                         ((NA_I (El x_abVM)) :* ((NA_I (El x_abVN)) :* NP0)))
               (El (GoSimpExpr x_abVO))
                 -> Rep (Pat38GoSimpExpr ((NA_I (El x_abVO)) :* NP0))
               (El (GoSimpInc x_abVP))
                 -> Rep (Pat38GoSimpInc ((NA_I (El x_abVP)) :* NP0))
               (El (GoSimpDec x_abVQ))
                 -> Rep (Pat38GoSimpDec ((NA_I (El x_abVQ)) :* NP0))
               (El (GoSimpAsn x_abVR x_abVS x_abVT))
                 -> Rep
                      (Pat38GoSimpAsn
                         ((NA_I (El x_abVR))
                            :* ((NA_I (El x_abVS)) :* ((NA_I (El x_abVT)) :* NP0))))
               (El (GoSimpVar x_abVU x_abVV))
                 -> Rep
                      (Pat38GoSimpVar
                         ((NA_I (El x_abVU)) :* ((NA_I (El x_abVV)) :* NP0)))
        IdxMaybeGoId
          -> \case
               (El Nothing) -> Rep (Pat39Nothing NP0)
               (El (Just x_abVW)) -> Rep (Pat39Just ((NA_I (El x_abVW)) :* NP0))
        IdxGoCond
          -> \case
               (El (GoCond x_abVX x_abVY))
                 -> Rep
                      (Pat40GoCond ((NA_I (El x_abVX)) :* ((NA_I (El x_abVY)) :* NP0)))
        IdxMaybeGoStmt
          -> \case
               (El Nothing) -> Rep (Pat41Nothing NP0)
               (El (Just x_abVZ)) -> Rep (Pat41Just ((NA_I (El x_abVZ)) :* NP0))
        IdxListGoCaseGoChan
          -> \case
               (El []) -> Rep (Pat429193 NP0)
               (El ((:) x_abW0 x_abW1))
                 -> Rep
                      (Pat4258 ((NA_I (El x_abW0)) :* ((NA_I (El x_abW1)) :* NP0)))
        IdxListGoCaseGoExpr
          -> \case
               (El []) -> Rep (Pat439193 NP0)
               (El ((:) x_abW2 x_abW3))
                 -> Rep
                      (Pat4358 ((NA_I (El x_abW2)) :* ((NA_I (El x_abW3)) :* NP0)))
        IdxListGoCaseGoType
          -> \case
               (El []) -> Rep (Pat449193 NP0)
               (El ((:) x_abW4 x_abW5))
                 -> Rep
                      (Pat4458 ((NA_I (El x_abW4)) :* ((NA_I (El x_abW5)) :* NP0)))
        IdxGoForClause
          -> \case
               (El (GoForWhile x_abW6))
                 -> Rep (Pat45GoForWhile ((NA_I (El x_abW6)) :* NP0))
               (El (GoForThree x_abW7 x_abW8 x_abW9))
                 -> Rep
                      (Pat45GoForThree
                         ((NA_I (El x_abW7))
                            :* ((NA_I (El x_abW8)) :* ((NA_I (El x_abW9)) :* NP0))))
               (El (GoForRange x_abWa x_abWb))
                 -> Rep
                      (Pat45GoForRange
                         ((NA_I (El x_abWa)) :* ((NA_I (El x_abWb)) :* NP0)))
        IdxMaybeGoSimp
          -> \case
               (El Nothing) -> Rep (Pat46Nothing NP0)
               (El (Just x_abWc)) -> Rep (Pat46Just ((NA_I (El x_abWc)) :* NP0))
        IdxMaybeGoExpr
          -> \case
               (El Nothing) -> Rep (Pat47Nothing NP0)
               (El (Just x_abWd)) -> Rep (Pat47Just ((NA_I (El x_abWd)) :* NP0))
        IdxGoCaseGoChan
          -> \case
               (El (GoCase x_abWe x_abWf))
                 -> Rep
                      (Pat48GoCase ((NA_I (El x_abWe)) :* ((NA_I (El x_abWf)) :* NP0)))
               (El (GoDefault x_abWg))
                 -> Rep (Pat48GoDefault ((NA_I (El x_abWg)) :* NP0))
        IdxListGoChan
          -> \case
               (El []) -> Rep (Pat499193 NP0)
               (El ((:) x_abWh x_abWi))
                 -> Rep
                      (Pat4958 ((NA_I (El x_abWh)) :* ((NA_I (El x_abWi)) :* NP0)))
        IdxGoChan
          -> \case
               (El (GoChanRecv x_abWj x_abWk))
                 -> Rep
                      (Pat50GoChanRecv
                         ((NA_I (El x_abWj)) :* ((NA_I (El x_abWk)) :* NP0)))
               (El (GoChanSend x_abWl x_abWm))
                 -> Rep
                      (Pat50GoChanSend
                         ((NA_I (El x_abWl)) :* ((NA_I (El x_abWm)) :* NP0)))
        IdxMaybeGoChanInner
          -> \case
               (El Nothing) -> Rep (Pat51Nothing NP0)
               (El (Just x_abWn)) -> Rep (Pat51Just ((NA_I (El x_abWn)) :* NP0))
        IdxGoChanInner
          -> \case
               (El (GoChanInner x_abWo x_abWp))
                 -> Rep
                      (Pat52GoChanInner
                         ((NA_I (El x_abWo)) :* ((NA_I (El x_abWp)) :* NP0)))
        IdxGoCaseGoExpr
          -> \case
               (El (GoCase x_abWq x_abWr))
                 -> Rep
                      (Pat53GoCase ((NA_I (El x_abWq)) :* ((NA_I (El x_abWr)) :* NP0)))
               (El (GoDefault x_abWs))
                 -> Rep (Pat53GoDefault ((NA_I (El x_abWs)) :* NP0))
        IdxGoCaseGoType
          -> \case
               (El (GoCase x_abWt x_abWu))
                 -> Rep
                      (Pat54GoCase ((NA_I (El x_abWt)) :* ((NA_I (El x_abWu)) :* NP0)))
               (El (GoDefault x_abWv))
                 -> Rep (Pat54GoDefault ((NA_I (El x_abWv)) :* NP0))
        IdxListGoType
          -> \case
               (El []) -> Rep (Pat559193 NP0)
               (El ((:) x_abWw x_abWx))
                 -> Rep
                      (Pat5558 ((NA_I (El x_abWw)) :* ((NA_I (El x_abWx)) :* NP0)))
        IdxGoMethSpec
          -> \case
               (El (GoMethSpec x_abWy x_abWz))
                 -> Rep
                      (Pat56GoMethSpec
                         ((NA_I (El x_abWy)) :* ((NA_I (El x_abWz)) :* NP0)))
               (El (GoInterface x_abWA))
                 -> Rep (Pat56GoInterface ((NA_I (El x_abWA)) :* NP0))
        IdxGoFieldType
          -> \case
               (El (GoFieldType x_abWB x_abWC x_abWD))
                 -> Rep
                      (Pat57GoFieldType
                         ((NA_K (SString x_abWB))
                            :* ((NA_I (El x_abWC)) :* ((NA_I (El x_abWD)) :* NP0))))
               (El (GoFieldAnon x_abWE x_abWF x_abWG))
                 -> Rep
                      (Pat57GoFieldAnon
                         ((NA_K (SString x_abWE))
                            :* ((NA_K (SBool x_abWF)) :* ((NA_I (El x_abWG)) :* NP0))))
        IdxGoTypeSpec
          -> \case
               (El (GoTypeSpec x_abWH x_abWI))
                 -> Rep
                      (Pat58GoTypeSpec
                         ((NA_I (El x_abWH)) :* ((NA_I (El x_abWI)) :* NP0)))
  sto'
    = \case
        IdxGoSource
          -> \case
               (Rep (Pat0GoSource (NA_I (El y_abWJ) :* (NA_I (El y_abWK) :* (NA_I (El y_abWL) :* NP0)))))
                 -> El (((GoSource y_abWJ) y_abWK) y_abWL)
               _ -> error "matchAll"
        IdxGoId
          -> \case
               (Rep (Pat1GoId (NA_K (SString y_abWM) :* NP0)))
                 -> El (GoId y_abWM)
               _ -> error "matchAll"
        IdxListGoPrel
          -> \case
               (Rep (Pat29193 NP0)) -> El []
               (Rep (Pat258 (NA_I (El y_abWN) :* (NA_I (El y_abWO) :* NP0))))
                 -> El (((:) y_abWN) y_abWO)
               _ -> error "matchAll"
        IdxListGoDecl
          -> \case
               (Rep (Pat39193 NP0)) -> El []
               (Rep (Pat358 (NA_I (El y_abWP) :* (NA_I (El y_abWQ) :* NP0))))
                 -> El (((:) y_abWP) y_abWQ)
               _ -> error "matchAll"
        IdxGoPrel
          -> \case
               (Rep (Pat4GoImportDecl (NA_I (El y_abWR) :* NP0)))
                 -> El (GoImportDecl y_abWR)
               (Rep (Pat4GoPragma (NA_K (SString y_abWS) :* NP0)))
                 -> El (GoPragma y_abWS)
               (Rep (Pat4GoDefine NP0)) -> El GoDefine
               (Rep (Pat4GoIfPrel NP0)) -> El GoIfPrel
               _ -> error "matchAll"
        IdxListGoImpSpec
          -> \case
               (Rep (Pat59193 NP0)) -> El []
               (Rep (Pat558 (NA_I (El y_abWT) :* (NA_I (El y_abWU) :* NP0))))
                 -> El (((:) y_abWT) y_abWU)
               _ -> error "matchAll"
        IdxGoImpSpec
          -> \case
               (Rep (Pat6GoImpSpec (NA_I (El y_abWV) :* (NA_K (SString y_abWW) :* NP0))))
                 -> El ((GoImpSpec y_abWV) y_abWW)
               _ -> error "matchAll"
        IdxGoImpType
          -> \case
               (Rep (Pat7GoImp NP0)) -> El GoImp
               (Rep (Pat7GoImpDot (NA_I (El y_abWX) :* NP0)))
                 -> El (GoImpDot y_abWX)
               (Rep (Pat7GoImpQual (NA_I (El y_abWY) :* NP0)))
                 -> El (GoImpQual y_abWY)
               _ -> error "matchAll"
        IdxGoOp
          -> \case
               (Rep (Pat8GoOp (NA_K (SString y_abWZ) :* NP0)))
                 -> El (GoOp y_abWZ)
               _ -> error "matchAll"
        IdxGoDecl
          -> \case
               (Rep (Pat9GoConst (NA_I (El y_abX0) :* NP0)))
                 -> El (GoConst y_abX0)
               (Rep (Pat9GoType (NA_I (El y_abX1) :* NP0)))
                 -> El (GoType y_abX1)
               (Rep (Pat9GoVar (NA_I (El y_abX2) :* NP0))) -> El (GoVar y_abX2)
               (Rep (Pat9GoFunc (NA_I (El y_abX3) :* NP0)))
                 -> El (GoFunc y_abX3)
               (Rep (Pat9GoMeth (NA_I (El y_abX4) :* NP0)))
                 -> El (GoMeth y_abX4)
               _ -> error "matchAll"
        IdxListGoCVSpec
          -> \case
               (Rep (Pat109193 NP0)) -> El []
               (Rep (Pat1058 (NA_I (El y_abX5) :* (NA_I (El y_abX6) :* NP0))))
                 -> El (((:) y_abX5) y_abX6)
               _ -> error "matchAll"
        IdxListGoTypeSpec
          -> \case
               (Rep (Pat119193 NP0)) -> El []
               (Rep (Pat1158 (NA_I (El y_abX7) :* (NA_I (El y_abX8) :* NP0))))
                 -> El (((:) y_abX7) y_abX8)
               _ -> error "matchAll"
        IdxGoFuncDecl
          -> \case
               (Rep (Pat12GoFuncDecl (NA_I (El y_abX9) :* (NA_I (El y_abXa) :* (NA_I (El y_abXb) :* NP0)))))
                 -> El (((GoFuncDecl y_abX9) y_abXa) y_abXb)
               _ -> error "matchAll"
        IdxGoMethDecl
          -> \case
               (Rep (Pat13GoMethDecl (NA_I (El y_abXc) :* (NA_I (El y_abXd) :* (NA_I (El y_abXe) :* (NA_I (El y_abXf) :* NP0))))))
                 -> El ((((GoMethDecl y_abXc) y_abXd) y_abXe) y_abXf)
               _ -> error "matchAll"
        IdxGoCVSpec
          -> \case
               (Rep (Pat14GoCVSpec (NA_I (El y_abXg) :* (NA_I (El y_abXh) :* (NA_I (El y_abXi) :* NP0)))))
                 -> El (((GoCVSpec y_abXg) y_abXh) y_abXi)
               _ -> error "matchAll"
        IdxListGoId
          -> \case
               (Rep (Pat159193 NP0)) -> El []
               (Rep (Pat1558 (NA_I (El y_abXj) :* (NA_I (El y_abXk) :* NP0))))
                 -> El (((:) y_abXj) y_abXk)
               _ -> error "matchAll"
        IdxMaybeGoType
          -> \case
               (Rep (Pat16Nothing NP0)) -> El Nothing
               (Rep (Pat16Just (NA_I (El y_abXl) :* NP0))) -> El (Just y_abXl)
               _ -> error "matchAll"
        IdxListGoExpr
          -> \case
               (Rep (Pat179193 NP0)) -> El []
               (Rep (Pat1758 (NA_I (El y_abXm) :* (NA_I (El y_abXn) :* NP0))))
                 -> El (((:) y_abXm) y_abXn)
               _ -> error "matchAll"
        IdxGoType
          -> \case
               (Rep (Pat18GoTypeName (NA_I (El y_abXo) :* (NA_I (El y_abXp) :* NP0))))
                 -> El ((GoTypeName y_abXo) y_abXp)
               (Rep (Pat18GoArrayType (NA_I (El y_abXq) :* (NA_I (El y_abXr) :* NP0))))
                 -> El ((GoArrayType y_abXq) y_abXr)
               (Rep (Pat18GoChannelType (NA_I (El y_abXs) :* (NA_I (El y_abXt) :* NP0))))
                 -> El ((GoChannelType y_abXs) y_abXt)
               (Rep (Pat18GoElipsisType (NA_I (El y_abXu) :* NP0)))
                 -> El (GoElipsisType y_abXu)
               (Rep (Pat18GoFunctionType (NA_I (El y_abXv) :* NP0)))
                 -> El (GoFunctionType y_abXv)
               (Rep (Pat18GoInterfaceType (NA_I (El y_abXw) :* NP0)))
                 -> El (GoInterfaceType y_abXw)
               (Rep (Pat18GoMapType (NA_I (El y_abXx) :* (NA_I (El y_abXy) :* NP0))))
                 -> El ((GoMapType y_abXx) y_abXy)
               (Rep (Pat18GoPointerType (NA_I (El y_abXz) :* NP0)))
                 -> El (GoPointerType y_abXz)
               (Rep (Pat18GoSliceType (NA_I (El y_abXA) :* NP0)))
                 -> El (GoSliceType y_abXA)
               (Rep (Pat18GoStructType (NA_I (El y_abXB) :* NP0)))
                 -> El (GoStructType y_abXB)
               _ -> error "matchAll"
        IdxGoExpr
          -> \case
               (Rep (Pat19GoPrim (NA_I (El y_abXC) :* NP0)))
                 -> El (GoPrim y_abXC)
               (Rep (Pat19Go1Op (NA_I (El y_abXD) :* (NA_I (El y_abXE) :* NP0))))
                 -> El ((Go1Op y_abXD) y_abXE)
               (Rep (Pat19Go2Op (NA_I (El y_abXF) :* (NA_I (El y_abXG) :* (NA_I (El y_abXH) :* NP0)))))
                 -> El (((Go2Op y_abXF) y_abXG) y_abXH)
               _ -> error "matchAll"
        IdxGoChanKind
          -> \case
               (Rep (Pat20GoIChan NP0)) -> El GoIChan
               (Rep (Pat20GoOChan NP0)) -> El GoOChan
               (Rep (Pat20GoIOChan NP0)) -> El GoIOChan
               _ -> error "matchAll"
        IdxGoSig
          -> \case
               (Rep (Pat21GoSig (NA_I (El y_abXI) :* (NA_I (El y_abXJ) :* NP0))))
                 -> El ((GoSig y_abXI) y_abXJ)
               _ -> error "matchAll"
        IdxListGoMethSpec
          -> \case
               (Rep (Pat229193 NP0)) -> El []
               (Rep (Pat2258 (NA_I (El y_abXK) :* (NA_I (El y_abXL) :* NP0))))
                 -> El (((:) y_abXK) y_abXL)
               _ -> error "matchAll"
        IdxListGoFieldType
          -> \case
               (Rep (Pat239193 NP0)) -> El []
               (Rep (Pat2358 (NA_I (El y_abXM) :* (NA_I (El y_abXN) :* NP0))))
                 -> El (((:) y_abXM) y_abXN)
               _ -> error "matchAll"
        IdxGoPrim
          -> \case
               (Rep (Pat24GoLiteral (NA_I (El y_abXO) :* NP0)))
                 -> El (GoLiteral y_abXO)
               (Rep (Pat24GoQual (NA_I (El y_abXP) :* (NA_I (El y_abXQ) :* NP0))))
                 -> El ((GoQual y_abXP) y_abXQ)
               (Rep (Pat24GoMethod (NA_I (El y_abXR) :* (NA_I (El y_abXS) :* NP0))))
                 -> El ((GoMethod y_abXR) y_abXS)
               (Rep (Pat24GoParen (NA_I (El y_abXT) :* NP0)))
                 -> El (GoParen y_abXT)
               (Rep (Pat24GoCast (NA_I (El y_abXU) :* (NA_I (El y_abXV) :* NP0))))
                 -> El ((GoCast y_abXU) y_abXV)
               (Rep (Pat24GoNew (NA_I (El y_abXW) :* NP0))) -> El (GoNew y_abXW)
               (Rep (Pat24GoMake (NA_I (El y_abXX) :* (NA_I (El y_abXY) :* NP0))))
                 -> El ((GoMake y_abXX) y_abXY)
               (Rep (Pat24GoSelect (NA_I (El y_abXZ) :* (NA_I (El y_abY0) :* NP0))))
                 -> El ((GoSelect y_abXZ) y_abY0)
               (Rep (Pat24GoIndex (NA_I (El y_abY1) :* (NA_I (El y_abY2) :* NP0))))
                 -> El ((GoIndex y_abY1) y_abY2)
               (Rep (Pat24GoSlice (NA_I (El y_abY3) :* (NA_I (El y_abY4) :* NP0))))
                 -> El ((GoSlice y_abY3) y_abY4)
               (Rep (Pat24GoTA (NA_I (El y_abY5) :* (NA_I (El y_abY6) :* NP0))))
                 -> El ((GoTA y_abY5) y_abY6)
               (Rep (Pat24GoCall (NA_I (El y_abY7) :* (NA_I (El y_abY8) :* (NA_K (SBool y_abY9) :* NP0)))))
                 -> El (((GoCall y_abY7) y_abY8) y_abY9)
               _ -> error "matchAll"
        IdxGoLit
          -> \case
               (Rep (Pat25GoLitInt (NA_K (SString y_abYa) :* (NA_K (SInteger y_abYb) :* NP0))))
                 -> El ((GoLitInt y_abYa) y_abYb)
               (Rep (Pat25GoLitReal (NA_K (SString y_abYc) :* (NA_K (SFloat y_abYd) :* NP0))))
                 -> El ((GoLitReal y_abYc) y_abYd)
               (Rep (Pat25GoLitImag (NA_K (SString y_abYe) :* (NA_K (SFloat y_abYf) :* NP0))))
                 -> El ((GoLitImag y_abYe) y_abYf)
               (Rep (Pat25GoLitChar (NA_K (SString y_abYg) :* (NA_K (SChar y_abYh) :* NP0))))
                 -> El ((GoLitChar y_abYg) y_abYh)
               (Rep (Pat25GoLitStr (NA_K (SString y_abYi) :* (NA_K (SString y_abYj) :* NP0))))
                 -> El ((GoLitStr y_abYi) y_abYj)
               (Rep (Pat25GoLitComp (NA_I (El y_abYk) :* (NA_I (El y_abYl) :* NP0))))
                 -> El ((GoLitComp y_abYk) y_abYl)
               (Rep (Pat25GoLitFunc (NA_I (El y_abYm) :* NP0)))
                 -> El (GoLitFunc y_abYm)
               _ -> error "matchAll"
        IdxGoRec
          -> \case
               (Rep (Pat26GoRec (NA_K (SBool y_abYn) :* (NA_I (El y_abYo) :* (NA_I (El y_abYp) :* NP0)))))
                 -> El (((GoRec y_abYn) y_abYo) y_abYp)
               _ -> error "matchAll"
        IdxGoComp
          -> \case
               (Rep (Pat27GoComp (NA_I (El y_abYq) :* NP0)))
                 -> El (GoComp y_abYq)
               _ -> error "matchAll"
        IdxGoFuncExpr
          -> \case
               (Rep (Pat28GoFuncExpr (NA_I (El y_abYr) :* (NA_I (El y_abYs) :* NP0))))
                 -> El ((GoFuncExpr y_abYr) y_abYs)
               _ -> error "matchAll"
        IdxListGoElement
          -> \case
               (Rep (Pat299193 NP0)) -> El []
               (Rep (Pat2958 (NA_I (El y_abYt) :* (NA_I (El y_abYu) :* NP0))))
                 -> El (((:) y_abYt) y_abYu)
               _ -> error "matchAll"
        IdxGoElement
          -> \case
               (Rep (Pat30GoElement (NA_I (El y_abYv) :* (NA_I (El y_abYw) :* NP0))))
                 -> El ((GoElement y_abYv) y_abYw)
               _ -> error "matchAll"
        IdxGoKey
          -> \case
               (Rep (Pat31GoKeyNone NP0)) -> El GoKeyNone
               (Rep (Pat31GoKeyField (NA_I (El y_abYx) :* NP0)))
                 -> El (GoKeyField y_abYx)
               (Rep (Pat31GoKeyIndex (NA_I (El y_abYy) :* NP0)))
                 -> El (GoKeyIndex y_abYy)
               _ -> error "matchAll"
        IdxGoValue
          -> \case
               (Rep (Pat32GoValueExpr (NA_I (El y_abYz) :* NP0)))
                 -> El (GoValueExpr y_abYz)
               (Rep (Pat32GoValueComp (NA_I (El y_abYA) :* NP0)))
                 -> El (GoValueComp y_abYA)
               _ -> error "matchAll"
        IdxGoBlock
          -> \case
               (Rep (Pat33GoBlock (NA_I (El y_abYB) :* NP0)))
                 -> El (GoBlock y_abYB)
               (Rep (Pat33GoNoBlock NP0)) -> El GoNoBlock
               _ -> error "matchAll"
        IdxListGoParam
          -> \case
               (Rep (Pat349193 NP0)) -> El []
               (Rep (Pat3458 (NA_I (El y_abYC) :* (NA_I (El y_abYD) :* NP0))))
                 -> El (((:) y_abYC) y_abYD)
               _ -> error "matchAll"
        IdxGoParam
          -> \case
               (Rep (Pat35GoParam (NA_I (El y_abYE) :* (NA_I (El y_abYF) :* NP0))))
                 -> El ((GoParam y_abYE) y_abYF)
               _ -> error "matchAll"
        IdxListGoStmt
          -> \case
               (Rep (Pat369193 NP0)) -> El []
               (Rep (Pat3658 (NA_I (El y_abYG) :* (NA_I (El y_abYH) :* NP0))))
                 -> El (((:) y_abYG) y_abYH)
               _ -> error "matchAll"
        IdxGoStmt
          -> \case
               (Rep (Pat37GoStmtDecl (NA_I (El y_abYI) :* NP0)))
                 -> El (GoStmtDecl y_abYI)
               (Rep (Pat37GoStmtLabeled (NA_I (El y_abYJ) :* (NA_I (El y_abYK) :* NP0))))
                 -> El ((GoStmtLabeled y_abYJ) y_abYK)
               (Rep (Pat37GoStmtSimple (NA_I (El y_abYL) :* NP0)))
                 -> El (GoStmtSimple y_abYL)
               (Rep (Pat37GoStmtGo (NA_I (El y_abYM) :* NP0)))
                 -> El (GoStmtGo y_abYM)
               (Rep (Pat37GoStmtReturn (NA_I (El y_abYN) :* NP0)))
                 -> El (GoStmtReturn y_abYN)
               (Rep (Pat37GoStmtBreak (NA_I (El y_abYO) :* NP0)))
                 -> El (GoStmtBreak y_abYO)
               (Rep (Pat37GoStmtContinue (NA_I (El y_abYP) :* NP0)))
                 -> El (GoStmtContinue y_abYP)
               (Rep (Pat37GoStmtGoto (NA_I (El y_abYQ) :* NP0)))
                 -> El (GoStmtGoto y_abYQ)
               (Rep (Pat37GoStmtFallthrough NP0)) -> El GoStmtFallthrough
               (Rep (Pat37GoStmtBlock (NA_I (El y_abYR) :* NP0)))
                 -> El (GoStmtBlock y_abYR)
               (Rep (Pat37GoStmtIf (NA_I (El y_abYS) :* (NA_I (El y_abYT) :* (NA_I (El y_abYU) :* NP0)))))
                 -> El (((GoStmtIf y_abYS) y_abYT) y_abYU)
               (Rep (Pat37GoStmtSelect (NA_I (El y_abYV) :* NP0)))
                 -> El (GoStmtSelect y_abYV)
               (Rep (Pat37GoStmtSwitch (NA_I (El y_abYW) :* (NA_I (El y_abYX) :* NP0))))
                 -> El ((GoStmtSwitch y_abYW) y_abYX)
               (Rep (Pat37GoStmtTypeSwitch (NA_I (El y_abYY) :* (NA_I (El y_abYZ) :* (NA_I (El y_abZ0) :* NP0)))))
                 -> El (((GoStmtTypeSwitch y_abYY) y_abYZ) y_abZ0)
               (Rep (Pat37GoStmtFor (NA_I (El y_abZ1) :* (NA_I (El y_abZ2) :* NP0))))
                 -> El ((GoStmtFor y_abZ1) y_abZ2)
               (Rep (Pat37GoStmtDefer (NA_I (El y_abZ3) :* NP0)))
                 -> El (GoStmtDefer y_abZ3)
               _ -> error "matchAll"
        IdxGoSimp
          -> \case
               (Rep (Pat38GoSimpEmpty NP0)) -> El GoSimpEmpty
               (Rep (Pat38GoSimpRecv (NA_I (El y_abZ4) :* NP0)))
                 -> El (GoSimpRecv y_abZ4)
               (Rep (Pat38GoSimpSend (NA_I (El y_abZ5) :* (NA_I (El y_abZ6) :* NP0))))
                 -> El ((GoSimpSend y_abZ5) y_abZ6)
               (Rep (Pat38GoSimpExpr (NA_I (El y_abZ7) :* NP0)))
                 -> El (GoSimpExpr y_abZ7)
               (Rep (Pat38GoSimpInc (NA_I (El y_abZ8) :* NP0)))
                 -> El (GoSimpInc y_abZ8)
               (Rep (Pat38GoSimpDec (NA_I (El y_abZ9) :* NP0)))
                 -> El (GoSimpDec y_abZ9)
               (Rep (Pat38GoSimpAsn (NA_I (El y_abZa) :* (NA_I (El y_abZb) :* (NA_I (El y_abZc) :* NP0)))))
                 -> El (((GoSimpAsn y_abZa) y_abZb) y_abZc)
               (Rep (Pat38GoSimpVar (NA_I (El y_abZd) :* (NA_I (El y_abZe) :* NP0))))
                 -> El ((GoSimpVar y_abZd) y_abZe)
               _ -> error "matchAll"
        IdxMaybeGoId
          -> \case
               (Rep (Pat39Nothing NP0)) -> El Nothing
               (Rep (Pat39Just (NA_I (El y_abZf) :* NP0))) -> El (Just y_abZf)
               _ -> error "matchAll"
        IdxGoCond
          -> \case
               (Rep (Pat40GoCond (NA_I (El y_abZg) :* (NA_I (El y_abZh) :* NP0))))
                 -> El ((GoCond y_abZg) y_abZh)
               _ -> error "matchAll"
        IdxMaybeGoStmt
          -> \case
               (Rep (Pat41Nothing NP0)) -> El Nothing
               (Rep (Pat41Just (NA_I (El y_abZi) :* NP0))) -> El (Just y_abZi)
               _ -> error "matchAll"
        IdxListGoCaseGoChan
          -> \case
               (Rep (Pat429193 NP0)) -> El []
               (Rep (Pat4258 (NA_I (El y_abZj) :* (NA_I (El y_abZk) :* NP0))))
                 -> El (((:) y_abZj) y_abZk)
               _ -> error "matchAll"
        IdxListGoCaseGoExpr
          -> \case
               (Rep (Pat439193 NP0)) -> El []
               (Rep (Pat4358 (NA_I (El y_abZl) :* (NA_I (El y_abZm) :* NP0))))
                 -> El (((:) y_abZl) y_abZm)
               _ -> error "matchAll"
        IdxListGoCaseGoType
          -> \case
               (Rep (Pat449193 NP0)) -> El []
               (Rep (Pat4458 (NA_I (El y_abZn) :* (NA_I (El y_abZo) :* NP0))))
                 -> El (((:) y_abZn) y_abZo)
               _ -> error "matchAll"
        IdxGoForClause
          -> \case
               (Rep (Pat45GoForWhile (NA_I (El y_abZp) :* NP0)))
                 -> El (GoForWhile y_abZp)
               (Rep (Pat45GoForThree (NA_I (El y_abZq) :* (NA_I (El y_abZr) :* (NA_I (El y_abZs) :* NP0)))))
                 -> El (((GoForThree y_abZq) y_abZr) y_abZs)
               (Rep (Pat45GoForRange (NA_I (El y_abZt) :* (NA_I (El y_abZu) :* NP0))))
                 -> El ((GoForRange y_abZt) y_abZu)
               _ -> error "matchAll"
        IdxMaybeGoSimp
          -> \case
               (Rep (Pat46Nothing NP0)) -> El Nothing
               (Rep (Pat46Just (NA_I (El y_abZv) :* NP0))) -> El (Just y_abZv)
               _ -> error "matchAll"
        IdxMaybeGoExpr
          -> \case
               (Rep (Pat47Nothing NP0)) -> El Nothing
               (Rep (Pat47Just (NA_I (El y_abZw) :* NP0))) -> El (Just y_abZw)
               _ -> error "matchAll"
        IdxGoCaseGoChan
          -> \case
               (Rep (Pat48GoCase (NA_I (El y_abZx) :* (NA_I (El y_abZy) :* NP0))))
                 -> El ((GoCase y_abZx) y_abZy)
               (Rep (Pat48GoDefault (NA_I (El y_abZz) :* NP0)))
                 -> El (GoDefault y_abZz)
               _ -> error "matchAll"
        IdxListGoChan
          -> \case
               (Rep (Pat499193 NP0)) -> El []
               (Rep (Pat4958 (NA_I (El y_abZA) :* (NA_I (El y_abZB) :* NP0))))
                 -> El (((:) y_abZA) y_abZB)
               _ -> error "matchAll"
        IdxGoChan
          -> \case
               (Rep (Pat50GoChanRecv (NA_I (El y_abZC) :* (NA_I (El y_abZD) :* NP0))))
                 -> El ((GoChanRecv y_abZC) y_abZD)
               (Rep (Pat50GoChanSend (NA_I (El y_abZE) :* (NA_I (El y_abZF) :* NP0))))
                 -> El ((GoChanSend y_abZE) y_abZF)
               _ -> error "matchAll"
        IdxMaybeGoChanInner
          -> \case
               (Rep (Pat51Nothing NP0)) -> El Nothing
               (Rep (Pat51Just (NA_I (El y_abZG) :* NP0))) -> El (Just y_abZG)
               _ -> error "matchAll"
        IdxGoChanInner
          -> \case
               (Rep (Pat52GoChanInner (NA_I (El y_abZH) :* (NA_I (El y_abZI) :* NP0))))
                 -> El ((GoChanInner y_abZH) y_abZI)
               _ -> error "matchAll"
        IdxGoCaseGoExpr
          -> \case
               (Rep (Pat53GoCase (NA_I (El y_abZJ) :* (NA_I (El y_abZK) :* NP0))))
                 -> El ((GoCase y_abZJ) y_abZK)
               (Rep (Pat53GoDefault (NA_I (El y_abZL) :* NP0)))
                 -> El (GoDefault y_abZL)
               _ -> error "matchAll"
        IdxGoCaseGoType
          -> \case
               (Rep (Pat54GoCase (NA_I (El y_abZM) :* (NA_I (El y_abZN) :* NP0))))
                 -> El ((GoCase y_abZM) y_abZN)
               (Rep (Pat54GoDefault (NA_I (El y_abZO) :* NP0)))
                 -> El (GoDefault y_abZO)
               _ -> error "matchAll"
        IdxListGoType
          -> \case
               (Rep (Pat559193 NP0)) -> El []
               (Rep (Pat5558 (NA_I (El y_abZP) :* (NA_I (El y_abZQ) :* NP0))))
                 -> El (((:) y_abZP) y_abZQ)
               _ -> error "matchAll"
        IdxGoMethSpec
          -> \case
               (Rep (Pat56GoMethSpec (NA_I (El y_abZR) :* (NA_I (El y_abZS) :* NP0))))
                 -> El ((GoMethSpec y_abZR) y_abZS)
               (Rep (Pat56GoInterface (NA_I (El y_abZT) :* NP0)))
                 -> El (GoInterface y_abZT)
               _ -> error "matchAll"
        IdxGoFieldType
          -> \case
               (Rep (Pat57GoFieldType (NA_K (SString y_abZU) :* (NA_I (El y_abZV) :* (NA_I (El y_abZW) :* NP0)))))
                 -> El (((GoFieldType y_abZU) y_abZV) y_abZW)
               (Rep (Pat57GoFieldAnon (NA_K (SString y_abZX) :* (NA_K (SBool y_abZY) :* (NA_I (El y_abZZ) :* NP0)))))
                 -> El (((GoFieldAnon y_abZX) y_abZY) y_abZZ)
               _ -> error "matchAll"
        IdxGoTypeSpec
          -> \case
               (Rep (Pat58GoTypeSpec (NA_I (El y_ac00) :* (NA_I (El y_ac01) :* NP0))))
                 -> El ((GoTypeSpec y_ac00) y_ac01)
               _ -> error "matchAll"
        _ -> error "matchAll"
