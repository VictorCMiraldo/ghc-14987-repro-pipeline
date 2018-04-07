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
pattern Pat58GoTypeSpec ::
          PoA Singl (El FamGoSource) '[I D1_, I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D1_, I D18_]]
pattern Pat58GoTypeSpec d_aHiD = H d_aHiD
pattern Pat57GoFieldAnon ::
          PoA Singl (El FamGoSource) '[K KString, K KBool, I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[K KString, I D15_, I D18_],
                                               '[K KString, K KBool, I D18_]]
pattern Pat57GoFieldAnon d_aHiC = T (H d_aHiC)
pattern Pat57GoFieldType ::
          PoA Singl (El FamGoSource) '[K KString, I D15_, I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[K KString, I D15_, I D18_],
                                               '[K KString, K KBool, I D18_]]
pattern Pat57GoFieldType d_aHiB = H d_aHiB
pattern Pat56GoInterface ::
          PoA Singl (El FamGoSource) '[I D1_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D1_, I D21_], '[I D1_]]
pattern Pat56GoInterface d_aHiA = T (H d_aHiA)
pattern Pat56GoMethSpec ::
          PoA Singl (El FamGoSource) '[I D1_, I D21_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D1_, I D21_], '[I D1_]]
pattern Pat56GoMethSpec d_aHiz = H d_aHiz
pattern Pat5558 ::
          PoA Singl (El FamGoSource) '[I D18_, I D55_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D18_, I D55_]]
pattern Pat5558 d_aHiy = T (H d_aHiy)
pattern Pat559193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D18_, I D55_]]
pattern Pat559193 d_aHix = H d_aHix
pattern Pat54GoDefault ::
          PoA Singl (El FamGoSource) '[I D36_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D55_, I D36_], '[I D36_]]
pattern Pat54GoDefault d_aHiw = T (H d_aHiw)
pattern Pat54GoCase ::
          PoA Singl (El FamGoSource) '[I D55_, I D36_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D55_, I D36_], '[I D36_]]
pattern Pat54GoCase d_aHiv = H d_aHiv
pattern Pat53GoDefault ::
          PoA Singl (El FamGoSource) '[I D36_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D17_, I D36_], '[I D36_]]
pattern Pat53GoDefault d_aHiu = T (H d_aHiu)
pattern Pat53GoCase ::
          PoA Singl (El FamGoSource) '[I D17_, I D36_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D17_, I D36_], '[I D36_]]
pattern Pat53GoCase d_aHit = H d_aHit
pattern Pat52GoChanInner ::
          PoA Singl (El FamGoSource) '[I D19_, I D8_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D19_, I D8_]]
pattern Pat52GoChanInner d_aHis = H d_aHis
pattern Pat51Just ::
          PoA Singl (El FamGoSource) '[I D52_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D52_]]
pattern Pat51Just d_aHir = T (H d_aHir)
pattern Pat51Nothing ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D52_]]
pattern Pat51Nothing d_aHiq = H d_aHiq
pattern Pat50GoChanSend ::
          PoA Singl (El FamGoSource) '[I D19_, I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D51_, I D19_],
                                               '[I D19_, I D19_]]
pattern Pat50GoChanSend d_aHip = T (H d_aHip)
pattern Pat50GoChanRecv ::
          PoA Singl (El FamGoSource) '[I D51_, I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D51_, I D19_],
                                               '[I D19_, I D19_]]
pattern Pat50GoChanRecv d_aHio = H d_aHio
pattern Pat4958 ::
          PoA Singl (El FamGoSource) '[I D50_, I D49_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D50_, I D49_]]
pattern Pat4958 d_aHin = T (H d_aHin)
pattern Pat499193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D50_, I D49_]]
pattern Pat499193 d_aHim = H d_aHim
pattern Pat48GoDefault ::
          PoA Singl (El FamGoSource) '[I D36_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D49_, I D36_], '[I D36_]]
pattern Pat48GoDefault d_aHil = T (H d_aHil)
pattern Pat48GoCase ::
          PoA Singl (El FamGoSource) '[I D49_, I D36_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D49_, I D36_], '[I D36_]]
pattern Pat48GoCase d_aHik = H d_aHik
pattern Pat47Just ::
          PoA Singl (El FamGoSource) '[I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D19_]]
pattern Pat47Just d_aHij = T (H d_aHij)
pattern Pat47Nothing ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D19_]]
pattern Pat47Nothing d_aHii = H d_aHii
pattern Pat46Just ::
          PoA Singl (El FamGoSource) '[I D38_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D38_]]
pattern Pat46Just d_aHih = T (H d_aHih)
pattern Pat46Nothing ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D38_]]
pattern Pat46Nothing d_aHig = H d_aHig
pattern Pat45GoForRange ::
          PoA Singl (El FamGoSource) '[I D17_, I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D19_],
                                               '[I D38_, I D47_, I D38_],
                                               '[I D17_, I D19_]]
pattern Pat45GoForRange d_aHif = T (T (H d_aHif))
pattern Pat45GoForThree ::
          PoA Singl (El FamGoSource) '[I D38_, I D47_, I D38_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D19_],
                                               '[I D38_, I D47_, I D38_],
                                               '[I D17_, I D19_]]
pattern Pat45GoForThree d_aHie = T (H d_aHie)
pattern Pat45GoForWhile ::
          PoA Singl (El FamGoSource) '[I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D19_],
                                               '[I D38_, I D47_, I D38_],
                                               '[I D17_, I D19_]]
pattern Pat45GoForWhile d_aHid = H d_aHid
pattern Pat4458 ::
          PoA Singl (El FamGoSource) '[I D54_, I D44_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D54_, I D44_]]
pattern Pat4458 d_aHic = T (H d_aHic)
pattern Pat449193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D54_, I D44_]]
pattern Pat449193 d_aHib = H d_aHib
pattern Pat4358 ::
          PoA Singl (El FamGoSource) '[I D53_, I D43_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D53_, I D43_]]
pattern Pat4358 d_aHia = T (H d_aHia)
pattern Pat439193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D53_, I D43_]]
pattern Pat439193 d_aHi9 = H d_aHi9
pattern Pat4258 ::
          PoA Singl (El FamGoSource) '[I D48_, I D42_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D48_, I D42_]]
pattern Pat4258 d_aHi8 = T (H d_aHi8)
pattern Pat429193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D48_, I D42_]]
pattern Pat429193 d_aHi7 = H d_aHi7
pattern Pat41Just ::
          PoA Singl (El FamGoSource) '[I D37_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D37_]]
pattern Pat41Just d_aHi6 = T (H d_aHi6)
pattern Pat41Nothing ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D37_]]
pattern Pat41Nothing d_aHi5 = H d_aHi5
pattern Pat40GoCond ::
          PoA Singl (El FamGoSource) '[I D46_, I D47_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D46_, I D47_]]
pattern Pat40GoCond d_aHi4 = H d_aHi4
pattern Pat39Just ::
          PoA Singl (El FamGoSource) '[I D1_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D1_]]
pattern Pat39Just d_aHi3 = T (H d_aHi3)
pattern Pat39Nothing ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D1_]]
pattern Pat39Nothing d_aHi2 = H d_aHi2
pattern Pat38GoSimpVar ::
          PoA Singl (El FamGoSource) '[I D15_, I D17_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[],
                                               '[I D19_],
                                               '[I D19_, I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D17_, I D8_, I D17_],
                                               '[I D15_, I D17_]]
pattern Pat38GoSimpVar d_aHi1 = T (T (T (T (T (T (T (H d_aHi1)))))))
pattern Pat38GoSimpAsn ::
          PoA Singl (El FamGoSource) '[I D17_, I D8_, I D17_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[],
                                               '[I D19_],
                                               '[I D19_, I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D17_, I D8_, I D17_],
                                               '[I D15_, I D17_]]
pattern Pat38GoSimpAsn d_aHi0 = T (T (T (T (T (T (H d_aHi0))))))
pattern Pat38GoSimpDec ::
          PoA Singl (El FamGoSource) '[I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[],
                                               '[I D19_],
                                               '[I D19_, I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D17_, I D8_, I D17_],
                                               '[I D15_, I D17_]]
pattern Pat38GoSimpDec d_aHhZ = T (T (T (T (T (H d_aHhZ)))))
pattern Pat38GoSimpInc ::
          PoA Singl (El FamGoSource) '[I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[],
                                               '[I D19_],
                                               '[I D19_, I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D17_, I D8_, I D17_],
                                               '[I D15_, I D17_]]
pattern Pat38GoSimpInc d_aHhY = T (T (T (T (H d_aHhY))))
pattern Pat38GoSimpExpr ::
          PoA Singl (El FamGoSource) '[I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[],
                                               '[I D19_],
                                               '[I D19_, I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D17_, I D8_, I D17_],
                                               '[I D15_, I D17_]]
pattern Pat38GoSimpExpr d_aHhX = T (T (T (H d_aHhX)))
pattern Pat38GoSimpSend ::
          PoA Singl (El FamGoSource) '[I D19_, I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[],
                                               '[I D19_],
                                               '[I D19_, I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D17_, I D8_, I D17_],
                                               '[I D15_, I D17_]]
pattern Pat38GoSimpSend d_aHhW = T (T (H d_aHhW))
pattern Pat38GoSimpRecv ::
          PoA Singl (El FamGoSource) '[I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[],
                                               '[I D19_],
                                               '[I D19_, I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D17_, I D8_, I D17_],
                                               '[I D15_, I D17_]]
pattern Pat38GoSimpRecv d_aHhV = T (H d_aHhV)
pattern Pat38GoSimpEmpty ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[],
                                               '[I D19_],
                                               '[I D19_, I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D19_],
                                               '[I D17_, I D8_, I D17_],
                                               '[I D15_, I D17_]]
pattern Pat38GoSimpEmpty d_aHhU = H d_aHhU
pattern Pat37GoStmtDefer ::
          PoA Singl (El FamGoSource) '[I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtDefer d_aHhT = T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aHhT)))))))))))))))
pattern Pat37GoStmtFor ::
          PoA Singl (El FamGoSource) '[I D45_, I D33_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtFor d_aHhS = T (T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aHhS))))))))))))))
pattern Pat37GoStmtTypeSwitch ::
          PoA Singl (El FamGoSource) '[I D40_, I D44_, I D39_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtTypeSwitch d_aHhR = T (T (T (T (T (T (T (T (T (T (T (T (T (H d_aHhR)))))))))))))
pattern Pat37GoStmtSwitch ::
          PoA Singl (El FamGoSource) '[I D40_, I D43_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtSwitch d_aHhQ = T (T (T (T (T (T (T (T (T (T (T (T (H d_aHhQ))))))))))))
pattern Pat37GoStmtSelect ::
          PoA Singl (El FamGoSource) '[I D42_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtSelect d_aHhP = T (T (T (T (T (T (T (T (T (T (T (H d_aHhP)))))))))))
pattern Pat37GoStmtIf ::
          PoA Singl (El FamGoSource) '[I D40_, I D33_, I D41_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtIf d_aHhO = T (T (T (T (T (T (T (T (T (T (H d_aHhO))))))))))
pattern Pat37GoStmtBlock ::
          PoA Singl (El FamGoSource) '[I D33_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtBlock d_aHhN = T (T (T (T (T (T (T (T (T (H d_aHhN)))))))))
pattern Pat37GoStmtFallthrough ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtFallthrough d_aHhM = T (T (T (T (T (T (T (T (H d_aHhM))))))))
pattern Pat37GoStmtGoto ::
          PoA Singl (El FamGoSource) '[I D1_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtGoto d_aHhL = T (T (T (T (T (T (T (H d_aHhL)))))))
pattern Pat37GoStmtContinue ::
          PoA Singl (El FamGoSource) '[I D39_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtContinue d_aHhK = T (T (T (T (T (T (H d_aHhK))))))
pattern Pat37GoStmtBreak ::
          PoA Singl (El FamGoSource) '[I D39_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtBreak d_aHhJ = T (T (T (T (T (H d_aHhJ)))))
pattern Pat37GoStmtReturn ::
          PoA Singl (El FamGoSource) '[I D17_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtReturn d_aHhI = T (T (T (T (H d_aHhI))))
pattern Pat37GoStmtGo ::
          PoA Singl (El FamGoSource) '[I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtGo d_aHhH = T (T (T (H d_aHhH)))
pattern Pat37GoStmtSimple ::
          PoA Singl (El FamGoSource) '[I D38_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtSimple d_aHhG = T (T (H d_aHhG))
pattern Pat37GoStmtLabeled ::
          PoA Singl (El FamGoSource) '[I D1_, I D37_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtLabeled d_aHhF = T (H d_aHhF)
pattern Pat37GoStmtDecl ::
          PoA Singl (El FamGoSource) '[I D9_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D9_],
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
                                               '[I D19_]]
pattern Pat37GoStmtDecl d_aHhE = H d_aHhE
pattern Pat3658 ::
          PoA Singl (El FamGoSource) '[I D37_, I D36_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D37_, I D36_]]
pattern Pat3658 d_aHhD = T (H d_aHhD)
pattern Pat369193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D37_, I D36_]]
pattern Pat369193 d_aHhC = H d_aHhC
pattern Pat35GoParam ::
          PoA Singl (El FamGoSource) '[I D15_, I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D15_, I D18_]]
pattern Pat35GoParam d_aHhB = H d_aHhB
pattern Pat3458 ::
          PoA Singl (El FamGoSource) '[I D35_, I D34_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D35_, I D34_]]
pattern Pat3458 d_aHhA = T (H d_aHhA)
pattern Pat349193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D35_, I D34_]]
pattern Pat349193 d_aHhz = H d_aHhz
pattern Pat33GoNoBlock ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D36_], '[]]
pattern Pat33GoNoBlock d_aHhy = T (H d_aHhy)
pattern Pat33GoBlock ::
          PoA Singl (El FamGoSource) '[I D36_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D36_], '[]]
pattern Pat33GoBlock d_aHhx = H d_aHhx
pattern Pat32GoValueComp ::
          PoA Singl (El FamGoSource) '[I D27_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D19_], '[I D27_]]
pattern Pat32GoValueComp d_aHhw = T (H d_aHhw)
pattern Pat32GoValueExpr ::
          PoA Singl (El FamGoSource) '[I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D19_], '[I D27_]]
pattern Pat32GoValueExpr d_aHhv = H d_aHhv
pattern Pat31GoKeyIndex ::
          PoA Singl (El FamGoSource) '[I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D1_], '[I D19_]]
pattern Pat31GoKeyIndex d_aHhu = T (T (H d_aHhu))
pattern Pat31GoKeyField ::
          PoA Singl (El FamGoSource) '[I D1_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D1_], '[I D19_]]
pattern Pat31GoKeyField d_aHht = T (H d_aHht)
pattern Pat31GoKeyNone ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D1_], '[I D19_]]
pattern Pat31GoKeyNone d_aHhs = H d_aHhs
pattern Pat30GoElement ::
          PoA Singl (El FamGoSource) '[I D31_, I D32_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D31_, I D32_]]
pattern Pat30GoElement d_aHhr = H d_aHhr
pattern Pat2958 ::
          PoA Singl (El FamGoSource) '[I D30_, I D29_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D30_, I D29_]]
pattern Pat2958 d_aHhq = T (H d_aHhq)
pattern Pat299193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D30_, I D29_]]
pattern Pat299193 d_aHhp = H d_aHhp
pattern Pat28GoFuncExpr ::
          PoA Singl (El FamGoSource) '[I D21_, I D33_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D21_, I D33_]]
pattern Pat28GoFuncExpr d_aHho = H d_aHho
pattern Pat27GoComp ::
          PoA Singl (El FamGoSource) '[I D29_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D29_]]
pattern Pat27GoComp d_aHhn = H d_aHhn
pattern Pat26GoRec ::
          PoA Singl (El FamGoSource) '[K KBool, I D39_, I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[K KBool, I D39_, I D18_]]
pattern Pat26GoRec d_aHhm = H d_aHhm
pattern Pat25GoLitFunc ::
          PoA Singl (El FamGoSource) '[I D28_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[K KString, K KInteger],
                                               '[K KString, K KFloat],
                                               '[K KString, K KFloat],
                                               '[K KString, K KChar],
                                               '[K KString, K KString],
                                               '[I D18_, I D27_],
                                               '[I D28_]]
pattern Pat25GoLitFunc d_aHhl = T (T (T (T (T (T (H d_aHhl))))))
pattern Pat25GoLitComp ::
          PoA Singl (El FamGoSource) '[I D18_, I D27_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[K KString, K KInteger],
                                               '[K KString, K KFloat],
                                               '[K KString, K KFloat],
                                               '[K KString, K KChar],
                                               '[K KString, K KString],
                                               '[I D18_, I D27_],
                                               '[I D28_]]
pattern Pat25GoLitComp d_aHhk = T (T (T (T (T (H d_aHhk)))))
pattern Pat25GoLitStr ::
          PoA Singl (El FamGoSource) '[K KString, K KString]
          -> NS (PoA Singl (El FamGoSource)) '[ '[K KString, K KInteger],
                                               '[K KString, K KFloat],
                                               '[K KString, K KFloat],
                                               '[K KString, K KChar],
                                               '[K KString, K KString],
                                               '[I D18_, I D27_],
                                               '[I D28_]]
pattern Pat25GoLitStr d_aHhj = T (T (T (T (H d_aHhj))))
pattern Pat25GoLitChar ::
          PoA Singl (El FamGoSource) '[K KString, K KChar]
          -> NS (PoA Singl (El FamGoSource)) '[ '[K KString, K KInteger],
                                               '[K KString, K KFloat],
                                               '[K KString, K KFloat],
                                               '[K KString, K KChar],
                                               '[K KString, K KString],
                                               '[I D18_, I D27_],
                                               '[I D28_]]
pattern Pat25GoLitChar d_aHhi = T (T (T (H d_aHhi)))
pattern Pat25GoLitImag ::
          PoA Singl (El FamGoSource) '[K KString, K KFloat]
          -> NS (PoA Singl (El FamGoSource)) '[ '[K KString, K KInteger],
                                               '[K KString, K KFloat],
                                               '[K KString, K KFloat],
                                               '[K KString, K KChar],
                                               '[K KString, K KString],
                                               '[I D18_, I D27_],
                                               '[I D28_]]
pattern Pat25GoLitImag d_aHhh = T (T (H d_aHhh))
pattern Pat25GoLitReal ::
          PoA Singl (El FamGoSource) '[K KString, K KFloat]
          -> NS (PoA Singl (El FamGoSource)) '[ '[K KString, K KInteger],
                                               '[K KString, K KFloat],
                                               '[K KString, K KFloat],
                                               '[K KString, K KChar],
                                               '[K KString, K KString],
                                               '[I D18_, I D27_],
                                               '[I D28_]]
pattern Pat25GoLitReal d_aHhg = T (H d_aHhg)
pattern Pat25GoLitInt ::
          PoA Singl (El FamGoSource) '[K KString, K KInteger]
          -> NS (PoA Singl (El FamGoSource)) '[ '[K KString, K KInteger],
                                               '[K KString, K KFloat],
                                               '[K KString, K KFloat],
                                               '[K KString, K KChar],
                                               '[K KString, K KString],
                                               '[I D18_, I D27_],
                                               '[I D28_]]
pattern Pat25GoLitInt d_aHhf = H d_aHhf
pattern Pat24GoCall ::
          PoA Singl (El FamGoSource) '[I D24_, I D17_, K KBool]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D25_],
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
                                               '[I D24_, I D17_, K KBool]]
pattern Pat24GoCall d_aHhe = T (T (T (T (T (T (T (T (T (T (T (H d_aHhe)))))))))))
pattern Pat24GoTA ::
          PoA Singl (El FamGoSource) '[I D24_, I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D25_],
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
                                               '[I D24_, I D17_, K KBool]]
pattern Pat24GoTA d_aHhd = T (T (T (T (T (T (T (T (T (T (H d_aHhd))))))))))
pattern Pat24GoSlice ::
          PoA Singl (El FamGoSource) '[I D24_, I D17_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D25_],
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
                                               '[I D24_, I D17_, K KBool]]
pattern Pat24GoSlice d_aHhc = T (T (T (T (T (T (T (T (T (H d_aHhc)))))))))
pattern Pat24GoIndex ::
          PoA Singl (El FamGoSource) '[I D24_, I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D25_],
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
                                               '[I D24_, I D17_, K KBool]]
pattern Pat24GoIndex d_aHhb = T (T (T (T (T (T (T (T (H d_aHhb))))))))
pattern Pat24GoSelect ::
          PoA Singl (El FamGoSource) '[I D24_, I D1_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D25_],
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
                                               '[I D24_, I D17_, K KBool]]
pattern Pat24GoSelect d_aHha = T (T (T (T (T (T (T (H d_aHha)))))))
pattern Pat24GoMake ::
          PoA Singl (El FamGoSource) '[I D18_, I D17_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D25_],
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
                                               '[I D24_, I D17_, K KBool]]
pattern Pat24GoMake d_aHh9 = T (T (T (T (T (T (H d_aHh9))))))
pattern Pat24GoNew ::
          PoA Singl (El FamGoSource) '[I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D25_],
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
                                               '[I D24_, I D17_, K KBool]]
pattern Pat24GoNew d_aHh8 = T (T (T (T (T (H d_aHh8)))))
pattern Pat24GoCast ::
          PoA Singl (El FamGoSource) '[I D18_, I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D25_],
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
                                               '[I D24_, I D17_, K KBool]]
pattern Pat24GoCast d_aHh7 = T (T (T (T (H d_aHh7))))
pattern Pat24GoParen ::
          PoA Singl (El FamGoSource) '[I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D25_],
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
                                               '[I D24_, I D17_, K KBool]]
pattern Pat24GoParen d_aHh6 = T (T (T (H d_aHh6)))
pattern Pat24GoMethod ::
          PoA Singl (El FamGoSource) '[I D26_, I D1_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D25_],
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
                                               '[I D24_, I D17_, K KBool]]
pattern Pat24GoMethod d_aHh5 = T (T (H d_aHh5))
pattern Pat24GoQual ::
          PoA Singl (El FamGoSource) '[I D15_, I D1_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D25_],
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
                                               '[I D24_, I D17_, K KBool]]
pattern Pat24GoQual d_aHh4 = T (H d_aHh4)
pattern Pat24GoLiteral ::
          PoA Singl (El FamGoSource) '[I D25_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D25_],
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
                                               '[I D24_, I D17_, K KBool]]
pattern Pat24GoLiteral d_aHh3 = H d_aHh3
pattern Pat2358 ::
          PoA Singl (El FamGoSource) '[I D57_, I D23_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D57_, I D23_]]
pattern Pat2358 d_aHh2 = T (H d_aHh2)
pattern Pat239193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D57_, I D23_]]
pattern Pat239193 d_aHh1 = H d_aHh1
pattern Pat2258 ::
          PoA Singl (El FamGoSource) '[I D56_, I D22_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D56_, I D22_]]
pattern Pat2258 d_aHh0 = T (H d_aHh0)
pattern Pat229193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D56_, I D22_]]
pattern Pat229193 d_aHgZ = H d_aHgZ
pattern Pat21GoSig ::
          PoA Singl (El FamGoSource) '[I D34_, I D34_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D34_, I D34_]]
pattern Pat21GoSig d_aHgY = H d_aHgY
pattern Pat20GoIOChan ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[], '[]]
pattern Pat20GoIOChan d_aHgX = T (T (H d_aHgX))
pattern Pat20GoOChan ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[], '[]]
pattern Pat20GoOChan d_aHgW = T (H d_aHgW)
pattern Pat20GoIChan ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[], '[]]
pattern Pat20GoIChan d_aHgV = H d_aHgV
pattern Pat19Go2Op ::
          PoA Singl (El FamGoSource) '[I D8_, I D19_, I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D24_],
                                               '[I D8_, I D19_],
                                               '[I D8_, I D19_, I D19_]]
pattern Pat19Go2Op d_aHgU = T (T (H d_aHgU))
pattern Pat19Go1Op ::
          PoA Singl (El FamGoSource) '[I D8_, I D19_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D24_],
                                               '[I D8_, I D19_],
                                               '[I D8_, I D19_, I D19_]]
pattern Pat19Go1Op d_aHgT = T (H d_aHgT)
pattern Pat19GoPrim ::
          PoA Singl (El FamGoSource) '[I D24_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D24_],
                                               '[I D8_, I D19_],
                                               '[I D8_, I D19_, I D19_]]
pattern Pat19GoPrim d_aHgS = H d_aHgS
pattern Pat18GoStructType ::
          PoA Singl (El FamGoSource) '[I D23_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D15_, I D1_],
                                               '[I D19_, I D18_],
                                               '[I D20_, I D18_],
                                               '[I D18_],
                                               '[I D21_],
                                               '[I D22_],
                                               '[I D18_, I D18_],
                                               '[I D18_],
                                               '[I D18_],
                                               '[I D23_]]
pattern Pat18GoStructType d_aHgR = T (T (T (T (T (T (T (T (T (H d_aHgR)))))))))
pattern Pat18GoSliceType ::
          PoA Singl (El FamGoSource) '[I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D15_, I D1_],
                                               '[I D19_, I D18_],
                                               '[I D20_, I D18_],
                                               '[I D18_],
                                               '[I D21_],
                                               '[I D22_],
                                               '[I D18_, I D18_],
                                               '[I D18_],
                                               '[I D18_],
                                               '[I D23_]]
pattern Pat18GoSliceType d_aHgQ = T (T (T (T (T (T (T (T (H d_aHgQ))))))))
pattern Pat18GoPointerType ::
          PoA Singl (El FamGoSource) '[I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D15_, I D1_],
                                               '[I D19_, I D18_],
                                               '[I D20_, I D18_],
                                               '[I D18_],
                                               '[I D21_],
                                               '[I D22_],
                                               '[I D18_, I D18_],
                                               '[I D18_],
                                               '[I D18_],
                                               '[I D23_]]
pattern Pat18GoPointerType d_aHgP = T (T (T (T (T (T (T (H d_aHgP)))))))
pattern Pat18GoMapType ::
          PoA Singl (El FamGoSource) '[I D18_, I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D15_, I D1_],
                                               '[I D19_, I D18_],
                                               '[I D20_, I D18_],
                                               '[I D18_],
                                               '[I D21_],
                                               '[I D22_],
                                               '[I D18_, I D18_],
                                               '[I D18_],
                                               '[I D18_],
                                               '[I D23_]]
pattern Pat18GoMapType d_aHgO = T (T (T (T (T (T (H d_aHgO))))))
pattern Pat18GoInterfaceType ::
          PoA Singl (El FamGoSource) '[I D22_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D15_, I D1_],
                                               '[I D19_, I D18_],
                                               '[I D20_, I D18_],
                                               '[I D18_],
                                               '[I D21_],
                                               '[I D22_],
                                               '[I D18_, I D18_],
                                               '[I D18_],
                                               '[I D18_],
                                               '[I D23_]]
pattern Pat18GoInterfaceType d_aHgN = T (T (T (T (T (H d_aHgN)))))
pattern Pat18GoFunctionType ::
          PoA Singl (El FamGoSource) '[I D21_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D15_, I D1_],
                                               '[I D19_, I D18_],
                                               '[I D20_, I D18_],
                                               '[I D18_],
                                               '[I D21_],
                                               '[I D22_],
                                               '[I D18_, I D18_],
                                               '[I D18_],
                                               '[I D18_],
                                               '[I D23_]]
pattern Pat18GoFunctionType d_aHgM = T (T (T (T (H d_aHgM))))
pattern Pat18GoElipsisType ::
          PoA Singl (El FamGoSource) '[I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D15_, I D1_],
                                               '[I D19_, I D18_],
                                               '[I D20_, I D18_],
                                               '[I D18_],
                                               '[I D21_],
                                               '[I D22_],
                                               '[I D18_, I D18_],
                                               '[I D18_],
                                               '[I D18_],
                                               '[I D23_]]
pattern Pat18GoElipsisType d_aHgL = T (T (T (H d_aHgL)))
pattern Pat18GoChannelType ::
          PoA Singl (El FamGoSource) '[I D20_, I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D15_, I D1_],
                                               '[I D19_, I D18_],
                                               '[I D20_, I D18_],
                                               '[I D18_],
                                               '[I D21_],
                                               '[I D22_],
                                               '[I D18_, I D18_],
                                               '[I D18_],
                                               '[I D18_],
                                               '[I D23_]]
pattern Pat18GoChannelType d_aHgK = T (T (H d_aHgK))
pattern Pat18GoArrayType ::
          PoA Singl (El FamGoSource) '[I D19_, I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D15_, I D1_],
                                               '[I D19_, I D18_],
                                               '[I D20_, I D18_],
                                               '[I D18_],
                                               '[I D21_],
                                               '[I D22_],
                                               '[I D18_, I D18_],
                                               '[I D18_],
                                               '[I D18_],
                                               '[I D23_]]
pattern Pat18GoArrayType d_aHgJ = T (H d_aHgJ)
pattern Pat18GoTypeName ::
          PoA Singl (El FamGoSource) '[I D15_, I D1_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D15_, I D1_],
                                               '[I D19_, I D18_],
                                               '[I D20_, I D18_],
                                               '[I D18_],
                                               '[I D21_],
                                               '[I D22_],
                                               '[I D18_, I D18_],
                                               '[I D18_],
                                               '[I D18_],
                                               '[I D23_]]
pattern Pat18GoTypeName d_aHgI = H d_aHgI
pattern Pat1758 ::
          PoA Singl (El FamGoSource) '[I D19_, I D17_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D19_, I D17_]]
pattern Pat1758 d_aHgH = T (H d_aHgH)
pattern Pat179193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D19_, I D17_]]
pattern Pat179193 d_aHgG = H d_aHgG
pattern Pat16Just ::
          PoA Singl (El FamGoSource) '[I D18_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D18_]]
pattern Pat16Just d_aHgF = T (H d_aHgF)
pattern Pat16Nothing ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D18_]]
pattern Pat16Nothing d_aHgE = H d_aHgE
pattern Pat1558 ::
          PoA Singl (El FamGoSource) '[I D1_, I D15_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D1_, I D15_]]
pattern Pat1558 d_aHgD = T (H d_aHgD)
pattern Pat159193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D1_, I D15_]]
pattern Pat159193 d_aHgC = H d_aHgC
pattern Pat14GoCVSpec ::
          PoA Singl (El FamGoSource) '[I D15_, I D16_, I D17_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D15_, I D16_, I D17_]]
pattern Pat14GoCVSpec d_aHgB = H d_aHgB
pattern Pat13GoMethDecl ::
          PoA Singl (El FamGoSource) '[I D26_, I D1_, I D21_, I D33_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D26_,
                                                 I D1_,
                                                 I D21_,
                                                 I D33_]]
pattern Pat13GoMethDecl d_aHgA = H d_aHgA
pattern Pat12GoFuncDecl ::
          PoA Singl (El FamGoSource) '[I D1_, I D21_, I D33_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D1_, I D21_, I D33_]]
pattern Pat12GoFuncDecl d_aHgz = H d_aHgz
pattern Pat1158 ::
          PoA Singl (El FamGoSource) '[I D58_, I D11_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D58_, I D11_]]
pattern Pat1158 d_aHgy = T (H d_aHgy)
pattern Pat119193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D58_, I D11_]]
pattern Pat119193 d_aHgx = H d_aHgx
pattern Pat1058 ::
          PoA Singl (El FamGoSource) '[I D14_, I D10_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D14_, I D10_]]
pattern Pat1058 d_aHgw = T (H d_aHgw)
pattern Pat109193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D14_, I D10_]]
pattern Pat109193 d_aHgv = H d_aHgv
pattern Pat9GoMeth ::
          PoA Singl (El FamGoSource) '[I D13_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D10_],
                                               '[I D11_],
                                               '[I D10_],
                                               '[I D12_],
                                               '[I D13_]]
pattern Pat9GoMeth d_aHgu = T (T (T (T (H d_aHgu))))
pattern Pat9GoFunc ::
          PoA Singl (El FamGoSource) '[I D12_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D10_],
                                               '[I D11_],
                                               '[I D10_],
                                               '[I D12_],
                                               '[I D13_]]
pattern Pat9GoFunc d_aHgt = T (T (T (H d_aHgt)))
pattern Pat9GoVar ::
          PoA Singl (El FamGoSource) '[I D10_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D10_],
                                               '[I D11_],
                                               '[I D10_],
                                               '[I D12_],
                                               '[I D13_]]
pattern Pat9GoVar d_aHgs = T (T (H d_aHgs))
pattern Pat9GoType ::
          PoA Singl (El FamGoSource) '[I D11_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D10_],
                                               '[I D11_],
                                               '[I D10_],
                                               '[I D12_],
                                               '[I D13_]]
pattern Pat9GoType d_aHgr = T (H d_aHgr)
pattern Pat9GoConst ::
          PoA Singl (El FamGoSource) '[I D10_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D10_],
                                               '[I D11_],
                                               '[I D10_],
                                               '[I D12_],
                                               '[I D13_]]
pattern Pat9GoConst d_aHgq = H d_aHgq
pattern Pat8GoOp ::
          PoA Singl (El FamGoSource) '[K KString]
          -> NS (PoA Singl (El FamGoSource)) '[ '[K KString]]
pattern Pat8GoOp d_aHgp = H d_aHgp
pattern Pat7GoImpQual ::
          PoA Singl (El FamGoSource) '[I D1_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D8_], '[I D1_]]
pattern Pat7GoImpQual d_aHgo = T (T (H d_aHgo))
pattern Pat7GoImpDot ::
          PoA Singl (El FamGoSource) '[I D8_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D8_], '[I D1_]]
pattern Pat7GoImpDot d_aHgn = T (H d_aHgn)
pattern Pat7GoImp ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D8_], '[I D1_]]
pattern Pat7GoImp d_aHgm = H d_aHgm
pattern Pat6GoImpSpec ::
          PoA Singl (El FamGoSource) '[I D7_, K KString]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D7_, K KString]]
pattern Pat6GoImpSpec d_aHgl = H d_aHgl
pattern Pat558 ::
          PoA Singl (El FamGoSource) '[I D6_, I D5_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D6_, I D5_]]
pattern Pat558 d_aHgk = T (H d_aHgk)
pattern Pat59193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D6_, I D5_]]
pattern Pat59193 d_aHgj = H d_aHgj
pattern Pat4GoIfPrel ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D5_],
                                               '[K KString],
                                               '[],
                                               '[]]
pattern Pat4GoIfPrel d_aHgi = T (T (T (H d_aHgi)))
pattern Pat4GoDefine ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D5_],
                                               '[K KString],
                                               '[],
                                               '[]]
pattern Pat4GoDefine d_aHgh = T (T (H d_aHgh))
pattern Pat4GoPragma ::
          PoA Singl (El FamGoSource) '[K KString]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D5_],
                                               '[K KString],
                                               '[],
                                               '[]]
pattern Pat4GoPragma d_aHgg = T (H d_aHgg)
pattern Pat4GoImportDecl ::
          PoA Singl (El FamGoSource) '[I D5_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D5_],
                                               '[K KString],
                                               '[],
                                               '[]]
pattern Pat4GoImportDecl d_aHgf = H d_aHgf
pattern Pat358 ::
          PoA Singl (El FamGoSource) '[I D9_, I D3_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D9_, I D3_]]
pattern Pat358 d_aHge = T (H d_aHge)
pattern Pat39193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D9_, I D3_]]
pattern Pat39193 d_aHgd = H d_aHgd
pattern Pat258 ::
          PoA Singl (El FamGoSource) '[I D4_, I D2_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D4_, I D2_]]
pattern Pat258 d_aHgc = T (H d_aHgc)
pattern Pat29193 ::
          PoA Singl (El FamGoSource) '[]
          -> NS (PoA Singl (El FamGoSource)) '[ '[], '[I D4_, I D2_]]
pattern Pat29193 d_aHgb = H d_aHgb
pattern Pat1GoId ::
          PoA Singl (El FamGoSource) '[K KString]
          -> NS (PoA Singl (El FamGoSource)) '[ '[K KString]]
pattern Pat1GoId d_aHga = H d_aHga
pattern Pat0GoSource ::
          PoA Singl (El FamGoSource) '[I D1_, I D2_, I D3_]
          -> NS (PoA Singl (El FamGoSource)) '[ '[I D1_, I D2_, I D3_]]
pattern Pat0GoSource d_aHg9 = H d_aHg9
instance Family Singl FamGoSource CodesGoSource where
  sfrom'
    = \case
        IdxGoSource
          -> \case
               (El (GoSource x_aHiE x_aHiF x_aHiG))
                 -> Rep
                      (Pat0GoSource
                         ((NA_I (El x_aHiE))
                            :* ((NA_I (El x_aHiF)) :* ((NA_I (El x_aHiG)) :* NP0))))
        IdxGoId
          -> \case
               (El (GoId x_aHiH))
                 -> Rep (Pat1GoId ((NA_K (SString x_aHiH)) :* NP0))
        IdxListGoPrel
          -> \case
               (El []) -> Rep (Pat29193 NP0)
               (El ((:) x_aHiI x_aHiJ))
                 -> Rep (Pat258 ((NA_I (El x_aHiI)) :* ((NA_I (El x_aHiJ)) :* NP0)))
        IdxListGoDecl
          -> \case
               (El []) -> Rep (Pat39193 NP0)
               (El ((:) x_aHiK x_aHiL))
                 -> Rep (Pat358 ((NA_I (El x_aHiK)) :* ((NA_I (El x_aHiL)) :* NP0)))
        IdxGoPrel
          -> \case
               (El (GoImportDecl x_aHiM))
                 -> Rep (Pat4GoImportDecl ((NA_I (El x_aHiM)) :* NP0))
               (El (GoPragma x_aHiN))
                 -> Rep (Pat4GoPragma ((NA_K (SString x_aHiN)) :* NP0))
               (El GoDefine) -> Rep (Pat4GoDefine NP0)
               (El GoIfPrel) -> Rep (Pat4GoIfPrel NP0)
        IdxListGoImpSpec
          -> \case
               (El []) -> Rep (Pat59193 NP0)
               (El ((:) x_aHiO x_aHiP))
                 -> Rep (Pat558 ((NA_I (El x_aHiO)) :* ((NA_I (El x_aHiP)) :* NP0)))
        IdxGoImpSpec
          -> \case
               (El (GoImpSpec x_aHiQ x_aHiR))
                 -> Rep
                      (Pat6GoImpSpec
                         ((NA_I (El x_aHiQ)) :* ((NA_K (SString x_aHiR)) :* NP0)))
        IdxGoImpType
          -> \case
               (El GoImp) -> Rep (Pat7GoImp NP0)
               (El (GoImpDot x_aHiS))
                 -> Rep (Pat7GoImpDot ((NA_I (El x_aHiS)) :* NP0))
               (El (GoImpQual x_aHiT))
                 -> Rep (Pat7GoImpQual ((NA_I (El x_aHiT)) :* NP0))
        IdxGoOp
          -> \case
               (El (GoOp x_aHiU))
                 -> Rep (Pat8GoOp ((NA_K (SString x_aHiU)) :* NP0))
        IdxGoDecl
          -> \case
               (El (GoConst x_aHiV))
                 -> Rep (Pat9GoConst ((NA_I (El x_aHiV)) :* NP0))
               (El (GoType x_aHiW))
                 -> Rep (Pat9GoType ((NA_I (El x_aHiW)) :* NP0))
               (El (GoVar x_aHiX))
                 -> Rep (Pat9GoVar ((NA_I (El x_aHiX)) :* NP0))
               (El (GoFunc x_aHiY))
                 -> Rep (Pat9GoFunc ((NA_I (El x_aHiY)) :* NP0))
               (El (GoMeth x_aHiZ))
                 -> Rep (Pat9GoMeth ((NA_I (El x_aHiZ)) :* NP0))
        IdxListGoCVSpec
          -> \case
               (El []) -> Rep (Pat109193 NP0)
               (El ((:) x_aHj0 x_aHj1))
                 -> Rep
                      (Pat1058 ((NA_I (El x_aHj0)) :* ((NA_I (El x_aHj1)) :* NP0)))
        IdxListGoTypeSpec
          -> \case
               (El []) -> Rep (Pat119193 NP0)
               (El ((:) x_aHj2 x_aHj3))
                 -> Rep
                      (Pat1158 ((NA_I (El x_aHj2)) :* ((NA_I (El x_aHj3)) :* NP0)))
        IdxGoFuncDecl
          -> \case
               (El (GoFuncDecl x_aHj4 x_aHj5 x_aHj6))
                 -> Rep
                      (Pat12GoFuncDecl
                         ((NA_I (El x_aHj4))
                            :* ((NA_I (El x_aHj5)) :* ((NA_I (El x_aHj6)) :* NP0))))
        IdxGoMethDecl
          -> \case
               (El (GoMethDecl x_aHj7 x_aHj8 x_aHj9 x_aHja))
                 -> Rep
                      (Pat13GoMethDecl
                         ((NA_I (El x_aHj7))
                            :*
                              ((NA_I (El x_aHj8))
                                 :* ((NA_I (El x_aHj9)) :* ((NA_I (El x_aHja)) :* NP0)))))
        IdxGoCVSpec
          -> \case
               (El (GoCVSpec x_aHjb x_aHjc x_aHjd))
                 -> Rep
                      (Pat14GoCVSpec
                         ((NA_I (El x_aHjb))
                            :* ((NA_I (El x_aHjc)) :* ((NA_I (El x_aHjd)) :* NP0))))
        IdxListGoId
          -> \case
               (El []) -> Rep (Pat159193 NP0)
               (El ((:) x_aHje x_aHjf))
                 -> Rep
                      (Pat1558 ((NA_I (El x_aHje)) :* ((NA_I (El x_aHjf)) :* NP0)))
        IdxMaybeGoType
          -> \case
               (El Nothing) -> Rep (Pat16Nothing NP0)
               (El (Just x_aHjg)) -> Rep (Pat16Just ((NA_I (El x_aHjg)) :* NP0))
        IdxListGoExpr
          -> \case
               (El []) -> Rep (Pat179193 NP0)
               (El ((:) x_aHjh x_aHji))
                 -> Rep
                      (Pat1758 ((NA_I (El x_aHjh)) :* ((NA_I (El x_aHji)) :* NP0)))
        IdxGoType
          -> \case
               (El (GoTypeName x_aHjj x_aHjk))
                 -> Rep
                      (Pat18GoTypeName
                         ((NA_I (El x_aHjj)) :* ((NA_I (El x_aHjk)) :* NP0)))
               (El (GoArrayType x_aHjl x_aHjm))
                 -> Rep
                      (Pat18GoArrayType
                         ((NA_I (El x_aHjl)) :* ((NA_I (El x_aHjm)) :* NP0)))
               (El (GoChannelType x_aHjn x_aHjo))
                 -> Rep
                      (Pat18GoChannelType
                         ((NA_I (El x_aHjn)) :* ((NA_I (El x_aHjo)) :* NP0)))
               (El (GoElipsisType x_aHjp))
                 -> Rep (Pat18GoElipsisType ((NA_I (El x_aHjp)) :* NP0))
               (El (GoFunctionType x_aHjq))
                 -> Rep (Pat18GoFunctionType ((NA_I (El x_aHjq)) :* NP0))
               (El (GoInterfaceType x_aHjr))
                 -> Rep (Pat18GoInterfaceType ((NA_I (El x_aHjr)) :* NP0))
               (El (GoMapType x_aHjs x_aHjt))
                 -> Rep
                      (Pat18GoMapType
                         ((NA_I (El x_aHjs)) :* ((NA_I (El x_aHjt)) :* NP0)))
               (El (GoPointerType x_aHju))
                 -> Rep (Pat18GoPointerType ((NA_I (El x_aHju)) :* NP0))
               (El (GoSliceType x_aHjv))
                 -> Rep (Pat18GoSliceType ((NA_I (El x_aHjv)) :* NP0))
               (El (GoStructType x_aHjw))
                 -> Rep (Pat18GoStructType ((NA_I (El x_aHjw)) :* NP0))
        IdxGoExpr
          -> \case
               (El (GoPrim x_aHjx))
                 -> Rep (Pat19GoPrim ((NA_I (El x_aHjx)) :* NP0))
               (El (Go1Op x_aHjy x_aHjz))
                 -> Rep
                      (Pat19Go1Op ((NA_I (El x_aHjy)) :* ((NA_I (El x_aHjz)) :* NP0)))
               (El (Go2Op x_aHjA x_aHjB x_aHjC))
                 -> Rep
                      (Pat19Go2Op
                         ((NA_I (El x_aHjA))
                            :* ((NA_I (El x_aHjB)) :* ((NA_I (El x_aHjC)) :* NP0))))
        IdxGoChanKind
          -> \case
               (El GoIChan) -> Rep (Pat20GoIChan NP0)
               (El GoOChan) -> Rep (Pat20GoOChan NP0)
               (El GoIOChan) -> Rep (Pat20GoIOChan NP0)
        IdxGoSig
          -> \case
               (El (GoSig x_aHjD x_aHjE))
                 -> Rep
                      (Pat21GoSig ((NA_I (El x_aHjD)) :* ((NA_I (El x_aHjE)) :* NP0)))
        IdxListGoMethSpec
          -> \case
               (El []) -> Rep (Pat229193 NP0)
               (El ((:) x_aHjF x_aHjG))
                 -> Rep
                      (Pat2258 ((NA_I (El x_aHjF)) :* ((NA_I (El x_aHjG)) :* NP0)))
        IdxListGoFieldType
          -> \case
               (El []) -> Rep (Pat239193 NP0)
               (El ((:) x_aHjH x_aHjI))
                 -> Rep
                      (Pat2358 ((NA_I (El x_aHjH)) :* ((NA_I (El x_aHjI)) :* NP0)))
        IdxGoPrim
          -> \case
               (El (GoLiteral x_aHjJ))
                 -> Rep (Pat24GoLiteral ((NA_I (El x_aHjJ)) :* NP0))
               (El (GoQual x_aHjK x_aHjL))
                 -> Rep
                      (Pat24GoQual ((NA_I (El x_aHjK)) :* ((NA_I (El x_aHjL)) :* NP0)))
               (El (GoMethod x_aHjM x_aHjN))
                 -> Rep
                      (Pat24GoMethod ((NA_I (El x_aHjM)) :* ((NA_I (El x_aHjN)) :* NP0)))
               (El (GoParen x_aHjO))
                 -> Rep (Pat24GoParen ((NA_I (El x_aHjO)) :* NP0))
               (El (GoCast x_aHjP x_aHjQ))
                 -> Rep
                      (Pat24GoCast ((NA_I (El x_aHjP)) :* ((NA_I (El x_aHjQ)) :* NP0)))
               (El (GoNew x_aHjR))
                 -> Rep (Pat24GoNew ((NA_I (El x_aHjR)) :* NP0))
               (El (GoMake x_aHjS x_aHjT))
                 -> Rep
                      (Pat24GoMake ((NA_I (El x_aHjS)) :* ((NA_I (El x_aHjT)) :* NP0)))
               (El (GoSelect x_aHjU x_aHjV))
                 -> Rep
                      (Pat24GoSelect ((NA_I (El x_aHjU)) :* ((NA_I (El x_aHjV)) :* NP0)))
               (El (GoIndex x_aHjW x_aHjX))
                 -> Rep
                      (Pat24GoIndex ((NA_I (El x_aHjW)) :* ((NA_I (El x_aHjX)) :* NP0)))
               (El (GoSlice x_aHjY x_aHjZ))
                 -> Rep
                      (Pat24GoSlice ((NA_I (El x_aHjY)) :* ((NA_I (El x_aHjZ)) :* NP0)))
               (El (GoTA x_aHk0 x_aHk1))
                 -> Rep
                      (Pat24GoTA ((NA_I (El x_aHk0)) :* ((NA_I (El x_aHk1)) :* NP0)))
               (El (GoCall x_aHk2 x_aHk3 x_aHk4))
                 -> Rep
                      (Pat24GoCall
                         ((NA_I (El x_aHk2))
                            :* ((NA_I (El x_aHk3)) :* ((NA_K (SBool x_aHk4)) :* NP0))))
        IdxGoLit
          -> \case
               (El (GoLitInt x_aHk5 x_aHk6))
                 -> Rep
                      (Pat25GoLitInt
                         ((NA_K (SString x_aHk5)) :* ((NA_K (SInteger x_aHk6)) :* NP0)))
               (El (GoLitReal x_aHk7 x_aHk8))
                 -> Rep
                      (Pat25GoLitReal
                         ((NA_K (SString x_aHk7)) :* ((NA_K (SFloat x_aHk8)) :* NP0)))
               (El (GoLitImag x_aHk9 x_aHka))
                 -> Rep
                      (Pat25GoLitImag
                         ((NA_K (SString x_aHk9)) :* ((NA_K (SFloat x_aHka)) :* NP0)))
               (El (GoLitChar x_aHkb x_aHkc))
                 -> Rep
                      (Pat25GoLitChar
                         ((NA_K (SString x_aHkb)) :* ((NA_K (SChar x_aHkc)) :* NP0)))
               (El (GoLitStr x_aHkd x_aHke))
                 -> Rep
                      (Pat25GoLitStr
                         ((NA_K (SString x_aHkd)) :* ((NA_K (SString x_aHke)) :* NP0)))
               (El (GoLitComp x_aHkf x_aHkg))
                 -> Rep
                      (Pat25GoLitComp
                         ((NA_I (El x_aHkf)) :* ((NA_I (El x_aHkg)) :* NP0)))
               (El (GoLitFunc x_aHkh))
                 -> Rep (Pat25GoLitFunc ((NA_I (El x_aHkh)) :* NP0))
        IdxGoRec
          -> \case
               (El (GoRec x_aHki x_aHkj x_aHkk))
                 -> Rep
                      (Pat26GoRec
                         ((NA_K (SBool x_aHki))
                            :* ((NA_I (El x_aHkj)) :* ((NA_I (El x_aHkk)) :* NP0))))
        IdxGoComp
          -> \case
               (El (GoComp x_aHkl))
                 -> Rep (Pat27GoComp ((NA_I (El x_aHkl)) :* NP0))
        IdxGoFuncExpr
          -> \case
               (El (GoFuncExpr x_aHkm x_aHkn))
                 -> Rep
                      (Pat28GoFuncExpr
                         ((NA_I (El x_aHkm)) :* ((NA_I (El x_aHkn)) :* NP0)))
        IdxListGoElement
          -> \case
               (El []) -> Rep (Pat299193 NP0)
               (El ((:) x_aHko x_aHkp))
                 -> Rep
                      (Pat2958 ((NA_I (El x_aHko)) :* ((NA_I (El x_aHkp)) :* NP0)))
        IdxGoElement
          -> \case
               (El (GoElement x_aHkq x_aHkr))
                 -> Rep
                      (Pat30GoElement
                         ((NA_I (El x_aHkq)) :* ((NA_I (El x_aHkr)) :* NP0)))
        IdxGoKey
          -> \case
               (El GoKeyNone) -> Rep (Pat31GoKeyNone NP0)
               (El (GoKeyField x_aHks))
                 -> Rep (Pat31GoKeyField ((NA_I (El x_aHks)) :* NP0))
               (El (GoKeyIndex x_aHkt))
                 -> Rep (Pat31GoKeyIndex ((NA_I (El x_aHkt)) :* NP0))
        IdxGoValue
          -> \case
               (El (GoValueExpr x_aHku))
                 -> Rep (Pat32GoValueExpr ((NA_I (El x_aHku)) :* NP0))
               (El (GoValueComp x_aHkv))
                 -> Rep (Pat32GoValueComp ((NA_I (El x_aHkv)) :* NP0))
        IdxGoBlock
          -> \case
               (El (GoBlock x_aHkw))
                 -> Rep (Pat33GoBlock ((NA_I (El x_aHkw)) :* NP0))
               (El GoNoBlock) -> Rep (Pat33GoNoBlock NP0)
        IdxListGoParam
          -> \case
               (El []) -> Rep (Pat349193 NP0)
               (El ((:) x_aHkx x_aHky))
                 -> Rep
                      (Pat3458 ((NA_I (El x_aHkx)) :* ((NA_I (El x_aHky)) :* NP0)))
        IdxGoParam
          -> \case
               (El (GoParam x_aHkz x_aHkA))
                 -> Rep
                      (Pat35GoParam ((NA_I (El x_aHkz)) :* ((NA_I (El x_aHkA)) :* NP0)))
        IdxListGoStmt
          -> \case
               (El []) -> Rep (Pat369193 NP0)
               (El ((:) x_aHkB x_aHkC))
                 -> Rep
                      (Pat3658 ((NA_I (El x_aHkB)) :* ((NA_I (El x_aHkC)) :* NP0)))
        IdxGoStmt
          -> \case
               (El (GoStmtDecl x_aHkD))
                 -> Rep (Pat37GoStmtDecl ((NA_I (El x_aHkD)) :* NP0))
               (El (GoStmtLabeled x_aHkE x_aHkF))
                 -> Rep
                      (Pat37GoStmtLabeled
                         ((NA_I (El x_aHkE)) :* ((NA_I (El x_aHkF)) :* NP0)))
               (El (GoStmtSimple x_aHkG))
                 -> Rep (Pat37GoStmtSimple ((NA_I (El x_aHkG)) :* NP0))
               (El (GoStmtGo x_aHkH))
                 -> Rep (Pat37GoStmtGo ((NA_I (El x_aHkH)) :* NP0))
               (El (GoStmtReturn x_aHkI))
                 -> Rep (Pat37GoStmtReturn ((NA_I (El x_aHkI)) :* NP0))
               (El (GoStmtBreak x_aHkJ))
                 -> Rep (Pat37GoStmtBreak ((NA_I (El x_aHkJ)) :* NP0))
               (El (GoStmtContinue x_aHkK))
                 -> Rep (Pat37GoStmtContinue ((NA_I (El x_aHkK)) :* NP0))
               (El (GoStmtGoto x_aHkL))
                 -> Rep (Pat37GoStmtGoto ((NA_I (El x_aHkL)) :* NP0))
               (El GoStmtFallthrough) -> Rep (Pat37GoStmtFallthrough NP0)
               (El (GoStmtBlock x_aHkM))
                 -> Rep (Pat37GoStmtBlock ((NA_I (El x_aHkM)) :* NP0))
               (El (GoStmtIf x_aHkN x_aHkO x_aHkP))
                 -> Rep
                      (Pat37GoStmtIf
                         ((NA_I (El x_aHkN))
                            :* ((NA_I (El x_aHkO)) :* ((NA_I (El x_aHkP)) :* NP0))))
               (El (GoStmtSelect x_aHkQ))
                 -> Rep (Pat37GoStmtSelect ((NA_I (El x_aHkQ)) :* NP0))
               (El (GoStmtSwitch x_aHkR x_aHkS))
                 -> Rep
                      (Pat37GoStmtSwitch
                         ((NA_I (El x_aHkR)) :* ((NA_I (El x_aHkS)) :* NP0)))
               (El (GoStmtTypeSwitch x_aHkT x_aHkU x_aHkV))
                 -> Rep
                      (Pat37GoStmtTypeSwitch
                         ((NA_I (El x_aHkT))
                            :* ((NA_I (El x_aHkU)) :* ((NA_I (El x_aHkV)) :* NP0))))
               (El (GoStmtFor x_aHkW x_aHkX))
                 -> Rep
                      (Pat37GoStmtFor
                         ((NA_I (El x_aHkW)) :* ((NA_I (El x_aHkX)) :* NP0)))
               (El (GoStmtDefer x_aHkY))
                 -> Rep (Pat37GoStmtDefer ((NA_I (El x_aHkY)) :* NP0))
        IdxGoSimp
          -> \case
               (El GoSimpEmpty) -> Rep (Pat38GoSimpEmpty NP0)
               (El (GoSimpRecv x_aHkZ))
                 -> Rep (Pat38GoSimpRecv ((NA_I (El x_aHkZ)) :* NP0))
               (El (GoSimpSend x_aHl0 x_aHl1))
                 -> Rep
                      (Pat38GoSimpSend
                         ((NA_I (El x_aHl0)) :* ((NA_I (El x_aHl1)) :* NP0)))
               (El (GoSimpExpr x_aHl2))
                 -> Rep (Pat38GoSimpExpr ((NA_I (El x_aHl2)) :* NP0))
               (El (GoSimpInc x_aHl3))
                 -> Rep (Pat38GoSimpInc ((NA_I (El x_aHl3)) :* NP0))
               (El (GoSimpDec x_aHl4))
                 -> Rep (Pat38GoSimpDec ((NA_I (El x_aHl4)) :* NP0))
               (El (GoSimpAsn x_aHl5 x_aHl6 x_aHl7))
                 -> Rep
                      (Pat38GoSimpAsn
                         ((NA_I (El x_aHl5))
                            :* ((NA_I (El x_aHl6)) :* ((NA_I (El x_aHl7)) :* NP0))))
               (El (GoSimpVar x_aHl8 x_aHl9))
                 -> Rep
                      (Pat38GoSimpVar
                         ((NA_I (El x_aHl8)) :* ((NA_I (El x_aHl9)) :* NP0)))
        IdxMaybeGoId
          -> \case
               (El Nothing) -> Rep (Pat39Nothing NP0)
               (El (Just x_aHla)) -> Rep (Pat39Just ((NA_I (El x_aHla)) :* NP0))
        IdxGoCond
          -> \case
               (El (GoCond x_aHlb x_aHlc))
                 -> Rep
                      (Pat40GoCond ((NA_I (El x_aHlb)) :* ((NA_I (El x_aHlc)) :* NP0)))
        IdxMaybeGoStmt
          -> \case
               (El Nothing) -> Rep (Pat41Nothing NP0)
               (El (Just x_aHld)) -> Rep (Pat41Just ((NA_I (El x_aHld)) :* NP0))
        IdxListGoCaseGoChan
          -> \case
               (El []) -> Rep (Pat429193 NP0)
               (El ((:) x_aHle x_aHlf))
                 -> Rep
                      (Pat4258 ((NA_I (El x_aHle)) :* ((NA_I (El x_aHlf)) :* NP0)))
        IdxListGoCaseGoExpr
          -> \case
               (El []) -> Rep (Pat439193 NP0)
               (El ((:) x_aHlg x_aHlh))
                 -> Rep
                      (Pat4358 ((NA_I (El x_aHlg)) :* ((NA_I (El x_aHlh)) :* NP0)))
        IdxListGoCaseGoType
          -> \case
               (El []) -> Rep (Pat449193 NP0)
               (El ((:) x_aHli x_aHlj))
                 -> Rep
                      (Pat4458 ((NA_I (El x_aHli)) :* ((NA_I (El x_aHlj)) :* NP0)))
        IdxGoForClause
          -> \case
               (El (GoForWhile x_aHlk))
                 -> Rep (Pat45GoForWhile ((NA_I (El x_aHlk)) :* NP0))
               (El (GoForThree x_aHll x_aHlm x_aHln))
                 -> Rep
                      (Pat45GoForThree
                         ((NA_I (El x_aHll))
                            :* ((NA_I (El x_aHlm)) :* ((NA_I (El x_aHln)) :* NP0))))
               (El (GoForRange x_aHlo x_aHlp))
                 -> Rep
                      (Pat45GoForRange
                         ((NA_I (El x_aHlo)) :* ((NA_I (El x_aHlp)) :* NP0)))
        IdxMaybeGoSimp
          -> \case
               (El Nothing) -> Rep (Pat46Nothing NP0)
               (El (Just x_aHlq)) -> Rep (Pat46Just ((NA_I (El x_aHlq)) :* NP0))
        IdxMaybeGoExpr
          -> \case
               (El Nothing) -> Rep (Pat47Nothing NP0)
               (El (Just x_aHlr)) -> Rep (Pat47Just ((NA_I (El x_aHlr)) :* NP0))
        IdxGoCaseGoChan
          -> \case
               (El (GoCase x_aHls x_aHlt))
                 -> Rep
                      (Pat48GoCase ((NA_I (El x_aHls)) :* ((NA_I (El x_aHlt)) :* NP0)))
               (El (GoDefault x_aHlu))
                 -> Rep (Pat48GoDefault ((NA_I (El x_aHlu)) :* NP0))
        IdxListGoChan
          -> \case
               (El []) -> Rep (Pat499193 NP0)
               (El ((:) x_aHlv x_aHlw))
                 -> Rep
                      (Pat4958 ((NA_I (El x_aHlv)) :* ((NA_I (El x_aHlw)) :* NP0)))
        IdxGoChan
          -> \case
               (El (GoChanRecv x_aHlx x_aHly))
                 -> Rep
                      (Pat50GoChanRecv
                         ((NA_I (El x_aHlx)) :* ((NA_I (El x_aHly)) :* NP0)))
               (El (GoChanSend x_aHlz x_aHlA))
                 -> Rep
                      (Pat50GoChanSend
                         ((NA_I (El x_aHlz)) :* ((NA_I (El x_aHlA)) :* NP0)))
        IdxMaybeGoChanInner
          -> \case
               (El Nothing) -> Rep (Pat51Nothing NP0)
               (El (Just x_aHlB)) -> Rep (Pat51Just ((NA_I (El x_aHlB)) :* NP0))
        IdxGoChanInner
          -> \case
               (El (GoChanInner x_aHlC x_aHlD))
                 -> Rep
                      (Pat52GoChanInner
                         ((NA_I (El x_aHlC)) :* ((NA_I (El x_aHlD)) :* NP0)))
        IdxGoCaseGoExpr
          -> \case
               (El (GoCase x_aHlE x_aHlF))
                 -> Rep
                      (Pat53GoCase ((NA_I (El x_aHlE)) :* ((NA_I (El x_aHlF)) :* NP0)))
               (El (GoDefault x_aHlG))
                 -> Rep (Pat53GoDefault ((NA_I (El x_aHlG)) :* NP0))
        IdxGoCaseGoType
          -> \case
               (El (GoCase x_aHlH x_aHlI))
                 -> Rep
                      (Pat54GoCase ((NA_I (El x_aHlH)) :* ((NA_I (El x_aHlI)) :* NP0)))
               (El (GoDefault x_aHlJ))
                 -> Rep (Pat54GoDefault ((NA_I (El x_aHlJ)) :* NP0))
        IdxListGoType
          -> \case
               (El []) -> Rep (Pat559193 NP0)
               (El ((:) x_aHlK x_aHlL))
                 -> Rep
                      (Pat5558 ((NA_I (El x_aHlK)) :* ((NA_I (El x_aHlL)) :* NP0)))
        IdxGoMethSpec
          -> \case
               (El (GoMethSpec x_aHlM x_aHlN))
                 -> Rep
                      (Pat56GoMethSpec
                         ((NA_I (El x_aHlM)) :* ((NA_I (El x_aHlN)) :* NP0)))
               (El (GoInterface x_aHlO))
                 -> Rep (Pat56GoInterface ((NA_I (El x_aHlO)) :* NP0))
        IdxGoFieldType
          -> \case
               (El (GoFieldType x_aHlP x_aHlQ x_aHlR))
                 -> Rep
                      (Pat57GoFieldType
                         ((NA_K (SString x_aHlP))
                            :* ((NA_I (El x_aHlQ)) :* ((NA_I (El x_aHlR)) :* NP0))))
               (El (GoFieldAnon x_aHlS x_aHlT x_aHlU))
                 -> Rep
                      (Pat57GoFieldAnon
                         ((NA_K (SString x_aHlS))
                            :* ((NA_K (SBool x_aHlT)) :* ((NA_I (El x_aHlU)) :* NP0))))
        IdxGoTypeSpec
          -> \case
               (El (GoTypeSpec x_aHlV x_aHlW))
                 -> Rep
                      (Pat58GoTypeSpec
                         ((NA_I (El x_aHlV)) :* ((NA_I (El x_aHlW)) :* NP0)))
  sto'
    = \case
        IdxGoSource
          -> \case
               (Rep (Pat0GoSource (NA_I (El y_aHlX) :* (NA_I (El y_aHlY) :* (NA_I (El y_aHlZ) :* NP0)))))
                 -> El (((GoSource y_aHlX) y_aHlY) y_aHlZ)
               _ -> error "matchAll"
        IdxGoId
          -> \case
               (Rep (Pat1GoId (NA_K (SString y_aHm0) :* NP0)))
                 -> El (GoId y_aHm0)
               _ -> error "matchAll"
        IdxListGoPrel
          -> \case
               (Rep (Pat29193 NP0)) -> El []
               (Rep (Pat258 (NA_I (El y_aHm1) :* (NA_I (El y_aHm2) :* NP0))))
                 -> El (((:) y_aHm1) y_aHm2)
               _ -> error "matchAll"
        IdxListGoDecl
          -> \case
               (Rep (Pat39193 NP0)) -> El []
               (Rep (Pat358 (NA_I (El y_aHm3) :* (NA_I (El y_aHm4) :* NP0))))
                 -> El (((:) y_aHm3) y_aHm4)
               _ -> error "matchAll"
        IdxGoPrel
          -> \case
               (Rep (Pat4GoImportDecl (NA_I (El y_aHm5) :* NP0)))
                 -> El (GoImportDecl y_aHm5)
               (Rep (Pat4GoPragma (NA_K (SString y_aHm6) :* NP0)))
                 -> El (GoPragma y_aHm6)
               (Rep (Pat4GoDefine NP0)) -> El GoDefine
               (Rep (Pat4GoIfPrel NP0)) -> El GoIfPrel
               _ -> error "matchAll"
        IdxListGoImpSpec
          -> \case
               (Rep (Pat59193 NP0)) -> El []
               (Rep (Pat558 (NA_I (El y_aHm7) :* (NA_I (El y_aHm8) :* NP0))))
                 -> El (((:) y_aHm7) y_aHm8)
               _ -> error "matchAll"
        IdxGoImpSpec
          -> \case
               (Rep (Pat6GoImpSpec (NA_I (El y_aHm9) :* (NA_K (SString y_aHma) :* NP0))))
                 -> El ((GoImpSpec y_aHm9) y_aHma)
               _ -> error "matchAll"
        IdxGoImpType
          -> \case
               (Rep (Pat7GoImp NP0)) -> El GoImp
               (Rep (Pat7GoImpDot (NA_I (El y_aHmb) :* NP0)))
                 -> El (GoImpDot y_aHmb)
               (Rep (Pat7GoImpQual (NA_I (El y_aHmc) :* NP0)))
                 -> El (GoImpQual y_aHmc)
               _ -> error "matchAll"
        IdxGoOp
          -> \case
               (Rep (Pat8GoOp (NA_K (SString y_aHmd) :* NP0)))
                 -> El (GoOp y_aHmd)
               _ -> error "matchAll"
        IdxGoDecl
          -> \case
               (Rep (Pat9GoConst (NA_I (El y_aHme) :* NP0)))
                 -> El (GoConst y_aHme)
               (Rep (Pat9GoType (NA_I (El y_aHmf) :* NP0)))
                 -> El (GoType y_aHmf)
               (Rep (Pat9GoVar (NA_I (El y_aHmg) :* NP0))) -> El (GoVar y_aHmg)
               (Rep (Pat9GoFunc (NA_I (El y_aHmh) :* NP0)))
                 -> El (GoFunc y_aHmh)
               (Rep (Pat9GoMeth (NA_I (El y_aHmi) :* NP0)))
                 -> El (GoMeth y_aHmi)
               _ -> error "matchAll"
        IdxListGoCVSpec
          -> \case
               (Rep (Pat109193 NP0)) -> El []
               (Rep (Pat1058 (NA_I (El y_aHmj) :* (NA_I (El y_aHmk) :* NP0))))
                 -> El (((:) y_aHmj) y_aHmk)
               _ -> error "matchAll"
        IdxListGoTypeSpec
          -> \case
               (Rep (Pat119193 NP0)) -> El []
               (Rep (Pat1158 (NA_I (El y_aHml) :* (NA_I (El y_aHmm) :* NP0))))
                 -> El (((:) y_aHml) y_aHmm)
               _ -> error "matchAll"
        IdxGoFuncDecl
          -> \case
               (Rep (Pat12GoFuncDecl (NA_I (El y_aHmn) :* (NA_I (El y_aHmo) :* (NA_I (El y_aHmp) :* NP0)))))
                 -> El (((GoFuncDecl y_aHmn) y_aHmo) y_aHmp)
               _ -> error "matchAll"
        IdxGoMethDecl
          -> \case
               (Rep (Pat13GoMethDecl (NA_I (El y_aHmq) :* (NA_I (El y_aHmr) :* (NA_I (El y_aHms) :* (NA_I (El y_aHmt) :* NP0))))))
                 -> El ((((GoMethDecl y_aHmq) y_aHmr) y_aHms) y_aHmt)
               _ -> error "matchAll"
        IdxGoCVSpec
          -> \case
               (Rep (Pat14GoCVSpec (NA_I (El y_aHmu) :* (NA_I (El y_aHmv) :* (NA_I (El y_aHmw) :* NP0)))))
                 -> El (((GoCVSpec y_aHmu) y_aHmv) y_aHmw)
               _ -> error "matchAll"
        IdxListGoId
          -> \case
               (Rep (Pat159193 NP0)) -> El []
               (Rep (Pat1558 (NA_I (El y_aHmx) :* (NA_I (El y_aHmy) :* NP0))))
                 -> El (((:) y_aHmx) y_aHmy)
               _ -> error "matchAll"
        IdxMaybeGoType
          -> \case
               (Rep (Pat16Nothing NP0)) -> El Nothing
               (Rep (Pat16Just (NA_I (El y_aHmz) :* NP0))) -> El (Just y_aHmz)
               _ -> error "matchAll"
        IdxListGoExpr
          -> \case
               (Rep (Pat179193 NP0)) -> El []
               (Rep (Pat1758 (NA_I (El y_aHmA) :* (NA_I (El y_aHmB) :* NP0))))
                 -> El (((:) y_aHmA) y_aHmB)
               _ -> error "matchAll"
        IdxGoType
          -> \case
               (Rep (Pat18GoTypeName (NA_I (El y_aHmC) :* (NA_I (El y_aHmD) :* NP0))))
                 -> El ((GoTypeName y_aHmC) y_aHmD)
               (Rep (Pat18GoArrayType (NA_I (El y_aHmE) :* (NA_I (El y_aHmF) :* NP0))))
                 -> El ((GoArrayType y_aHmE) y_aHmF)
               (Rep (Pat18GoChannelType (NA_I (El y_aHmG) :* (NA_I (El y_aHmH) :* NP0))))
                 -> El ((GoChannelType y_aHmG) y_aHmH)
               (Rep (Pat18GoElipsisType (NA_I (El y_aHmI) :* NP0)))
                 -> El (GoElipsisType y_aHmI)
               (Rep (Pat18GoFunctionType (NA_I (El y_aHmJ) :* NP0)))
                 -> El (GoFunctionType y_aHmJ)
               (Rep (Pat18GoInterfaceType (NA_I (El y_aHmK) :* NP0)))
                 -> El (GoInterfaceType y_aHmK)
               (Rep (Pat18GoMapType (NA_I (El y_aHmL) :* (NA_I (El y_aHmM) :* NP0))))
                 -> El ((GoMapType y_aHmL) y_aHmM)
               (Rep (Pat18GoPointerType (NA_I (El y_aHmN) :* NP0)))
                 -> El (GoPointerType y_aHmN)
               (Rep (Pat18GoSliceType (NA_I (El y_aHmO) :* NP0)))
                 -> El (GoSliceType y_aHmO)
               (Rep (Pat18GoStructType (NA_I (El y_aHmP) :* NP0)))
                 -> El (GoStructType y_aHmP)
               _ -> error "matchAll"
        IdxGoExpr
          -> \case
               (Rep (Pat19GoPrim (NA_I (El y_aHmQ) :* NP0)))
                 -> El (GoPrim y_aHmQ)
               (Rep (Pat19Go1Op (NA_I (El y_aHmR) :* (NA_I (El y_aHmS) :* NP0))))
                 -> El ((Go1Op y_aHmR) y_aHmS)
               (Rep (Pat19Go2Op (NA_I (El y_aHmT) :* (NA_I (El y_aHmU) :* (NA_I (El y_aHmV) :* NP0)))))
                 -> El (((Go2Op y_aHmT) y_aHmU) y_aHmV)
               _ -> error "matchAll"
        IdxGoChanKind
          -> \case
               (Rep (Pat20GoIChan NP0)) -> El GoIChan
               (Rep (Pat20GoOChan NP0)) -> El GoOChan
               (Rep (Pat20GoIOChan NP0)) -> El GoIOChan
               _ -> error "matchAll"
        IdxGoSig
          -> \case
               (Rep (Pat21GoSig (NA_I (El y_aHmW) :* (NA_I (El y_aHmX) :* NP0))))
                 -> El ((GoSig y_aHmW) y_aHmX)
               _ -> error "matchAll"
        IdxListGoMethSpec
          -> \case
               (Rep (Pat229193 NP0)) -> El []
               (Rep (Pat2258 (NA_I (El y_aHmY) :* (NA_I (El y_aHmZ) :* NP0))))
                 -> El (((:) y_aHmY) y_aHmZ)
               _ -> error "matchAll"
        IdxListGoFieldType
          -> \case
               (Rep (Pat239193 NP0)) -> El []
               (Rep (Pat2358 (NA_I (El y_aHn0) :* (NA_I (El y_aHn1) :* NP0))))
                 -> El (((:) y_aHn0) y_aHn1)
               _ -> error "matchAll"
        IdxGoPrim
          -> \case
               (Rep (Pat24GoLiteral (NA_I (El y_aHn2) :* NP0)))
                 -> El (GoLiteral y_aHn2)
               (Rep (Pat24GoQual (NA_I (El y_aHn3) :* (NA_I (El y_aHn4) :* NP0))))
                 -> El ((GoQual y_aHn3) y_aHn4)
               (Rep (Pat24GoMethod (NA_I (El y_aHn5) :* (NA_I (El y_aHn6) :* NP0))))
                 -> El ((GoMethod y_aHn5) y_aHn6)
               (Rep (Pat24GoParen (NA_I (El y_aHn7) :* NP0)))
                 -> El (GoParen y_aHn7)
               (Rep (Pat24GoCast (NA_I (El y_aHn8) :* (NA_I (El y_aHn9) :* NP0))))
                 -> El ((GoCast y_aHn8) y_aHn9)
               (Rep (Pat24GoNew (NA_I (El y_aHna) :* NP0))) -> El (GoNew y_aHna)
               (Rep (Pat24GoMake (NA_I (El y_aHnb) :* (NA_I (El y_aHnc) :* NP0))))
                 -> El ((GoMake y_aHnb) y_aHnc)
               (Rep (Pat24GoSelect (NA_I (El y_aHnd) :* (NA_I (El y_aHne) :* NP0))))
                 -> El ((GoSelect y_aHnd) y_aHne)
               (Rep (Pat24GoIndex (NA_I (El y_aHnf) :* (NA_I (El y_aHng) :* NP0))))
                 -> El ((GoIndex y_aHnf) y_aHng)
               (Rep (Pat24GoSlice (NA_I (El y_aHnh) :* (NA_I (El y_aHni) :* NP0))))
                 -> El ((GoSlice y_aHnh) y_aHni)
               (Rep (Pat24GoTA (NA_I (El y_aHnj) :* (NA_I (El y_aHnk) :* NP0))))
                 -> El ((GoTA y_aHnj) y_aHnk)
               (Rep (Pat24GoCall (NA_I (El y_aHnl) :* (NA_I (El y_aHnm) :* (NA_K (SBool y_aHnn) :* NP0)))))
                 -> El (((GoCall y_aHnl) y_aHnm) y_aHnn)
               _ -> error "matchAll"
        IdxGoLit
          -> \case
               (Rep (Pat25GoLitInt (NA_K (SString y_aHno) :* (NA_K (SInteger y_aHnp) :* NP0))))
                 -> El ((GoLitInt y_aHno) y_aHnp)
               (Rep (Pat25GoLitReal (NA_K (SString y_aHnq) :* (NA_K (SFloat y_aHnr) :* NP0))))
                 -> El ((GoLitReal y_aHnq) y_aHnr)
               (Rep (Pat25GoLitImag (NA_K (SString y_aHns) :* (NA_K (SFloat y_aHnt) :* NP0))))
                 -> El ((GoLitImag y_aHns) y_aHnt)
               (Rep (Pat25GoLitChar (NA_K (SString y_aHnu) :* (NA_K (SChar y_aHnv) :* NP0))))
                 -> El ((GoLitChar y_aHnu) y_aHnv)
               (Rep (Pat25GoLitStr (NA_K (SString y_aHnw) :* (NA_K (SString y_aHnx) :* NP0))))
                 -> El ((GoLitStr y_aHnw) y_aHnx)
               (Rep (Pat25GoLitComp (NA_I (El y_aHny) :* (NA_I (El y_aHnz) :* NP0))))
                 -> El ((GoLitComp y_aHny) y_aHnz)
               (Rep (Pat25GoLitFunc (NA_I (El y_aHnA) :* NP0)))
                 -> El (GoLitFunc y_aHnA)
               _ -> error "matchAll"
        IdxGoRec
          -> \case
               (Rep (Pat26GoRec (NA_K (SBool y_aHnB) :* (NA_I (El y_aHnC) :* (NA_I (El y_aHnD) :* NP0)))))
                 -> El (((GoRec y_aHnB) y_aHnC) y_aHnD)
               _ -> error "matchAll"
        IdxGoComp
          -> \case
               (Rep (Pat27GoComp (NA_I (El y_aHnE) :* NP0)))
                 -> El (GoComp y_aHnE)
               _ -> error "matchAll"
        IdxGoFuncExpr
          -> \case
               (Rep (Pat28GoFuncExpr (NA_I (El y_aHnF) :* (NA_I (El y_aHnG) :* NP0))))
                 -> El ((GoFuncExpr y_aHnF) y_aHnG)
               _ -> error "matchAll"
        IdxListGoElement
          -> \case
               (Rep (Pat299193 NP0)) -> El []
               (Rep (Pat2958 (NA_I (El y_aHnH) :* (NA_I (El y_aHnI) :* NP0))))
                 -> El (((:) y_aHnH) y_aHnI)
               _ -> error "matchAll"
        IdxGoElement
          -> \case
               (Rep (Pat30GoElement (NA_I (El y_aHnJ) :* (NA_I (El y_aHnK) :* NP0))))
                 -> El ((GoElement y_aHnJ) y_aHnK)
               _ -> error "matchAll"
        IdxGoKey
          -> \case
               (Rep (Pat31GoKeyNone NP0)) -> El GoKeyNone
               (Rep (Pat31GoKeyField (NA_I (El y_aHnL) :* NP0)))
                 -> El (GoKeyField y_aHnL)
               (Rep (Pat31GoKeyIndex (NA_I (El y_aHnM) :* NP0)))
                 -> El (GoKeyIndex y_aHnM)
               _ -> error "matchAll"
        IdxGoValue
          -> \case
               (Rep (Pat32GoValueExpr (NA_I (El y_aHnN) :* NP0)))
                 -> El (GoValueExpr y_aHnN)
               (Rep (Pat32GoValueComp (NA_I (El y_aHnO) :* NP0)))
                 -> El (GoValueComp y_aHnO)
               _ -> error "matchAll"
        IdxGoBlock
          -> \case
               (Rep (Pat33GoBlock (NA_I (El y_aHnP) :* NP0)))
                 -> El (GoBlock y_aHnP)
               (Rep (Pat33GoNoBlock NP0)) -> El GoNoBlock
               _ -> error "matchAll"
        IdxListGoParam
          -> \case
               (Rep (Pat349193 NP0)) -> El []
               (Rep (Pat3458 (NA_I (El y_aHnQ) :* (NA_I (El y_aHnR) :* NP0))))
                 -> El (((:) y_aHnQ) y_aHnR)
               _ -> error "matchAll"
        IdxGoParam
          -> \case
               (Rep (Pat35GoParam (NA_I (El y_aHnS) :* (NA_I (El y_aHnT) :* NP0))))
                 -> El ((GoParam y_aHnS) y_aHnT)
               _ -> error "matchAll"
        IdxListGoStmt
          -> \case
               (Rep (Pat369193 NP0)) -> El []
               (Rep (Pat3658 (NA_I (El y_aHnU) :* (NA_I (El y_aHnV) :* NP0))))
                 -> El (((:) y_aHnU) y_aHnV)
               _ -> error "matchAll"
        IdxGoStmt
          -> \case
               (Rep (Pat37GoStmtDecl (NA_I (El y_aHnW) :* NP0)))
                 -> El (GoStmtDecl y_aHnW)
               (Rep (Pat37GoStmtLabeled (NA_I (El y_aHnX) :* (NA_I (El y_aHnY) :* NP0))))
                 -> El ((GoStmtLabeled y_aHnX) y_aHnY)
               (Rep (Pat37GoStmtSimple (NA_I (El y_aHnZ) :* NP0)))
                 -> El (GoStmtSimple y_aHnZ)
               (Rep (Pat37GoStmtGo (NA_I (El y_aHo0) :* NP0)))
                 -> El (GoStmtGo y_aHo0)
               (Rep (Pat37GoStmtReturn (NA_I (El y_aHo1) :* NP0)))
                 -> El (GoStmtReturn y_aHo1)
               (Rep (Pat37GoStmtBreak (NA_I (El y_aHo2) :* NP0)))
                 -> El (GoStmtBreak y_aHo2)
               (Rep (Pat37GoStmtContinue (NA_I (El y_aHo3) :* NP0)))
                 -> El (GoStmtContinue y_aHo3)
               (Rep (Pat37GoStmtGoto (NA_I (El y_aHo4) :* NP0)))
                 -> El (GoStmtGoto y_aHo4)
               (Rep (Pat37GoStmtFallthrough NP0)) -> El GoStmtFallthrough
               (Rep (Pat37GoStmtBlock (NA_I (El y_aHo5) :* NP0)))
                 -> El (GoStmtBlock y_aHo5)
               (Rep (Pat37GoStmtIf (NA_I (El y_aHo6) :* (NA_I (El y_aHo7) :* (NA_I (El y_aHo8) :* NP0)))))
                 -> El (((GoStmtIf y_aHo6) y_aHo7) y_aHo8)
               (Rep (Pat37GoStmtSelect (NA_I (El y_aHo9) :* NP0)))
                 -> El (GoStmtSelect y_aHo9)
               (Rep (Pat37GoStmtSwitch (NA_I (El y_aHoa) :* (NA_I (El y_aHob) :* NP0))))
                 -> El ((GoStmtSwitch y_aHoa) y_aHob)
               (Rep (Pat37GoStmtTypeSwitch (NA_I (El y_aHoc) :* (NA_I (El y_aHod) :* (NA_I (El y_aHoe) :* NP0)))))
                 -> El (((GoStmtTypeSwitch y_aHoc) y_aHod) y_aHoe)
               (Rep (Pat37GoStmtFor (NA_I (El y_aHof) :* (NA_I (El y_aHog) :* NP0))))
                 -> El ((GoStmtFor y_aHof) y_aHog)
               (Rep (Pat37GoStmtDefer (NA_I (El y_aHoh) :* NP0)))
                 -> El (GoStmtDefer y_aHoh)
               _ -> error "matchAll"
        IdxGoSimp
          -> \case
               (Rep (Pat38GoSimpEmpty NP0)) -> El GoSimpEmpty
               (Rep (Pat38GoSimpRecv (NA_I (El y_aHoi) :* NP0)))
                 -> El (GoSimpRecv y_aHoi)
               (Rep (Pat38GoSimpSend (NA_I (El y_aHoj) :* (NA_I (El y_aHok) :* NP0))))
                 -> El ((GoSimpSend y_aHoj) y_aHok)
               (Rep (Pat38GoSimpExpr (NA_I (El y_aHol) :* NP0)))
                 -> El (GoSimpExpr y_aHol)
               (Rep (Pat38GoSimpInc (NA_I (El y_aHom) :* NP0)))
                 -> El (GoSimpInc y_aHom)
               (Rep (Pat38GoSimpDec (NA_I (El y_aHon) :* NP0)))
                 -> El (GoSimpDec y_aHon)
               (Rep (Pat38GoSimpAsn (NA_I (El y_aHoo) :* (NA_I (El y_aHop) :* (NA_I (El y_aHoq) :* NP0)))))
                 -> El (((GoSimpAsn y_aHoo) y_aHop) y_aHoq)
               (Rep (Pat38GoSimpVar (NA_I (El y_aHor) :* (NA_I (El y_aHos) :* NP0))))
                 -> El ((GoSimpVar y_aHor) y_aHos)
               _ -> error "matchAll"
        IdxMaybeGoId
          -> \case
               (Rep (Pat39Nothing NP0)) -> El Nothing
               (Rep (Pat39Just (NA_I (El y_aHot) :* NP0))) -> El (Just y_aHot)
               _ -> error "matchAll"
        IdxGoCond
          -> \case
               (Rep (Pat40GoCond (NA_I (El y_aHou) :* (NA_I (El y_aHov) :* NP0))))
                 -> El ((GoCond y_aHou) y_aHov)
               _ -> error "matchAll"
        IdxMaybeGoStmt
          -> \case
               (Rep (Pat41Nothing NP0)) -> El Nothing
               (Rep (Pat41Just (NA_I (El y_aHow) :* NP0))) -> El (Just y_aHow)
               _ -> error "matchAll"
        IdxListGoCaseGoChan
          -> \case
               (Rep (Pat429193 NP0)) -> El []
               (Rep (Pat4258 (NA_I (El y_aHox) :* (NA_I (El y_aHoy) :* NP0))))
                 -> El (((:) y_aHox) y_aHoy)
               _ -> error "matchAll"
        IdxListGoCaseGoExpr
          -> \case
               (Rep (Pat439193 NP0)) -> El []
               (Rep (Pat4358 (NA_I (El y_aHoz) :* (NA_I (El y_aHoA) :* NP0))))
                 -> El (((:) y_aHoz) y_aHoA)
               _ -> error "matchAll"
        IdxListGoCaseGoType
          -> \case
               (Rep (Pat449193 NP0)) -> El []
               (Rep (Pat4458 (NA_I (El y_aHoB) :* (NA_I (El y_aHoC) :* NP0))))
                 -> El (((:) y_aHoB) y_aHoC)
               _ -> error "matchAll"
        IdxGoForClause
          -> \case
               (Rep (Pat45GoForWhile (NA_I (El y_aHoD) :* NP0)))
                 -> El (GoForWhile y_aHoD)
               (Rep (Pat45GoForThree (NA_I (El y_aHoE) :* (NA_I (El y_aHoF) :* (NA_I (El y_aHoG) :* NP0)))))
                 -> El (((GoForThree y_aHoE) y_aHoF) y_aHoG)
               (Rep (Pat45GoForRange (NA_I (El y_aHoH) :* (NA_I (El y_aHoI) :* NP0))))
                 -> El ((GoForRange y_aHoH) y_aHoI)
               _ -> error "matchAll"
        IdxMaybeGoSimp
          -> \case
               (Rep (Pat46Nothing NP0)) -> El Nothing
               (Rep (Pat46Just (NA_I (El y_aHoJ) :* NP0))) -> El (Just y_aHoJ)
               _ -> error "matchAll"
        IdxMaybeGoExpr
          -> \case
               (Rep (Pat47Nothing NP0)) -> El Nothing
               (Rep (Pat47Just (NA_I (El y_aHoK) :* NP0))) -> El (Just y_aHoK)
               _ -> error "matchAll"
        IdxGoCaseGoChan
          -> \case
               (Rep (Pat48GoCase (NA_I (El y_aHoL) :* (NA_I (El y_aHoM) :* NP0))))
                 -> El ((GoCase y_aHoL) y_aHoM)
               (Rep (Pat48GoDefault (NA_I (El y_aHoN) :* NP0)))
                 -> El (GoDefault y_aHoN)
               _ -> error "matchAll"
        IdxListGoChan
          -> \case
               (Rep (Pat499193 NP0)) -> El []
               (Rep (Pat4958 (NA_I (El y_aHoO) :* (NA_I (El y_aHoP) :* NP0))))
                 -> El (((:) y_aHoO) y_aHoP)
               _ -> error "matchAll"
        IdxGoChan
          -> \case
               (Rep (Pat50GoChanRecv (NA_I (El y_aHoQ) :* (NA_I (El y_aHoR) :* NP0))))
                 -> El ((GoChanRecv y_aHoQ) y_aHoR)
               (Rep (Pat50GoChanSend (NA_I (El y_aHoS) :* (NA_I (El y_aHoT) :* NP0))))
                 -> El ((GoChanSend y_aHoS) y_aHoT)
               _ -> error "matchAll"
        IdxMaybeGoChanInner
          -> \case
               (Rep (Pat51Nothing NP0)) -> El Nothing
               (Rep (Pat51Just (NA_I (El y_aHoU) :* NP0))) -> El (Just y_aHoU)
               _ -> error "matchAll"
        IdxGoChanInner
          -> \case
               (Rep (Pat52GoChanInner (NA_I (El y_aHoV) :* (NA_I (El y_aHoW) :* NP0))))
                 -> El ((GoChanInner y_aHoV) y_aHoW)
               _ -> error "matchAll"
        IdxGoCaseGoExpr
          -> \case
               (Rep (Pat53GoCase (NA_I (El y_aHoX) :* (NA_I (El y_aHoY) :* NP0))))
                 -> El ((GoCase y_aHoX) y_aHoY)
               (Rep (Pat53GoDefault (NA_I (El y_aHoZ) :* NP0)))
                 -> El (GoDefault y_aHoZ)
               _ -> error "matchAll"
        IdxGoCaseGoType
          -> \case
               (Rep (Pat54GoCase (NA_I (El y_aHp0) :* (NA_I (El y_aHp1) :* NP0))))
                 -> El ((GoCase y_aHp0) y_aHp1)
               (Rep (Pat54GoDefault (NA_I (El y_aHp2) :* NP0)))
                 -> El (GoDefault y_aHp2)
               _ -> error "matchAll"
        IdxListGoType
          -> \case
               (Rep (Pat559193 NP0)) -> El []
               (Rep (Pat5558 (NA_I (El y_aHp3) :* (NA_I (El y_aHp4) :* NP0))))
                 -> El (((:) y_aHp3) y_aHp4)
               _ -> error "matchAll"
        IdxGoMethSpec
          -> \case
               (Rep (Pat56GoMethSpec (NA_I (El y_aHp5) :* (NA_I (El y_aHp6) :* NP0))))
                 -> El ((GoMethSpec y_aHp5) y_aHp6)
               (Rep (Pat56GoInterface (NA_I (El y_aHp7) :* NP0)))
                 -> El (GoInterface y_aHp7)
               _ -> error "matchAll"
        IdxGoFieldType
          -> \case
               (Rep (Pat57GoFieldType (NA_K (SString y_aHp8) :* (NA_I (El y_aHp9) :* (NA_I (El y_aHpa) :* NP0)))))
                 -> El (((GoFieldType y_aHp8) y_aHp9) y_aHpa)
               (Rep (Pat57GoFieldAnon (NA_K (SString y_aHpb) :* (NA_K (SBool y_aHpc) :* (NA_I (El y_aHpd) :* NP0)))))
                 -> El (((GoFieldAnon y_aHpb) y_aHpc) y_aHpd)
               _ -> error "matchAll"
        IdxGoTypeSpec
          -> \case
               (Rep (Pat58GoTypeSpec (NA_I (El y_aHpe) :* (NA_I (El y_aHpf) :* NP0))))
                 -> El ((GoTypeSpec y_aHpe) y_aHpf)
               _ -> error "matchAll"
        _ -> error "matchAll"
