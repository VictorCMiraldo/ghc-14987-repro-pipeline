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

data View :: (kon -> *) -> (Nat -> *) -> [[ Atom kon ]] -> * where
  Tag :: {- IsNat n => -} Constr sum n -> PoA ki fam (Lkup n sum) -> View ki fam sum

data Constr :: [k] -> Nat -> * where
  CS :: Constr xs n -> Constr (x : xs) ('S n)
  CZ ::                Constr (x : xs) 'Z

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
                 deriving (Eq, Read, Show)

data GoPrel = GoImportDecl [GoImpSpec]
-- 
-- #ifdef DSGO
--             | GoPragma String
--             | GoDefine
--             | GoIfPrel
-- #endif
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

data GoChan = GoChanRecv (Maybe (GoExpr, GoOp)) GoExpr
            | GoChanSend GoExpr GoExpr
              deriving (Eq, Read, Show)

data GoCond = GoCond (Maybe GoSimp) (Maybe GoExpr)
              deriving (Eq, Read, Show)
data GoCase a = GoCase [a] [GoStmt]
              | GoDefault  [GoStmt]
                deriving (Eq, Read, Show)
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
      Maybe (GoExpr, GoOp),
      (GoExpr, GoOp),
      GoCase GoExpr,
      GoCase GoType,
      [GoType],
      GoMethSpec,
      GoFieldType,
      GoTypeSpec]
type CodesGoSource =
    '[ '[ '[ 'I ( 'S  'Z),
           'I ( 'S ( 'S  'Z)),
           'I ( 'S ( 'S ( 'S  'Z)))]],
      '[ '[ 'K  'KString]],
      '[ '[], '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z)))),  'I ( 'S ( 'S  'Z))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))),
           'I ( 'S ( 'S ( 'S  'Z)))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'K  'KString]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))],
        '[ 'I ( 'S  'Z)]],
      '[ '[ 'K  'KString]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))]],
      '[ '[ 'I ( 'S  'Z),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))),
           'I ( 'S  'Z),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S  'Z),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))),
           'I ( 'S  'Z)],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))]],
      '[ '[], '[], '[]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))),
           'I ( 'S  'Z)],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))),
           'I ( 'S  'Z)],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))),
           'I ( 'S  'Z)],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))),
           'K  'KBool]],
      '[ '[ 'K  'KString,  'K  'KInteger],
        '[ 'K  'KString,  'K  'KFloat],
        '[ 'K  'KString,  'K  'KFloat],
        '[ 'K  'KString,  'K  'KChar],
        '[ 'K  'KString,  'K  'KString],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))]],
      '[ '[ 'K  'KBool,
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S  'Z)],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))],
        '[]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))],
        '[ 'I ( 'S  'Z),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S  'Z)],
        '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))]],
      '[ '[], '[ 'I ( 'S  'Z)]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S  'Z),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))],
        '[ 'I ( 'S  'Z)]],
      '[ '[ 'K  'KString,
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))],
        '[ 'K  'KString,
           'K  'KBool,
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))]],
      '[ '[ 'I ( 'S  'Z),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))]]]
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
pattern IdxMaybeTup1GoExprGoOp = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxTup1GoExprGoOp = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoCaseGoExpr = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoCaseGoType = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxListGoType = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoMethSpec = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoFieldType = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxGoTypeSpec = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern GoSource_ ::
          phi_a2Eps ( 'S  'Z)
          -> phi_a2Eps ( 'S ( 'S  'Z))
             -> phi_a2Eps ( 'S ( 'S ( 'S  'Z)))
                -> View kon_a2Ept phi_a2Eps (Lkup  'Z CodesGoSource)
pattern GoSource_ p_a2Epp p_a2Epq p_a2Epr = Tag CZ
                                                (NA_I p_a2Epp :* (NA_I p_a2Epq :* (NA_I p_a2Epr :* NP0)))
pattern GoId_ ::
          kon_a2Epw  'KString
          -> View kon_a2Epw phi_a2Epv (Lkup ( 'S  'Z) CodesGoSource)
pattern GoId_ p_a2Epu = Tag CZ (NA_K p_a2Epu :* NP0)
pattern ListGoPrel_Ifx0 ::
          View kon_a2Epy phi_a2Epx (Lkup ( 'S ( 'S  'Z)) CodesGoSource)
pattern ListGoPrel_Ifx0 = Tag CZ NP0
pattern ListGoPrel_Ifx1 ::
          phi_a2EpB ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> phi_a2EpB ( 'S ( 'S  'Z))
             -> View kon_a2EpC phi_a2EpB (Lkup ( 'S ( 'S  'Z)) CodesGoSource)
pattern ListGoPrel_Ifx1 p_a2Epz p_a2EpA = Tag (CS CZ)
                                              (NA_I p_a2Epz :* (NA_I p_a2EpA :* NP0))
pattern ListGoDecl_Ifx0 ::
          View kon_a2EpE phi_a2EpD (Lkup ( 'S ( 'S ( 'S  'Z))) CodesGoSource)
pattern ListGoDecl_Ifx0 = Tag CZ NP0
pattern ListGoDecl_Ifx1 ::
          phi_a2EpH ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))
          -> phi_a2EpH ( 'S ( 'S ( 'S  'Z)))
             -> View kon_a2EpI phi_a2EpH (Lkup ( 'S ( 'S ( 'S  'Z))) CodesGoSource)
pattern ListGoDecl_Ifx1 p_a2EpF p_a2EpG = Tag (CS CZ)
                                              (NA_I p_a2EpF :* (NA_I p_a2EpG :* NP0))
pattern GoImportDecl_ ::
          phi_a2EpK ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))
          -> View kon_a2EpL phi_a2EpK (Lkup ( 'S ( 'S ( 'S ( 'S  'Z)))) CodesGoSource)
pattern GoImportDecl_ p_a2EpJ = Tag CZ (NA_I p_a2EpJ :* NP0)
pattern ListGoImpSpec_Ifx0 ::
          View kon_a2EpN phi_a2EpM (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))) CodesGoSource)
pattern ListGoImpSpec_Ifx0 = Tag CZ NP0
pattern ListGoImpSpec_Ifx1 ::
          phi_a2EpQ ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))
          -> phi_a2EpQ ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))
             -> View kon_a2EpR phi_a2EpQ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))) CodesGoSource)
pattern ListGoImpSpec_Ifx1 p_a2EpO p_a2EpP = Tag (CS CZ)
                                                 (NA_I p_a2EpO :* (NA_I p_a2EpP :* NP0))
pattern GoImpSpec_ ::
          phi_a2EpU ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> kon_a2EpV  'KString
             -> View kon_a2EpV phi_a2EpU (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))) CodesGoSource)
pattern GoImpSpec_ p_a2EpS p_a2EpT = Tag CZ
                                         (NA_I p_a2EpS :* (NA_K p_a2EpT :* NP0))
pattern GoImp_ ::
          View kon_a2EpX phi_a2EpW (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesGoSource)
pattern GoImp_ = Tag CZ NP0
pattern GoImpDot_ ::
          phi_a2EpZ ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
          -> View kon_a2Eq0 phi_a2EpZ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesGoSource)
pattern GoImpDot_ p_a2EpY = Tag (CS CZ) (NA_I p_a2EpY :* NP0)
pattern GoImpQual_ ::
          phi_a2Eq2 ( 'S  'Z)
          -> View kon_a2Eq3 phi_a2Eq2 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesGoSource)
pattern GoImpQual_ p_a2Eq1 = Tag (CS (CS CZ)) (NA_I p_a2Eq1 :* NP0)
pattern GoOp_ ::
          kon_a2Eq6  'KString
          -> View kon_a2Eq6 phi_a2Eq5 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))) CodesGoSource)
pattern GoOp_ p_a2Eq4 = Tag CZ (NA_K p_a2Eq4 :* NP0)
pattern GoConst_ ::
          phi_a2Eq8 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> View kon_a2Eq9 phi_a2Eq8 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))) CodesGoSource)
pattern GoConst_ p_a2Eq7 = Tag CZ (NA_I p_a2Eq7 :* NP0)
pattern GoType_ ::
          phi_a2Eqb ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))
          -> View kon_a2Eqc phi_a2Eqb (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))) CodesGoSource)
pattern GoType_ p_a2Eqa = Tag (CS CZ) (NA_I p_a2Eqa :* NP0)
pattern GoVar_ ::
          phi_a2Eqe ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> View kon_a2Eqf phi_a2Eqe (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))) CodesGoSource)
pattern GoVar_ p_a2Eqd = Tag (CS (CS CZ)) (NA_I p_a2Eqd :* NP0)
pattern GoFunc_ ::
          phi_a2Eqh ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))
          -> View kon_a2Eqi phi_a2Eqh (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))) CodesGoSource)
pattern GoFunc_ p_a2Eqg = Tag (CS (CS (CS CZ)))
                              (NA_I p_a2Eqg :* NP0)
pattern GoMeth_ ::
          phi_a2Eqk ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))
          -> View kon_a2Eql phi_a2Eqk (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))) CodesGoSource)
pattern GoMeth_ p_a2Eqj = Tag (CS (CS (CS (CS CZ))))
                              (NA_I p_a2Eqj :* NP0)
pattern ListGoCVSpec_Ifx0 ::
          View kon_a2Eqn phi_a2Eqm (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))) CodesGoSource)
pattern ListGoCVSpec_Ifx0 = Tag CZ NP0
pattern ListGoCVSpec_Ifx1 ::
          phi_a2Eqq ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))
          -> phi_a2Eqq ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
             -> View kon_a2Eqr phi_a2Eqq (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))) CodesGoSource)
pattern ListGoCVSpec_Ifx1 p_a2Eqo p_a2Eqp = Tag (CS CZ)
                                                (NA_I p_a2Eqo :* (NA_I p_a2Eqp :* NP0))
pattern ListGoTypeSpec_Ifx0 ::
          View kon_a2Eqt phi_a2Eqs (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))) CodesGoSource)
pattern ListGoTypeSpec_Ifx0 = Tag CZ NP0
pattern ListGoTypeSpec_Ifx1 ::
          phi_a2Eqw ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_a2Eqw ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))
             -> View kon_a2Eqx phi_a2Eqw (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))) CodesGoSource)
pattern ListGoTypeSpec_Ifx1 p_a2Equ p_a2Eqv = Tag (CS CZ)
                                                  (NA_I p_a2Equ :* (NA_I p_a2Eqv :* NP0))
pattern GoFuncDecl_ ::
          phi_a2EqB ( 'S  'Z)
          -> phi_a2EqB ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))
             -> phi_a2EqB ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))
                -> View kon_a2EqC phi_a2EqB (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))) CodesGoSource)
pattern GoFuncDecl_ p_a2Eqy p_a2Eqz p_a2EqA = Tag CZ
                                                  (NA_I p_a2Eqy :* (NA_I p_a2Eqz :* (NA_I p_a2EqA :* NP0)))
pattern GoMethDecl_ ::
          phi_a2EqH ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))
          -> phi_a2EqH ( 'S  'Z)
             -> phi_a2EqH ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))
                -> phi_a2EqH ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))
                   -> View kon_a2EqI phi_a2EqH (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))) CodesGoSource)
pattern GoMethDecl_ p_a2EqD p_a2EqE p_a2EqF p_a2EqG = Tag CZ
                                                          (NA_I p_a2EqD :* (NA_I p_a2EqE :* (NA_I p_a2EqF :* (NA_I p_a2EqG :* NP0))))
pattern GoCVSpec_ ::
          phi_a2EqM ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))
          -> phi_a2EqM ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))
             -> phi_a2EqM ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))
                -> View kon_a2EqN phi_a2EqM (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))) CodesGoSource)
pattern GoCVSpec_ p_a2EqJ p_a2EqK p_a2EqL = Tag CZ
                                                (NA_I p_a2EqJ :* (NA_I p_a2EqK :* (NA_I p_a2EqL :* NP0)))
pattern ListGoId_Ifx0 ::
          View kon_a2EqP phi_a2EqO (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesGoSource)
pattern ListGoId_Ifx0 = Tag CZ NP0
pattern ListGoId_Ifx1 ::
          phi_a2EqS ( 'S  'Z)
          -> phi_a2EqS ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))
             -> View kon_a2EqT phi_a2EqS (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesGoSource)
pattern ListGoId_Ifx1 p_a2EqQ p_a2EqR = Tag (CS CZ)
                                            (NA_I p_a2EqQ :* (NA_I p_a2EqR :* NP0))
pattern MaybeGoTypeNothing_ ::
          View kon_a2EqV phi_a2EqU (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))) CodesGoSource)
pattern MaybeGoTypeNothing_ = Tag CZ NP0
pattern MaybeGoTypeJust_ ::
          phi_a2EqX ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
          -> View kon_a2EqY phi_a2EqX (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))) CodesGoSource)
pattern MaybeGoTypeJust_ p_a2EqW = Tag (CS CZ)
                                       (NA_I p_a2EqW :* NP0)
pattern ListGoExpr_Ifx0 ::
          View kon_a2Er0 phi_a2EqZ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))) CodesGoSource)
pattern ListGoExpr_Ifx0 = Tag CZ NP0
pattern ListGoExpr_Ifx1 ::
          phi_a2Er3 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> phi_a2Er3 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))
             -> View kon_a2Er4 phi_a2Er3 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))) CodesGoSource)
pattern ListGoExpr_Ifx1 p_a2Er1 p_a2Er2 = Tag (CS CZ)
                                              (NA_I p_a2Er1 :* (NA_I p_a2Er2 :* NP0))
pattern GoTypeName_ ::
          phi_a2Er7 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))
          -> phi_a2Er7 ( 'S  'Z)
             -> View kon_a2Er8 phi_a2Er7 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))) CodesGoSource)
pattern GoTypeName_ p_a2Er5 p_a2Er6 = Tag CZ
                                          (NA_I p_a2Er5 :* (NA_I p_a2Er6 :* NP0))
pattern GoArrayType_ ::
          phi_a2Erb ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> phi_a2Erb ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
             -> View kon_a2Erc phi_a2Erb (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))) CodesGoSource)
pattern GoArrayType_ p_a2Er9 p_a2Era = Tag (CS CZ)
                                           (NA_I p_a2Er9 :* (NA_I p_a2Era :* NP0))
pattern GoChannelType_ ::
          phi_a2Erf ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))
          -> phi_a2Erf ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
             -> View kon_a2Erg phi_a2Erf (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))) CodesGoSource)
pattern GoChannelType_ p_a2Erd p_a2Ere = Tag (CS (CS CZ))
                                             (NA_I p_a2Erd :* (NA_I p_a2Ere :* NP0))
pattern GoElipsisType_ ::
          phi_a2Eri ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
          -> View kon_a2Erj phi_a2Eri (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))) CodesGoSource)
pattern GoElipsisType_ p_a2Erh = Tag (CS (CS (CS CZ)))
                                     (NA_I p_a2Erh :* NP0)
pattern GoFunctionType_ ::
          phi_a2Erl ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))
          -> View kon_a2Erm phi_a2Erl (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))) CodesGoSource)
pattern GoFunctionType_ p_a2Erk = Tag (CS (CS (CS (CS CZ))))
                                      (NA_I p_a2Erk :* NP0)
pattern GoInterfaceType_ ::
          phi_a2Ero ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))
          -> View kon_a2Erp phi_a2Ero (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))) CodesGoSource)
pattern GoInterfaceType_ p_a2Ern = Tag (CS (CS (CS (CS (CS CZ)))))
                                       (NA_I p_a2Ern :* NP0)
pattern GoMapType_ ::
          phi_a2Ers ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
          -> phi_a2Ers ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
             -> View kon_a2Ert phi_a2Ers (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))) CodesGoSource)
pattern GoMapType_ p_a2Erq p_a2Err = Tag (CS (CS (CS (CS (CS (CS CZ))))))
                                         (NA_I p_a2Erq :* (NA_I p_a2Err :* NP0))
pattern GoPointerType_ ::
          phi_a2Erv ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
          -> View kon_a2Erw phi_a2Erv (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))) CodesGoSource)
pattern GoPointerType_ p_a2Eru = Tag (CS (CS (CS (CS (CS (CS (CS CZ)))))))
                                     (NA_I p_a2Eru :* NP0)
pattern GoSliceType_ ::
          phi_a2Ery ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
          -> View kon_a2Erz phi_a2Ery (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))) CodesGoSource)
pattern GoSliceType_ p_a2Erx = Tag (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))
                                   (NA_I p_a2Erx :* NP0)
pattern GoStructType_ ::
          phi_a2ErB ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))
          -> View kon_a2ErC phi_a2ErB (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))) CodesGoSource)
pattern GoStructType_ p_a2ErA = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))
                                    (NA_I p_a2ErA :* NP0)
pattern GoPrim_ ::
          phi_a2ErE ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))
          -> View kon_a2ErF phi_a2ErE (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))) CodesGoSource)
pattern GoPrim_ p_a2ErD = Tag CZ (NA_I p_a2ErD :* NP0)
pattern Go1Op_ ::
          phi_a2ErI ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
          -> phi_a2ErI ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
             -> View kon_a2ErJ phi_a2ErI (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))) CodesGoSource)
pattern Go1Op_ p_a2ErG p_a2ErH = Tag (CS CZ)
                                     (NA_I p_a2ErG :* (NA_I p_a2ErH :* NP0))
pattern Go2Op_ ::
          phi_a2ErN ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
          -> phi_a2ErN ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
             -> phi_a2ErN ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
                -> View kon_a2ErO phi_a2ErN (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))) CodesGoSource)
pattern Go2Op_ p_a2ErK p_a2ErL p_a2ErM = Tag (CS (CS CZ))
                                             (NA_I p_a2ErK :* (NA_I p_a2ErL :* (NA_I p_a2ErM :* NP0)))
pattern GoIChan_ ::
          View kon_a2ErQ phi_a2ErP (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))) CodesGoSource)
pattern GoIChan_ = Tag CZ NP0
pattern GoOChan_ ::
          View kon_a2ErS phi_a2ErR (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))) CodesGoSource)
pattern GoOChan_ = Tag (CS CZ) NP0
pattern GoIOChan_ ::
          View kon_a2ErU phi_a2ErT (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))) CodesGoSource)
pattern GoIOChan_ = Tag (CS (CS CZ)) NP0
pattern GoSig_ ::
          phi_a2ErX ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))
          -> phi_a2ErX ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))
             -> View kon_a2ErY phi_a2ErX (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))) CodesGoSource)
pattern GoSig_ p_a2ErV p_a2ErW = Tag CZ
                                     (NA_I p_a2ErV :* (NA_I p_a2ErW :* NP0))
pattern ListGoMethSpec_Ifx0 ::
          View kon_a2Es0 phi_a2ErZ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))) CodesGoSource)
pattern ListGoMethSpec_Ifx0 = Tag CZ NP0
pattern ListGoMethSpec_Ifx1 ::
          phi_a2Es3 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_a2Es3 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))
             -> View kon_a2Es4 phi_a2Es3 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))) CodesGoSource)
pattern ListGoMethSpec_Ifx1 p_a2Es1 p_a2Es2 = Tag (CS CZ)
                                                  (NA_I p_a2Es1 :* (NA_I p_a2Es2 :* NP0))
pattern ListGoFieldType_Ifx0 ::
          View kon_a2Es6 phi_a2Es5 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))) CodesGoSource)
pattern ListGoFieldType_Ifx0 = Tag CZ NP0
pattern ListGoFieldType_Ifx1 ::
          phi_a2Es9 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_a2Es9 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))
             -> View kon_a2Esa phi_a2Es9 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))) CodesGoSource)
pattern ListGoFieldType_Ifx1 p_a2Es7 p_a2Es8 = Tag (CS CZ)
                                                   (NA_I p_a2Es7 :* (NA_I p_a2Es8 :* NP0))
pattern GoLiteral_ ::
          phi_a2Esc ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))
          -> View kon_a2Esd phi_a2Esc (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesGoSource)
pattern GoLiteral_ p_a2Esb = Tag CZ (NA_I p_a2Esb :* NP0)
pattern GoQual_ ::
          phi_a2Esg ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))
          -> phi_a2Esg ( 'S  'Z)
             -> View kon_a2Esh phi_a2Esg (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesGoSource)
pattern GoQual_ p_a2Ese p_a2Esf = Tag (CS CZ)
                                      (NA_I p_a2Ese :* (NA_I p_a2Esf :* NP0))
pattern GoMethod_ ::
          phi_a2Esk ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))
          -> phi_a2Esk ( 'S  'Z)
             -> View kon_a2Esl phi_a2Esk (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesGoSource)
pattern GoMethod_ p_a2Esi p_a2Esj = Tag (CS (CS CZ))
                                        (NA_I p_a2Esi :* (NA_I p_a2Esj :* NP0))
pattern GoParen_ ::
          phi_a2Esn ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> View kon_a2Eso phi_a2Esn (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesGoSource)
pattern GoParen_ p_a2Esm = Tag (CS (CS (CS CZ)))
                               (NA_I p_a2Esm :* NP0)
pattern GoCast_ ::
          phi_a2Esr ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
          -> phi_a2Esr ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
             -> View kon_a2Ess phi_a2Esr (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesGoSource)
pattern GoCast_ p_a2Esp p_a2Esq = Tag (CS (CS (CS (CS CZ))))
                                      (NA_I p_a2Esp :* (NA_I p_a2Esq :* NP0))
pattern GoNew_ ::
          phi_a2Esu ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
          -> View kon_a2Esv phi_a2Esu (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesGoSource)
pattern GoNew_ p_a2Est = Tag (CS (CS (CS (CS (CS CZ)))))
                             (NA_I p_a2Est :* NP0)
pattern GoMake_ ::
          phi_a2Esy ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
          -> phi_a2Esy ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))
             -> View kon_a2Esz phi_a2Esy (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesGoSource)
pattern GoMake_ p_a2Esw p_a2Esx = Tag (CS (CS (CS (CS (CS (CS CZ))))))
                                      (NA_I p_a2Esw :* (NA_I p_a2Esx :* NP0))
pattern GoSelect_ ::
          phi_a2EsC ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))
          -> phi_a2EsC ( 'S  'Z)
             -> View kon_a2EsD phi_a2EsC (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesGoSource)
pattern GoSelect_ p_a2EsA p_a2EsB = Tag (CS (CS (CS (CS (CS (CS (CS CZ)))))))
                                        (NA_I p_a2EsA :* (NA_I p_a2EsB :* NP0))
pattern GoIndex_ ::
          phi_a2EsG ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))
          -> phi_a2EsG ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
             -> View kon_a2EsH phi_a2EsG (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesGoSource)
pattern GoIndex_ p_a2EsE p_a2EsF = Tag (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))
                                       (NA_I p_a2EsE :* (NA_I p_a2EsF :* NP0))
pattern GoSlice_ ::
          phi_a2EsK ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))
          -> phi_a2EsK ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))
             -> View kon_a2EsL phi_a2EsK (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesGoSource)
pattern GoSlice_ p_a2EsI p_a2EsJ = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))
                                       (NA_I p_a2EsI :* (NA_I p_a2EsJ :* NP0))
pattern GoTA_ ::
          phi_a2EsO ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))
          -> phi_a2EsO ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
             -> View kon_a2EsP phi_a2EsO (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesGoSource)
pattern GoTA_ p_a2EsM p_a2EsN = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))
                                    (NA_I p_a2EsM :* (NA_I p_a2EsN :* NP0))
pattern GoCall_ ::
          phi_a2EsT ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))
          -> phi_a2EsT ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))
             -> kon_a2EsU  'KBool
                -> View kon_a2EsU phi_a2EsT (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesGoSource)
pattern GoCall_ p_a2EsQ p_a2EsR p_a2EsS = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))
                                              (NA_I p_a2EsQ :* (NA_I p_a2EsR :* (NA_K p_a2EsS :* NP0)))
pattern GoLitInt_ ::
          kon_a2EsY  'KString
          -> kon_a2EsY  'KInteger
             -> View kon_a2EsY phi_a2EsX (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))) CodesGoSource)
pattern GoLitInt_ p_a2EsV p_a2EsW = Tag CZ
                                        (NA_K p_a2EsV :* (NA_K p_a2EsW :* NP0))
pattern GoLitReal_ ::
          kon_a2Et2  'KString
          -> kon_a2Et2  'KFloat
             -> View kon_a2Et2 phi_a2Et1 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))) CodesGoSource)
pattern GoLitReal_ p_a2EsZ p_a2Et0 = Tag (CS CZ)
                                         (NA_K p_a2EsZ :* (NA_K p_a2Et0 :* NP0))
pattern GoLitImag_ ::
          kon_a2Et6  'KString
          -> kon_a2Et6  'KFloat
             -> View kon_a2Et6 phi_a2Et5 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))) CodesGoSource)
pattern GoLitImag_ p_a2Et3 p_a2Et4 = Tag (CS (CS CZ))
                                         (NA_K p_a2Et3 :* (NA_K p_a2Et4 :* NP0))
pattern GoLitChar_ ::
          kon_a2Eta  'KString
          -> kon_a2Eta  'KChar
             -> View kon_a2Eta phi_a2Et9 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))) CodesGoSource)
pattern GoLitChar_ p_a2Et7 p_a2Et8 = Tag (CS (CS (CS CZ)))
                                         (NA_K p_a2Et7 :* (NA_K p_a2Et8 :* NP0))
pattern GoLitStr_ ::
          kon_a2Ete  'KString
          -> kon_a2Ete  'KString
             -> View kon_a2Ete phi_a2Etd (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))) CodesGoSource)
pattern GoLitStr_ p_a2Etb p_a2Etc = Tag (CS (CS (CS (CS CZ))))
                                        (NA_K p_a2Etb :* (NA_K p_a2Etc :* NP0))
pattern GoLitComp_ ::
          phi_a2Eth ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
          -> phi_a2Eth ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))
             -> View kon_a2Eti phi_a2Eth (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))) CodesGoSource)
pattern GoLitComp_ p_a2Etf p_a2Etg = Tag (CS (CS (CS (CS (CS CZ)))))
                                         (NA_I p_a2Etf :* (NA_I p_a2Etg :* NP0))
pattern GoLitFunc_ ::
          phi_a2Etk ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))
          -> View kon_a2Etl phi_a2Etk (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))) CodesGoSource)
pattern GoLitFunc_ p_a2Etj = Tag (CS (CS (CS (CS (CS (CS CZ))))))
                                 (NA_I p_a2Etj :* NP0)
pattern GoRec_ ::
          kon_a2Etq  'KBool
          -> phi_a2Etp ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))
             -> phi_a2Etp ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
                -> View kon_a2Etq phi_a2Etp (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))) CodesGoSource)
pattern GoRec_ p_a2Etm p_a2Etn p_a2Eto = Tag CZ
                                             (NA_K p_a2Etm :* (NA_I p_a2Etn :* (NA_I p_a2Eto :* NP0)))
pattern GoComp_ ::
          phi_a2Ets ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))
          -> View kon_a2Ett phi_a2Ets (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))) CodesGoSource)
pattern GoComp_ p_a2Etr = Tag CZ (NA_I p_a2Etr :* NP0)
pattern GoFuncExpr_ ::
          phi_a2Etw ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))
          -> phi_a2Etw ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))
             -> View kon_a2Etx phi_a2Etw (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))) CodesGoSource)
pattern GoFuncExpr_ p_a2Etu p_a2Etv = Tag CZ
                                          (NA_I p_a2Etu :* (NA_I p_a2Etv :* NP0))
pattern ListGoElement_Ifx0 ::
          View kon_a2Etz phi_a2Ety (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoElement_Ifx0 = Tag CZ NP0
pattern ListGoElement_Ifx1 ::
          phi_a2EtC ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))
          -> phi_a2EtC ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))
             -> View kon_a2EtD phi_a2EtC (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoElement_Ifx1 p_a2EtA p_a2EtB = Tag (CS CZ)
                                                 (NA_I p_a2EtA :* (NA_I p_a2EtB :* NP0))
pattern GoElement_ ::
          phi_a2EtG ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))
          -> phi_a2EtG ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))
             -> View kon_a2EtH phi_a2EtG (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesGoSource)
pattern GoElement_ p_a2EtE p_a2EtF = Tag CZ
                                         (NA_I p_a2EtE :* (NA_I p_a2EtF :* NP0))
pattern GoKeyNone_ ::
          View kon_a2EtJ phi_a2EtI (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoKeyNone_ = Tag CZ NP0
pattern GoKeyField_ ::
          phi_a2EtL ( 'S  'Z)
          -> View kon_a2EtM phi_a2EtL (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoKeyField_ p_a2EtK = Tag (CS CZ) (NA_I p_a2EtK :* NP0)
pattern GoKeyIndex_ ::
          phi_a2EtO ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> View kon_a2EtP phi_a2EtO (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoKeyIndex_ p_a2EtN = Tag (CS (CS CZ))
                                  (NA_I p_a2EtN :* NP0)
pattern GoValueExpr_ ::
          phi_a2EtR ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> View kon_a2EtS phi_a2EtR (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoValueExpr_ p_a2EtQ = Tag CZ (NA_I p_a2EtQ :* NP0)
pattern GoValueComp_ ::
          phi_a2EtU ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))
          -> View kon_a2EtV phi_a2EtU (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoValueComp_ p_a2EtT = Tag (CS CZ) (NA_I p_a2EtT :* NP0)
pattern GoBlock_ ::
          phi_a2EtX ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))
          -> View kon_a2EtY phi_a2EtX (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoBlock_ p_a2EtW = Tag CZ (NA_I p_a2EtW :* NP0)
pattern GoNoBlock_ ::
          View kon_a2Eu0 phi_a2EtZ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoNoBlock_ = Tag (CS CZ) NP0
pattern ListGoParam_Ifx0 ::
          View kon_a2Eu2 phi_a2Eu1 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoParam_Ifx0 = Tag CZ NP0
pattern ListGoParam_Ifx1 ::
          phi_a2Eu5 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))
          -> phi_a2Eu5 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))
             -> View kon_a2Eu6 phi_a2Eu5 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoParam_Ifx1 p_a2Eu3 p_a2Eu4 = Tag (CS CZ)
                                               (NA_I p_a2Eu3 :* (NA_I p_a2Eu4 :* NP0))
pattern GoParam_ ::
          phi_a2Eu9 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))
          -> phi_a2Eu9 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
             -> View kon_a2Eua phi_a2Eu9 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoParam_ p_a2Eu7 p_a2Eu8 = Tag CZ
                                       (NA_I p_a2Eu7 :* (NA_I p_a2Eu8 :* NP0))
pattern ListGoStmt_Ifx0 ::
          View kon_a2Euc phi_a2Eub (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoStmt_Ifx0 = Tag CZ NP0
pattern ListGoStmt_Ifx1 ::
          phi_a2Euf ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))
          -> phi_a2Euf ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))
             -> View kon_a2Eug phi_a2Euf (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoStmt_Ifx1 p_a2Eud p_a2Eue = Tag (CS CZ)
                                              (NA_I p_a2Eud :* (NA_I p_a2Eue :* NP0))
pattern GoStmtDecl_ ::
          phi_a2Eui ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))
          -> View kon_a2Euj phi_a2Eui (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtDecl_ p_a2Euh = Tag CZ (NA_I p_a2Euh :* NP0)
pattern GoStmtLabeled_ ::
          phi_a2Eum ( 'S  'Z)
          -> phi_a2Eum ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))
             -> View kon_a2Eun phi_a2Eum (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtLabeled_ p_a2Euk p_a2Eul = Tag (CS CZ)
                                             (NA_I p_a2Euk :* (NA_I p_a2Eul :* NP0))
pattern GoStmtSimple_ ::
          phi_a2Eup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))
          -> View kon_a2Euq phi_a2Eup (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtSimple_ p_a2Euo = Tag (CS (CS CZ))
                                    (NA_I p_a2Euo :* NP0)
pattern GoStmtGo_ ::
          phi_a2Eus ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> View kon_a2Eut phi_a2Eus (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtGo_ p_a2Eur = Tag (CS (CS (CS CZ)))
                                (NA_I p_a2Eur :* NP0)
pattern GoStmtReturn_ ::
          phi_a2Euv ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))
          -> View kon_a2Euw phi_a2Euv (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtReturn_ p_a2Euu = Tag (CS (CS (CS (CS CZ))))
                                    (NA_I p_a2Euu :* NP0)
pattern GoStmtBreak_ ::
          phi_a2Euy ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))
          -> View kon_a2Euz phi_a2Euy (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtBreak_ p_a2Eux = Tag (CS (CS (CS (CS (CS CZ)))))
                                   (NA_I p_a2Eux :* NP0)
pattern GoStmtContinue_ ::
          phi_a2EuB ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))
          -> View kon_a2EuC phi_a2EuB (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtContinue_ p_a2EuA = Tag (CS (CS (CS (CS (CS (CS CZ))))))
                                      (NA_I p_a2EuA :* NP0)
pattern GoStmtGoto_ ::
          phi_a2EuE ( 'S  'Z)
          -> View kon_a2EuF phi_a2EuE (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtGoto_ p_a2EuD = Tag (CS (CS (CS (CS (CS (CS (CS CZ)))))))
                                  (NA_I p_a2EuD :* NP0)
pattern GoStmtFallthrough_ ::
          View kon_a2EuH phi_a2EuG (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtFallthrough_ = Tag (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))
                                 NP0
pattern GoStmtBlock_ ::
          phi_a2EuJ ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))
          -> View kon_a2EuK phi_a2EuJ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtBlock_ p_a2EuI = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))
                                   (NA_I p_a2EuI :* NP0)
pattern GoStmtIf_ ::
          phi_a2EuO ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))
          -> phi_a2EuO ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))
             -> phi_a2EuO ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))
                -> View kon_a2EuP phi_a2EuO (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtIf_ p_a2EuL p_a2EuM p_a2EuN = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))
                                                (NA_I p_a2EuL :* (NA_I p_a2EuM :* (NA_I p_a2EuN :* NP0)))
pattern GoStmtSelect_ ::
          phi_a2EuR ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))
          -> View kon_a2EuS phi_a2EuR (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtSelect_ p_a2EuQ = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))
                                    (NA_I p_a2EuQ :* NP0)
pattern GoStmtSwitch_ ::
          phi_a2EuV ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))
          -> phi_a2EuV ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))
             -> View kon_a2EuW phi_a2EuV (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtSwitch_ p_a2EuT p_a2EuU = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))
                                            (NA_I p_a2EuT :* (NA_I p_a2EuU :* NP0))
pattern GoStmtTypeSwitch_ ::
          phi_a2Ev0 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))
          -> phi_a2Ev0 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))
             -> phi_a2Ev0 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))
                -> View kon_a2Ev1 phi_a2Ev0 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtTypeSwitch_ p_a2EuX p_a2EuY p_a2EuZ = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))
                                                        (NA_I p_a2EuX :* (NA_I p_a2EuY :* (NA_I p_a2EuZ :* NP0)))
pattern GoStmtFor_ ::
          phi_a2Ev4 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))
          -> phi_a2Ev4 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))
             -> View kon_a2Ev5 phi_a2Ev4 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtFor_ p_a2Ev2 p_a2Ev3 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))
                                         (NA_I p_a2Ev2 :* (NA_I p_a2Ev3 :* NP0))
pattern GoStmtDefer_ ::
          phi_a2Ev7 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> View kon_a2Ev8 phi_a2Ev7 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoStmtDefer_ p_a2Ev6 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))
                                   (NA_I p_a2Ev6 :* NP0)
pattern GoSimpEmpty_ ::
          View kon_a2Eva phi_a2Ev9 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoSimpEmpty_ = Tag CZ NP0
pattern GoSimpRecv_ ::
          phi_a2Evc ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> View kon_a2Evd phi_a2Evc (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoSimpRecv_ p_a2Evb = Tag (CS CZ) (NA_I p_a2Evb :* NP0)
pattern GoSimpSend_ ::
          phi_a2Evg ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> phi_a2Evg ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
             -> View kon_a2Evh phi_a2Evg (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoSimpSend_ p_a2Eve p_a2Evf = Tag (CS (CS CZ))
                                          (NA_I p_a2Eve :* (NA_I p_a2Evf :* NP0))
pattern GoSimpExpr_ ::
          phi_a2Evj ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> View kon_a2Evk phi_a2Evj (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoSimpExpr_ p_a2Evi = Tag (CS (CS (CS CZ)))
                                  (NA_I p_a2Evi :* NP0)
pattern GoSimpInc_ ::
          phi_a2Evm ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> View kon_a2Evn phi_a2Evm (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoSimpInc_ p_a2Evl = Tag (CS (CS (CS (CS CZ))))
                                 (NA_I p_a2Evl :* NP0)
pattern GoSimpDec_ ::
          phi_a2Evp ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> View kon_a2Evq phi_a2Evp (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoSimpDec_ p_a2Evo = Tag (CS (CS (CS (CS (CS CZ)))))
                                 (NA_I p_a2Evo :* NP0)
pattern GoSimpAsn_ ::
          phi_a2Evu ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))
          -> phi_a2Evu ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
             -> phi_a2Evu ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))
                -> View kon_a2Evv phi_a2Evu (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoSimpAsn_ p_a2Evr p_a2Evs p_a2Evt = Tag (CS (CS (CS (CS (CS (CS CZ))))))
                                                 (NA_I p_a2Evr :* (NA_I p_a2Evs :* (NA_I p_a2Evt :* NP0)))
pattern GoSimpVar_ ::
          phi_a2Evy ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))
          -> phi_a2Evy ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))
             -> View kon_a2Evz phi_a2Evy (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoSimpVar_ p_a2Evw p_a2Evx = Tag (CS (CS (CS (CS (CS (CS (CS CZ)))))))
                                         (NA_I p_a2Evw :* (NA_I p_a2Evx :* NP0))
pattern MaybeGoIdNothing_ ::
          View kon_a2EvB phi_a2EvA (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern MaybeGoIdNothing_ = Tag CZ NP0
pattern MaybeGoIdJust_ ::
          phi_a2EvD ( 'S  'Z)
          -> View kon_a2EvE phi_a2EvD (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern MaybeGoIdJust_ p_a2EvC = Tag (CS CZ) (NA_I p_a2EvC :* NP0)
pattern GoCond_ ::
          phi_a2EvH ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_a2EvH ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))
             -> View kon_a2EvI phi_a2EvH (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoCond_ p_a2EvF p_a2EvG = Tag CZ
                                      (NA_I p_a2EvF :* (NA_I p_a2EvG :* NP0))
pattern MaybeGoStmtNothing_ ::
          View kon_a2EvK phi_a2EvJ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern MaybeGoStmtNothing_ = Tag CZ NP0
pattern MaybeGoStmtJust_ ::
          phi_a2EvM ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))
          -> View kon_a2EvN phi_a2EvM (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern MaybeGoStmtJust_ p_a2EvL = Tag (CS CZ)
                                       (NA_I p_a2EvL :* NP0)
pattern ListGoCaseGoChan_Ifx0 ::
          View kon_a2EvP phi_a2EvO (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoCaseGoChan_Ifx0 = Tag CZ NP0
pattern ListGoCaseGoChan_Ifx1 ::
          phi_a2EvS ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_a2EvS ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))
             -> View kon_a2EvT phi_a2EvS (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoCaseGoChan_Ifx1 p_a2EvQ p_a2EvR = Tag (CS CZ)
                                                    (NA_I p_a2EvQ :* (NA_I p_a2EvR :* NP0))
pattern ListGoCaseGoExpr_Ifx0 ::
          View kon_a2EvV phi_a2EvU (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoCaseGoExpr_Ifx0 = Tag CZ NP0
pattern ListGoCaseGoExpr_Ifx1 ::
          phi_a2EvY ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_a2EvY ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))
             -> View kon_a2EvZ phi_a2EvY (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoCaseGoExpr_Ifx1 p_a2EvW p_a2EvX = Tag (CS CZ)
                                                    (NA_I p_a2EvW :* (NA_I p_a2EvX :* NP0))
pattern ListGoCaseGoType_Ifx0 ::
          View kon_a2Ew1 phi_a2Ew0 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoCaseGoType_Ifx0 = Tag CZ NP0
pattern ListGoCaseGoType_Ifx1 ::
          phi_a2Ew4 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_a2Ew4 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))
             -> View kon_a2Ew5 phi_a2Ew4 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoCaseGoType_Ifx1 p_a2Ew2 p_a2Ew3 = Tag (CS CZ)
                                                    (NA_I p_a2Ew2 :* (NA_I p_a2Ew3 :* NP0))
pattern GoForWhile_ ::
          phi_a2Ew7 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> View kon_a2Ew8 phi_a2Ew7 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoForWhile_ p_a2Ew6 = Tag CZ (NA_I p_a2Ew6 :* NP0)
pattern GoForThree_ ::
          phi_a2Ewc ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))
          -> phi_a2Ewc ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))
             -> phi_a2Ewc ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))
                -> View kon_a2Ewd phi_a2Ewc (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoForThree_ p_a2Ew9 p_a2Ewa p_a2Ewb = Tag (CS CZ)
                                                  (NA_I p_a2Ew9 :* (NA_I p_a2Ewa :* (NA_I p_a2Ewb :* NP0)))
pattern GoForRange_ ::
          phi_a2Ewg ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))
          -> phi_a2Ewg ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
             -> View kon_a2Ewh phi_a2Ewg (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoForRange_ p_a2Ewe p_a2Ewf = Tag (CS (CS CZ))
                                          (NA_I p_a2Ewe :* (NA_I p_a2Ewf :* NP0))
pattern MaybeGoSimpNothing_ ::
          View kon_a2Ewj phi_a2Ewi (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern MaybeGoSimpNothing_ = Tag CZ NP0
pattern MaybeGoSimpJust_ ::
          phi_a2Ewl ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))
          -> View kon_a2Ewm phi_a2Ewl (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern MaybeGoSimpJust_ p_a2Ewk = Tag (CS CZ)
                                       (NA_I p_a2Ewk :* NP0)
pattern MaybeGoExprNothing_ ::
          View kon_a2Ewo phi_a2Ewn (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern MaybeGoExprNothing_ = Tag CZ NP0
pattern MaybeGoExprJust_ ::
          phi_a2Ewq ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> View kon_a2Ewr phi_a2Ewq (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern MaybeGoExprJust_ p_a2Ewp = Tag (CS CZ)
                                       (NA_I p_a2Ewp :* NP0)
pattern GoCaseGoChanGoCase_ ::
          phi_a2Ewu ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_a2Ewu ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))
             -> View kon_a2Ewv phi_a2Ewu (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoCaseGoChanGoCase_ p_a2Ews p_a2Ewt = Tag CZ
                                                  (NA_I p_a2Ews :* (NA_I p_a2Ewt :* NP0))
pattern GoCaseGoChanGoDefault_ ::
          phi_a2Ewx ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))
          -> View kon_a2Ewy phi_a2Ewx (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoCaseGoChanGoDefault_ p_a2Eww = Tag (CS CZ)
                                             (NA_I p_a2Eww :* NP0)
pattern ListGoChan_Ifx0 ::
          View kon_a2EwA phi_a2Ewz (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoChan_Ifx0 = Tag CZ NP0
pattern ListGoChan_Ifx1 ::
          phi_a2EwD ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_a2EwD ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))
             -> View kon_a2EwE phi_a2EwD (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoChan_Ifx1 p_a2EwB p_a2EwC = Tag (CS CZ)
                                              (NA_I p_a2EwB :* (NA_I p_a2EwC :* NP0))
pattern GoChanRecv_ ::
          phi_a2EwH ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_a2EwH ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
             -> View kon_a2EwI phi_a2EwH (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoChanRecv_ p_a2EwF p_a2EwG = Tag CZ
                                          (NA_I p_a2EwF :* (NA_I p_a2EwG :* NP0))
pattern GoChanSend_ ::
          phi_a2EwL ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> phi_a2EwL ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
             -> View kon_a2EwM phi_a2EwL (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoChanSend_ p_a2EwJ p_a2EwK = Tag (CS CZ)
                                          (NA_I p_a2EwJ :* (NA_I p_a2EwK :* NP0))
pattern MaybeTup1GoExprGoOpNothing_ ::
          View kon_a2EwO phi_a2EwN (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern MaybeTup1GoExprGoOpNothing_ = Tag CZ NP0
pattern MaybeTup1GoExprGoOpJust_ ::
          phi_a2EwQ ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> View kon_a2EwR phi_a2EwQ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern MaybeTup1GoExprGoOpJust_ p_a2EwP = Tag (CS CZ)
                                               (NA_I p_a2EwP :* NP0)
pattern Tup1GoExprGoOp_Ifx0 ::
          phi_a2EwU ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> phi_a2EwU ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
             -> View kon_a2EwV phi_a2EwU (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern Tup1GoExprGoOp_Ifx0 p_a2EwS p_a2EwT = Tag CZ
                                                  (NA_I p_a2EwS :* (NA_I p_a2EwT :* NP0))
pattern GoCaseGoExprGoCase_ ::
          phi_a2EwY ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))
          -> phi_a2EwY ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))
             -> View kon_a2EwZ phi_a2EwY (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoCaseGoExprGoCase_ p_a2EwW p_a2EwX = Tag CZ
                                                  (NA_I p_a2EwW :* (NA_I p_a2EwX :* NP0))
pattern GoCaseGoExprGoDefault_ ::
          phi_a2Ex1 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))
          -> View kon_a2Ex2 phi_a2Ex1 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoCaseGoExprGoDefault_ p_a2Ex0 = Tag (CS CZ)
                                             (NA_I p_a2Ex0 :* NP0)
pattern GoCaseGoTypeGoCase_ ::
          phi_a2Ex5 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_a2Ex5 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))
             -> View kon_a2Ex6 phi_a2Ex5 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoCaseGoTypeGoCase_ p_a2Ex3 p_a2Ex4 = Tag CZ
                                                  (NA_I p_a2Ex3 :* (NA_I p_a2Ex4 :* NP0))
pattern GoCaseGoTypeGoDefault_ ::
          phi_a2Ex8 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))
          -> View kon_a2Ex9 phi_a2Ex8 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoCaseGoTypeGoDefault_ p_a2Ex7 = Tag (CS CZ)
                                             (NA_I p_a2Ex7 :* NP0)
pattern ListGoType_Ifx0 ::
          View kon_a2Exb phi_a2Exa (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoType_Ifx0 = Tag CZ NP0
pattern ListGoType_Ifx1 ::
          phi_a2Exe ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
          -> phi_a2Exe ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))
             -> View kon_a2Exf phi_a2Exe (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern ListGoType_Ifx1 p_a2Exc p_a2Exd = Tag (CS CZ)
                                              (NA_I p_a2Exc :* (NA_I p_a2Exd :* NP0))
pattern GoMethSpec_ ::
          phi_a2Exi ( 'S  'Z)
          -> phi_a2Exi ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))
             -> View kon_a2Exj phi_a2Exi (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoMethSpec_ p_a2Exg p_a2Exh = Tag CZ
                                          (NA_I p_a2Exg :* (NA_I p_a2Exh :* NP0))
pattern GoInterface_ ::
          phi_a2Exl ( 'S  'Z)
          -> View kon_a2Exm phi_a2Exl (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoInterface_ p_a2Exk = Tag (CS CZ) (NA_I p_a2Exk :* NP0)
pattern GoFieldType_ ::
          kon_a2Exr  'KString
          -> phi_a2Exq ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))
             -> phi_a2Exq ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
                -> View kon_a2Exr phi_a2Exq (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoFieldType_ p_a2Exn p_a2Exo p_a2Exp = Tag CZ
                                                   (NA_K p_a2Exn :* (NA_I p_a2Exo :* (NA_I p_a2Exp :* NP0)))
pattern GoFieldAnon_ ::
          kon_a2Exw  'KString
          -> kon_a2Exw  'KBool
             -> phi_a2Exv ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
                -> View kon_a2Exw phi_a2Exv (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoFieldAnon_ p_a2Exs p_a2Ext p_a2Exu = Tag (CS CZ)
                                                   (NA_K p_a2Exs :* (NA_K p_a2Ext :* (NA_I p_a2Exu :* NP0)))
pattern GoTypeSpec_ ::
          phi_a2Exz ( 'S  'Z)
          -> phi_a2Exz ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
             -> View kon_a2ExA phi_a2Exz (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) CodesGoSource)
pattern GoTypeSpec_ p_a2Exx p_a2Exy = Tag CZ
                                          (NA_I p_a2Exx :* (NA_I p_a2Exy :* NP0))
instance Family Singl FamGoSource CodesGoSource where
  sfrom'
    = \case
        IdxGoSource
          -> \case
               El (GoSource x_a2ExB x_a2ExC x_a2ExD)
                 -> Rep
                      (H
                         (NA_I (El x_a2ExB)
                            :* (NA_I (El x_a2ExC) :* (NA_I (El x_a2ExD) :* NP0))))
        IdxGoId
          -> \case
               El (GoId x_a2ExE)
                 -> Rep
                      (H (NA_K (SString x_a2ExE) :* NP0))
        IdxListGoPrel
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2ExF x_a2ExG)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2ExF) :* (NA_I (El x_a2ExG) :* NP0))))
        IdxListGoDecl
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2ExH x_a2ExI)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2ExH) :* (NA_I (El x_a2ExI) :* NP0))))
        IdxGoPrel
          -> \case
               El (GoImportDecl x_a2ExJ)
                 -> Rep (H (NA_I (El x_a2ExJ) :* NP0))
        IdxListGoImpSpec
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2ExK x_a2ExL)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2ExK) :* (NA_I (El x_a2ExL) :* NP0))))
        IdxGoImpSpec
          -> \case
               El (GoImpSpec x_a2ExM x_a2ExN)
                 -> Rep
                      (H
                         (NA_I (El x_a2ExM) :* (NA_K (SString x_a2ExN) :* NP0)))
        IdxGoImpType
          -> \case
               El GoImp -> Rep (H NP0)
               El (GoImpDot x_a2ExO)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2ExO) :* NP0)))
               El (GoImpQual x_a2ExP)
                 -> Rep
                      (T
                         (T
                            (H (NA_I (El x_a2ExP) :* NP0))))
        IdxGoOp
          -> \case
               El (GoOp x_a2ExQ)
                 -> Rep
                      (H (NA_K (SString x_a2ExQ) :* NP0))
        IdxGoDecl
          -> \case
               El (GoConst x_a2ExR)
                 -> Rep (H (NA_I (El x_a2ExR) :* NP0))
               El (GoType x_a2ExS)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2ExS) :* NP0)))
               El (GoVar x_a2ExT)
                 -> Rep
                      (T
                         (T
                            (H (NA_I (El x_a2ExT) :* NP0))))
               El (GoFunc x_a2ExU)
                 -> Rep
                      (T
                         (T
                            (T
                               (H (NA_I (El x_a2ExU) :* NP0)))))
               El (GoMeth x_a2ExV)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (H
                                     (NA_I (El x_a2ExV) :* NP0))))))
        IdxListGoCVSpec
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2ExW x_a2ExX)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2ExW) :* (NA_I (El x_a2ExX) :* NP0))))
        IdxListGoTypeSpec
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2ExY x_a2ExZ)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2ExY) :* (NA_I (El x_a2ExZ) :* NP0))))
        IdxGoFuncDecl
          -> \case
               El (GoFuncDecl x_a2Ey0 x_a2Ey1 x_a2Ey2)
                 -> Rep
                      (H
                         (NA_I (El x_a2Ey0)
                            :* (NA_I (El x_a2Ey1) :* (NA_I (El x_a2Ey2) :* NP0))))
        IdxGoMethDecl
          -> \case
               El (GoMethDecl x_a2Ey3 x_a2Ey4 x_a2Ey5 x_a2Ey6)
                 -> Rep
                      (H
                         (NA_I (El x_a2Ey3)
                            :*
                              (NA_I (El x_a2Ey4)
                                 :* (NA_I (El x_a2Ey5) :* (NA_I (El x_a2Ey6) :* NP0)))))
        IdxGoCVSpec
          -> \case
               El (GoCVSpec x_a2Ey7 x_a2Ey8 x_a2Ey9)
                 -> Rep
                      (H
                         (NA_I (El x_a2Ey7)
                            :* (NA_I (El x_a2Ey8) :* (NA_I (El x_a2Ey9) :* NP0))))
        IdxListGoId
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2Eya x_a2Eyb)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2Eya) :* (NA_I (El x_a2Eyb) :* NP0))))
        IdxMaybeGoType
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_a2Eyc)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2Eyc) :* NP0)))
        IdxListGoExpr
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2Eyd x_a2Eye)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2Eyd) :* (NA_I (El x_a2Eye) :* NP0))))
        IdxGoType
          -> \case
               El (GoTypeName x_a2Eyf x_a2Eyg)
                 -> Rep
                      (H
                         (NA_I (El x_a2Eyf) :* (NA_I (El x_a2Eyg) :* NP0)))
               El (GoArrayType x_a2Eyh x_a2Eyi)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2Eyh) :* (NA_I (El x_a2Eyi) :* NP0))))
               El (GoChannelType x_a2Eyj x_a2Eyk)
                 -> Rep
                      (T
                         (T
                            (H
                               (NA_I (El x_a2Eyj) :* (NA_I (El x_a2Eyk) :* NP0)))))
               El (GoElipsisType x_a2Eyl)
                 -> Rep
                      (T
                         (T
                            (T
                               (H (NA_I (El x_a2Eyl) :* NP0)))))
               El (GoFunctionType x_a2Eym)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (H
                                     (NA_I (El x_a2Eym) :* NP0))))))
               El (GoInterfaceType x_a2Eyn)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (H
                                        (NA_I (El x_a2Eyn) :* NP0)))))))
               El (GoMapType x_a2Eyo x_a2Eyp)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (H
                                           (NA_I (El x_a2Eyo)
                                              :* (NA_I (El x_a2Eyp) :* NP0)))))))))
               El (GoPointerType x_a2Eyq)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (H
                                              (NA_I (El x_a2Eyq) :* NP0)))))))))
               El (GoSliceType x_a2Eyr)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (H
                                                 (NA_I (El x_a2Eyr) :* NP0))))))))))
               El (GoStructType x_a2Eys)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (T
                                                 (H
                                                    (NA_I (El x_a2Eys) :* NP0)))))))))))
        IdxGoExpr
          -> \case
               El (GoPrim x_a2Eyt)
                 -> Rep (H (NA_I (El x_a2Eyt) :* NP0))
               El (Go1Op x_a2Eyu x_a2Eyv)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2Eyu) :* (NA_I (El x_a2Eyv) :* NP0))))
               El (Go2Op x_a2Eyw x_a2Eyx x_a2Eyy)
                 -> Rep
                      (T
                         (T
                            (H
                               (NA_I (El x_a2Eyw)
                                  :* (NA_I (El x_a2Eyx) :* (NA_I (El x_a2Eyy) :* NP0))))))
        IdxGoChanKind
          -> \case
               El GoIChan -> Rep (H NP0)
               El GoOChan
                 -> Rep
                      (T
                         (H NP0))
               El GoIOChan
                 -> Rep
                      (T
                         (T
                            (H NP0)))
        IdxGoSig
          -> \case
               El (GoSig x_a2Eyz x_a2EyA)
                 -> Rep
                      (H
                         (NA_I (El x_a2Eyz) :* (NA_I (El x_a2EyA) :* NP0)))
        IdxListGoMethSpec
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2EyB x_a2EyC)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2EyB) :* (NA_I (El x_a2EyC) :* NP0))))
        IdxListGoFieldType
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2EyD x_a2EyE)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2EyD) :* (NA_I (El x_a2EyE) :* NP0))))
        IdxGoPrim
          -> \case
               El (GoLiteral x_a2EyF)
                 -> Rep (H (NA_I (El x_a2EyF) :* NP0))
               El (GoQual x_a2EyG x_a2EyH)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2EyG) :* (NA_I (El x_a2EyH) :* NP0))))
               El (GoMethod x_a2EyI x_a2EyJ)
                 -> Rep
                      (T
                         (T
                            (H
                               (NA_I (El x_a2EyI) :* (NA_I (El x_a2EyJ) :* NP0)))))
               El (GoParen x_a2EyK)
                 -> Rep
                      (T
                         (T
                            (T
                               (H (NA_I (El x_a2EyK) :* NP0)))))
               El (GoCast x_a2EyL x_a2EyM)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (H
                                     (NA_I (El x_a2EyL) :* (NA_I (El x_a2EyM) :* NP0)))))))
               El (GoNew x_a2EyN)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (H
                                        (NA_I (El x_a2EyN) :* NP0)))))))
               El (GoMake x_a2EyO x_a2EyP)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (H
                                           (NA_I (El x_a2EyO)
                                              :* (NA_I (El x_a2EyP) :* NP0)))))))))
               El (GoSelect x_a2EyQ x_a2EyR)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (H
                                              (NA_I (El x_a2EyQ)
                                                 :* (NA_I (El x_a2EyR) :* NP0))))))))))
               El (GoIndex x_a2EyS x_a2EyT)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (H
                                                 (NA_I (El x_a2EyS)
                                                    :* (NA_I (El x_a2EyT) :* NP0)))))))))))
               El (GoSlice x_a2EyU x_a2EyV)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (T
                                                 (H
                                                    (NA_I (El x_a2EyU)
                                                       :* (NA_I (El x_a2EyV) :* NP0))))))))))))
               El (GoTA x_a2EyW x_a2EyX)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (T
                                                 (T
                                                    (H
                                                       (NA_I (El x_a2EyW)
                                                          :*
                                                            (NA_I (El x_a2EyX)
                                                               :* NP0)))))))))))))
               El (GoCall x_a2EyY x_a2EyZ x_a2Ez0)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (T
                                                 (T
                                                    (T
                                                       (H
                                                          (NA_I (El x_a2EyY)
                                                             :*
                                                               (NA_I (El x_a2EyZ)
                                                                  :*
                                                                    (NA_K (SBool x_a2Ez0)
                                                                       :* NP0)))))))))))))))
        IdxGoLit
          -> \case
               El (GoLitInt x_a2Ez1 x_a2Ez2)
                 -> Rep
                      (H
                         (NA_K (SString x_a2Ez1) :* (NA_K (SInteger x_a2Ez2) :* NP0)))
               El (GoLitReal x_a2Ez3 x_a2Ez4)
                 -> Rep
                      (T
                         (H
                            (NA_K (SString x_a2Ez3) :* (NA_K (SFloat x_a2Ez4) :* NP0))))
               El (GoLitImag x_a2Ez5 x_a2Ez6)
                 -> Rep
                      (T
                         (T
                            (H
                               (NA_K (SString x_a2Ez5) :* (NA_K (SFloat x_a2Ez6) :* NP0)))))
               El (GoLitChar x_a2Ez7 x_a2Ez8)
                 -> Rep
                      (T
                         (T
                            (T
                               (H
                                  (NA_K (SString x_a2Ez7)
                                     :* (NA_K (SChar x_a2Ez8) :* NP0))))))
               El (GoLitStr x_a2Ez9 x_a2Eza)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (H
                                     (NA_K (SString x_a2Ez9)
                                        :* (NA_K (SString x_a2Eza) :* NP0)))))))
               El (GoLitComp x_a2Ezb x_a2Ezc)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (H
                                        (NA_I (El x_a2Ezb) :* (NA_I (El x_a2Ezc) :* NP0))))))))
               El (GoLitFunc x_a2Ezd)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (H
                                           (NA_I (El x_a2Ezd) :* NP0))))))))
        IdxGoRec
          -> \case
               El (GoRec x_a2Eze x_a2Ezf x_a2Ezg)
                 -> Rep
                      (H
                         (NA_K (SBool x_a2Eze)
                            :* (NA_I (El x_a2Ezf) :* (NA_I (El x_a2Ezg) :* NP0))))
        IdxGoComp
          -> \case
               El (GoComp x_a2Ezh)
                 -> Rep (H (NA_I (El x_a2Ezh) :* NP0))
        IdxGoFuncExpr
          -> \case
               El (GoFuncExpr x_a2Ezi x_a2Ezj)
                 -> Rep
                      (H
                         (NA_I (El x_a2Ezi) :* (NA_I (El x_a2Ezj) :* NP0)))
        IdxListGoElement
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2Ezk x_a2Ezl)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2Ezk) :* (NA_I (El x_a2Ezl) :* NP0))))
        IdxGoElement
          -> \case
               El (GoElement x_a2Ezm x_a2Ezn)
                 -> Rep
                      (H
                         (NA_I (El x_a2Ezm) :* (NA_I (El x_a2Ezn) :* NP0)))
        IdxGoKey
          -> \case
               El GoKeyNone -> Rep (H NP0)
               El (GoKeyField x_a2Ezo)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2Ezo) :* NP0)))
               El (GoKeyIndex x_a2Ezp)
                 -> Rep
                      (T
                         (T
                            (H (NA_I (El x_a2Ezp) :* NP0))))
        IdxGoValue
          -> \case
               El (GoValueExpr x_a2Ezq)
                 -> Rep (H (NA_I (El x_a2Ezq) :* NP0))
               El (GoValueComp x_a2Ezr)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2Ezr) :* NP0)))
        IdxGoBlock
          -> \case
               El (GoBlock x_a2Ezs)
                 -> Rep (H (NA_I (El x_a2Ezs) :* NP0))
               El GoNoBlock
                 -> Rep
                      (T
                         (H NP0))
        IdxListGoParam
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2Ezt x_a2Ezu)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2Ezt) :* (NA_I (El x_a2Ezu) :* NP0))))
        IdxGoParam
          -> \case
               El (GoParam x_a2Ezv x_a2Ezw)
                 -> Rep
                      (H
                         (NA_I (El x_a2Ezv) :* (NA_I (El x_a2Ezw) :* NP0)))
        IdxListGoStmt
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2Ezx x_a2Ezy)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2Ezx) :* (NA_I (El x_a2Ezy) :* NP0))))
        IdxGoStmt
          -> \case
               El (GoStmtDecl x_a2Ezz)
                 -> Rep (H (NA_I (El x_a2Ezz) :* NP0))
               El (GoStmtLabeled x_a2EzA x_a2EzB)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2EzA) :* (NA_I (El x_a2EzB) :* NP0))))
               El (GoStmtSimple x_a2EzC)
                 -> Rep
                      (T
                         (T
                            (H (NA_I (El x_a2EzC) :* NP0))))
               El (GoStmtGo x_a2EzD)
                 -> Rep
                      (T
                         (T
                            (T
                               (H (NA_I (El x_a2EzD) :* NP0)))))
               El (GoStmtReturn x_a2EzE)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (H
                                     (NA_I (El x_a2EzE) :* NP0))))))
               El (GoStmtBreak x_a2EzF)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (H
                                        (NA_I (El x_a2EzF) :* NP0)))))))
               El (GoStmtContinue x_a2EzG)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (H
                                           (NA_I (El x_a2EzG) :* NP0))))))))
               El (GoStmtGoto x_a2EzH)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (H
                                              (NA_I (El x_a2EzH) :* NP0)))))))))
               El GoStmtFallthrough
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (H NP0)))))))))
               El (GoStmtBlock x_a2EzI)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (T
                                                 (H
                                                    (NA_I (El x_a2EzI) :* NP0)))))))))))
               El (GoStmtIf x_a2EzJ x_a2EzK x_a2EzL)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (T
                                                 (T
                                                    (H
                                                       (NA_I (El x_a2EzJ)
                                                          :*
                                                            (NA_I (El x_a2EzK)
                                                               :*
                                                                 (NA_I (El x_a2EzL)
                                                                    :* NP0))))))))))))))
               El (GoStmtSelect x_a2EzM)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (T
                                                 (T
                                                    (T
                                                       (H
                                                          (NA_I (El x_a2EzM) :* NP0)))))))))))))
               El (GoStmtSwitch x_a2EzN x_a2EzO)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (T
                                                 (T
                                                    (T
                                                       (T
                                                          (H
                                                             (NA_I (El x_a2EzN)
                                                                :*
                                                                  (NA_I (El x_a2EzO)
                                                                     :* NP0)))))))))))))))
               El (GoStmtTypeSwitch x_a2EzP x_a2EzQ x_a2EzR)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (T
                                                 (T
                                                    (T
                                                       (T
                                                          (T
                                                             (H
                                                                (NA_I (El x_a2EzP)
                                                                   :*
                                                                     (NA_I (El x_a2EzQ)
                                                                        :*
                                                                          (NA_I (El x_a2EzR)
                                                                             :*
                                                                               NP0)))))))))))))))))
               El (GoStmtFor x_a2EzS x_a2EzT)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (T
                                                 (T
                                                    (T
                                                       (T
                                                          (T
                                                             (T
                                                                (H
                                                                   (NA_I (El x_a2EzS)
                                                                      :*
                                                                        (NA_I (El x_a2EzT)
                                                                           :*
                                                                             NP0)))))))))))))))))
               El (GoStmtDefer x_a2EzU)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (T
                                              (T
                                                 (T
                                                    (T
                                                       (T
                                                          (T
                                                             (T
                                                                (T
                                                                   (H
                                                                      (NA_I (El x_a2EzU)
                                                                         :* NP0)))))))))))))))))
        IdxGoSimp
          -> \case
               El GoSimpEmpty -> Rep (H NP0)
               El (GoSimpRecv x_a2EzV)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2EzV) :* NP0)))
               El (GoSimpSend x_a2EzW x_a2EzX)
                 -> Rep
                      (T
                         (T
                            (H
                               (NA_I (El x_a2EzW) :* (NA_I (El x_a2EzX) :* NP0)))))
               El (GoSimpExpr x_a2EzY)
                 -> Rep
                      (T
                         (T
                            (T
                               (H (NA_I (El x_a2EzY) :* NP0)))))
               El (GoSimpInc x_a2EzZ)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (H
                                     (NA_I (El x_a2EzZ) :* NP0))))))
               El (GoSimpDec x_a2EA0)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (H
                                        (NA_I (El x_a2EA0) :* NP0)))))))
               El (GoSimpAsn x_a2EA1 x_a2EA2 x_a2EA3)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (H
                                           (NA_I (El x_a2EA1)
                                              :*
                                                (NA_I (El x_a2EA2)
                                                   :* (NA_I (El x_a2EA3) :* NP0))))))))))
               El (GoSimpVar x_a2EA4 x_a2EA5)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (H
                                              (NA_I (El x_a2EA4)
                                                 :* (NA_I (El x_a2EA5) :* NP0))))))))))
        IdxMaybeGoId
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_a2EA6)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2EA6) :* NP0)))
        IdxGoCond
          -> \case
               El (GoCond x_a2EA7 x_a2EA8)
                 -> Rep
                      (H
                         (NA_I (El x_a2EA7) :* (NA_I (El x_a2EA8) :* NP0)))
        IdxMaybeGoStmt
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_a2EA9)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2EA9) :* NP0)))
        IdxListGoCaseGoChan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2EAa x_a2EAb)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2EAa) :* (NA_I (El x_a2EAb) :* NP0))))
        IdxListGoCaseGoExpr
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2EAc x_a2EAd)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2EAc) :* (NA_I (El x_a2EAd) :* NP0))))
        IdxListGoCaseGoType
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2EAe x_a2EAf)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2EAe) :* (NA_I (El x_a2EAf) :* NP0))))
        IdxGoForClause
          -> \case
               El (GoForWhile x_a2EAg)
                 -> Rep (H (NA_I (El x_a2EAg) :* NP0))
               El (GoForThree x_a2EAh x_a2EAi x_a2EAj)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2EAh)
                               :* (NA_I (El x_a2EAi) :* (NA_I (El x_a2EAj) :* NP0)))))
               El (GoForRange x_a2EAk x_a2EAl)
                 -> Rep
                      (T
                         (T
                            (H
                               (NA_I (El x_a2EAk) :* (NA_I (El x_a2EAl) :* NP0)))))
        IdxMaybeGoSimp
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_a2EAm)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2EAm) :* NP0)))
        IdxMaybeGoExpr
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_a2EAn)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2EAn) :* NP0)))
        IdxGoCaseGoChan
          -> \case
               El (GoCase x_a2EAo x_a2EAp)
                 -> Rep
                      (H
                         (NA_I (El x_a2EAo) :* (NA_I (El x_a2EAp) :* NP0)))
               El (GoDefault x_a2EAq)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2EAq) :* NP0)))
        IdxListGoChan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2EAr x_a2EAs)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2EAr) :* (NA_I (El x_a2EAs) :* NP0))))
        IdxGoChan
          -> \case
               El (GoChanRecv x_a2EAt x_a2EAu)
                 -> Rep
                      (H
                         (NA_I (El x_a2EAt) :* (NA_I (El x_a2EAu) :* NP0)))
               El (GoChanSend x_a2EAv x_a2EAw)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2EAv) :* (NA_I (El x_a2EAw) :* NP0))))
        IdxMaybeTup1GoExprGoOp
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_a2EAx)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2EAx) :* NP0)))
        IdxTup1GoExprGoOp
          -> \case
               El ((,) x_a2EAy x_a2EAz)
                 -> Rep
                      (H
                         (NA_I (El x_a2EAy) :* (NA_I (El x_a2EAz) :* NP0)))
        IdxGoCaseGoExpr
          -> \case
               El (GoCase x_a2EAA x_a2EAB)
                 -> Rep
                      (H
                         (NA_I (El x_a2EAA) :* (NA_I (El x_a2EAB) :* NP0)))
               El (GoDefault x_a2EAC)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2EAC) :* NP0)))
        IdxGoCaseGoType
          -> \case
               El (GoCase x_a2EAD x_a2EAE)
                 -> Rep
                      (H
                         (NA_I (El x_a2EAD) :* (NA_I (El x_a2EAE) :* NP0)))
               El (GoDefault x_a2EAF)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2EAF) :* NP0)))
        IdxListGoType
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_a2EAG x_a2EAH)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_a2EAG) :* (NA_I (El x_a2EAH) :* NP0))))
        IdxGoMethSpec
          -> \case
               El (GoMethSpec x_a2EAI x_a2EAJ)
                 -> Rep
                      (H
                         (NA_I (El x_a2EAI) :* (NA_I (El x_a2EAJ) :* NP0)))
               El (GoInterface x_a2EAK)
                 -> Rep
                      (T
                         (H (NA_I (El x_a2EAK) :* NP0)))
        IdxGoFieldType
          -> \case
               El (GoFieldType x_a2EAL x_a2EAM x_a2EAN)
                 -> Rep
                      (H
                         (NA_K (SString x_a2EAL)
                            :* (NA_I (El x_a2EAM) :* (NA_I (El x_a2EAN) :* NP0))))
               El (GoFieldAnon x_a2EAO x_a2EAP x_a2EAQ)
                 -> Rep
                      (T
                         (H
                            (NA_K (SString x_a2EAO)
                               :* (NA_K (SBool x_a2EAP) :* (NA_I (El x_a2EAQ) :* NP0)))))
        IdxGoTypeSpec
          -> \case
               El (GoTypeSpec x_a2EAR x_a2EAS)
                 -> Rep
                      (H
                         (NA_I (El x_a2EAR) :* (NA_I (El x_a2EAS) :* NP0)))
  sto'
    = \case
        IdxGoSource
          -> \case
               Rep (H (NA_I (El y_a2EAT) :* (NA_I (El y_a2EAU) :* (NA_I (El y_a2EAV) :* NP0))))
                 -> El (((GoSource y_a2EAT) y_a2EAU) y_a2EAV)
        IdxGoId
          -> \case
               Rep (H (NA_K (SString y_a2EAW) :* NP0))
                 -> El (GoId y_a2EAW)
        IdxListGoPrel
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EAX) :* (NA_I (El y_a2EAY) :* NP0))))
                 -> El (((:) y_a2EAX) y_a2EAY)
        IdxListGoDecl
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EAZ) :* (NA_I (El y_a2EB0) :* NP0))))
                 -> El (((:) y_a2EAZ) y_a2EB0)
        IdxGoPrel
          -> \case
               Rep (H (NA_I (El y_a2EB1) :* NP0))
                 -> El (GoImportDecl y_a2EB1)
        IdxListGoImpSpec
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EB2) :* (NA_I (El y_a2EB3) :* NP0))))
                 -> El (((:) y_a2EB2) y_a2EB3)
        IdxGoImpSpec
          -> \case
               Rep (H (NA_I (El y_a2EB4) :* (NA_K (SString y_a2EB5) :* NP0)))
                 -> El ((GoImpSpec y_a2EB4) y_a2EB5)
        IdxGoImpType
          -> \case
               Rep (H NP0) -> El GoImp
               Rep (T (H (NA_I (El y_a2EB6) :* NP0)))
                 -> El (GoImpDot y_a2EB6)
               Rep (T (T (H (NA_I (El y_a2EB7) :* NP0))))
                 -> El (GoImpQual y_a2EB7)
        IdxGoOp
          -> \case
               Rep (H (NA_K (SString y_a2EB8) :* NP0))
                 -> El (GoOp y_a2EB8)
        IdxGoDecl
          -> \case
               Rep (H (NA_I (El y_a2EB9) :* NP0))
                 -> El (GoConst y_a2EB9)
               Rep (T (H (NA_I (El y_a2EBa) :* NP0)))
                 -> El (GoType y_a2EBa)
               Rep (T (T (H (NA_I (El y_a2EBb) :* NP0))))
                 -> El (GoVar y_a2EBb)
               Rep (T (T (T (H (NA_I (El y_a2EBc) :* NP0)))))
                 -> El (GoFunc y_a2EBc)
               Rep (T (T (T (T (H (NA_I (El y_a2EBd) :* NP0))))))
                 -> El (GoMeth y_a2EBd)
        IdxListGoCVSpec
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EBe) :* (NA_I (El y_a2EBf) :* NP0))))
                 -> El (((:) y_a2EBe) y_a2EBf)
        IdxListGoTypeSpec
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EBg) :* (NA_I (El y_a2EBh) :* NP0))))
                 -> El (((:) y_a2EBg) y_a2EBh)
        IdxGoFuncDecl
          -> \case
               Rep (H (NA_I (El y_a2EBi) :* (NA_I (El y_a2EBj) :* (NA_I (El y_a2EBk) :* NP0))))
                 -> El (((GoFuncDecl y_a2EBi) y_a2EBj) y_a2EBk)
        IdxGoMethDecl
          -> \case
               Rep (H (NA_I (El y_a2EBl) :* (NA_I (El y_a2EBm) :* (NA_I (El y_a2EBn) :* (NA_I (El y_a2EBo) :* NP0)))))
                 -> El ((((GoMethDecl y_a2EBl) y_a2EBm) y_a2EBn) y_a2EBo)
        IdxGoCVSpec
          -> \case
               Rep (H (NA_I (El y_a2EBp) :* (NA_I (El y_a2EBq) :* (NA_I (El y_a2EBr) :* NP0))))
                 -> El (((GoCVSpec y_a2EBp) y_a2EBq) y_a2EBr)
        IdxListGoId
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EBs) :* (NA_I (El y_a2EBt) :* NP0))))
                 -> El (((:) y_a2EBs) y_a2EBt)
        IdxMaybeGoType
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_a2EBu) :* NP0)))
                 -> El (Just y_a2EBu)
        IdxListGoExpr
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EBv) :* (NA_I (El y_a2EBw) :* NP0))))
                 -> El (((:) y_a2EBv) y_a2EBw)
        IdxGoType
          -> \case
               Rep (H (NA_I (El y_a2EBx) :* (NA_I (El y_a2EBy) :* NP0)))
                 -> El ((GoTypeName y_a2EBx) y_a2EBy)
               Rep (T (H (NA_I (El y_a2EBz) :* (NA_I (El y_a2EBA) :* NP0))))
                 -> El ((GoArrayType y_a2EBz) y_a2EBA)
               Rep (T (T (H (NA_I (El y_a2EBB) :* (NA_I (El y_a2EBC) :* NP0)))))
                 -> El ((GoChannelType y_a2EBB) y_a2EBC)
               Rep (T (T (T (H (NA_I (El y_a2EBD) :* NP0)))))
                 -> El (GoElipsisType y_a2EBD)
               Rep (T (T (T (T (H (NA_I (El y_a2EBE) :* NP0))))))
                 -> El (GoFunctionType y_a2EBE)
               Rep (T (T (T (T (T (H (NA_I (El y_a2EBF) :* NP0)))))))
                 -> El (GoInterfaceType y_a2EBF)
               Rep (T (T (T (T (T (T (H (NA_I (El y_a2EBG) :* (NA_I (El y_a2EBH) :* NP0)))))))))
                 -> El ((GoMapType y_a2EBG) y_a2EBH)
               Rep (T (T (T (T (T (T (T (H (NA_I (El y_a2EBI) :* NP0)))))))))
                 -> El (GoPointerType y_a2EBI)
               Rep (T (T (T (T (T (T (T (T (H (NA_I (El y_a2EBJ) :* NP0))))))))))
                 -> El (GoSliceType y_a2EBJ)
               Rep (T (T (T (T (T (T (T (T (T (H (NA_I (El y_a2EBK) :* NP0)))))))))))
                 -> El (GoStructType y_a2EBK)
        IdxGoExpr
          -> \case
               Rep (H (NA_I (El y_a2EBL) :* NP0))
                 -> El (GoPrim y_a2EBL)
               Rep (T (H (NA_I (El y_a2EBM) :* (NA_I (El y_a2EBN) :* NP0))))
                 -> El ((Go1Op y_a2EBM) y_a2EBN)
               Rep (T (T (H (NA_I (El y_a2EBO) :* (NA_I (El y_a2EBP) :* (NA_I (El y_a2EBQ) :* NP0))))))
                 -> El (((Go2Op y_a2EBO) y_a2EBP) y_a2EBQ)
        IdxGoChanKind
          -> \case
               Rep (H NP0) -> El GoIChan
               Rep (T (H NP0))
                 -> El GoOChan
               Rep (T (T (H NP0)))
                 -> El GoIOChan
        IdxGoSig
          -> \case
               Rep (H (NA_I (El y_a2EBR) :* (NA_I (El y_a2EBS) :* NP0)))
                 -> El ((GoSig y_a2EBR) y_a2EBS)
        IdxListGoMethSpec
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EBT) :* (NA_I (El y_a2EBU) :* NP0))))
                 -> El (((:) y_a2EBT) y_a2EBU)
        IdxListGoFieldType
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EBV) :* (NA_I (El y_a2EBW) :* NP0))))
                 -> El (((:) y_a2EBV) y_a2EBW)
        IdxGoPrim
          -> \case
               Rep (H (NA_I (El y_a2EBX) :* NP0))
                 -> El (GoLiteral y_a2EBX)
               Rep (T (H (NA_I (El y_a2EBY) :* (NA_I (El y_a2EBZ) :* NP0))))
                 -> El ((GoQual y_a2EBY) y_a2EBZ)
               Rep (T (T (H (NA_I (El y_a2EC0) :* (NA_I (El y_a2EC1) :* NP0)))))
                 -> El ((GoMethod y_a2EC0) y_a2EC1)
               Rep (T (T (T (H (NA_I (El y_a2EC2) :* NP0)))))
                 -> El (GoParen y_a2EC2)
               Rep (T (T (T (T (H (NA_I (El y_a2EC3) :* (NA_I (El y_a2EC4) :* NP0)))))))
                 -> El ((GoCast y_a2EC3) y_a2EC4)
               Rep (T (T (T (T (T (H (NA_I (El y_a2EC5) :* NP0)))))))
                 -> El (GoNew y_a2EC5)
               Rep (T (T (T (T (T (T (H (NA_I (El y_a2EC6) :* (NA_I (El y_a2EC7) :* NP0)))))))))
                 -> El ((GoMake y_a2EC6) y_a2EC7)
               Rep (T (T (T (T (T (T (T (H (NA_I (El y_a2EC8) :* (NA_I (El y_a2EC9) :* NP0))))))))))
                 -> El ((GoSelect y_a2EC8) y_a2EC9)
               Rep (T (T (T (T (T (T (T (T (H (NA_I (El y_a2ECa) :* (NA_I (El y_a2ECb) :* NP0)))))))))))
                 -> El ((GoIndex y_a2ECa) y_a2ECb)
               Rep (T (T (T (T (T (T (T (T (T (H (NA_I (El y_a2ECc) :* (NA_I (El y_a2ECd) :* NP0))))))))))))
                 -> El ((GoSlice y_a2ECc) y_a2ECd)
               Rep (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_a2ECe) :* (NA_I (El y_a2ECf) :* NP0)))))))))))))
                 -> El ((GoTA y_a2ECe) y_a2ECf)
               Rep (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_a2ECg) :* (NA_I (El y_a2ECh) :* (NA_K (SBool y_a2ECi) :* NP0)))))))))))))))
                 -> El (((GoCall y_a2ECg) y_a2ECh) y_a2ECi)
        IdxGoLit
          -> \case
               Rep (H (NA_K (SString y_a2ECj) :* (NA_K (SInteger y_a2ECk) :* NP0)))
                 -> El ((GoLitInt y_a2ECj) y_a2ECk)
               Rep (T (H (NA_K (SString y_a2ECl) :* (NA_K (SFloat y_a2ECm) :* NP0))))
                 -> El ((GoLitReal y_a2ECl) y_a2ECm)
               Rep (T (T (H (NA_K (SString y_a2ECn) :* (NA_K (SFloat y_a2ECo) :* NP0)))))
                 -> El ((GoLitImag y_a2ECn) y_a2ECo)
               Rep (T (T (T (H (NA_K (SString y_a2ECp) :* (NA_K (SChar y_a2ECq) :* NP0))))))
                 -> El ((GoLitChar y_a2ECp) y_a2ECq)
               Rep (T (T (T (T (H (NA_K (SString y_a2ECr) :* (NA_K (SString y_a2ECs) :* NP0)))))))
                 -> El ((GoLitStr y_a2ECr) y_a2ECs)
               Rep (T (T (T (T (T (H (NA_I (El y_a2ECt) :* (NA_I (El y_a2ECu) :* NP0))))))))
                 -> El ((GoLitComp y_a2ECt) y_a2ECu)
               Rep (T (T (T (T (T (T (H (NA_I (El y_a2ECv) :* NP0))))))))
                 -> El (GoLitFunc y_a2ECv)
        IdxGoRec
          -> \case
               Rep (H (NA_K (SBool y_a2ECw) :* (NA_I (El y_a2ECx) :* (NA_I (El y_a2ECy) :* NP0))))
                 -> El (((GoRec y_a2ECw) y_a2ECx) y_a2ECy)
        IdxGoComp
          -> \case
               Rep (H (NA_I (El y_a2ECz) :* NP0))
                 -> El (GoComp y_a2ECz)
        IdxGoFuncExpr
          -> \case
               Rep (H (NA_I (El y_a2ECA) :* (NA_I (El y_a2ECB) :* NP0)))
                 -> El ((GoFuncExpr y_a2ECA) y_a2ECB)
        IdxListGoElement
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2ECC) :* (NA_I (El y_a2ECD) :* NP0))))
                 -> El (((:) y_a2ECC) y_a2ECD)
        IdxGoElement
          -> \case
               Rep (H (NA_I (El y_a2ECE) :* (NA_I (El y_a2ECF) :* NP0)))
                 -> El ((GoElement y_a2ECE) y_a2ECF)
        IdxGoKey
          -> \case
               Rep (H NP0) -> El GoKeyNone
               Rep (T (H (NA_I (El y_a2ECG) :* NP0)))
                 -> El (GoKeyField y_a2ECG)
               Rep (T (T (H (NA_I (El y_a2ECH) :* NP0))))
                 -> El (GoKeyIndex y_a2ECH)
        IdxGoValue
          -> \case
               Rep (H (NA_I (El y_a2ECI) :* NP0))
                 -> El (GoValueExpr y_a2ECI)
               Rep (T (H (NA_I (El y_a2ECJ) :* NP0)))
                 -> El (GoValueComp y_a2ECJ)
        IdxGoBlock
          -> \case
               Rep (H (NA_I (El y_a2ECK) :* NP0))
                 -> El (GoBlock y_a2ECK)
               Rep (T (H NP0))
                 -> El GoNoBlock
        IdxListGoParam
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2ECL) :* (NA_I (El y_a2ECM) :* NP0))))
                 -> El (((:) y_a2ECL) y_a2ECM)
        IdxGoParam
          -> \case
               Rep (H (NA_I (El y_a2ECN) :* (NA_I (El y_a2ECO) :* NP0)))
                 -> El ((GoParam y_a2ECN) y_a2ECO)
        IdxListGoStmt
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2ECP) :* (NA_I (El y_a2ECQ) :* NP0))))
                 -> El (((:) y_a2ECP) y_a2ECQ)
        IdxGoStmt
          -> \case
               Rep (H (NA_I (El y_a2ECR) :* NP0))
                 -> El (GoStmtDecl y_a2ECR)
               Rep (T (H (NA_I (El y_a2ECS) :* (NA_I (El y_a2ECT) :* NP0))))
                 -> El ((GoStmtLabeled y_a2ECS) y_a2ECT)
               Rep (T (T (H (NA_I (El y_a2ECU) :* NP0))))
                 -> El (GoStmtSimple y_a2ECU)
               Rep (T (T (T (H (NA_I (El y_a2ECV) :* NP0)))))
                 -> El (GoStmtGo y_a2ECV)
               Rep (T (T (T (T (H (NA_I (El y_a2ECW) :* NP0))))))
                 -> El (GoStmtReturn y_a2ECW)
               Rep (T (T (T (T (T (H (NA_I (El y_a2ECX) :* NP0)))))))
                 -> El (GoStmtBreak y_a2ECX)
               Rep (T (T (T (T (T (T (H (NA_I (El y_a2ECY) :* NP0))))))))
                 -> El (GoStmtContinue y_a2ECY)
               Rep (T (T (T (T (T (T (T (H (NA_I (El y_a2ECZ) :* NP0)))))))))
                 -> El (GoStmtGoto y_a2ECZ)
               Rep (T (T (T (T (T (T (T (T (H NP0)))))))))
                 -> El GoStmtFallthrough
               Rep (T (T (T (T (T (T (T (T (T (H (NA_I (El y_a2ED0) :* NP0)))))))))))
                 -> El (GoStmtBlock y_a2ED0)
               Rep (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_a2ED1) :* (NA_I (El y_a2ED2) :* (NA_I (El y_a2ED3) :* NP0))))))))))))))
                 -> El (((GoStmtIf y_a2ED1) y_a2ED2) y_a2ED3)
               Rep (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_a2ED4) :* NP0)))))))))))))
                 -> El (GoStmtSelect y_a2ED4)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_a2ED5) :* (NA_I (El y_a2ED6) :* NP0)))))))))))))))
                 -> El ((GoStmtSwitch y_a2ED5) y_a2ED6)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_a2ED7) :* (NA_I (El y_a2ED8) :* (NA_I (El y_a2ED9) :* NP0)))))))))))))))))
                 -> El (((GoStmtTypeSwitch y_a2ED7) y_a2ED8) y_a2ED9)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_a2EDa) :* (NA_I (El y_a2EDb) :* NP0)))))))))))))))))
                 -> El ((GoStmtFor y_a2EDa) y_a2EDb)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_a2EDc) :* NP0)))))))))))))))))
                 -> El (GoStmtDefer y_a2EDc)
        IdxGoSimp
          -> \case
               Rep (H NP0) -> El GoSimpEmpty
               Rep (T (H (NA_I (El y_a2EDd) :* NP0)))
                 -> El (GoSimpRecv y_a2EDd)
               Rep (T (T (H (NA_I (El y_a2EDe) :* (NA_I (El y_a2EDf) :* NP0)))))
                 -> El ((GoSimpSend y_a2EDe) y_a2EDf)
               Rep (T (T (T (H (NA_I (El y_a2EDg) :* NP0)))))
                 -> El (GoSimpExpr y_a2EDg)
               Rep (T (T (T (T (H (NA_I (El y_a2EDh) :* NP0))))))
                 -> El (GoSimpInc y_a2EDh)
               Rep (T (T (T (T (T (H (NA_I (El y_a2EDi) :* NP0)))))))
                 -> El (GoSimpDec y_a2EDi)
               Rep (T (T (T (T (T (T (H (NA_I (El y_a2EDj) :* (NA_I (El y_a2EDk) :* (NA_I (El y_a2EDl) :* NP0))))))))))
                 -> El (((GoSimpAsn y_a2EDj) y_a2EDk) y_a2EDl)
               Rep (T (T (T (T (T (T (T (H (NA_I (El y_a2EDm) :* (NA_I (El y_a2EDn) :* NP0))))))))))
                 -> El ((GoSimpVar y_a2EDm) y_a2EDn)
        IdxMaybeGoId
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_a2EDo) :* NP0)))
                 -> El (Just y_a2EDo)
        IdxGoCond
          -> \case
               Rep (H (NA_I (El y_a2EDp) :* (NA_I (El y_a2EDq) :* NP0)))
                 -> El ((GoCond y_a2EDp) y_a2EDq)
        IdxMaybeGoStmt
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_a2EDr) :* NP0)))
                 -> El (Just y_a2EDr)
        IdxListGoCaseGoChan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EDs) :* (NA_I (El y_a2EDt) :* NP0))))
                 -> El (((:) y_a2EDs) y_a2EDt)
        IdxListGoCaseGoExpr
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EDu) :* (NA_I (El y_a2EDv) :* NP0))))
                 -> El (((:) y_a2EDu) y_a2EDv)
        IdxListGoCaseGoType
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EDw) :* (NA_I (El y_a2EDx) :* NP0))))
                 -> El (((:) y_a2EDw) y_a2EDx)
        IdxGoForClause
          -> \case
               Rep (H (NA_I (El y_a2EDy) :* NP0))
                 -> El (GoForWhile y_a2EDy)
               Rep (T (H (NA_I (El y_a2EDz) :* (NA_I (El y_a2EDA) :* (NA_I (El y_a2EDB) :* NP0)))))
                 -> El (((GoForThree y_a2EDz) y_a2EDA) y_a2EDB)
               Rep (T (T (H (NA_I (El y_a2EDC) :* (NA_I (El y_a2EDD) :* NP0)))))
                 -> El ((GoForRange y_a2EDC) y_a2EDD)
        IdxMaybeGoSimp
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_a2EDE) :* NP0)))
                 -> El (Just y_a2EDE)
        IdxMaybeGoExpr
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_a2EDF) :* NP0)))
                 -> El (Just y_a2EDF)
        IdxGoCaseGoChan
          -> \case
               Rep (H (NA_I (El y_a2EDG) :* (NA_I (El y_a2EDH) :* NP0)))
                 -> El ((GoCase y_a2EDG) y_a2EDH)
               Rep (T (H (NA_I (El y_a2EDI) :* NP0)))
                 -> El (GoDefault y_a2EDI)
        IdxListGoChan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EDJ) :* (NA_I (El y_a2EDK) :* NP0))))
                 -> El (((:) y_a2EDJ) y_a2EDK)
        IdxGoChan
          -> \case
               Rep (H (NA_I (El y_a2EDL) :* (NA_I (El y_a2EDM) :* NP0)))
                 -> El ((GoChanRecv y_a2EDL) y_a2EDM)
               Rep (T (H (NA_I (El y_a2EDN) :* (NA_I (El y_a2EDO) :* NP0))))
                 -> El ((GoChanSend y_a2EDN) y_a2EDO)
        IdxMaybeTup1GoExprGoOp
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_a2EDP) :* NP0)))
                 -> El (Just y_a2EDP)
        IdxTup1GoExprGoOp
          -> \case
               Rep (H (NA_I (El y_a2EDQ) :* (NA_I (El y_a2EDR) :* NP0)))
                 -> El (((,) y_a2EDQ) y_a2EDR)
        IdxGoCaseGoExpr
          -> \case
               Rep (H (NA_I (El y_a2EDS) :* (NA_I (El y_a2EDT) :* NP0)))
                 -> El ((GoCase y_a2EDS) y_a2EDT)
               Rep (T (H (NA_I (El y_a2EDU) :* NP0)))
                 -> El (GoDefault y_a2EDU)
        IdxGoCaseGoType
          -> \case
               Rep (H (NA_I (El y_a2EDV) :* (NA_I (El y_a2EDW) :* NP0)))
                 -> El ((GoCase y_a2EDV) y_a2EDW)
               Rep (T (H (NA_I (El y_a2EDX) :* NP0)))
                 -> El (GoDefault y_a2EDX)
        IdxListGoType
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_a2EDY) :* (NA_I (El y_a2EDZ) :* NP0))))
                 -> El (((:) y_a2EDY) y_a2EDZ)
        IdxGoMethSpec
          -> \case
               Rep (H (NA_I (El y_a2EE0) :* (NA_I (El y_a2EE1) :* NP0)))
                 -> El ((GoMethSpec y_a2EE0) y_a2EE1)
               Rep (T (H (NA_I (El y_a2EE2) :* NP0)))
                 -> El (GoInterface y_a2EE2)
        IdxGoFieldType
          -> \case
               Rep (H (NA_K (SString y_a2EE3) :* (NA_I (El y_a2EE4) :* (NA_I (El y_a2EE5) :* NP0))))
                 -> El (((GoFieldType y_a2EE3) y_a2EE4) y_a2EE5)
               Rep (T (H (NA_K (SString y_a2EE6) :* (NA_K (SBool y_a2EE7) :* (NA_I (El y_a2EE8) :* NP0)))))
                 -> El (((GoFieldAnon y_a2EE6) y_a2EE7) y_a2EE8)
        IdxGoTypeSpec
          -> \case
               Rep (H (NA_I (El y_a2EE9) :* (NA_I (El y_a2EEa) :* NP0)))
                 -> El ((GoTypeSpec y_a2EE9) y_a2EEa)
