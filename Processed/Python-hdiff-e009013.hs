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


-- | Convenient access to annotations in annotated types. 
class Annotated t where
   -- | Given an annotated type, project out its annotation value.
   annot :: t annot -> annot

-- | Identifier.
data Ident annot = Ident { ident_string :: !String, ident_annot :: annot }
   deriving (Eq,Ord,Show)

type IdentSpan = Ident SrcSpan



-- | A module (Python source file). 
--
--    * Version 2.6 <http://docs.python.org/2.6/reference/toplevel_components.html>
-- 
--    * Version 3.1 <http://docs.python.org/3.1/reference/toplevel_components.html> 
-- 
newtype Module annot = Module [Statement annot] -- ^ A module is just a sequence of top-level statements.
   deriving (Eq,Ord,Show)

type ModuleSpan = Module SrcSpan

-- | A block of statements. A suite is a group of statements controlled by a clause, 
-- for example, the body of a loop. 
--
--    * Version 2.6 <http://docs.python.org/2.6/reference/compound_stmts.html>
-- 
--    * Version 3.1 <http://docs.python.org/3.1/reference/compound_stmts.html>
--
type Suite annot = [Statement annot]

type SuiteSpan = Suite SrcSpan

-- | A compound name constructed with the dot operator.
type DottedName annot = [Ident annot]

type DottedNameSpan = DottedName SrcSpan

-- | An entity imported using the \'import\' keyword.
-- 
--    * Version 2.6 <http://docs.python.org/2.6/reference/simple_stmts.html#the-import-statement>
--
--    * Version 3.1 <http://docs.python.org/3.1/reference/simple_stmts.html#the-import-statement> 
--
data ImportItem annot =
   ImportItem
   { import_item_name :: DottedName annot   -- ^ The name of module to import.
   , import_as_name :: Maybe (Ident annot)  -- ^ An optional name to refer to the entity (the \'as\' name). 
   , import_item_annot :: annot
   }
   deriving (Eq,Ord,Show)

type ImportItemSpan = ImportItem SrcSpan



-- | An entity imported using the \'from ... import\' construct.
--
--    * Version 2.6 <http://docs.python.org/2.6/reference/simple_stmts.html#the-import-statement>
-- 
--    * Version 3.1 <http://docs.python.org/3.1/reference/simple_stmts.html#the-import-statement>
--
data FromItem annot =
   FromItem
   { from_item_name :: Ident annot       -- ^ The name of the entity imported. 
   , from_as_name :: Maybe (Ident annot) -- ^ An optional name to refer to the entity (the \'as\' name).
   , from_item_annot :: annot
   }
   deriving (Eq,Ord,Show)

type FromItemSpan = FromItem SrcSpan



-- | Items imported using the \'from ... import\' construct.
data FromItems annot
   = ImportEverything { from_items_annot :: annot } -- ^ Import everything exported from the module.
   | FromItems { from_items_items :: [FromItem annot], from_items_annot :: annot } -- ^ Import a specific list of items from the module.
   deriving (Eq,Ord,Show)

type FromItemsSpan = FromItems SrcSpan



-- | A reference to the module to import from using the \'from ... import\' construct.
data ImportRelative annot
   = ImportRelative
     { import_relative_dots :: Int
     , import_relative_module :: Maybe (DottedName annot)
     , import_relative_annot :: annot
     }
   deriving (Eq,Ord,Show)

type ImportRelativeSpan = ImportRelative SrcSpan



-- | Statements.
--
--    * Simple statements:
--
--       * Version 2.6 <http://docs.python.org/2.6/reference/simple_stmts.html>
-- 
--       * Version 3.1 <http://docs.python.org/3.1/reference/simple_stmts.html>
--
--    * Compound statements:
--
--       * Version 2.6 <http://docs.python.org/2.6/reference/compound_stmts.html>
--
--       * Version 3.1 <http://docs.python.org/3.1/reference/compound_stmts.html>
--
data Statement annot
   -- | Import statement.
   = Import
     { import_items :: [ImportItem annot] -- ^ Items to import.
     , stmt_annot :: annot
     }
   -- | From ... import statement.
   | FromImport
     { from_module :: ImportRelative annot -- ^ Module to import from.
     , from_items :: FromItems annot -- ^ Items to import.
     , stmt_annot :: annot
     }
   -- | While loop. 
   | While
     { while_cond :: Expr annot -- ^ Loop condition.
     , while_body :: Suite annot -- ^ Loop body.
     , while_else :: Suite annot -- ^ Else clause.
     , stmt_annot :: annot
     }
   -- | For loop. 
   | For
     { for_targets :: [Expr annot] -- ^ Loop variables.
     , for_generator :: Expr annot -- ^ Loop generator. 
     , for_body :: Suite annot -- ^ Loop body
     , for_else :: Suite annot -- ^ Else clause.
     , stmt_annot :: annot
     }
   | AsyncFor
     { for_stmt :: Statement annot -- ^ For statement
     , stmt_annot :: annot
     }
   -- | Function definition. 
   | Fun
     { fun_name :: Ident annot -- ^ Function name.
     , fun_args :: [Parameter annot] -- ^ Function parameter list.
     , fun_result_annotation :: Maybe (Expr annot) -- ^ Optional result annotation.
     , fun_body :: Suite annot -- ^ Function body.
     , stmt_annot :: annot
     }
   | AsyncFun
     { fun_def :: Statement annot -- ^ Function definition (Fun)
     , stmt_annot :: annot
     }
   -- | Class definition. 
   | Class
     { class_name :: Ident annot -- ^ Class name.
     , class_args :: [Argument annot] -- ^ Class argument list. In version 2.x this is only ArgExprs. 
     , class_body :: Suite annot -- ^ Class body.
     , stmt_annot :: annot
     }
   -- | Conditional statement (if-elif-else). 
   | Conditional
     { cond_guards :: [(Expr annot, Suite annot)] -- ^ Sequence of if-elif conditional clauses.
     , cond_else :: Suite annot -- ^ Possibly empty unconditional else clause.
     , stmt_annot :: annot
     }
   -- | Assignment statement. 
   | Assign
     { assign_to :: [Expr annot] -- ^ Entity to assign to. 
     , assign_expr :: Expr annot -- ^ Expression to evaluate.
     , stmt_annot :: annot
     }
   -- | Augmented assignment statement. 
   | AugmentedAssign
     { aug_assign_to :: Expr annot -- ^ Entity to assign to.
     , aug_assign_op :: AssignOp annot -- ^ Assignment operator (for example \'+=\').
     , aug_assign_expr :: Expr annot  -- ^ Expression to evaluate.
     , stmt_annot :: annot
     }
   | AnnotatedAssign
    { ann_assign_annotation :: Expr annot
    , ann_assign_to :: Expr annot
    , ann_assign_expr :: Maybe (Expr annot)
    , stmt_annot :: annot
    }
   -- | Decorated definition of a function or class.
   | Decorated
     { decorated_decorators :: [Decorator annot] -- ^ Decorators.
     , decorated_def :: Statement annot -- ^ Function or class definition to be decorated.
     , stmt_annot :: annot
     }
   -- | Return statement (may only occur syntactically nested in a function definition). 
   | Return
     { return_expr :: Maybe (Expr annot) -- ^ Optional expression to evaluate and return to caller.
     , stmt_annot :: annot
     }
   -- | Try statement (exception handling). 
   | Try
     { try_body :: Suite annot -- ^ Try clause.
     , try_excepts :: [Handler annot] -- ^ Exception handlers.
     , try_else :: Suite annot -- ^ Possibly empty else clause, executed if and when control flows off the end of the try clause.
     , try_finally :: Suite annot -- ^ Possibly empty finally clause.
     , stmt_annot :: annot
     }
   -- | Raise statement (exception throwing). 
   | Raise
     { raise_expr :: RaiseExpr annot
     , stmt_annot :: annot
     }
   -- | With statement (context management). 
   | With
     { with_context :: [(Expr annot, Maybe (Expr annot))] -- ^ Context expression(s) (yields a context manager).
     , with_body :: Suite annot -- ^ Suite to be managed.
     , stmt_annot :: annot
     }
   | AsyncWith
      { with_stmt :: Statement annot -- ^ With statement
      , stmt_annot :: annot
      }
   -- | Pass statement (null operation). 
   | Pass { stmt_annot :: annot }
   -- | Break statement (may only occur syntactically nested in a for or while loop, but not nested in a function or class definition within that loop). 
   | Break { stmt_annot :: annot }
   -- | Continue statement (may only occur syntactically nested in a for or while loop, but not nested in a function or class definition or finally clause within that loop). 
   | Continue { stmt_annot :: annot }
   -- | Del statement (delete). 
   | Delete
     { del_exprs :: [Expr annot] -- ^ Items to delete.
     , stmt_annot :: annot
     }
   -- | Expression statement. 
   | StmtExpr { stmt_expr :: Expr annot, stmt_annot :: annot }
   -- | Global declaration. 
   | Global
     { global_vars :: [Ident annot] -- ^ Variables declared global in the current block.
     , stmt_annot :: annot
     }
   -- | Nonlocal declaration. /Version 3.x only/. 
   | NonLocal
     { nonLocal_vars :: [Ident annot] -- ^ Variables declared nonlocal in the current block (their binding comes from bound the nearest enclosing scope).
     , stmt_annot :: annot
     }
   -- | Assertion. 
   | Assert
     { assert_exprs :: [Expr annot] -- ^ Expressions being asserted.
     , stmt_annot :: annot
     }
   -- | Print statement. /Version 2 only/. 
   | Print
     { print_chevron :: Bool -- ^ Optional chevron (>>)
     , print_exprs :: [Expr annot] -- ^ Arguments to print
     , print_trailing_comma :: Bool -- ^ Does it end in a comma?
     , stmt_annot :: annot
     }
   -- | Exec statement. /Version 2 only/. 
   | Exec
     { exec_expr :: Expr annot -- ^ Expression to exec.
     , exec_globals_locals :: Maybe (Expr annot, Maybe (Expr annot)) -- ^ Global and local environments to evaluate the expression within.
     , stmt_annot :: annot
     }
   deriving (Eq,Ord,Show)

type StatementSpan = Statement SrcSpan



-- | The argument for a @raise@ statement.
data RaiseExpr annot
   = RaiseV3 (Maybe (Expr annot, Maybe (Expr annot))) -- ^ Optional expression to evaluate, and optional \'from\' clause. /Version 3 only/.
   | RaiseV2 (Maybe (Expr annot, (Maybe (Expr annot, Maybe (Expr annot))))) -- ^ /Version 2 only/.
   deriving (Eq,Ord,Show)

type RaiseExprSpan = RaiseExpr SrcSpan

-- | Decorator.
data Decorator annot =
   Decorator
   { decorator_name :: DottedName annot -- ^ Decorator name.
   , decorator_args :: [Argument annot] -- ^ Decorator arguments.
   , decorator_annot :: annot
   }
   deriving (Eq,Ord,Show)

type DecoratorSpan = Decorator SrcSpan



-- | Formal parameter of function definitions and lambda expressions.
-- 
-- * Version 2.6: 
--
-- * <http://docs.python.org/2.6/reference/compound_stmts.html#function-definitions>
--
-- * <http://docs.python.org/2.6/reference/expressions.html#calls>
--
-- * Version 3.1: 
--
-- * <http://docs.python.org/3.1/reference/compound_stmts.html#function-definitions>
--
-- * <http://docs.python.org/3.1/reference/expressions.html#calls>
--
data Parameter annot
   -- | Ordinary named parameter.
   = Param
     { param_name :: Ident annot -- ^ Parameter name.
     , param_py_annotation :: Maybe (Expr annot) -- ^ Optional annotation.
     , param_default :: Maybe (Expr annot) -- ^ Optional default value.
     , param_annot :: annot
     }
   -- | Excess positional parameter (single asterisk before its name in the concrete syntax). 
   | VarArgsPos
     { param_name :: Ident annot -- ^ Parameter name.
     , param_py_annotation :: Maybe (Expr annot) -- ^ Optional annotation.
     , param_annot :: annot
     }
   -- | Excess keyword parameter (double asterisk before its name in the concrete syntax).
   | VarArgsKeyword
     { param_name :: Ident annot -- ^ Parameter name.
     , param_py_annotation :: Maybe (Expr annot) -- ^ Optional annotation.
     , param_annot :: annot
     }
   -- | Marker for the end of positional parameters (not a parameter itself).
   | EndPositional { param_annot :: annot }
   -- | Tuple unpack. /Version 2 only/.
   | UnPackTuple
     { param_unpack_tuple :: ParamTuple annot -- ^ The tuple to unpack.
     , param_default :: Maybe (Expr annot) -- ^ Optional default value.
     , param_annot :: annot
     }
   deriving (Eq,Ord,Show)

type ParameterSpan = Parameter SrcSpan



-- | Tuple unpack parameter. /Version 2 only/.
data ParamTuple annot
   = ParamTupleName { param_tuple_name :: Ident annot, param_tuple_annot :: annot } -- ^ A variable name.
   | ParamTuple { param_tuple :: [ParamTuple annot], param_tuple_annot :: annot } -- ^ A (possibly nested) tuple parameter.
   deriving (Eq,Ord,Show)

type ParamTupleSpan = ParamTuple SrcSpan



-- | Arguments to function calls, class declarations and decorators.
data Argument annot
   -- | Ordinary argument expression.
   = ArgExpr { arg_expr :: Expr annot, arg_annot :: annot }
   -- | Excess positional argument.
   | ArgVarArgsPos { arg_expr :: Expr annot, arg_annot :: annot }
   -- | Excess keyword argument.
   | ArgVarArgsKeyword { arg_expr :: Expr annot, arg_annot :: annot }
   -- | Keyword argument.
   | ArgKeyword
     { arg_keyword :: Ident annot -- ^ Keyword name.
     , arg_expr :: Expr annot -- ^ Argument expression.
     , arg_annot :: annot
     }
   deriving (Eq,Ord,Show)

type ArgumentSpan = Argument SrcSpan



-- | Exception handler. 
data Handler annot
   = Handler
     { handler_clause :: ExceptClause annot
     , handler_suite :: Suite annot
     , handler_annot :: annot
     }
   deriving (Eq,Ord,Show)

type HandlerSpan = Handler SrcSpan



-- | Exception clause. 
data ExceptClause annot
   = ExceptClause
     -- NB: difference with version 3 (has NAME as target, but looks like bug in grammar)
     { except_clause :: Maybe (Expr annot, Maybe (Expr annot))
     , except_clause_annot :: annot
     }
   deriving (Eq,Ord,Show)

type ExceptClauseSpan = ExceptClause SrcSpan



-- | Comprehension. In version 3.x this can be used for lists, sets, dictionaries and generators. 
-- data Comprehension e annot
data Comprehension annot
   = Comprehension
     { comprehension_expr :: ComprehensionExpr annot
     , comprehension_for :: CompFor annot
     , comprehension_annot :: annot
     }
   deriving (Eq,Ord,Show)

type ComprehensionSpan = Comprehension SrcSpan



data ComprehensionExpr annot
   = ComprehensionExpr (Expr annot)
   | ComprehensionDict (DictKeyDatumList annot)
   deriving (Eq,Ord,Show)

type ComprehensionExprSpan = ComprehensionExpr SrcSpan


-- | Comprehension \'for\' component. 
data CompFor annot =
   CompFor
   { comp_for_async :: Bool
   , comp_for_exprs :: [Expr annot]
   , comp_in_expr :: Expr annot
   , comp_for_iter :: Maybe (CompIter annot)
   , comp_for_annot :: annot
   }
   deriving (Eq,Ord,Show)

type CompForSpan = CompFor SrcSpan



-- | Comprehension guard. 
data CompIf annot =
   CompIf
   { comp_if :: Expr annot
   , comp_if_iter :: Maybe (CompIter annot)
   , comp_if_annot :: annot
   }
   deriving (Eq,Ord,Show)

type CompIfSpan = CompIf SrcSpan



-- | Comprehension iterator (either a \'for\' or an \'if\'). 
data CompIter annot
   = IterFor { comp_iter_for :: CompFor annot, comp_iter_annot :: annot }
   | IterIf { comp_iter_if :: CompIf annot, comp_iter_annot :: annot }
   deriving (Eq,Ord,Show)

type CompIterSpan = CompIter SrcSpan



-- | Expressions.
-- 
-- * Version 2.6 <http://docs.python.org/2.6/reference/expressions.html>.
-- 
-- * Version 3.1 <http://docs.python.org/3.1/reference/expressions.html>.
-- 
data Expr annot
   -- | Variable.
   = Var { var_ident :: Ident annot, expr_annot :: annot }
   -- | Literal integer.
   | Int { int_value :: Integer, expr_literal :: String, expr_annot :: annot }
   -- | Long literal integer. /Version 2 only/.
   | LongInt { int_value :: Integer, expr_literal :: String, expr_annot :: annot }
   -- | Literal floating point number.
   | Float { float_value :: Double, expr_literal :: String, expr_annot :: annot }
   -- | Literal imaginary number.
   | Imaginary { imaginary_value :: Double, expr_literal :: String, expr_annot :: annot }
   -- | Literal boolean.
   | Bool { bool_value :: Bool, expr_annot :: annot }
   -- | Literal \'None\' value.
   | None { expr_annot :: annot }
   -- | Ellipsis \'...\'.
   | Ellipsis { expr_annot :: annot }
   -- | Literal byte string.
   | ByteStrings { byte_string_strings :: [String], expr_annot :: annot }
   -- | Literal strings (to be concatentated together).
   | Strings { strings_strings :: [String], expr_annot :: annot }
   -- | Unicode literal strings (to be concatentated together). Version 2 only.
   | UnicodeStrings { unicodestrings_strings :: [String], expr_annot :: annot }
   -- | Function call. 
   | Call
     { call_fun :: Expr annot -- ^ Expression yielding a callable object (such as a function).
     , call_args :: [Argument annot] -- ^ Call arguments.
     , expr_annot :: annot
     }
   -- | Subscription, for example \'x [y]\'. 
   | Subscript { subscriptee :: Expr annot, subscript_expr :: Expr annot, expr_annot :: annot }
   -- | Slicing, for example \'w [x:y:z]\'. 
   | SlicedExpr { slicee :: Expr annot, slices :: [Slice annot], expr_annot :: annot }
   -- | Conditional expresison. 
   | CondExpr
     { ce_true_branch :: Expr annot -- ^ Expression to evaluate if condition is True.
     , ce_condition :: Expr annot -- ^ Boolean condition.
     , ce_false_branch :: Expr annot -- ^ Expression to evaluate if condition is False.
     , expr_annot :: annot
     }
   -- | Binary operator application.
   | BinaryOp { operator :: Op annot, left_op_arg :: Expr annot, right_op_arg :: Expr annot, expr_annot :: annot }
   -- | Unary operator application.
   | UnaryOp { operator :: Op annot, op_arg :: Expr annot, expr_annot :: annot }
   -- Dot operator (attribute selection)
   | Dot { dot_expr :: Expr annot, dot_attribute :: Ident annot, expr_annot :: annot }
   -- | Anonymous function definition (lambda). 
   | Lambda { lambda_args :: [Parameter annot], lambda_body :: Expr annot, expr_annot :: annot }
   -- | Tuple. Can be empty. 
   | Tuple { tuple_exprs :: [Expr annot], expr_annot :: annot }
   -- | Generator yield. 
   | Yield
     -- { yield_expr :: Maybe (Expr annot) -- ^ Optional expression to yield.
     { yield_arg :: Maybe (YieldArg annot) -- ^ Optional Yield argument.
     , expr_annot :: annot
     }
   -- | Generator. 
   | Generator { gen_comprehension :: Comprehension annot, expr_annot :: annot }
   -- | Await
   | Await { await_expr :: Expr annot, expr_annot :: annot }
   -- | List comprehension. 
   | ListComp { list_comprehension :: Comprehension annot, expr_annot :: annot }
   -- | List. 
   | List { list_exprs :: [Expr annot], expr_annot :: annot }
   -- | Dictionary. 
   | Dictionary { dict_mappings :: [DictKeyDatumList annot], expr_annot :: annot }
   -- | Dictionary comprehension. /Version 3 only/. 
   | DictComp { dict_comprehension :: Comprehension annot, expr_annot :: annot }
   -- | Set. 
   | Set { set_exprs :: [Expr annot], expr_annot :: annot }
   -- | Set comprehension. /Version 3 only/. 
   | SetComp { set_comprehension :: Comprehension annot, expr_annot :: annot }
   -- | Starred expression. /Version 3 only/.
   | Starred { starred_expr :: Expr annot, expr_annot :: annot }
   -- | Parenthesised expression.
   | Paren { paren_expr :: Expr annot, expr_annot :: annot }
   -- | String conversion (backquoted expression). Version 2 only. 
   | StringConversion { backquoted_expr :: Expr annot, expr_anot :: annot }
   deriving (Eq,Ord,Show)

type ExprSpan = Expr SrcSpan


data YieldArg annot
   = YieldFrom (Expr annot) annot -- ^ Yield from a generator (Version 3 only)
   | YieldExpr (Expr annot) -- ^ Yield value of an expression
   deriving (Eq,Ord,Show)

type YieldArgSpan = YieldArg SrcSpan

data SrcLocation =
   Sloc { sloc_filename :: !String
        , sloc_row :: {-# UNPACK #-} !Int
        , sloc_column :: {-# UNPACK #-} !Int
        }
   | NoLocation
   deriving (Eq,Ord,Show)

data SrcSpan
    -- | A span which starts and ends on the same line.
  = SpanCoLinear
    { span_filename     :: !String
    , span_row          :: {-# UNPACK #-} !Int
    , span_start_column :: {-# UNPACK #-} !Int
    , span_end_column   :: {-# UNPACK #-} !Int
    }
    -- | A span which starts and ends on different lines.
  | SpanMultiLine
    { span_filename     :: !String
    , span_start_row    :: {-# UNPACK #-} !Int
    , span_start_column :: {-# UNPACK #-} !Int
    , span_end_row      :: {-# UNPACK #-} !Int
    , span_end_column   :: {-# UNPACK #-} !Int
    }
    -- | A span which is actually just one point in the file.
  | SpanPoint
    { span_filename :: !String
    , span_row      :: {-# UNPACK #-} !Int
    , span_column   :: {-# UNPACK #-} !Int
    }
    -- | No span information.
  | SpanEmpty
   deriving (Eq,Ord,Show)   

data DictKeyDatumList annot =
   DictMappingPair (Expr annot) (Expr annot)
   | DictUnpacking (Expr annot)
   deriving (Eq,Ord,Show)

type DictKeyDatumListSpan = DictKeyDatumList SrcSpan


-- | Slice compenent.
data Slice annot
   = SliceProper
     { slice_lower :: Maybe (Expr annot)
     , slice_upper :: Maybe (Expr annot)
     , slice_stride :: Maybe (Maybe (Expr annot))
     , slice_annot :: annot
     }
   | SliceExpr
     { slice_expr :: Expr annot
     , slice_annot :: annot
     }
   | SliceEllipsis { slice_annot :: annot }
   deriving (Eq,Ord,Show)

type SliceSpan = Slice SrcSpan



-- | Operators.
data Op annot
   = And { op_annot :: annot } -- ^ \'and\'
   | Or { op_annot :: annot } -- ^ \'or\'
   | Not { op_annot :: annot } -- ^ \'not\'
   | Exponent { op_annot :: annot } -- ^ \'**\'
   | LessThan { op_annot :: annot } -- ^ \'<\'
   | GreaterThan { op_annot :: annot } -- ^ \'>\'
   | Equality { op_annot :: annot } -- ^ \'==\'
   | GreaterThanEquals { op_annot :: annot } -- ^ \'>=\'
   | LessThanEquals { op_annot :: annot } -- ^ \'<=\'
   | NotEquals  { op_annot :: annot } -- ^ \'!=\'
   | NotEqualsV2  { op_annot :: annot } -- ^ \'<>\'. Version 2 only.
   | In { op_annot :: annot } -- ^ \'in\'
   | Is { op_annot :: annot } -- ^ \'is\'
   | IsNot { op_annot :: annot } -- ^ \'is not\'
   | NotIn { op_annot :: annot } -- ^ \'not in\'
   | BinaryOr { op_annot :: annot } -- ^ \'|\'
   | Xor { op_annot :: annot } -- ^ \'^\'
   | BinaryAnd { op_annot :: annot } -- ^ \'&\'
   | ShiftLeft { op_annot :: annot } -- ^ \'<<\'
   | ShiftRight { op_annot :: annot } -- ^ \'>>\'
   | Multiply { op_annot :: annot } -- ^ \'*\'
   | Plus { op_annot :: annot } -- ^ \'+\'
   | Minus { op_annot :: annot } -- ^ \'-\'
   | Divide { op_annot :: annot } -- ^ \'\/\'
   | FloorDivide { op_annot :: annot } -- ^ \'\/\/\'
   | MatrixMult { op_annot :: annot } -- ^ \'@\'
   | Invert { op_annot :: annot } -- ^ \'~\' (bitwise inversion of its integer argument)
   | Modulo { op_annot :: annot } -- ^ \'%\'
   deriving (Eq,Ord,Show)

type OpSpan = Op SrcSpan



-- | Augmented assignment operators.
data AssignOp annot
   = PlusAssign { assignOp_annot :: annot } -- ^ \'+=\'
   | MinusAssign { assignOp_annot :: annot } -- ^ \'-=\'
   | MultAssign { assignOp_annot :: annot } -- ^ \'*=\'
   | DivAssign { assignOp_annot :: annot } -- ^ \'\/=\'
   | ModAssign { assignOp_annot :: annot } -- ^ \'%=\'
   | PowAssign { assignOp_annot :: annot } -- ^ \'*=\'
   | BinAndAssign { assignOp_annot :: annot } -- ^ \'&=\'
   | BinOrAssign { assignOp_annot :: annot } -- ^ \'|=\'
   | BinXorAssign { assignOp_annot :: annot } -- ^ \'^=\' 
   | LeftShiftAssign { assignOp_annot :: annot } -- ^ \'<<=\'
   | RightShiftAssign { assignOp_annot :: annot } -- ^ \'>>=\'
   | FloorDivAssign { assignOp_annot :: annot } -- ^ \'\/\/=\'
   | MatrixMultAssign { assignOp_annot :: annot } -- ^ \'@=\'
   deriving (Eq,Ord,Show)

type AssignOpSpan = AssignOp SrcSpan


type FamModuleSrcSpan =
    '[Module SrcSpan,
      [Statement SrcSpan],
      Statement SrcSpan,
      [ImportItem SrcSpan],
      SrcSpan,
      ImportRelative SrcSpan,
      FromItems SrcSpan,
      Expr SrcSpan,
      Suite SrcSpan,
      [Expr SrcSpan],
      Ident SrcSpan,
      [Parameter SrcSpan],
      Maybe (Expr SrcSpan),
      [Argument SrcSpan],
      [(Expr SrcSpan, Suite SrcSpan)],
      AssignOp SrcSpan,
      [Decorator SrcSpan],
      [Handler SrcSpan],
      RaiseExpr SrcSpan,
      [(Expr SrcSpan, Maybe (Expr SrcSpan))],
      [Ident SrcSpan],
      Maybe (Expr SrcSpan, Maybe (Expr SrcSpan)),
      ImportItem SrcSpan,
      DottedName SrcSpan,
      Maybe (Ident SrcSpan),
      Maybe (DottedName SrcSpan),
      [FromItem SrcSpan],
      FromItem SrcSpan,
      [String],
      [Slice SrcSpan],
      Op SrcSpan,
      Maybe (YieldArg SrcSpan),
      Comprehension SrcSpan,
      [DictKeyDatumList SrcSpan],
      Argument SrcSpan,
      Slice SrcSpan,
      Maybe (Maybe (Expr SrcSpan)),
      Parameter SrcSpan,
      ParamTuple SrcSpan,
      [ParamTuple SrcSpan],
      YieldArg SrcSpan,
      ComprehensionExpr SrcSpan,
      CompFor SrcSpan,
      DictKeyDatumList SrcSpan,
      Maybe (CompIter SrcSpan),
      CompIter SrcSpan,
      CompIf SrcSpan,
      (Expr SrcSpan, Suite SrcSpan),
      Decorator SrcSpan,
      Handler SrcSpan,
      ExceptClause SrcSpan,
      (Expr SrcSpan, Maybe (Expr SrcSpan)),
      Maybe (Expr SrcSpan, Maybe (Expr SrcSpan, Maybe (Expr SrcSpan))),
      (Expr SrcSpan, Maybe (Expr SrcSpan, Maybe (Expr SrcSpan)))]
type CodesModuleSrcSpan =
    '[ '[ '[ 'I ( 'S  'Z)]],
      '[ '[], '[ 'I ( 'S ( 'S  'Z)),  'I ( 'S  'Z)]],
      '[ '[ 'I ( 'S ( 'S ( 'S  'Z))),  'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S  'Z)),  'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S  'Z)),  'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))),
           'I ( 'S ( 'S  'Z)),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S  'Z)),  'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'K  'KBool,
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))),
           'K  'KBool,
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S  'Z)))]],
      '[ '[ 'K  'KString,  'K  'KInt,  'K  'KInt,  'K  'KInt],
        '[ 'K  'KString,  'K  'KInt,  'K  'KInt,  'K  'KInt,  'K  'KInt],
        '[ 'K  'KString,  'K  'KInt,  'K  'KInt],
        '[]],
      '[ '[ 'K  'KInt,
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'K  'KInteger,  'K  'KString,  'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'K  'KInteger,  'K  'KString,  'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'K  'KDouble,  'K  'KString,  'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'K  'KDouble,  'K  'KString,  'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'K  'KBool,  'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S  'Z)),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))]],
      '[ '[ 'K  'KString,  'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))]],
      '[ '[], '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[],
        '[ 'K  'KString,
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[ 'K  'KBool,
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))),
           'I ( 'S ( 'S ( 'S ( 'S  'Z))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))]],
      '[ '[],
        '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))]],
      '[ '[ 'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))),
           'I ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))]]]
pattern IdxModuleSrcSpan = SZ
pattern IdxListStatementSrcSpan = SS SZ
pattern IdxStatementSrcSpan = SS (SS SZ)
pattern IdxListImportItemSrcSpan = SS (SS (SS SZ))
pattern IdxSrcSpan = SS (SS (SS (SS SZ)))
pattern IdxImportRelativeSrcSpan = SS (SS (SS (SS (SS SZ))))
pattern IdxFromItemsSrcSpan = SS (SS (SS (SS (SS (SS SZ)))))
pattern IdxExprSrcSpan = SS (SS (SS (SS (SS (SS (SS SZ))))))
pattern IdxSuiteSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))
pattern IdxListExprSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))
pattern IdxIdentSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))
pattern IdxListParameterSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))
pattern IdxMaybeExprSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))
pattern IdxListArgumentSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))
pattern IdxListTup1ExprSrcSpanSuiteSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))
pattern IdxAssignOpSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))
pattern IdxListDecoratorSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))
pattern IdxListHandlerSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))
pattern IdxRaiseExprSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))
pattern IdxListTup1ExprSrcSpanMaybeExprSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))
pattern IdxListIdentSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))
pattern IdxMaybeTup1ExprSrcSpanMaybeExprSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))
pattern IdxImportItemSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))
pattern IdxDottedNameSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))
pattern IdxMaybeIdentSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))
pattern IdxMaybeDottedNameSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))
pattern IdxListFromItemSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))
pattern IdxFromItemSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))
pattern IdxListString = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))
pattern IdxListSliceSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))
pattern IdxOpSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))
pattern IdxMaybeYieldArgSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))
pattern IdxComprehensionSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))
pattern IdxListDictKeyDatumListSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))
pattern IdxArgumentSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))
pattern IdxSliceSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))
pattern IdxMaybeMaybeExprSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))
pattern IdxParameterSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))
pattern IdxParamTupleSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))
pattern IdxListParamTupleSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))
pattern IdxYieldArgSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))
pattern IdxComprehensionExprSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))
pattern IdxCompForSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))
pattern IdxDictKeyDatumListSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))
pattern IdxMaybeCompIterSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))
pattern IdxCompIterSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))
pattern IdxCompIfSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))
pattern IdxTup1ExprSrcSpanSuiteSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxDecoratorSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxHandlerSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxExceptClauseSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxTup1ExprSrcSpanMaybeExprSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxMaybeTup1ExprSrcSpanMaybeTup1ExprSrcSpanMaybeExprSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ)))))))))))))))))))))))))))))))))))))))))))))))))))
pattern IdxTup1ExprSrcSpanMaybeTup1ExprSrcSpanMaybeExprSrcSpan = SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS (SS SZ))))))))))))))))))))))))))))))))))))))))))))))))))))
pattern ModuleSrcSpanModule_ ::
          phi_ajgp ( 'S  'Z)
          -> View kon_ajgq phi_ajgp (Lkup  'Z CodesModuleSrcSpan)
pattern ModuleSrcSpanModule_ p_ajgo = Tag CZ (NA_I p_ajgo :* NP0)
pattern ListStatementSrcSpan_Ifx0 ::
          View kon_ajgs phi_ajgr (Lkup ( 'S  'Z) CodesModuleSrcSpan)
pattern ListStatementSrcSpan_Ifx0 = Tag CZ NP0
pattern ListStatementSrcSpan_Ifx1 ::
          phi_ajgv ( 'S ( 'S  'Z))
          -> phi_ajgv ( 'S  'Z)
             -> View kon_ajgw phi_ajgv (Lkup ( 'S  'Z) CodesModuleSrcSpan)
pattern ListStatementSrcSpan_Ifx1 p_ajgt p_ajgu = Tag (CS CZ)
                                                      (NA_I p_ajgt :* (NA_I p_ajgu :* NP0))
pattern StatementSrcSpanImport_ ::
          phi_ajgz ( 'S ( 'S ( 'S  'Z)))
          -> phi_ajgz ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajgA phi_ajgz (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanImport_ p_ajgx p_ajgy = Tag CZ
                                                    (NA_I p_ajgx :* (NA_I p_ajgy :* NP0))
pattern StatementSrcSpanFromImport_ ::
          phi_ajgE ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))
          -> phi_ajgE ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))
             -> phi_ajgE ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajgF phi_ajgE (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanFromImport_ p_ajgB p_ajgC p_ajgD = Tag (CS CZ)
                                                               (NA_I p_ajgB :* (NA_I p_ajgC :* (NA_I p_ajgD :* NP0)))
pattern StatementSrcSpanWhile_ ::
          phi_ajgK ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajgK ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
             -> phi_ajgK ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
                -> phi_ajgK ( 'S ( 'S ( 'S ( 'S  'Z))))
                   -> View kon_ajgL phi_ajgK (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanWhile_ p_ajgG p_ajgH p_ajgI p_ajgJ = Tag (CS (CS CZ))
                                                                 (NA_I p_ajgG :* (NA_I p_ajgH :* (NA_I p_ajgI :* (NA_I p_ajgJ :* NP0))))
pattern StatementSrcSpanFor_ ::
          phi_ajgR ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))
          -> phi_ajgR ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
             -> phi_ajgR ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
                -> phi_ajgR ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
                   -> phi_ajgR ( 'S ( 'S ( 'S ( 'S  'Z))))
                      -> View kon_ajgS phi_ajgR (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanFor_ p_ajgM p_ajgN p_ajgO p_ajgP p_ajgQ = Tag (CS (CS (CS CZ)))
                                                                      (NA_I p_ajgM :* (NA_I p_ajgN :* (NA_I p_ajgO :* (NA_I p_ajgP :* (NA_I p_ajgQ :* NP0)))))
pattern StatementSrcSpanAsyncFor_ ::
          phi_ajgV ( 'S ( 'S  'Z))
          -> phi_ajgV ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajgW phi_ajgV (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanAsyncFor_ p_ajgT p_ajgU = Tag (CS (CS (CS (CS CZ))))
                                                      (NA_I p_ajgT :* (NA_I p_ajgU :* NP0))
pattern StatementSrcSpanFun_ ::
          phi_ajh2 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> phi_ajh2 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))
             -> phi_ajh2 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))
                -> phi_ajh2 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
                   -> phi_ajh2 ( 'S ( 'S ( 'S ( 'S  'Z))))
                      -> View kon_ajh3 phi_ajh2 (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanFun_ p_ajgX p_ajgY p_ajgZ p_ajh0 p_ajh1 = Tag (CS (CS (CS (CS (CS CZ)))))
                                                                      (NA_I p_ajgX :* (NA_I p_ajgY :* (NA_I p_ajgZ :* (NA_I p_ajh0 :* (NA_I p_ajh1 :* NP0)))))
pattern StatementSrcSpanAsyncFun_ ::
          phi_ajh6 ( 'S ( 'S  'Z))
          -> phi_ajh6 ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajh7 phi_ajh6 (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanAsyncFun_ p_ajh4 p_ajh5 = Tag (CS (CS (CS (CS (CS (CS CZ))))))
                                                      (NA_I p_ajh4 :* (NA_I p_ajh5 :* NP0))
pattern StatementSrcSpanClass_ ::
          phi_ajhc ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> phi_ajhc ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))
             -> phi_ajhc ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
                -> phi_ajhc ( 'S ( 'S ( 'S ( 'S  'Z))))
                   -> View kon_ajhd phi_ajhc (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanClass_ p_ajh8 p_ajh9 p_ajha p_ajhb = Tag (CS (CS (CS (CS (CS (CS (CS CZ)))))))
                                                                 (NA_I p_ajh8 :* (NA_I p_ajh9 :* (NA_I p_ajha :* (NA_I p_ajhb :* NP0))))
pattern StatementSrcSpanConditional_ ::
          phi_ajhh ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))
          -> phi_ajhh ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
             -> phi_ajhh ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajhi phi_ajhh (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanConditional_ p_ajhe p_ajhf p_ajhg = Tag (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))
                                                                (NA_I p_ajhe :* (NA_I p_ajhf :* (NA_I p_ajhg :* NP0)))
pattern StatementSrcSpanAssign_ ::
          phi_ajhm ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))
          -> phi_ajhm ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
             -> phi_ajhm ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajhn phi_ajhm (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanAssign_ p_ajhj p_ajhk p_ajhl = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))
                                                           (NA_I p_ajhj :* (NA_I p_ajhk :* (NA_I p_ajhl :* NP0)))
pattern StatementSrcSpanAugmentedAssign_ ::
          phi_ajhs ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajhs ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))
             -> phi_ajhs ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
                -> phi_ajhs ( 'S ( 'S ( 'S ( 'S  'Z))))
                   -> View kon_ajht phi_ajhs (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanAugmentedAssign_ p_ajho p_ajhp p_ajhq p_ajhr = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))
                                                                           (NA_I p_ajho :* (NA_I p_ajhp :* (NA_I p_ajhq :* (NA_I p_ajhr :* NP0))))
pattern StatementSrcSpanAnnotatedAssign_ ::
          phi_ajhy ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajhy ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
             -> phi_ajhy ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))
                -> phi_ajhy ( 'S ( 'S ( 'S ( 'S  'Z))))
                   -> View kon_ajhz phi_ajhy (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanAnnotatedAssign_ p_ajhu p_ajhv p_ajhw p_ajhx = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))
                                                                           (NA_I p_ajhu :* (NA_I p_ajhv :* (NA_I p_ajhw :* (NA_I p_ajhx :* NP0))))
pattern StatementSrcSpanDecorated_ ::
          phi_ajhD ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))
          -> phi_ajhD ( 'S ( 'S  'Z))
             -> phi_ajhD ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajhE phi_ajhD (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanDecorated_ p_ajhA p_ajhB p_ajhC = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))
                                                              (NA_I p_ajhA :* (NA_I p_ajhB :* (NA_I p_ajhC :* NP0)))
pattern StatementSrcSpanReturn_ ::
          phi_ajhH ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))
          -> phi_ajhH ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajhI phi_ajhH (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanReturn_ p_ajhF p_ajhG = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))
                                                    (NA_I p_ajhF :* (NA_I p_ajhG :* NP0))
pattern StatementSrcSpanTry_ ::
          phi_ajhO ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
          -> phi_ajhO ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))
             -> phi_ajhO ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
                -> phi_ajhO ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
                   -> phi_ajhO ( 'S ( 'S ( 'S ( 'S  'Z))))
                      -> View kon_ajhP phi_ajhO (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanTry_ p_ajhJ p_ajhK p_ajhL p_ajhM p_ajhN = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))
                                                                      (NA_I p_ajhJ :* (NA_I p_ajhK :* (NA_I p_ajhL :* (NA_I p_ajhM :* (NA_I p_ajhN :* NP0)))))
pattern StatementSrcSpanRaise_ ::
          phi_ajhS ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))
          -> phi_ajhS ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajhT phi_ajhS (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanRaise_ p_ajhQ p_ajhR = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))
                                                   (NA_I p_ajhQ :* (NA_I p_ajhR :* NP0))
pattern StatementSrcSpanWith_ ::
          phi_ajhX ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
          -> phi_ajhX ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
             -> phi_ajhX ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajhY phi_ajhX (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanWith_ p_ajhU p_ajhV p_ajhW = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))
                                                         (NA_I p_ajhU :* (NA_I p_ajhV :* (NA_I p_ajhW :* NP0)))
pattern StatementSrcSpanAsyncWith_ ::
          phi_aji1 ( 'S ( 'S  'Z))
          -> phi_aji1 ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_aji2 phi_aji1 (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanAsyncWith_ p_ajhZ p_aji0 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))
                                                       (NA_I p_ajhZ :* (NA_I p_aji0 :* NP0))
pattern StatementSrcSpanPass_ ::
          phi_aji4 ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_aji5 phi_aji4 (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanPass_ p_aji3 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))
                                           (NA_I p_aji3 :* NP0)
pattern StatementSrcSpanBreak_ ::
          phi_aji7 ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_aji8 phi_aji7 (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanBreak_ p_aji6 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))
                                            (NA_I p_aji6 :* NP0)
pattern StatementSrcSpanContinue_ ::
          phi_ajia ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajib phi_ajia (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanContinue_ p_aji9 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))
                                               (NA_I p_aji9 :* NP0)
pattern StatementSrcSpanDelete_ ::
          phi_ajie ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))
          -> phi_ajie ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajif phi_ajie (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanDelete_ p_ajic p_ajid = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))
                                                    (NA_I p_ajic :* (NA_I p_ajid :* NP0))
pattern StatementSrcSpanStmtExpr_ ::
          phi_ajii ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajii ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajij phi_ajii (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanStmtExpr_ p_ajig p_ajih = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))))
                                                      (NA_I p_ajig :* (NA_I p_ajih :* NP0))
pattern StatementSrcSpanGlobal_ ::
          phi_ajim ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))
          -> phi_ajim ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajin phi_ajim (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanGlobal_ p_ajik p_ajil = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))))
                                                    (NA_I p_ajik :* (NA_I p_ajil :* NP0))
pattern StatementSrcSpanNonLocal_ ::
          phi_ajiq ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))
          -> phi_ajiq ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajir phi_ajiq (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanNonLocal_ p_ajio p_ajip = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))))))
                                                      (NA_I p_ajio :* (NA_I p_ajip :* NP0))
pattern StatementSrcSpanAssert_ ::
          phi_ajiu ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))
          -> phi_ajiu ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajiv phi_ajiu (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanAssert_ p_ajis p_ajit = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))))))
                                                    (NA_I p_ajis :* (NA_I p_ajit :* NP0))
pattern StatementSrcSpanPrint_ ::
          kon_ajiB  'KBool
          -> phi_ajiA ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))
             -> kon_ajiB  'KBool
                -> phi_ajiA ( 'S ( 'S ( 'S ( 'S  'Z))))
                   -> View kon_ajiB phi_ajiA (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanPrint_ p_ajiw p_ajix p_ajiy p_ajiz = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))))))))
                                                                 (NA_K p_ajiw :* (NA_I p_ajix :* (NA_K p_ajiy :* (NA_I p_ajiz :* NP0))))
pattern StatementSrcSpanExec_ ::
          phi_ajiF ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajiF ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))
             -> phi_ajiF ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajiG phi_ajiF (Lkup ( 'S ( 'S  'Z)) CodesModuleSrcSpan)
pattern StatementSrcSpanExec_ p_ajiC p_ajiD p_ajiE = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))))))))
                                                         (NA_I p_ajiC :* (NA_I p_ajiD :* (NA_I p_ajiE :* NP0)))
pattern ListImportItemSrcSpan_Ifx0 ::
          View kon_ajiI phi_ajiH (Lkup ( 'S ( 'S ( 'S  'Z))) CodesModuleSrcSpan)
pattern ListImportItemSrcSpan_Ifx0 = Tag CZ NP0
pattern ListImportItemSrcSpan_Ifx1 ::
          phi_ajiL ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))
          -> phi_ajiL ( 'S ( 'S ( 'S  'Z)))
             -> View kon_ajiM phi_ajiL (Lkup ( 'S ( 'S ( 'S  'Z))) CodesModuleSrcSpan)
pattern ListImportItemSrcSpan_Ifx1 p_ajiJ p_ajiK = Tag (CS CZ)
                                                       (NA_I p_ajiJ :* (NA_I p_ajiK :* NP0))
pattern SpanCoLinear_ ::
          kon_ajiS  'KString
          -> kon_ajiS  'KInt
             -> kon_ajiS  'KInt
                -> kon_ajiS  'KInt
                   -> View kon_ajiS phi_ajiR (Lkup ( 'S ( 'S ( 'S ( 'S  'Z)))) CodesModuleSrcSpan)
pattern SpanCoLinear_ p_ajiN p_ajiO p_ajiP p_ajiQ = Tag CZ
                                                        (NA_K p_ajiN :* (NA_K p_ajiO :* (NA_K p_ajiP :* (NA_K p_ajiQ :* NP0))))
pattern SpanMultiLine_ ::
          kon_ajiZ  'KString
          -> kon_ajiZ  'KInt
             -> kon_ajiZ  'KInt
                -> kon_ajiZ  'KInt
                   -> kon_ajiZ  'KInt
                      -> View kon_ajiZ phi_ajiY (Lkup ( 'S ( 'S ( 'S ( 'S  'Z)))) CodesModuleSrcSpan)
pattern SpanMultiLine_ p_ajiT p_ajiU p_ajiV p_ajiW p_ajiX = Tag (CS CZ)
                                                                (NA_K p_ajiT :* (NA_K p_ajiU :* (NA_K p_ajiV :* (NA_K p_ajiW :* (NA_K p_ajiX :* NP0)))))
pattern SpanPoint_ ::
          kon_ajj4  'KString
          -> kon_ajj4  'KInt
             -> kon_ajj4  'KInt
                -> View kon_ajj4 phi_ajj3 (Lkup ( 'S ( 'S ( 'S ( 'S  'Z)))) CodesModuleSrcSpan)
pattern SpanPoint_ p_ajj0 p_ajj1 p_ajj2 = Tag (CS (CS CZ))
                                              (NA_K p_ajj0 :* (NA_K p_ajj1 :* (NA_K p_ajj2 :* NP0)))
pattern SpanEmpty_ ::
          View kon_ajj6 phi_ajj5 (Lkup ( 'S ( 'S ( 'S ( 'S  'Z)))) CodesModuleSrcSpan)
pattern SpanEmpty_ = Tag (CS (CS (CS CZ))) NP0
pattern ImportRelativeSrcSpanImportRelative_ ::
          kon_ajjb  'KInt
          -> phi_ajja ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))
             -> phi_ajja ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajjb phi_ajja (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))) CodesModuleSrcSpan)
pattern ImportRelativeSrcSpanImportRelative_ p_ajj7 p_ajj8 p_ajj9 = Tag CZ
                                                                        (NA_K p_ajj7 :* (NA_I p_ajj8 :* (NA_I p_ajj9 :* NP0)))
pattern FromItemsSrcSpanImportEverything_ ::
          phi_ajjd ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajje phi_ajjd (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))) CodesModuleSrcSpan)
pattern FromItemsSrcSpanImportEverything_ p_ajjc = Tag CZ
                                                       (NA_I p_ajjc :* NP0)
pattern FromItemsSrcSpanFromItems_ ::
          phi_ajjh ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))
          -> phi_ajjh ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajji phi_ajjh (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))) CodesModuleSrcSpan)
pattern FromItemsSrcSpanFromItems_ p_ajjf p_ajjg = Tag (CS CZ)
                                                       (NA_I p_ajjf :* (NA_I p_ajjg :* NP0))
pattern ExprSrcSpanVar_ ::
          phi_ajjl ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> phi_ajjl ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajjm phi_ajjl (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanVar_ p_ajjj p_ajjk = Tag CZ
                                            (NA_I p_ajjj :* (NA_I p_ajjk :* NP0))
pattern ExprSrcSpanInt_ ::
          kon_ajjr  'KInteger
          -> kon_ajjr  'KString
             -> phi_ajjq ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajjr phi_ajjq (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanInt_ p_ajjn p_ajjo p_ajjp = Tag (CS CZ)
                                                   (NA_K p_ajjn :* (NA_K p_ajjo :* (NA_I p_ajjp :* NP0)))
pattern ExprSrcSpanLongInt_ ::
          kon_ajjw  'KInteger
          -> kon_ajjw  'KString
             -> phi_ajjv ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajjw phi_ajjv (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanLongInt_ p_ajjs p_ajjt p_ajju = Tag (CS (CS CZ))
                                                       (NA_K p_ajjs :* (NA_K p_ajjt :* (NA_I p_ajju :* NP0)))
pattern ExprSrcSpanFloat_ ::
          kon_ajjB  'KDouble
          -> kon_ajjB  'KString
             -> phi_ajjA ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajjB phi_ajjA (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanFloat_ p_ajjx p_ajjy p_ajjz = Tag (CS (CS (CS CZ)))
                                                     (NA_K p_ajjx :* (NA_K p_ajjy :* (NA_I p_ajjz :* NP0)))
pattern ExprSrcSpanImaginary_ ::
          kon_ajjG  'KDouble
          -> kon_ajjG  'KString
             -> phi_ajjF ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajjG phi_ajjF (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanImaginary_ p_ajjC p_ajjD p_ajjE = Tag (CS (CS (CS (CS CZ))))
                                                         (NA_K p_ajjC :* (NA_K p_ajjD :* (NA_I p_ajjE :* NP0)))
pattern ExprSrcSpanBool_ ::
          kon_ajjK  'KBool
          -> phi_ajjJ ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajjK phi_ajjJ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanBool_ p_ajjH p_ajjI = Tag (CS (CS (CS (CS (CS CZ)))))
                                             (NA_K p_ajjH :* (NA_I p_ajjI :* NP0))
pattern ExprSrcSpanNone_ ::
          phi_ajjM ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajjN phi_ajjM (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanNone_ p_ajjL = Tag (CS (CS (CS (CS (CS (CS CZ))))))
                                      (NA_I p_ajjL :* NP0)
pattern ExprSrcSpanEllipsis_ ::
          phi_ajjP ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajjQ phi_ajjP (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanEllipsis_ p_ajjO = Tag (CS (CS (CS (CS (CS (CS (CS CZ)))))))
                                          (NA_I p_ajjO :* NP0)
pattern ExprSrcSpanByteStrings_ ::
          phi_ajjT ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))
          -> phi_ajjT ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajjU phi_ajjT (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanByteStrings_ p_ajjR p_ajjS = Tag (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))
                                                    (NA_I p_ajjR :* (NA_I p_ajjS :* NP0))
pattern ExprSrcSpanStrings_ ::
          phi_ajjX ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))
          -> phi_ajjX ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajjY phi_ajjX (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanStrings_ p_ajjV p_ajjW = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))
                                                (NA_I p_ajjV :* (NA_I p_ajjW :* NP0))
pattern ExprSrcSpanUnicodeStrings_ ::
          phi_ajk1 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))
          -> phi_ajk1 ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajk2 phi_ajk1 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanUnicodeStrings_ p_ajjZ p_ajk0 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))
                                                       (NA_I p_ajjZ :* (NA_I p_ajk0 :* NP0))
pattern ExprSrcSpanCall_ ::
          phi_ajk6 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajk6 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))
             -> phi_ajk6 ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajk7 phi_ajk6 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanCall_ p_ajk3 p_ajk4 p_ajk5 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))
                                                    (NA_I p_ajk3 :* (NA_I p_ajk4 :* (NA_I p_ajk5 :* NP0)))
pattern ExprSrcSpanSubscript_ ::
          phi_ajkb ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajkb ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
             -> phi_ajkb ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajkc phi_ajkb (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanSubscript_ p_ajk8 p_ajk9 p_ajka = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))
                                                         (NA_I p_ajk8 :* (NA_I p_ajk9 :* (NA_I p_ajka :* NP0)))
pattern ExprSrcSpanSlicedExpr_ ::
          phi_ajkg ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajkg ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))
             -> phi_ajkg ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajkh phi_ajkg (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanSlicedExpr_ p_ajkd p_ajke p_ajkf = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))
                                                          (NA_I p_ajkd :* (NA_I p_ajke :* (NA_I p_ajkf :* NP0)))
pattern ExprSrcSpanCondExpr_ ::
          phi_ajkm ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajkm ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
             -> phi_ajkm ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
                -> phi_ajkm ( 'S ( 'S ( 'S ( 'S  'Z))))
                   -> View kon_ajkn phi_ajkm (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanCondExpr_ p_ajki p_ajkj p_ajkk p_ajkl = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))
                                                               (NA_I p_ajki :* (NA_I p_ajkj :* (NA_I p_ajkk :* (NA_I p_ajkl :* NP0))))
pattern ExprSrcSpanBinaryOp_ ::
          phi_ajks ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))
          -> phi_ajks ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
             -> phi_ajks ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
                -> phi_ajks ( 'S ( 'S ( 'S ( 'S  'Z))))
                   -> View kon_ajkt phi_ajks (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanBinaryOp_ p_ajko p_ajkp p_ajkq p_ajkr = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))
                                                               (NA_I p_ajko :* (NA_I p_ajkp :* (NA_I p_ajkq :* (NA_I p_ajkr :* NP0))))
pattern ExprSrcSpanUnaryOp_ ::
          phi_ajkx ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))
          -> phi_ajkx ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
             -> phi_ajkx ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajky phi_ajkx (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanUnaryOp_ p_ajku p_ajkv p_ajkw = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))
                                                       (NA_I p_ajku :* (NA_I p_ajkv :* (NA_I p_ajkw :* NP0)))
pattern ExprSrcSpanDot_ ::
          phi_ajkC ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajkC ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
             -> phi_ajkC ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajkD phi_ajkC (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanDot_ p_ajkz p_ajkA p_ajkB = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))
                                                   (NA_I p_ajkz :* (NA_I p_ajkA :* (NA_I p_ajkB :* NP0)))
pattern ExprSrcSpanLambda_ ::
          phi_ajkH ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))
          -> phi_ajkH ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
             -> phi_ajkH ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajkI phi_ajkH (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanLambda_ p_ajkE p_ajkF p_ajkG = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))
                                                      (NA_I p_ajkE :* (NA_I p_ajkF :* (NA_I p_ajkG :* NP0)))
pattern ExprSrcSpanTuple_ ::
          phi_ajkL ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))
          -> phi_ajkL ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajkM phi_ajkL (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanTuple_ p_ajkJ p_ajkK = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))
                                              (NA_I p_ajkJ :* (NA_I p_ajkK :* NP0))
pattern ExprSrcSpanYield_ ::
          phi_ajkP ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))
          -> phi_ajkP ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajkQ phi_ajkP (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanYield_ p_ajkN p_ajkO = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))
                                              (NA_I p_ajkN :* (NA_I p_ajkO :* NP0))
pattern ExprSrcSpanGenerator_ ::
          phi_ajkT ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))
          -> phi_ajkT ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajkU phi_ajkT (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanGenerator_ p_ajkR p_ajkS = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))
                                                  (NA_I p_ajkR :* (NA_I p_ajkS :* NP0))
pattern ExprSrcSpanAwait_ ::
          phi_ajkX ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajkX ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajkY phi_ajkX (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanAwait_ p_ajkV p_ajkW = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))))
                                              (NA_I p_ajkV :* (NA_I p_ajkW :* NP0))
pattern ExprSrcSpanListComp_ ::
          phi_ajl1 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))
          -> phi_ajl1 ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajl2 phi_ajl1 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanListComp_ p_ajkZ p_ajl0 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))))
                                                 (NA_I p_ajkZ :* (NA_I p_ajl0 :* NP0))
pattern ExprSrcSpanList_ ::
          phi_ajl5 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))
          -> phi_ajl5 ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajl6 phi_ajl5 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanList_ p_ajl3 p_ajl4 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))))))
                                             (NA_I p_ajl3 :* (NA_I p_ajl4 :* NP0))
pattern ExprSrcSpanDictionary_ ::
          phi_ajl9 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))
          -> phi_ajl9 ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajla phi_ajl9 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanDictionary_ p_ajl7 p_ajl8 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))))))
                                                   (NA_I p_ajl7 :* (NA_I p_ajl8 :* NP0))
pattern ExprSrcSpanDictComp_ ::
          phi_ajld ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))
          -> phi_ajld ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajle phi_ajld (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanDictComp_ p_ajlb p_ajlc = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))))))))
                                                 (NA_I p_ajlb :* (NA_I p_ajlc :* NP0))
pattern ExprSrcSpanSet_ ::
          phi_ajlh ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))
          -> phi_ajlh ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajli phi_ajlh (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanSet_ p_ajlf p_ajlg = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))))))))
                                            (NA_I p_ajlf :* (NA_I p_ajlg :* NP0))
pattern ExprSrcSpanSetComp_ ::
          phi_ajll ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))
          -> phi_ajll ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajlm phi_ajll (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanSetComp_ p_ajlj p_ajlk = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))))))))))
                                                (NA_I p_ajlj :* (NA_I p_ajlk :* NP0))
pattern ExprSrcSpanStarred_ ::
          phi_ajlp ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajlp ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajlq phi_ajlp (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanStarred_ p_ajln p_ajlo = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))))))))))
                                                (NA_I p_ajln :* (NA_I p_ajlo :* NP0))
pattern ExprSrcSpanParen_ ::
          phi_ajlt ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajlt ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajlu phi_ajlt (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanParen_ p_ajlr p_ajls = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))))))))))))
                                              (NA_I p_ajlr :* (NA_I p_ajls :* NP0))
pattern ExprSrcSpanStringConversion_ ::
          phi_ajlx ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajlx ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajly phi_ajlx (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))) CodesModuleSrcSpan)
pattern ExprSrcSpanStringConversion_ p_ajlv p_ajlw = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))))))))))))
                                                         (NA_I p_ajlv :* (NA_I p_ajlw :* NP0))
pattern SuiteSrcSpan_Ifx0 ::
          View kon_ajlA phi_ajlz (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))) CodesModuleSrcSpan)
pattern SuiteSrcSpan_Ifx0 = Tag CZ NP0
pattern SuiteSrcSpan_Ifx1 ::
          phi_ajlD ( 'S ( 'S  'Z))
          -> phi_ajlD ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
             -> View kon_ajlE phi_ajlD (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))) CodesModuleSrcSpan)
pattern SuiteSrcSpan_Ifx1 p_ajlB p_ajlC = Tag (CS CZ)
                                              (NA_I p_ajlB :* (NA_I p_ajlC :* NP0))
pattern ListExprSrcSpan_Ifx0 ::
          View kon_ajlG phi_ajlF (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))) CodesModuleSrcSpan)
pattern ListExprSrcSpan_Ifx0 = Tag CZ NP0
pattern ListExprSrcSpan_Ifx1 ::
          phi_ajlJ ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajlJ ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))
             -> View kon_ajlK phi_ajlJ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))) CodesModuleSrcSpan)
pattern ListExprSrcSpan_Ifx1 p_ajlH p_ajlI = Tag (CS CZ)
                                                 (NA_I p_ajlH :* (NA_I p_ajlI :* NP0))
pattern IdentSrcSpanIdent_ ::
          kon_ajlO  'KString
          -> phi_ajlN ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajlO phi_ajlN (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))) CodesModuleSrcSpan)
pattern IdentSrcSpanIdent_ p_ajlL p_ajlM = Tag CZ
                                               (NA_K p_ajlL :* (NA_I p_ajlM :* NP0))
pattern ListParameterSrcSpan_Ifx0 ::
          View kon_ajlQ phi_ajlP (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))) CodesModuleSrcSpan)
pattern ListParameterSrcSpan_Ifx0 = Tag CZ NP0
pattern ListParameterSrcSpan_Ifx1 ::
          phi_ajlT ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))
          -> phi_ajlT ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))
             -> View kon_ajlU phi_ajlT (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))) CodesModuleSrcSpan)
pattern ListParameterSrcSpan_Ifx1 p_ajlR p_ajlS = Tag (CS CZ)
                                                      (NA_I p_ajlR :* (NA_I p_ajlS :* NP0))
pattern MaybeExprSrcSpanNothing_ ::
          View kon_ajlW phi_ajlV (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))) CodesModuleSrcSpan)
pattern MaybeExprSrcSpanNothing_ = Tag CZ NP0
pattern MaybeExprSrcSpanJust_ ::
          phi_ajlY ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> View kon_ajlZ phi_ajlY (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))) CodesModuleSrcSpan)
pattern MaybeExprSrcSpanJust_ p_ajlX = Tag (CS CZ)
                                           (NA_I p_ajlX :* NP0)
pattern ListArgumentSrcSpan_Ifx0 ::
          View kon_ajm1 phi_ajm0 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))) CodesModuleSrcSpan)
pattern ListArgumentSrcSpan_Ifx0 = Tag CZ NP0
pattern ListArgumentSrcSpan_Ifx1 ::
          phi_ajm4 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))
          -> phi_ajm4 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))
             -> View kon_ajm5 phi_ajm4 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))) CodesModuleSrcSpan)
pattern ListArgumentSrcSpan_Ifx1 p_ajm2 p_ajm3 = Tag (CS CZ)
                                                     (NA_I p_ajm2 :* (NA_I p_ajm3 :* NP0))
pattern ListTup1ExprSrcSpanSuiteSrcSpan_Ifx0 ::
          View kon_ajm7 phi_ajm6 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))) CodesModuleSrcSpan)
pattern ListTup1ExprSrcSpanSuiteSrcSpan_Ifx0 = Tag CZ NP0
pattern ListTup1ExprSrcSpanSuiteSrcSpan_Ifx1 ::
          phi_ajma ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_ajma ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))
             -> View kon_ajmb phi_ajma (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))) CodesModuleSrcSpan)
pattern ListTup1ExprSrcSpanSuiteSrcSpan_Ifx1 p_ajm8 p_ajm9 = Tag (CS CZ)
                                                                 (NA_I p_ajm8 :* (NA_I p_ajm9 :* NP0))
pattern AssignOpSrcSpanPlusAssign_ ::
          phi_ajmd ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajme phi_ajmd (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesModuleSrcSpan)
pattern AssignOpSrcSpanPlusAssign_ p_ajmc = Tag CZ
                                                (NA_I p_ajmc :* NP0)
pattern AssignOpSrcSpanMinusAssign_ ::
          phi_ajmg ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajmh phi_ajmg (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesModuleSrcSpan)
pattern AssignOpSrcSpanMinusAssign_ p_ajmf = Tag (CS CZ)
                                                 (NA_I p_ajmf :* NP0)
pattern AssignOpSrcSpanMultAssign_ ::
          phi_ajmj ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajmk phi_ajmj (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesModuleSrcSpan)
pattern AssignOpSrcSpanMultAssign_ p_ajmi = Tag (CS (CS CZ))
                                                (NA_I p_ajmi :* NP0)
pattern AssignOpSrcSpanDivAssign_ ::
          phi_ajmm ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajmn phi_ajmm (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesModuleSrcSpan)
pattern AssignOpSrcSpanDivAssign_ p_ajml = Tag (CS (CS (CS CZ)))
                                               (NA_I p_ajml :* NP0)
pattern AssignOpSrcSpanModAssign_ ::
          phi_ajmp ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajmq phi_ajmp (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesModuleSrcSpan)
pattern AssignOpSrcSpanModAssign_ p_ajmo = Tag (CS (CS (CS (CS CZ))))
                                               (NA_I p_ajmo :* NP0)
pattern AssignOpSrcSpanPowAssign_ ::
          phi_ajms ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajmt phi_ajms (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesModuleSrcSpan)
pattern AssignOpSrcSpanPowAssign_ p_ajmr = Tag (CS (CS (CS (CS (CS CZ)))))
                                               (NA_I p_ajmr :* NP0)
pattern AssignOpSrcSpanBinAndAssign_ ::
          phi_ajmv ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajmw phi_ajmv (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesModuleSrcSpan)
pattern AssignOpSrcSpanBinAndAssign_ p_ajmu = Tag (CS (CS (CS (CS (CS (CS CZ))))))
                                                  (NA_I p_ajmu :* NP0)
pattern AssignOpSrcSpanBinOrAssign_ ::
          phi_ajmy ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajmz phi_ajmy (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesModuleSrcSpan)
pattern AssignOpSrcSpanBinOrAssign_ p_ajmx = Tag (CS (CS (CS (CS (CS (CS (CS CZ)))))))
                                                 (NA_I p_ajmx :* NP0)
pattern AssignOpSrcSpanBinXorAssign_ ::
          phi_ajmB ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajmC phi_ajmB (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesModuleSrcSpan)
pattern AssignOpSrcSpanBinXorAssign_ p_ajmA = Tag (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))
                                                  (NA_I p_ajmA :* NP0)
pattern AssignOpSrcSpanLeftShiftAssign_ ::
          phi_ajmE ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajmF phi_ajmE (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesModuleSrcSpan)
pattern AssignOpSrcSpanLeftShiftAssign_ p_ajmD = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))
                                                     (NA_I p_ajmD :* NP0)
pattern AssignOpSrcSpanRightShiftAssign_ ::
          phi_ajmH ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajmI phi_ajmH (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesModuleSrcSpan)
pattern AssignOpSrcSpanRightShiftAssign_ p_ajmG = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))
                                                      (NA_I p_ajmG :* NP0)
pattern AssignOpSrcSpanFloorDivAssign_ ::
          phi_ajmK ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajmL phi_ajmK (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesModuleSrcSpan)
pattern AssignOpSrcSpanFloorDivAssign_ p_ajmJ = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))
                                                    (NA_I p_ajmJ :* NP0)
pattern AssignOpSrcSpanMatrixMultAssign_ ::
          phi_ajmN ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajmO phi_ajmN (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))) CodesModuleSrcSpan)
pattern AssignOpSrcSpanMatrixMultAssign_ p_ajmM = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))
                                                      (NA_I p_ajmM :* NP0)
pattern ListDecoratorSrcSpan_Ifx0 ::
          View kon_ajmQ phi_ajmP (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))) CodesModuleSrcSpan)
pattern ListDecoratorSrcSpan_Ifx0 = Tag CZ NP0
pattern ListDecoratorSrcSpan_Ifx1 ::
          phi_ajmT ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_ajmT ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))
             -> View kon_ajmU phi_ajmT (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))) CodesModuleSrcSpan)
pattern ListDecoratorSrcSpan_Ifx1 p_ajmR p_ajmS = Tag (CS CZ)
                                                      (NA_I p_ajmR :* (NA_I p_ajmS :* NP0))
pattern ListHandlerSrcSpan_Ifx0 ::
          View kon_ajmW phi_ajmV (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))) CodesModuleSrcSpan)
pattern ListHandlerSrcSpan_Ifx0 = Tag CZ NP0
pattern ListHandlerSrcSpan_Ifx1 ::
          phi_ajmZ ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_ajmZ ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))
             -> View kon_ajn0 phi_ajmZ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))) CodesModuleSrcSpan)
pattern ListHandlerSrcSpan_Ifx1 p_ajmX p_ajmY = Tag (CS CZ)
                                                    (NA_I p_ajmX :* (NA_I p_ajmY :* NP0))
pattern RaiseExprSrcSpanRaiseV3_ ::
          phi_ajn2 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))
          -> View kon_ajn3 phi_ajn2 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))) CodesModuleSrcSpan)
pattern RaiseExprSrcSpanRaiseV3_ p_ajn1 = Tag CZ
                                              (NA_I p_ajn1 :* NP0)
pattern RaiseExprSrcSpanRaiseV2_ ::
          phi_ajn5 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> View kon_ajn6 phi_ajn5 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))) CodesModuleSrcSpan)
pattern RaiseExprSrcSpanRaiseV2_ p_ajn4 = Tag (CS CZ)
                                              (NA_I p_ajn4 :* NP0)
pattern ListTup1ExprSrcSpanMaybeExprSrcSpan_Ifx0 ::
          View kon_ajn8 phi_ajn7 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))) CodesModuleSrcSpan)
pattern ListTup1ExprSrcSpanMaybeExprSrcSpan_Ifx0 = Tag CZ NP0
pattern ListTup1ExprSrcSpanMaybeExprSrcSpan_Ifx1 ::
          phi_ajnb ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_ajnb ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))
             -> View kon_ajnc phi_ajnb (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))) CodesModuleSrcSpan)
pattern ListTup1ExprSrcSpanMaybeExprSrcSpan_Ifx1 p_ajn9 p_ajna = Tag (CS CZ)
                                                                     (NA_I p_ajn9 :* (NA_I p_ajna :* NP0))
pattern ListIdentSrcSpan_Ifx0 ::
          View kon_ajne phi_ajnd (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))) CodesModuleSrcSpan)
pattern ListIdentSrcSpan_Ifx0 = Tag CZ NP0
pattern ListIdentSrcSpan_Ifx1 ::
          phi_ajnh ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> phi_ajnh ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))
             -> View kon_ajni phi_ajnh (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))) CodesModuleSrcSpan)
pattern ListIdentSrcSpan_Ifx1 p_ajnf p_ajng = Tag (CS CZ)
                                                  (NA_I p_ajnf :* (NA_I p_ajng :* NP0))
pattern MaybeTup1ExprSrcSpanMaybeExprSrcSpanNothing_ ::
          View kon_ajnk phi_ajnj (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeTup1ExprSrcSpanMaybeExprSrcSpanNothing_ = Tag CZ NP0
pattern MaybeTup1ExprSrcSpanMaybeExprSrcSpanJust_ ::
          phi_ajnm ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))
          -> View kon_ajnn phi_ajnm (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeTup1ExprSrcSpanMaybeExprSrcSpanJust_ p_ajnl = Tag (CS CZ)
                                                               (NA_I p_ajnl :* NP0)
pattern ImportItemSrcSpanImportItem_ ::
          phi_ajnr ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))
          -> phi_ajnr ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))
             -> phi_ajnr ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajns phi_ajnr (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))) CodesModuleSrcSpan)
pattern ImportItemSrcSpanImportItem_ p_ajno p_ajnp p_ajnq = Tag CZ
                                                                (NA_I p_ajno :* (NA_I p_ajnp :* (NA_I p_ajnq :* NP0)))
pattern DottedNameSrcSpan_Ifx0 ::
          View kon_ajnu phi_ajnt (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))) CodesModuleSrcSpan)
pattern DottedNameSrcSpan_Ifx0 = Tag CZ NP0
pattern DottedNameSrcSpan_Ifx1 ::
          phi_ajnx ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> phi_ajnx ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))
             -> View kon_ajny phi_ajnx (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))) CodesModuleSrcSpan)
pattern DottedNameSrcSpan_Ifx1 p_ajnv p_ajnw = Tag (CS CZ)
                                                   (NA_I p_ajnv :* (NA_I p_ajnw :* NP0))
pattern MaybeIdentSrcSpanNothing_ ::
          View kon_ajnA phi_ajnz (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeIdentSrcSpanNothing_ = Tag CZ NP0
pattern MaybeIdentSrcSpanJust_ ::
          phi_ajnC ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> View kon_ajnD phi_ajnC (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeIdentSrcSpanJust_ p_ajnB = Tag (CS CZ)
                                            (NA_I p_ajnB :* NP0)
pattern MaybeDottedNameSrcSpanNothing_ ::
          View kon_ajnF phi_ajnE (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeDottedNameSrcSpanNothing_ = Tag CZ NP0
pattern MaybeDottedNameSrcSpanJust_ ::
          phi_ajnH ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))
          -> View kon_ajnI phi_ajnH (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeDottedNameSrcSpanJust_ p_ajnG = Tag (CS CZ)
                                                 (NA_I p_ajnG :* NP0)
pattern ListFromItemSrcSpan_Ifx0 ::
          View kon_ajnK phi_ajnJ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ListFromItemSrcSpan_Ifx0 = Tag CZ NP0
pattern ListFromItemSrcSpan_Ifx1 ::
          phi_ajnN ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))
          -> phi_ajnN ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))
             -> View kon_ajnO phi_ajnN (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ListFromItemSrcSpan_Ifx1 p_ajnL p_ajnM = Tag (CS CZ)
                                                     (NA_I p_ajnL :* (NA_I p_ajnM :* NP0))
pattern FromItemSrcSpanFromItem_ ::
          phi_ajnS ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> phi_ajnS ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))
             -> phi_ajnS ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajnT phi_ajnS (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern FromItemSrcSpanFromItem_ p_ajnP p_ajnQ p_ajnR = Tag CZ
                                                            (NA_I p_ajnP :* (NA_I p_ajnQ :* (NA_I p_ajnR :* NP0)))
pattern ListString_Ifx0 ::
          View kon_ajnV phi_ajnU (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ListString_Ifx0 = Tag CZ NP0
pattern ListString_Ifx1 ::
          kon_ajnZ  'KString
          -> phi_ajnY ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))
             -> View kon_ajnZ phi_ajnY (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ListString_Ifx1 p_ajnW p_ajnX = Tag (CS CZ)
                                            (NA_K p_ajnW :* (NA_I p_ajnX :* NP0))
pattern ListSliceSrcSpan_Ifx0 ::
          View kon_ajo1 phi_ajo0 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ListSliceSrcSpan_Ifx0 = Tag CZ NP0
pattern ListSliceSrcSpan_Ifx1 ::
          phi_ajo4 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))
          -> phi_ajo4 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))
             -> View kon_ajo5 phi_ajo4 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ListSliceSrcSpan_Ifx1 p_ajo2 p_ajo3 = Tag (CS CZ)
                                                  (NA_I p_ajo2 :* (NA_I p_ajo3 :* NP0))
pattern OpSrcSpanAnd_ ::
          phi_ajo7 ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajo8 phi_ajo7 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanAnd_ p_ajo6 = Tag CZ (NA_I p_ajo6 :* NP0)
pattern OpSrcSpanOr_ ::
          phi_ajoa ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajob phi_ajoa (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanOr_ p_ajo9 = Tag (CS CZ) (NA_I p_ajo9 :* NP0)
pattern OpSrcSpanNot_ ::
          phi_ajod ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajoe phi_ajod (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanNot_ p_ajoc = Tag (CS (CS CZ))
                                   (NA_I p_ajoc :* NP0)
pattern OpSrcSpanExponent_ ::
          phi_ajog ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajoh phi_ajog (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanExponent_ p_ajof = Tag (CS (CS (CS CZ)))
                                        (NA_I p_ajof :* NP0)
pattern OpSrcSpanLessThan_ ::
          phi_ajoj ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajok phi_ajoj (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanLessThan_ p_ajoi = Tag (CS (CS (CS (CS CZ))))
                                        (NA_I p_ajoi :* NP0)
pattern OpSrcSpanGreaterThan_ ::
          phi_ajom ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajon phi_ajom (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanGreaterThan_ p_ajol = Tag (CS (CS (CS (CS (CS CZ)))))
                                           (NA_I p_ajol :* NP0)
pattern OpSrcSpanEquality_ ::
          phi_ajop ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajoq phi_ajop (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanEquality_ p_ajoo = Tag (CS (CS (CS (CS (CS (CS CZ))))))
                                        (NA_I p_ajoo :* NP0)
pattern OpSrcSpanGreaterThanEquals_ ::
          phi_ajos ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajot phi_ajos (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanGreaterThanEquals_ p_ajor = Tag (CS (CS (CS (CS (CS (CS (CS CZ)))))))
                                                 (NA_I p_ajor :* NP0)
pattern OpSrcSpanLessThanEquals_ ::
          phi_ajov ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajow phi_ajov (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanLessThanEquals_ p_ajou = Tag (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))
                                              (NA_I p_ajou :* NP0)
pattern OpSrcSpanNotEquals_ ::
          phi_ajoy ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajoz phi_ajoy (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanNotEquals_ p_ajox = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))
                                         (NA_I p_ajox :* NP0)
pattern OpSrcSpanNotEqualsV2_ ::
          phi_ajoB ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajoC phi_ajoB (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanNotEqualsV2_ p_ajoA = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))
                                           (NA_I p_ajoA :* NP0)
pattern OpSrcSpanIn_ ::
          phi_ajoE ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajoF phi_ajoE (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanIn_ p_ajoD = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))
                                  (NA_I p_ajoD :* NP0)
pattern OpSrcSpanIs_ ::
          phi_ajoH ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajoI phi_ajoH (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanIs_ p_ajoG = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))
                                  (NA_I p_ajoG :* NP0)
pattern OpSrcSpanIsNot_ ::
          phi_ajoK ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajoL phi_ajoK (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanIsNot_ p_ajoJ = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))
                                     (NA_I p_ajoJ :* NP0)
pattern OpSrcSpanNotIn_ ::
          phi_ajoN ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajoO phi_ajoN (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanNotIn_ p_ajoM = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))
                                     (NA_I p_ajoM :* NP0)
pattern OpSrcSpanBinaryOr_ ::
          phi_ajoQ ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajoR phi_ajoQ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanBinaryOr_ p_ajoP = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))
                                        (NA_I p_ajoP :* NP0)
pattern OpSrcSpanXor_ ::
          phi_ajoT ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajoU phi_ajoT (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanXor_ p_ajoS = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))
                                   (NA_I p_ajoS :* NP0)
pattern OpSrcSpanBinaryAnd_ ::
          phi_ajoW ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajoX phi_ajoW (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanBinaryAnd_ p_ajoV = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))
                                         (NA_I p_ajoV :* NP0)
pattern OpSrcSpanShiftLeft_ ::
          phi_ajoZ ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajp0 phi_ajoZ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanShiftLeft_ p_ajoY = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))
                                         (NA_I p_ajoY :* NP0)
pattern OpSrcSpanShiftRight_ ::
          phi_ajp2 ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajp3 phi_ajp2 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanShiftRight_ p_ajp1 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))
                                          (NA_I p_ajp1 :* NP0)
pattern OpSrcSpanMultiply_ ::
          phi_ajp5 ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajp6 phi_ajp5 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanMultiply_ p_ajp4 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))
                                        (NA_I p_ajp4 :* NP0)
pattern OpSrcSpanPlus_ ::
          phi_ajp8 ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajp9 phi_ajp8 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanPlus_ p_ajp7 = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))
                                    (NA_I p_ajp7 :* NP0)
pattern OpSrcSpanMinus_ ::
          phi_ajpb ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajpc phi_ajpb (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanMinus_ p_ajpa = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))))
                                     (NA_I p_ajpa :* NP0)
pattern OpSrcSpanDivide_ ::
          phi_ajpe ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajpf phi_ajpe (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanDivide_ p_ajpd = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))))
                                      (NA_I p_ajpd :* NP0)
pattern OpSrcSpanFloorDivide_ ::
          phi_ajph ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajpi phi_ajph (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanFloorDivide_ p_ajpg = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))))))
                                           (NA_I p_ajpg :* NP0)
pattern OpSrcSpanMatrixMult_ ::
          phi_ajpk ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajpl phi_ajpk (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanMatrixMult_ p_ajpj = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))))))
                                          (NA_I p_ajpj :* NP0)
pattern OpSrcSpanInvert_ ::
          phi_ajpn ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajpo phi_ajpn (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanInvert_ p_ajpm = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ))))))))))))))))))))))))))
                                      (NA_I p_ajpm :* NP0)
pattern OpSrcSpanModulo_ ::
          phi_ajpq ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajpr phi_ajpq (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern OpSrcSpanModulo_ p_ajpp = Tag (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS (CS CZ)))))))))))))))))))))))))))
                                      (NA_I p_ajpp :* NP0)
pattern MaybeYieldArgSrcSpanNothing_ ::
          View kon_ajpt phi_ajps (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeYieldArgSrcSpanNothing_ = Tag CZ NP0
pattern MaybeYieldArgSrcSpanJust_ ::
          phi_ajpv ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))
          -> View kon_ajpw phi_ajpv (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeYieldArgSrcSpanJust_ p_ajpu = Tag (CS CZ)
                                               (NA_I p_ajpu :* NP0)
pattern ComprehensionSrcSpanComprehension_ ::
          phi_ajpA ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))
          -> phi_ajpA ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))
             -> phi_ajpA ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajpB phi_ajpA (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ComprehensionSrcSpanComprehension_ p_ajpx p_ajpy p_ajpz = Tag CZ
                                                                      (NA_I p_ajpx :* (NA_I p_ajpy :* (NA_I p_ajpz :* NP0)))
pattern ListDictKeyDatumListSrcSpan_Ifx0 ::
          View kon_ajpD phi_ajpC (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ListDictKeyDatumListSrcSpan_Ifx0 = Tag CZ NP0
pattern ListDictKeyDatumListSrcSpan_Ifx1 ::
          phi_ajpG ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))
          -> phi_ajpG ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))
             -> View kon_ajpH phi_ajpG (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ListDictKeyDatumListSrcSpan_Ifx1 p_ajpE p_ajpF = Tag (CS CZ)
                                                             (NA_I p_ajpE :* (NA_I p_ajpF :* NP0))
pattern ArgumentSrcSpanArgExpr_ ::
          phi_ajpK ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajpK ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajpL phi_ajpK (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ArgumentSrcSpanArgExpr_ p_ajpI p_ajpJ = Tag CZ
                                                    (NA_I p_ajpI :* (NA_I p_ajpJ :* NP0))
pattern ArgumentSrcSpanArgVarArgsPos_ ::
          phi_ajpO ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajpO ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajpP phi_ajpO (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ArgumentSrcSpanArgVarArgsPos_ p_ajpM p_ajpN = Tag (CS CZ)
                                                          (NA_I p_ajpM :* (NA_I p_ajpN :* NP0))
pattern ArgumentSrcSpanArgVarArgsKeyword_ ::
          phi_ajpS ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajpS ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajpT phi_ajpS (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ArgumentSrcSpanArgVarArgsKeyword_ p_ajpQ p_ajpR = Tag (CS (CS CZ))
                                                              (NA_I p_ajpQ :* (NA_I p_ajpR :* NP0))
pattern ArgumentSrcSpanArgKeyword_ ::
          phi_ajpX ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> phi_ajpX ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
             -> phi_ajpX ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajpY phi_ajpX (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ArgumentSrcSpanArgKeyword_ p_ajpU p_ajpV p_ajpW = Tag (CS (CS (CS CZ)))
                                                              (NA_I p_ajpU :* (NA_I p_ajpV :* (NA_I p_ajpW :* NP0)))
pattern SliceSrcSpanSliceProper_ ::
          phi_ajq3 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))
          -> phi_ajq3 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))
             -> phi_ajq3 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))
                -> phi_ajq3 ( 'S ( 'S ( 'S ( 'S  'Z))))
                   -> View kon_ajq4 phi_ajq3 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern SliceSrcSpanSliceProper_ p_ajpZ p_ajq0 p_ajq1 p_ajq2 = Tag CZ
                                                                   (NA_I p_ajpZ :* (NA_I p_ajq0 :* (NA_I p_ajq1 :* (NA_I p_ajq2 :* NP0))))
pattern SliceSrcSpanSliceExpr_ ::
          phi_ajq7 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajq7 ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajq8 phi_ajq7 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern SliceSrcSpanSliceExpr_ p_ajq5 p_ajq6 = Tag (CS CZ)
                                                   (NA_I p_ajq5 :* (NA_I p_ajq6 :* NP0))
pattern SliceSrcSpanSliceEllipsis_ ::
          phi_ajqa ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajqb phi_ajqa (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern SliceSrcSpanSliceEllipsis_ p_ajq9 = Tag (CS (CS CZ))
                                                (NA_I p_ajq9 :* NP0)
pattern MaybeMaybeExprSrcSpanNothing_ ::
          View kon_ajqd phi_ajqc (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeMaybeExprSrcSpanNothing_ = Tag CZ NP0
pattern MaybeMaybeExprSrcSpanJust_ ::
          phi_ajqf ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))
          -> View kon_ajqg phi_ajqf (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeMaybeExprSrcSpanJust_ p_ajqe = Tag (CS CZ)
                                                (NA_I p_ajqe :* NP0)
pattern ParameterSrcSpanParam_ ::
          phi_ajql ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> phi_ajql ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))
             -> phi_ajql ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))
                -> phi_ajql ( 'S ( 'S ( 'S ( 'S  'Z))))
                   -> View kon_ajqm phi_ajql (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ParameterSrcSpanParam_ p_ajqh p_ajqi p_ajqj p_ajqk = Tag CZ
                                                                 (NA_I p_ajqh :* (NA_I p_ajqi :* (NA_I p_ajqj :* (NA_I p_ajqk :* NP0))))
pattern ParameterSrcSpanVarArgsPos_ ::
          phi_ajqq ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> phi_ajqq ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))
             -> phi_ajqq ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajqr phi_ajqq (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ParameterSrcSpanVarArgsPos_ p_ajqn p_ajqo p_ajqp = Tag (CS CZ)
                                                               (NA_I p_ajqn :* (NA_I p_ajqo :* (NA_I p_ajqp :* NP0)))
pattern ParameterSrcSpanVarArgsKeyword_ ::
          phi_ajqv ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> phi_ajqv ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))
             -> phi_ajqv ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajqw phi_ajqv (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ParameterSrcSpanVarArgsKeyword_ p_ajqs p_ajqt p_ajqu = Tag (CS (CS CZ))
                                                                   (NA_I p_ajqs :* (NA_I p_ajqt :* (NA_I p_ajqu :* NP0)))
pattern ParameterSrcSpanEndPositional_ ::
          phi_ajqy ( 'S ( 'S ( 'S ( 'S  'Z))))
          -> View kon_ajqz phi_ajqy (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ParameterSrcSpanEndPositional_ p_ajqx = Tag (CS (CS (CS CZ)))
                                                    (NA_I p_ajqx :* NP0)
pattern ParameterSrcSpanUnPackTuple_ ::
          phi_ajqD ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))
          -> phi_ajqD ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))
             -> phi_ajqD ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajqE phi_ajqD (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ParameterSrcSpanUnPackTuple_ p_ajqA p_ajqB p_ajqC = Tag (CS (CS (CS (CS CZ))))
                                                                (NA_I p_ajqA :* (NA_I p_ajqB :* (NA_I p_ajqC :* NP0)))
pattern ParamTupleSrcSpanParamTupleName_ ::
          phi_ajqH ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))
          -> phi_ajqH ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajqI phi_ajqH (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ParamTupleSrcSpanParamTupleName_ p_ajqF p_ajqG = Tag CZ
                                                             (NA_I p_ajqF :* (NA_I p_ajqG :* NP0))
pattern ParamTupleSrcSpanParamTuple_ ::
          phi_ajqL ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))
          -> phi_ajqL ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajqM phi_ajqL (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ParamTupleSrcSpanParamTuple_ p_ajqJ p_ajqK = Tag (CS CZ)
                                                         (NA_I p_ajqJ :* (NA_I p_ajqK :* NP0))
pattern ListParamTupleSrcSpan_Ifx0 ::
          View kon_ajqO phi_ajqN (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ListParamTupleSrcSpan_Ifx0 = Tag CZ NP0
pattern ListParamTupleSrcSpan_Ifx1 ::
          phi_ajqR ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))
          -> phi_ajqR ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))
             -> View kon_ajqS phi_ajqR (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ListParamTupleSrcSpan_Ifx1 p_ajqP p_ajqQ = Tag (CS CZ)
                                                       (NA_I p_ajqP :* (NA_I p_ajqQ :* NP0))
pattern YieldArgSrcSpanYieldFrom_ ::
          phi_ajqV ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajqV ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajqW phi_ajqV (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern YieldArgSrcSpanYieldFrom_ p_ajqT p_ajqU = Tag CZ
                                                      (NA_I p_ajqT :* (NA_I p_ajqU :* NP0))
pattern YieldArgSrcSpanYieldExpr_ ::
          phi_ajqY ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> View kon_ajqZ phi_ajqY (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern YieldArgSrcSpanYieldExpr_ p_ajqX = Tag (CS CZ)
                                               (NA_I p_ajqX :* NP0)
pattern ComprehensionExprSrcSpanComprehensionExpr_ ::
          phi_ajr1 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> View kon_ajr2 phi_ajr1 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ComprehensionExprSrcSpanComprehensionExpr_ p_ajr0 = Tag CZ
                                                                (NA_I p_ajr0 :* NP0)
pattern ComprehensionExprSrcSpanComprehensionDict_ ::
          phi_ajr4 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))
          -> View kon_ajr5 phi_ajr4 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ComprehensionExprSrcSpanComprehensionDict_ p_ajr3 = Tag (CS CZ)
                                                                (NA_I p_ajr3 :* NP0)
pattern CompForSrcSpanCompFor_ ::
          kon_ajrc  'KBool
          -> phi_ajrb ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))
             -> phi_ajrb ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
                -> phi_ajrb ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))
                   -> phi_ajrb ( 'S ( 'S ( 'S ( 'S  'Z))))
                      -> View kon_ajrc phi_ajrb (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern CompForSrcSpanCompFor_ p_ajr6 p_ajr7 p_ajr8 p_ajr9 p_ajra = Tag CZ
                                                                        (NA_K p_ajr6 :* (NA_I p_ajr7 :* (NA_I p_ajr8 :* (NA_I p_ajr9 :* (NA_I p_ajra :* NP0)))))
pattern DictKeyDatumListSrcSpanDictMappingPair_ ::
          phi_ajrf ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajrf ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
             -> View kon_ajrg phi_ajrf (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern DictKeyDatumListSrcSpanDictMappingPair_ p_ajrd p_ajre = Tag CZ
                                                                    (NA_I p_ajrd :* (NA_I p_ajre :* NP0))
pattern DictKeyDatumListSrcSpanDictUnpacking_ ::
          phi_ajri ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> View kon_ajrj phi_ajri (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern DictKeyDatumListSrcSpanDictUnpacking_ p_ajrh = Tag (CS CZ)
                                                           (NA_I p_ajrh :* NP0)
pattern MaybeCompIterSrcSpanNothing_ ::
          View kon_ajrl phi_ajrk (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeCompIterSrcSpanNothing_ = Tag CZ NP0
pattern MaybeCompIterSrcSpanJust_ ::
          phi_ajrn ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))
          -> View kon_ajro phi_ajrn (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeCompIterSrcSpanJust_ p_ajrm = Tag (CS CZ)
                                               (NA_I p_ajrm :* NP0)
pattern CompIterSrcSpanIterFor_ ::
          phi_ajrr ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))
          -> phi_ajrr ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajrs phi_ajrr (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern CompIterSrcSpanIterFor_ p_ajrp p_ajrq = Tag CZ
                                                    (NA_I p_ajrp :* (NA_I p_ajrq :* NP0))
pattern CompIterSrcSpanIterIf_ ::
          phi_ajrv ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_ajrv ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajrw phi_ajrv (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern CompIterSrcSpanIterIf_ p_ajrt p_ajru = Tag (CS CZ)
                                                   (NA_I p_ajrt :* (NA_I p_ajru :* NP0))
pattern CompIfSrcSpanCompIf_ ::
          phi_ajrA ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajrA ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))
             -> phi_ajrA ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajrB phi_ajrA (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern CompIfSrcSpanCompIf_ p_ajrx p_ajry p_ajrz = Tag CZ
                                                        (NA_I p_ajrx :* (NA_I p_ajry :* (NA_I p_ajrz :* NP0)))
pattern Tup1ExprSrcSpanSuiteSrcSpan_Ifx0 ::
          phi_ajrE ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajrE ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
             -> View kon_ajrF phi_ajrE (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern Tup1ExprSrcSpanSuiteSrcSpan_Ifx0 p_ajrC p_ajrD = Tag CZ
                                                             (NA_I p_ajrC :* (NA_I p_ajrD :* NP0))
pattern DecoratorSrcSpanDecorator_ ::
          phi_ajrJ ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))
          -> phi_ajrJ ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))
             -> phi_ajrJ ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajrK phi_ajrJ (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern DecoratorSrcSpanDecorator_ p_ajrG p_ajrH p_ajrI = Tag CZ
                                                              (NA_I p_ajrG :* (NA_I p_ajrH :* (NA_I p_ajrI :* NP0)))
pattern HandlerSrcSpanHandler_ ::
          phi_ajrO ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))
          -> phi_ajrO ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))
             -> phi_ajrO ( 'S ( 'S ( 'S ( 'S  'Z))))
                -> View kon_ajrP phi_ajrO (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern HandlerSrcSpanHandler_ p_ajrL p_ajrM p_ajrN = Tag CZ
                                                          (NA_I p_ajrL :* (NA_I p_ajrM :* (NA_I p_ajrN :* NP0)))
pattern ExceptClauseSrcSpanExceptClause_ ::
          phi_ajrS ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))
          -> phi_ajrS ( 'S ( 'S ( 'S ( 'S  'Z))))
             -> View kon_ajrT phi_ajrS (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern ExceptClauseSrcSpanExceptClause_ p_ajrQ p_ajrR = Tag CZ
                                                             (NA_I p_ajrQ :* (NA_I p_ajrR :* NP0))
pattern Tup1ExprSrcSpanMaybeExprSrcSpan_Ifx0 ::
          phi_ajrW ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajrW ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))
             -> View kon_ajrX phi_ajrW (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern Tup1ExprSrcSpanMaybeExprSrcSpan_Ifx0 p_ajrU p_ajrV = Tag CZ
                                                                 (NA_I p_ajrU :* (NA_I p_ajrV :* NP0))
pattern MaybeTup1ExprSrcSpanMaybeTup1ExprSrcSpanMaybeExprSrcSpanNothing_ ::
          View kon_ajrZ phi_ajrY (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeTup1ExprSrcSpanMaybeTup1ExprSrcSpanMaybeExprSrcSpanNothing_ = Tag CZ
                                                                               NP0
pattern MaybeTup1ExprSrcSpanMaybeTup1ExprSrcSpanMaybeExprSrcSpanJust_ ::
          phi_ajs1 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))))
          -> View kon_ajs2 phi_ajs1 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern MaybeTup1ExprSrcSpanMaybeTup1ExprSrcSpanMaybeExprSrcSpanJust_ p_ajs0 = Tag (CS CZ)
                                                                                   (NA_I p_ajs0 :* NP0)
pattern Tup1ExprSrcSpanMaybeTup1ExprSrcSpanMaybeExprSrcSpan_Ifx0 ::
          phi_ajs5 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))
          -> phi_ajs5 ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z)))))))))))))))))))))
             -> View kon_ajs6 phi_ajs5 (Lkup ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S ( 'S  'Z))))))))))))))))))))))))))))))))))))))))))))))))))))) CodesModuleSrcSpan)
pattern Tup1ExprSrcSpanMaybeTup1ExprSrcSpanMaybeExprSrcSpan_Ifx0 p_ajs3 p_ajs4 = Tag CZ
                                                                                     (NA_I p_ajs3 :* (NA_I p_ajs4 :* NP0))
instance Family Singl FamModuleSrcSpan CodesModuleSrcSpan where
  sfrom'
    = \case
        IdxModuleSrcSpan
          -> \case
               El (Module x_ajs7)
                 -> Rep (H (NA_I (El x_ajs7) :* NP0))
        IdxListStatementSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajs8 x_ajs9)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajs8) :* (NA_I (El x_ajs9) :* NP0))))
        IdxStatementSrcSpan
          -> \case
               El (Import x_ajsa x_ajsb)
                 -> Rep
                      (H
                         (NA_I (El x_ajsa) :* (NA_I (El x_ajsb) :* NP0)))
               El (FromImport x_ajsc x_ajsd x_ajse)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajsc)
                               :* (NA_I (El x_ajsd) :* (NA_I (El x_ajse) :* NP0)))))
               El (While x_ajsf x_ajsg x_ajsh x_ajsi)
                 -> Rep
                      (T
                         (T
                            (H
                               (NA_I (El x_ajsf)
                                  :*
                                    (NA_I (El x_ajsg)
                                       :* (NA_I (El x_ajsh) :* (NA_I (El x_ajsi) :* NP0)))))))
               El (For x_ajsj x_ajsk x_ajsl x_ajsm x_ajsn)
                 -> Rep
                      (T
                         (T
                            (T
                               (H
                                  (NA_I (El x_ajsj)
                                     :*
                                       (NA_I (El x_ajsk)
                                          :*
                                            (NA_I (El x_ajsl)
                                               :*
                                                 (NA_I (El x_ajsm)
                                                    :* (NA_I (El x_ajsn) :* NP0)))))))))
               El (AsyncFor x_ajso x_ajsp)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (H
                                     (NA_I (El x_ajso) :* (NA_I (El x_ajsp) :* NP0)))))))
               El (Fun x_ajsq x_ajsr x_ajss x_ajst x_ajsu)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (H
                                        (NA_I (El x_ajsq)
                                           :*
                                             (NA_I (El x_ajsr)
                                                :*
                                                  (NA_I (El x_ajss)
                                                     :*
                                                       (NA_I (El x_ajst)
                                                          :* (NA_I (El x_ajsu) :* NP0)))))))))))
               El (AsyncFun x_ajsv x_ajsw)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (H
                                           (NA_I (El x_ajsv)
                                              :* (NA_I (El x_ajsw) :* NP0)))))))))
               El (Class x_ajsx x_ajsy x_ajsz x_ajsA)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (H
                                              (NA_I (El x_ajsx)
                                                 :*
                                                   (NA_I (El x_ajsy)
                                                      :*
                                                        (NA_I (El x_ajsz)
                                                           :*
                                                             (NA_I (El x_ajsA)
                                                                :* NP0))))))))))))
               El (Conditional x_ajsB x_ajsC x_ajsD)
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
                                                 (NA_I (El x_ajsB)
                                                    :*
                                                      (NA_I (El x_ajsC)
                                                         :* (NA_I (El x_ajsD) :* NP0))))))))))))
               El (Assign x_ajsE x_ajsF x_ajsG)
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
                                                    (NA_I (El x_ajsE)
                                                       :*
                                                         (NA_I (El x_ajsF)
                                                            :*
                                                              (NA_I (El x_ajsG)
                                                                 :* NP0)))))))))))))
               El (AugmentedAssign x_ajsH x_ajsI x_ajsJ x_ajsK)
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
                                                       (NA_I (El x_ajsH)
                                                          :*
                                                            (NA_I (El x_ajsI)
                                                               :*
                                                                 (NA_I (El x_ajsJ)
                                                                    :*
                                                                      (NA_I (El x_ajsK)
                                                                         :* NP0)))))))))))))))
               El (AnnotatedAssign x_ajsL x_ajsM x_ajsN x_ajsO)
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
                                                          (NA_I (El x_ajsL)
                                                             :*
                                                               (NA_I (El x_ajsM)
                                                                  :*
                                                                    (NA_I (El x_ajsN)
                                                                       :*
                                                                         (NA_I (El x_ajsO)
                                                                            :*
                                                                              NP0))))))))))))))))
               El (Decorated x_ajsP x_ajsQ x_ajsR)
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
                                                             (NA_I (El x_ajsP)
                                                                :*
                                                                  (NA_I (El x_ajsQ)
                                                                     :*
                                                                       (NA_I (El x_ajsR)
                                                                          :* NP0))))))))))))))))
               El (Return x_ajsS x_ajsT)
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
                                                                (NA_I (El x_ajsS)
                                                                   :*
                                                                     (NA_I (El x_ajsT)
                                                                        :* NP0))))))))))))))))
               El (Try x_ajsU x_ajsV x_ajsW x_ajsX x_ajsY)
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
                                                                   (NA_I (El x_ajsU)
                                                                      :*
                                                                        (NA_I (El x_ajsV)
                                                                           :*
                                                                             (NA_I (El x_ajsW)
                                                                                :*
                                                                                  (NA_I
                                                                                     (El x_ajsX)
                                                                                     :*
                                                                                       (NA_I
                                                                                          (El
                                                                                             x_ajsY)
                                                                                          :*
                                                                                            NP0))))))))))))))))))))
               El (Raise x_ajsZ x_ajt0)
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
                                                                      (NA_I (El x_ajsZ)
                                                                         :*
                                                                           (NA_I (El x_ajt0)
                                                                              :*
                                                                                NP0))))))))))))))))))
               El (With x_ajt1 x_ajt2 x_ajt3)
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
                                                                   (T
                                                                      (H
                                                                         (NA_I (El x_ajt1)
                                                                            :*
                                                                              (NA_I (El x_ajt2)
                                                                                 :*
                                                                                   (NA_I
                                                                                      (El
                                                                                         x_ajt3)
                                                                                      :*
                                                                                        NP0))))))))))))))))))))
               El (AsyncWith x_ajt4 x_ajt5)
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
                                                                   (T
                                                                      (T
                                                                         (H
                                                                            (NA_I (El x_ajt4)
                                                                               :*
                                                                                 (NA_I
                                                                                    (El x_ajt5)
                                                                                    :*
                                                                                      NP0))))))))))))))))))))
               El (Pass x_ajt6)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (H
                                                                               (NA_I (El x_ajt6)
                                                                                  :*
                                                                                    NP0))))))))))))))))))))
               El (Break x_ajt7)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (H
                                                                                  (NA_I
                                                                                     (El x_ajt7)
                                                                                     :*
                                                                                       NP0)))))))))))))))))))))
               El (Continue x_ajt8)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (T
                                                                                  (H
                                                                                     (NA_I
                                                                                        (El
                                                                                           x_ajt8)
                                                                                        :*
                                                                                          NP0))))))))))))))))))))))
               El (Delete x_ajt9 x_ajta)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (T
                                                                                  (T
                                                                                     (H
                                                                                        (NA_I
                                                                                           (El
                                                                                              x_ajt9)
                                                                                           :*
                                                                                             (NA_I
                                                                                                (El
                                                                                                   x_ajta)
                                                                                                :*
                                                                                                  NP0))))))))))))))))))))))))
               El (StmtExpr x_ajtb x_ajtc)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (T
                                                                                  (T
                                                                                     (T
                                                                                        (H
                                                                                           (NA_I
                                                                                              (El
                                                                                                 x_ajtb)
                                                                                              :*
                                                                                                (NA_I
                                                                                                   (El
                                                                                                      x_ajtc)
                                                                                                   :*
                                                                                                     NP0)))))))))))))))))))))))))
               El (Global x_ajtd x_ajte)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (T
                                                                                  (T
                                                                                     (T
                                                                                        (T
                                                                                           (H
                                                                                              (NA_I
                                                                                                 (El
                                                                                                    x_ajtd)
                                                                                                 :*
                                                                                                   (NA_I
                                                                                                      (El
                                                                                                         x_ajte)
                                                                                                      :*
                                                                                                        NP0))))))))))))))))))))))))))
               El (NonLocal x_ajtf x_ajtg)
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
                                                                                                 (NA_I
                                                                                                    (El
                                                                                                       x_ajtf)
                                                                                                    :*
                                                                                                      (NA_I
                                                                                                         (El
                                                                                                            x_ajtg)
                                                                                                         :*
                                                                                                           NP0)))))))))))))))))))))))))))
               El (Assert x_ajth x_ajti)
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
                                                                                                    (NA_I
                                                                                                       (El
                                                                                                          x_ajth)
                                                                                                       :*
                                                                                                         (NA_I
                                                                                                            (El
                                                                                                               x_ajti)
                                                                                                            :*
                                                                                                              NP0))))))))))))))))))))))))))))
               El (Print x_ajtj x_ajtk x_ajtl x_ajtm)
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
                                                                                                       (NA_K
                                                                                                          (SBool
                                                                                                             x_ajtj)
                                                                                                          :*
                                                                                                            (NA_I
                                                                                                               (El
                                                                                                                  x_ajtk)
                                                                                                               :*
                                                                                                                 (NA_K
                                                                                                                    (SBool
                                                                                                                       x_ajtl)
                                                                                                                    :*
                                                                                                                      (NA_I
                                                                                                                         (El
                                                                                                                            x_ajtm)
                                                                                                                         :*
                                                                                                                           NP0)))))))))))))))))))))))))))))))
               El (Exec x_ajtn x_ajto x_ajtp)
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
                                                                                                          (NA_I
                                                                                                             (El
                                                                                                                x_ajtn)
                                                                                                             :*
                                                                                                               (NA_I
                                                                                                                  (El
                                                                                                                     x_ajto)
                                                                                                                  :*
                                                                                                                    (NA_I
                                                                                                                       (El
                                                                                                                          x_ajtp)
                                                                                                                       :*
                                                                                                                         NP0)))))))))))))))))))))))))))))))
        IdxListImportItemSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajtq x_ajtr)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajtq) :* (NA_I (El x_ajtr) :* NP0))))
        IdxSrcSpan
          -> \case
               El (SpanCoLinear x_ajts x_ajtt x_ajtu x_ajtv)
                 -> Rep
                      (H
                         (NA_K (SString x_ajts)
                            :*
                              (NA_K (SInt x_ajtt)
                                 :* (NA_K (SInt x_ajtu) :* (NA_K (SInt x_ajtv) :* NP0)))))
               El (SpanMultiLine x_ajtw x_ajtx x_ajty x_ajtz x_ajtA)
                 -> Rep
                      (T
                         (H
                            (NA_K (SString x_ajtw)
                               :*
                                 (NA_K (SInt x_ajtx)
                                    :*
                                      (NA_K (SInt x_ajty)
                                         :*
                                           (NA_K (SInt x_ajtz)
                                              :* (NA_K (SInt x_ajtA) :* NP0)))))))
               El (SpanPoint x_ajtB x_ajtC x_ajtD)
                 -> Rep
                      (T
                         (T
                            (H
                               (NA_K (SString x_ajtB)
                                  :* (NA_K (SInt x_ajtC) :* (NA_K (SInt x_ajtD) :* NP0))))))
               El SpanEmpty
                 -> Rep
                      (T
                         (T
                            (T
                               (H NP0))))
        IdxImportRelativeSrcSpan
          -> \case
               El (ImportRelative x_ajtE x_ajtF x_ajtG)
                 -> Rep
                      (H
                         (NA_K (SInt x_ajtE)
                            :* (NA_I (El x_ajtF) :* (NA_I (El x_ajtG) :* NP0))))
        IdxFromItemsSrcSpan
          -> \case
               El (ImportEverything x_ajtH)
                 -> Rep (H (NA_I (El x_ajtH) :* NP0))
               El (FromItems x_ajtI x_ajtJ)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajtI) :* (NA_I (El x_ajtJ) :* NP0))))
        IdxExprSrcSpan
          -> \case
               El (Var x_ajtK x_ajtL)
                 -> Rep
                      (H
                         (NA_I (El x_ajtK) :* (NA_I (El x_ajtL) :* NP0)))
               El (Int x_ajtM x_ajtN x_ajtO)
                 -> Rep
                      (T
                         (H
                            (NA_K (SInteger x_ajtM)
                               :* (NA_K (SString x_ajtN) :* (NA_I (El x_ajtO) :* NP0)))))
               El (LongInt x_ajtP x_ajtQ x_ajtR)
                 -> Rep
                      (T
                         (T
                            (H
                               (NA_K (SInteger x_ajtP)
                                  :* (NA_K (SString x_ajtQ) :* (NA_I (El x_ajtR) :* NP0))))))
               El (Float x_ajtS x_ajtT x_ajtU)
                 -> Rep
                      (T
                         (T
                            (T
                               (H
                                  (NA_K (SDouble x_ajtS)
                                     :*
                                       (NA_K (SString x_ajtT) :* (NA_I (El x_ajtU) :* NP0)))))))
               El (Imaginary x_ajtV x_ajtW x_ajtX)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (H
                                     (NA_K (SDouble x_ajtV)
                                        :*
                                          (NA_K (SString x_ajtW)
                                             :* (NA_I (El x_ajtX) :* NP0))))))))
               El (Bool x_ajtY x_ajtZ)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (H
                                        (NA_K (SBool x_ajtY) :* (NA_I (El x_ajtZ) :* NP0))))))))
               El (None x_aju0)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (H
                                           (NA_I (El x_aju0) :* NP0))))))))
               El (Ellipsis x_aju1)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (H
                                              (NA_I (El x_aju1) :* NP0)))))))))
               El (ByteStrings x_aju2 x_aju3)
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
                                                 (NA_I (El x_aju2)
                                                    :* (NA_I (El x_aju3) :* NP0)))))))))))
               El (Strings x_aju4 x_aju5)
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
                                                    (NA_I (El x_aju4)
                                                       :* (NA_I (El x_aju5) :* NP0))))))))))))
               El (UnicodeStrings x_aju6 x_aju7)
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
                                                       (NA_I (El x_aju6)
                                                          :*
                                                            (NA_I (El x_aju7)
                                                               :* NP0)))))))))))))
               El (Call x_aju8 x_aju9 x_ajua)
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
                                                          (NA_I (El x_aju8)
                                                             :*
                                                               (NA_I (El x_aju9)
                                                                  :*
                                                                    (NA_I (El x_ajua)
                                                                       :* NP0)))))))))))))))
               El (Subscript x_ajub x_ajuc x_ajud)
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
                                                             (NA_I (El x_ajub)
                                                                :*
                                                                  (NA_I (El x_ajuc)
                                                                     :*
                                                                       (NA_I (El x_ajud)
                                                                          :* NP0))))))))))))))))
               El (SlicedExpr x_ajue x_ajuf x_ajug)
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
                                                                (NA_I (El x_ajue)
                                                                   :*
                                                                     (NA_I (El x_ajuf)
                                                                        :*
                                                                          (NA_I (El x_ajug)
                                                                             :*
                                                                               NP0)))))))))))))))))
               El (CondExpr x_ajuh x_ajui x_ajuj x_ajuk)
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
                                                                   (NA_I (El x_ajuh)
                                                                      :*
                                                                        (NA_I (El x_ajui)
                                                                           :*
                                                                             (NA_I (El x_ajuj)
                                                                                :*
                                                                                  (NA_I
                                                                                     (El x_ajuk)
                                                                                     :*
                                                                                       NP0)))))))))))))))))))
               El (BinaryOp x_ajul x_ajum x_ajun x_ajuo)
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
                                                                      (NA_I (El x_ajul)
                                                                         :*
                                                                           (NA_I (El x_ajum)
                                                                              :*
                                                                                (NA_I
                                                                                   (El x_ajun)
                                                                                   :*
                                                                                     (NA_I
                                                                                        (El
                                                                                           x_ajuo)
                                                                                        :*
                                                                                          NP0))))))))))))))))))))
               El (UnaryOp x_ajup x_ajuq x_ajur)
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
                                                                   (T
                                                                      (H
                                                                         (NA_I (El x_ajup)
                                                                            :*
                                                                              (NA_I (El x_ajuq)
                                                                                 :*
                                                                                   (NA_I
                                                                                      (El
                                                                                         x_ajur)
                                                                                      :*
                                                                                        NP0))))))))))))))))))))
               El (Dot x_ajus x_ajut x_ajuu)
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
                                                                   (T
                                                                      (T
                                                                         (H
                                                                            (NA_I (El x_ajus)
                                                                               :*
                                                                                 (NA_I
                                                                                    (El x_ajut)
                                                                                    :*
                                                                                      (NA_I
                                                                                         (El
                                                                                            x_ajuu)
                                                                                         :*
                                                                                           NP0)))))))))))))))))))))
               El (Lambda x_ajuv x_ajuw x_ajux)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (H
                                                                               (NA_I (El x_ajuv)
                                                                                  :*
                                                                                    (NA_I
                                                                                       (El
                                                                                          x_ajuw)
                                                                                       :*
                                                                                         (NA_I
                                                                                            (El
                                                                                               x_ajux)
                                                                                            :*
                                                                                              NP0))))))))))))))))))))))
               El (Tuple x_ajuy x_ajuz)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (H
                                                                                  (NA_I
                                                                                     (El x_ajuy)
                                                                                     :*
                                                                                       (NA_I
                                                                                          (El
                                                                                             x_ajuz)
                                                                                          :*
                                                                                            NP0))))))))))))))))))))))
               El (Yield x_ajuA x_ajuB)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (T
                                                                                  (H
                                                                                     (NA_I
                                                                                        (El
                                                                                           x_ajuA)
                                                                                        :*
                                                                                          (NA_I
                                                                                             (El
                                                                                                x_ajuB)
                                                                                             :*
                                                                                               NP0)))))))))))))))))))))))
               El (Generator x_ajuC x_ajuD)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (T
                                                                                  (T
                                                                                     (H
                                                                                        (NA_I
                                                                                           (El
                                                                                              x_ajuC)
                                                                                           :*
                                                                                             (NA_I
                                                                                                (El
                                                                                                   x_ajuD)
                                                                                                :*
                                                                                                  NP0))))))))))))))))))))))))
               El (Await x_ajuE x_ajuF)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (T
                                                                                  (T
                                                                                     (T
                                                                                        (H
                                                                                           (NA_I
                                                                                              (El
                                                                                                 x_ajuE)
                                                                                              :*
                                                                                                (NA_I
                                                                                                   (El
                                                                                                      x_ajuF)
                                                                                                   :*
                                                                                                     NP0)))))))))))))))))))))))))
               El (ListComp x_ajuG x_ajuH)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (T
                                                                                  (T
                                                                                     (T
                                                                                        (T
                                                                                           (H
                                                                                              (NA_I
                                                                                                 (El
                                                                                                    x_ajuG)
                                                                                                 :*
                                                                                                   (NA_I
                                                                                                      (El
                                                                                                         x_ajuH)
                                                                                                      :*
                                                                                                        NP0))))))))))))))))))))))))))
               El (List x_ajuI x_ajuJ)
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
                                                                                                 (NA_I
                                                                                                    (El
                                                                                                       x_ajuI)
                                                                                                    :*
                                                                                                      (NA_I
                                                                                                         (El
                                                                                                            x_ajuJ)
                                                                                                         :*
                                                                                                           NP0)))))))))))))))))))))))))))
               El (Dictionary x_ajuK x_ajuL)
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
                                                                                                    (NA_I
                                                                                                       (El
                                                                                                          x_ajuK)
                                                                                                       :*
                                                                                                         (NA_I
                                                                                                            (El
                                                                                                               x_ajuL)
                                                                                                            :*
                                                                                                              NP0))))))))))))))))))))))))))))
               El (DictComp x_ajuM x_ajuN)
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
                                                                                                       (NA_I
                                                                                                          (El
                                                                                                             x_ajuM)
                                                                                                          :*
                                                                                                            (NA_I
                                                                                                               (El
                                                                                                                  x_ajuN)
                                                                                                               :*
                                                                                                                 NP0)))))))))))))))))))))))))))))
               El (Set x_ajuO x_ajuP)
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
                                                                                                          (NA_I
                                                                                                             (El
                                                                                                                x_ajuO)
                                                                                                             :*
                                                                                                               (NA_I
                                                                                                                  (El
                                                                                                                     x_ajuP)
                                                                                                                  :*
                                                                                                                    NP0))))))))))))))))))))))))))))))
               El (SetComp x_ajuQ x_ajuR)
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
                                                                                                             (NA_I
                                                                                                                (El
                                                                                                                   x_ajuQ)
                                                                                                                :*
                                                                                                                  (NA_I
                                                                                                                     (El
                                                                                                                        x_ajuR)
                                                                                                                     :*
                                                                                                                       NP0)))))))))))))))))))))))))))))))
               El (Starred x_ajuS x_ajuT)
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
                                                                                                                (NA_I
                                                                                                                   (El
                                                                                                                      x_ajuS)
                                                                                                                   :*
                                                                                                                     (NA_I
                                                                                                                        (El
                                                                                                                           x_ajuT)
                                                                                                                        :*
                                                                                                                          NP0))))))))))))))))))))))))))))))))
               El (Paren x_ajuU x_ajuV)
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
                                                                                                                   (NA_I
                                                                                                                      (El
                                                                                                                         x_ajuU)
                                                                                                                      :*
                                                                                                                        (NA_I
                                                                                                                           (El
                                                                                                                              x_ajuV)
                                                                                                                           :*
                                                                                                                             NP0)))))))))))))))))))))))))))))))))
               El (StringConversion x_ajuW x_ajuX)
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
                                                                                                                (T
                                                                                                                   (H
                                                                                                                      (NA_I
                                                                                                                         (El
                                                                                                                            x_ajuW)
                                                                                                                         :*
                                                                                                                           (NA_I
                                                                                                                              (El
                                                                                                                                 x_ajuX)
                                                                                                                              :*
                                                                                                                                NP0))))))))))))))))))))))))))))))))))
        IdxSuiteSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajuY x_ajuZ)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajuY) :* (NA_I (El x_ajuZ) :* NP0))))
        IdxListExprSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajv0 x_ajv1)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajv0) :* (NA_I (El x_ajv1) :* NP0))))
        IdxIdentSrcSpan
          -> \case
               El (Ident x_ajv2 x_ajv3)
                 -> Rep
                      (H
                         (NA_K (SString x_ajv2) :* (NA_I (El x_ajv3) :* NP0)))
        IdxListParameterSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajv4 x_ajv5)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajv4) :* (NA_I (El x_ajv5) :* NP0))))
        IdxMaybeExprSrcSpan
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_ajv6)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajv6) :* NP0)))
        IdxListArgumentSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajv7 x_ajv8)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajv7) :* (NA_I (El x_ajv8) :* NP0))))
        IdxListTup1ExprSrcSpanSuiteSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajv9 x_ajva)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajv9) :* (NA_I (El x_ajva) :* NP0))))
        IdxAssignOpSrcSpan
          -> \case
               El (PlusAssign x_ajvb)
                 -> Rep (H (NA_I (El x_ajvb) :* NP0))
               El (MinusAssign x_ajvc)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajvc) :* NP0)))
               El (MultAssign x_ajvd)
                 -> Rep
                      (T
                         (T
                            (H (NA_I (El x_ajvd) :* NP0))))
               El (DivAssign x_ajve)
                 -> Rep
                      (T
                         (T
                            (T
                               (H (NA_I (El x_ajve) :* NP0)))))
               El (ModAssign x_ajvf)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (H (NA_I (El x_ajvf) :* NP0))))))
               El (PowAssign x_ajvg)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (H
                                        (NA_I (El x_ajvg) :* NP0)))))))
               El (BinAndAssign x_ajvh)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (H
                                           (NA_I (El x_ajvh) :* NP0))))))))
               El (BinOrAssign x_ajvi)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (H
                                              (NA_I (El x_ajvi) :* NP0)))))))))
               El (BinXorAssign x_ajvj)
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
                                                 (NA_I (El x_ajvj) :* NP0))))))))))
               El (LeftShiftAssign x_ajvk)
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
                                                    (NA_I (El x_ajvk) :* NP0)))))))))))
               El (RightShiftAssign x_ajvl)
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
                                                       (NA_I (El x_ajvl) :* NP0))))))))))))
               El (FloorDivAssign x_ajvm)
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
                                                          (NA_I (El x_ajvm) :* NP0)))))))))))))
               El (MatrixMultAssign x_ajvn)
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
                                                             (NA_I (El x_ajvn)
                                                                :* NP0))))))))))))))
        IdxListDecoratorSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajvo x_ajvp)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajvo) :* (NA_I (El x_ajvp) :* NP0))))
        IdxListHandlerSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajvq x_ajvr)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajvq) :* (NA_I (El x_ajvr) :* NP0))))
        IdxRaiseExprSrcSpan
          -> \case
               El (RaiseV3 x_ajvs)
                 -> Rep (H (NA_I (El x_ajvs) :* NP0))
               El (RaiseV2 x_ajvt)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajvt) :* NP0)))
        IdxListTup1ExprSrcSpanMaybeExprSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajvu x_ajvv)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajvu) :* (NA_I (El x_ajvv) :* NP0))))
        IdxListIdentSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajvw x_ajvx)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajvw) :* (NA_I (El x_ajvx) :* NP0))))
        IdxMaybeTup1ExprSrcSpanMaybeExprSrcSpan
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_ajvy)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajvy) :* NP0)))
        IdxImportItemSrcSpan
          -> \case
               El (ImportItem x_ajvz x_ajvA x_ajvB)
                 -> Rep
                      (H
                         (NA_I (El x_ajvz)
                            :* (NA_I (El x_ajvA) :* (NA_I (El x_ajvB) :* NP0))))
        IdxDottedNameSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajvC x_ajvD)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajvC) :* (NA_I (El x_ajvD) :* NP0))))
        IdxMaybeIdentSrcSpan
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_ajvE)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajvE) :* NP0)))
        IdxMaybeDottedNameSrcSpan
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_ajvF)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajvF) :* NP0)))
        IdxListFromItemSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajvG x_ajvH)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajvG) :* (NA_I (El x_ajvH) :* NP0))))
        IdxFromItemSrcSpan
          -> \case
               El (FromItem x_ajvI x_ajvJ x_ajvK)
                 -> Rep
                      (H
                         (NA_I (El x_ajvI)
                            :* (NA_I (El x_ajvJ) :* (NA_I (El x_ajvK) :* NP0))))
        IdxListString
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajvL x_ajvM)
                 -> Rep
                      (T
                         (H
                            (NA_K (SString x_ajvL) :* (NA_I (El x_ajvM) :* NP0))))
        IdxListSliceSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajvN x_ajvO)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajvN) :* (NA_I (El x_ajvO) :* NP0))))
        IdxOpSrcSpan
          -> \case
               El (And x_ajvP)
                 -> Rep (H (NA_I (El x_ajvP) :* NP0))
               El (Or x_ajvQ)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajvQ) :* NP0)))
               El (Not x_ajvR)
                 -> Rep
                      (T
                         (T
                            (H (NA_I (El x_ajvR) :* NP0))))
               El (Exponent x_ajvS)
                 -> Rep
                      (T
                         (T
                            (T
                               (H (NA_I (El x_ajvS) :* NP0)))))
               El (LessThan x_ajvT)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (H (NA_I (El x_ajvT) :* NP0))))))
               El (GreaterThan x_ajvU)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (H
                                        (NA_I (El x_ajvU) :* NP0)))))))
               El (Equality x_ajvV)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (H
                                           (NA_I (El x_ajvV) :* NP0))))))))
               El (GreaterThanEquals x_ajvW)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (T
                                     (T
                                        (T
                                           (H
                                              (NA_I (El x_ajvW) :* NP0)))))))))
               El (LessThanEquals x_ajvX)
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
                                                 (NA_I (El x_ajvX) :* NP0))))))))))
               El (NotEquals x_ajvY)
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
                                                    (NA_I (El x_ajvY) :* NP0)))))))))))
               El (NotEqualsV2 x_ajvZ)
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
                                                       (NA_I (El x_ajvZ) :* NP0))))))))))))
               El (In x_ajw0)
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
                                                          (NA_I (El x_ajw0) :* NP0)))))))))))))
               El (Is x_ajw1)
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
                                                             (NA_I (El x_ajw1)
                                                                :* NP0))))))))))))))
               El (IsNot x_ajw2)
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
                                                                (NA_I (El x_ajw2)
                                                                   :* NP0)))))))))))))))
               El (NotIn x_ajw3)
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
                                                                   (NA_I (El x_ajw3)
                                                                      :* NP0))))))))))))))))
               El (BinaryOr x_ajw4)
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
                                                                      (NA_I (El x_ajw4)
                                                                         :* NP0)))))))))))))))))
               El (Xor x_ajw5)
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
                                                                   (T
                                                                      (H
                                                                         (NA_I (El x_ajw5)
                                                                            :*
                                                                              NP0))))))))))))))))))
               El (BinaryAnd x_ajw6)
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
                                                                   (T
                                                                      (T
                                                                         (H
                                                                            (NA_I (El x_ajw6)
                                                                               :*
                                                                                 NP0)))))))))))))))))))
               El (ShiftLeft x_ajw7)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (H
                                                                               (NA_I (El x_ajw7)
                                                                                  :*
                                                                                    NP0))))))))))))))))))))
               El (ShiftRight x_ajw8)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (H
                                                                                  (NA_I
                                                                                     (El x_ajw8)
                                                                                     :*
                                                                                       NP0)))))))))))))))))))))
               El (Multiply x_ajw9)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (T
                                                                                  (H
                                                                                     (NA_I
                                                                                        (El
                                                                                           x_ajw9)
                                                                                        :*
                                                                                          NP0))))))))))))))))))))))
               El (Plus x_ajwa)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (T
                                                                                  (T
                                                                                     (H
                                                                                        (NA_I
                                                                                           (El
                                                                                              x_ajwa)
                                                                                           :*
                                                                                             NP0)))))))))))))))))))))))
               El (Minus x_ajwb)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (T
                                                                                  (T
                                                                                     (T
                                                                                        (H
                                                                                           (NA_I
                                                                                              (El
                                                                                                 x_ajwb)
                                                                                              :*
                                                                                                NP0))))))))))))))))))))))))
               El (Divide x_ajwc)
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
                                                                   (T
                                                                      (T
                                                                         (T
                                                                            (T
                                                                               (T
                                                                                  (T
                                                                                     (T
                                                                                        (T
                                                                                           (H
                                                                                              (NA_I
                                                                                                 (El
                                                                                                    x_ajwc)
                                                                                                 :*
                                                                                                   NP0)))))))))))))))))))))))))
               El (FloorDivide x_ajwd)
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
                                                                                                 (NA_I
                                                                                                    (El
                                                                                                       x_ajwd)
                                                                                                    :*
                                                                                                      NP0))))))))))))))))))))))))))
               El (MatrixMult x_ajwe)
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
                                                                                                    (NA_I
                                                                                                       (El
                                                                                                          x_ajwe)
                                                                                                       :*
                                                                                                         NP0)))))))))))))))))))))))))))
               El (Invert x_ajwf)
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
                                                                                                       (NA_I
                                                                                                          (El
                                                                                                             x_ajwf)
                                                                                                          :*
                                                                                                            NP0))))))))))))))))))))))))))))
               El (Modulo x_ajwg)
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
                                                                                                          (NA_I
                                                                                                             (El
                                                                                                                x_ajwg)
                                                                                                             :*
                                                                                                               NP0)))))))))))))))))))))))))))))
        IdxMaybeYieldArgSrcSpan
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_ajwh)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajwh) :* NP0)))
        IdxComprehensionSrcSpan
          -> \case
               El (Comprehension x_ajwi x_ajwj x_ajwk)
                 -> Rep
                      (H
                         (NA_I (El x_ajwi)
                            :* (NA_I (El x_ajwj) :* (NA_I (El x_ajwk) :* NP0))))
        IdxListDictKeyDatumListSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajwl x_ajwm)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajwl) :* (NA_I (El x_ajwm) :* NP0))))
        IdxArgumentSrcSpan
          -> \case
               El (ArgExpr x_ajwn x_ajwo)
                 -> Rep
                      (H
                         (NA_I (El x_ajwn) :* (NA_I (El x_ajwo) :* NP0)))
               El (ArgVarArgsPos x_ajwp x_ajwq)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajwp) :* (NA_I (El x_ajwq) :* NP0))))
               El (ArgVarArgsKeyword x_ajwr x_ajws)
                 -> Rep
                      (T
                         (T
                            (H
                               (NA_I (El x_ajwr) :* (NA_I (El x_ajws) :* NP0)))))
               El (ArgKeyword x_ajwt x_ajwu x_ajwv)
                 -> Rep
                      (T
                         (T
                            (T
                               (H
                                  (NA_I (El x_ajwt)
                                     :* (NA_I (El x_ajwu) :* (NA_I (El x_ajwv) :* NP0)))))))
        IdxSliceSrcSpan
          -> \case
               El (SliceProper x_ajww x_ajwx x_ajwy x_ajwz)
                 -> Rep
                      (H
                         (NA_I (El x_ajww)
                            :*
                              (NA_I (El x_ajwx)
                                 :* (NA_I (El x_ajwy) :* (NA_I (El x_ajwz) :* NP0)))))
               El (SliceExpr x_ajwA x_ajwB)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajwA) :* (NA_I (El x_ajwB) :* NP0))))
               El (SliceEllipsis x_ajwC)
                 -> Rep
                      (T
                         (T
                            (H (NA_I (El x_ajwC) :* NP0))))
        IdxMaybeMaybeExprSrcSpan
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_ajwD)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajwD) :* NP0)))
        IdxParameterSrcSpan
          -> \case
               El (Param x_ajwE x_ajwF x_ajwG x_ajwH)
                 -> Rep
                      (H
                         (NA_I (El x_ajwE)
                            :*
                              (NA_I (El x_ajwF)
                                 :* (NA_I (El x_ajwG) :* (NA_I (El x_ajwH) :* NP0)))))
               El (VarArgsPos x_ajwI x_ajwJ x_ajwK)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajwI)
                               :* (NA_I (El x_ajwJ) :* (NA_I (El x_ajwK) :* NP0)))))
               El (VarArgsKeyword x_ajwL x_ajwM x_ajwN)
                 -> Rep
                      (T
                         (T
                            (H
                               (NA_I (El x_ajwL)
                                  :* (NA_I (El x_ajwM) :* (NA_I (El x_ajwN) :* NP0))))))
               El (EndPositional x_ajwO)
                 -> Rep
                      (T
                         (T
                            (T
                               (H (NA_I (El x_ajwO) :* NP0)))))
               El (UnPackTuple x_ajwP x_ajwQ x_ajwR)
                 -> Rep
                      (T
                         (T
                            (T
                               (T
                                  (H
                                     (NA_I (El x_ajwP)
                                        :* (NA_I (El x_ajwQ) :* (NA_I (El x_ajwR) :* NP0))))))))
        IdxParamTupleSrcSpan
          -> \case
               El (ParamTupleName x_ajwS x_ajwT)
                 -> Rep
                      (H
                         (NA_I (El x_ajwS) :* (NA_I (El x_ajwT) :* NP0)))
               El (ParamTuple x_ajwU x_ajwV)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajwU) :* (NA_I (El x_ajwV) :* NP0))))
        IdxListParamTupleSrcSpan
          -> \case
               El [] -> Rep (H NP0)
               El ((:) x_ajwW x_ajwX)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajwW) :* (NA_I (El x_ajwX) :* NP0))))
        IdxYieldArgSrcSpan
          -> \case
               El (YieldFrom x_ajwY x_ajwZ)
                 -> Rep
                      (H
                         (NA_I (El x_ajwY) :* (NA_I (El x_ajwZ) :* NP0)))
               El (YieldExpr x_ajx0)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajx0) :* NP0)))
        IdxComprehensionExprSrcSpan
          -> \case
               El (ComprehensionExpr x_ajx1)
                 -> Rep (H (NA_I (El x_ajx1) :* NP0))
               El (ComprehensionDict x_ajx2)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajx2) :* NP0)))
        IdxCompForSrcSpan
          -> \case
               El (CompFor x_ajx3 x_ajx4 x_ajx5 x_ajx6 x_ajx7)
                 -> Rep
                      (H
                         (NA_K (SBool x_ajx3)
                            :*
                              (NA_I (El x_ajx4)
                                 :*
                                   (NA_I (El x_ajx5)
                                      :* (NA_I (El x_ajx6) :* (NA_I (El x_ajx7) :* NP0))))))
        IdxDictKeyDatumListSrcSpan
          -> \case
               El (DictMappingPair x_ajx8 x_ajx9)
                 -> Rep
                      (H
                         (NA_I (El x_ajx8) :* (NA_I (El x_ajx9) :* NP0)))
               El (DictUnpacking x_ajxa)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajxa) :* NP0)))
        IdxMaybeCompIterSrcSpan
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_ajxb)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajxb) :* NP0)))
        IdxCompIterSrcSpan
          -> \case
               El (IterFor x_ajxc x_ajxd)
                 -> Rep
                      (H
                         (NA_I (El x_ajxc) :* (NA_I (El x_ajxd) :* NP0)))
               El (IterIf x_ajxe x_ajxf)
                 -> Rep
                      (T
                         (H
                            (NA_I (El x_ajxe) :* (NA_I (El x_ajxf) :* NP0))))
        IdxCompIfSrcSpan
          -> \case
               El (CompIf x_ajxg x_ajxh x_ajxi)
                 -> Rep
                      (H
                         (NA_I (El x_ajxg)
                            :* (NA_I (El x_ajxh) :* (NA_I (El x_ajxi) :* NP0))))
        IdxTup1ExprSrcSpanSuiteSrcSpan
          -> \case
               El ((,) x_ajxj x_ajxk)
                 -> Rep
                      (H
                         (NA_I (El x_ajxj) :* (NA_I (El x_ajxk) :* NP0)))
        IdxDecoratorSrcSpan
          -> \case
               El (Decorator x_ajxl x_ajxm x_ajxn)
                 -> Rep
                      (H
                         (NA_I (El x_ajxl)
                            :* (NA_I (El x_ajxm) :* (NA_I (El x_ajxn) :* NP0))))
        IdxHandlerSrcSpan
          -> \case
               El (Handler x_ajxo x_ajxp x_ajxq)
                 -> Rep
                      (H
                         (NA_I (El x_ajxo)
                            :* (NA_I (El x_ajxp) :* (NA_I (El x_ajxq) :* NP0))))
        IdxExceptClauseSrcSpan
          -> \case
               El (ExceptClause x_ajxr x_ajxs)
                 -> Rep
                      (H
                         (NA_I (El x_ajxr) :* (NA_I (El x_ajxs) :* NP0)))
        IdxTup1ExprSrcSpanMaybeExprSrcSpan
          -> \case
               El ((,) x_ajxt x_ajxu)
                 -> Rep
                      (H
                         (NA_I (El x_ajxt) :* (NA_I (El x_ajxu) :* NP0)))
        IdxMaybeTup1ExprSrcSpanMaybeTup1ExprSrcSpanMaybeExprSrcSpan
          -> \case
               El Nothing -> Rep (H NP0)
               El (Just x_ajxv)
                 -> Rep
                      (T
                         (H (NA_I (El x_ajxv) :* NP0)))
        IdxTup1ExprSrcSpanMaybeTup1ExprSrcSpanMaybeExprSrcSpan
          -> \case
               El ((,) x_ajxw x_ajxx)
                 -> Rep
                      (H
                         (NA_I (El x_ajxw) :* (NA_I (El x_ajxx) :* NP0)))
  sto'
    = \case
        IdxModuleSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajxy) :* NP0))
                 -> El (Module y_ajxy)
        IdxListStatementSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajxz) :* (NA_I (El y_ajxA) :* NP0))))
                 -> El (((:) y_ajxz) y_ajxA)
        IdxStatementSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajxB) :* (NA_I (El y_ajxC) :* NP0)))
                 -> El ((Import y_ajxB) y_ajxC)
               Rep (T (H (NA_I (El y_ajxD) :* (NA_I (El y_ajxE) :* (NA_I (El y_ajxF) :* NP0)))))
                 -> El (((FromImport y_ajxD) y_ajxE) y_ajxF)
               Rep (T (T (H (NA_I (El y_ajxG) :* (NA_I (El y_ajxH) :* (NA_I (El y_ajxI) :* (NA_I (El y_ajxJ) :* NP0)))))))
                 -> El ((((While y_ajxG) y_ajxH) y_ajxI) y_ajxJ)
               Rep (T (T (T (H (NA_I (El y_ajxK) :* (NA_I (El y_ajxL) :* (NA_I (El y_ajxM) :* (NA_I (El y_ajxN) :* (NA_I (El y_ajxO) :* NP0)))))))))
                 -> El (((((For y_ajxK) y_ajxL) y_ajxM) y_ajxN) y_ajxO)
               Rep (T (T (T (T (H (NA_I (El y_ajxP) :* (NA_I (El y_ajxQ) :* NP0)))))))
                 -> El ((AsyncFor y_ajxP) y_ajxQ)
               Rep (T (T (T (T (T (H (NA_I (El y_ajxR) :* (NA_I (El y_ajxS) :* (NA_I (El y_ajxT) :* (NA_I (El y_ajxU) :* (NA_I (El y_ajxV) :* NP0)))))))))))
                 -> El (((((Fun y_ajxR) y_ajxS) y_ajxT) y_ajxU) y_ajxV)
               Rep (T (T (T (T (T (T (H (NA_I (El y_ajxW) :* (NA_I (El y_ajxX) :* NP0)))))))))
                 -> El ((AsyncFun y_ajxW) y_ajxX)
               Rep (T (T (T (T (T (T (T (H (NA_I (El y_ajxY) :* (NA_I (El y_ajxZ) :* (NA_I (El y_ajy0) :* (NA_I (El y_ajy1) :* NP0))))))))))))
                 -> El ((((Class y_ajxY) y_ajxZ) y_ajy0) y_ajy1)
               Rep (T (T (T (T (T (T (T (T (H (NA_I (El y_ajy2) :* (NA_I (El y_ajy3) :* (NA_I (El y_ajy4) :* NP0))))))))))))
                 -> El (((Conditional y_ajy2) y_ajy3) y_ajy4)
               Rep (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajy5) :* (NA_I (El y_ajy6) :* (NA_I (El y_ajy7) :* NP0)))))))))))))
                 -> El (((Assign y_ajy5) y_ajy6) y_ajy7)
               Rep (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajy8) :* (NA_I (El y_ajy9) :* (NA_I (El y_ajya) :* (NA_I (El y_ajyb) :* NP0)))))))))))))))
                 -> El ((((AugmentedAssign y_ajy8) y_ajy9) y_ajya) y_ajyb)
               Rep (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyc) :* (NA_I (El y_ajyd) :* (NA_I (El y_ajye) :* (NA_I (El y_ajyf) :* NP0))))))))))))))))
                 -> El ((((AnnotatedAssign y_ajyc) y_ajyd) y_ajye) y_ajyf)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyg) :* (NA_I (El y_ajyh) :* (NA_I (El y_ajyi) :* NP0))))))))))))))))
                 -> El (((Decorated y_ajyg) y_ajyh) y_ajyi)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyj) :* (NA_I (El y_ajyk) :* NP0))))))))))))))))
                 -> El ((Return y_ajyj) y_ajyk)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyl) :* (NA_I (El y_ajym) :* (NA_I (El y_ajyn) :* (NA_I (El y_ajyo) :* (NA_I (El y_ajyp) :* NP0))))))))))))))))))))
                 -> El (((((Try y_ajyl) y_ajym) y_ajyn) y_ajyo) y_ajyp)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyq) :* (NA_I (El y_ajyr) :* NP0))))))))))))))))))
                 -> El ((Raise y_ajyq) y_ajyr)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajys) :* (NA_I (El y_ajyt) :* (NA_I (El y_ajyu) :* NP0))))))))))))))))))))
                 -> El (((With y_ajys) y_ajyt) y_ajyu)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyv) :* (NA_I (El y_ajyw) :* NP0))))))))))))))))))))
                 -> El ((AsyncWith y_ajyv) y_ajyw)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyx) :* NP0))))))))))))))))))))
                 -> El (Pass y_ajyx)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyy) :* NP0)))))))))))))))))))))
                 -> El (Break y_ajyy)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyz) :* NP0))))))))))))))))))))))
                 -> El (Continue y_ajyz)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyA) :* (NA_I (El y_ajyB) :* NP0))))))))))))))))))))))))
                 -> El ((Delete y_ajyA) y_ajyB)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyC) :* (NA_I (El y_ajyD) :* NP0)))))))))))))))))))))))))
                 -> El ((StmtExpr y_ajyC) y_ajyD)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyE) :* (NA_I (El y_ajyF) :* NP0))))))))))))))))))))))))))
                 -> El ((Global y_ajyE) y_ajyF)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyG) :* (NA_I (El y_ajyH) :* NP0)))))))))))))))))))))))))))
                 -> El ((NonLocal y_ajyG) y_ajyH)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyI) :* (NA_I (El y_ajyJ) :* NP0))))))))))))))))))))))))))))
                 -> El ((Assert y_ajyI) y_ajyJ)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_K (SBool y_ajyK) :* (NA_I (El y_ajyL) :* (NA_K (SBool y_ajyM) :* (NA_I (El y_ajyN) :* NP0)))))))))))))))))))))))))))))))
                 -> El ((((Print y_ajyK) y_ajyL) y_ajyM) y_ajyN)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajyO) :* (NA_I (El y_ajyP) :* (NA_I (El y_ajyQ) :* NP0)))))))))))))))))))))))))))))))
                 -> El (((Exec y_ajyO) y_ajyP) y_ajyQ)
        IdxListImportItemSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajyR) :* (NA_I (El y_ajyS) :* NP0))))
                 -> El (((:) y_ajyR) y_ajyS)
        IdxSrcSpan
          -> \case
               Rep (H (NA_K (SString y_ajyT) :* (NA_K (SInt y_ajyU) :* (NA_K (SInt y_ajyV) :* (NA_K (SInt y_ajyW) :* NP0)))))
                 -> El ((((SpanCoLinear y_ajyT) y_ajyU) y_ajyV) y_ajyW)
               Rep (T (H (NA_K (SString y_ajyX) :* (NA_K (SInt y_ajyY) :* (NA_K (SInt y_ajyZ) :* (NA_K (SInt y_ajz0) :* (NA_K (SInt y_ajz1) :* NP0)))))))
                 -> El (((((SpanMultiLine y_ajyX) y_ajyY) y_ajyZ) y_ajz0) y_ajz1)
               Rep (T (T (H (NA_K (SString y_ajz2) :* (NA_K (SInt y_ajz3) :* (NA_K (SInt y_ajz4) :* NP0))))))
                 -> El (((SpanPoint y_ajz2) y_ajz3) y_ajz4)
               Rep (T (T (T (H NP0))))
                 -> El SpanEmpty
        IdxImportRelativeSrcSpan
          -> \case
               Rep (H (NA_K (SInt y_ajz5) :* (NA_I (El y_ajz6) :* (NA_I (El y_ajz7) :* NP0))))
                 -> El (((ImportRelative y_ajz5) y_ajz6) y_ajz7)
        IdxFromItemsSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajz8) :* NP0))
                 -> El (ImportEverything y_ajz8)
               Rep (T (H (NA_I (El y_ajz9) :* (NA_I (El y_ajza) :* NP0))))
                 -> El ((FromItems y_ajz9) y_ajza)
        IdxExprSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajzb) :* (NA_I (El y_ajzc) :* NP0)))
                 -> El ((Var y_ajzb) y_ajzc)
               Rep (T (H (NA_K (SInteger y_ajzd) :* (NA_K (SString y_ajze) :* (NA_I (El y_ajzf) :* NP0)))))
                 -> El (((Int y_ajzd) y_ajze) y_ajzf)
               Rep (T (T (H (NA_K (SInteger y_ajzg) :* (NA_K (SString y_ajzh) :* (NA_I (El y_ajzi) :* NP0))))))
                 -> El (((LongInt y_ajzg) y_ajzh) y_ajzi)
               Rep (T (T (T (H (NA_K (SDouble y_ajzj) :* (NA_K (SString y_ajzk) :* (NA_I (El y_ajzl) :* NP0)))))))
                 -> El (((Float y_ajzj) y_ajzk) y_ajzl)
               Rep (T (T (T (T (H (NA_K (SDouble y_ajzm) :* (NA_K (SString y_ajzn) :* (NA_I (El y_ajzo) :* NP0))))))))
                 -> El (((Imaginary y_ajzm) y_ajzn) y_ajzo)
               Rep (T (T (T (T (T (H (NA_K (SBool y_ajzp) :* (NA_I (El y_ajzq) :* NP0))))))))
                 -> El ((Bool y_ajzp) y_ajzq)
               Rep (T (T (T (T (T (T (H (NA_I (El y_ajzr) :* NP0))))))))
                 -> El (None y_ajzr)
               Rep (T (T (T (T (T (T (T (H (NA_I (El y_ajzs) :* NP0)))))))))
                 -> El (Ellipsis y_ajzs)
               Rep (T (T (T (T (T (T (T (T (H (NA_I (El y_ajzt) :* (NA_I (El y_ajzu) :* NP0)))))))))))
                 -> El ((ByteStrings y_ajzt) y_ajzu)
               Rep (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajzv) :* (NA_I (El y_ajzw) :* NP0))))))))))))
                 -> El ((Strings y_ajzv) y_ajzw)
               Rep (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajzx) :* (NA_I (El y_ajzy) :* NP0)))))))))))))
                 -> El ((UnicodeStrings y_ajzx) y_ajzy)
               Rep (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajzz) :* (NA_I (El y_ajzA) :* (NA_I (El y_ajzB) :* NP0)))))))))))))))
                 -> El (((Call y_ajzz) y_ajzA) y_ajzB)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajzC) :* (NA_I (El y_ajzD) :* (NA_I (El y_ajzE) :* NP0))))))))))))))))
                 -> El (((Subscript y_ajzC) y_ajzD) y_ajzE)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajzF) :* (NA_I (El y_ajzG) :* (NA_I (El y_ajzH) :* NP0)))))))))))))))))
                 -> El (((SlicedExpr y_ajzF) y_ajzG) y_ajzH)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajzI) :* (NA_I (El y_ajzJ) :* (NA_I (El y_ajzK) :* (NA_I (El y_ajzL) :* NP0)))))))))))))))))))
                 -> El ((((CondExpr y_ajzI) y_ajzJ) y_ajzK) y_ajzL)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajzM) :* (NA_I (El y_ajzN) :* (NA_I (El y_ajzO) :* (NA_I (El y_ajzP) :* NP0))))))))))))))))))))
                 -> El ((((BinaryOp y_ajzM) y_ajzN) y_ajzO) y_ajzP)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajzQ) :* (NA_I (El y_ajzR) :* (NA_I (El y_ajzS) :* NP0))))))))))))))))))))
                 -> El (((UnaryOp y_ajzQ) y_ajzR) y_ajzS)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajzT) :* (NA_I (El y_ajzU) :* (NA_I (El y_ajzV) :* NP0)))))))))))))))))))))
                 -> El (((Dot y_ajzT) y_ajzU) y_ajzV)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajzW) :* (NA_I (El y_ajzX) :* (NA_I (El y_ajzY) :* NP0))))))))))))))))))))))
                 -> El (((Lambda y_ajzW) y_ajzX) y_ajzY)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajzZ) :* (NA_I (El y_ajA0) :* NP0))))))))))))))))))))))
                 -> El ((Tuple y_ajzZ) y_ajA0)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajA1) :* (NA_I (El y_ajA2) :* NP0)))))))))))))))))))))))
                 -> El ((Yield y_ajA1) y_ajA2)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajA3) :* (NA_I (El y_ajA4) :* NP0))))))))))))))))))))))))
                 -> El ((Generator y_ajA3) y_ajA4)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajA5) :* (NA_I (El y_ajA6) :* NP0)))))))))))))))))))))))))
                 -> El ((Await y_ajA5) y_ajA6)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajA7) :* (NA_I (El y_ajA8) :* NP0))))))))))))))))))))))))))
                 -> El ((ListComp y_ajA7) y_ajA8)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajA9) :* (NA_I (El y_ajAa) :* NP0)))))))))))))))))))))))))))
                 -> El ((List y_ajA9) y_ajAa)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajAb) :* (NA_I (El y_ajAc) :* NP0))))))))))))))))))))))))))))
                 -> El ((Dictionary y_ajAb) y_ajAc)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajAd) :* (NA_I (El y_ajAe) :* NP0)))))))))))))))))))))))))))))
                 -> El ((DictComp y_ajAd) y_ajAe)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajAf) :* (NA_I (El y_ajAg) :* NP0))))))))))))))))))))))))))))))
                 -> El ((Set y_ajAf) y_ajAg)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajAh) :* (NA_I (El y_ajAi) :* NP0)))))))))))))))))))))))))))))))
                 -> El ((SetComp y_ajAh) y_ajAi)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajAj) :* (NA_I (El y_ajAk) :* NP0))))))))))))))))))))))))))))))))
                 -> El ((Starred y_ajAj) y_ajAk)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajAl) :* (NA_I (El y_ajAm) :* NP0)))))))))))))))))))))))))))))))))
                 -> El ((Paren y_ajAl) y_ajAm)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajAn) :* (NA_I (El y_ajAo) :* NP0))))))))))))))))))))))))))))))))))
                 -> El ((StringConversion y_ajAn) y_ajAo)
        IdxSuiteSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajAp) :* (NA_I (El y_ajAq) :* NP0))))
                 -> El (((:) y_ajAp) y_ajAq)
        IdxListExprSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajAr) :* (NA_I (El y_ajAs) :* NP0))))
                 -> El (((:) y_ajAr) y_ajAs)
        IdxIdentSrcSpan
          -> \case
               Rep (H (NA_K (SString y_ajAt) :* (NA_I (El y_ajAu) :* NP0)))
                 -> El ((Ident y_ajAt) y_ajAu)
        IdxListParameterSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajAv) :* (NA_I (El y_ajAw) :* NP0))))
                 -> El (((:) y_ajAv) y_ajAw)
        IdxMaybeExprSrcSpan
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_ajAx) :* NP0)))
                 -> El (Just y_ajAx)
        IdxListArgumentSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajAy) :* (NA_I (El y_ajAz) :* NP0))))
                 -> El (((:) y_ajAy) y_ajAz)
        IdxListTup1ExprSrcSpanSuiteSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajAA) :* (NA_I (El y_ajAB) :* NP0))))
                 -> El (((:) y_ajAA) y_ajAB)
        IdxAssignOpSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajAC) :* NP0))
                 -> El (PlusAssign y_ajAC)
               Rep (T (H (NA_I (El y_ajAD) :* NP0)))
                 -> El (MinusAssign y_ajAD)
               Rep (T (T (H (NA_I (El y_ajAE) :* NP0))))
                 -> El (MultAssign y_ajAE)
               Rep (T (T (T (H (NA_I (El y_ajAF) :* NP0)))))
                 -> El (DivAssign y_ajAF)
               Rep (T (T (T (T (H (NA_I (El y_ajAG) :* NP0))))))
                 -> El (ModAssign y_ajAG)
               Rep (T (T (T (T (T (H (NA_I (El y_ajAH) :* NP0)))))))
                 -> El (PowAssign y_ajAH)
               Rep (T (T (T (T (T (T (H (NA_I (El y_ajAI) :* NP0))))))))
                 -> El (BinAndAssign y_ajAI)
               Rep (T (T (T (T (T (T (T (H (NA_I (El y_ajAJ) :* NP0)))))))))
                 -> El (BinOrAssign y_ajAJ)
               Rep (T (T (T (T (T (T (T (T (H (NA_I (El y_ajAK) :* NP0))))))))))
                 -> El (BinXorAssign y_ajAK)
               Rep (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajAL) :* NP0)))))))))))
                 -> El (LeftShiftAssign y_ajAL)
               Rep (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajAM) :* NP0))))))))))))
                 -> El (RightShiftAssign y_ajAM)
               Rep (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajAN) :* NP0)))))))))))))
                 -> El (FloorDivAssign y_ajAN)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajAO) :* NP0))))))))))))))
                 -> El (MatrixMultAssign y_ajAO)
        IdxListDecoratorSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajAP) :* (NA_I (El y_ajAQ) :* NP0))))
                 -> El (((:) y_ajAP) y_ajAQ)
        IdxListHandlerSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajAR) :* (NA_I (El y_ajAS) :* NP0))))
                 -> El (((:) y_ajAR) y_ajAS)
        IdxRaiseExprSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajAT) :* NP0))
                 -> El (RaiseV3 y_ajAT)
               Rep (T (H (NA_I (El y_ajAU) :* NP0)))
                 -> El (RaiseV2 y_ajAU)
        IdxListTup1ExprSrcSpanMaybeExprSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajAV) :* (NA_I (El y_ajAW) :* NP0))))
                 -> El (((:) y_ajAV) y_ajAW)
        IdxListIdentSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajAX) :* (NA_I (El y_ajAY) :* NP0))))
                 -> El (((:) y_ajAX) y_ajAY)
        IdxMaybeTup1ExprSrcSpanMaybeExprSrcSpan
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_ajAZ) :* NP0)))
                 -> El (Just y_ajAZ)
        IdxImportItemSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajB0) :* (NA_I (El y_ajB1) :* (NA_I (El y_ajB2) :* NP0))))
                 -> El (((ImportItem y_ajB0) y_ajB1) y_ajB2)
        IdxDottedNameSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajB3) :* (NA_I (El y_ajB4) :* NP0))))
                 -> El (((:) y_ajB3) y_ajB4)
        IdxMaybeIdentSrcSpan
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_ajB5) :* NP0)))
                 -> El (Just y_ajB5)
        IdxMaybeDottedNameSrcSpan
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_ajB6) :* NP0)))
                 -> El (Just y_ajB6)
        IdxListFromItemSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajB7) :* (NA_I (El y_ajB8) :* NP0))))
                 -> El (((:) y_ajB7) y_ajB8)
        IdxFromItemSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajB9) :* (NA_I (El y_ajBa) :* (NA_I (El y_ajBb) :* NP0))))
                 -> El (((FromItem y_ajB9) y_ajBa) y_ajBb)
        IdxListString
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_K (SString y_ajBc) :* (NA_I (El y_ajBd) :* NP0))))
                 -> El (((:) y_ajBc) y_ajBd)
        IdxListSliceSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajBe) :* (NA_I (El y_ajBf) :* NP0))))
                 -> El (((:) y_ajBe) y_ajBf)
        IdxOpSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajBg) :* NP0))
                 -> El (And y_ajBg)
               Rep (T (H (NA_I (El y_ajBh) :* NP0)))
                 -> El (Or y_ajBh)
               Rep (T (T (H (NA_I (El y_ajBi) :* NP0))))
                 -> El (Not y_ajBi)
               Rep (T (T (T (H (NA_I (El y_ajBj) :* NP0)))))
                 -> El (Exponent y_ajBj)
               Rep (T (T (T (T (H (NA_I (El y_ajBk) :* NP0))))))
                 -> El (LessThan y_ajBk)
               Rep (T (T (T (T (T (H (NA_I (El y_ajBl) :* NP0)))))))
                 -> El (GreaterThan y_ajBl)
               Rep (T (T (T (T (T (T (H (NA_I (El y_ajBm) :* NP0))))))))
                 -> El (Equality y_ajBm)
               Rep (T (T (T (T (T (T (T (H (NA_I (El y_ajBn) :* NP0)))))))))
                 -> El (GreaterThanEquals y_ajBn)
               Rep (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBo) :* NP0))))))))))
                 -> El (LessThanEquals y_ajBo)
               Rep (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBp) :* NP0)))))))))))
                 -> El (NotEquals y_ajBp)
               Rep (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBq) :* NP0))))))))))))
                 -> El (NotEqualsV2 y_ajBq)
               Rep (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBr) :* NP0)))))))))))))
                 -> El (In y_ajBr)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBs) :* NP0))))))))))))))
                 -> El (Is y_ajBs)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBt) :* NP0)))))))))))))))
                 -> El (IsNot y_ajBt)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBu) :* NP0))))))))))))))))
                 -> El (NotIn y_ajBu)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBv) :* NP0)))))))))))))))))
                 -> El (BinaryOr y_ajBv)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBw) :* NP0))))))))))))))))))
                 -> El (Xor y_ajBw)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBx) :* NP0)))))))))))))))))))
                 -> El (BinaryAnd y_ajBx)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBy) :* NP0))))))))))))))))))))
                 -> El (ShiftLeft y_ajBy)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBz) :* NP0)))))))))))))))))))))
                 -> El (ShiftRight y_ajBz)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBA) :* NP0))))))))))))))))))))))
                 -> El (Multiply y_ajBA)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBB) :* NP0)))))))))))))))))))))))
                 -> El (Plus y_ajBB)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBC) :* NP0))))))))))))))))))))))))
                 -> El (Minus y_ajBC)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBD) :* NP0)))))))))))))))))))))))))
                 -> El (Divide y_ajBD)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBE) :* NP0))))))))))))))))))))))))))
                 -> El (FloorDivide y_ajBE)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBF) :* NP0)))))))))))))))))))))))))))
                 -> El (MatrixMult y_ajBF)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBG) :* NP0))))))))))))))))))))))))))))
                 -> El (Invert y_ajBG)
               Rep (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (H (NA_I (El y_ajBH) :* NP0)))))))))))))))))))))))))))))
                 -> El (Modulo y_ajBH)
        IdxMaybeYieldArgSrcSpan
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_ajBI) :* NP0)))
                 -> El (Just y_ajBI)
        IdxComprehensionSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajBJ) :* (NA_I (El y_ajBK) :* (NA_I (El y_ajBL) :* NP0))))
                 -> El (((Comprehension y_ajBJ) y_ajBK) y_ajBL)
        IdxListDictKeyDatumListSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajBM) :* (NA_I (El y_ajBN) :* NP0))))
                 -> El (((:) y_ajBM) y_ajBN)
        IdxArgumentSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajBO) :* (NA_I (El y_ajBP) :* NP0)))
                 -> El ((ArgExpr y_ajBO) y_ajBP)
               Rep (T (H (NA_I (El y_ajBQ) :* (NA_I (El y_ajBR) :* NP0))))
                 -> El ((ArgVarArgsPos y_ajBQ) y_ajBR)
               Rep (T (T (H (NA_I (El y_ajBS) :* (NA_I (El y_ajBT) :* NP0)))))
                 -> El ((ArgVarArgsKeyword y_ajBS) y_ajBT)
               Rep (T (T (T (H (NA_I (El y_ajBU) :* (NA_I (El y_ajBV) :* (NA_I (El y_ajBW) :* NP0)))))))
                 -> El (((ArgKeyword y_ajBU) y_ajBV) y_ajBW)
        IdxSliceSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajBX) :* (NA_I (El y_ajBY) :* (NA_I (El y_ajBZ) :* (NA_I (El y_ajC0) :* NP0)))))
                 -> El ((((SliceProper y_ajBX) y_ajBY) y_ajBZ) y_ajC0)
               Rep (T (H (NA_I (El y_ajC1) :* (NA_I (El y_ajC2) :* NP0))))
                 -> El ((SliceExpr y_ajC1) y_ajC2)
               Rep (T (T (H (NA_I (El y_ajC3) :* NP0))))
                 -> El (SliceEllipsis y_ajC3)
        IdxMaybeMaybeExprSrcSpan
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_ajC4) :* NP0)))
                 -> El (Just y_ajC4)
        IdxParameterSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajC5) :* (NA_I (El y_ajC6) :* (NA_I (El y_ajC7) :* (NA_I (El y_ajC8) :* NP0)))))
                 -> El ((((Param y_ajC5) y_ajC6) y_ajC7) y_ajC8)
               Rep (T (H (NA_I (El y_ajC9) :* (NA_I (El y_ajCa) :* (NA_I (El y_ajCb) :* NP0)))))
                 -> El (((VarArgsPos y_ajC9) y_ajCa) y_ajCb)
               Rep (T (T (H (NA_I (El y_ajCc) :* (NA_I (El y_ajCd) :* (NA_I (El y_ajCe) :* NP0))))))
                 -> El (((VarArgsKeyword y_ajCc) y_ajCd) y_ajCe)
               Rep (T (T (T (H (NA_I (El y_ajCf) :* NP0)))))
                 -> El (EndPositional y_ajCf)
               Rep (T (T (T (T (H (NA_I (El y_ajCg) :* (NA_I (El y_ajCh) :* (NA_I (El y_ajCi) :* NP0))))))))
                 -> El (((UnPackTuple y_ajCg) y_ajCh) y_ajCi)
        IdxParamTupleSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajCj) :* (NA_I (El y_ajCk) :* NP0)))
                 -> El ((ParamTupleName y_ajCj) y_ajCk)
               Rep (T (H (NA_I (El y_ajCl) :* (NA_I (El y_ajCm) :* NP0))))
                 -> El ((ParamTuple y_ajCl) y_ajCm)
        IdxListParamTupleSrcSpan
          -> \case
               Rep (H NP0) -> El []
               Rep (T (H (NA_I (El y_ajCn) :* (NA_I (El y_ajCo) :* NP0))))
                 -> El (((:) y_ajCn) y_ajCo)
        IdxYieldArgSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajCp) :* (NA_I (El y_ajCq) :* NP0)))
                 -> El ((YieldFrom y_ajCp) y_ajCq)
               Rep (T (H (NA_I (El y_ajCr) :* NP0)))
                 -> El (YieldExpr y_ajCr)
        IdxComprehensionExprSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajCs) :* NP0))
                 -> El (ComprehensionExpr y_ajCs)
               Rep (T (H (NA_I (El y_ajCt) :* NP0)))
                 -> El (ComprehensionDict y_ajCt)
        IdxCompForSrcSpan
          -> \case
               Rep (H (NA_K (SBool y_ajCu) :* (NA_I (El y_ajCv) :* (NA_I (El y_ajCw) :* (NA_I (El y_ajCx) :* (NA_I (El y_ajCy) :* NP0))))))
                 -> El (((((CompFor y_ajCu) y_ajCv) y_ajCw) y_ajCx) y_ajCy)
        IdxDictKeyDatumListSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajCz) :* (NA_I (El y_ajCA) :* NP0)))
                 -> El ((DictMappingPair y_ajCz) y_ajCA)
               Rep (T (H (NA_I (El y_ajCB) :* NP0)))
                 -> El (DictUnpacking y_ajCB)
        IdxMaybeCompIterSrcSpan
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_ajCC) :* NP0)))
                 -> El (Just y_ajCC)
        IdxCompIterSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajCD) :* (NA_I (El y_ajCE) :* NP0)))
                 -> El ((IterFor y_ajCD) y_ajCE)
               Rep (T (H (NA_I (El y_ajCF) :* (NA_I (El y_ajCG) :* NP0))))
                 -> El ((IterIf y_ajCF) y_ajCG)
        IdxCompIfSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajCH) :* (NA_I (El y_ajCI) :* (NA_I (El y_ajCJ) :* NP0))))
                 -> El (((CompIf y_ajCH) y_ajCI) y_ajCJ)
        IdxTup1ExprSrcSpanSuiteSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajCK) :* (NA_I (El y_ajCL) :* NP0)))
                 -> El (((,) y_ajCK) y_ajCL)
        IdxDecoratorSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajCM) :* (NA_I (El y_ajCN) :* (NA_I (El y_ajCO) :* NP0))))
                 -> El (((Decorator y_ajCM) y_ajCN) y_ajCO)
        IdxHandlerSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajCP) :* (NA_I (El y_ajCQ) :* (NA_I (El y_ajCR) :* NP0))))
                 -> El (((Handler y_ajCP) y_ajCQ) y_ajCR)
        IdxExceptClauseSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajCS) :* (NA_I (El y_ajCT) :* NP0)))
                 -> El ((ExceptClause y_ajCS) y_ajCT)
        IdxTup1ExprSrcSpanMaybeExprSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajCU) :* (NA_I (El y_ajCV) :* NP0)))
                 -> El (((,) y_ajCU) y_ajCV)
        IdxMaybeTup1ExprSrcSpanMaybeTup1ExprSrcSpanMaybeExprSrcSpan
          -> \case
               Rep (H NP0) -> El Nothing
               Rep (T (H (NA_I (El y_ajCW) :* NP0)))
                 -> El (Just y_ajCW)
        IdxTup1ExprSrcSpanMaybeTup1ExprSrcSpanMaybeExprSrcSpan
          -> \case
               Rep (H (NA_I (El y_ajCX) :* (NA_I (El y_ajCY) :* NP0)))
                 -> El (((,) y_ajCX) y_ajCY)
