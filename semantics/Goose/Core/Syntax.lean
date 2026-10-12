import Goose.Core.Num

/-!
Typed Goose Core for the pilot profile: types, syntax and module structure.

Every identifier is a dense index into a table of the module or of the
implementation being read. Types are resolved trees: the decoder looks type
indices up, so the evaluator and validator never consult a type table.
-/

namespace Goose.Core

abbrev VarId := Nat
abbrev GlobalId := Nat
abbrev ContextId := Nat
abbrev ImplId := Nat
abbrev OriginId := Nat

/-- Whether a reference or slice permits writes through it. -/
inductive Mutability
  | mutable
  | readOnly
  deriving DecidableEq, Repr, Inhabited

/-- Whether a variable may be assigned after its initialization. -/
inductive VarKind
  | immutable
  | mutable
  deriving DecidableEq, Repr, Inhabited

/-- Whether a parameter receives a copy or a reference to the caller's place. -/
inductive Mode
  | byValue
  | byRef
  deriving DecidableEq, Repr, Inhabited

mutual
/-- Core types. `tuple` exists only so the encoding can name the type of a
call with several results; the validator accepts no form that builds one. -/
inductive Ty
  | int (t : IntTy)
  | bool
  | unit
  | arr (elem : Ty) (count : Nat)
  | grow (elem : Ty)
  | ref (m : Mutability) (target : Ty)
  | slice (m : Mutability) (elem : Ty)
  | tuple (parts : TyList)

/-- The components of a tuple type. A mutual type, not `List Ty`, so that
`Ty` has decidable equality. -/
inductive TyList
  | nil
  | cons (head : Ty) (tail : TyList)
end

deriving instance DecidableEq, Repr, Inhabited for Ty, TyList

mutual
/-- A place: storage that can be read, written or referred to. -/
inductive Place
  | var (x : VarId)
  | global (g : GlobalId)
  | deref (e : Expr)
  | elem (v : View) (index : Expr) (org : OriginId)

/-- A sampled run of elements. `of` samples the owner's current length;
`val` takes the run a slice value denotes. -/
inductive View
  | of (p : Place)
  | val (e : Expr)

inductive Bound
  | expr (e : Expr)
  | fromEnd (e : Expr)
  | omitted

inductive Expr
  | lit (t : IntTy) (n : Int)
  | bool (b : Bool)
  | read (p : Place)
  | ref (m : Mutability) (p : Place)
  | slice (m : Mutability) (v : View) (lo hi : Bound) (org : OriginId)
  | len (v : View)
  | un (op : UnOp) (e : Expr) (org : OriginId)
  | bin (op : BinOp) (a b : Expr) (org : OriginId)
  | cmp (op : CmpOp) (a b : Expr)
  | and (a b : Expr)
  | or (a b : Expr)
  | not (e : Expr)
  | conv (k : ConvKind) (target : Ty) (e : Expr) (org : OriginId)
  | call (c : ContextId) (args : List Arg) (org : OriginId)
  | push (owner : Place) (e : Expr)
  | ifE (c : Expr) (thenB elseB : Block)
  | blockE (b : Block)
  | arrLit (t : Ty) (es : List Expr)
  | fill (t : Ty) (e : Expr)

inductive Arg
  | byVal (e : Expr)
  | byRef (m : Mutability) (p : Place)

/-- A scope. `scope` is the block's number within its implementation. -/
inductive Block
  | mk (scope : Nat) (stmts : List Stmt) (value : Option Expr)

inductive PrintArg
  | text (s : String)
  | expr (e : Expr)

inductive Stmt
  | letS (x : VarId) (e : Expr) (org : OriginId)
  | assign (p : Place) (e : Expr) (org : OriginId)
  | assignOp (op : BinOp) (p : Place) (e : Expr) (org : OriginId)
  | rebind (x : VarId) (e : Expr) (org : OriginId)
  | expr (e : Expr) (org : OriginId)
  | append (owner : Place) (src : View) (org : OriginId)
  | ifS (c : Expr) (thenB : Block) (elseB : Option Block) (org : OriginId)
  | while (c : Expr) (body : Block) (org : OriginId)
  | forRange (x : VarId) (lo hi : Expr) (body : Block) (org : OriginId)
  | forEach (x : VarId) (index : Option VarId) (v : View) (byRef : Bool)
      (body : Block) (org : OriginId)
  | ret (e : Option Expr) (org : OriginId)
  | brk (org : OriginId)
  | cont (org : OriginId)
  | print (args : List PrintArg) (org : OriginId)
  | assertS (e : Expr) (org : OriginId)
  | abort (message : String) (org : OriginId)
  | exit (e : Expr) (org : OriginId)
end

def Block.scope : Block → Nat
  | .mk s _ _ => s

def Block.stmts : Block → List Stmt
  | .mk _ ss _ => ss

def Block.value : Block → Option Expr
  | .mk _ _ v => v

structure Param where
  var : VarId
  mode : Mode
  deriving Repr

/-- One variable of an implementation, parameters included. -/
structure LocalVar where
  name : String
  ty : Ty
  kind : VarKind
  /-- Number of the block that declares the variable. -/
  scope : Nat
  org : OriginId
  deriving Repr

/-- Storage an effect summary can name: a parameter's reachable storage or a global. -/
inductive Target
  | param (i : Nat)
  | global (g : GlobalId)
  deriving DecidableEq, Repr

structure Summary where
  reads : List Target
  writes : List Target
  grows : List Target
  rebinds : List Target
  aborts : Bool
  outputs : Bool
  deriving DecidableEq, Repr

/-- `unknown` implies every effect. -/
inductive SummaryAnn
  | known (s : Summary)
  | unknown
  deriving DecidableEq, Repr

structure Impl where
  name : String
  params : Array Param
  results : Array Ty
  vars : Array LocalVar
  body : Block
  summary : SummaryAnn

/-- What a reference or slice variable may be rooted at. `local` and `param`
are relative to the implementation the context specializes. -/
inductive RootRef
  | local (x : VarId)
  | global (g : GlobalId)
  | param (i : Nat)
  deriving DecidableEq, Repr

/-- One checked specialization of a source function. Execution never reads it. -/
structure Context where
  impl : ImplId
  decl : String
  /-- Root set of each variable of reference or slice type, ascending by variable. -/
  varRoots : List (VarId × List RootRef)
  /-- One root set per result. -/
  resultRoots : List (List RootRef)
  deriving Repr

structure Global where
  name : String
  ty : Ty
  kind : VarKind
  init : Expr
  org : OriginId

structure Origin where
  file : Nat
  line : Nat
  kind : String
  deriving Repr

structure Module where
  files : Array String
  types : Array Ty
  globals : Array Global
  impls : Array Impl
  contexts : Array Context
  entry : ContextId
  origins : Array Origin

/-- Abort kinds of the pilot profile, in the names the encoding uses. -/
inductive AbortKind
  | divZero
  | divOverflow
  | indexOob
  | sliceOob
  | assert
  | userAbort
  | intOverflow
  | castRange
  deriving DecidableEq, Repr, Inhabited

def AbortKind.tag : AbortKind → String
  | .divZero => "div_zero"
  | .divOverflow => "div_overflow"
  | .indexOob => "index_oob"
  | .sliceOob => "slice_oob"
  | .assert => "assert"
  | .userAbort => "user_abort"
  | .intOverflow => "int_overflow"
  | .castRange => "cast_range"

def AbortKind.ofTag? : String → Option AbortKind
  | "div_zero" => some .divZero
  | "div_overflow" => some .divOverflow
  | "index_oob" => some .indexOob
  | "slice_oob" => some .sliceOob
  | "assert" => some .assert
  | "user_abort" => some .userAbort
  | "int_overflow" => some .intOverflow
  | "cast_range" => some .castRange
  | _ => none

def AbortKind.ofNum : NumAbort → AbortKind
  | .divZero => .divZero
  | .divOverflow => .divOverflow
  | .intOverflow => .intOverflow
  | .castRange => .castRange

/-- Node kinds an origin may name. -/
def originKinds : List String :=
  ["global", "param", "let", "assign", "assign_op", "rebind", "expr", "if", "while",
   "for", "return", "break", "continue", "print", "assert", "abort", "exit", "call",
   "index", "slice", "binary", "unary", "cast"]

/-- Types made only of integers, booleans and fixed arrays of those: the
elements a pilot array may hold and the values that can be copied whole. -/
def Ty.flat : Ty → Bool
  | .int _ | .bool => true
  | .arr e _ => e.flat
  | _ => false

end Goose.Core
