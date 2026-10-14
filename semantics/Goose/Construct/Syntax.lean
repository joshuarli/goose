import Goose.Core.Construction

namespace Goose.Construct
open Goose.Core (Mutability VarKind Mode IntTy UnOp BinOp CmpOp ConvKind NumAbort OriginId StructId VarId GlobalId ContextId ImplId Request NonlocalTarget)

mutual

inductive Ty
  | int (t : IntTy)
  | bool
  | unit
  | arr (elem : Ty) (count : Nat)
  | varr (elem : Ty)
  | grow (elem : Ty)
  | growshrink (elem : Ty)
  | limited (elem : Ty) (capacity : Nat)
  | ref (m : Mutability) (target : Ty)
  | slice (m : Mutability) (elem : Ty)
  | tuple (parts : TyList)
  
  | structT (id : StructId) (fields : TyList)

inductive TyList
  | nil
  | cons (head : Ty) (tail : TyList)
end

deriving instance DecidableEq, Repr, Inhabited for Ty, TyList

def TyList.toList : TyList → List Ty
  | .nil => []
  | .cons t ts => t :: ts.toList

def TyList.ofList : List Ty → TyList
  | [] => .nil
  | t :: ts => .cons t (TyList.ofList ts)

structure StructField where
  ty : Ty
  binding : VarKind
  contents : Mutability
  byteOffset : Nat
  deriving DecidableEq, Repr

structure StructDef where
  byteSize : Nat
  fields : Array StructField
  displayName : String
  deriving DecidableEq, Repr

mutual

inductive Place
  | var (x : VarId)
  | global (g : GlobalId)
  | deref (e : Expr)
  | elem (v : View) (index : Expr) (org : OriginId)
  | field (owner : Place) (index : Nat)

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
  | push (owner : Place) (e : Expr) (org : Option OriginId := none)
  | pop (owner : Place) (org : OriginId)
  | ifE (c : Expr) (thenB elseB : Block)
  | blockE (b : Block)
  | arrLit (t : Ty) (es : List Expr)
  | fill (t : Ty) (e : Expr)
  | structLit (t : Ty) (es : List Expr)
  | bytes (t : Ty) (data : List UInt8) (org : OriginId)
  | str (t : Ty) (args : List PrintArg) (org : OriginId)
  | copy (t : Ty) (source : Place) (org : OriginId)
  | resultLocal (var : VarId) (org : OriginId)
  | values (operands : List Expr)

inductive Arg
  | byVal (e : Expr)
  | construct (e : Expr)
  | byRef (m : Mutability) (p : Place)

inductive Block
  | mk (scope : Nat) (stmts : List Stmt) (value : Option Expr)

inductive PrintArg
  | text (s : String)
  | expr (e : Expr)
  | view (v : View)

inductive Stmt
  | letS (x : VarId) (e : Expr) (org : OriginId)
  | assign (p : Place) (e : Expr) (org : OriginId)
  | assignOp (op : BinOp) (p : Place) (e : Expr) (org : OriginId)
  | rebind (x : VarId) (e : Expr) (org : OriginId)
  | expr (e : Expr) (org : OriginId)
  | append (owner : Place) (src : View) (org : OriginId)
  | popN (owner : Place) (count : Expr) (org : OriginId)
  | resize (owner : Place) (size : Expr) (fill : Option Expr) (org : OriginId)
  | clear (owner : Place) (org : OriginId)
  | assignWhole (owner : Place) (replacement : Expr) (org : OriginId)
  | ifS (c : Expr) (thenB : Block) (elseB : Option Block) (org : OriginId)
  | while (c : Expr) (body : Block) (org : OriginId)
  | forRange (x : VarId) (lo hi : Expr) (body : Block) (org : OriginId)
  | forEach (x : VarId) (index : Option VarId) (v : View) (byRef : Bool)
      (body : Block) (org : OriginId)
  | receive (vars : List VarId) (producer : Expr) (org : OriginId)
  | appendValue (owner : Place) (producer : Expr) (org : OriginId)
  | appendConstruct (owner : Place) (producer : Expr) (org : OriginId)
  | retValues (operands : List Expr) (org : OriginId)
  | retForward (call : Expr) (org : OriginId)
  | returnFrom (target : Nat) (operands : List Expr) (org : OriginId)
  | returnFromForward (target : Nat) (call : Expr) (org : OriginId)
  | breakValue (value : Expr) (org : OriginId)
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

structure LocalVar where
  name : String
  ty : Ty
  kind : VarKind
  
  scope : Nat
  org : OriginId
  deriving Repr

inductive Target
  | param (i : Nat)
  | global (g : GlobalId)
  deriving DecidableEq, Repr

structure Summary where
  reads : List Target
  writes : List Target
  grows : List Target
  shrinks : List Target
  rebinds : List Target
  constructs : List Nat
  needs : List Nat
  escapes : List Nat
  aborts : Bool
  outputs : Bool
  deriving DecidableEq, Repr

inductive SummaryAnn
  | known (s : Summary)
  | unknown
  deriving DecidableEq, Repr

structure ResultDescriptor where
  ty : Ty
  request : Request
  namedLocal : Option VarId
  deriving DecidableEq, Repr

structure Impl where
  name : String
  params : Array Param
  results : Array ResultDescriptor
  vars : Array LocalVar
  body : Block
  summary : SummaryAnn

inductive RootRef
  | static
  | local (x : VarId)
  | global (g : GlobalId)
  | param (i : Nat)
  deriving DecidableEq, Repr

structure Context where
  impl : ImplId
  decl : String
  
  varRoots : List (VarId × List RootRef)
  
  resultRoots : List (List RootRef)
  
  contentRoots : List (VarId × List RootRef) := []
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
  structs : Array StructDef
  targets : Array NonlocalTarget

def Module.structType? (m : Module) (sid : StructId) : Option Ty :=
  m.structs[sid]?.map fun d => .structT sid (TyList.ofList (d.fields.toList.map (·.ty)))

mutual
def Ty.flat : Ty → Bool
  | .int _ | .bool => true
  | .arr e _ => e.flat
  | .structT _ fs => fs.flat
  | _ => false

def TyList.flat : TyList → Bool
  | .nil => true
  | .cons t ts => t.flat && ts.flat
end

mutual
def Ty.variableElement : Ty → Bool
  | .varr e => e.flat || e.variableElement
  | .arr e _ => e.variableElement
  | _ => false

def Ty.nonfixed : Ty → Bool
  | .varr _ | .grow _ | .growshrink _ | .limited _ _ => true
  | .arr e _ => e.variableElement
  | _ => false
end

def Ty.constructible : Ty → Bool
  | .varr e | .grow e => e.flat || e.variableElement
  | .arr e _ => e.flat || e.variableElement
  | .growshrink e | .limited e _ => e.flat
  | t => t.flat

end Goose.Construct
