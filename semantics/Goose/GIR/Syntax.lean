import Goose.Core.Typing

/-!
GIR-H for the pilot, flat fixed-struct and owner-shrink profiles: a typed
control-flow graph over SSA temporaries and memory slots.

Design decisions that the rest of the pipeline relies on.

* Data types are Core's types, unchanged. The only extra value type is the
  sampled `view`, which exists as an SSA value only. A value of aggregate type
  (`arr`, `grow`, `growshrink`, `limited`, `structT`) is a transient: it is constructed and read by
  `load`, and it lives in a slot or in the result of a global initializer.
* Every source variable has a slot, numbered like the variable. Parameters
  arrive as parameters of the entry block and are copied into their slots
  right after the body scope is entered.
* A block is a list of parameters and a list of instructions in which exactly
  one terminator must appear, last. The type allows zero or several so that a
  verifier, not the type, rejects them.
* Every instruction that defines a value says which value it defines. Value
  ids are dense from 0, unique within a function, and need not be in
  definition order.
* The scope tree is a forest: a scope with no parent may be entered only when
  no scope is entered. A function body is scope 0; a global initializer has
  one root scope per block that its expression contains.
* Origins are optional on every instruction that takes one, so that a verifier
  can reject an operation that needs one and has none.
* Short-circuit operators, `if` values, loops and `assert` are control flow;
  by-reference parameters are `ref` values passed in the ordinary way.
* Operations whose result is undefined for a bad operand but that the
  lowering only emits where the operand is in range (`ref.elem`, `int.next`)
  fault rather than abort.
-/

namespace Goose.GIR

open Goose.Core

abbrev ValueId := Nat
abbrev BlockId := Nat
abbrev SlotId := Nat
abbrev ScopeId := Nat
abbrev FnId := Nat

/-- The type of an SSA value: a Core data type or a sampled view of a run of
elements. A view carries the mutability of the storage it was sampled from. -/
inductive VTy
  | data (t : Ty)
  | view (m : Mutability) (elem : Ty)
  deriving DecidableEq, Repr, Inhabited

/-- A bound of `view.slice`, resolved against the view's length at run time:
`fromEnd v` is the length minus the value. -/
inductive Bnd
  | omitted
  | val (v : ValueId)
  | fromEnd (v : ValueId)
  deriving DecidableEq, Repr

/-- A sampled array view comes directly from its owner or through a reference. -/
inductive SnapshotMode
  | owner
  | borrowed
  deriving DecidableEq, Repr

inductive PrintPart
  | text (s : String)
  | val (v : ValueId)
  deriving DecidableEq, Repr

/-- Instructions that define one value. -/
inductive Op
  | constInt (t : IntTy) (n : Int)
  | constBool (b : Bool)
  | constUnit
  | bin (op : BinOp) (t : IntTy) (a b : ValueId) (org : Option OriginId)
  | un (op : UnOp) (t : IntTy) (a : ValueId) (org : Option OriginId)
  | cmp (op : CmpOp) (t : IntTy) (a b : ValueId)
  | boolCmp (op : CmpOp) (a b : ValueId)
  | boolNot (a : ValueId)
  | conv (k : ConvKind) (src dst : IntTy) (a : ValueId) (org : Option OriginId)
  /-- `a + 1` for a loop counter that is known to be below its type's maximum. -/
  | next (t : IntTy) (a : ValueId)
  | slotAddr (s : SlotId)
  | globalAddr (g : GlobalId)
  /-- Address of element `i` of the run `v` denotes; no check, no read. -/
  | refElem (v i : ValueId)
  /-- The same address as a read-only reference. -/
  | refFreeze (r : ValueId)
  | load (r : ValueId)
  | snapshot (mode : SnapshotMode) (r : ValueId)
  | sliceView (s : ValueId)
  | viewLen (v : ValueId)
  | viewSlice (m : Mutability) (v : ValueId) (lo hi : Bnd) (org : Option OriginId)
  | arrayLen (r : ValueId)
  | indexChecked (v i : ValueId) (org : Option OriginId)
  /-- Element address whose bounds are established by the function certificate. -/
  | indexProven (v i : ValueId)
  | push (r v : ValueId) (org : Option OriginId)
  /-- Copy and remove the last element of an owner. -/
  | pop (r : ValueId) (org : Option OriginId)
  | call (f : FnId) (args : List ValueId) (org : Option OriginId)
  | arrLit (t : Ty) (vs : List ValueId)
  | arrFill (t : Ty) (v : ValueId)
  | structLit (t : Ty) (vs : List ValueId)
  | fieldAddr (owner : ValueId) (index : Nat)


/-- Instructions that define no value. -/
inductive Effect
  /-- Bring the slot's storage into existence holding `v`. -/
  | slotInit (s : SlotId) (v : ValueId) (org : Option OriginId)
  | store (r v : ValueId) (org : Option OriginId)
  | append (r v : ValueId) (org : Option OriginId)
  /-- Reduce an owner's visible length by a checked count. -/
  | popN (r count : ValueId) (org : Option OriginId)
  /-- Set an owner's length; a fill is evaluated before this instruction. -/
  | resize (r size : ValueId) (fill : Option ValueId) (org : Option OriginId)
  /-- Reduce an owner's visible length to zero. -/
  | clear (r : ValueId) (org : Option OriginId)
  /-- Publish a fresh grow/growshrink run into an owner already cleared. -/
  | replace (r run : ValueId) (org : Option OriginId)
  | enter (sc : ScopeId)
  | leave (sc : ScopeId)
  | print (parts : List PrintPart) (org : Option OriginId)


inductive Term
  | br (b : BlockId) (args : List ValueId)
  | condbr (c : ValueId) (t : BlockId) (targs : List ValueId) (e : BlockId) (eargs : List ValueId)
  | ret (vs : List ValueId) (org : Option OriginId)
  | abort (k : AbortKind) (org : Option OriginId)
  | exit (v : ValueId) (org : Option OriginId)
  /-- The preceding call is known not to return. Reaching this term is a fault. -/
  | unreachable


inductive Inst
  | def (res : ValueId) (op : Op)
  | eff (e : Effect)
  | term (t : Term)


structure Block where
  params : List (ValueId × VTy)
  insts : List Inst


/-- Memory-resident storage of one source variable. -/
structure Slot where
  ty : Ty
  kind : VarKind
  scope : ScopeId
  var : VarId

/-- Root annotations merged from the Core contexts that specialize this
implementation. Rows use parameter positions; result rows align with the
function results. -/
structure RootInfo where
  params : Array (Nat × List RootRef) := #[]
  contents : Array (Nat × List RootRef) := #[]
  results : Array (List RootRef) := #[]

inductive Fact
  | ge0 (i : ValueId)
  | lt (i n : ValueId)
  | lenGe (reference n : ValueId)
  | viewLenGe (v n : ValueId)
  deriving DecidableEq, Repr

abbrev FactCertificate := Array (List Fact)


structure Func where
  name : String
  /-- The signature; block 0's parameters must have these types. -/
  params : List Ty
  results : List Ty
  slots : Array Slot
  /-- The scope tree: the parent of each scope, if it has one. -/
  scopes : Array (Option ScopeId)
  blocks : Array Block
  roots : RootInfo := {}
  summary : SummaryAnn
  org : Option OriginId
  certificate : Option FactCertificate := none


structure Global where
  name : String
  ty : Ty
  kind : VarKind
  /-- A function with no parameters returning the initial value. -/
  init : Func
  org : OriginId


structure Module where
  files : Array String
  globals : Array Global
  funcs : Array Func
  entry : FnId
  origins : Array Origin
  profile : ArtifactProfile := .pilot
  structs : Array StructDef := #[]


/-! ### Structure queries -/

def Term.successors : Term → List BlockId
  | .br b _ => [b]
  | .condbr _ t _ e _ => [t, e]
  | _ => []

def Inst.term? : Inst → Option Term
  | .term t => some t
  | _ => none

/-- The terminators of a block, in order. -/
def Block.terms (b : Block) : List Term := b.insts.filterMap Inst.term?

/-- The block's last instruction, when it is a terminator. -/
def Block.lastTerm? (b : Block) : Option Term :=
  match b.insts.getLast? with
  | some (.term t) => some t
  | _ => none

/-- Values the instruction reads. -/
def Bnd.uses : Bnd → List ValueId
  | .omitted => []
  | .val v | .fromEnd v => [v]

def Op.uses : Op → List ValueId
  | .constInt .. | .constBool _ | .constUnit | .slotAddr _ | .globalAddr _ => []
  | .bin _ _ a b _ | .cmp _ _ a b | .boolCmp _ a b => [a, b]
  | .un _ _ a _ | .boolNot a | .conv _ _ _ a _ | .next _ a => [a]
  | .refElem v i | .indexChecked v i _ | .indexProven v i => [v, i]
  | .refFreeze r | .load r | .sliceView r | .viewLen r | .arrayLen r => [r]
  | .snapshot _ r => [r]
  | .viewSlice _ v lo hi _ => v :: (lo.uses ++ hi.uses)
  | .push r v _ => [r, v]
  | .pop r _ => [r]
  | .call _ args _ => args
  | .arrLit _ vs | .structLit _ vs => vs
  | .arrFill _ v | .fieldAddr v _ => [v]

def PrintPart.uses : PrintPart → List ValueId
  | .text _ => []
  | .val v => [v]

def Effect.uses : Effect → List ValueId
  | .slotInit _ v _ => [v]
  | .store r v _ | .append r v _ => [r, v]
  | .popN r count _ => [r, count]
  | .resize r size fill _ => [r, size] ++ fill.toList
  | .clear r _ => [r]
  | .replace r run _ => [r, run]
  | .enter _ | .leave _ => []
  | .print parts _ => parts.flatMap PrintPart.uses

def Term.uses : Term → List ValueId
  | .br _ args => args
  | .condbr c _ ta _ ea => c :: (ta ++ ea)
  | .ret vs _ => vs
  | .abort .. | .unreachable => []
  | .exit v _ => [v]

def Inst.uses : Inst → List ValueId
  | .def _ op => op.uses
  | .eff e => e.uses
  | .term t => t.uses

/-- The value ids a function defines: block parameters and instruction results. -/
def Block.defs (b : Block) : List ValueId :=
  b.params.map (·.1) ++ b.insts.filterMap fun
    | .def r _ => some r
    | _ => none

def Func.numValues (f : Func) : Nat :=
  f.blocks.foldl (fun n b => n + (b.params.length + (b.insts.filter fun
    | .def .. => true
    | _ => false).length)) 0

end Goose.GIR
