import Goose.Construct.Typing



namespace Goose.Construct.GIR

open Goose.Core (Mutability VarKind IntTy BinOp UnOp CmpOp ConvKind OriginId GlobalId VarId AbortKind NonlocalTarget Request ConstructionRequest RelocationReason)

abbrev ValueId := Nat
abbrev BlockId := Nat
abbrev SlotId := Nat
abbrev ScopeId := Nat
abbrev FnId := Nat


inductive VTy
  | data (t : Ty)
  | view (m : Mutability) (elem : Ty)
  | dest (ty : Ty) (request : ConstructionRequest)
  | built (ty : Ty) (request : ConstructionRequest)
  | cancelled (ty : Ty) (request : ConstructionRequest)
  | pack (parts : List ResultDescriptor)
  deriving DecidableEq, Repr, Inhabited


inductive Bnd
  | omitted
  | val (v : ValueId)
  | fromEnd (v : ValueId)
  deriving DecidableEq, Repr


inductive SnapshotMode
  | owner
  | borrowed
  deriving DecidableEq, Repr

inductive PrintPart
  | text (s : String)
  | val (v : ValueId)
  deriving DecidableEq, Repr


inductive DestReceiver
  | slot (id : SlotId)
  | global (id : GlobalId)
  | push (reference : ValueId)
  | append (reference : ValueId)
  | whole (reference : ValueId)
  | arg (callee : FnId) (position : Nat)
  deriving DecidableEq, Repr

def DestReceiver.uses : DestReceiver → List ValueId
  | .push v | .append v | .whole v => [v]
  | _ => []

structure EscapeEdge where
  target : Nat
  block : BlockId
  args : List ValueId
  deriving DecidableEq, Repr

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
  
  | next (t : IntTy) (a : ValueId)
  | slotAddr (s : SlotId)
  | globalAddr (g : GlobalId)
  
  | refElem (v i : ValueId)
  
  | refFreeze (r : ValueId)
  | load (r : ValueId)
  | snapshot (mode : SnapshotMode) (r : ValueId)
  | sliceView (s : ValueId)
  | viewLen (v : ValueId)
  | viewSlice (m : Mutability) (v : ValueId) (lo hi : Bnd) (org : Option OriginId)
  | arrayLen (r : ValueId)
  | indexChecked (v i : ValueId) (org : Option OriginId)
  
  | indexProven (v i : ValueId)
  | push (r v : ValueId) (org : Option OriginId)
  
  | pop (r : ValueId) (org : Option OriginId)
  | call (f : FnId) (args : List ValueId) (org : Option OriginId)
  | arrLit (t : Ty) (vs : List ValueId)
  | arrFill (t : Ty) (v : ValueId)
  | structLit (t : Ty) (vs : List ValueId)
  | fieldAddr (owner : ValueId) (index : Nat)
  | render (operand : ValueId) (org : Option OriginId)
  | bytes (data : List UInt8) (org : Option OriginId)
  | result (pack : ValueId) (position : Nat)
  | destOpen (receiver : DestReceiver) (ty : Ty) (request : ConstructionRequest) (count : Option ValueId) (org : Option OriginId)
  | destChild (parent : ValueId) (element : Ty) (org : Option OriginId)
  | destFinish (destination : ValueId) (org : Option OriginId)
  | destNamed (slot : SlotId) (org : Option OriginId)
  | resultExitDest (position : Nat) (org : Option OriginId)
  | destAbandonNamed (slot : SlotId) (replacement : ValueId) (org : Option OriginId)
  | destPublishRef (built : ValueId) (org : Option OriginId)
  | destArg (built : ValueId) (org : Option OriginId)
  | destAbandon (carrier : ValueId) (org : Option OriginId)
  | destValue (destination : ValueId) (org : Option OriginId)
  | destRelocate (built : ValueId) (reason : RelocationReason) (org : Option OriginId)
  | destStage (destination : ValueId) (org : Option OriginId)
  | destFit (built : ValueId) (org : Option OriginId)
  | callConstruct (callee : FnId) (args destinations : List ValueId) (org : Option OriginId)
  | targetDest (target position : Nat) (org : Option OriginId)



inductive Effect
  
  | slotInit (s : SlotId) (v : ValueId) (org : Option OriginId)
  | store (r v : ValueId) (org : Option OriginId)
  | append (r v : ValueId) (org : Option OriginId)
  
  | popN (r count : ValueId) (org : Option OriginId)
  
  | resize (r size : ValueId) (fill : Option ValueId) (org : Option OriginId)
  
  | clear (r : ValueId) (org : Option OriginId)
  
  | replace (r run : ValueId) (org : Option OriginId)
  | enter (sc : ScopeId)
  | leave (sc : ScopeId)
  | print (parts : List PrintPart) (org : Option OriginId)
  | appendValue (receiver snapshot : ValueId) (org : Option OriginId)
  | destRepeat (destination source : ValueId) (org : Option OriginId)
  | destSnapshot (destination snapshot : ValueId) (org : Option OriginId)
  | destWrite (destination value : ValueId) (org : Option OriginId)
  | destAttach (parent child : ValueId) (org : Option OriginId)
  | destBytes (destination : ValueId) (bytes : List UInt8) (org : Option OriginId)
  | destText (destination value : ValueId) (org : Option OriginId)
  | destCopy (destination source : ValueId) (org : Option OriginId)
  | destBind (slot : SlotId) (built : ValueId) (org : Option OriginId)
  | destPublish (built : ValueId) (org : Option OriginId)
  | destCancel (cancelled : ValueId) (org : Option OriginId)


inductive Term
  | br (b : BlockId) (args : List ValueId)
  | condbr (c : ValueId) (t : BlockId) (targs : List ValueId) (e : BlockId) (eargs : List ValueId)
  | ret (vs : List ValueId) (org : Option OriginId)
  | abort (k : AbortKind) (org : Option OriginId)
  | exit (v : ValueId) (org : Option OriginId)
  
  | unreachable
  | invoke (callee : FnId) (args destinations : List ValueId) (normal : BlockId) (forwarded : List ValueId) (escapes : List EscapeEdge) (org : Option OriginId)
  | escape (target : Nat) (results cancellations : List ValueId) (org : Option OriginId)


inductive Inst
  | def (res : ValueId) (op : Op)
  | eff (e : Effect)
  | term (t : Term)


structure Block where
  params : List (ValueId × VTy)
  insts : List Inst



structure Slot where
  ty : Ty
  kind : VarKind
  scope : ScopeId
  var : VarId


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
  
  params : List Ty
  results : List ResultDescriptor
  slots : Array Slot
  
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
  
  init : Func
  org : OriginId


structure Module where
  files : Array String
  globals : Array Global
  funcs : Array Func
  entry : FnId
  origins : Array Origin
  structs : Array StructDef := #[]
  types : Array VTy := #[]
  targets : Array NonlocalTarget := #[]




def Term.successors : Term → List BlockId
  | .br b _ => [b]
  | .condbr _ t _ e _ => [t, e]
  | .invoke _ _ _ normal _ escapes _ => normal :: escapes.map (·.block)
  | _ => []

def Inst.term? : Inst → Option Term
  | .term t => some t
  | _ => none


def Block.terms (b : Block) : List Term := b.insts.filterMap Inst.term?


def Block.lastTerm? (b : Block) : Option Term :=
  match b.insts.getLast? with
  | some (.term t) => some t
  | _ => none


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
  | .bytes .. | .destNamed .. | .resultExitDest .. | .targetDest .. => []
  | .result v _ | .render v _ => [v]
  | .destOpen receiver _ _ count _ => receiver.uses ++ count.toList
  | .destChild v _ _ | .destFinish v _ | .destPublishRef v _ | .destArg v _ | .destAbandon v _ |
      .destValue v _ | .destRelocate v _ _ | .destStage v _ | .destFit v _ => [v]
  | .destAbandonNamed _ v _ => [v]
  | .callConstruct _ args destinations _ => args ++ destinations

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
  | .destRepeat a b _ | .destSnapshot a b _ | .appendValue a b _ | .destWrite a b _ | .destAttach a b _ | .destText a b _ | .destCopy a b _ => [a,b]
  | .destBytes d _ _ | .destBind _ d _ | .destPublish d _ | .destCancel d _ => [d]

def Term.uses : Term → List ValueId
  | .br _ args => args
  | .condbr c _ ta _ ea => c :: (ta ++ ea)
  | .ret vs _ => vs
  | .abort .. | .unreachable => []
  | .exit v _ => [v]
  | .invoke _ args destinations _ forwarded escapes _ => args ++ destinations ++ forwarded ++ escapes.flatMap (·.args)
  | .escape _ results cancellations _ => results ++ cancellations

def Inst.uses : Inst → List ValueId
  | .def _ op => op.uses
  | .eff e => e.uses
  | .term t => t.uses


def Block.defs (b : Block) : List ValueId :=
  b.params.map (·.1) ++ b.insts.filterMap fun
    | .def r _ => some r
    | _ => none

def Func.numValues (f : Func) : Nat :=
  f.blocks.foldl (fun n b => n + (b.params.length + (b.insts.filter fun
    | .def .. => true
    | _ => false).length)) 0

end Goose.Construct.GIR
