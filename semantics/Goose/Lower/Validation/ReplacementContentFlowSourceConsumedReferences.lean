import Goose.GIR.ReplacementContentFlowProofsScopedTyping
import Goose.GIR.RootBounds
import Goose.Core.Demand

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.GIR.ReplacementContentFlow.Model

inductive ConsumedReferenceOccurrence (env : PEnv) (root : DemandNode) (func : Func)
    (types : Array (Option VTy)) (upper : Prov) : ValueId → Prop
  | place (value : ValueId) (localEnv : PEnv) (path : List Nat) (place : Place)
      (before : RState) (roots : List RootRef) (after : RState)
      (access : localEnv.access = env.access) (source : DemandNodeAt root path (.place place))
      (replay : rpPlace localEnv place before = .ok (roots,after))
      (bounded : value < upper.vals.size) (refined : GIR.RootsRefine func (rootsAt upper.vals value) roots) :
      ConsumedReferenceOccurrence env root func types upper value
  | read (value : ValueId) (localEnv : PEnv) (path : List Nat) (place : Place)
      (before : RState) (roots : List RootRef) (after : RState)
      (access : localEnv.access = env.access) (source : DemandNodeAt root path (.expression (.read place)))
      (replay : rpExpr localEnv (.read place) before = .ok (roots,after))
      (bounded : value < upper.vals.size) (refined : GIR.RootsRefine func (rootsAt upper.vals value) roots) :
      ConsumedReferenceOccurrence env root func types upper value
  | administrative (value slot : Nat) (storage : Slot) (mutability : Mutability) (block : GIR.Block)
      (member : block ∈ func.blocks.toList) (defined : Inst.def value (.slotAddr slot) ∈ block.insts)
      (storageAt : func.slots[slot]? = some storage)
      (typeAt : types[value]? = some (some (.data (.ref mutability storage.ty))))
      (nonowner : storage.ty.ownerElem?.isSome = false) :
      ConsumedReferenceOccurrence env root func types upper value
  | backing (value source : ValueId) (op : Op) (block : GIR.Block)
      (member : block ∈ func.blocks.toList) (defined : Inst.def value op ∈ block.insts)
      (forward : BackingOp op source) (sourceType : VTy)
      (sourceAt : types[source]? = some (some sourceType)) (carrier : SliceViewType sourceType) :
      ConsumedReferenceOccurrence env root func types upper value

theorem sourcePath_append {root parent node : DemandNode} {outerPath suffix : List Nat}
    (outer : DemandNodeAt root outerPath parent) (inner : DemandNodeAt parent suffix node) :
    DemandNodeAt root (outerPath ++ suffix) node := by
  induction outer with
  | here => exact inner
  | child first rest ih => exact .child first (ih inner)

theorem ConsumedReferenceOccurrence.retained {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {before after : Prov} {value : ValueId}
    (origin : ConsumedReferenceOccurrence env root func types before value)
    (growth : before.vals.size ≤ after.vals.size)
    (retained : ∀ index, index < before.vals.size → rootsAt after.vals index = rootsAt before.vals index) :
    ConsumedReferenceOccurrence env root func types after value := by
  cases origin with
  | place localEnv path place start roots finish access source replay bounded refined =>
      apply ConsumedReferenceOccurrence.place value localEnv path place start roots finish access source replay (Nat.lt_of_lt_of_le bounded growth)
      rw [retained value bounded]
      exact refined
  | read localEnv path place start roots finish access source replay bounded refined =>
      apply ConsumedReferenceOccurrence.read value localEnv path place start roots finish access source replay (Nat.lt_of_lt_of_le bounded growth)
      rw [retained value bounded]
      exact refined
  | administrative slot storage mutability block member defined storageAt typeAt nonowner =>
      exact .administrative value slot storage mutability block member defined storageAt typeAt nonowner
  | backing source op block member defined forward sourceType sourceAt carrier =>
      exact .backing value source op block member defined forward sourceType sourceAt carrier

theorem ConsumedReferenceOccurrence.underRoot {env : PEnv} {parent root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {value : ValueId} {outerPath : List Nat}
    (outer : DemandNodeAt root outerPath parent)
    (origin : ConsumedReferenceOccurrence env parent func types upper value) :
    ConsumedReferenceOccurrence env root func types upper value := by
  cases origin with
  | place localEnv path place start roots finish access source replay bounded refined =>
      exact .place value localEnv (outerPath ++ path) place start roots finish access
        (sourcePath_append outer source) replay bounded refined
  | read localEnv path place start roots finish access source replay bounded refined =>
      exact .read value localEnv (outerPath ++ path) place start roots finish access
        (sourcePath_append outer source) replay bounded refined
  | administrative slot storage mutability block member defined storageAt typeAt nonowner =>
      exact .administrative value slot storage mutability block member defined storageAt typeAt nonowner
  | backing source op block member defined forward sourceType sourceAt carrier =>
      exact .backing value source op block member defined forward sourceType sourceAt carrier

theorem ConsumedReferenceOccurrence.access_eq {env nextEnv : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {value : ValueId}
    (same : env.access = nextEnv.access)
    (origin : ConsumedReferenceOccurrence env root func types upper value) :
    ConsumedReferenceOccurrence nextEnv root func types upper value := by
  cases origin with
  | place localEnv path place start roots finish access source replay bounded refined =>
      exact .place value localEnv path place start roots finish (access.trans same) source replay bounded refined
  | read localEnv path place start roots finish access source replay bounded refined =>
      exact .read value localEnv path place start roots finish (access.trans same) source replay bounded refined
  | administrative slot storage mutability block member defined storageAt typeAt nonowner =>
      exact .administrative value slot storage mutability block member defined storageAt typeAt nonowner
  | backing source op block member defined forward sourceType sourceAt carrier =>
      exact .backing value source op block member defined forward sourceType sourceAt carrier

#print axioms sourcePath_append
#print axioms ConsumedReferenceOccurrence.retained
#print axioms ConsumedReferenceOccurrence.underRoot
#print axioms ConsumedReferenceOccurrence.access_eq

end Goose.Lower.Validation.ReplacementContentFlowSource
