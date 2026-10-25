import Goose.Lower.Validation.ExpressionContentsRules

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem FreshContentsEvidence.snapshot {le : LEnv} {first : Nat} {before after : LS}
    {owner value : ValueId} {mode : SnapshotMode} {current : BlockId}
    (evidence : FreshContentsEvidence le first before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.snapshot mode owner) le before = (value, after)) :
    FreshContentsEvidence le first after value :=
  evidence.emitDef_dependency checked bounded live run (fun _ permitted => permitted)

theorem FreshContentsEvidence.indexChecked {le : LEnv} {first : Nat} {before after : LS}
    {owner value index : ValueId} {origin : Option OriginId} {current : BlockId}
    (evidence : FreshContentsEvidence le first before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.indexChecked owner index origin) le before = (value, after)) :
    FreshContentsEvidence le first after value :=
  evidence.emitDef_dependency checked bounded live run (fun _ permitted => permitted)

theorem FreshContentsEvidence.refElem {le : LEnv} {first : Nat} {before after : LS}
    {owner value index : ValueId} {current : BlockId}
    (evidence : FreshContentsEvidence le first before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : emitDef (.refElem owner index) le before = (value, after)) :
    FreshContentsEvidence le first after value :=
  evidence.emitDef_dependency checked bounded live run (fun _ permitted => permitted)

theorem freshViewContentsEvidence_intrinsic {le : LEnv} {before after : LS}
    {value : ValueId} {op : Op} {element : Ty} {current : BlockId}
    (intrinsic : IntrinsicContentsOperation op)
    (typed : op.resultTy (tyEnv le before) = .ok (.view .mutable element))
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after)) :
    FreshContentsEvidence le before.vals.size after value := by
  have recorded := (emitDef_recorded live typed).2.2.1
  change (emitDef op le before).2.vals[(emitDef op le before).1]? = _ at recorded
  rw [run] at recorded
  apply freshContentsEvidence_definition checked bounded live run
  cases intrinsic <;> simp only [ContentsOperation, typedPermissions, recorded, beq_self_eq_true]

#print axioms FreshContentsEvidence.snapshot
#print axioms FreshContentsEvidence.indexChecked
#print axioms FreshContentsEvidence.refElem
#print axioms freshViewContentsEvidence_intrinsic

end Goose.Lower.Validation
