import Goose.Lower.Validation.PermissionPreservationContents
import Goose.Lower.Validation.PermissionPreservationSourceTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerPlace_var_binding_evidence {env : Core.TEnv} {index : VarId} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.var index) start = .ok (info, finish))
    (writable : info.bindingWritable = true) {results : List Ty} {before after : LS}
    {value : ValueId} {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : lowerPlace (.var index) (lowerEnv env.mod env.vars results) before = (value, after)) :
    WritableEvidence (lowerEnv env.mod env.vars results) after value := by
  unfold Core.tyPlace at source
  obtain ⟨localVar, _, lookup, source⟩ := (st_bind_ok _ _ _ _).mp source
  have row := (varOf_ok _ _ _ _).mp lookup
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  dsimp only at shape
  have mutable : localVar.kind = .mutable := by
    rw [shape] at writable
    cases kind : localVar.kind <;> simp_all
  have slotRow : (lowerEnv env.mod env.vars results).slots[index]? =
      some ⟨localVar.ty, localVar.kind, localVar.scope, index⟩ := by
    simp [lowerEnv, Array.getElem?_mapIdx, row.2.1]
  exact writableEvidence_slot checked bounded live slotRow mutable run

theorem lowerPlace_global_binding_evidence {env : Core.TEnv} {index : GlobalId} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.global index) start = .ok (info, finish))
    (writable : info.bindingWritable = true) {results : List Ty} {before after : LS}
    {value : ValueId} {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : lowerPlace (.global index) (lowerEnv env.mod env.vars results) before = (value, after)) :
    WritableEvidence (lowerEnv env.mod env.vars results) after value := by
  by_cases available : index < env.globalLimit
  · cases globalRow : env.mod.globals[index]? with
    | none => simp [Core.tyPlace, available, globalRow, rej_ok] at source
    | some globalVar =>
      simp only [Core.tyPlace, available, globalRow, ite_true] at source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      dsimp only at shape
      have mutable : globalVar.kind = .mutable := by
        rw [shape] at writable
        cases kind : globalVar.kind <;> simp_all
      have row : (lowerEnv env.mod env.vars results).globals[index]? = some (globalVar.ty, .mutable) := by
        simp only [lowerEnv, Array.getElem?_map, globalRow, Option.map_some, mutable]
      exact writableEvidence_global checked bounded live row run
  · simp [Core.tyPlace, available, rej_ok] at source

theorem source_field_binding_authority {env : Core.TEnv} {owner : Place} {index : Nat}
    {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.field owner index) start = .ok (info, finish))
    (writable : info.bindingWritable = true) :
    ∃ ownerInfo next field fieldFinish,
      Core.tyPlace env owner start = .ok (ownerInfo, next) ∧
      Core.structField env ownerInfo.ty index next = .ok (field, fieldFinish) ∧
      ownerInfo.contentsWritable = true ∧ field.binding = .mutable := by
  unfold Core.tyPlace at source
  obtain ⟨ownerInfo, next, ownerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨field, fieldFinish, fieldSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  dsimp only at shape
  rw [shape] at writable
  have both := Bool.and_eq_true_iff.mp writable
  have binding : field.binding = .mutable := eq_of_beq both.2
  exact ⟨ownerInfo, next, field, fieldFinish, ownerSource, fieldSource, both.1, binding⟩

theorem lowerPlace_field_binding_evidence_of_owner {env : Core.TEnv} {owner : Place} {index : Nat}
    {ownerInfo info : PlaceInfo} {start ownerFinish finish : Nat}
    (ownerSource : Core.tyPlace env owner start = .ok (ownerInfo, ownerFinish))
    (source : Core.tyPlace env (.field owner index) start = .ok (info, finish))
    (writable : info.bindingWritable = true) {results : List Ty} {before middle after : LS}
    {ownerValue value : ValueId} {mu : Mutability} {current : BlockId}
    (ownerRun : lowerPlace owner (lowerEnv env.mod env.vars results) before = (ownerValue, middle))
    (ownerTyped : middle.vals[ownerValue]? = some (some (.data (.ref mu ownerInfo.ty))))
    (ownerEvidence : ContentsEvidence (lowerEnv env.mod env.vars results) middle ownerValue)
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle) (live : middle.cur = some current)
    (run : lowerPlace (.field owner index) (lowerEnv env.mod env.vars results) before = (value, after)) :
    WritableEvidence (lowerEnv env.mod env.vars results) after value := by
  obtain ⟨actualOwner, next, field, fieldFinish, childSource, fieldSource, _, binding⟩ :=
    source_field_binding_authority source writable
  rw [ownerSource] at childSource
  cases Except.ok.inj childSource
  obtain ⟨id, fields, descriptor, shape, descriptorRow, _, fieldRow⟩ := structField_descriptor fieldSource
  rw [shape] at ownerTyped
  simp only [lowerPlace, bind_run, ownerRun] at run
  exact ownerEvidence.fieldAddr_binding checked bounded live ownerTyped descriptorRow fieldRow binding run

theorem lowerPlace_elem_binding_evidence_of_children {le : LEnv} {view : View} {index : Expr}
    {origin : OriginId} {before viewAfter indexAfter after : LS} {viewValue indexValue value : ValueId}
    {current : BlockId} (viewRun : lowerView view le before = (viewValue, viewAfter))
    (indexRun : lowerExpr index le viewAfter = (indexValue, indexAfter))
    (viewEvidence : ContentsEvidence le indexAfter viewValue)
    (checked : indexAfter.DenseDefinitions) (bounded : LiveBound indexAfter)
    (live : indexAfter.cur = some current)
    (run : lowerPlace (.elem view index origin) le before = (value, after)) :
    WritableEvidence le after value := by
  simp only [lowerPlace, bind_run, viewRun, indexRun] at run
  exact viewEvidence.indexChecked_binding checked bounded live run

#print axioms lowerPlace_var_binding_evidence
#print axioms lowerPlace_global_binding_evidence
#print axioms source_field_binding_authority
#print axioms lowerPlace_field_binding_evidence_of_owner
#print axioms lowerPlace_elem_binding_evidence_of_children

end Goose.Lower.Validation
