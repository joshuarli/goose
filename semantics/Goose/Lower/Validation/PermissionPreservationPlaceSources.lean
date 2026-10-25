import Goose.Lower.Validation.PermissionPreservationFreshOperations
import Goose.Lower.Validation.PermissionPreservationSourceTransfers
import Goose.Lower.Validation.DereferenceTyping

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerPlace_var_fresh_binding_evidence {env : Core.TEnv} {index : VarId} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.var index) start = .ok (info, finish))
    (writable : info.bindingWritable = true) {results : List Ty} {before after : LS}
    {value : ValueId} {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : lowerPlace (.var index) (lowerEnv env.mod env.vars results) before = (value, after)) :
    FreshWritableEvidence (lowerEnv env.mod env.vars results) before.vals.size after value := by
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
  exact freshWritableEvidence_slot checked bounded live slotRow mutable run

theorem lowerPlace_global_fresh_binding_evidence {env : Core.TEnv} {index : GlobalId} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.global index) start = .ok (info, finish))
    (writable : info.bindingWritable = true) {results : List Ty} {before after : LS}
    {value : ValueId} {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current)
    (run : lowerPlace (.global index) (lowerEnv env.mod env.vars results) before = (value, after)) :
    FreshWritableEvidence (lowerEnv env.mod env.vars results) before.vals.size after value := by
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
      exact freshWritableEvidence_global checked bounded live row run
  · simp [Core.tyPlace, available, rej_ok] at source

theorem source_deref_binding_referenceWritable {env : Core.TEnv} {expr : Expr} {info : PlaceInfo}
    {start finish : Nat} (source : Core.tyPlace env (.deref expr) start = .ok (info, finish))
    (binding : info.bindingWritable = true) : info.referenceWritable env.mod.profile = true := by
  unfold Core.tyPlace at source
  obtain ⟨referent, next, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  cases referent with
  | ref mu target =>
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    dsimp only at shape
    have same : info.bindingWritable = info.contentsWritable := by rw [shape]
    cases ty : info.ty <;> simp_all [PlaceInfo.referenceWritable]
  | _ => exact (rej_ok _ _ _ _).mp source |>.elim

theorem source_elem_binding_contents {env : Core.TEnv} {view : View} {index : Expr}
    {origin : OriginId} {info : PlaceInfo} {start finish : Nat}
    (source : Core.tyPlace env (.elem view index origin) start = .ok (info, finish))
    (binding : info.bindingWritable = true) : info.contentsWritable = true := by
  unfold Core.tyPlace at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨⟨element, mu⟩, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
  dsimp only at shape
  simpa only [shape] using binding

theorem source_deref_binding_child {env : Core.TEnv} {expr : Expr} {info : PlaceInfo}
    {start finish : Nat} (ordinary : Core.sliceRefTy env expr = none)
    (source : Core.tyPlace env (.deref expr) start = .ok (info, finish))
    (binding : info.bindingWritable = true) :
    ∃ childFinish, Core.tyExpr env expr start = .ok (.ref .mutable info.ty, childFinish) := by
  simp only [Core.tyPlace, ordinary] at source
  obtain ⟨referent, next, input, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨childTy, childFinish, childSource, input⟩ := (st_bind_ok _ _ _ _).mp input
  by_cases referenceSlice : childTy.isRefSlice = true
  · simp [referenceSlice, chk] at input
  · simp only [referenceSlice] at input
    have same : referent = childTy := congrArg Prod.fst ((st_pure_ok _ _ _).mp input)
    subst referent
    cases childTy with
    | ref mu target =>
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      dsimp only at shape
      cases mu with
      | readOnly => simp only [shape] at binding; contradiction
      | mutable =>
        exact ⟨childFinish, by simpa only [shape] using childSource⟩
    | _ => exact (rej_ok _ _ _ _).mp source |>.elim

#print axioms lowerPlace_var_fresh_binding_evidence
#print axioms lowerPlace_global_fresh_binding_evidence
#print axioms source_deref_binding_referenceWritable
#print axioms source_elem_binding_contents
#print axioms source_deref_binding_child

end Goose.Lower.Validation
