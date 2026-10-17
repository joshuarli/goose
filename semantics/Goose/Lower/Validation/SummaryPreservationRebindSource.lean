import Goose.Lower.Validation.SummaryPreservationStores
import Goose.Lower.Validation.SummaryPreservationCoerceSlots

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_rebind_contract {env : PEnv} {varId : VarId} {expression : Expr} {org : OriginId}
    {roots : List RootRef} {initial before after : RState}
    (operand : rpExpr env expression initial = .ok (roots, before))
    (source : rpStmt env (.rebind varId expression org) initial = .ok ((), after)) :
    bindRootsV env env.scopes varId roots = .ok () ∧
      after.eff = if varId < env.impl.params.size then
        { before.eff with rebinds := addTargets before.eff.rebinds [.param varId] } else before.eff := by
  change (do
    let roots ← rpExpr env expression
    bindRoots env env.scopes varId roots
    if varId < env.impl.params.size then
      modify fun state : RState => { state with eff := { state.eff with rebinds := addTargets state.eff.rebinds [.param varId] } })
    initial = .ok ((), after) at source
  obtain ⟨returned, middle, run, tail⟩ := (st_bind_ok _ _ _ _).mp source
  rw [operand] at run
  cases run
  obtain ⟨_, checkedState, binding, finish⟩ := (st_bind_ok _ _ _ _).mp tail
  obtain ⟨checked, stateEq⟩ := (liftV_ok _ _ _).mp binding
  have sameChecked : checkedState = before := stateEq
  subst checkedState
  refine ⟨checked, ?_⟩
  by_cases parameter : varId < env.impl.params.size
  · simp only [parameter, ite_true] at finish ⊢
    have update := (st_modify_ok _ _ _).mp finish
    exact congrArg (fun pair => pair.2.eff) update
  · simp only [parameter, ite_false] at finish ⊢
    have same := (st_pure_ok _ _ _).mp finish
    exact congrArg (fun pair => pair.2.eff) same


theorem effectStep_store_local {module : Core.Module} {ctx : Context} {impl : Impl}
    {vt : Array (Option VTy)} {provenance : Prov} {actual : Core.Eff}
    {address value : ValueId} {varId : VarId} {localVar : LocalVar} {org : OriginId}
    (variableRow : impl.vars[varId]? = some localVar) (reference : localVar.ty.isRefLike = true)
    (roots : rootsAt provenance.vals address = [.local varId])
    (owner : (ownerTy vt address).any Ty.isRefLike = true) :
    (lowerContextAt module ctx impl).effectStep (lower module) vt provenance actual
      (.eff (.store address value (some org))) =
      if varId < impl.params.size then
        { actual with rebinds := addTargets actual.rebinds [.param varId] } else actual := by
  have count : (lowerContextAt module ctx impl).params.length = impl.params.size := by
    simp [lowerContextAt, lowerImpl]
  by_cases parameter : varId < impl.params.size
  all_goals simp [Func.effectStep, roots, targetsOf, rootsTargets, rootTarget,
    List.filterMap_cons, List.filterMap_nil, lowerContext_slot (module := module) (ctx := ctx) variableRow,
    reference, count, parameter, owner, addTargets]


theorem effectStep_rebind_refines_from_source {env : PEnv} {varId : VarId} {expression : Expr}
    {org : OriginId} {roots : List RootRef} {initial before after : RState}
    {vt : Array (Option VTy)} {provenance : Prov} {address value : ValueId} {localVar : LocalVar}
    (variableRow : env.impl.vars[varId]? = some localVar) (reference : localVar.ty.isRefLike = true)
    (addressRoots : rootsAt provenance.vals address = [.local varId])
    (owner : (ownerTy vt address).any Ty.isRefLike = true)
    (operand : rpExpr env expression initial = .ok (roots, before))
    (source : rpStmt env (.rebind varId expression org) initial = .ok ((), after)) :
    EffectRefinement (lowerContextAt env.mod env.ctx env.impl)
      ((lowerContextAt env.mod env.ctx env.impl).effectStep (lower env.mod) vt provenance {}
        (.eff (.store address value (some org)))) after.eff := by
  rw [effectStep_store_local variableRow reference addressRoots owner,
    (rpStmt_rebind_contract operand source).2]
  split
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Func.storageTargets]
    · simp [Func.storageTargets]
    · simp [Func.storageTargets]
    · simp [Func.storageTargets]
    · intro target member
      have same : target = .param varId := by simpa [addTargets] using member
      subst target
      exact addTargets_right _ _ _ (by simp)
    · simp
    · simp
    · simp
  · exact effectRefinement_empty _ _

end Goose.Lower.Validation.SummaryPreservation
