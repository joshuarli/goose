import Goose.Lower.Validation.SummaryPreservationReplayLoopsEachSource
import Goose.Lower.Validation.SummaryPreservationEffectMonotonicity
import Goose.Lower.Validation.SummaryPreservationTypedSlots

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_each_children {env : PEnv} {variableId : VarId} {index : Option VarId}
    {view : View} {byRef : Bool} {body : Core.Block} {origin : OriginId} {before after : RState}
    (source : rpStmt env (.forEach variableId index view byRef body origin) before = .ok ((), after)) :
    ∃ viewStart sourceRoots viewState boundState bodyRoots bodyRange bodyState,
      rpView env view viewStart = .ok (sourceRoots, viewState) ∧
      (if byRef then bindRoots env (body.scope :: env.scopes) variableId sourceRoots else addReads sourceRoots)
        viewState = .ok ((), boundState) ∧
      rpBlockValue env [] body boundState = .ok ((bodyRoots, bodyRange), bodyState) ∧ after = bodyState := by
  simp only [rpStmt] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, viewStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨sourceRoots, viewState, viewReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
  cases byRef <;> simp only [Bool.false_eq_true, ite_false, ite_true] at source ⊢
  all_goals
    obtain ⟨_, boundState, binding, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨result, bodyState, bodyReplay, source⟩ := (st_bind_ok _ _ _ _).mp source
    exact ⟨viewStart, sourceRoots, viewState, boundState, result.1, result.2, bodyState,
      viewReplay, binding, bodyReplay, by simpa using ((liftV_ok _ _ _).mp source).2⟩

theorem each_binding_effects {env : PEnv} {variableId : VarId} {scopes : List Nat}
    {byRef : Bool} {sourceRoots : List RootRef} {before after : RState}
    (source : (if byRef then bindRoots env scopes variableId sourceRoots else addReads sourceRoots)
      before = .ok ((), after)) : EffectTargetsBelow before.eff after.eff := by
  cases byRef with
  | true =>
    have same := ((bindRoots_ok _ _ _ _ _ _).mp source).2
    dsimp only at same
    rw [same]
    exact ⟨EffLe.refl _, fun _ h => h, EffectFlagsLe.refl _⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false, addReads, addRoots] at source
    have same := congrArg Prod.snd ((st_modify_ok _ _ _).mp source)
    dsimp only at same
    rw [same]
    exact ⟨⟨fun t h => addTargets_left _ _ t h, fun _ h => h, fun _ h => h,
      fun _ h => h, fun h => h⟩, fun _ h => h, ⟨fun h => h, fun h => h⟩⟩

theorem each_view_effect_bound {env : PEnv} {variableId : VarId} {scopes : List Nat}
    {byRef : Bool} {sourceRoots bodyRoots : List RootRef} {body : Core.Block} {bodyRange : Nat × Nat}
    {viewState boundState bodyState after : RState} {func : Func} {target : Core.Eff}
    (binding : (if byRef then bindRoots env scopes variableId sourceRoots else addReads sourceRoots)
      viewState = .ok ((), boundState))
    (bodyReplay : rpBlockValue env [] body boundState = .ok ((bodyRoots, bodyRange), bodyState))
    (same : after = bodyState) (wholeEffect : EffectRefinement func after.eff target) :
    EffectRefinement func viewState.eff target := by
  have step := (each_binding_effects binding).refines (func := func)
  have body : EffectTargetsBelow boundState.eff bodyState.eff :=
    ⟨(rpBlockValue_mono bodyReplay).2, rpBlockValue_rebinds_mono bodyReplay, rpBlockValue_flags_mono bodyReplay⟩
  exact step.trans (body.refines.trans (by simpa only [same] using wholeEffect))

private theorem read_step_roots {sourceRoots : List RootRef} {before after : RState}
    (source : addReads sourceRoots before = .ok ((), after)) :
    ∀ item ∈ rootsTargets sourceRoots, item ∈ after.eff.reads := by
  simp only [addReads, addRoots] at source
  have same := congrArg Prod.snd ((st_modify_ok _ _ _).mp source)
  dsimp only at same
  rw [same]
  exact fun item member => addTargets_right _ _ item member

private theorem view_owner_reads {env : PEnv} {place : Place} {before after : RState} {sourceRoots : List RootRef}
    (source : rpView env (.of place) before = .ok (sourceRoots, after)) :
    ∀ item ∈ rootsTargets sourceRoots, item ∈ after.eff.reads := by
  simp only [rpView] at source
  obtain ⟨placeRoots, placeState, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, readState, reads, source⟩ := (st_bind_ok _ _ _ _).mp source
  have same := (st_pure_ok _ _ _).mp source
  cases same
  exact read_step_roots reads

theorem each_source_read_bound {env : PEnv} {variableId : VarId} {scopes : List Nat}
    {view : View} {byRef : Bool} {sourceRoots bodyRoots : List RootRef} {body : Core.Block}
    {bodyRange : Nat × Nat} {viewStart viewState boundState bodyState after : RState}
    {func : Func} {target : Core.Eff}
    (viewReplay : rpView env view viewStart = .ok (sourceRoots, viewState))
    (binding : (if byRef then bindRoots env scopes variableId sourceRoots else addReads sourceRoots)
      viewState = .ok ((), boundState))
    (bodyReplay : rpBlockValue env [] body boundState = .ok ((bodyRoots, bodyRange), bodyState))
    (same : after = bodyState) (wholeEffect : EffectRefinement func after.eff target)
    (reads : byRef = false ∨ ∃ place, view = .of place) :
    ∀ item ∈ func.storageTargets (rootsTargets sourceRoots), item ∈ func.storageTargets target.reads := by
  have bodyEffects := (rpBlockValue_mono bodyReplay).2
  have raw : ∀ item ∈ rootsTargets sourceRoots, item ∈ after.eff.reads := by
    rw [same]
    rcases reads with rfl | ⟨place, rfl⟩
    · exact fun item member => bodyEffects.1 item (read_step_roots binding item member)
    · have toBinding := (each_binding_effects binding).1
      exact fun item member => bodyEffects.1 item (toBinding.1 item (view_owner_reads viewReplay item member))
  exact fun item member => wholeEffect.reads item (storageTargets_mono raw item member)

theorem each_source_binding_bound {env : PEnv} {variableId : VarId} {scopes : List Nat}
    {sourceRoots actual : List RootRef} {before after : RState} {localVar : LocalVar}
    (annotations : checkAnnotationShape env.mod env.impl env.ctx = .ok ())
    (row : env.impl.vars[variableId]? = some localVar) (ordinary : localVar.ty.isRefSlice = false)
    (binding : bindRoots env scopes variableId sourceRoots before = .ok ((), after))
    (refined : RootsRefine (lowerContextAt env.mod env.ctx env.impl) actual sourceRoots) :
    ∀ root ∈ actual, root ∈ rootsAt (typedContextSlotUpper env.mod env.ctx env.impl) variableId :=
  bindRootsV_typed_slot_bound annotations row ordinary ((bindRoots_ok _ _ _ _ _ _).mp binding).1 refined

#print axioms rpStmt_each_children
#print axioms each_source_read_bound
#print axioms each_source_binding_bound

end Goose.Lower.Validation.SummaryPreservation
