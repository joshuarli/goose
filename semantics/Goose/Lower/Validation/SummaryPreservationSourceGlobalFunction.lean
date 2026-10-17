import Goose.Lower.Validation.SummaryPreservationSourceGlobalReplay
import Goose.Lower.Validation.SummaryPreservationSourceFunction
import Goose.Lower.Validation.SummaryPreservationGlobalEntryFrame
import Goose.Lower.Validation.SummaryPreservationReplayFinished
import Goose.Lower.Validation.SourceGlobalReadShape

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def GlobalReplayProduced (module : Core.Module) (global : Core.Global)
    (results : Array (List RootRef)) : Prop :=
  ∃ roots after upper,
    rpExpr ⟨module, initImpl, initContext, []⟩ global.init ⟨0, {}⟩ = .ok (roots, after) ∧
    ReplayBuilder (lower module) results ((lowerGlobal module global).init.valueTypes (lower module))
      (lowerGlobal module global).init after.eff (lowerEnv module #[] [global.ty])
      (lowerGlobal module global).init.scopes.size #[] (cfg_globalState module global) upper ∧
    BuilderReturnsBound upper [] (cfg_globalState module global)

theorem accepted_global_replay_produced {module : Core.Module} {global : Core.Global} {index : GlobalId}
    {results : Array (List RootRef)} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global)
    (bounded : RootsBelow results (moduleTypedResultUpper module)) : GlobalReplayProduced module global results := by
  let env : PEnv := ⟨module, initImpl, initContext, []⟩
  let le := lowerEnv module #[] [global.ty]
  let entry := entryReplayState [] le
  let startUpper : Prov := ⟨#[], entryRootValues []⟩
  let lowered := lowerExpr global.init le entry
  let vt := (lowerGlobal module global).init.valueTypes (lower module)
  have checked := (validate_modOk module accepted).glob index global globalRow
  obtain ⟨finish, typed⟩ := checked.init
  obtain ⟨roots, after, replayed, _, _⟩ := checked.roots
  have source : SourceGlobalEnvironment (initEnv module index) env (lowerGlobal module global).init :=
    ⟨accepted, ⟨rfl, rfl⟩, rfl, rfl, global_initializer_parameterRoots_closed module global⟩
  have whole : cfg_globalState module global =
      (Goose.Lower.emitTerm (.ret [lowered.1] (some global.org)) le lowered.2).2 := by
    simp only [cfg_globalState, cfg_globalAction, bind_run, setCur_run, lowered, entry, entryReplayState, le]
  have nativeFinal : NativeRows vt (cfg_globalState module global) := by
    rw [show vt = (cfg_globalState module global).vals from lowerGlobal_valueTypes_of_accepted accepted globalRow]
    exact NativeRows.refl _
  have nativeValue : NativeRows vt lowered.2 := by
    rw [whole] at nativeFinal
    exact nativeFinal.of_prefix (types_emitTerm (.ret [lowered.1] (some global.org)) le lowered.2 _ _ rfl)
  have initialReady := entryReplayBuilder (lower module) results vt (lowerGlobal module global).init
    after.eff le (lowerGlobal module global).init.scopes.size #[] []
  have scopes := accepted_global_scope_bounds accepted globalRow
  obtain ⟨upper, ready, value, retained⟩ :=
    global_source_expression_replay global.init source bounded scopes entry startUpper
      global.ty 0 finish ⟨0, {}⟩ after roots typed replayed (EffectRefinement.refl _ after.eff)
      initialReady (entryReplayState_generated [] le) nativeValue
  have originBound := checkGlobal_origin_bound (validate_global_checks accepted globalRow)
  have finalReady := ready.emitTerm (.ret [lowered.1] (some global.org))
    (by
      intro live
      apply Inst.SymbolsWithin.term
      · intro operand member
        have same : operand = lowered.1 := by simpa only [Term.uses, List.mem_singleton] using member
        rw [same]
        exact (value live).bound
      · intro origin same
        have identity : origin = global.org := (Option.some.inj same).symm
        simpa only [identity, le, lowerEnv] using originBound
      · simp [Term.successors])
    (by intros; trivial) (by intro _; exact effectRefinement_empty _ _)
  have prior : BuilderReturnsBound startUpper [] entry := by
    intro value origin member
    rw [entryReplayState_instructions [] le] at member
    cases member
  have valueReturns := prior.expression initialReady.symbols initialReady.roots.valueSize typed rfl retained
  have returned : BuilderReturnsBound upper []
      (Goose.Lower.emitTerm (.ret [lowered.1] (some global.org)) le lowered.2).2 := by
    cases current : lowered.2.cur with
    | none =>
      rw [emitTerm_none _ _ current]
      exact valueReturns
    | some block =>
      have live : lowered.2.cur.isSome = true := by simp [current]
      apply valueReturns.emitTerm ready.current (.ret [lowered.1] (some global.org))
      intro returned origin same root member
      have identity : returned = lowered.1 := (List.singleton_inj.mp (Term.ret.inj same).1).symm
      subst returned
      have scalar : rootsAt upper.vals lowered.1 = [] := (value live).scalar checked.ty.2
      rw [scalar] at member
      cases member
  refine ⟨roots, after, upper, replayed, ?_, ?_⟩
  · rw [whole]
    exact finalReady
  · rw [whole]
    exact returned

theorem accepted_global_returnedRoots_empty {module : Core.Module} {global : Core.Global} {index : GlobalId}
    {candidate : Array (List RootRef)} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global)
    (bounded : RootsBelow candidate (moduleTypedResultUpper module)) (rootCount : Nat) :
    (lowerGlobal module global).init.returnedRoots
      ((lowerGlobal module global).init.provenance candidate
        ((lowerGlobal module global).init.valueTypes (lower module)) rootCount) = [] := by
  obtain ⟨roots, after, upper, replayed, ready, returned⟩ :=
    accepted_global_replay_produced accepted globalRow bounded
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro root member
  have impossible := ready.finished_returnedRoots (cfg_global_blocks module global)
    (global_provenance_seed module global _ upper) returned rootCount root member
  cases impossible

theorem accepted_global_effects_refinement {module : Core.Module} {global : Core.Global} {index : GlobalId}
    {candidate : Array (List RootRef)} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global)
    (bounded : RootsBelow candidate (moduleTypedResultUpper module)) (rootCount : Nat) :
    ∃ roots after,
      rpExpr ⟨module, initImpl, initContext, []⟩ global.init ⟨0, {}⟩ = .ok (roots, after) ∧
      EffectRefinement (lowerGlobal module global).init
        ((lowerGlobal module global).init.effects (lower module)
          ((lowerGlobal module global).init.provenance candidate
            ((lowerGlobal module global).init.valueTypes (lower module)) rootCount)) after.eff := by
  obtain ⟨roots, after, upper, replayed, ready, returned⟩ :=
    accepted_global_replay_produced accepted globalRow bounded
  exact ⟨roots, after, replayed, ready.finished_computed_effects (cfg_global_blocks module global) rfl
    (global_provenance_seed module global _ upper) rootCount⟩

#print axioms accepted_global_returnedRoots_empty
#print axioms accepted_global_effects_refinement

#print axioms accepted_global_replay_produced

end Goose.Lower.Validation.SummaryPreservation
