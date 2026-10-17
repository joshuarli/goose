import Goose.Lower.Validation.SummaryPreservationSourceGlobalEnvironment
import Goose.Lower.Validation.SummaryPreservationEntryBindingFacts
import Goose.Lower.Validation.SummaryPreservationGlobalEntryFrame
import Goose.Lower.Validation.SummaryPreservationSourceScopeBoundsAccepted
import Goose.Lower.Validation.SourceGlobalReadShape
import Goose.Lower.Validation.SummaryPreservationReturnLedger
import Goose.Lower.Validation.ValidationTypedModuleTables
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.SourceOccurrenceFinishActions
import Goose.Lower.Validation.SourceOccurrenceFinishEntry
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

def GlobalOccurrenceReplayProduced (module : Core.Module) (global : Core.Global)
    (results : Array (List RootRef)) : Prop :=
  ∃ roots after upper,
    rpExpr ⟨module, initImpl, initContext, []⟩ global.init ⟨0, {}⟩ = .ok (roots, after) ∧
    ReplayBuilder (lower module) results ((lowerGlobal module global).init.valueTypes (lower module))
      (lowerGlobal module global).init after.eff (lowerEnv module #[] [global.ty])
      (lowerGlobal module global).init.scopes.size #[] (cfg_globalState module global) upper ∧
    BuilderReturnsBound upper [] (cfg_globalState module global) ∧
    OccurrenceLedger ⟨module, initImpl, initContext, []⟩ (.expression global.init) (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module)) upper initState (cfg_globalState module global) ∧
    OccurrenceSitesBuilder ⟨module, initImpl, initContext, []⟩ (.expression global.init) []
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper

theorem global_occurrence_replay_produced_of_expression {module : Core.Module} {global : Core.Global} {index : GlobalId}
    {results : Array (List RootRef)} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global)
    (expressionReplay : ∀ roots after,
      rpExpr ⟨module, initImpl, initContext, []⟩ global.init ⟨0, {}⟩ = .ok (roots, after) →
      GlobalExpressionOccurrenceReplayAt (initEnv module index) ⟨module, initImpl, initContext, []⟩ results
        ((lowerGlobal module global).init.valueTypes (lower module)) (lowerGlobal module global).init
        [global.ty] #[] after.eff (lowerGlobal module global).init.scopes.size (.expression global.init) [] global.init
        (entryReplayState [] (lowerEnv module #[] [global.ty])) ⟨#[], entryRootValues []⟩) :
    GlobalOccurrenceReplayProduced module global results := by
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
    ⟨accepted, ⟨rfl, rfl⟩, rfl, rfl, rfl, global_initializer_parameterRoots_identity module global⟩
  have whole : cfg_globalState module global =
      (Goose.Lower.emitTerm (.ret [lowered.1] (some global.org)) le lowered.2).2 := by
    simp only [cfg_globalState, cfg_globalAction, bind_run, setCur_run, lowered, entry, entryReplayState, le]
  have nativeFinal : NativeRows vt (cfg_globalState module global) := by
    rw [show vt = (cfg_globalState module global).vals from lowerGlobal_valueTypes_of_accepted accepted globalRow]
    exact NativeRows.refl _
  have nativeValue : NativeRows vt lowered.2 := by
    rw [whole] at nativeFinal
    exact nativeFinal.of_prefix (types_emitTerm (.ret [lowered.1] (some global.org)) le lowered.2 _ _ rfl)
  have metadataFinal : SourceCanonicalRootFloors.RecipeMetadataProjects env (.expression global.init)
      (lowerGlobal module global).init (cfg_globalState module global) :=
    SourceCanonicalRootFloors.lowerGlobal_recipeMetadataProjects module global
  have metadataValue : SourceCanonicalRootFloors.RecipeMetadataProjects env (.expression global.init)
      (lowerGlobal module global).init lowered.2 := by
    rw [whole] at metadataFinal
    exact metadataFinal.of_advance (advB_emitTerm (.ret [lowered.1] (some global.org)) le lowered.2 _ _ rfl)
  have continuationValue : NativeBuilderContinuation (lowerGlobal module global).init lowered.2 := by
    apply NativeBuilderContinuation.global
    rw [whole]
    exact (advB_emitTerm (.ret [lowered.1] (some global.org)) le lowered.2 _ _ rfl).ext
  have initialReady := entryReplayBuilder (lower module) results vt (lowerGlobal module global).init
    after.eff le (lowerGlobal module global).init.scopes.size #[] []
  have scopes := accepted_global_scope_bounds accepted globalRow
  obtain ⟨upper, ready, value, retained, expressionLedger, expressionSites⟩ :=
    expressionReplay roots after replayed ⟨[], .here _⟩
      global.ty 0 finish ⟨0, {}⟩ after roots typed replayed (EffectRefinement.refl _ after.eff)
      initialReady (entryReplayState_occurrenceSites env (.expression global.init) [] [] le _ vt startUpper)
      (by intro target member; cases member) (entryReplayState_generated [] le) nativeValue metadataValue continuationValue
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
  have entryLedger : OccurrenceLedger env (.expression global.init) (lowerGlobal module global).init vt upper initState entry :=
    entryReplayState_emitsOnly _ [] le
  have completedLedger := (entryLedger.trans expressionLedger).trans
    (emitsOnly_emitTerm (.ret [lowered.1] (some global.org))
      (InstructionOccurrences.term env (.expression global.init) (lowerGlobal module global).init vt upper _) le lowered.2 _ _ rfl)
  have completedSites := expressionSites.of_emits
    (emitsOnly_emitTerm (.ret [lowered.1] (some global.org)) (by trivial) le lowered.2 _ _ rfl)
    (types_emitTerm _ le lowered.2 _ _ rfl)
    (ReplacementIntervalsPreserved.of_run (generatedTargetFrame_emitNoSuccessors none
      (.ret [lowered.1] (some global.org)) rfl) rfl) (Nat.le_refl _) (fun _ _ => rfl)
  refine ⟨roots, after, upper, replayed, ?_, ?_, ?_, ?_⟩
  · rw [whole]
    exact finalReady
  · rw [whole]
    exact returned

  · rw [whole]
    exact completedLedger
  · rw [whole]
    exact completedSites

#print axioms global_occurrence_replay_produced_of_expression

end Goose.Lower.Validation.ReplacementContentFlowSource
