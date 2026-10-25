import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalRoot
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalFinish
import Goose.Lower.Validation.SummaryPreservationEntryBindingFacts
import Goose.Lower.Validation.SummaryPreservationSourceContextEnvironment
import Goose.Lower.Validation.SummaryPreservationSourceBodyResults
import Goose.Lower.Validation.SummaryPreservationSourceScopeBoundsAccepted
import Goose.Lower.Validation.SummaryPreservationReplayFunctionFinish
import Goose.Lower.Validation.ValidationTypedModuleTables
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlContracts
import Goose.Lower.Validation.SourceOccurrenceFinishActions
import Goose.Lower.Validation.SourceOccurrenceFinishEntry
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlRecipeFrames
import Goose.Lower.Finish

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

def CanonicalContextOccurrenceReplayProduced (module : Core.Module) (ctx : Context) (impl : Impl)
    (results : Array (List RootRef)) : Prop :=
  ∃ roots range after upper,
    rpBlockValue ⟨module, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ = .ok ((roots, range), after) ∧
    ReplayBuilder (lower module) results ((lowerContextAt module ctx impl).valueTypes (lower module))
      (lowerContextAt module ctx impl) after.eff (lowerEnv module impl.vars impl.results.toList)
      (lowerContextAt module ctx impl).scopes.size (typedContextSlotUpper module ctx impl)
      (cfg_implState module impl) upper ∧
    BuilderReturnsBound upper (contextTypedResultUpper module ctx) (cfg_implState module impl) ∧
    (∀ index, index < impl.params.size → rootsAt upper.vals index =
      rootsAt (entryRootValues (impl.params.toList.map fun parameter => .data (tyOfVar impl parameter.var))) index) ∧
    OccurrenceLedger ⟨module, impl, ctx, []⟩ (.block impl.body) (lowerContextAt module ctx impl)
      ((lowerContextAt module ctx impl).valueTypes (lower module)) upper initState (cfg_implState module impl) ∧
    CanonicalOccurrenceSitesBuilder (contextReplayFragment module impl) (contextInitial module impl) (contextInitial module impl) ⟨module, impl, ctx, []⟩ (.block impl.body) []
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
      (lowerContextAt module ctx impl) ((lowerContextAt module ctx impl).valueTypes (lower module)) upper

theorem canonical_context_occurrence_replay_produced_of_body {module : Core.Module} {ctx : Context} {impl : Impl} {context : ContextId}
    {results : Array (List RootRef)}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (bodyReplay : ∀ roots range after,
      rpBlockValue ⟨module, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ = .ok ((roots, range), after) →
      CanonicalBlockOccurrenceReplayAt (contextReplayFragment module impl) (contextInitial module impl) (contextInitial module impl) (implEnv module impl) ⟨module, impl, ctx, []⟩ results
        ((lowerContextAt module ctx impl).valueTypes (lower module)) after.eff
        (lowerContextAt module ctx impl).scopes.size (.block impl.body) [] none
        (contextEntryBindings impl (lowerEnv module impl.vars impl.results.toList)) impl.body.value.isSome impl.body
        (entryReplayState (impl.params.toList.map fun parameter => .data (tyOfVar impl parameter.var))
          (lowerEnv module impl.vars impl.results.toList))
        ⟨typedContextSlotUpper module ctx impl,
          entryRootValues (impl.params.toList.map fun parameter => .data (tyOfVar impl parameter.var))⟩) :
    CanonicalContextOccurrenceReplayProduced module ctx impl results := by
  let env : PEnv := ⟨module, impl, ctx, []⟩
  let le := lowerEnv module impl.vars impl.results.toList
  let types := impl.params.toList.map fun p => VTy.data (tyOfVar impl p.var)
  let entry := entryReplayState types le
  let startUpper : Prov := ⟨typedContextSlotUpper module ctx impl, entryRootValues types⟩
  let bindings := contextEntryBindings impl le
  let body := lowerBlock none bindings impl.body.value.isSome impl.body le entry
  let vt := (lowerContextAt module ctx impl).valueTypes (lower module)
  have source : SourceContextEnvironment (implEnv module impl) env context :=
    ⟨accepted, ⟨rfl, rfl⟩, rfl, contextRow, implementationRow⟩
  obtain ⟨type, finish, typed, _⟩ := (validate_modOk module accepted).impl ctx.impl impl implementationRow |>.body
  obtain ⟨roots, range, after, replayed, _, _⟩ := source.contextOk.body
  have whole : cfg_implState module impl = (Goose.Lower.finishFunction impl body.1 le body.2).2 := by
    simp only [cfg_implState, cfg_implAction, bind_run, setCur_run, body, bindings, contextEntryBindings,
      entry, entryReplayState, types, le, lowerBlock_value_want]
  have nativeFinal : NativeRows vt (cfg_implState module impl) := by
    rw [show vt = (cfg_implState module impl).vals from lowerContext_valueTypes_of_accepted accepted implementationRow]
    exact NativeRows.refl _
  have nativeBody : NativeRows vt body.2 := by
    rw [whole] at nativeFinal
    exact nativeFinal.of_prefix (ReplayBuilder.types_finishFunction impl body.1 le body.2 _ _ rfl)
  have metadataFinal : SourceCanonicalRootFloors.RecipeMetadataProjects env (.block impl.body)
      (lowerContextAt module ctx impl) (cfg_implState module impl) :=
    SourceCanonicalRootFloors.lowerContextAt_recipeMetadataProjects module ctx impl
  have metadataBody : SourceCanonicalRootFloors.RecipeMetadataProjects env (.block impl.body)
      (lowerContextAt module ctx impl) body.2 := by
    rw [whole] at metadataFinal
    exact metadataFinal.of_advance (advB_finishFunction impl body.1 le body.2 _ _ rfl)
  have continuationBody : NativeBuilderContinuation (lowerContextAt module ctx impl) body.2 := by
    apply NativeBuilderContinuation.context
    rw [whole]
    exact (advB_finishFunction impl body.1 le body.2 _ _ rfl).ext
  have ready := lowerContext_entryReplayBuilder module ctx impl results vt after.eff (lowerContextAt module ctx impl).scopes.size
  have scopes := accepted_context_scope_bounds accepted contextRow implementationRow
  obtain ⟨upper, bodyReady, bodyValue, retained, transferred, bodyLedger, bodySites⟩ :=
    bodyReplay roots range after replayed ⟨[], .here _⟩
      ⟨[],SourceLoweringAt.here _ _ _⟩
      type impl.params.size finish ⟨impl.params.size, {}⟩ after roots range typed replayed
      (EffectRefinement.refl _ after.eff) scopes
      (contextEntryBindings_metadata le accepted implementationRow)
      (fun _ => contextEntryBindings_values le accepted implementationRow)
      (contextEntryBindings_roots le accepted implementationRow source.contextOk)
      (by intro _ scope member; simp [entryReplayState, newBlock_run_general, initState] at member)
      ready (CanonicalOccurrenceSitesBuilder.initial (entryReplayState_occurrenceSites env (.block impl.body) [] types le _ vt startUpper))
      (by intro target member; cases member) (entryReplayState_generated types le)
      trivial trivial trivial (by intro target member; cases member) nativeBody metadataBody continuationBody
  have prior : BuilderReturnsBound startUpper (contextTypedResultUpper module ctx) entry := by
    intro value origin member
    rw [entryReplayState_instructions types le] at member
    cases member
  have bodyReturns := transferred.apply_expected prior
  obtain ⟨finished, finishReturns⟩ := bodyReady.finishFunction impl body.1 (contextTypedResultUpper module ctx)
    (fun live present => (bodyValue present live).bound)
    (fun live present => source_body_result_upper accepted contextRow implementationRow typed replayed present
      (bodyValue present live))
  have entryLedger : OccurrenceLedger env (.block impl.body) (lowerContextAt module ctx impl) vt upper initState entry :=
    entryReplayState_emitsOnly _ types le
  have finalLedger := OccurrenceLedger.finishFunction (le := le) (entryLedger.trans bodyLedger) impl body.1 rfl
  have finalSites := bodySites.finishFunction impl body.1
  refine ⟨roots, range, after, upper, replayed, ?_, ?_, ?_, ?_, ?_⟩
  · rw [whole]
    exact finished
  · rw [whole]
    exact finishReturns.apply_expected bodyReturns
  · intro index bound
    apply retained index
    simpa only [startUpper, entryRootValues, Array.size_mapIdx, List.size_toArray, List.length_map,
      Array.length_toList, types] using bound

  · rw [whole]
    exact finalLedger
  · rw [whole]
    exact finalSites

#print axioms canonical_context_occurrence_replay_produced_of_body

end Goose.Lower.Validation.SourceReplacementWriterLedger
