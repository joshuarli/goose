import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceStorageAssign
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceAccessReadLocal

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem referenceSlicePlaceOccurrence_of_context {typingEnv : TEnv} {env : PEnv} {context : ContextId}
    {results : Array (List RootRef)} {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat}
    {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}
    (source : SourceContextEnvironment typingEnv env context) :
    ReferenceSlicePlaceOccurrenceReplayAt env results vt (lowerContextAt env.mod env.ctx env.impl)
      env.impl.results.toList (typedContextSlotUpper env.mod env.ctx env.impl) target scopeCount
      siteRoot siteTargets initial upper := by
  intro index localVar variableRow reference before after roots replay ready sites metadata
  obtain ⟨param, parameterRow, _identity, _mode⟩ :=
    accepted_refSlice_parameter source.accepted source.implementationRow variableRow reference
  refine ⟨(Array.getElem?_eq_some_iff.mp parameterRow).1, ?_, ?_⟩
  · simp [PEnv.isRefSliceVar, variableRow, reference]
  · exact occurrenceReplay_referenceSlicePlace source variableRow reference replay ready sites metadata

theorem referenceSlicePlaceOccurrence_of_empty_variables {env : PEnv} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)}
    {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId}
    {initial : LS} {upper : Prov} (empty : env.impl.vars = #[]) :
    ReferenceSlicePlaceOccurrenceReplayAt env results vt func returnTypes slots target scopeCount
      siteRoot siteTargets initial upper := by
  intro index localVar variableRow
  simp [empty] at variableRow

#print axioms referenceSlicePlaceOccurrence_of_context
#print axioms referenceSlicePlaceOccurrence_of_empty_variables

end Goose.Lower.Validation.ReplacementContentFlowSource
