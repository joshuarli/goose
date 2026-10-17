import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsPhysicalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceArgumentsGlobal
import Goose.Lower.Validation.SourceRootShapeReads

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty}
  {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat}
  {siteRoot anchor : DemandNode} {siteTargets : List BlockId}

theorem typedEmptyPhysicalArgumentOccurrence (tables : SourceRootTables typingEnv env)
    (empty : typingEnv.vars = #[]) (argument : Arg)
    (expressionChild : ∀ expression, argument = .byVal expression → ∀ state provenance,
      GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
        expression state provenance)
    (placeChild : ∀ mutability place, argument = .byRef mutability place → ∀ state provenance,
      GlobalPlaceOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets
        place state provenance) :
    ∀ initial upper, PhysicalArgumentOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount
      siteRoot siteTargets anchor argument initial upper := by
  intro initial upper anchored path start finish before after sourceRoots typed replay wholeEffect
    ready sites targets generated native metadata continuation
  obtain ⟨next, completed, returned, retained, ledger, nextSites⟩ :=
    typedGlobalArgumentOccurrence argument expressionChild placeChild initial upper
      anchored path start finish before after sourceRoots typed replay wholeEffect ready sites targets generated native metadata continuation
  refine ⟨next, completed, returned, retained, ledger, nextSites, ?_⟩
  intro live mutability place same shaped
  cases same
  obtain ⟨info, placeTyped⟩ := typed
  obtain ⟨index, localPlace | ⟨contents, reference⟩⟩ := shaped
  · subst place
    have bound := Core.tyPlace_var_success_bound placeTyped
    simp [empty] at bound
  · simp [PEnv.isRefSliceVar, tables.variablesEq, empty] at reference

#print axioms typedEmptyPhysicalArgumentOccurrence

end Goose.Lower.Validation.ReplacementContentFlowSource
