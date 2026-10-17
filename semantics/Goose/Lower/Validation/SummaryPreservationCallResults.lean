import Goose.Lower.Validation.SummaryPreservationCallSource
import Goose.Lower.Validation.SummaryPreservationCalls
import Goose.Lower.Validation.SummaryPreservationResultBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem callResultRoots_mapping {module : Core.Module} {ctx : Context} {callee : Impl}
    {args : List (List RootRef)} {roots : List RootRef}
    (implOk : ImplOk module callee) (contextOk : CtxOk module callee ctx)
    (returned : callResultRoots callee ctx args = .ok roots) :
    mapResultRoots args [] (ctx.resultRoots[0]?.getD []) = .ok roots := by
  obtain ⟨_, _, _, shape⟩ := implOk.body
  rcases shape with ⟨emptyResults, _⟩ | ⟨ty, resultRow, _⟩
  · have resultCount : callee.results.size = 0 := by
      simpa using congrArg List.length emptyResults
    have contextEmpty : ctx.resultRoots = [] :=
      List.length_eq_zero_iff.mp (contextOk.resultLen.trans resultCount)
    simp only [callResultRoots, emptyResults, contextEmpty] at returned
    cases returned
    simp [contextEmpty, mapResultRoots]
    rfl
  · have resultCount : callee.results.size = 1 := by
      simpa using congrArg List.length resultRow
    obtain ⟨declared, contextRow⟩ := List.length_eq_one_iff.mp (contextOk.resultLen.trans resultCount)
    simp only [callResultRoots, resultRow, contextRow] at returned
    cases reference : ty.isRefLike with
    | true => simpa [reference, contextRow] using returned
    | false =>
      have declaredEmpty := (Core.Declarative.declaredResults_sound module callee ctx
        contextOk.resultShape).2 ty declared (by simp [resultRow, contextRow])
      have empty : declared = [] := declaredEmpty.1 reference
      simp only [reference, ite_false] at returned
      cases returned
      simp [contextRow, empty, mapResultRoots]
      rfl

theorem rootsOfDef_call_from_source {env : PEnv} {calleeId : ContextId}
    {ctx : Context} {callee : Impl} {caller : Func} {provenance : Prov}
    {vt : Array (Option VTy)} {results : Array (List RootRef)} {args : List ValueId}
    {sourceArgs : List (List RootRef)} {roots : List RootRef} {before after : RState}
    {result : ValueId} {origin : Option OriginId}
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[calleeId]? = some ctx)
    (implLookup : env.mod.impls[ctx.impl]? = some callee)
    (bounded : RootsBelow results (moduleResultUpper env.mod))
    (argumentCount : args.length = callee.params.size)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value →
      ∃ sourceRoots, sourceArgs[index]? = some sourceRoots ∧
        RootsRepresent caller (rootsAt provenance.vals value) sourceRoots)
    (replay : rpCall env calleeId sourceArgs before = .ok (roots, after)) :
    RootsRepresent caller
      (rootsOfDef results vt caller provenance result (.call calleeId args origin)) roots := by
  have moduleOk := validate_modOk env.mod accepted
  have implOk := moduleOk.impl ctx.impl callee implLookup
  obtain ⟨checkedCallee, checkedLookup, contextOk⟩ := moduleOk.ctx calleeId ctx contextLookup
  rw [implLookup] at checkedLookup
  cases checkedLookup
  have sourceContract := rpCall_replay_contract contextLookup implLookup replay
  apply rootsOfDef_call_represent (candidateResult_represent bounded contextLookup implLookup)
    (lowerContextAt_parameterRoots_closed accepted contextLookup implLookup) arguments
  · intro index bound
    have parameterBound : index < callee.params.size := by simpa only [argumentCount] using bound
    exact checkArgRoots_parameterContract accepted contextLookup implLookup parameterBound
      ((forAll_ok _ _).mp sourceContract.1 index (List.mem_range.mpr parameterBound))
  · exact callResultRoots_mapping implOk contextOk sourceContract.2.2

end Goose.Lower.Validation.SummaryPreservation
