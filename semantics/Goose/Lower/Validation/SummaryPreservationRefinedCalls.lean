import Goose.Lower.Validation.SummaryPreservationRootRefinement
import Goose.Lower.Validation.SummaryPreservationCalls
import Goose.Lower.Validation.SummaryPreservationCallResults
import Goose.Lower.Validation.SummaryPreservationRefinedResultBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rootsOfDef_call_refines {caller callee : Func} {provenance : Prov}
    {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {function : FnId} {result : ValueId} {args : List ValueId} {origin : Option OriginId}
    {sourceArgs : List (List RootRef)} {declared sourceResult : List RootRef}
    (returns : RootsRefine callee (rootsAt results function) declared)
    (calleeRoots : ParameterRootsClosed callee)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value →
      ∃ roots, sourceArgs[index]? = some roots ∧
        RootsRefine caller (rootsAt provenance.vals value) roots)
    (argumentContract : ∀ index, index < args.length → callee.parameterRoots index = [.param index] ∨
      ∀ root ∈ sourceArgs[index]?.getD [], root ∈ callee.parameterRoots index)
    (sourceMapping : mapResultRoots sourceArgs [] declared = .ok sourceResult) :
    RootsRefine caller
      (rootsOfDef results vt caller provenance result (.call function args origin)) sourceResult := by
  have mapped := (mapResultRoots_ok sourceArgs declared [] sourceResult sourceMapping).2
  intro root member
  obtain ⟨returned, returnedMember, rootMember⟩ := List.mem_flatMap.mp member
  cases returned with
  | «local» slot => simp at rootMember
  | global global =>
    have declaredGlobal : RootRef.global global ∈ declared := by
      rcases returns (.global global) returnedMember with literal | expanded
      · exact literal
      · exact expanded (.global global) (by simp [Func.expandParameterRoot])
    have rootEq : root = .global global := List.mem_singleton.mp rootMember
    subst root
    exact Or.inl (mapped (.global global) declaredGlobal)
  | param index =>
    cases argument : args[index]? with
    | none => simp [argument] at rootMember
    | some value =>
      simp only [argument] at rootMember
      obtain ⟨sourceRoots, sourceLookup, refined⟩ := arguments index value argument
      by_cases declaredParam : RootRef.param index ∈ declared
      · obtain ⟨roots, lookup, subset⟩ := mapped (.param index) declaredParam
        rw [sourceLookup] at lookup
        cases lookup
        exact refined.source_mono subset root rootMember
      · have expanded : ∀ concrete ∈ callee.parameterRoots index, concrete ∈ declared := by
          rcases returns (.param index) returnedMember with literal | expanded
          · exact False.elim (declaredParam literal)
          · exact expanded
        have sourceBound : ∀ concrete ∈ sourceRoots, concrete ∈ callee.parameterRoots index := by
          rcases argumentContract index (List.getElem?_eq_some_iff.mp argument).1 with generic | subset
          · have own : RootRef.param index ∈ callee.parameterRoots index := by simp [generic]
            exact False.elim (declaredParam (expanded _ own))
          · simpa [sourceLookup] using subset
        have sourceMapped : ∀ concrete ∈ sourceRoots, concrete ∈ sourceResult := by
          intro concrete sourceMember
          have calleeMember := sourceBound concrete sourceMember
          have declaredRoot := expanded concrete calleeMember
          rcases calleeRoots index concrete calleeMember with sameParam | ⟨global, sameGlobal⟩
          · rw [sameParam] at declaredRoot
            exact False.elim (declaredParam declaredRoot)
          · subst concrete
            exact mapped (.global global) declaredRoot
        exact refined.source_mono sourceMapped root rootMember

theorem rootsOfDef_call_refines_from_source {env : PEnv} {calleeId : ContextId}
    {ctx : Context} {callee : Impl} {caller : Func} {provenance : Prov}
    {vt : Array (Option VTy)} {results : Array (List RootRef)} {args : List ValueId}
    {sourceArgs : List (List RootRef)} {roots : List RootRef} {before after : RState}
    {result : ValueId} {origin : Option OriginId}
    (accepted : Core.validate env.mod = .ok ())
    (contextLookup : env.mod.contexts[calleeId]? = some ctx)
    (implLookup : env.mod.impls[ctx.impl]? = some callee)
    (bounded : RootsBelow results (moduleRefinedResultUpper env.mod))
    (argumentCount : args.length = callee.params.size)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value →
      ∃ sourceRoots, sourceArgs[index]? = some sourceRoots ∧
        RootsRefine caller (rootsAt provenance.vals value) sourceRoots)
    (replay : rpCall env calleeId sourceArgs before = .ok (roots, after)) :
    RootsRefine caller
      (rootsOfDef results vt caller provenance result (.call calleeId args origin)) roots := by
  have moduleOk := validate_modOk env.mod accepted
  have implOk := moduleOk.impl ctx.impl callee implLookup
  obtain ⟨checkedCallee, checkedLookup, contextOk⟩ := moduleOk.ctx calleeId ctx contextLookup
  rw [implLookup] at checkedLookup
  cases checkedLookup
  have sourceContract := rpCall_replay_contract contextLookup implLookup replay
  apply rootsOfDef_call_refines (candidateResult_refines bounded contextLookup implLookup)
    (lowerContextAt_parameterRoots_closed accepted contextLookup implLookup) arguments
  · intro index bound
    have parameterBound : index < callee.params.size := by simpa only [argumentCount] using bound
    exact checkArgRoots_parameterContract accepted contextLookup implLookup parameterBound
      ((forAll_ok _ _).mp sourceContract.1 index (List.mem_range.mpr parameterBound))
  · exact callResultRoots_mapping implOk contextOk sourceContract.2.2

end Goose.Lower.Validation.SummaryPreservation
