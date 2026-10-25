import Goose.Lower.Validation.ReplacementContentFlowSourceCalls
import Goose.Lower.Validation.SummaryPreservationCalls
import Goose.Lower.Validation.SummaryPreservationCallSource

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model
open SummaryPreservation

theorem accepted_call_argument_globals {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {caller : Func} {sourceArgs : List (List RootRef)} {index : Nat}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (bounded : index < impl.params.size)
    (checked : checkArgRoots impl ctx sourceArgs index = .ok ())
    (specialized : RootRef.param index ∉ (lowerContextAt module ctx impl).parameterRoots index) :
    ∀ root ∈ (sourceArgs[index]?.getD []).flatMap caller.expandParameterRoot,
      root ∈ (lowerContextAt module ctx impl).parameterRoots index := by
  have permitted := checkArgRoots_parameterContract accepted contextRow implementationRow bounded checked
  have declared : ∀ root ∈ sourceArgs[index]?.getD [],
      root ∈ (lowerContextAt module ctx impl).parameterRoots index := by
    rcases permitted with generic | limited
    · exact False.elim (specialized (by simp [generic]))
    · exact limited
  have closed := lowerContextAt_parameterRoots_closed accepted contextRow implementationRow
  intro root member
  obtain ⟨sourceRoot, sourceMember, expanded⟩ := List.mem_flatMap.mp member
  have permittedRoot := declared sourceRoot sourceMember
  rcases closed index sourceRoot permittedRoot with own | ⟨global, identity⟩
  · exact False.elim (specialized (own ▸ permittedRoot))
  · subst sourceRoot
    have identity : root = .global global := by simpa [Func.expandParameterRoot] using expanded
    subst root
    exact permittedRoot

theorem rpCall_argument_globals {env : PEnv} {context : ContextId} {ctx : Context} {impl : Impl}
    {caller : Func} {sourceArgs : List (List RootRef)} {result : List RootRef}
    {before after : RState} {index : Nat}
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some ctx)
    (implementationRow : env.mod.impls[ctx.impl]? = some impl)
    (bounded : index < impl.params.size)
    (replayed : rpCall env context sourceArgs before = .ok (result, after))
    (specialized : RootRef.param index ∉ (lowerContextAt env.mod ctx impl).parameterRoots index) :
    ∀ root ∈ (sourceArgs[index]?.getD []).flatMap caller.expandParameterRoot,
      root ∈ (lowerContextAt env.mod ctx impl).parameterRoots index := by
  have contract := rpCall_replay_contract contextRow implementationRow replayed
  exact accepted_call_argument_globals accepted contextRow implementationRow bounded
    ((forAll_ok _ _).mp contract.1 index (List.mem_range.mpr bounded)) specialized

#print axioms accepted_call_argument_globals
#print axioms rpCall_argument_globals

end Goose.Lower.Validation.ReplacementContentFlowSource
