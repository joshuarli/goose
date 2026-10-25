import Goose.Lower.Validation.SourceReadyObservations
import Goose.Lower.Validation.SourceReadyInductionCalls
import Goose.GIR.ReplacementContentFlowProofsSliceContentReady
import Goose.GIR.ReplacementContentFlowProofsSliceSubstitution

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.call_observation (facts : SourceReadyFunction)
    {calleeId : FnId} {arguments : List ValueId}
    (site : CallSiteFacts (lower facts.source.mod) facts.func facts.types facts.provenance calleeId arguments)
    (calleeFacts : FunctionRootFacts site.callee)
    (argumentsReady : ∀ (index : Nat) (value : ValueId), arguments[index]? = some value → flowAt facts.state.values value ≠ .pending)
    (contentsReady : ∀ (index : Nat) (value : ValueId), (site.callee.roots.contents.find? (·.1 == index)).isSome = true →
      arguments[index]? = some value → content facts.func facts.state (flowAt facts.state.values value) ≠ .pending) :
    CallObservationReady site.callee facts.func facts.state arguments := by
  constructor
  · intro index bounded
    obtain ⟨value, row, valueBound⟩ := site.arguments index bounded
    have stateBound : value < facts.state.values.size := by simpa only [facts.canonical.shape.values] using valueBound
    obtain ⟨roots, normalized, _⟩ := (facts.canonical.values value stateBound).actual facts.native.roots.closed
      (argumentsReady index value row)
    exact ⟨value, roots, row, normalized⟩
  · intro index ceiling bounded annotation
    have reference := calleeFacts.contentTypes index ceiling annotation
    cases parameterAt : site.callee.params[index]? with
    | none => simp [parameterAt] at reference
    | some parameter =>
      have parameterReference : parameter.isRefSlice = true := by simpa only [parameterAt, Option.any_some] using reference
      obtain ⟨outer, inner, element, rfl, flat⟩ := isRefSlice_shape parameterReference
      obtain ⟨value, mutability, row, nativeType, valueBound⟩ := site.references index outer (.slice inner element) parameterAt
      have stateBound : value < facts.state.values.size := by simpa only [facts.canonical.shape.values] using valueBound
      have holder := facts.canonical.holderValues value stateBound mutability (.slice inner element) nativeType (by rfl)
      have observed : (site.callee.roots.contents.find? (·.1 == index)).isSome = true := by simp [annotation]
      obtain ⟨roots, normalized⟩ := facts.canonical.holder_content_normalized holder facts.native.roots.parameters
        (by rfl) (by
          intro receiver mu receiverRow member
          apply site.observed index value row reference observed receiver member
          have receiverReference := paramOk_refLike_payload facts.native.roots.parameters receiverRow (by rfl)
          simp only [receiverRow, Option.any_some, receiverReference])
        (contentsReady index value observed row)
      exact ⟨value, roots, row, normalized⟩

#print axioms SourceReadyFunction.call_observation

end Goose.Lower.Validation.ReplacementContentFlowSource
