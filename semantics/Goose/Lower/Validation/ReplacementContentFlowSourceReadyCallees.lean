import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCalls
import Goose.GIR.ReplacementContentFlowProofsCanonicalInvariant
import Goose.GIR.ReplacementContentFlowProofsClosure

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem closed_callee_returned_ready {module : GIR.Module} {types : Array (Array (Option VTy))}
    {states : Array State} {index : FnId} {callee : Func} {effects : State}
    (closed : close module types = some states)
    (calleeRow : module.funcs[index]? = some callee) (effectRow : states[index]? = some effects) :
    effects.returned ≠ .pending := by
  have growth := (close_initial_extends closed).values index
  simp only [moduleStart, Array.getElem?_mapIdx, calleeRow, effectRow, Option.map_some, Option.getD_some] at growth
  exact returned_ready_of_initial_extends growth

theorem closed_callee_returned_normalized {module : GIR.Module} {types : Array (Array (Option VTy))}
    {states : Array State} {index : FnId} {callee : Func} {effects : State} {vt : Array (Option VTy)}
    {provenance : Prov} {type : Ty}
    (closed : close module types = some states)
    (calleeRow : module.funcs[index]? = some callee) (effectRow : states[index]? = some effects)
    (canonical : effects.CanonicalWithin callee vt provenance)
    (parameters : ∀ index root, root ∈ callee.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (result : callee.results = [type]) (reference : type.isRefLike = true) :
    ∃ roots, normalize callee effects.returned = some roots ∧
      roots ⊆ (callee.roots.results[0]?.getD []).flatMap callee.expandParameterRoot :=
  (canonical.returned type result reference).actual parameters
    (closed_callee_returned_ready closed calleeRow effectRow)

theorem call_result_ready_of_closed_callee {module : GIR.Module} {types : Array (Array (Option VTy))}
    {states : Array State} {caller callee : Func} {state effects : State} {index : FnId}
    {args : List ValueId} {vt : Array (Option VTy)} {provenance : Prov} {type : Ty}
    (closed : close module types = some states)
    (calleeRow : module.funcs[index]? = some callee) (effectRow : states[index]? = some effects)
    (canonical : effects.CanonicalWithin callee vt provenance)
    (parameters : ∀ index root, root ∈ callee.parameterRoots index →
      root = .param index ∨ ∃ global, root = .global global)
    (result : callee.results = [type]) (reference : type.isRefLike = true)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value → flowAt state.values value ≠ .pending)
    (contents : ∀ (index : Nat) (value : ValueId), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      args[index]? = some value → content caller state (flowAt state.values value) ≠ .pending) :
    (callState module states caller state index args).1 ≠ .pending := by
  obtain ⟨roots, known, _⟩ := closed_callee_returned_normalized closed calleeRow effectRow canonical parameters result reference
  exact call_result_ready_of_normalized calleeRow effectRow known arguments contents

#print axioms closed_callee_returned_ready
#print axioms closed_callee_returned_normalized
#print axioms call_result_ready_of_closed_callee

end Goose.Lower.Validation.ReplacementContentFlowSource
