import Goose.Lower.Validation.ReplacementContentFlowSourceReadySteps
import Goose.GIR.ReplacementContentFlowProofsTransfer

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem substitute_ready_of_normalized {caller callee : Func} {state : State}
    {args : List ValueId} {roots : Roots} {normalized : List RootRef}
    (known : normalize callee roots = some normalized)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value → flowAt state.values value ≠ .pending)
    (contents : ∀ (index : Nat) (value : ValueId), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      args[index]? = some value → content caller state (flowAt state.values value) ≠ .pending) :
    substitute caller state args roots ≠ .pending := by
  obtain ⟨atoms, rfl⟩ := normalize_known_shape known
  have mapped := (normalize_fold_atoms callee atoms [] normalized known).2
  apply bind_ready (by simp)
  intro actual equality atom member
  cases equality
  cases atom with
  | «local» slot => simp [substitute, Roots.bind]
  | global global => simp [substitute, Roots.bind]
  | param index =>
    cases found : args[index]? with
    | none => simp [found]
    | some value => simpa only [found, Option.map_some, Option.getD_some] using arguments index value found
  | contents index =>
    obtain ⟨actualRoots, actualKnown, _⟩ := mapped (.contents index) member
    have declared : (callee.roots.contents.find? (·.1 == index)).isSome = true := by
      cases row : callee.roots.contents.find? (·.1 == index) with
      | none => simp [normalizeAtom, row] at actualKnown
      | some bound => simp [row]
    cases found : args[index]? with
    | none => simp [found]
    | some value =>
      simpa only [found, Option.map_some, Option.getD_some] using contents index value declared found

theorem call_result_ready_of_normalized {module : GIR.Module} {callees : Array State} {caller callee : Func}
    {state effects : State} {fn : FnId} {args : List ValueId} {normalized : List RootRef}
    (calleeRow : module.funcs[fn]? = some callee) (effectRow : callees[fn]? = some effects)
    (known : normalize callee effects.returned = some normalized)
    (arguments : ∀ (index : Nat) (value : ValueId), args[index]? = some value → flowAt state.values value ≠ .pending)
    (contents : ∀ (index : Nat) (value : ValueId), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      args[index]? = some value → content caller state (flowAt state.values value) ≠ .pending) :
    (callState module callees caller state fn args).1 ≠ .pending := by
  rw [callState_result _ _ _ _ _ _ _ _ calleeRow effectRow]
  exact substitute_ready_of_normalized known arguments contents

#print axioms substitute_ready_of_normalized
#print axioms call_result_ready_of_normalized

end Goose.Lower.Validation.ReplacementContentFlowSource
