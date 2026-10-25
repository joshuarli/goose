import Goose.Lower.Validation.ReplacementCallQueryApart
import Goose.Lower.Validation.ReplacementOwnerDependencyApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlow.Model

private theorem argument_fold_apart {module : GIR.Module} {func : Func} {types : Array (Option VTy)}
    {state : State} {queries : ReplacementQueries} {owner : ValueId}
    (arguments : List ValueId)
    (apart : ∀ argument ∈ arguments, valRefLike types argument = true →
      ReplacementApart queries owner (ownerDependencies module func (flowAt state.values argument)))
    {prior roots : List RootRef} (priorApart : ReplacementApart queries owner (some prior))
    (known : arguments.foldlM (fun roots value => do
      if !valRefLike types value then pure roots else
        let actual ← ownerDependencies module func (flowAt state.values value)
        pure (unionRoots roots actual)) prior = some roots) :
    ReplacementApart queries owner (some roots) := by
  induction arguments generalizing prior with
  | nil =>
    have same : prior = roots := Option.some.inj known
    exact same ▸ priorApart
  | cons argument rest ih =>
    have tailApart := fun value member => apart value (List.mem_cons_of_mem _ member)
    by_cases reference : valRefLike types argument = true
    · cases actualAt : ownerDependencies module func (flowAt state.values argument) with
      | none => simp [List.foldlM_cons, reference, actualAt] at known
      | some actual =>
        have actualApart := apart argument (by simp) reference
        rw [actualAt] at actualApart
        exact ih tailApart (priorApart.union actualApart)
          (by simpa [List.foldlM_cons, reference, actualAt] using known)
    · exact ih tailApart priorApart (by simpa [List.foldlM_cons, reference] using known)

theorem callQuery_apart_of_public_touches {module : GIR.Module} {func : Func} {types : Array (Option VTy)}
    {states : Array State} {state : State} {queries : ReplacementQueries}
    {owner function : ValueId} {arguments : List ValueId} {roots : List RootRef}
    (known : callQuery module func types states state function arguments = some roots)
    (apart : ∀ argument ∈ arguments, valRefLike types argument = true →
      ReplacementApart queries owner (ownerDependencies module func (flowAt state.values argument)))
    (touches : ∀ effects, states[function]? = some effects →
      (substitute func state arguments (publicTouches effects.touched)).AtomsWithin
        (OwnerDependencyApart module func queries owner)) :
    ReplacementApart queries owner (some roots) := by
  unfold callQuery at known
  dsimp only at known
  split at known
  · simp [failure, bind, Option.bind] at known
  · cases effectsAt : states[function]? with
    | none => simp [effectsAt, bind, Option.bind, pure] at known
    | some effects =>
      simp only [pure, bind, Option.bind, effectsAt] at known
      split at known
      · cases known
      · rename_i argumentRoots argumentsAt
        dsimp only at known
        split at known
        · cases known
        · rename_i touched touchedAt
          cases known
          exact (argument_fold_apart arguments apart (Or.inl rfl) argumentsAt).union
            (ownerDependencies_apart_of_atoms (touches effects effectsAt) touchedAt)

theorem function_call_apart_of_public_touches {flow : ReplacementFunctionFlow}
    {queries : ReplacementQueries} {owner function : ValueId} {arguments : List ValueId}
    {roots : List RootRef} (known : flow.call function arguments = some roots)
    (argumentsApart : ∀ argument ∈ arguments,
      ReplacementApart queries owner (flow.ownerDependencies argument))
    (touches : ∀ final, flow.model = some final →
      ∀ states, flow.calleeStates = some states → ∀ effects, states[function]? = some effects →
      (substitute flow.source final arguments (publicTouches effects.touched)).AtomsWithin
        (OwnerDependencyApart flow.module flow.source queries owner)) :
    ReplacementApart queries owner (some roots) := by
  rw [ReplacementFunctionFlow.call_model] at known
  cases finalAt : flow.model with
  | none => simp [finalAt] at known
  | some final =>
    cases statesAt : flow.calleeStates with
    | none => simp [finalAt, statesAt] at known
    | some states =>
      simp only [finalAt, statesAt, Option.bind_some] at known
      apply callQuery_apart_of_public_touches known ?_ (touches final finalAt states statesAt)
      intro argument member reference
      have apart := argumentsApart argument member
      rw [ReplacementFunctionFlow.ownerDependencies_model, finalAt] at apart
      exact apart

#print axioms callQuery_apart_of_public_touches
#print axioms function_call_apart_of_public_touches

end Goose.Lower.Validation
