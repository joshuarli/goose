import Goose.GIR.ReplacementContentFlowProofsObservation

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

private theorem argument_fold_dependencies (module : Module) (func : Func) (types : Array (Option VTy))
    (state : State) (args : List ValueId) (initial actual : List RootRef)
    (known : args.foldlM (fun roots value => do
      if !valRefLike types value then pure roots else
        let next ← ownerDependencies module func (flowAt state.values value)
        pure (unionRoots roots next)) initial = some actual) :
    initial ⊆ actual ∧ ∀ value ∈ args, valRefLike types value = true →
      ∃ roots, ownerDependencies module func (flowAt state.values value) = some roots ∧ roots ⊆ actual := by
  induction args generalizing initial with
  | nil => cases known; exact ⟨List.Subset.refl _,by simp⟩
  | cons value rest ih =>
      by_cases reference : valRefLike types value = true
      · cases nextAt : ownerDependencies module func (flowAt state.values value) with
        | none => simp [List.foldlM_cons,reference,nextAt] at known
        | some roots =>
            have restKnown : rest.foldlM (fun roots value => do
                if !valRefLike types value then pure roots else
                  let next ← ownerDependencies module func (flowAt state.values value)
                  pure (unionRoots roots next)) (unionRoots initial roots) = some actual := by
              simpa [List.foldlM_cons,reference,nextAt] using known
            obtain ⟨within,mapped⟩ := ih _ restKnown
            refine ⟨fun root member => within ((unionRoots_mem_iff _ _ _).mpr (Or.inl member)),?_⟩
            intro argument member like
            rcases List.mem_cons.mp member with same | member
            · subst argument
              exact ⟨roots,nextAt,fun root member => within ((unionRoots_mem_iff _ _ _).mpr (Or.inr member))⟩
            · exact mapped argument member like
      · have restKnown : rest.foldlM (fun roots value => do
              if !valRefLike types value then pure roots else
                let next ← ownerDependencies module func (flowAt state.values value)
                pure (unionRoots roots next)) initial = some actual := by
          simpa [List.foldlM_cons,reference] using known
        obtain ⟨within,mapped⟩ := ih _ restKnown
        refine ⟨within,?_⟩
        intro argument member like
        rcases List.mem_cons.mp member with same | member
        · subst argument; exact False.elim (reference like)
        · exact mapped argument member like

theorem callQuery_argument_dependencies {module : Module} {func : Func} {types : Array (Option VTy)}
    {states : Array State} {state : State} {fn : FnId} {args : List ValueId} {actual : List RootRef}
    (known : callQuery module func types states state fn args = some actual)
    {argument : ValueId} (member : argument ∈ args) (reference : valRefLike types argument = true) :
    ∃ roots, ownerDependencies module func (flowAt state.values argument) = some roots ∧ roots ⊆ actual := by
  unfold callQuery at known
  dsimp only at known
  split at known
  · simp [failure,bind,Option.bind] at known
  · cases effectsAt : states[fn]? with
    | none => simp [effectsAt,bind,Option.bind,pure] at known
    | some effects =>
        simp only [pure,bind,Option.bind,effectsAt] at known
        split at known
        · cases known
        · rename_i arguments argumentsAt
          dsimp only at known
          split at known
          · cases known
          · rename_i touched touchedAt
            cases known
            obtain ⟨roots,rootsAt,within⟩ := (argument_fold_dependencies _ _ _ _ _ _ _ argumentsAt).2 argument member reference
            exact ⟨roots,rootsAt,fun root member => (unionRoots_mem_iff _ _ _).mpr (Or.inl (within member))⟩

#print axioms callQuery_argument_dependencies

end Goose.GIR.ReplacementContentFlow.Model

namespace Goose.GIR

open Goose.Core ReplacementContentFlow.Model

theorem ReplacementFunctionFlow.call_argument_dependencies {flow : ReplacementFunctionFlow}
    {fn : FnId} {args : List ValueId} {actual : List RootRef} {argument : ValueId}
    (known : flow.call fn args = some actual) (member : argument ∈ args)
    (reference : valRefLike flow.valueTypes argument = true) :
    ∃ roots, flow.ownerDependencies argument = some roots ∧ roots ⊆ actual := by
  rw [ReplacementFunctionFlow.call_model] at known
  rw [ReplacementFunctionFlow.ownerDependencies_model]
  cases stateAt : flow.model with
  | none => simp [stateAt] at known
  | some state =>
      cases statesAt : flow.calleeStates with
      | none => simp [stateAt,statesAt] at known
      | some states =>
          simp only [stateAt,statesAt,Option.bind_some] at known ⊢
          exact callQuery_argument_dependencies known member reference

#print axioms ReplacementFunctionFlow.call_argument_dependencies

end Goose.GIR
