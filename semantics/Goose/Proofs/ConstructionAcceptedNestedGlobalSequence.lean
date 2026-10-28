import Goose.Proofs.ConstructionAcceptedNestedGlobal
import Goose.Proofs.ConstructionAcceptedMixedGlobal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

def NestedGlobalInitializer (descriptor : Global) : Prop :=
  (NestedScalarExpression descriptor.init ∧ ((∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)) ∨
    ∃ bytes bytesOrigin, descriptor.ty = .varr (.int .u8) ∧
      descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin

theorem initGlobals_nested_head (fuel initialized : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (scalars : FlatGlobalsAreScalar config)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (descriptor : Global) (world : AcceptedWorld config initialized before ambient types live [] [])
    (clear : FutureGlobalsClear config initialized before)
    (declared : config.module.globals[initialized]? = some descriptor)
    (initializer : NestedGlobalInitializer descriptor) :
    ∃ completed nextLive regions,
      let outcome := initGlobals fuel config [initialized] before
      let after := Goose.Proofs.Exit.stepState outcome
      initialized ≤ completed ∧ completed ≤ initialized + 1 ∧
      AcceptedWorld config completed after ambient types nextLive regions [] ∧
      (match outcome with
      | .ok _ _ => completed = initialized + 1 ∧ regions = [] ∧ FutureGlobalsClear config completed after
      | .stop _ _ => completed < initialized + 1
      | .escape .. | .jump .. => False) := by
  rcases initializer with scalarForm | ⟨bytes, bytesOrigin, ty, init⟩
  · obtain ⟨completed, nextLive, lower, upper, nextWorld, nextFlow⟩ :=
      initGlobals_nestedScalar_single fuel initialized config accepted before ambient types live descriptor world clear declared scalarForm.1 scalars scalarForm.2
    refine ⟨completed, nextLive, [], lower, upper, nextWorld, ?_⟩
    cases execution : initGlobals fuel config [initialized] before with
    | ok value after =>
      cases value
      simp only [execution, Goose.Proofs.Exit.stepState] at nextFlow ⊢
      exact ⟨nextFlow.1, trivial, nextFlow.2⟩
    | stop reason after => simp only [execution] at nextFlow ⊢; omega
    | escape address carriers after | jump target kind after => simp only [execution] at nextFlow
  · exact initGlobals_mixed_single fuel initialized config before ambient types live descriptor world clear declared
      (Or.inr ⟨bytes, bytesOrigin, ty, init⟩)

theorem initGlobals_nested_complete (count : Nat) :
    ∀ (fuel initialized : Nat) (config : EvalConfig) (_accepted : AcceptedModule config) (_scalars : FlatGlobalsAreScalar config) (before : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop),
      initialized + count ≤ config.module.globals.size →
      (∀ id, initialized ≤ id → id < initialized + count →
        ∃ descriptor, config.module.globals[id]? = some descriptor ∧ NestedGlobalInitializer descriptor) →
      AcceptedWorld config initialized before ambient types live [] [] → FutureGlobalsClear config initialized before →
      ∃ completed nextLive regions,
        let outcome := initGlobals fuel config (List.range' initialized count) before
        let after := Goose.Proofs.Exit.stepState outcome
        initialized ≤ completed ∧ completed ≤ initialized + count ∧
        AcceptedWorld config completed after ambient types nextLive regions [] ∧
        (match outcome with
        | .ok _ _ => completed = initialized + count ∧ regions = [] ∧ FutureGlobalsClear config completed after
        | .stop _ _ => completed < initialized + count
        | .escape .. | .jump .. => False) := by
  induction count with
  | zero =>
    intro fuel initialized config accepted scalars before ambient types live bound declarations world clear
    simp only [List.range'_zero, initGlobals, pure, Goose.Proofs.Exit.stepState]
    exact ⟨initialized, live, [], by omega, by omega, world, by simp, rfl, clear⟩
  | succ count ih =>
    intro fuel initialized config accepted scalars before ambient types live bound declarations world clear
    obtain ⟨descriptor, declared, literal⟩ := declarations initialized (Nat.le_refl _) (by omega)
    obtain ⟨completed, nextLive, regions, lower, upper, headWorld, headFlow⟩ :=
      initGlobals_nested_head fuel initialized config accepted scalars before ambient types live descriptor world clear declared literal
    have factor := initGlobals_head_factor fuel config initialized (List.range' (initialized + 1) count)
    cases head : initGlobals fuel config [initialized] before with
    | stop reason after =>
      simp only [head, Goose.Proofs.Exit.stepState] at headWorld headFlow
      have done : initGlobals fuel config (List.range' initialized (count + 1)) before = .stop reason after := by
        simp only [List.range'_succ, factor, bind, head]
      simp only [done, Goose.Proofs.Exit.stepState]
      exact ⟨completed, nextLive, regions, lower, by omega, headWorld, by omega⟩
    | escape address carriers after | jump target kind after => simp only [head] at headFlow
    | ok value middle =>
      cases value
      simp only [head, Goose.Proofs.Exit.stepState] at headWorld headFlow
      obtain ⟨completedEq, regionsEq, nextClear⟩ := headFlow
      subst completed regions
      have tailDeclarations : ∀ id, initialized + 1 ≤ id → id < initialized + 1 + count →
          ∃ descriptor, config.module.globals[id]? = some descriptor ∧ NestedGlobalInitializer descriptor := by
        intro id lower upper
        exact declarations id (by omega) (by omega)
      obtain ⟨finalCompleted, finalLive, finalRegions, finalLower, finalUpper, finalWorld, finalFlow⟩ :=
        ih fuel (initialized + 1) config accepted scalars middle ambient types nextLive (by omega) tailDeclarations headWorld nextClear
      have done : initGlobals fuel config (List.range' initialized (count + 1)) before =
          initGlobals fuel config (List.range' (initialized + 1) count) middle := by
        simp only [List.range'_succ, factor, bind, head]
      simp only [done, Goose.Proofs.Exit.stepState]
      refine ⟨finalCompleted, finalLive, finalRegions, by omega, by omega, finalWorld, ?_⟩
      cases tail : initGlobals fuel config (List.range' (initialized + 1) count) middle with
      | ok value after =>
        cases value
        simp only [tail] at finalFlow ⊢
        obtain ⟨completedEq, regionsEq, finalClear⟩ := finalFlow
        exact ⟨by omega, regionsEq, by simpa only [completedEq, tail, Goose.Proofs.Exit.stepState] using finalClear⟩
      | stop reason after => simp only [tail] at finalFlow ⊢; omega
      | escape address carriers after | jump target kind after => simp only [tail] at finalFlow


theorem initGlobals_nested_initial_complete (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (scalars : FlatGlobalsAreScalar config)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ NestedGlobalInitializer descriptor) :
    ∃ completed live regions,
      let outcome := initGlobals fuel config (List.range config.module.globals.size) .initial
      let after := Goose.Proofs.Exit.stepState outcome
      completed ≤ config.module.globals.size ∧
      AcceptedWorld config completed after [] (declaredRootTypes config.module) live regions [] ∧
      (match outcome with
       | .ok _ _ => completed = config.module.globals.size ∧ regions = [] ∧ FutureGlobalsClear config completed after
       | .stop stop _ => completed < config.module.globals.size ∧ runModule fuel config .initial = .stop stop after
       | .escape .. | .jump .. => False) := by
  have checked : ∀ id, 0 ≤ id → id < 0 + config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ NestedGlobalInitializer descriptor := by
    intro id lower upper
    exact declarations id (by simpa using upper)
  obtain ⟨completed, live, regions, lower, upper, finalWorld, final⟩ :=
    initGlobals_nested_complete config.module.globals.size fuel 0 config accepted scalars .initial [] (declaredRootTypes config.module)
      (fun _ => False) (by simp) checked (initial_acceptedWorld config accepted.accepted) (futureGlobalsClear_initial config)
  simp only [Nat.zero_add, ← List.range_eq_range'] at upper finalWorld final
  refine ⟨completed, live, regions, upper, finalWorld, ?_⟩
  cases outcome : initGlobals fuel config (List.range config.module.globals.size) .initial with
  | ok value after =>
    cases value
    simp only [outcome] at final ⊢
    exact final
  | stop stop after =>
    simp only [outcome] at final ⊢
    refine ⟨final, ?_⟩
    simp only [runModule, bind, outcome, Goose.Proofs.Exit.stepState]
  | escape target carriers after | jump target kind after =>
    simp only [outcome] at final




#print axioms initGlobals_nested_initial_complete
#print axioms initGlobals_nested_complete
#print axioms initGlobals_nested_head
end Goose.Proofs.ConstructionAcceptedExecution
