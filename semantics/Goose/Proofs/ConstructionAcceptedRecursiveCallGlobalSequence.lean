import Goose.Proofs.ConstructionAcceptedRecursiveCallGlobal
import Goose.Proofs.ConstructionAcceptedNestedGlobalSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

def RecursiveCallGlobalInitializer (config : EvalConfig) (descriptor : Global) : Prop :=
  NestedGlobalInitializer descriptor ∨
  ∃ target origin context callee,
    descriptor.init = .call target [] origin ∧
    ((∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) ∧
    config.module.contexts[target]? = some context ∧ config.module.impls[context.impl]? = some callee ∧
    callee.params = #[] ∧ callee.results = #[⟨descriptor.ty, .register, none⟩] ∧ RegisterCallGraph config descriptor.ty

theorem initGlobals_recursiveCall_head (fuel initialized : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (scalars : FlatGlobalsAreScalar config) (before : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (descriptor : Global)
    (world : AcceptedWorld config initialized before ambient types live [] []) (clear : FutureGlobalsClear config initialized before)
    (declared : config.module.globals[initialized]? = some descriptor) (form : RecursiveCallGlobalInitializer config descriptor) :
    ∃ completed nextTypes nextLive nextAmbient regions,
      let outcome := initGlobals fuel config [initialized] before
      let after := Goose.Proofs.Exit.stepState outcome
      RootTypesExtend types nextTypes ∧ initialized ≤ completed ∧ completed ≤ initialized + 1 ∧
      AcceptedWorld config completed after nextAmbient nextTypes nextLive regions [] ∧
      (match outcome with
       | .ok _ _ => nextAmbient = ambient ∧ completed = initialized + 1 ∧ regions = [] ∧ FutureGlobalsClear config completed after
       | .stop _ _ => completed < initialized + 1
       | .escape .. | .jump .. => False) := by
  rcases form with nested | ⟨target, origin, context, callee, init, scalar, contextAt, calleeAt, parameters, results, graph⟩
  · obtain ⟨completed, nextLive, regions, lower, upper, afterWorld, flow⟩ :=
      initGlobals_nested_head fuel initialized config accepted scalars before ambient types live descriptor world clear declared nested
    refine ⟨completed, types, nextLive, ambient, regions, (fun _ _ found => found), lower, upper, afterWorld, ?_⟩
    cases execution : initGlobals fuel config [initialized] before with
    | ok value after => simp only [execution] at flow ⊢; exact ⟨trivial, flow⟩
    | stop reason after => simpa only [execution] using flow
    | escape address carriers after | jump target kind after => simp only [execution] at flow
  · obtain ⟨completed, nextTypes, nextLive, nextAmbient, extend, lower, upper, afterWorld, flow⟩ :=
      initGlobals_recursive_register_single fuel initialized config accepted before ambient types live descriptor target origin context callee
        world clear declared init scalar contextAt calleeAt parameters results graph
    refine ⟨completed, nextTypes, nextLive, nextAmbient, [], extend, lower, upper, afterWorld, ?_⟩
    cases execution : initGlobals fuel config [initialized] before with
    | ok value after =>
      simp only [execution] at flow ⊢
      exact ⟨flow.1, flow.2.1, trivial, flow.2.2⟩
    | stop reason after => simp only [execution] at flow ⊢; omega
    | escape address carriers after | jump target kind after => simp only [execution] at flow

theorem initGlobals_recursiveCall_complete (count : Nat) :
    ∀ (fuel initialized : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (scalars : FlatGlobalsAreScalar config)
      (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop),
      initialized + count ≤ config.module.globals.size →
      (∀ id, initialized ≤ id → id < initialized + count →
        ∃ descriptor, config.module.globals[id]? = some descriptor ∧ RecursiveCallGlobalInitializer config descriptor) →
      AcceptedWorld config initialized before ambient types live [] [] → FutureGlobalsClear config initialized before →
      ∃ completed nextTypes nextLive nextAmbient regions,
        let outcome := initGlobals fuel config (List.range' initialized count) before
        let after := Goose.Proofs.Exit.stepState outcome
        RootTypesExtend types nextTypes ∧ initialized ≤ completed ∧ completed ≤ initialized + count ∧
        AcceptedWorld config completed after nextAmbient nextTypes nextLive regions [] ∧
        (match outcome with
         | .ok _ _ => nextAmbient = ambient ∧ completed = initialized + count ∧ regions = [] ∧ FutureGlobalsClear config completed after
         | .stop _ _ => completed < initialized + count
         | .escape .. | .jump .. => False) := by
  induction count with
  | zero =>
    intro fuel initialized config accepted scalars before ambient types live bound declarations world clear
    simp only [List.range'_zero, initGlobals, pure, Goose.Proofs.Exit.stepState]
    exact ⟨initialized, types, live, ambient, [], (fun _ _ found => found), by omega, by omega, world, rfl, by omega, rfl, clear⟩
  | succ count ih =>
    intro fuel initialized config accepted scalars before ambient types live bound declarations world clear
    obtain ⟨descriptor, declared, form⟩ := declarations initialized (Nat.le_refl _) (by omega)
    obtain ⟨completed, nextTypes, nextLive, nextAmbient, regions, extend, lower, upper, headWorld, headFlow⟩ :=
      initGlobals_recursiveCall_head fuel initialized config accepted scalars before ambient types live descriptor world clear declared form
    have factor := initGlobals_head_factor fuel config initialized (List.range' (initialized + 1) count)
    cases head : initGlobals fuel config [initialized] before with
    | stop reason after =>
      simp only [head, Goose.Proofs.Exit.stepState] at headWorld headFlow
      have done : initGlobals fuel config (List.range' initialized (count + 1)) before = .stop reason after := by
        simp only [List.range'_succ, factor, bind, head]
      simp only [done, Goose.Proofs.Exit.stepState]
      exact ⟨completed, nextTypes, nextLive, nextAmbient, regions, extend, lower, by omega, headWorld, by omega⟩
    | escape address carriers after | jump target kind after => simp only [head] at headFlow
    | ok value middle =>
      cases value
      simp only [head, Goose.Proofs.Exit.stepState] at headWorld headFlow
      obtain ⟨ambientEq, completedEq, regionsEq, nextClear⟩ := headFlow
      subst nextAmbient completed regions
      have tailDeclarations : ∀ id, initialized + 1 ≤ id → id < initialized + 1 + count →
          ∃ descriptor, config.module.globals[id]? = some descriptor ∧ RecursiveCallGlobalInitializer config descriptor := by
        intro id lower upper
        exact declarations id (by omega) (by omega)
      obtain ⟨finalCompleted, finalTypes, finalLive, finalAmbient, finalRegions, finalExtend, finalLower, finalUpper, finalWorld, finalFlow⟩ :=
        ih fuel (initialized + 1) config accepted scalars middle ambient nextTypes nextLive (by omega) tailDeclarations headWorld nextClear
      have done : initGlobals fuel config (List.range' initialized (count + 1)) before =
          initGlobals fuel config (List.range' (initialized + 1) count) middle := by
        simp only [List.range'_succ, factor, bind, head]
      simp only [done, Goose.Proofs.Exit.stepState]
      have fullExtend : RootTypesExtend types finalTypes := by intro root ty found; exact finalExtend root ty (extend root ty found)
      refine ⟨finalCompleted, finalTypes, finalLive, finalAmbient, finalRegions, fullExtend, by omega, by omega, finalWorld, ?_⟩
      cases tail : initGlobals fuel config (List.range' (initialized + 1) count) middle with
      | ok value after =>
        cases value
        simp only [tail] at finalFlow ⊢
        obtain ⟨ambientEq, completedEq, regionsEq, finalClear⟩ := finalFlow
        exact ⟨ambientEq, by omega, regionsEq, by simpa only [completedEq, tail, Goose.Proofs.Exit.stepState] using finalClear⟩
      | stop reason after => simp only [tail] at finalFlow ⊢; omega
      | escape address carriers after | jump target kind after => simp only [tail] at finalFlow

theorem initGlobals_recursiveCall_initial_complete (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (scalars : FlatGlobalsAreScalar config)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ RecursiveCallGlobalInitializer config descriptor) :
    ∃ completed types live ambient regions,
      let outcome := initGlobals fuel config (List.range config.module.globals.size) .initial
      let after := Goose.Proofs.Exit.stepState outcome
      RootTypesExtend (declaredRootTypes config.module) types ∧ completed ≤ config.module.globals.size ∧
      AcceptedWorld config completed after ambient types live regions [] ∧
      (match outcome with
       | .ok _ _ => ambient = [] ∧ completed = config.module.globals.size ∧ regions = [] ∧ FutureGlobalsClear config completed after
       | .stop stop _ => completed < config.module.globals.size ∧ runModule fuel config .initial = .stop stop after
       | .escape .. | .jump .. => False) := by
  have checked : ∀ id, 0 ≤ id → id < 0 + config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ RecursiveCallGlobalInitializer config descriptor := by
    intro id lower upper
    exact declarations id (by simpa using upper)
  obtain ⟨completed, types, live, ambient, regions, extend, lower, upper, finalWorld, final⟩ :=
    initGlobals_recursiveCall_complete config.module.globals.size fuel 0 config accepted scalars .initial [] (declaredRootTypes config.module)
      (fun _ => False) (by simp) checked (initial_acceptedWorld config accepted.accepted) (futureGlobalsClear_initial config)
  simp only [Nat.zero_add, ← List.range_eq_range'] at upper finalWorld final
  refine ⟨completed, types, live, ambient, regions, extend, upper, finalWorld, ?_⟩
  cases outcome : initGlobals fuel config (List.range config.module.globals.size) .initial with
  | ok value after =>
    cases value
    simp only [outcome] at final ⊢
    exact final
  | stop stop after =>
    simp only [outcome] at final ⊢
    refine ⟨final, ?_⟩
    simp only [runModule, bind, outcome, Goose.Proofs.Exit.stepState]
  | escape target carriers after | jump target kind after => simp only [outcome] at final

#print axioms initGlobals_recursiveCall_initial_complete
#print axioms initGlobals_recursiveCall_complete
#print axioms initGlobals_recursiveCall_head
end Goose.Proofs.ConstructionAcceptedExecution
