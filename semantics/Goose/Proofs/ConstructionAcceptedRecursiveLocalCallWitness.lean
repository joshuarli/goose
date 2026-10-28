import Goose.Proofs.ConstructionAcceptedRecursiveMixedGlobalModule
import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallModule
import Goose.Proofs.ConstructionAcceptedNestedGlobal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private def localTailSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def localTailEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, localTailSummary⟩
private def localTailInner : Impl := ⟨"inner", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 7)), localTailSummary⟩
private def localTailOuter : Impl := ⟨"outer", #[], #[⟨.int .i64, .register, none⟩],
  #[⟨"local", .int .i64, .immutable, 0, 0⟩],
  .mk 0 [.letS 0 (.lit .i64 3) 0] (some (.call 2 [] 0)), localTailSummary⟩
private def localTailModule : Module := ⟨#["local-call.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩], #[localTailEntry, localTailOuter, localTailInner],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "outer", [], [[]], []⟩, ⟨2, "inner", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def localTailConfig : EvalConfig := ⟨.release, localTailModule⟩

theorem localTail_validated : validate localTailModule = .ok () := by cbv

theorem localTail_graph : RegisterCallGraphWithLocals localTailConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [localTailConfig, localTailModule] at contextAt
    subst context
    simp [localTailConfig, localTailModule] at implementationAt
    subst implementation
    simp [localTailEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [localTailConfig, localTailModule] at contextAt
      subst context
      simp [localTailConfig, localTailModule] at implementationAt
      subst implementation
      refine ⟨_, rfl, Or.inr ⟨0, _, 2, 0, ⟨2, "inner", [], [[]], []⟩, localTailInner, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩⟩
      · repeat constructor
      · intro id expression origin member descriptor found
        simp [localTailOuter, Block.stmts] at member found
        obtain ⟨rfl, rfl, rfl⟩ := member
        simp at found
        subst descriptor
        exact Or.inl ⟨.i64, rfl⟩
    | succ target =>
      cases target with
      | zero =>
        simp [localTailConfig, localTailModule] at contextAt
        subst context
        simp [localTailConfig, localTailModule] at implementationAt
        subst implementation
        refine ⟨_, rfl, Or.inl ⟨0, [], .lit .i64 7, rfl, .nil, ?_, ?_⟩⟩
        · repeat constructor
        · intro id expression origin member
          cases member
      | succ target => simp [localTailConfig, localTailModule] at contextAt

private def localTailObservation : Option Int :=
  match runModule 100 localTailConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem localTail_result : localTailObservation = some 7 := by decide +kernel

theorem localTail_invoke_allFuel (fuel : Nat) :
    ∃ types live ambient,
      let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
      let environment : RuntimeActivation := ⟨0, ExecutionState.initial.nextAct, #[], [], []⟩
      let outcome := invokeCall fuel localTailConfig environment 1 [] [.register (.int .i64)] 0 activated
      AcceptedWorld localTailConfig 0 (Goose.Proofs.Exit.stepState outcome) ambient types live [] [] ∧
      FutureGlobalsClear localTailConfig 0 (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => ambient = [] ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation (.int .i64) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩
  obtain ⟨names, roots, typingAfter, rootsAfter, world, source, checked⟩ :=
    accepted_nestedGlobal_checked localTailConfig (acceptedModule localTailConfig localTail_validated) 0 descriptor .initial []
      (declaredRootTypes localTailModule) (fun _ => False) (initial_acceptedWorld localTailConfig localTail_validated)
      (futureGlobalsClear_initial localTailConfig) (by rfl) (Or.inl ⟨.i64, rfl⟩)
  let frame := scalarGlobalInitializerFrame localTailConfig 0 ExecutionState.initial.nextAct names
  let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
  let context : Context := ⟨1, "outer", [], [[]], []⟩
  obtain ⟨types, live, ambient, extend, acts, scopes, finalWorld, clear, flow⟩ :=
    invokeCall_recursive_register_withLocals fuel localTailConfig (acceptedModule localTailConfig localTail_validated)
      (.int .i64) (Or.inl ⟨.i64, rfl⟩) localTail_graph frame activated [] (declaredRootTypes localTailModule)
      (fun _ => False) [] [] 1 context localTailOuter 0 world source (by rfl) (by rfl) (by rfl) (by rfl)
      roots typingAfter rootsAfter checked
  exact ⟨types, live, ambient, finalWorld, clear, flow⟩

theorem localTail_eval_allFuel (fuel : Nat) :
    ∃ types live ambient,
      let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
      let environment : RuntimeActivation := ⟨0, ExecutionState.initial.nextAct, #[], [], []⟩
      let outcome := evalValue fuel localTailConfig environment (.call 1 [] 0) activated
      AcceptedWorld localTailConfig 0 (Goose.Proofs.Exit.stepState outcome) ambient types live [] [] ∧
      FutureGlobalsClear localTailConfig 0 (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok value _ => ambient = [] ∧ ValueRepresentation (.int .i64) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩
  obtain ⟨names, roots, typingAfter, rootsAfter, world, source, checked⟩ :=
    accepted_nestedGlobal_checked localTailConfig (acceptedModule localTailConfig localTail_validated) 0 descriptor .initial []
      (declaredRootTypes localTailModule) (fun _ => False) (initial_acceptedWorld localTailConfig localTail_validated)
      (futureGlobalsClear_initial localTailConfig) (by rfl) (Or.inl ⟨.i64, rfl⟩)
  let frame := scalarGlobalInitializerFrame localTailConfig 0 ExecutionState.initial.nextAct names
  let activated := { ExecutionState.initial with nextAct := ExecutionState.initial.nextAct + 1 }
  let context : Context := ⟨1, "outer", [], [[]], []⟩
  obtain ⟨types, live, ambient, extend, acts, scopes, finalWorld, clear, flow⟩ :=
    evalValue_recursive_register_withLocals fuel localTailConfig (acceptedModule localTailConfig localTail_validated)
      frame activated [] (declaredRootTypes localTailModule) (fun _ => False) [] [] 1 context localTailOuter (.int .i64) 0
      localTail_graph world source (by rfl) (by rfl) (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
      roots typingAfter rootsAfter checked
  exact ⟨types, live, ambient, finalWorld, clear, flow⟩

theorem localTail_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld localTailConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel localTailConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel localTailConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩
  let calleeContext : Context := ⟨1, "outer", [], [[]], []⟩
  let entryContext : Context := ⟨0, "entry", [], [], []⟩
  apply acceptedLocalCallModule_allFuel fuel localTailConfig (acceptedModule localTailConfig localTail_validated)
    descriptor 1 0 calleeContext localTailOuter (by rfl) (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    (by rfl) (by rfl) (by rfl) (by rfl) localTail_graph entryContext localTailEntry (by rfl) (by rfl)
  · exact .nil
  · simp [localTailEntry, Block.stmts]
  · simp [localTailEntry, Block.stmts]
  · simp [localTailEntry, Block.stmts]
  · simp [localTailEntry, Block.stmts]
  · rfl

private def localTailMixedModule : Module := ⟨#["mixed-local-call.goose"], #[.int .i64, .varr (.int .u8)],
  #[⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩,
    ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩], #[localTailEntry, localTailOuter, localTailInner],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "outer", [], [[]], []⟩, ⟨2, "inner", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def localTailMixedConfig : EvalConfig := ⟨.release, localTailMixedModule⟩

theorem localTailMixed_validated : validate localTailMixedModule = .ok () := by cbv

theorem localTailMixed_graph : RegisterCallGraphWithLocals localTailMixedConfig (.int .i64) := by
  simpa [RegisterCallGraphWithLocals, RegisterCalleeFormWithLocals, localTailMixedConfig, localTailMixedModule,
    localTailConfig, localTailModule] using localTail_graph

private def localTailMixedObservation : Option Int :=
  match runModule 100 localTailMixedConfig .initial with
  | .ok () state => match state.objects.lookup (.global 1) with
    | some (.int .i64 value) => some value
    | _ => none
  | _ => none

theorem localTailMixed_result : localTailMixedObservation = some 7 := by decide +kernel

theorem localTailMixed_module_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld localTailMixedConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel localTailMixedConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel localTailMixedConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  have scalars : FlatGlobalsAreScalar localTailMixedConfig := by
    intro id descriptor declared flat
    cases id with
    | zero =>
      have same : descriptor = ⟨"bytes", .varr (.int .u8), .immutable, .bytes (.varr (.int .u8)) [65] 0, 0⟩ := by
        simpa [localTailMixedConfig, localTailMixedModule] using declared.symm
      subst descriptor
      simp [Ty.flat] at flat
    | succ id =>
      cases id with
      | zero =>
        have same : descriptor = ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩ := by
          simpa [localTailMixedConfig, localTailMixedModule] using declared.symm
        subst descriptor
        exact Or.inl ⟨.i64, rfl⟩
      | succ id => simp [localTailMixedConfig, localTailMixedModule] at declared
  apply acceptedRecursiveMixedGlobalModule_allFuel_withLocals fuel localTailMixedConfig
    (acceptedModule localTailMixedConfig localTailMixed_validated) scalars ⟨0, "entry", [], [], []⟩ localTailEntry
  · intro id inside
    change id < 2 at inside
    cases id with
    | zero => exact ⟨_, rfl, Or.inl (Or.inr ⟨[65], 0, rfl, rfl⟩)⟩
    | succ id =>
      cases id with
      | zero => exact ⟨_, rfl, Or.inr ⟨1, 0, ⟨1, "outer", [], [[]], []⟩, localTailOuter,
          rfl, Or.inl ⟨.i64, rfl⟩, rfl, rfl, rfl, rfl, localTailMixed_graph⟩⟩
      | succ id => omega
  · rfl
  · rfl
  · exact .nil
  · simp [localTailEntry, Block.stmts]
  · simp [localTailEntry, Block.stmts]
  · simp [localTailEntry, Block.stmts]
  · simp [localTailEntry, Block.stmts]
  · rfl

#print axioms localTailMixed_module_allFuel
#print axioms localTailMixed_result
#print axioms localTailMixed_graph
#print axioms localTailMixed_validated
#print axioms localTail_module_allFuel
#print axioms localTail_eval_allFuel
#print axioms localTail_invoke_allFuel
#print axioms localTail_result
#print axioms localTail_graph
#print axioms localTail_validated
end Goose.Proofs.ConstructionAcceptedExecution
