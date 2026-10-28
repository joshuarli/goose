import Goose.Proofs.ConstructionAcceptedRecursiveRegisterCall
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

#print axioms localTail_invoke_allFuel
#print axioms localTail_result
#print axioms localTail_graph
#print axioms localTail_validated
end Goose.Proofs.ConstructionAcceptedExecution
