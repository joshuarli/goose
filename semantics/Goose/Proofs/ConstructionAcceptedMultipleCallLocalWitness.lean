import Goose.Proofs.ConstructionAcceptedCallLocalGraphModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

private def multipleCallSummary : SummaryAnn := .known ⟨[], [], [], [], [], [], [], [], false, false⟩
private def multipleCallEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [] none, multipleCallSummary⟩
private def multipleCallLeaf : Impl := ⟨"leaf", #[], #[⟨.int .i64, .register, none⟩], #[],
  .mk 0 [] (some (.lit .i64 7)), multipleCallSummary⟩
private def multipleCallHelper : Impl := ⟨"cycle", #[], #[⟨.int .i64, .register, none⟩],
  #[⟨"first", .int .i64, .immutable, 0, 0⟩, ⟨"second", .int .i64, .immutable, 0, 0⟩],
  .mk 0 [.letS 0 (.call 2 [] 0) 0, .letS 1 (.call 1 [] 0) 0] (some (.read (.var 1))), multipleCallSummary⟩
private def multipleCallModule : Module := ⟨#["multiple-local-calls.goose"], #[.int .i64],
  #[⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩], #[multipleCallEntry, multipleCallHelper, multipleCallLeaf],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "cycle", [], [[]], []⟩, ⟨2, "leaf", [], [[]], []⟩],
  0, #[⟨0, 1, "call"⟩], #[], #[]⟩
private def multipleCallConfig : EvalConfig := ⟨.release, multipleCallModule⟩

theorem multipleCall_validated : validate multipleCallModule = .ok () := by cbv

theorem multipleCall_graph : RegisterCallGraphWithCallLocals multipleCallConfig (.int .i64) := by
  intro target context implementation contextAt implementationAt parameters results
  cases target with
  | zero =>
    simp [multipleCallConfig, multipleCallModule] at contextAt
    subst context
    simp [multipleCallConfig, multipleCallModule] at implementationAt
    subst implementation
    simp [multipleCallEntry] at results
  | succ target =>
    cases target with
    | zero =>
      simp [multipleCallConfig, multipleCallModule] at contextAt
      subst context
      simp [multipleCallConfig, multipleCallModule] at implementationAt
      subst implementation
      apply Or.inr
      refine ⟨_, 0, [.letS 0 (.call 2 [] 0) 0, .letS 1 (.call 1 [] 0) 0], .read (.var 1), rfl, rfl, ?_, ?_, ?_⟩
      · apply CallLocalStatements.call 0 2 0 0 _ ⟨2, "leaf", [], [[]], []⟩ multipleCallLeaf rfl rfl rfl rfl
        exact .call 1 1 0 0 [] ⟨1, "cycle", [], [[]], []⟩ multipleCallHelper rfl rfl rfl rfl .nil
      · repeat constructor
      · intro id expression origin member descriptor found
        simp at member
        rcases member with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
          simp [multipleCallHelper] at found <;> subst descriptor <;> exact Or.inl ⟨.i64, rfl⟩
    | succ target =>
      cases target with
      | zero =>
        simp [multipleCallConfig, multipleCallModule] at contextAt
        subst context
        simp [multipleCallConfig, multipleCallModule] at implementationAt
        subst implementation
        apply Or.inl
        refine ⟨_, rfl, Or.inl ⟨0, [], .lit .i64 7, rfl, .nil, ?_, ?_⟩⟩
        · repeat constructor
        · intro id expression origin member
          cases member
      | succ target => simp [multipleCallConfig, multipleCallModule] at contextAt

private def multipleCallProgress : Bool :=
  match runModule 40 multipleCallConfig .initial with
  | .stop .timeout state =>
    match state.objects.lookup (.local 1 0 0) with
    | some (.int .i64 value) => decide (value = 7)
    | _ => false
  | _ => false

theorem multipleCall_firstBound : multipleCallProgress = true := by decide +kernel

theorem multipleCall_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld multipleCallConfig initialized (Goose.Proofs.Exit.stepState (runModule fuel multipleCallConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel multipleCallConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let descriptor : Global := ⟨"answer", .int .i64, .immutable, .call 1 [] 0, 0⟩
  let context : Context := ⟨1, "cycle", [], [[]], []⟩
  apply acceptedCallLocalGraphModule_allFuel fuel multipleCallConfig (acceptedModule multipleCallConfig multipleCall_validated)
    descriptor 1 0 context multipleCallHelper (by rfl) (by rfl) (by rfl) (Or.inl ⟨.i64, rfl⟩)
    (by rfl) (by rfl) (by rfl) (by rfl) multipleCall_graph ⟨0, "entry", [], [], []⟩ multipleCallEntry (by rfl) (by rfl)
  · exact .nil
  · simp [multipleCallEntry, Block.stmts]
  · simp [multipleCallEntry, Block.stmts]
  · simp [multipleCallEntry, Block.stmts]
  · simp [multipleCallEntry, Block.stmts]
  · rfl

#print axioms multipleCall_allFuel
#print axioms multipleCall_firstBound
#print axioms multipleCall_graph
#print axioms multipleCall_validated
end Goose.Proofs.ConstructionAcceptedExecution
