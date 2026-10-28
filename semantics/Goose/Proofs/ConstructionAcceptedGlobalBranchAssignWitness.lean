import Goose.Proofs.ConstructionAcceptedAssignConditionalModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def globalBranchAssignEntry : Impl :=
  ⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩

private def globalBranchAssignModule : Module :=
  ⟨#["branch-assign.goose"], #[.int .i64],
    #[⟨"source", .int .i64, .mutable, .lit .i64 1, 0⟩,
      ⟨"number", .int .i64, .immutable,
        .ifE (.bool true) (.mk 0 [.assign (.global 0) (.lit .i64 7) 0] (some (.read (.global 0))))
          (.mk 1 [] (some (.lit .i64 4))) 0, 0⟩],
    #[globalBranchAssignEntry], #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 1, "assign"⟩], #[], #[]⟩

private def globalBranchAssignConfig : EvalConfig := ⟨.release, globalBranchAssignModule⟩

theorem globalBranchAssign_validated : validate globalBranchAssignModule = .ok () := by cbv

private def globalBranchAssignObservation : Option (Int × Int) :=
  match runModule 100 globalBranchAssignConfig .initial with
  | .ok () state => match state.objects.lookup (.global 0), state.objects.lookup (.global 1) with
    | some (.int .i64 first), some (.int .i64 second) => some (first, second)
    | _, _ => none
  | _ => none

theorem globalBranchAssign_result : globalBranchAssignObservation = some (7, 7) := by decide +kernel

theorem globalBranchAssign_allFuel (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld globalBranchAssignConfig initialized
        (Goose.Proofs.Exit.stepState (runModule fuel globalBranchAssignConfig .initial)) ambient types live regions [] ∧
      (match runModule fuel globalBranchAssignConfig .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  apply acceptedAssignConditionalModule_allFuel fuel globalBranchAssignConfig
    (acceptedModule globalBranchAssignConfig globalBranchAssign_validated)
    ⟨0, "entry", [], [], []⟩ globalBranchAssignEntry
  · intro id inside
    change id < 2 at inside
    cases id with
    | zero => exact ⟨_, rfl, Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        ⟨.numeric (.scalar (.scalar (.integer .i64 1))), Or.inl ⟨.i64, rfl⟩⟩))))⟩
    | succ id =>
      cases id with
      | zero =>
        refine ⟨_, rfl, Or.inr ⟨_, _, _, _, _, 0, 1, 0, rfl,
          .numeric (.scalar (.scalar (.boolean true))), .numeric (.scalar (.scalar (.globalRead 0))),
          .numeric (.scalar (.scalar (.integer .i64 4))),
          .assign 0 (.lit .i64 7) 0 [] (.numeric (.scalar (.scalar (.integer .i64 7)))) .nil,
          .nil, ?_, Or.inl ⟨.i64, rfl⟩⟩⟩
        intro global expression origin member target declared
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        obtain ⟨sameGlobal, sameExpression, sameOrigin⟩ := member
        have same : target = ⟨"source", .int .i64, .mutable, .lit .i64 1, 0⟩ := by
          simpa [globalBranchAssignConfig, globalBranchAssignModule] using declared.symm
        subst target
        exact Or.inl ⟨.i64, rfl⟩
      | succ id => omega
  · rfl
  · rfl
  · exact .nil
  · intro declaration member
    simp [globalBranchAssignEntry, Block.stmts] at member
  · intro id expression origin member
    simp [globalBranchAssignEntry, Block.stmts] at member
  · intro id expression origin member
    simp [globalBranchAssignEntry, Block.stmts] at member
  · intro id expression origin member
    simp [globalBranchAssignEntry, Block.stmts] at member
  · rfl

#print axioms globalBranchAssign_allFuel
#print axioms globalBranchAssign_validated
#print axioms globalBranchAssign_result
end Goose.Proofs.ConstructionAcceptedExecution
