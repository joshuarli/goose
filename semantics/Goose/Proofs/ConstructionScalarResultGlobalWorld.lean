import Goose.Proofs.ConstructionAcceptedRegisterGlobalAssignmentsContract
import Goose.Proofs.ConstructionScalarResultGlobalWitness

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem scalarResultGlobalWitness_world (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld ⟨.release, scalarResultGlobalWitness⟩ initialized
        (Goose.Proofs.Exit.stepState (runModule fuel ⟨.release, scalarResultGlobalWitness⟩ .initial)) ambient types live regions [] ∧
      (match runModule fuel ⟨.release, scalarResultGlobalWitness⟩ .initial with
      | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let config : EvalConfig := ⟨.release, scalarResultGlobalWitness⟩
  let entry : Context := ⟨0, "entry", [], [], []⟩
  let helperContext : Context := ⟨1, "helper", [], [[]], []⟩
  let statements : List Stmt := [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0,
    .letS 1 (.lit .i64 7) 0, .expr (.read (.var 1)) 0,
    .letS 2 (.bool true) 0, .expr (.not (.read (.var 2))) 0]
  let entryImpl : Impl := ⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
    ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩,
    ⟨"result", .int .i64, .immutable, 0, 0⟩],
    .mk 0 (statements ++ (.letS 3 (.call 1 [.byVal (.lit .i64 7)] 0) 0 ::
      (globalIntegerAssignments [⟨0, .i64, 9, 0⟩] ++ [.print [.expr (.read (.var 3))] 0]))) none, .unknown⟩
  let parameter : Param := ⟨0, .byValue⟩
  let descriptor : LocalVar := ⟨"parameter", .int .i64, .immutable, 0, 0⟩
  let helper : Impl := ⟨"helper", #[parameter], #[⟨.int .i64, .register, none⟩],
    #[descriptor, ⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
      ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩],
    .mk 0 [.letS 1 (.bytes (.varr (.int .u8)) [66, 67] 0) 0, .letS 2 (.read (.var 0)) 0,
      .expr (.read (.var 2)) 0, .letS 3 (.bool false) 0, .expr (.not (.read (.var 3))) 0]
      (some (.read (.var 0))), .unknown⟩
  apply acceptedModule_checkedRecursiveSequence_allFuel fuel config (acceptedModule config scalarResultGlobalWitness_validation)
    entry entryImpl
  · intro id bound
    change id < 2 at bound
    cases id with
    | zero =>
      exact ⟨_, rfl, Or.inl ⟨.binary .add 0 (.numeric (.scalar (.scalar (.integer .i64 2))))
        (.numeric (.scalar (.scalar (.integer .i64 3)))), Or.inl ⟨.i64, rfl⟩⟩⟩
    | succ id =>
      cases id with
      | zero => exact ⟨_, rfl, Or.inr ⟨[71], 0, rfl, rfl⟩⟩
      | succ id => omega
  · rfl
  · rfl
  · rfl
  · apply checkedSequence_registerGlobalAssignmentsPrint config (acceptedModule config scalarResultGlobalWitness_validation)
      entry entryImpl statements 1 0 3 0 0 [⟨0, .i64, 9, 0⟩] (.lit .i64 7)
      helperContext helper parameter descriptor (.int .i64) (.read (.var 0))
    · rfl
    · rfl
    · rfl
    · change MixedLocalStatements
        [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0, .letS 1 (.lit .i64 7) 0,
          .expr (.read (.var 1)) 0, .letS 2 (.bool true) 0, .expr (.not (.read (.var 2))) 0]
      exact .byte ⟨0, [65], 0, 0⟩ _
        (.scalarLocal 1 (.lit .i64 7) 0 _ (.numeric (.scalar (.scalar (.integer .i64 7))))
          (.scalar (.read (.var 1)) 0 _ (.numeric (.scalar (.scalar (.localRead 1))))
            (.scalarLocal 2 (.bool true) 0 _ (.numeric (.scalar (.scalar (.boolean true))))
              (.scalar (.not (.read (.var 2))) 0 _ (.not (.numeric (.scalar (.scalar (.localRead 2))))) .nil))))
    · intro declaration member
      simp [statements, entryImpl, ByteOwnerDeclaration.statement] at member ⊢
      rcases member with ⟨id, rest⟩
      simp [id]
    · intro id expression origin member form descriptor declared
      simp [statements, entryImpl] at member declared
      rcases member with first | second | third
      · rcases first with ⟨rfl, rfl, rfl⟩
        cases form with
        | numeric form => cases form with
          | scalar form => cases form with
            | scalar form => cases form
      · rcases second with ⟨rfl, rfl, rfl⟩
        simp at declared
        subst descriptor
        exact Or.inl ⟨.i64, rfl⟩
      · rcases third with ⟨rfl, rfl, rfl⟩
        simp at declared
        subst descriptor
        exact Or.inr rfl
    · intro localDescriptor declared
      simp [entryImpl] at declared
      subst localDescriptor
      exact Or.inl ⟨.i64, rfl⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact Or.inl ⟨.i64, rfl⟩
    · exact Or.inl ⟨.i64, rfl⟩
    · intro assignment member
      simp only [List.mem_singleton] at member
      subst assignment
      exact ⟨_, rfl, rfl⟩
    · exact .numeric (.scalar (.scalar (.integer .i64 7)))
    · change MixedLocalStatements
        [.letS 1 (.bytes (.varr (.int .u8)) [66, 67] 0) 0,
          .letS 2 (.read (.var 0)) 0, .expr (.read (.var 2)) 0,
          .letS 3 (.bool false) 0, .expr (.not (.read (.var 3))) 0]
      exact .byte ⟨1, [66, 67], 0, 0⟩ _
        (.scalarLocal 2 (.read (.var 0)) 0 _ (.numeric (.scalar (.scalar (.localRead 0))))
          (.scalar (.read (.var 2)) 0 _ (.numeric (.scalar (.scalar (.localRead 2))))
            (.scalarLocal 3 (.bool false) 0 _ (.numeric (.scalar (.scalar (.boolean false))))
              (.scalar (.not (.read (.var 3))) 0 _ (.not (.numeric (.scalar (.scalar (.localRead 3))))) .nil))))
    · rfl
    · exact .numeric (.scalar (.scalar (.localRead 0)))
    · intro declaration member
      simp [helper, Block.stmts, ByteOwnerDeclaration.statement] at member ⊢
      rcases member with ⟨id, rest⟩
      simp [id]
    · intro id expression origin member form descriptor declared
      simp [helper, Block.stmts] at member declared
      rcases member with first | second | third
      · rcases first with ⟨rfl, rfl, rfl⟩
        cases form with
        | numeric form => cases form with
          | scalar form => cases form with
            | scalar form => cases form
      · rcases second with ⟨rfl, rfl, rfl⟩
        simp at declared
        subst descriptor
        exact Or.inl ⟨.i64, rfl⟩
      · rcases third with ⟨rfl, rfl, rfl⟩
        simp at declared
        subst descriptor
        exact Or.inr rfl

theorem scalarResultGlobalWitness_success_world :
    ∃ after initialized ambient types live regions,
      runModule 50 ⟨.release, scalarResultGlobalWitness⟩ .initial = .ok () after ∧
      AcceptedWorld ⟨.release, scalarResultGlobalWitness⟩ initialized after ambient types live regions [] := by
  obtain ⟨initialized, ambient, types, live, regions, world, flow⟩ := scalarResultGlobalWitness_world 50
  have returns := scalarResultGlobalWitness_returns
  cases outcome : runModule 50 ⟨.release, scalarResultGlobalWitness⟩ .initial with
  | stop reason after | escape reason carriers after | jump reason kind after =>
    simp [scalarResultGlobalWitnessReturns, outcome] at returns
  | ok value after =>
    cases value
    simp only [outcome, Goose.Proofs.Exit.stepState] at world
    exact ⟨after, initialized, ambient, types, live, regions, rfl, world⟩

theorem scalarResultGlobalWitness_success_effects_world :
    ∃ after initialized ambient types live regions,
      runModule 50 ⟨.release, scalarResultGlobalWitness⟩ .initial = .ok () after ∧
      after.construction.stdout = "7\n".toUTF8 ∧
      after.objects.lookup (.global 0) = some (.int .i64 9) ∧
      AcceptedWorld ⟨.release, scalarResultGlobalWitness⟩ initialized after ambient types live regions [] := by
  obtain ⟨after, initialized, ambient, types, live, regions, executed, world⟩ := scalarResultGlobalWitness_success_world
  have output := scalarResultGlobalWitness_returns
  simp only [scalarResultGlobalWitnessReturns, executed, Bool.and_eq_true] at output
  have outputBytes := output.1
  change (after.construction.stdout.data == "7\n".toUTF8.data) = true at outputBytes
  have equalData := beq_iff_eq.mp outputBytes
  have assignment := scalarResultGlobalWitness_assignment
  simp only [executed] at assignment
  exact ⟨after, initialized, ambient, types, live, regions, executed, ByteArray.ext equalData, assignment, world⟩

#print axioms scalarResultGlobalWitness_success_effects_world
#print axioms scalarResultGlobalWitness_success_world
#print axioms scalarResultGlobalWitness_world
end Goose.Proofs.ConstructionAcceptedExecution
