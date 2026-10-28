import Goose.Proofs.ConstructionAcceptedMixedRegisterModule
import Goose.Proofs.ConstructionScalarResultNoPrintWitness

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem scalarResultNoPrintWitness_world (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld ⟨.release, scalarResultNoPrintWitness⟩ initialized
        (Goose.Proofs.Exit.stepState (runModule fuel ⟨.release, scalarResultNoPrintWitness⟩ .initial)) ambient types live regions [] ∧
      (match runModule fuel ⟨.release, scalarResultNoPrintWitness⟩ .initial with
      | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let config : EvalConfig := ⟨.release, scalarResultNoPrintWitness⟩
  let entry : Context := ⟨0, "entry", [], [], []⟩
  let helperContext : Context := ⟨1, "helper", [], [[]], []⟩
  let statements : List Stmt := [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0,
    .letS 1 (.lit .i64 7) 0, .expr (.read (.var 1)) 0,
    .letS 2 (.bool true) 0, .expr (.not (.read (.var 2))) 0]
  let entryImpl : Impl := ⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
    ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩,
    ⟨"result", .int .i64, .immutable, 0, 0⟩],
    .mk 0 (statements ++ [.letS 3 (.call 1 [.byVal (.lit .i64 7)] 0) 0]) none, .unknown⟩
  let parameter : Param := ⟨0, .byValue⟩
  let descriptor : LocalVar := ⟨"parameter", .int .i64, .immutable, 0, 0⟩
  let helper : Impl := ⟨"helper", #[parameter], #[⟨.int .i64, .register, none⟩],
    #[descriptor, ⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
      ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩],
    .mk 0 [.letS 1 (.bytes (.varr (.int .u8)) [66, 67] 0) 0, .letS 2 (.read (.var 0)) 0,
      .expr (.read (.var 2)) 0, .letS 3 (.bool false) 0, .expr (.not (.read (.var 3))) 0]
      (some (.read (.var 0))), .unknown⟩
  apply acceptedModule_mixedRegisterLet_allFuel fuel config (acceptedModule config scalarResultNoPrintWitness_validation)
    entry entryImpl statements 1 0 3 0 (.lit .i64 7) helperContext helper parameter descriptor (.int .i64) (.read (.var 0))
  · intro id bound
    simp [config, scalarResultNoPrintWitness] at bound
  · rfl
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

theorem scalarResultNoPrintWitness_success_world :
    ∃ after initialized ambient types live regions,
      runModule 50 ⟨.release, scalarResultNoPrintWitness⟩ .initial = .ok () after ∧
      AcceptedWorld ⟨.release, scalarResultNoPrintWitness⟩ initialized after ambient types live regions [] := by
  obtain ⟨initialized, ambient, types, live, regions, world, flow⟩ := scalarResultNoPrintWitness_world 50
  have returns := scalarResultNoPrintWitness_returns
  cases outcome : runModule 50 ⟨.release, scalarResultNoPrintWitness⟩ .initial with
  | stop reason after | escape reason carriers after | jump reason kind after =>
    simp [scalarResultNoPrintWitnessReturns, outcome] at returns
  | ok value after =>
    cases value
    simp only [outcome, Goose.Proofs.Exit.stepState] at world
    exact ⟨after, initialized, ambient, types, live, regions, rfl, world⟩

#print axioms scalarResultNoPrintWitness_success_world
#print axioms scalarResultNoPrintWitness_world
end Goose.Proofs.ConstructionAcceptedExecution
