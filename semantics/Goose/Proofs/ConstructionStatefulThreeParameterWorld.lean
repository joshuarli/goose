import Goose.Proofs.ConstructionStatefulThreeParameterWitness
import Goose.Proofs.ConstructionAcceptedArgumentListSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem statefulThreeParameterWitness_world (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld ⟨.release, statefulThreeParameterWitness⟩ initialized
        (Goose.Proofs.Exit.stepState (runModule fuel ⟨.release, statefulThreeParameterWitness⟩ .initial)) ambient types live regions [] ∧
      (match runModule fuel ⟨.release, statefulThreeParameterWitness⟩ .initial with
      | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let config : EvalConfig := ⟨.release, statefulThreeParameterWitness⟩
  let entry : Context := ⟨0, "entry", [], [], []⟩
  let helperContext : Context := ⟨1, "helper", [], [[]], []⟩
  let statements : List Stmt := [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0, .letS 1 (.lit .i64 7) 0]
  let first : Param := ⟨0, .byValue⟩
  let second : Param := ⟨1, .byValue⟩
  let third : Param := ⟨2, .byValue⟩
  let firstDescriptor : LocalVar := ⟨"first", .int .i64, .immutable, 0, 0⟩
  let secondDescriptor : LocalVar := ⟨"second", .int .i64, .immutable, 0, 0⟩
  let thirdDescriptor : LocalVar := ⟨"third", .int .i64, .immutable, 0, 0⟩
  let entryImpl : Impl := ⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
    ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"result", .int .i64, .immutable, 0, 0⟩],
    .mk 0 (statements ++ [.letS 2 (.call 1 [.byVal (.blockE (.mk 1
      [.assign (.global 0) (.lit .i64 8) 0] (some (.lit .i64 3))) 0), .byVal (.read (.global 0)), .byVal (.lit .i64 2)] 0) 0]) none, .unknown⟩
  let helper : Impl := ⟨"helper", #[first, second, third], #[⟨.int .i64, .register, none⟩],
    #[firstDescriptor, secondDescriptor, thirdDescriptor, ⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
      ⟨"flag", .bool, .immutable, 0, 0⟩],
    .mk 0 [.letS 3 (.bytes (.varr (.int .u8)) [66] 0) 0, .letS 4 (.bool false) 0]
      (some (.bin .add (.bin .sub (.read (.var 1)) (.read (.var 0)) 0) (.read (.var 2)) 0)), .unknown⟩
  apply acceptedModule_statefulArgumentList_allFuel fuel config (acceptedModule config statefulThreeParameterWitness_validation)
    entry entryImpl statements 2 0 1 0 helperContext helper first [second, third] firstDescriptor [.int .i64, .int .i64]
    1 0 0 0 (.lit .i64 8) .i64 3 [.read (.global 0), .lit .i64 2] (.int .i64) (.bin .add (.bin .sub (.read (.var 1)) (.read (.var 0)) 0) (.read (.var 2)) 0)
  · intro globalId bound
    change globalId < 2 at bound
    cases globalId with
    | zero => exact ⟨_, rfl, Or.inl ⟨.binary .add 0 (.numeric (.scalar (.scalar (.integer .i64 2))))
        (.numeric (.scalar (.scalar (.integer .i64 3)))), Or.inl ⟨.i64, rfl⟩⟩⟩
    | succ globalId =>
      cases globalId with
      | zero => exact ⟨_, rfl, Or.inr ⟨[71], 0, rfl, rfl⟩⟩
      | succ globalId => omega
  · rfl
  · rfl
  · rfl
  · rfl
  · exact .byte ⟨0, [65], 0, 0⟩ _ (.scalarLocal 1 (.lit .i64 7) 0 _ (.numeric (.scalar (.scalar (.integer .i64 7)))) .nil)
  · intro declaration member
    simp [statements, entryImpl, ByteOwnerDeclaration.statement] at member ⊢
    rcases member with ⟨id, rest⟩
    simp [id]
  · intro id expression origin member form descriptor declared
    simp [statements, entryImpl] at member declared
    rcases member with first | second
    · rcases first with ⟨rfl, rfl, rfl⟩
      cases form with
      | numeric form => cases form with
        | scalar form => cases form with
          | scalar form => cases form
    · rcases second with ⟨rfl, rfl, rfl⟩
      simp at declared
      subst descriptor
      exact Or.inl ⟨.i64, rfl⟩
  · intro descriptor declared
    simp [entryImpl] at declared
    subst descriptor
    exact Or.inl ⟨.i64, rfl⟩
  · decide
  · intro descriptor member
    simp [entryImpl] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro descriptor declared
    simp [config, statefulThreeParameterWitness] at declared
    subst descriptor
    exact Or.inl ⟨.i64, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact Or.inl ⟨.i64, rfl⟩
  · exact .cons rfl secondDescriptor rfl rfl (Or.inl ⟨.i64, rfl⟩)
      (.cons rfl thirdDescriptor rfl rfl (Or.inl ⟨.i64, rfl⟩) (.nil 3))
  · rfl
  · exact Or.inl ⟨.i64, rfl⟩
  · exact .numeric (.scalar (.scalar (.integer .i64 8)))
  · exact .cons (.numeric (.scalar (.scalar (.globalRead 0))))
      (.cons (.numeric (.scalar (.scalar (.integer .i64 2)))) .nil)
  · exact .byte ⟨3, [66], 0, 0⟩ _ (.scalarLocal 4 (.bool false) 0 _ (.numeric (.scalar (.scalar (.boolean false)))) .nil)
  · rfl
  · exact .binary .add 0 (.binary .sub 0 (.numeric (.scalar (.scalar (.localRead 1)))) (.numeric (.scalar (.scalar (.localRead 0))))) (.numeric (.scalar (.scalar (.localRead 2))))
  · intro declaration member
    simp [helper, Block.stmts, ByteOwnerDeclaration.statement] at member ⊢
    rcases member with ⟨id, rest⟩
    simp [id]
  · intro id expression origin member form descriptor declared
    simp [helper, Block.stmts] at member declared
    rcases member with first | second
    · rcases first with ⟨rfl, rfl, rfl⟩
      cases form with
      | numeric form => cases form with
        | scalar form => cases form with
          | scalar form => cases form
    · rcases second with ⟨rfl, rfl, rfl⟩
      simp at declared
      subst descriptor
      exact Or.inr rfl

theorem statefulThreeParameterWitness_success_world :
    ∃ after initialized ambient types live regions,
      runModule 80 ⟨.release, statefulThreeParameterWitness⟩ .initial = .ok () after ∧
      after.objects.lookup (.global 0) = some (.int .i64 8) ∧
      AcceptedWorld ⟨.release, statefulThreeParameterWitness⟩ initialized after ambient types live regions [] := by
  obtain ⟨initialized, ambient, types, live, regions, world, flow⟩ := statefulThreeParameterWitness_world 80
  have effects := statefulThreeParameterWitness_effects
  cases outcome : runModule 80 ⟨.release, statefulThreeParameterWitness⟩ .initial with
  | stop reason after | escape address carriers after | jump target kind after => simp [outcome] at effects
  | ok value after =>
    cases value
    simp only [outcome, Goose.Proofs.Exit.stepState] at world
    simp only [outcome] at effects
    exact ⟨after, initialized, ambient, types, live, regions, rfl, effects, world⟩


#print axioms statefulThreeParameterWitness_world
#print axioms statefulThreeParameterWitness_success_world
end Goose.Proofs.ConstructionAcceptedExecution
