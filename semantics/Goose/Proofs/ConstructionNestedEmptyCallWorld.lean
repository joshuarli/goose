import Goose.Proofs.ConstructionNestedEmptyCallWitness
import Goose.Proofs.ConstructionMixedLocalNestedEmptyTail

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem nestedEmptyCallWitness_outcomes (fuel : Nat) :
    (∃ stop after initialized ambient types live regions,
      runModule fuel ⟨.release, nestedEmptyCallWitness⟩ .initial = .stop stop after ∧
      AcceptedWorld ⟨.release, nestedEmptyCallWitness⟩ initialized after ambient types live regions []) ∨
    (∃ after initialized types live regions,
      runModule fuel ⟨.release, nestedEmptyCallWitness⟩ .initial = .ok () after ∧
      AcceptedWorld ⟨.release, nestedEmptyCallWitness⟩ initialized after [] types live regions []) := by
  let config : EvalConfig := ⟨.release, nestedEmptyCallWitness⟩
  let entry : Context := ⟨0, "entry", [], [], []⟩
  let helperContext : Context := ⟨1, "helper", [], [], []⟩
  let statements : List Stmt := [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0, .letS 1 (.lit .i64 7) 0]
  let first : Param := ⟨0, .byValue⟩
  let second : Param := ⟨1, .byValue⟩
  let third : Param := ⟨2, .byValue⟩
  let firstDescriptor : LocalVar := ⟨"first", .int .i64, .immutable, 0, 0⟩
  let secondDescriptor : LocalVar := ⟨"second", .int .i64, .immutable, 0, 0⟩
  let thirdDescriptor : LocalVar := ⟨"third", .int .i64, .immutable, 0, 0⟩
  let expressions : List Expr := [.lit .i64 3,
    .blockE (.mk 1 [.assign (.global 0) (.lit .i64 8) 0] (some (.lit .i64 4))) 0,
    .blockE (.mk 2 [] (some (.blockE (.mk 3 [.assign (.global 0) (.bin .add (.read (.global 0)) (.lit .i64 1) 0) 0] (some (.lit .i64 2))) 0))) 0]
  let entryImpl : Impl := ⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
    ⟨"number", .int .i64, .immutable, 0, 0⟩],
    .mk 0 statements (some (.call 1 (expressions.map Arg.byVal) 0)), .unknown⟩
  let helper : Impl := ⟨"helper", #[first, second, third], #[],
    #[firstDescriptor, secondDescriptor, thirdDescriptor, ⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
      ⟨"flag", .bool, .immutable, 0, 0⟩],
    .mk 0 [.letS 3 (.bytes (.varr (.int .u8)) [66] 0) 0, .letS 4 (.bool false) 0]
      none, .unknown⟩
  apply acceptedMixedLocalModule_nestedEmptyTail fuel config (acceptedModule config nestedEmptyCallWitness_validation)
    entry entryImpl 1 0 helperContext helper expressions [.int .i64, .int .i64, .int .i64]
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
  · exact .byte ⟨0, [65], 0, 0⟩ _ (.scalarLocal 1 (.lit .i64 7) 0 _ (.numeric (.scalar (.scalar (.integer .i64 7)))) .nil)
  · intro declaration member
    simp [statements, entryImpl, Block.stmts, ByteOwnerDeclaration.statement] at member ⊢
    rcases member with ⟨id, rest⟩
    simp [id]
  · intro id expression origin member form descriptor declared
    simp [statements, entryImpl, Block.stmts] at member declared
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
  · rfl
  · rfl
  · rfl
  · rfl
  · exact .cons rfl firstDescriptor rfl rfl (Or.inl ⟨.i64, rfl⟩)
      (.cons rfl secondDescriptor rfl rfl (Or.inl ⟨.i64, rfl⟩)
        (.cons rfl thirdDescriptor rfl rfl (Or.inl ⟨.i64, rfl⟩) (.nil 3)))
  · exact .cons (.flat (.scalar (.numeric (.scalar (.scalar (.integer .i64 3))))))
      (.cons (.flat (.globalAssign 1 0 0 0 (.lit .i64 8) .i64 4 (.numeric (.scalar (.scalar (.integer .i64 8))))))
        (.cons (.nested 2 3 0 0 0 0 (.bin .add (.read (.global 0)) (.lit .i64 1) 0) .i64 2
          (.binary .add 0 (.numeric (.scalar (.scalar (.globalRead 0)))) (.numeric (.scalar (.scalar (.integer .i64 1)))))) .nil))
  · intro expression member scope id origin blockOrigin value intTy literal equal
    simp [expressions] at member
    rcases member with firstMember | secondMember | thirdMember <;> subst expression <;>
      simp_all [entryImpl, Block.scope, config, nestedEmptyCallWitness]
  · intro expression member outerScope innerScope id origin innerOrigin outerOrigin value intTy literal equal
    simp [expressions] at member
    rcases member with firstMember | secondMember | thirdMember <;> subst expression <;>
      simp_all [entryImpl, Block.scope, config, nestedEmptyCallWitness]
  · exact .byte ⟨3, [66], 0, 0⟩ _ (.scalarLocal 4 (.bool false) 0 _ (.numeric (.scalar (.scalar (.boolean false)))) .nil)
  · rfl
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

theorem nestedEmptyCallWitness_world (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld ⟨.release, nestedEmptyCallWitness⟩ initialized
        (Goose.Proofs.Exit.stepState (runModule fuel ⟨.release, nestedEmptyCallWitness⟩ .initial)) ambient types live regions [] ∧
      (match runModule fuel ⟨.release, nestedEmptyCallWitness⟩ .initial with
      | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  rcases nestedEmptyCallWitness_outcomes fuel with stopped | completed
  · obtain ⟨reason, after, initialized, ambient, types, live, regions, same, world⟩ := stopped
    exact ⟨initialized, ambient, types, live, regions, by simpa [same, Goose.Proofs.Exit.stepState] using world, by simp [same]⟩
  · obtain ⟨after, initialized, types, live, regions, same, world⟩ := completed
    exact ⟨initialized, [], types, live, regions, by simpa [same, Goose.Proofs.Exit.stepState] using world, by simp [same]⟩

theorem nestedEmptyCallWitness_success_world :
    ∃ after initialized ambient types live regions,
      runModule 100 ⟨.release, nestedEmptyCallWitness⟩ .initial = .ok () after ∧
      after.objects.lookup (.global 0) = some (.int .i64 9) ∧
      AcceptedWorld ⟨.release, nestedEmptyCallWitness⟩ initialized after ambient types live regions [] := by
  obtain ⟨initialized, ambient, types, live, regions, world, flow⟩ := nestedEmptyCallWitness_world 100
  have effects := nestedEmptyCallWitness_effects
  cases outcome : runModule 100 ⟨.release, nestedEmptyCallWitness⟩ .initial with
  | stop reason after | escape address carriers after | jump target kind after => simp [outcome] at effects
  | ok value after =>
    cases value
    simp only [outcome, Goose.Proofs.Exit.stepState] at world
    simp only [outcome] at effects
    exact ⟨after, initialized, ambient, types, live, regions, rfl, effects, world⟩

#print axioms nestedEmptyCallWitness_outcomes
#print axioms nestedEmptyCallWitness_world
#print axioms nestedEmptyCallWitness_success_world
end Goose.Proofs.ConstructionAcceptedExecution
