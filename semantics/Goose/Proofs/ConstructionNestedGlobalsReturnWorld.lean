import Goose.Proofs.ConstructionNestedGlobalsReturnWitness
import Goose.Proofs.ConstructionAcceptedNestedScalarGlobalsSequence

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem nestedGlobalsReturnWitness_world (fuel : Nat) :
    ∃ initialized ambient types live regions,
      AcceptedWorld ⟨.release, nestedGlobalsReturnWitness⟩ initialized
        (Goose.Proofs.Exit.stepState (runModule fuel ⟨.release, nestedGlobalsReturnWitness⟩ .initial)) ambient types live regions [] ∧
      (match runModule fuel ⟨.release, nestedGlobalsReturnWitness⟩ .initial with
      | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  let config : EvalConfig := ⟨.release, nestedGlobalsReturnWitness⟩
  let entry : Context := ⟨0, "entry", [], [], []⟩
  let helperContext : Context := ⟨1, "helper", [], [[]], []⟩
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
    ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"result", .int .i64, .immutable, 0, 0⟩],
    .mk 0 (statements ++ [.letS 2 (.call 1 (expressions.map Arg.byVal) 0) 0]) none, .unknown⟩
  let helper : Impl := ⟨"helper", #[first, second, third], #[⟨.int .i64, .register, none⟩],
    #[firstDescriptor, secondDescriptor, thirdDescriptor],
    .mk 0 [.assign (.global 0) (.bin .add (.read (.global 0)) (.read (.var 2)) 0) 0, .assign (.global 0) (.bin .add (.read (.global 0)) (.lit .i64 1) 0) 0]
      (some (.bin .add (.bin .sub (.read (.var 1)) (.read (.var 0)) 0) (.read (.var 2)) 0)), .unknown⟩
  apply acceptedModule_nestedScalarGlobals_allFuel fuel config (acceptedModule config nestedGlobalsReturnWitness_validation)
    entry entryImpl statements 2 0 1 0 helperContext helper expressions [.int .i64, .int .i64, .int .i64]
    (.int .i64) (.bin .add (.bin .sub (.read (.var 1)) (.read (.var 0)) 0) (.read (.var 2)) 0)
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
  · intro expression member scope id origin blockOrigin value intTy literal equal
    simp [expressions] at member
    rcases member with firstMember | secondMember | thirdMember <;> subst expression <;>
      simp_all [entryImpl, Block.scope, config, nestedGlobalsReturnWitness]
  · intro expression member outerScope innerScope id origin innerOrigin outerOrigin value intTy literal equal
    simp [expressions] at member
    rcases member with firstMember | secondMember | thirdMember <;> subst expression <;>
      simp_all [entryImpl, Block.scope, config, nestedGlobalsReturnWitness]
  · rfl
  · rfl
  · exact .cons rfl firstDescriptor rfl rfl (Or.inl ⟨.i64, rfl⟩)
      (.cons rfl secondDescriptor rfl rfl (Or.inl ⟨.i64, rfl⟩)
        (.cons rfl thirdDescriptor rfl rfl (Or.inl ⟨.i64, rfl⟩) (.nil 3)))
  · rfl
  · exact Or.inl ⟨.i64, rfl⟩
  · exact .cons (.flat (.scalar (.numeric (.scalar (.scalar (.integer .i64 3))))))
      (.cons (.flat (.globalAssign 1 0 0 0 (.lit .i64 8) .i64 4 (.numeric (.scalar (.scalar (.integer .i64 8))))))
        (.cons (.nested 2 3 0 0 0 0 (.bin .add (.read (.global 0)) (.lit .i64 1) 0) .i64 2
          (.binary .add 0 (.numeric (.scalar (.scalar (.globalRead 0)))) (.numeric (.scalar (.scalar (.integer .i64 1)))))) .nil))
  · rfl
  · exact .binary .add 0 (.binary .sub 0 (.numeric (.scalar (.scalar (.localRead 1)))) (.numeric (.scalar (.scalar (.localRead 0))))) (.numeric (.scalar (.scalar (.localRead 2))))
  · exact .cons 0 _ 0 _ (.binary .add 0 (.numeric (.scalar (.scalar (.globalRead 0)))) (.numeric (.scalar (.scalar (.localRead 2)))))
      (.cons 0 _ 0 _ (.binary .add 0 (.numeric (.scalar (.scalar (.globalRead 0)))) (.numeric (.scalar (.scalar (.integer .i64 1))))) .nil)
  · intro id expression origin member descriptor declared
    simp [helper, Block.stmts] at member
    rcases member with member | member <;> rcases member with ⟨rfl, rfl, rfl⟩ <;> simp [config, nestedGlobalsReturnWitness] at declared <;> subst descriptor <;> exact Or.inl ⟨.i64, rfl⟩

theorem nestedGlobalsReturnWitness_success_world :
    ∃ after initialized ambient types live regions,
      runModule 80 ⟨.release, nestedGlobalsReturnWitness⟩ .initial = .ok () after ∧
      after.objects.lookup (.global 0) = some (.int .i64 12) ∧
      AcceptedWorld ⟨.release, nestedGlobalsReturnWitness⟩ initialized after ambient types live regions [] := by
  obtain ⟨initialized, ambient, types, live, regions, world, flow⟩ := nestedGlobalsReturnWitness_world 80
  have effects := nestedGlobalsReturnWitness_effects
  cases outcome : runModule 80 ⟨.release, nestedGlobalsReturnWitness⟩ .initial with
  | stop reason after | escape address carriers after | jump target kind after => simp [outcome] at effects
  | ok value after =>
    cases value
    simp only [outcome, Goose.Proofs.Exit.stepState] at world
    simp only [outcome] at effects
    exact ⟨after, initialized, ambient, types, live, regions, rfl, effects, world⟩


#print axioms nestedGlobalsReturnWitness_world
#print axioms nestedGlobalsReturnWitness_success_world
end Goose.Proofs.ConstructionAcceptedExecution
