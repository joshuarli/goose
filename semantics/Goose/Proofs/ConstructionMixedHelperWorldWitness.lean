import Goose.Proofs.ConstructionMixedLocalModuleHelperTail
import Goose.Proofs.ConstructionMixedHelperWitness

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem mixedHelperWitness_world (fuel : Nat) :
    (∃ stop after initialized ambient types live regions,
      runModule fuel ⟨.release, mixedHelperWitness⟩ .initial = .stop stop after ∧
      AcceptedWorld ⟨.release, mixedHelperWitness⟩ initialized after ambient types live regions []) ∨
    (∃ after initialized types live regions,
      runModule fuel ⟨.release, mixedHelperWitness⟩ .initial = .ok () after ∧
      AcceptedWorld ⟨.release, mixedHelperWitness⟩ initialized after [] types live regions []) := by
  let config : EvalConfig := ⟨.release, mixedHelperWitness⟩
  let entry : Context := ⟨0, "entry", [], [], []⟩
  let helperContext : Context := ⟨1, "helper", [], [], []⟩
  let entryImpl : Impl := ⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
    ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0, .letS 1 (.lit .i64 7) 0,
      .expr (.read (.var 1)) 0, .letS 2 (.bool true) 0, .expr (.not (.read (.var 2))) 0]
      (some (.call 1 [] 0)), .unknown⟩
  let helper : Impl := ⟨"helper", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩,
    ⟨"number", .int .i64, .immutable, 0, 0⟩, ⟨"flag", .bool, .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [66, 67] 0) 0, .letS 1 (.lit .i64 9) 0,
      .expr (.read (.var 1)) 0, .letS 2 (.bool false) 0, .expr (.not (.read (.var 2))) 0] none, .unknown⟩
  apply acceptedMixedLocalModule_mixedHelperTail fuel config (acceptedModule config mixedHelperWitness_validation)
    entry entryImpl 1 0 helperContext helper
  · intro id bound
    simp [config, mixedHelperWitness] at bound
  · rfl
  · rfl
  · change MixedLocalStatements
      [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0,
        .letS 1 (.lit .i64 7) 0, .expr (.read (.var 1)) 0,
        .letS 2 (.bool true) 0, .expr (.not (.read (.var 2))) 0]
    exact .byte ⟨0, [65], 0, 0⟩ _
      (.scalarLocal 1 (.lit .i64 7) 0 _ (.numeric (.scalar (.scalar (.integer .i64 7))))
        (.scalar (.read (.var 1)) 0 _ (.numeric (.scalar (.scalar (.localRead 1))))
          (.scalarLocal 2 (.bool true) 0 _ (.numeric (.scalar (.scalar (.boolean true))))
            (.scalar (.not (.read (.var 2))) 0 _ (.not (.numeric (.scalar (.scalar (.localRead 2))))) .nil))))
  · intro declaration member
    simp [entryImpl, Block.stmts, ByteOwnerDeclaration.statement] at member ⊢
    rcases member with ⟨id, rest⟩
    simp [id]
  · intro id expression origin member form descriptor declared
    simp [entryImpl, Block.stmts] at member declared
    rcases member with first | second | third
    · rcases first with ⟨rfl, rfl, rfl⟩
      cases form with
      | numeric form =>
        cases form with
        | scalar form =>
          cases form with
          | scalar form => cases form
    · rcases second with ⟨rfl, rfl, rfl⟩
      simp at declared
      subst descriptor
      exact Or.inl ⟨.i64, rfl⟩
    · rcases third with ⟨rfl, rfl, rfl⟩
      simp at declared
      subst descriptor
      exact Or.inr rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · change MixedLocalStatements
      [.letS 0 (.bytes (.varr (.int .u8)) [66, 67] 0) 0,
        .letS 1 (.lit .i64 9) 0, .expr (.read (.var 1)) 0,
        .letS 2 (.bool false) 0, .expr (.not (.read (.var 2))) 0]
    exact .byte ⟨0, [66, 67], 0, 0⟩ _
      (.scalarLocal 1 (.lit .i64 9) 0 _ (.numeric (.scalar (.scalar (.integer .i64 9))))
        (.scalar (.read (.var 1)) 0 _ (.numeric (.scalar (.scalar (.localRead 1))))
          (.scalarLocal 2 (.bool false) 0 _ (.numeric (.scalar (.scalar (.boolean false))))
            (.scalar (.not (.read (.var 2))) 0 _ (.not (.numeric (.scalar (.scalar (.localRead 2))))) .nil))))
  · rfl
  · intro declaration member
    simp [helper, Block.stmts, ByteOwnerDeclaration.statement] at member ⊢
    rcases member with ⟨id, rest⟩
    simp [id]
  · intro id expression origin member form descriptor declared
    simp [helper, Block.stmts] at member declared
    rcases member with first | second | third
    · rcases first with ⟨rfl, rfl, rfl⟩
      cases form with
      | numeric form =>
        cases form with
        | scalar form =>
          cases form with
          | scalar form => cases form
    · rcases second with ⟨rfl, rfl, rfl⟩
      simp at declared
      subst descriptor
      exact Or.inl ⟨.i64, rfl⟩
    · rcases third with ⟨rfl, rfl, rfl⟩
      simp at declared
      subst descriptor
      exact Or.inr rfl

theorem mixedHelperWitness_success_world :
    ∃ after initialized types live regions,
      runModule 50 ⟨.release, mixedHelperWitness⟩ .initial = .ok () after ∧
      AcceptedWorld ⟨.release, mixedHelperWitness⟩ initialized after [] types live regions [] := by
  rcases mixedHelperWitness_world 50 with stopped | success
  · obtain ⟨reason, after, initialized, ambient, types, live, regions, stopped, world⟩ := stopped
    have result := mixedHelperWitness_returns
    simp only [mixedHelperWitnessReturns, stopped] at result
    cases result
  · exact success

#print axioms mixedHelperWitness_world
#print axioms mixedHelperWitness_success_world
end Goose.Proofs.ConstructionAcceptedExecution
