import Goose.Proofs.ConstructionByteModuleHelperTail
import Goose.Proofs.ConstructionUnitTailWitness

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem unitTailWitness_world (fuel : Nat) :
    (∃ stop after initialized ambient types live regions,
      runModule fuel ⟨.release, unitTailWitness⟩ .initial = .stop stop after ∧
      AcceptedWorld ⟨.release, unitTailWitness⟩ initialized after ambient types live regions []) ∨
    (∃ after initialized types live regions,
      runModule fuel ⟨.release, unitTailWitness⟩ .initial = .ok () after ∧
      AcceptedWorld ⟨.release, unitTailWitness⟩ initialized after [] types live regions []) := by
  let config : EvalConfig := ⟨.release, unitTailWitness⟩
  let entry : Context := ⟨0, "entry", [], [], []⟩
  let helperContext : Context := ⟨1, "helper", [], [], []⟩
  let entryImpl : Impl := ⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0] (some (.call 1 [] 0)), .unknown⟩
  let helper : Impl := ⟨"helper", #[], #[], #[], .mk 0 [] none, .unknown⟩
  let declaration : ByteOwnerDeclaration := ⟨0, [65], 0, 0⟩
  apply acceptedByteModule_emptyHelperTail fuel config (acceptedModule config unitTailWitness_validation)
    [declaration] entry entryImpl 1 0 helperContext helper
  · intro id bound
    simp [config, unitTailWitness] at bound
  · rfl
  · rfl
  · rfl
  · rfl
  · intro item member
    simp only [List.mem_singleton] at member
    subst item
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

theorem unitTailWitness_success_world :
    ∃ after initialized types live regions,
      runModule 30 ⟨.release, unitTailWitness⟩ .initial = .ok () after ∧
      AcceptedWorld ⟨.release, unitTailWitness⟩ initialized after [] types live regions [] := by
  rcases unitTailWitness_world 30 with stopped | success
  · obtain ⟨reason, after, initialized, ambient, types, live, regions, stopped, world⟩ := stopped
    have result := unitTailWitness_returns
    simp only [unitTailWitnessReturns, stopped] at result
    cases result
  · exact success

#print axioms unitTailWitness_world
#print axioms unitTailWitness_success_world
end Goose.Proofs.ConstructionAcceptedExecution
