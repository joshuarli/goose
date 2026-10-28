import Goose.Proofs.ConstructionByteModuleByteHelperTail
import Goose.Proofs.ConstructionByteHelperTailWitness

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem byteHelperTailWitness_world (fuel : Nat) :
    (∃ stop after initialized ambient types live regions,
      runModule fuel ⟨.release, byteHelperTailWitness⟩ .initial = .stop stop after ∧
      AcceptedWorld ⟨.release, byteHelperTailWitness⟩ initialized after ambient types live regions []) ∨
    (∃ after initialized types live regions,
      runModule fuel ⟨.release, byteHelperTailWitness⟩ .initial = .ok () after ∧
      AcceptedWorld ⟨.release, byteHelperTailWitness⟩ initialized after [] types live regions []) := by
  let config : EvalConfig := ⟨.release, byteHelperTailWitness⟩
  let entry : Context := ⟨0, "entry", [], [], []⟩
  let helperContext : Context := ⟨1, "helper", [], [], []⟩
  let entryImpl : Impl := ⟨"entry", #[], #[], #[⟨"bytes", .varr (.int .u8), .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [65] 0) 0] (some (.call 1 [] 0)), .unknown⟩
  let helper : Impl := ⟨"helper", #[], #[], #[⟨"local", .varr (.int .u8), .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.bytes (.varr (.int .u8)) [66, 67] 0) 0] none, .unknown⟩
  let helperDeclaration : ByteOwnerDeclaration := ⟨0, [66, 67], 0, 0⟩
  let declaration : ByteOwnerDeclaration := ⟨0, [65], 0, 0⟩
  apply acceptedByteModule_byteHelperTail fuel config (acceptedModule config byteHelperTailWitness_validation)
    [declaration] entry entryImpl 1 0 helperContext helper [helperDeclaration]
  · intro id bound
    simp [config, byteHelperTailWitness] at bound
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
  · intro item member
    simp only [List.mem_singleton] at member
    subst item
    rfl
  · decide
  · decide

theorem byteHelperTailWitness_success_world :
    ∃ after initialized types live regions,
      runModule 30 ⟨.release, byteHelperTailWitness⟩ .initial = .ok () after ∧
      AcceptedWorld ⟨.release, byteHelperTailWitness⟩ initialized after [] types live regions [] := by
  rcases byteHelperTailWitness_world 30 with stopped | success
  · obtain ⟨reason, after, initialized, ambient, types, live, regions, stopped, world⟩ := stopped
    have result := byteHelperTailWitness_returns
    simp only [byteHelperTailWitnessReturns, stopped] at result
    cases result
  · exact success

#print axioms byteHelperTailWitness_world
#print axioms byteHelperTailWitness_success_world
end Goose.Proofs.ConstructionAcceptedExecution
