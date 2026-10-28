import Goose.Proofs.ConstructionByteGlobalZeroComplete

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem initGlobals_byteOwners_initial_complete (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin) :
    ∃ completed live regions,
      let outcome := initGlobals fuel config (List.range config.module.globals.size) .initial
      let after := Goose.Proofs.Exit.stepState outcome
      completed ≤ config.module.globals.size ∧
      AcceptedWorld config completed after [] (declaredRootTypes config.module) live regions [] ∧
      (match outcome with
       | .ok _ _ => completed = config.module.globals.size ∧ regions = [] ∧ FutureGlobalsClear config completed after
       | .stop stop _ => completed < config.module.globals.size ∧ runModule fuel config .initial = .stop stop after
       | .escape .. | .jump .. => False) := by
  have checked : ∀ id, 0 ≤ id → id < 0 + config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin := by
    intro id lower upper
    exact declarations id (by simpa using upper)
  obtain ⟨completed, live, regions, lower, upper, finalWorld, final⟩ :=
    initGlobals_byteOwners_complete fuel 0 config.module.globals.size config .initial [] (declaredRootTypes config.module)
      (fun _ => False) (by simp) checked (initial_acceptedWorld config accepted.accepted) (futureGlobalsClear_initial config)
  simp only [Nat.zero_add, ← List.range_eq_range'] at upper finalWorld final
  refine ⟨completed, live, regions, upper, finalWorld, ?_⟩
  cases outcome : initGlobals fuel config (List.range config.module.globals.size) .initial with
  | ok value after =>
    cases value
    simp only [outcome] at final ⊢
    exact final
  | stop stop after =>
    simp only [outcome] at final ⊢
    refine ⟨final, ?_⟩
    simp only [runModule, bind, outcome, Goose.Proofs.Exit.stepState]
  | escape target carriers after | jump target kind after =>
    simp only [outcome] at final

#print axioms initGlobals_byteOwners_initial_complete

end Goose.Proofs.ConstructionAcceptedExecution
