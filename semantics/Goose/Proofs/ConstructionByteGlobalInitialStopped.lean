import Goose.Proofs.ConstructionByteGlobalStopped

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem initGlobals_byteOwners_initial_stopped_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (after : ExecutionState) (stop : Goose.Core.Stop)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (executed : initGlobals (fuel + 1) config (List.range config.module.globals.size) .initial = .stop stop after) :
    ∃ completed live regions, completed < config.module.globals.size ∧
      AcceptedWorld config completed after [] (declaredRootTypes config.module) live regions [] := by
  have checked : ∀ id, 0 ≤ id → id < 0 + config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin := by
    intro id lower upper
    exact declarations id (by simpa using upper)
  have run : initGlobals (fuel + 1) config (List.range' 0 config.module.globals.size) .initial = .stop stop after := by
    simpa only [List.range_eq_range'] using executed
  obtain ⟨completed, live, regions, lower, upper, world⟩ :=
    initGlobals_byteOwners_stopped_world config.module.globals.size fuel 0 config .initial after stop []
      (declaredRootTypes config.module) (fun _ => False) (initial_acceptedWorld config accepted.accepted)
      (futureGlobalsClear_initial config) checked run
  exact ⟨completed, live, regions, by simpa using upper, world⟩

#print axioms initGlobals_byteOwners_initial_stopped_world

end Goose.Proofs.ConstructionAcceptedExecution
