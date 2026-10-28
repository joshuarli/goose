import Goose.Proofs.ConstructionAcceptedByteGlobalOutcome

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedByteGlobals_runPrefix (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin) :
    (∃ initialized live,
      initGlobals (fuel + 1) config (List.range config.module.globals.size) .initial = .ok () initialized ∧
      AcceptedWorld config config.module.globals.size initialized [] (declaredRootTypes config.module) live [] []) ∨
    (∃ completed middle live, completed < config.module.globals.size ∧
      AcceptedWorld config completed middle [] (declaredRootTypes config.module) live [] [] ∧
      FutureGlobalsClear config completed middle ∧
      initGlobals (fuel + 1) config [completed] middle = runModule (fuel + 1) config .initial) := by
  let globals := List.range config.module.globals.size
  cases initialized : initGlobals (fuel + 1) config globals .initial with
  | ok value state =>
    cases value
    left
    obtain ⟨live, world, clear⟩ := initGlobals_byteOwners_initial fuel config accepted state declarations initialized
    exact ⟨state, live, rfl, world⟩
  | stop reason state | escape reason carriers state | jump reason kind state =>
    right
    have checked : ∀ id, 0 ≤ id → id < 0 + config.module.globals.size →
        ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
          descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin := by
      intro id lower upper
      exact declarations id (by simpa using upper)
    have actual := initialized
    simp only [globals, List.range_eq_range'] at actual
    have traced := initGlobals_byteOwners_prefix config.module.globals.size fuel 0 config .initial _ []
      (declaredRootTypes config.module) (fun _ => False) [] (by simp) checked
      (initial_acceptedWorld config accepted.accepted) (futureGlobalsClear_initial config)
      (by simpa only [List.append_nil] using actual)
    obtain ⟨completed, middle, live, bound, world, clear, outcome⟩ := traced
    rcases outcome with ⟨done, impossible⟩ | ⟨notDone, stopped⟩
    · simp only [initGlobals, pure] at impossible
      cases impossible
    · refine ⟨completed, middle, live, notDone, ?_, ?_, ?_⟩
      · simpa only [Nat.zero_add] using world
      · simpa only [Nat.zero_add] using clear
      · simp only [globals] at initialized
        simp only [runModule, bind, initialized]
        simpa only [Nat.zero_add] using stopped

#print axioms acceptedByteGlobals_runPrefix

end Goose.Proofs.ConstructionAcceptedExecution
