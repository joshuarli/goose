import Goose.Proofs.ConstructionAcceptedEntryScope

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedZeroGlobalEntryStatements (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (noGlobals : config.module.globals.size = 0) :
    ∃ frame : ConstructionSourceFrame,
      let initial := ExecutionState.initial
      let activated := { initial with nextAct := initial.nextAct + 1 }
      let after := { activated with nextScope := activated.nextScope + 1 }
      let next := entryStatementsFrame config frame activated.nextScope
      initGlobals fuel config (List.range config.module.globals.size) initial = .ok () initial ∧
      freshAct initial = .ok frame.interpretation.environment.act activated ∧
      freshScope activated = .ok activated.nextScope after ∧
      AcceptedWorld config next.initialized after [] (declaredRootTypes config.module) (fun _ => False) [] [] ∧
      AcceptedFrame config accepted next after (declaredRootTypes config.module) ∧
      SourcePosition accepted next (.statements frame.source.impl.body.stmts) ∧
      frame.phase = .implementation config.module.entry ∧ frame.source.impl.results = #[] := by
  have world : AcceptedWorld config config.module.globals.size .initial [] (declaredRootTypes config.module)
      (fun _ => False) [] [] := by
    simpa only [noGlobals] using initial_acceptedWorld config accepted.accepted
  obtain ⟨frame, act, scope, finalWorld, finalSource, position, phase, results⟩ :=
    acceptedEntryFreshStatements config accepted .initial [] (declaredRootTypes config.module) (fun _ => False) [] [] world
  refine ⟨frame, ?_, act, scope, finalWorld, finalSource, position, phase, results⟩
  simp only [noGlobals, List.range_zero, initGlobals, pure]

#print axioms acceptedZeroGlobalEntryStatements

end Goose.Proofs.ConstructionAcceptedExecution
