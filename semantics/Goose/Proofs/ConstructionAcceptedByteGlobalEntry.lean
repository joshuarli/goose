import Goose.Proofs.ConstructionByteGlobalEntryComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedByteGlobalsReturnedEntry (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (final : ExecutionState)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (returned : runModule (fuel + 3) config .initial = .ok () final) :
    ∃ (initialized : ExecutionState) (frame : ConstructionSourceFrame) (activation : RuntimeActivation)
      (live : Goose.Core.RootInst → Prop),
      let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := entryStatementsFrame config frame activated.nextScope
      initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial = .ok () initialized ∧
      runModule (fuel + 3) config .initial =
        (invokeCall (fuel + 3) config environment config.module.entry [] [] 0 >>= fun carriers => publishCarriers 0 carriers) initialized ∧
      invokeCall (fuel + 3) config environment config.module.entry [] [] 0 initialized =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      frame.interpretation.environment = activation ∧
      AcceptedWorld config next.initialized after [.callChannels activation []] (declaredRootTypes config.module) live [] [] ∧
      AcceptedFrame config accepted next after (declaredRootTypes config.module) ∧
      SourcePosition accepted next (.statements frame.source.impl.body.stmts) ∧
      frame.phase = .implementation config.module.entry ∧ frame.source.impl.results = #[] := by
  cases initialized : initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial with
  | stop reason state | escape reason carriers state | jump reason kind state =>
    simp only [runModule, bind, initialized] at returned
    cases returned
  | ok result state =>
    cases result
    obtain ⟨frame, activation, live, moduleStep, call, environmentEq, finalWorld, finalSource, position, phase, results⟩ :=
      acceptedByteGlobalsEntry fuel config accepted state declarations initialized
    exact ⟨state, frame, activation, live, rfl, moduleStep, call, environmentEq, finalWorld, finalSource,
      position, phase, results⟩

#print axioms acceptedByteGlobalsReturnedEntry

end Goose.Proofs.ConstructionAcceptedExecution
