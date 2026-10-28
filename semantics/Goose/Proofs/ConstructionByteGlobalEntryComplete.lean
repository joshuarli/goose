import Goose.Proofs.ConstructionByteGlobalInitialComplete
import Goose.Proofs.ConstructionAcceptedEntryInvocation

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedByteGlobalsEntry (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (initialized : ExecutionState)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (globals : initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial = .ok () initialized) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (live : Goose.Core.RootInst → Prop),
      let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := entryStatementsFrame config frame activated.nextScope
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
  have globalRun : initGlobals ((fuel + 2) + 1) config (List.range config.module.globals.size) .initial = .ok () initialized := by
    simpa only [Nat.add_assoc] using globals
  obtain ⟨live, globalWorld, clear⟩ := initGlobals_byteOwners_initial (fuel + 2) config accepted initialized declarations globalRun
  have depth : initialized.activations.length < Goose.Core.maxCallDepth := by
    have runtime := globalWorld.ownership.runtime.activations
    cases active : initialized.activations with
    | nil => simp [Goose.Core.maxCallDepth]
    | cons head tail => simp [active, OwnershipAmbient.activations] at runtime
  obtain ⟨frame, activation, environmentEq, call, finalWorld, finalSource, position, phase, results⟩ :=
    acceptedEntryCallSetup fuel config accepted ⟨0, 0, #[], [], []⟩ initialized [] (declaredRootTypes config.module)
      live [] [] globalWorld depth
  obtain ⟨original, implementation, originalAt, implementationAt, parametersEmpty, resultsEmpty⟩ :=
    validated_entry config.module accepted.accepted
  have moduleStep : runModule (fuel + 3) config .initial =
      (invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>= fun carriers =>
        publishCarriers 0 carriers) initialized := by
    simp only [runModule, globals, bind, getImplementation, originalAt, implementationAt, resultsEmpty,
      Array.toList_empty, channelsFor, List.mapM_nil, pure]
  exact ⟨frame, activation, live, moduleStep, call, environmentEq, finalWorld, finalSource, position, phase, results⟩

#print axioms acceptedByteGlobalsEntry

end Goose.Proofs.ConstructionAcceptedExecution
