import Goose.Proofs.ConstructionRootCorrespondenceAcceptedEntry
import Goose.Proofs.ConstructionAcceptedState

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership (OwnershipAmbient)

theorem acceptedEntryWorldFrame (config : EvalConfig) (accepted : AcceptedModule config) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config config.module.globals.size { state with nextAct := state.nextAct + 1 }
      ambient types liveRoots regions pending) :
    ∃ frame : ConstructionSourceFrame,
      AcceptedWorld config frame.initialized { state with nextAct := state.nextAct + 1 }
        ambient types liveRoots regions pending ∧
      AcceptedFrame config accepted frame { state with nextAct := state.nextAct + 1 } types ∧
      frame.phase = .implementation config.module.entry ∧ frame.typing.visible = [] ∧
      frame.typingFuel = 4096 ∧ frame.typingCounter = 0 ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      frame.initialized = config.module.globals.size ∧
      frame.source.impl.params = #[] ∧ frame.source.impl.results = #[] ∧
      frame.source.scopes = [] ∧ frame.interpretation.environment.scopes = [] ∧
      frame.interpretation.environment.channels = [] ∧
      freshAct state = .ok frame.interpretation.environment.act { state with nextAct := state.nextAct + 1 } ∧
      ∃ bodyTypes declared, typeBlock frame.typingFuel frame.typing frame.source.impl.body frame.typingCounter =
        .ok (bodyTypes, declared) := by
  obtain ⟨frame, phase, visible, fuel, counter, cursor, initialized, parametersEmpty, resultsEmpty,
      sourceScopes, scopes, channels, allocated, compatible, aliases, frontier, direct, contents,
      bodyTypes, declared, typed⟩ := acceptedEntryFrame config accepted state
  have framed : AcceptedFrame config accepted frame { state with nextAct := state.nextAct + 1 } types := {
    compatible := compatible
    frontier := frontier
    aliases := aliases
    locals := by
      intro id member
      rw [visible] at member
      cases member
    localTypes := by
      intro id member
      rw [visible] at member
      cases member
    uninitializedLocals := by
      intro id _ root resolved
      have actual := rootOf_instantiates frame.interpretation id _ root resolved
      cases actual with
      | «local» id descriptor scope declared active =>
        rw [scopes] at active
        cases active
    futureGlobals := by
      intro id future bound
      rw [initialized] at future
      exact (Nat.not_lt_of_ge future bound).elim
    direct := direct
    contents := contents }
  have frameWorld : AcceptedWorld config frame.initialized { state with nextAct := state.nextAct + 1 }
      ambient types liveRoots regions pending := initialized.symm ▸ world
  exact ⟨frame, frameWorld, framed, phase, visible, fuel, counter, cursor, initialized, parametersEmpty, resultsEmpty,
    sourceScopes, scopes, channels, allocated, bodyTypes, declared, typed⟩

end Goose.Proofs.ConstructionAcceptedExecution
