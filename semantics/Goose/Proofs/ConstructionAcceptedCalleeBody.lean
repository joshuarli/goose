import Goose.Proofs.ConstructionAcceptedEntryCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedCalleeBodyScope (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation context)
    (parameters : frame.source.impl.params = #[]) (scopes : frame.interpretation.environment.scopes = [])
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) :
    let activation := frame.interpretation.environment
    let next := entryStatementsFrame config frame state.nextScope
    let after := ownershipResultScopeState activation frame.source.impl.body.scope state
    AcceptedWorld config next.initialized after ambient types live regions pending ∧
      AcceptedFrame config accepted next after types ∧
      SourcePosition accepted next (.statements frame.source.impl.body.stmts) := by
  obtain ⟨fresh, scopeWorld, scopeSource, position⟩ := acceptedCalleeStatementsFrame config accepted frame context state
    ambient types live regions pending world source phase parameters scopes cursor
  have scopeVisible : (entryStatementsFrame config frame state.nextScope).typing.visible = [] := by
    simp [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parameters]
  have actualSource := scopeSource.emptyVisible_activations scopeVisible
    (({ state with nextScope := state.nextScope + 1 }).activations.map (fun (current : RuntimeActivation) =>
      if current.act == frame.interpretation.environment.act then
        { current with scopes := (frame.source.impl.body.scope, state.nextScope) :: frame.interpretation.environment.scopes }
      else current))
  have actualWorld := acceptedWorld_resultScope config frame.initialized state ambient types live regions pending
    frame.interpretation.environment frame.source.impl.body.scope world
  exact ⟨actualWorld, actualSource, position⟩

#print axioms acceptedCalleeBodyScope
end Goose.Proofs.ConstructionAcceptedExecution
