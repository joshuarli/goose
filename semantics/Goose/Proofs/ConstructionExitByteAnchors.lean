import Goose.Proofs.ConstructionExitByteRetention
import Goose.Proofs.ConstructionExitByteFinishParent
import Goose.Proofs.ConstructionExitByteRuntime
import Goose.Proofs.ConstructionExitStructuralRelease

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

private theorem supported_preimage (before after : ConstructionState) (id : Nat)
    (rows : ∀ (id : Nat) (row : PendingDestination), after.destinations[id]? = some row →
      ∃ old, before.destinations[id]? = some old ∧ old.use = row.use ∧
        (activeProgress row.progress = true → activeProgress old.progress = true))
    (supported : ReplacementSupported after id) : ReplacementSupported before id := by
  induction supported with
  | active id row present live =>
    obtain ⟨old, found, _, active⟩ := rows id row present
    exact .active id old found (active live)
  | parent id parent row present use supported ih =>
    obtain ⟨old, found, sameUse, _⟩ := rows id row present
    exact .parent id parent old found (sameUse.trans use) ih

theorem build_packed_bytes_anchors (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id count : Nat) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before after : ExecutionState) (carriers : List Carrier)
    (valid : OwnershipSourceState before.construction) (anchors : RetainedReplacementAnchors before.construction carriers)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    RetainedReplacementAnchors after.construction carriers := by
  have indexing := build_packed_bytes_indexing fuel config environment id count bytes origin before after valid ready packed request current executed
  have history := (buildExpr_bytes_ownershipSource fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count valid.structural.1.1.1 current ready.present ready.opened executed).1
  have uses := source_extension_same_uses before.construction after.construction indexing.1 history
  obtain ⟨builtRow, builtPresent, _, builtPhase⟩ := build_packed_bytes_capability fuel config environment id count
    bytes origin before after valid ready packed request current executed
  have otherRow : ∀ other, other ≠ id → after.construction.destinations[other]? = before.construction.destinations[other]? := by
    intro other different
    exact build_packed_bytes_other_row fuel config environment id count other bytes origin before after valid ready packed request current different executed
  have rows : ∀ (index : Nat) (row : PendingDestination), after.construction.destinations[index]? = some row →
      ∃ old, before.construction.destinations[index]? = some old ∧ old.use = row.use ∧
        (activeProgress row.progress = true → activeProgress old.progress = true) := by
    intro index row found
    by_cases same : index = id
    · subst index
      have sameRow : row = builtRow := Option.some.inj (found.symm.trans builtPresent)
      subst row
      obtain ⟨updated, updatedPresent, sameUse, _⟩ := history id ready.destination ready.present
      have sameUpdated : updated = builtRow := Option.some.inj (updatedPresent.symm.trans builtPresent)
      subst updated
      exact ⟨ready.destination, ready.present, sameUse.symm, by intro _; simp only [ready.opened, activeProgress]⟩
    · have beforeFound : before.construction.destinations[index]? = some row := by
        simpa only [otherRow index same] using found
      exact ⟨row, beforeFound, rfl, fun h => h⟩
  intro index row found inactive supported
  have different : index ≠ id := by
    intro same
    subst index
    have sameRow : row = builtRow := Option.some.inj (found.symm.trans builtPresent)
    subst row
    simp only [builtPhase, activeProgress] at inactive
    cases inactive
  have beforeFound : before.construction.destinations[index]? = some row := by
    simpa only [otherRow index different] using found
  have prior := supported_preimage before.construction after.construction index rows supported
  obtain ⟨retained, member, descendant⟩ := anchors index row beforeFound inactive prior
  exact ⟨retained, member, by
    rw [← destinationDescendant_congr_uses before.construction.destinations after.construction.destinations uses index retained]
    exact descendant⟩

theorem build_packed_bytes_execution_context (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id count : Nat) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before after : ExecutionState) (ambient : OwnershipAmbient)
    (context : OwnershipExecutionContext before ambient)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    OwnershipExecutionContext after ambient := by
  have source := buildExpr_bytes_sourceState fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count context.source current ready.present ready.opened executed
  have anchors := build_packed_bytes_anchors fuel config environment id count bytes origin before after ambient.retained
    context.source context.retention.anchors ready packed request current executed
  have boundaries := build_packed_bytes_boundaries fuel config environment id count bytes origin before after ambient
    context.source context.retention.boundaries ready packed request current executed
  have captured := build_packed_bytes_captured_receiving fuel config environment id count bytes origin before after ambient
    context.source context.bounds context.receiving ready packed request current executed
  have tickets := buildExpr_bytes_tickets fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count context.source current ready.present ready.opened executed
  have sameRuntime := buildExpr_bytes_runtime fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count context.source current ready.present ready.opened executed
  refine ⟨source, ⟨source.structural.1, anchors, boundaries⟩, ?_, ?_, captured.2, captured.1, ?_⟩
  · rw [sameRuntime]
    exact ⟨context.runtime.activations, context.runtime.breaks⟩
  · simpa only [OwnershipReservationFrames, tickets] using context.reservations
  · rw [sameRuntime]
    exact ⟨context.identities.activations, context.identities.breaks⟩

theorem build_packed_bytes_cleanup_context (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id count token incoming : Nat) (snapshot : PendingDestination)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (channels : List Channel) (carriers : List Carrier) (outer : OwnershipAmbient)
    (context : OwnershipExecutionContext before (.exitChannels [token] channels carriers :: outer))
    (ticket : before.construction.exitReservations[token]? = some (.active .fresh incoming id snapshot))
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after)
    (scope : Nat) (scopeInst : Goose.Core.ScopeInst) :
    ∃ cleaned, Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed origin [] [token] false carriers after = .ok () cleaned ∧
      OwnershipExecutionContext (releaseScopeState environment scope scopeInst cleaned) (.returned carriers :: outer) := by
  have afterContext := build_packed_bytes_execution_context fuel config environment id count bytes origin before after
    (.exitChannels [token] channels carriers :: outer) context ready packed request current executed
  have tickets := buildExpr_bytes_tickets fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count context.source current ready.present ready.opened executed
  have afterTicket : after.construction.exitReservations[token]? = some (.active .fresh incoming id snapshot) := by
    simpa only [tickets] using ticket
  exact cleanup_exit_execution_context after token incoming id snapshot channels carriers outer origin environment scope scopeInst afterTicket afterContext

#print axioms build_packed_bytes_cleanup_context
#print axioms build_packed_bytes_execution_context
#print axioms build_packed_bytes_anchors

end Goose.Proofs.ConstructionAcceptedExecution
