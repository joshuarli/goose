import Goose.Proofs.ConstructionExitByteCaptured
import Goose.Proofs.ConstructionExecutionProtocolOwnersAncestry

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem source_extension_same_uses (before after : ConstructionState)
    (size : after.destinations.size = before.destinations.size)
    (history : OwnershipSourceExtension before after) :
    before.destinations.map (·.use) = after.destinations.map (·.use) := by
  apply Array.ext
  · simp only [Array.size_map, size]
  · intro index left right
    simp only [Array.size_map] at left right
    let row := before.destinations[index]
    have found : before.destinations[index]? = some row := Array.getElem?_eq_getElem left
    obtain ⟨updated, actual, use, _⟩ := history index row found
    have afterRow := (Array.getElem?_eq_some_iff.mp actual).2
    simp only [Array.getElem_map]
    simpa only [← afterRow] using use.symm

theorem boundaries_indexing_frame (before after : ConstructionState) (ambient : OwnershipAmbient)
    (size : after.destinations.size = before.destinations.size)
    (successors : after.destinationSuccessors = before.destinationSuccessors)
    (tickets : after.exitReservations = before.exitReservations)
    (uses : before.destinations.map (·.use) = after.destinations.map (·.use))
    (valid : OwnershipAmbientBoundaries before ambient) : OwnershipAmbientBoundaries after ambient := by
  induction ambient with
  | nil => trivial
  | cons frame outer ih =>
    refine ⟨?_, ih valid.2⟩
    intro token incoming reserved selected snapshot member ticket current retained carrier
    have oldTicket : before.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) := by
      simpa only [tickets] using ticket
    have oldCurrent : destinationCurrent before reserved = .ok selected := by
      rw [destinationCurrent_result, size,
        destinationCurrentSteps_same_indexing _ before after size successors] at current
      simpa only [destinationCurrent_result] using current
    have old := valid.1 token incoming reserved selected snapshot member oldTicket oldCurrent retained carrier
    rw [← destinationDescendant_congr_uses before.destinations after.destinations uses selected retained]
    exact old

theorem build_packed_bytes_boundaries (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id count : Nat) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before after : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipSourceState before.construction) (boundaries : OwnershipAmbientBoundaries before.construction ambient)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    OwnershipAmbientBoundaries after.construction ambient := by
  have indexing := build_packed_bytes_indexing fuel config environment id count bytes origin before after valid ready packed request current executed
  have tickets := buildExpr_bytes_tickets fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count valid current ready.present ready.opened executed
  have history := (buildExpr_bytes_ownershipSource fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count valid.structural.1.1.1 current ready.present ready.opened executed).1
  exact boundaries_indexing_frame before.construction after.construction ambient indexing.1 indexing.2 tickets
    (source_extension_same_uses before.construction after.construction indexing.1 history) boundaries

#print axioms build_packed_bytes_boundaries
#print axioms boundaries_indexing_frame
#print axioms source_extension_same_uses

end Goose.Proofs.ConstructionAcceptedExecution
