import Goose.Proofs.ConstructionAcceptedDestinationAncestry

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (DestinationId)
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionOwnership

private theorem newDestination_sourceState (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (before after : ExecutionState) (id : Nat)
    (valid : OwnershipSourceState before.construction)
    (executed : newDestination layout owner ty request origin none knownCount before = .ok id after) :
    OwnershipSourceState after.construction := by
  let prepared : ExecutionState := { before with construction :=
    { before.construction with storage := before.construction.storage.push ⟨ByteArray.empty, 0⟩ } }
  have preparedValid : OwnershipSourceState prepared.construction := by
    have preserved := constructionPrimitive_sourceState_of_sourceExtension (reserveStorage ByteArray.empty 0)
      (.reserveStorage ByteArray.empty 0) before.construction valid
      (reserveStorage_ownership_source ByteArray.empty 0 before.construction)
    simpa only [reserveStorage, ConstructionM.get, ConstructionM.set, bind, pure, ConstructionResult.finalState] using preserved
  have query := stateQuery_receivingLayout layout ty prepared
  simp only [newDestination, liftConstruction, reserveStorage, ConstructionM.get, ConstructionM.set, bind, pure] at executed
  change ((receivingLayout layout ty >>= fun selected => liftConstruction origin
    (openDestination before.construction.storage.size
      ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount)) prepared) = .ok id after at executed
  cases result : receivingLayout layout ty prepared with
  | stop reason middle | escape target carriers middle | jump target kind middle =>
    simp only [bind, result] at executed
    cases executed
  | ok selected middle =>
    simp only [result, Goose.Proofs.Exit.stepState] at query
    subst middle
    simp only [bind, result, liftConstruction] at executed
    cases opened : openDestination before.construction.storage.size
        ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount prepared.construction with
    | fault reason final => simp only [opened] at executed; cases executed
    | ok value final =>
      simp only [opened] at executed
      cases executed
      have source := openDestination_ownership_source before.construction.storage.size
        ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ selected knownCount prepared.construction preparedValid.structural.1.1.1
      have preserved := constructionPrimitive_sourceState_of_sourceExtension _ (.openDestination _ _ _ _)
        prepared.construction preparedValid source
      simpa only [opened, ConstructionResult.finalState] using preserved

private theorem FreshDestinationFrame.source {before after : ExecutionState} (frame : FreshDestinationFrame before after) :
    OwnershipSourceExtension before.construction after.construction := by
  intro id row present
  refine ⟨row, (frame.lookup id (Array.getElem?_eq_some_iff.mp present).1).trans present, rfl, ?_⟩
  cases use : row.use <;> simp only [OwnershipLinkBacking, use] <;> trivial

private theorem FreshDestinationFrame.inactive_supported_old {before after : ExecutionState}
    (frame : FreshDestinationFrame before after) (ordered : DestinationOwnersOrdered after.construction)
    (id : Nat) (row : PendingDestination) (present : after.construction.destinations[id]? = some row)
    (inactive : activeProgress row.progress = false) (supported : ReplacementSupported after.construction id) :
    id < before.construction.destinations.size := by
  cases supported with
  | active id actual found live =>
    have same : actual = row := Option.some.inj (found.symm.trans present)
    subst actual
    exact False.elim (Bool.noConfusion (live.symm.trans inactive))
  | parent child parent actual found use supported =>
    have earlier : id < child := by simpa only [use] using ordered child actual found
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    rw [frame.destinations, Array.size_push] at inside
    exact Nat.lt_of_lt_of_le earlier (Nat.le_of_lt_succ inside)

private theorem FreshDestinationFrame.anchors {before after : ExecutionState}
    (frame : FreshDestinationFrame before after) (beforeOrdered : DestinationOwnersOrdered before.construction)
    (afterOrdered : DestinationOwnersOrdered after.construction)
    (carriers : List Carrier) (valid : RetainedReplacementAnchors before.construction carriers) :
    RetainedReplacementAnchors after.construction carriers := by
  intro id row present inactive supported
  have inside := frame.inactive_supported_old afterOrdered id row present inactive supported
  have original : before.construction.destinations[id]? = some row := (frame.lookup id inside).symm.trans present
  have pushSupport := replacementSupported_congr_destinations after.construction
    { before.construction with destinations := before.construction.destinations.push frame.row }
    frame.destinations.symm id supported
  have oldSupport := replacementSupported_push_back before.construction frame.row
    (by intro parent use; rw [frame.receiver] at use; cases use) id inside pushSupport
  obtain ⟨retained, kept, descendant⟩ := valid id row original inactive oldSupport
  exact ⟨retained, kept, by rw [frame.ancestry beforeOrdered id retained inside]; exact descendant⟩

private theorem FreshDestinationFrame.boundaries {before after : ExecutionState}
    (frame : FreshDestinationFrame before after) (valid : OwnershipSourceState before.construction)
    (ambient : OwnershipAmbient) (boundaries : OwnershipAmbientBoundaries before.construction ambient) :
    OwnershipAmbientBoundaries after.construction ambient := by
  induction ambient with
  | nil => trivial
  | cons head outer ih =>
    refine ⟨?_, ih boundaries.2⟩
    intro token incoming reserved selected snapshot member ticket resolved retained kept
    have oldTicket : before.construction.exitReservations[token]? = some (.active .fresh incoming reserved snapshot) := by
      simpa only [frame.tickets] using ticket
    have reservedInside := (valid.structural.1.1.2.active token .fresh incoming reserved snapshot oldTicket).2.1
    obtain ⟨current, oldResolved, _, currentInside, _⟩ :=
      destinationCurrent_total before.construction valid.structural.2.1 reserved reservedInside
    have nextResolved := destinationCurrent_extension before.construction after.construction frame.successors frame.size reserved current oldResolved
    have same : current = selected := Except.ok.inj (nextResolved.symm.trans resolved)
    subst selected
    rw [frame.ancestry valid.structural.1.1.1.2.2.2 current retained currentInside]
    exact boundaries.1 token incoming reserved current snapshot member oldTicket oldResolved retained kept

theorem FreshDestinationFrame.ownershipContext {before after : ExecutionState}
    (frame : FreshDestinationFrame before after) (ambient : OwnershipAmbient)
    (valid : OwnershipExecutionContext before ambient) (source : OwnershipSourceState after.construction) :
    OwnershipExecutionContext after ambient := by
  have captures := ownershipCapturedReceivingFrames_sourceExtension before.construction after.construction ambient
    valid.source.structural.1.1 valid.source.structural.2.1 source.structural.1.1.1.2.2.2 frame.source
    frame.successors frame.size frame.tickets valid.bounds valid.receiving
  refine ⟨source, ⟨source.structural.1,
    frame.anchors valid.source.structural.1.1.1.2.2.2 source.structural.1.1.1.2.2.2 ambient.retained valid.retention.anchors,
    frame.boundaries valid.source ambient valid.retention.boundaries⟩, ?_, ?_, captures.2, captures.1, ?_⟩
  · rw [frame.outer]
    exact ⟨valid.runtime.activations, valid.runtime.breaks⟩
  · intro token reservation present needs
    rw [frame.tickets] at present
    exact valid.reservations token reservation present needs
  · rw [frame.outer]
    exact ⟨valid.identities.activations, valid.identities.breaks⟩

theorem newDestination_ownershipContext (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (knownCount : Option Nat) (before after : ExecutionState) (id : Nat) (ambient : OwnershipAmbient)
    (valid : OwnershipExecutionContext before ambient)
    (executed : newDestination layout owner ty request origin none knownCount before = .ok id after) :
    OwnershipExecutionContext after ambient := by
  obtain ⟨frame⟩ := newDestination_fresh_frame layout owner ty request origin knownCount before after id valid.source.structural.1.1.1 executed
  have source := newDestination_sourceState layout owner ty request origin knownCount before after id valid.source executed
  exact frame.ownershipContext ambient valid source

#print axioms FreshDestinationFrame.ownershipContext
#print axioms newDestination_ownershipContext

end Goose.Proofs.ConstructionAcceptedExecution
