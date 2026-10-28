import Goose.Proofs.ConstructionExitByteCall
import Goose.Proofs.ConstructionExitByteFinishCaller

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionAcceptedExecution

theorem accepted_nested_byte_handler (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (outer inner : RuntimeActivation) (outerPre innerPre : List (Goose.Core.VarId × Value))
    (outerScope innerScope targetId incoming selected token count writeCount : Nat)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (outerRest innerRest : List Stmt)
    (outerTail innerTail : Option Expr) (contextId : Goose.Core.ContextId) (arguments : List Arg)
    (callChannels exitChannels : List Channel)
    (outerInitial outerBound callPrepared innerEntered innerBound after : ExecutionState)
    (outerImpl innerImpl calledImpl : Impl) (calledId : Goose.Core.ImplId)
    (reserved : ConstructionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (outerLookup : config.module.impls[outer.implementation]? = some outerImpl)
    (results : outerImpl.results.toList.map (·.ty) = [.varr (.int .u8)])
    (outerChannels : outer.channels = [.construct incoming])
    (outerBinding : bindAll outer.act outerInitial.nextScope outerPre { outerInitial with
      nextScope := outerInitial.nextScope + 1
      activations := outerInitial.activations.map (fun current => if current.act == outer.act then
        { current with scopes := (outerScope, outerInitial.nextScope) :: outer.scopes } else current) } = .ok () outerBound)
    (called : getImplementation config contextId outerBound = .ok (calledId, calledImpl) outerBound)
    (callSetup : channelsFor config.layout outer.act calledImpl.results.toList origin outerBound = .ok callChannels callPrepared)
    (callPrefix : CallActivationPrefix (fuel + 7) config
      { outer with scopes := (outerScope, outerInitial.nextScope) :: outer.scopes }
      contextId arguments callChannels origin callPrepared inner innerPre
      (.mk innerScope (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin :: innerRest) innerTail) innerEntered)
    (innerLookup : config.module.impls[inner.implementation]? = some innerImpl)
    (innerBinding : bindAll inner.act innerEntered.nextScope innerPre { innerEntered with
      nextScope := innerEntered.nextScope + 1
      activations := innerEntered.activations.map (fun current => if current.act == inner.act then
        { current with scopes := (innerScope, innerEntered.nextScope) :: inner.scopes } else current) } = .ok () innerBound)
    (selection : targetActivation config targetId innerBound = .ok outer innerBound)
    (distinct : outer.act ≠ inner.act)
    (receiver : OpenDestinationBacking config.layout innerBound incoming (.varr (.int .u8)) (count + 1))
    (receiverRole : receiver.destination.use = .receiver)
    (receiverAdaptation : receiver.destination.adaptation = none)
    (receiverPhysical : receiver.destination.capability.layout = .varr (.int .u8))
    (receiverCurrent : destinationCurrent innerBound.construction incoming = .ok incoming)
    (valid : ReservationLifecycleInvariant innerBound.construction)
    (reservation : reserveExitDestination incoming .newValue innerBound.construction = .ok (token, selected) reserved)
    (world : AcceptedWorld config initialized { innerBound with construction := reserved }
      (.exitChannels [token] exitChannels [.completed selected] :: ambient) types live regions pending)
    (ready : OpenDestinationBacking config.layout { innerBound with construction := reserved } selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (fits : writeCount + bytes.length < 2 ^ 32) (current : destinationCurrent reserved selected = .ok selected)
    (built : buildExpr (fuel + 1) config { inner with scopes := (innerScope, innerEntered.nextScope) :: inner.scopes }
      selected (.bytes (.varr (.int .u8)) bytes origin) { innerBound with construction := reserved } = .ok () after) :
    ∃ final, enterActivation (fuel + 13) config outer outerPre
      (.mk outerScope (.expr (.call contextId arguments origin) origin :: outerRest) outerTail) origin outerInitial =
      .ok [.completed selected] final ∧
      final.construction.stdout = after.construction.stdout ∧
      ∀ entry : Goose.Core.RootInst × Value,
        (Goose.Proofs.Exit.runtimeScopeRoots inner innerScope innerEntered.nextScope).contains entry.1 = false →
        (Goose.Proofs.Exit.runtimeScopeRoots outer outerScope outerInitial.nextScope).contains entry.1 = false →
        (entry ∈ final.objects ↔ entry ∈ after.objects) := by
  let innerEnv := { inner with scopes := (innerScope, innerEntered.nextScope) :: inner.scopes }
  let outerEnv := { outer with scopes := (outerScope, outerInitial.nextScope) :: outer.scopes }
  let cleaned := { after with construction := { after.construction with
    exitReservations := after.construction.exitReservations.set! token .released } }
  let innerUnwound := releaseScopeState inner innerScope innerEntered.nextScope cleaned
  let crossed := { innerUnwound with activations := innerUnwound.activations.filter (fun current => current.act != inner.act) }
  let outerUnwound := releaseScopeState outer outerScope outerInitial.nextScope crossed
  have callEscape := accepted_byte_return_crosses_call fuel config initialized outerEnv inner outer innerPre
    innerScope targetId incoming selected token count writeCount bytes origin innerRest innerTail contextId arguments callChannels
    callPrepared innerEntered innerBound after innerImpl receiver.destination reserved
    (.exitChannels [token] exitChannels [.completed selected] :: ambient) types live regions pending
    callPrefix innerLookup innerBinding selection distinct outerChannels receiver.present receiver.opened receiverCurrent
    valid reservation world ready packed request fits current built
  have bodyEscape : execActivationBody (fuel + 12) config outer outerPre
      (.mk outerScope (.expr (.call contextId arguments origin) origin :: outerRest) outerTail) outerInitial =
      .escape ⟨outer.act, .nonlocal targetId⟩ [.completed selected] outerUnwound := by
    unfold execActivationBody execResultScope
    have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
      funext state
      rfl
    rw [fresh]
    simp only [bind, EvalM.get, EvalM.set, withScope, outerBinding, execStmts, execStmt, evalValue,
      called, callSetup]
    dsimp only [outerEnv, innerUnwound, crossed, cleaned] at callEscape ⊢
    simp only [callEscape.1, releaseScope, bind, EvalM.get, EvalM.set]
    rfl
  obtain ⟨cleanedState, landed, cleanup, finished⟩ := reserved_byte_finish_channels_caller fuel config initialized
    innerBound.construction reserved incoming selected token count writeCount innerBound rfl receiver receiverRole
    receiverAdaptation receiverPhysical receiverCurrent reservation innerEnv { innerBound with construction := reserved } after rfl
    ambient exitChannels types live regions pending world ready packed request bytes fits current origin built
    innerScope innerEntered.nextScope inner outer outerScope outerInitial.nextScope inner.act outer.act
  have ticket : ({ innerBound with construction := reserved } : ExecutionState).construction.exitReservations[token]? =
      some (.active .fresh incoming selected receiver.destination) := by
    exact (reserve_open_receiver_snapshot innerBound.construction reserved incoming selected token count receiver.destination
      receiver.present receiver.opened receiverCurrent reservation).2
  have tickets := buildExpr_bytes_tickets fuel config innerEnv selected (.varr (.int .u8)) bytes origin
    { innerBound with construction := reserved } after ready.destination writeCount world.ownership.source current ready.present ready.opened built
  have afterTicket : after.construction.exitReservations[token]? = some (.active .fresh incoming selected receiver.destination) := by
    simpa only [tickets] using ticket
  have released := releaseExitReservation_active after.construction token .fresh incoming selected receiver.destination afterTicket
  have exactCleanup : exitChannelCleanupBorrowed origin [] [token] false [.completed selected] after = .ok () cleaned := by
    simp only [exitChannelCleanupBorrowed, Bool.false_eq_true, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.forIn_cons, List.forIn_nil, liftConstruction, released, bind, pure]
    rfl
  have same := cleanup.symm.trans exactCleanup
  cases same
  have matched : enterActivation (fuel + 13) config outer outerPre
      (.mk outerScope (.expr (.call contextId arguments origin) origin :: outerRest) outerTail) origin outerInitial =
      .ok [.completed selected] landed := by
    simp only [enterActivation, outerLookup, finishActivation, bodyEscape, beq_self_eq_true, ↓reduceIte, outerChannels, results]
    change finishChannels config.layout [.construct incoming] [.varr (.int .u8)] [.completed selected] origin
      { outerUnwound with activations := outerUnwound.activations.filter (fun current => current.act != outer.act) } = .ok () landed at finished
    rw [finished]
  have finishedActivation : finishActivation config.layout outer (outerImpl.results.toList.map (·.ty)) origin
      (execActivationBody (fuel + 12) config outer outerPre
        (.mk outerScope (.expr (.call contextId arguments origin) origin :: outerRest) outerTail)) outerInitial =
      .ok [.completed selected] landed := by
    simpa only [enterActivation, outerLookup] using matched
  have output := Goose.Proofs.Exit.runtime_activation_landing_frames_output config.layout outer (.nonlocal targetId)
    (outerImpl.results.toList.map (·.ty)) origin _ outerInitial outerUnwound [.completed selected] bodyEscape
  have objects := Goose.Proofs.Exit.runtime_activation_landing_frames_objects config.layout outer (.nonlocal targetId)
    (outerImpl.results.toList.map (·.ty)) origin _ outerInitial outerUnwound [.completed selected] bodyEscape
  rw [finishedActivation] at output objects
  simp only [Goose.Proofs.Exit.stepState] at output objects
  refine ⟨landed, matched, ?_, ?_⟩
  · exact output
  · intro entry innerOutside outerOutside
    rw [objects]
    change entry ∈ (releaseScopeState outer outerScope outerInitial.nextScope crossed).objects ↔ entry ∈ after.objects
    rw [Goose.Proofs.Exit.runtime_release_scope_outside outer outerScope outerInitial.nextScope crossed entry outerOutside]
    change entry ∈ (releaseScopeState inner innerScope innerEntered.nextScope cleaned).objects ↔ entry ∈ after.objects
    rw [Goose.Proofs.Exit.runtime_release_scope_outside inner innerScope innerEntered.nextScope cleaned entry innerOutside]

#print axioms accepted_nested_byte_handler

end Goose.Proofs.ExitExecution
