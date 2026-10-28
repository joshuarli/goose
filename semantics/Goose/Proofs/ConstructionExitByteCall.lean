import Goose.Proofs.ConstructionExitByteSetup
import Goose.Proofs.ExitExecutionPathDispatchUnwind
import Goose.Proofs.ExitExecutionUnwind

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionAcceptedExecution

theorem accepted_byte_return_crosses_call (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (caller inner target : RuntimeActivation) (innerPre : List (Goose.Core.VarId × Value))
    (scope targetId incoming selected token count writeCount : Nat) (bytes : List UInt8)
    (origin : Goose.Core.OriginId) (rest : List Stmt) (tail : Option Expr)
    (contextId : Goose.Core.ContextId) (arguments : List Arg) (callChannels : List Channel)
    (callInitial entered bound after : ExecutionState) (innerImpl : Impl)
    (row : PendingDestination) (reserved : ConstructionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame)
    (callPrefix : CallActivationPrefix (fuel + 7) config caller contextId arguments callChannels origin
      callInitial inner innerPre (.mk scope (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin :: rest) tail) entered)
    (lookup : config.module.impls[inner.implementation]? = some innerImpl)
    (binding : bindAll inner.act entered.nextScope innerPre { entered with
      nextScope := entered.nextScope + 1
      activations := entered.activations.map (fun current => if current.act == inner.act then
        { current with scopes := (scope, entered.nextScope) :: inner.scopes } else current) } = .ok () bound)
    (selection : targetActivation config targetId bound = .ok target bound)
    (distinct : target.act ≠ inner.act) (channels : target.channels = [.construct incoming])
    (present : bound.construction.destinations[incoming]? = some row)
    (opened : row.progress = .open (count + 1))
    (receiverCurrent : destinationCurrent bound.construction incoming = .ok incoming)
    (valid : ReservationLifecycleInvariant bound.construction)
    (reservation : reserveExitDestination incoming .newValue bound.construction = .ok (token, selected) reserved)
    (world : AcceptedWorld config initialized { bound with construction := reserved } ambient types live regions pending)
    (ready : OpenDestinationBacking config.layout { bound with construction := reserved } selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (fits : writeCount + bytes.length < 2 ^ 32) (current : destinationCurrent reserved selected = .ok selected)
    (built : buildExpr (fuel + 1) config { inner with scopes := (scope, entered.nextScope) :: inner.scopes }
      selected (.bytes (.varr (.int .u8)) bytes origin) { bound with construction := reserved } = .ok () after) :
    let cleaned := { after with construction := { after.construction with
      exitReservations := after.construction.exitReservations.set! token .released } }
    let unwound := releaseScopeState inner scope entered.nextScope cleaned
    let escapedState := { unwound with activations := unwound.activations.filter (fun current => current.act != inner.act) }
    invokeCall (fuel + 8) config caller contextId arguments callChannels origin callInitial =
      .escape ⟨target.act, .nonlocal targetId⟩ [.completed selected] escapedState ∧
    escapedState.construction.destinations[incoming]? = some { row with progress := .exiting (count + 1) selected } ∧
    escapedState.construction.storage = after.construction.storage := by
  let localEnv := { inner with scopes := (scope, entered.nextScope) :: inner.scopes }
  let cleaned := { after with construction := { after.construction with
    exitReservations := after.construction.exitReservations.set! token .released } }
  let unwound := releaseScopeState inner scope entered.nextScope cleaned
  have returned := accepted_open_byte_return fuel config initialized localEnv target targetId incoming selected token count writeCount
    bytes origin bound after row reserved ambient types live regions pending selection channels present opened receiverCurrent valid
    reservation world ready packed request fits current built
  have statements : execStmts (fuel + 5) config localEnv
      (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin :: rest) bound =
      .escape ⟨target.act, .nonlocal targetId⟩ [.completed selected] cleaned := by
    simp only [execStmts, bind, returned.1]
    rfl
  have bodyEscape : execActivationBody (fuel + 6) config inner innerPre
      (.mk scope (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin :: rest) tail) entered =
      .escape ⟨target.act, .nonlocal targetId⟩ [.completed selected] unwound := by
    unfold execActivationBody execResultScope
    have fresh : freshScope = fun state => .ok state.nextScope { state with nextScope := state.nextScope + 1 } := by
      funext state
      rfl
    rw [fresh]
    simp only [bind, EvalM.get, EvalM.set, withScope, binding]
    dsimp only [localEnv] at statements ⊢
    simp only [statements, releaseScope, bind, EvalM.get, EvalM.set]
    rfl
  have innerEscape : enterActivation (fuel + 7) config inner innerPre
      (.mk scope (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin :: rest) tail) origin entered =
      .escape ⟨target.act, .nonlocal targetId⟩ [.completed selected]
        { unwound with activations := unwound.activations.filter (fun current => current.act != inner.act) } := by
    simp only [enterActivation, lookup]
    exact Goose.Proofs.Exit.runtime_activation_propagates config.layout inner (innerImpl.results.toList.map (·.ty)) origin
      _ entered unwound ⟨target.act, .nonlocal targetId⟩ [.completed selected] bodyEscape distinct
  refine ⟨callPrefix.escape_call _ _ innerEscape, ?_, ?_⟩
  · exact returned.2.1
  · exact returned.2.2

theorem byte_call_unwind_outside (inner : RuntimeActivation) (scope : Nat) (scopeInst : Goose.Core.ScopeInst)
    (state : ExecutionState) (token : Nat) (entry : Goose.Core.RootInst × Value)
    (outside : (Goose.Proofs.Exit.runtimeScopeRoots inner scope scopeInst).contains entry.1 = false) :
    let cleaned := { state with construction := { state.construction with
      exitReservations := state.construction.exitReservations.set! token .released } }
    let unwound := releaseScopeState inner scope scopeInst cleaned
    let escapedState := { unwound with activations := unwound.activations.filter (fun current => current.act != inner.act) }
    escapedState.construction.stdout = state.construction.stdout ∧
      (entry ∈ escapedState.objects ↔ entry ∈ state.objects) := by
  refine ⟨rfl, ?_⟩
  exact Goose.Proofs.Exit.runtime_release_scope_outside inner scope scopeInst _ entry outside

#print axioms byte_call_unwind_outside
#print axioms accepted_byte_return_crosses_call

end Goose.Proofs.ExitExecution
