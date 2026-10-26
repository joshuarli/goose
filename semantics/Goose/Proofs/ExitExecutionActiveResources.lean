import Goose.Proofs.ExitExecutionLiveCarriers
import Goose.Proofs.OwnershipAmbientContinuations

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Core (OriginId)
open Goose.Proofs.ConstructionExecutionOwnership

inductive ExitScopeTarget
  | ordinary
  | nonlocal (target : Nat)
  | block (target : BreakTarget)

def ExitScopeTarget.Selected (target : ExitScopeTarget) (config : EvalConfig)
    (source : RuntimeActivation) (entered : ExecutionState) (activation : RuntimeActivation) : Prop :=
  match target with
  | .ordinary => enclosingActivation source entered = .ok activation entered
  | .nonlocal id => targetActivation config id entered = .ok activation entered
  | .block target => currentBreak source.act (some .block) entered = .ok target entered ∧
      activation = { source with channels := target.channels }

structure ActiveExitScope (config : EvalConfig) (source : RuntimeActivation) (entered : ExecutionState) where
  activation : RuntimeActivation
  target : ExitScopeTarget
  selected : target.Selected config source entered activation
  operands : List Expr
  origin : OriginId
  prepared : ExecutionState
  channels : List Channel
  setup : exitChannels source activation operands origin entered = .ok channels prepared

def ActiveExitScope.ownNewTokens {config : EvalConfig} {source : RuntimeActivation} {entered : ExecutionState}
    (scope : ActiveExitScope config source entered) : List ExitReservationId :=
  newOwnershipExitTokens entered.construction.exitReservations.size scope.prepared

def ActiveExitScope.borrowed {config : EvalConfig} {source : RuntimeActivation} {entered : ExecutionState}
    (scope : ActiveExitScope config source entered) : List BorrowedWaitingExitReservation :=
  borrowedOwnershipExitReceipts scope.activation entered

def survivingPendingNamed (result : OwnershipChannelResult) : List ExitReservationId :=
  result.carriers.filterMap fun carrier => match carrier with
    | .pendingNamed token => some token
    | .register _ | .completed _ => none

structure ActiveExitResources {config : EvalConfig} {source : RuntimeActivation} {entered : ExecutionState}
    (scope : ActiveExitScope config source entered) (state : ExecutionState) (result : OwnershipChannelResult) : Prop where
  backing : ∀ carrier ∈ result.carriers, CarrierResultBacking config.layout state carrier
  surviving : ∀ token ∈ survivingPendingNamed result, token ∉ scope.ownNewTokens

theorem ActiveExitScope.borrowed_source {config : EvalConfig} {source : RuntimeActivation} {entered : ExecutionState}
    (scope : ActiveExitScope config source entered) (receipt : BorrowedWaitingExitReservation)
    (member : receipt ∈ scope.borrowed) :
    Channel.completion receipt.token ∈ scope.activation.channels ∧
      entered.construction.exitReservations[receipt.token]? = some (.waiting receipt.incoming) :=
  borrowedOwnershipExitReceipts_source scope.activation entered receipt member

theorem ActiveExitScope.borrowed_not_owned {config : EvalConfig} {source : RuntimeActivation} {entered : ExecutionState}
    (scope : ActiveExitScope config source entered) (receipt : BorrowedWaitingExitReservation)
    (member : receipt ∈ scope.borrowed) : receipt.token ∉ scope.ownNewTokens := by
  have inside := borrowedOwnershipExitReceipts_bounded scope.activation entered receipt member
  intro owned
  have lower := (newOwnershipExitTokens_mem entered.construction.exitReservations.size scope.prepared receipt.token).mp owned
  exact (Nat.not_le_of_lt inside) lower.1

theorem survivingPendingNamed_member (result : OwnershipChannelResult) (token : ExitReservationId) :
    token ∈ survivingPendingNamed result ↔ Carrier.pendingNamed token ∈ result.carriers := by
  simp only [survivingPendingNamed, List.mem_filterMap]
  constructor
  · rintro ⟨carrier, member, selected⟩
    cases carrier <;> simp only [reduceCtorEq, Option.some.injEq] at selected
    subst token
    exact member
  · intro member
    exact ⟨.pendingNamed token, member, rfl⟩

theorem borrowed_pending_cleanup (origin : OriginId) (receipt : BorrowedWaitingExitReservation)
    (result : OwnershipChannelResult) (state : ExecutionState)
    (carried : receipt.token ∈ survivingPendingNamed result) :
    ownershipBorrowedReceiptCleanup origin receipt result.carriers state = .ok () state := by
  have member := (survivingPendingNamed_member result receipt.token).mp carried
  simp only [ownershipBorrowedReceiptCleanup]
  split
  · rfl
  · rename_i absent
    exact False.elim (absent (List.any_eq_true.mpr ⟨.pendingNamed receipt.token, member, by simp⟩))

private theorem mapM_output_property {α β : Type} (items : List α) (action : α → EvalM β)
    (property : β → Prop)
    (one : ∀ item before value after, action item before = .ok value after → property value)
    (before after : ExecutionState) (values : List β) (executed : items.mapM action before = .ok values after) :
    ∀ value ∈ values, property value := by
  induction items generalizing before after values with
  | nil =>
    simp only [List.mapM_nil, pure] at executed
    cases executed
    simp
  | cons first rest ih =>
    simp only [List.mapM_cons, bind] at executed
    cases head : action first before with
    | stop reason middle | escape address carriers middle | jump target kind middle =>
      simp only [head] at executed
      cases executed
    | ok value middle =>
      simp only [head] at executed
      cases tail : rest.mapM action middle with
      | stop reason final | escape address carriers final | jump target kind final =>
        simp only [tail] at executed
        cases executed
      | ok remaining final =>
        simp only [tail, pure] at executed
        cases executed
        intro actual member
        rcases List.mem_cons.mp member with same | member
        · subst actual
          exact one first before value middle head
        · exact ih middle _ remaining tail actual member

theorem materializeOwnedCarriers_surviving (origin : OriginId) (tokens : List ExitReservationId)
    (carriers output : List Carrier) (before after : ExecutionState)
    (executed : materializeOwnedCarriers origin tokens carriers before = .ok output after) :
    ∀ token ∈ survivingPendingNamed (.completed output), token ∉ tokens := by
  let action : Carrier → EvalM Carrier := fun carrier => match carrier with
    | .pendingNamed token => if tokens.contains token then do
        pure (.completed (← liftConstruction origin (materializeNamedReservation token))) else pure carrier
    | carrier => pure carrier
  have one : ∀ (carrier : Carrier) (state : ExecutionState) (value : Carrier) (final : ExecutionState),
      action carrier state = .ok value final →
      ∀ token, value = .pendingNamed token → token ∉ tokens := by
    intro carrier state value final evaluated token same
    subst value
    cases carrier with
    | register value | completed id => cases evaluated
    | pendingNamed actual =>
      cases owned : tokens.contains actual with
      | false =>
        simp only [action, owned, Bool.false_eq_true, ↓reduceIte, pure] at evaluated
        cases evaluated
        intro member
        have contained := List.contains_iff_mem.mpr member
        rw [owned] at contained
        cases contained
      | true =>
        simp only [action, owned, ↓reduceIte, bind] at evaluated
        cases materialized : materializeNamedReservation actual state.construction with
        | fault reason construction => simp only [liftConstruction, materialized] at evaluated; cases evaluated
        | ok id construction => simp only [liftConstruction, materialized, pure] at evaluated; cases evaluated
  have values := mapM_output_property carriers action
    (fun carrier => ∀ token, carrier = .pendingNamed token → token ∉ tokens) one before after output executed
  intro token member
  exact values (.pendingNamed token) ((survivingPendingNamed_member (.completed output) token).mp member) token rfl

def ActiveExitScope.cleanup {config : EvalConfig} {source : RuntimeActivation} {entered : ExecutionState}
    (scope : ActiveExitScope config source entered) (result : OwnershipChannelResult) : EvalM Unit :=
  ownershipExitCleanup scope.origin scope.borrowed scope.ownNewTokens result.cancel result.carriers

inductive ActiveExitDischarge {config : EvalConfig} {source : RuntimeActivation} {entered : ExecutionState}
    (scope : ActiveExitScope config source entered) (before : ExecutionState) :
    OwnershipChannelResult → ExecutionStep (List Carrier) → Prop
  | completed (carriers : List Carrier) (after : ExecutionState)
      (cleaned : scope.cleanup (.completed carriers) before = .ok () after) :
      ActiveExitDischarge scope before (.completed carriers) (.ok carriers after)
  | stopped (reason : Goose.Core.Stop) (after : ExecutionState)
      (cleaned : scope.cleanup (.stopped reason) before = .ok () after) :
      ActiveExitDischarge scope before (.stopped reason) (.stop reason after)
  | escaped (address : ExitAddress) (carriers : List Carrier) (after : ExecutionState)
      (cleaned : scope.cleanup (.escaped address carriers) before = .ok () after) :
      ActiveExitDischarge scope before (.escaped address carriers) (.escape address carriers after)
  | jumped (target : Nat) (kind : JumpKind) (after : ExecutionState)
      (cleaned : scope.cleanup (.jumped target kind) before = .ok () after) :
      ActiveExitDischarge scope before (.jumped target kind) (.jump target kind after)
  | cleanupStopped (result : OwnershipChannelResult) (reason : Goose.Core.Stop) (after : ExecutionState)
      (cleaned : scope.cleanup result before = .stop reason after) :
      ActiveExitDischarge scope before result (.stop reason after)

theorem ActiveExitDischarge.native {config : EvalConfig} {source : RuntimeActivation} {entered : ExecutionState}
    {scope : ActiveExitScope config source entered} {before : ExecutionState}
    {result : OwnershipChannelResult} {output : ExecutionStep (List Carrier)}
    (discharged : ActiveExitDischarge scope before result output) :
    finishOwnershipExitChannels scope.origin scope.borrowed scope.ownNewTokens (result.emit before) = output := by
  rw [finishOwnershipExitChannels_emit]
  cases discharged <;>
    simp only [runOwnershipExitContinuation, ActiveExitScope.cleanup] at *
  all_goals simp_all only [OwnershipChannelResult.emit]

theorem ActiveExitScope.discharge {config : EvalConfig} {source : RuntimeActivation} {entered : ExecutionState}
    (scope : ActiveExitScope config source entered) (before : ExecutionState) (result : OwnershipChannelResult) :
    ActiveExitDischarge scope before result
      (finishOwnershipExitChannels scope.origin scope.borrowed scope.ownNewTokens (result.emit before)) := by
  obtain ⟨after, cleaned | ⟨reason, stopped⟩⟩ :=
    ownershipExitCleanup_control scope.origin scope.borrowed scope.ownNewTokens result.cancel result.carriers before
  · cases result with
    | completed carriers =>
      have discharged : ActiveExitDischarge scope before (.completed carriers) (.ok carriers after) := .completed carriers after cleaned
      rw [discharged.native]
      exact discharged
    | stopped reason =>
      have discharged : ActiveExitDischarge scope before (.stopped reason) (.stop reason after) := .stopped reason after cleaned
      rw [discharged.native]
      exact discharged
    | escaped address carriers =>
      have discharged : ActiveExitDischarge scope before (.escaped address carriers) (.escape address carriers after) := .escaped address carriers after cleaned
      rw [discharged.native]
      exact discharged
    | jumped target kind =>
      have discharged : ActiveExitDischarge scope before (.jumped target kind) (.jump target kind after) := .jumped target kind after cleaned
      rw [discharged.native]
      exact discharged
  · have discharged : ActiveExitDischarge scope before result (.stop reason after) := .cleanupStopped result reason after stopped
    rw [discharged.native]
    exact discharged

theorem ActiveExitScope.discharge_body {config : EvalConfig} {source : RuntimeActivation} {entered : ExecutionState}
    (scope : ActiveExitScope config source entered) (action : List Channel → EvalM (List Carrier))
    (before : ExecutionState) (result : OwnershipChannelResult)
    (evaluated : ((do materializeOwnedCarriers scope.origin scope.ownNewTokens (← action scope.channels)) scope.prepared) = result.emit before) :
    ActiveExitDischarge scope before result
      (withExitChannels source scope.activation scope.operands scope.origin action entered) := by
  rw [withExitChannels_ownership_continuation, scope.setup]
  change ActiveExitDischarge scope before result
    (finishOwnershipExitChannels scope.origin scope.borrowed scope.ownNewTokens
      ((do materializeOwnedCarriers scope.origin scope.ownNewTokens (← action scope.channels)) scope.prepared))
  rw [evaluated]
  exact scope.discharge before result

#print axioms borrowed_pending_cleanup
#print axioms materializeOwnedCarriers_surviving
#print axioms ActiveExitScope.borrowed_not_owned
#print axioms ActiveExitDischarge.native
#print axioms ActiveExitScope.discharge
#print axioms ActiveExitScope.discharge_body

end Goose.Proofs.ExitExecution
