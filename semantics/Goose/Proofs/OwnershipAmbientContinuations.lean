import Goose.Proofs.OwnershipAmbientFrontiers

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct Goose.Proofs.ConstructionExecutionProtocol
open Goose.Core (OriginId ScopeInst VarId DestinationId)

inductive OwnershipChannelResult
  | completed (carriers : List Construct.Carrier)
  | stopped (reason : Core.Stop)
  | escaped (address : ExitAddress) (carriers : List Construct.Carrier)
  | jumped (target : Nat) (kind : JumpKind)

def OwnershipChannelResult.carriers : OwnershipChannelResult → List Construct.Carrier
  | .completed carriers | .escaped _ carriers | .jumped _ (.breakValue carriers) => carriers
  | .stopped _ | .jumped _ .continueLoop => []

def OwnershipChannelResult.cancel : OwnershipChannelResult → Bool
  | .completed _ | .stopped _ => false
  | .escaped _ _ | .jumped _ _ => true

def OwnershipChannelResult.emit : OwnershipChannelResult → ExecutionState → ExecutionStep (List Construct.Carrier)
  | .completed carriers, state => .ok carriers state
  | .stopped reason, state => .stop reason state
  | .escaped address carriers, state => .escape address carriers state
  | .jumped target kind, state => .jump target kind state

def ownershipChannelCleanup (origin : OriginId) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Construct.Carrier) : EvalM Unit := do
  for token in tokens do
    if cancel then liftConstruction origin (cancelExitReservation token (completedCarrierIds carriers))
    liftConstruction origin (releaseExitReservation token)

private def CleanupControl : ExecutionStep α → Prop
  | .ok _ _ | .stop _ _ => True
  | .escape _ _ _ | .jump _ _ _ => False

private theorem cleanupControl_bind (action : EvalM α) (next : α → EvalM β)
    (first : ∀ state, CleanupControl (action state))
    (remaining : ∀ value state, CleanupControl (next value state)) (state : ExecutionState) :
    CleanupControl ((action >>= next) state) := by
  have control := first state
  cases evaluated : action state with
  | ok value after => simpa only [bind, evaluated] using remaining value after
  | stop reason after => simp only [bind, evaluated, CleanupControl]
  | escape address carriers after | jump target kind after =>
      simp only [evaluated, CleanupControl] at control

private theorem cleanupControl_lift (origin : OriginId) (action : ConstructionM α) (state : ExecutionState) :
    CleanupControl (liftConstruction origin action state) := by
  cases evaluated : action state.construction <;> simp [liftConstruction, evaluated, CleanupControl]

private theorem cleanupControl_forIn (items : List α) (action : α → β → EvalM (ForInStep β))
    (initial : β) (body : ∀ item value state, CleanupControl (action item value state)) (state : ExecutionState) :
    CleanupControl (forIn items initial action state) := by
  induction items generalizing initial state with
  | nil => trivial
  | cons item rest previous =>
      rw [List.forIn_cons]
      apply cleanupControl_bind _ _ (body item initial)
      intro step after
      cases step with
      | done value => trivial
      | yield value => exact previous value after

private theorem ownershipChannelCleanup_straight (origin : OriginId) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Construct.Carrier) (state : ExecutionState) :
    CleanupControl (ownershipChannelCleanup origin tokens cancel carriers state) := by
  unfold ownershipChannelCleanup
  apply cleanupControl_bind
  · intro current
    apply cleanupControl_forIn
    intro token accumulator now
    cases cancel <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · apply cleanupControl_bind _ _ (cleanupControl_lift origin (releaseExitReservation token))
      intro value after
      trivial
    · apply cleanupControl_bind _ _ (cleanupControl_lift origin (cancelExitReservation token (completedCarrierIds carriers)))
      intro value after
      apply cleanupControl_bind _ _ (cleanupControl_lift origin (releaseExitReservation token))
      intro value final
      trivial
  · intro value current
    trivial

theorem ownershipChannelCleanup_control (origin : OriginId) (tokens : List ExitReservationId)
    (cancel : Bool) (carriers : List Construct.Carrier) (state : ExecutionState) :
    ∃ final, ownershipChannelCleanup origin tokens cancel carriers state = .ok () final ∨
      ∃ reason, ownershipChannelCleanup origin tokens cancel carriers state = .stop reason final := by
  have control := ownershipChannelCleanup_straight origin tokens cancel carriers state
  cases evaluated : ownershipChannelCleanup origin tokens cancel carriers state with
  | ok value final => cases value; exact ⟨final, Or.inl rfl⟩
  | stop reason final => exact ⟨final, Or.inr ⟨reason, rfl⟩⟩
  | escape address values final | jump target kind final =>
      simp only [evaluated, CleanupControl] at control

def runOwnershipChannelContinuation (origin : OriginId) (tokens : List ExitReservationId)
    (result : OwnershipChannelResult) (state : ExecutionState) : ExecutionStep (List Construct.Carrier) :=
  match ownershipChannelCleanup origin tokens.reverse result.cancel result.carriers state with
  | .ok () final => result.emit final
  | .stop reason final => .stop reason final
  | .escape address carriers final => .escape address carriers final
  | .jump target kind final => .jump target kind final

theorem runOwnershipChannelContinuation_retains (origin : OriginId) (tokens : List ExitReservationId)
    (result : OwnershipChannelResult) (state : ExecutionState) :
    ∃ final, runOwnershipChannelContinuation origin tokens result state = result.emit final ∨
      ∃ reason, runOwnershipChannelContinuation origin tokens result state = .stop reason final := by
  obtain ⟨final, completed | ⟨reason, stopped⟩⟩ :=
    ownershipChannelCleanup_control origin tokens.reverse result.cancel result.carriers state
  · exact ⟨final, Or.inl (by simp only [runOwnershipChannelContinuation, completed])⟩
  · exact ⟨final, Or.inr ⟨reason, by simp only [runOwnershipChannelContinuation, stopped]⟩⟩

theorem ownershipChannelResult_capture (state : ExecutionState) (frame : OwnershipAmbientFrame)
    (outer : OwnershipAmbient) (result : OwnershipChannelResult) :
    OwnershipAmbientOutcome (frame.withCarriers [] :: outer) .carriers (result.emit state) ↔
      match result with
      | .stopped _ => OwnershipStructural state.construction
      | .jumped _ .continueLoop => OwnershipAmbientInvariant state.construction (frame.withCarriers [] :: outer)
      | _ => OwnershipAmbientInvariant state.construction (frame.withCarriers result.carriers :: outer) := by
  cases result with
  | completed carriers | escaped address carriers =>
      exact ownershipAmbientInvariant_capture_returned state.construction frame outer carriers
  | stopped reason => rfl
  | jumped target kind =>
      cases kind with
      | breakValue carriers => exact ownershipAmbientInvariant_capture_returned state.construction frame outer carriers
      | continueLoop => rfl

def finishOwnershipChannels (origin : OriginId) (tokens : List ExitReservationId) :
    ExecutionStep (List Construct.Carrier) → ExecutionStep (List Construct.Carrier)
  | .ok carriers state => runOwnershipChannelContinuation origin tokens (.completed carriers) state
  | .stop reason state => runOwnershipChannelContinuation origin tokens (.stopped reason) state
  | .escape address carriers state => runOwnershipChannelContinuation origin tokens (.escaped address carriers) state
  | .jump target kind state => runOwnershipChannelContinuation origin tokens (.jumped target kind) state

def newOwnershipExitTokens (first : Nat) (prepared : ExecutionState) : List ExitReservationId :=
  (List.range (prepared.construction.exitReservations.size - first)).map (first + ·)

theorem newOwnershipExitTokens_mem (first : Nat) (prepared : ExecutionState) (token : ExitReservationId) :
    token ∈ newOwnershipExitTokens first prepared ↔
      first ≤ token ∧ token < prepared.construction.exitReservations.size := by
  simp only [newOwnershipExitTokens, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨offset, bounded, rfl⟩
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_of_lt_sub' bounded⟩
  · intro bounded
    exact ⟨token - first, Nat.sub_lt_sub_right bounded.1 bounded.2, Nat.add_sub_of_le bounded.1⟩

theorem releaseExitReservation_other_ticket (state : ConstructionState) (token other : ExitReservationId)
    (different : token ≠ other) :
    (releaseExitReservation token state).finalState.exitReservations[other]? = state.exitReservations[other]? := by
  cases found : state.exitReservations[token]? with
  | none => simp [releaseExitReservation, found, ConstructionM.get, ConstructionM.fail, bind, ConstructionResult.finalState]
  | some reservation =>
      cases reservation <;>
        simp [releaseExitReservation, found, ConstructionM.get, ConstructionM.set,
          ConstructionM.fail, bind, pure, ConstructionResult.finalState, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne different]

def borrowedOwnershipExitReceipts (activation : RuntimeActivation) (state : ExecutionState) :
    List BorrowedWaitingExitReservation :=
  activation.channels.filterMap fun channel => match channel with
    | .completion token => captureWaitingExitReservation token state.construction
    | _ => none

theorem borrowedOwnershipExitReceipts_source (activation : RuntimeActivation) (state : ExecutionState)
    (receipt : BorrowedWaitingExitReservation) (member : receipt ∈ borrowedOwnershipExitReceipts activation state) :
    Construct.Channel.completion receipt.token ∈ activation.channels ∧
      state.construction.exitReservations[receipt.token]? = some (.waiting receipt.incoming) := by
  obtain ⟨channel, present, captured⟩ := List.mem_filterMap.mp member
  cases channel with
  | register ty | construct incoming => simp at captured
  | completion token =>
      obtain ⟨same, waiting⟩ := captureWaitingExitReservation_source token state.construction receipt captured
      simpa only [same] using And.intro present waiting

theorem borrowedOwnershipExitReceipts_bounded (activation : RuntimeActivation) (state : ExecutionState)
    (receipt : BorrowedWaitingExitReservation) (member : receipt ∈ borrowedOwnershipExitReceipts activation state) :
    receipt.token < state.construction.exitReservations.size := by
  exact (Array.getElem?_eq_some_iff.mp (borrowedOwnershipExitReceipts_source activation state receipt member).2).1

def ownershipBorrowedReceiptCleanup (origin : OriginId) (receipt : BorrowedWaitingExitReservation)
    (carriers : List Construct.Carrier) : EvalM Unit := do
  let token := receipt.token
  if carriers.any (fun carrier => match carrier with
      | .pendingNamed actual => actual == token
      | _ => false) then pure ()
  else do
    liftConstruction origin (cancelExitReservation token (completedCarrierIds carriers))
    match (← EvalM.get).construction.exitReservations[token]? with
    | some .restored => liftConstruction origin (rearmExitReservation receipt)
    | some (.waiting actual) => if actual != receipt.incoming then fault .flow
    | some (.active ..) => pure ()
    | _ => fault .flow


def ownershipExitCleanup (origin : OriginId) (borrowed : List BorrowedWaitingExitReservation)
    (tokens : List ExitReservationId) (cancel : Bool) (carriers : List Construct.Carrier) : EvalM Unit := do
  if cancel then
    for receipt in borrowed.reverse do
      let token := receipt.token
      if carriers.any (fun carrier => match carrier with
          | .pendingNamed actual => actual == token
          | _ => false) then pure ()
      else do
        liftConstruction origin (cancelExitReservation token (completedCarrierIds carriers))
        match (← EvalM.get).construction.exitReservations[token]? with
        | some .restored => liftConstruction origin (rearmExitReservation receipt)
        | some (.waiting actual) => if actual != receipt.incoming then fault .flow
        | some (.active ..) => pure ()
        | _ => fault .flow

  for token in tokens.reverse do
    if cancel then liftConstruction origin (cancelExitReservation token (completedCarrierIds carriers))
    liftConstruction origin (releaseExitReservation token)

private theorem ownershipBorrowedReceiptCleanup_straight (origin : OriginId)
    (receipt : BorrowedWaitingExitReservation) (carriers : List Construct.Carrier) (state : ExecutionState) :
    CleanupControl (ownershipBorrowedReceiptCleanup origin receipt carriers state) := by
  unfold ownershipBorrowedReceiptCleanup
  split <;> first | trivial | skip
  apply cleanupControl_bind _ _ (cleanupControl_lift origin _)
  intro value after
  apply cleanupControl_bind
  · intro final
    trivial
  · intro current final
    cases found : current.construction.exitReservations[receipt.token]? with
    | none => trivial
    | some reservation =>
        cases reservation with
        | waiting incoming => dsimp only; split <;> trivial
        | active role incoming reserved snapshot => trivial
        | restored => exact cleanupControl_lift origin _ final
        | released => trivial


theorem ownershipBorrowedReceiptCleanup_control (origin : OriginId)
    (receipt : BorrowedWaitingExitReservation) (carriers : List Construct.Carrier) (state : ExecutionState) :
    ∃ final, ownershipBorrowedReceiptCleanup origin receipt carriers state = .ok () final ∨
      ∃ reason, ownershipBorrowedReceiptCleanup origin receipt carriers state = .stop reason final := by
  have control := ownershipBorrowedReceiptCleanup_straight origin receipt carriers state
  cases evaluated : ownershipBorrowedReceiptCleanup origin receipt carriers state with
  | ok value final => cases value; exact ⟨final, Or.inl rfl⟩
  | stop reason final => exact ⟨final, Or.inr ⟨reason, rfl⟩⟩
  | escape address values final | jump target kind final =>
      simp only [evaluated, CleanupControl] at control

private theorem ownershipExitCleanup_straight (origin : OriginId) (borrowed : List BorrowedWaitingExitReservation)
    (tokens : List ExitReservationId) (cancel : Bool) (carriers : List Construct.Carrier) (state : ExecutionState) :
    CleanupControl (ownershipExitCleanup origin borrowed tokens cancel carriers state) := by
  cases cancel with
  | false =>
      exact ownershipChannelCleanup_straight origin tokens.reverse false carriers state
  | true =>
      unfold ownershipExitCleanup
      dsimp only
      apply cleanupControl_bind
      · intro current
        apply cleanupControl_forIn
        intro receipt accumulator now
        split <;> first | trivial | skip
        apply cleanupControl_bind _ _ (cleanupControl_lift origin _)
        intro value after
        apply cleanupControl_bind
        · intro final
          trivial
        · intro current final
          cases found : current.construction.exitReservations[receipt.token]? with
          | none => trivial
          | some reservation =>
              cases reservation with
              | waiting incoming =>
                  dsimp only
                  split
                  · trivial
                  · trivial
              | active role incoming reserved snapshot => trivial
              | restored =>
                  dsimp only
                  apply cleanupControl_bind _ _ (cleanupControl_lift origin _)
                  intro value last
                  trivial
              | released => trivial
      · intro value current
        exact ownershipChannelCleanup_straight origin tokens.reverse true carriers current

theorem ownershipExitCleanup_control (origin : OriginId) (borrowed : List BorrowedWaitingExitReservation)
    (tokens : List ExitReservationId) (cancel : Bool) (carriers : List Construct.Carrier) (state : ExecutionState) :
    ∃ final, ownershipExitCleanup origin borrowed tokens cancel carriers state = .ok () final ∨
      ∃ reason, ownershipExitCleanup origin borrowed tokens cancel carriers state = .stop reason final := by
  have control := ownershipExitCleanup_straight origin borrowed tokens cancel carriers state
  cases evaluated : ownershipExitCleanup origin borrowed tokens cancel carriers state with
  | ok value final => cases value; exact ⟨final, Or.inl rfl⟩
  | stop reason final => exact ⟨final, Or.inr ⟨reason, rfl⟩⟩
  | escape address values final | jump target kind final =>
      simp only [evaluated, CleanupControl] at control

def runOwnershipExitContinuation (origin : OriginId) (borrowed : List BorrowedWaitingExitReservation)
    (tokens : List ExitReservationId) (result : OwnershipChannelResult) (state : ExecutionState) :
    ExecutionStep (List Construct.Carrier) :=
  match ownershipExitCleanup origin borrowed tokens result.cancel result.carriers state with
  | .ok () final => result.emit final
  | .stop reason final => .stop reason final
  | .escape address carriers final => .escape address carriers final
  | .jump target kind final => .jump target kind final

theorem runOwnershipExitContinuation_retains (origin : OriginId) (borrowed : List BorrowedWaitingExitReservation)
    (tokens : List ExitReservationId) (result : OwnershipChannelResult) (state : ExecutionState) :
    ∃ final, runOwnershipExitContinuation origin borrowed tokens result state = result.emit final ∨
      ∃ reason, runOwnershipExitContinuation origin borrowed tokens result state = .stop reason final := by
  obtain ⟨final, completed | ⟨reason, stopped⟩⟩ :=
    ownershipExitCleanup_control origin borrowed tokens result.cancel result.carriers state
  · exact ⟨final, Or.inl (by simp only [runOwnershipExitContinuation, completed])⟩
  · exact ⟨final, Or.inr ⟨reason, by simp only [runOwnershipExitContinuation, stopped]⟩⟩

def finishOwnershipExitChannels (origin : OriginId) (borrowed : List BorrowedWaitingExitReservation)
    (tokens : List ExitReservationId) : ExecutionStep (List Construct.Carrier) → ExecutionStep (List Construct.Carrier)
  | .ok carriers state => runOwnershipExitContinuation origin borrowed tokens (.completed carriers) state
  | .stop reason state => runOwnershipExitContinuation origin borrowed tokens (.stopped reason) state
  | .escape address carriers state => runOwnershipExitContinuation origin borrowed tokens (.escaped address carriers) state
  | .jump target kind state => runOwnershipExitContinuation origin borrowed tokens (.jumped target kind) state

theorem ownershipExitCleanup_without_cancel (origin : OriginId) (borrowed : List BorrowedWaitingExitReservation)
    (tokens : List ExitReservationId) (carriers : List Construct.Carrier) :
    ownershipExitCleanup origin borrowed tokens false carriers = ownershipChannelCleanup origin tokens.reverse false carriers := by
  funext state
  simp only [ownershipExitCleanup, Bool.false_eq_true, ↓reduceIte, pure, bind]
  rfl

theorem runOwnershipExitContinuation_without_cancel (origin : OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List ExitReservationId)
    (result : OwnershipChannelResult) (state : ExecutionState) (ordinary : result.cancel = false) :
    runOwnershipExitContinuation origin borrowed tokens result state =
      runOwnershipChannelContinuation origin tokens result state := by
  simp only [runOwnershipExitContinuation, runOwnershipChannelContinuation, ordinary,
    ownershipExitCleanup_without_cancel]

theorem withExitChannels_ownership_continuation (source activation : RuntimeActivation)
    (operands : List Expr) (origin : OriginId) (action : List Construct.Channel → EvalM (List Construct.Carrier))
    (state : ExecutionState) :
    withExitChannels source activation operands origin action state =
      match exitChannels source activation operands origin state with
      | .ok channels prepared => finishOwnershipExitChannels origin (borrowedOwnershipExitReceipts activation state)
          (newOwnershipExitTokens state.construction.exitReservations.size prepared)
          ((do materializeOwnedCarriers origin (newOwnershipExitTokens state.construction.exitReservations.size prepared) (← action channels)) prepared)
      | .stop reason final => .stop reason final
      | .escape address carriers final => .escape address carriers final
      | .jump target kind final => .jump target kind final := by
  unfold withExitChannels
  cases setupResult : exitChannels source activation operands origin state with
  | stop reason final | escape address carriers final | jump target kind final => rfl
  | ok channels prepared =>
      dsimp only [newOwnershipExitTokens]
      cases evaluated : ((do materializeOwnedCarriers origin ((List.range (prepared.construction.exitReservations.size - state.construction.exitReservations.size)).map (state.construction.exitReservations.size + ·)) (← action channels)) prepared) with
      | ok carriers final | stop reason final | escape address carriers final => rfl
      | jump target kind final => cases kind <;> rfl

theorem finishOwnershipExitChannels_emit (origin : OriginId) (borrowed : List BorrowedWaitingExitReservation)
    (tokens : List ExitReservationId) (result : OwnershipChannelResult) (state : ExecutionState) :
    finishOwnershipExitChannels origin borrowed tokens (result.emit state) =
      runOwnershipExitContinuation origin borrowed tokens result state := by
  cases result <;> rfl

theorem withExitChannels_retains_evaluated (source activation : RuntimeActivation)
    (operands : List Expr) (origin : OriginId) (action : List Construct.Channel → EvalM (List Construct.Carrier))
    (state prepared after : ExecutionState) (channels : List Construct.Channel) (result : OwnershipChannelResult)
    (setup : exitChannels source activation operands origin state = .ok channels prepared)
    (evaluated : ((do materializeOwnedCarriers origin (newOwnershipExitTokens state.construction.exitReservations.size prepared) (← action channels)) prepared) = result.emit after) :
    ∃ final, withExitChannels source activation operands origin action state = result.emit final ∨
      ∃ reason, withExitChannels source activation operands origin action state = .stop reason final := by
  simp only [withExitChannels_ownership_continuation, setup]
  rw [evaluated, finishOwnershipExitChannels_emit]
  exact runOwnershipExitContinuation_retains origin (borrowedOwnershipExitReceipts activation state)
    (newOwnershipExitTokens state.construction.exitReservations.size prepared) result after

def ownershipCompletionSetupAt (channels : List Construct.Channel) (origin : OriginId) :
    EvalM (List Construct.Channel × List ExitReservationId) := do
  let planned ← channels.mapM fun channel => match channel with
    | .construct incoming => do
        let token ← liftConstruction origin (waitExitDestination incoming)
        pure (Construct.Channel.completion token, some token)
    | .register ty => pure (Construct.Channel.register ty, none)
    | .completion _ => fault .flow
  pure (planned.map Prod.fst, planned.filterMap Prod.snd)

theorem withCompletionChannels_ownership_continuation (channels : List Construct.Channel)
    (origin : OriginId) (action : List Construct.Channel → EvalM (List Construct.Carrier)) (state : ExecutionState) :
    withCompletionChannels channels origin action state =
      match ownershipCompletionSetupAt channels origin state with
      | .ok (planned, tokens) prepared => finishOwnershipChannels origin tokens
          ((do materializeOwnedCarriers origin tokens (← action planned)) prepared)
      | .stop reason final => .stop reason final
      | .escape address carriers final => .escape address carriers final
      | .jump target kind final => .jump target kind final := by
  unfold withCompletionChannels
  change (match ownershipCompletionSetupAt channels origin state with
    | .ok (planned, tokens) prepared => _
    | .stop reason final => ExecutionStep.stop reason final
    | .escape address carriers final => ExecutionStep.escape address carriers final
    | .jump target kind final => ExecutionStep.jump target kind final) = _
  cases setupResult : ownershipCompletionSetupAt channels origin state with
  | stop reason final | escape address carriers final | jump target kind final => rfl
  | ok pair prepared =>
      rcases pair with ⟨planned, tokens⟩
      dsimp only
      cases evaluated : ((do materializeOwnedCarriers origin tokens (← action planned)) prepared) with
      | ok carriers final | stop reason final | escape address carriers final => rfl
      | jump target kind final => cases kind <;> rfl

theorem withScope_ownership_outcome (environment : RuntimeActivation) (scope : Nat) (scopeInst : ScopeInst)
    (ambient : OwnershipAmbient) (shape : OwnershipResultShape α) (action : EvalM α) (state : ExecutionState) :
    OwnershipAmbientOutcome ambient shape (withScope environment scope scopeInst action state) ↔
      OwnershipAmbientOutcome ambient shape (action state) := by
  unfold withScope
  cases evaluated : action state with
  | ok value final | stop reason final | escape address carriers final => rfl
  | jump target kind final => cases kind <;> rfl

def ownershipResultScopeState (environment : RuntimeActivation) (scope : Nat) (state : ExecutionState) : ExecutionState :=
  { state with
    nextScope := state.nextScope + 1
    activations := state.activations.map (fun current =>
      if current.act == environment.act then { current with scopes := (scope, state.nextScope) :: environment.scopes }
      else current) }

theorem execResultScope_ownership_continuation (environment : RuntimeActivation)
    (pre : List (VarId × Value)) (channels : List Construct.Channel) (scope : Nat)
    (statements : List Stmt) (value : Option Expr)
    (statementsAction : RuntimeActivation → List Stmt → EvalM Construct.Flow)
    (tailAction : RuntimeActivation → Expr → EvalM (List Construct.Carrier)) (state : ExecutionState) :
    execResultScope environment pre channels (.mk scope statements value) statementsAction tailAction state =
      withScope environment scope state.nextScope (do
        bindAll environment.act state.nextScope pre
        let flow ← statementsAction { environment with scopes := (scope, state.nextScope) :: environment.scopes } statements
        match flow, value with
        | .normal _, some expression => pure (.normal .unit,
            ← tailAction { environment with scopes := (scope, state.nextScope) :: environment.scopes } expression)
        | .normal _, none =>
            if channels.isEmpty then pure (flow, [])
            else match channels with
              | [.register .unit] => pure (flow, [.register .unit])
              | _ => fault .arity
        | flow, _ => pure (flow, [])) (ownershipResultScopeState environment scope state) := rfl

theorem ownershipResultScopeState_construction (environment : RuntimeActivation) (scope : Nat) (state : ExecutionState) :
    (ownershipResultScopeState environment scope state).construction = state.construction := rfl

theorem landCarriersInto_pending_named (origin : OriginId) (token : ExitReservationId) (state : ExecutionState) :
    landCarriersInto origin [.completion token] [.pendingNamed token] state = .ok () state := by
  simp [landCarriersInto, List.forIn_cons, List.forIn_nil, bind, pure]

theorem landCarriersInto_current_completion (origin : OriginId) (token : ExitReservationId)
    (role : ExitReservationRole) (incoming reserved current replacement : DestinationId)
    (snapshot : PendingDestination) (state : ExecutionState)
    (ticket : state.construction.exitReservations[token]? = some (.active role incoming reserved snapshot))
    (resolved : destinationCurrent state.construction reserved = .ok current) :
    landCarriersInto origin [.completion token] [.completed replacement] state =
      if current != replacement then liftConstruction origin (landExitReplacementInto current replacement) state
      else .ok () state := by
  by_cases same : current = replacement
  · subst replacement
    simp [landCarriersInto, ticket, receivingDestination, liftConstruction, resolved,
      List.forIn_cons, List.forIn_nil, bind, pure, EvalM.get]
  · have different : (current != replacement) = true := bne_iff_ne.mpr same
    cases landed : landExitReplacementInto current replacement state.construction with
    | ok value construction =>
        cases value
        simp [landCarriersInto, ticket, receivingDestination, liftConstruction, resolved,
          List.forIn_cons, List.forIn_nil, bind, pure, EvalM.get, different, same, landed]
    | fault kind construction =>
        simp [landCarriersInto, ticket, receivingDestination, liftConstruction, resolved,
          List.forIn_cons, List.forIn_nil, bind, pure, EvalM.get, different, same, landed]

#print axioms withExitChannels_retains_evaluated
#print axioms borrowedOwnershipExitReceipts_bounded
#print axioms ownershipBorrowedReceiptCleanup_control
#print axioms runOwnershipExitContinuation_without_cancel
#print axioms borrowedOwnershipExitReceipts_source
#print axioms ownershipExitCleanup_control
#print axioms runOwnershipExitContinuation_retains
#print axioms ownershipExitCleanup_without_cancel
#print axioms withExitChannels_ownership_continuation
#print axioms withCompletionChannels_ownership_continuation
#print axioms withScope_ownership_outcome
#print axioms execResultScope_ownership_continuation
#print axioms ownershipChannelCleanup_control
#print axioms runOwnershipChannelContinuation_retains
#print axioms ownershipChannelResult_capture
#print axioms newOwnershipExitTokens_mem
#print axioms landCarriersInto_current_completion
#print axioms landCarriersInto_pending_named

end Goose.Proofs.ConstructionExecutionOwnership
