import Goose.Proofs.ExitExecutionCleanupStorageLanding

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core

local syntax "cleanup_finish_storage" : tactic
macro_rules
  | `(tactic| cleanup_finish_storage) => `(tactic|
    repeat' first
      | with_reducible exact RuntimeCleanupStorage.of_storage_eq _ (fun _ => rfl)
      | with_reducible exact RuntimeCleanupStorage.query _ (stateQuery_getDestination _)
      | with_reducible exact RuntimeCleanupStorage.query _ (stateQuery_receivingDestination _)
      | with_reducible exact RuntimeCleanupStorage.query _ (stateQuery_receivingLayout _ _)
      | solve
        | with_reducible apply RuntimeCleanupStorage.lift
          first
            | exact landExitReplacementChain_storage _
            | exact landExitReplacementInto_storage _ _
            | exact normalizeProducerDestination_storage _ _
            | exact removeConstructionHeader_storage _
            | exact restoreReceivingLayout_storage _ _
            | exact adaptDestinationType_storage _ _
      | with_reducible apply RuntimeCleanupStorage.bind
      | with_reducible apply RuntimeCleanupStorage.ite
      | split
      | (guard_target = ∀ _, RuntimeCleanupStorage _; intro value))

theorem landCarrier_storage (origin : OriginId) (carrier : Goose.Construct.Carrier) :
    RuntimeCleanupStorage (landCarrier origin carrier) := by
  unfold landCarrier
  cases carrier <;> cleanup_finish_storage

theorem landCarriers_storage (origin : OriginId) (carriers : List Goose.Construct.Carrier) :
    RuntimeCleanupStorage (landCarriers origin carriers) := by
  unfold landCarriers
  apply RuntimeCleanupStorage.foreach
  exact landCarrier_storage origin

theorem landCarriersInto_storage (origin : OriginId) (channels : List Channel)
    (carriers : List Goose.Construct.Carrier) :
    RuntimeCleanupStorage (landCarriersInto origin channels carriers) := by
  unfold landCarriersInto
  apply RuntimeCleanupStorage.ite
  · exact .of_storage_eq _ (fun _ => rfl)
  · apply RuntimeCleanupStorage.bind
    · apply RuntimeCleanupStorage.forIn
      intro item accumulator
      rcases item with ⟨channel, carrier⟩
      cases channel <;> cases carrier <;> cleanup_finish_storage
    · intro _
      exact .pure _

theorem finishChannel_storage (layout : LayoutEnv) (origin : OriginId)
    (carrier : Goose.Construct.Carrier) (result : Goose.Construct.Ty) :
    RuntimeCleanupStorage (finishChannel layout origin carrier result) := by
  unfold finishChannel
  cases carrier <;> cleanup_finish_storage

theorem finishChannels_storage (layout : LayoutEnv) (channels : List Channel)
    (types : List Goose.Construct.Ty) (carriers : List Goose.Construct.Carrier) (origin : OriginId) :
    RuntimeCleanupStorage (finishChannels layout channels types carriers origin) := by
  unfold finishChannels
  apply RuntimeCleanupStorage.bind
  · exact landCarriersInto_storage origin channels carriers
  · intro _
    apply RuntimeCleanupStorage.ite
    · exact .of_storage_eq _ (fun _ => rfl)
    · apply RuntimeCleanupStorage.bind
      · apply RuntimeCleanupStorage.forIn
        intro item accumulator
        rcases item with ⟨carrier, result⟩
        apply RuntimeCleanupStorage.bind
        · exact finishChannel_storage layout origin carrier result
        · intro _
          exact .pure _
      · intro _
        exact .pure _

theorem finishActivation_after_action_storage (layout : LayoutEnv) (activation : RuntimeActivation)
    (types : List Goose.Construct.Ty) (origin : OriginId) (action : EvalM (List Goose.Construct.Carrier)) :
    ∀ initial, ∃ changes, CleanupStorageTrace changes
      (Goose.Proofs.Exit.stepState (action initial)).construction.storage
      (Goose.Proofs.Exit.stepState (finishActivation layout activation types origin action initial)).construction.storage := by
  intro initial
  cases evaluated : action initial with
  | ok carriers after =>
      obtain ⟨changes, framed⟩ := finishChannels_storage layout activation.channels types carriers origin
        { after with activations := after.activations.filter (fun current => current.act != activation.act) }
      cases finishing : finishChannels layout activation.channels types carriers origin
          { after with activations := after.activations.filter (fun current => current.act != activation.act) } with
      | ok ignored final =>
          cases ignored
          exact ⟨changes, by simpa only [finishActivation, evaluated, finishing,
            Goose.Proofs.Exit.stepState] using framed⟩
      | stop reason final | escape address values final | jump target kind final =>
          exact ⟨changes, by simpa only [finishActivation, evaluated, finishing,
            Goose.Proofs.Exit.stepState] using framed⟩
  | escape address carriers after =>
      by_cases caught : (address.activation == activation.act) = true
      ·
        obtain ⟨changes, framed⟩ := finishChannels_storage layout activation.channels types carriers origin
          { after with activations := after.activations.filter (fun current => current.act != activation.act) }
        cases finishing : finishChannels layout activation.channels types carriers origin
            { after with activations := after.activations.filter (fun current => current.act != activation.act) } with
        | ok ignored final =>
            cases ignored
            exact ⟨changes, by simpa only [finishActivation, evaluated, caught, ↓reduceIte, finishing,
              Goose.Proofs.Exit.stepState] using framed⟩
        | stop reason final | escape address values final | jump target kind final =>
            exact ⟨changes, by simpa only [finishActivation, evaluated, caught, ↓reduceIte, finishing,
              Goose.Proofs.Exit.stepState] using framed⟩
      · simp only [finishActivation, evaluated, caught, ↓reduceIte, Goose.Proofs.Exit.stepState]
        exact ⟨[], .refl _⟩
  | stop reason after | jump target kind after =>
      simp only [finishActivation, evaluated, Goose.Proofs.Exit.stepState]
      exact ⟨[], .refl _⟩

theorem withScope_after_action_storage (environment : RuntimeActivation) (scope scopeInst : Nat)
    (action : EvalM α) (initial : ExecutionState) :
    (Goose.Proofs.Exit.stepState (withScope environment scope scopeInst action initial)).construction.storage =
      (Goose.Proofs.Exit.stepState (action initial)).construction.storage := by
  cases evaluated : action initial <;>
    simp only [withScope, evaluated, Goose.Construct.releaseScope, EvalM.get, EvalM.set, bind,
      Goose.Proofs.Exit.stepState, releaseScopeState]

theorem protectDestination_after_action_storage (origin : OriginId) (id : DestinationId)
    (action : EvalM α) :
    ∀ initial, ∃ changes, CleanupStorageTrace changes
      (Goose.Proofs.Exit.stepState (action initial)).construction.storage
      (Goose.Proofs.Exit.stepState (protectDestination origin id action initial)).construction.storage := by
  intro initial
  cases evaluated : action initial with
  | ok value after | stop reason after =>
      simp only [protectDestination, evaluated, Goose.Proofs.Exit.stepState]
      exact ⟨[], .refl _⟩
  | escape address carriers after =>
      obtain ⟨changes, framed⟩ := cleanupReceivingDestination_storage origin id carriers after
      cases cleaned : cleanupReceivingDestination origin id carriers after with
      | ok ignored final =>
          cases ignored
          exact ⟨changes, by simpa only [protectDestination, evaluated, cleaned,
            Goose.Proofs.Exit.stepState] using framed⟩
      | stop reason final | escape address values final | jump target kind final =>
          exact ⟨changes, by simpa only [protectDestination, evaluated, cleaned,
            Goose.Proofs.Exit.stepState] using framed⟩
  | jump target kind after =>
      cases kind with
      | breakValue carriers =>
          obtain ⟨changes, framed⟩ := cleanupReceivingDestination_storage origin id carriers after
          cases cleaned : cleanupReceivingDestination origin id carriers after with
          | ok ignored final =>
              cases ignored
              exact ⟨changes, by simpa only [protectDestination, evaluated, cleaned,
                Goose.Proofs.Exit.stepState] using framed⟩
          | stop reason final | escape address values final | jump next nextKind final =>
              exact ⟨changes, by simpa only [protectDestination, evaluated, cleaned,
                Goose.Proofs.Exit.stepState] using framed⟩
      | continueLoop =>
          obtain ⟨changes, framed⟩ := cleanupReceivingDestination_storage origin id [] after
          cases cleaned : cleanupReceivingDestination origin id [] after with
          | ok ignored final =>
              cases ignored
              exact ⟨changes, by simpa only [protectDestination, evaluated, cleaned,
                Goose.Proofs.Exit.stepState] using framed⟩
          | stop reason final | escape address values final | jump next nextKind final =>
              exact ⟨changes, by simpa only [protectDestination, evaluated, cleaned,
                Goose.Proofs.Exit.stepState] using framed⟩

theorem withBreakTarget_escape_storage (act : ActId) (scope : BreakScope) (channels : List Channel)
    (action : EvalM α) (receive : JumpKind → EvalM α) (initial after : ExecutionState)
    (address : ExitAddress) (carriers : List Goose.Construct.Carrier)
    (escaped : action { initial with nextScope := initial.nextScope + 1, breaks := ⟨initial.nextScope, act, scope, channels⟩ :: initial.breaks } = .escape address carriers after) :
    (Goose.Proofs.Exit.stepState
      (withBreakTarget act scope channels action receive initial)).construction.storage = after.construction.storage := by
  simp only [withBreakTarget, escaped, mapStepState, Goose.Proofs.Exit.stepState]

end Goose.Proofs.ExitExecution
