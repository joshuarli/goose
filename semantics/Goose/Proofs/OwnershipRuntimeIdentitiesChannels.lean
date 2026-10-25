import Goose.Proofs.OwnershipRuntimeIdentitiesActions

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership

open Goose.Construct
open Goose.Proofs.ExitExecution

theorem preservesOwnershipBreakIdentities_landCarrier (origin : Goose.Core.OriginId) (carrier : Carrier) :
    PreservesOwnershipBreakIdentities (landCarrier origin carrier) := by
  unfold landCarrier
  cases carrier with
  | register value => exact preservesOwnershipBreakIdentities_pure _
  | pendingNamed token => exact preservesOwnershipBreakIdentities_stop _
  | completed id =>
      apply preservesOwnershipBreakIdentities_bind
      · exact stateQuery_preservesOwnershipBreakIdentities _ (stateQuery_getDestination id)
      · intro destination
        cases destination.use with
        | replacement old => exact preservesOwnershipBreakIdentities_lift _ _
        | receiver | child parent => exact preservesOwnershipBreakIdentities_pure _

theorem preservesOwnershipBreakIdentities_landCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    PreservesOwnershipBreakIdentities (landCarriers origin carriers) := by
  unfold landCarriers
  apply preservesOwnershipBreakIdentities_bind
  · apply preservesOwnershipBreakIdentities_listForIn
    intro carrier _
    apply preservesOwnershipBreakIdentities_bind
    · exact preservesOwnershipBreakIdentities_landCarrier origin carrier
    · intro _; exact preservesOwnershipBreakIdentities_pure _
  · intro _; exact preservesOwnershipBreakIdentities_pure _

theorem preservesOwnershipBreakIdentities_receivingDestination (id : Goose.Core.DestinationId) :
    PreservesOwnershipBreakIdentities (receivingDestination id) := by
  exact preservesOwnershipBreakIdentities_lift _ _

private def completionLanding (origin : Goose.Core.OriginId) (token : ExitReservationId)
    (replacement : Goose.Core.DestinationId) : EvalM (ForInStep PUnit) := do
  let some (.active _ _ selected _) := (← EvalM.get).construction.exitReservations[token]? | fault .flow
  let receiving ← receivingDestination selected
  if receiving != replacement then
    liftConstruction origin (landExitReplacementInto receiving replacement)
  pure (.yield PUnit.unit)

private theorem preservesOwnershipBreakIdentities_completionLanding (origin : Goose.Core.OriginId)
    (token : ExitReservationId) (replacement : Goose.Core.DestinationId) :
    PreservesOwnershipBreakIdentities (completionLanding origin token replacement) := by
  unfold completionLanding
  apply preservesOwnershipBreakIdentities_bind
  · exact preservesOwnershipBreakIdentities_get
  · intro state
    cases found : state.construction.exitReservations[token]? with
    | none => exact preservesOwnershipBreakIdentities_stop (.fault .flow)
    | some reservation =>
        cases reservation with
        | waiting incoming => exact preservesOwnershipBreakIdentities_stop (.fault .flow)
        | active role incoming selected snapshot =>
            apply preservesOwnershipBreakIdentities_bind
            · exact preservesOwnershipBreakIdentities_receivingDestination selected
            · intro receiving
              cases changed : (receiving != replacement) with
              | false => simp; exact preservesOwnershipBreakIdentities_pure _
              | true =>
                  simp
                  apply preservesOwnershipBreakIdentities_bind
                  · exact preservesOwnershipBreakIdentities_lift _ _
                  · intro _; exact preservesOwnershipBreakIdentities_pure _
        | restored | released => exact preservesOwnershipBreakIdentities_stop (.fault .flow)

theorem preservesOwnershipBreakIdentities_landCarriersInto (origin : Goose.Core.OriginId) (channels : List Channel)
    (carriers : List Carrier) : PreservesOwnershipBreakIdentities (landCarriersInto origin channels carriers) := by
  unfold landCarriersInto
  split
  · exact preservesOwnershipBreakIdentities_stop _
  · simp only [bind]
    apply preservesOwnershipBreakIdentities_bind
    · apply preservesOwnershipBreakIdentities_listForIn
      intro item _
      cases item with
      | mk channel carrier =>
          simp only
          cases channel with
          | register ty =>
              cases carrier with
              | register value => exact preservesOwnershipBreakIdentities_pure _
              | completed id | pendingNamed _ => exact preservesOwnershipBreakIdentities_stop _
          | construct incoming =>
              cases carrier with
              | register value | pendingNamed _ => exact preservesOwnershipBreakIdentities_stop _
              | completed replacement =>
                  simp only
                  apply preservesOwnershipBreakIdentities_bind
                  · exact preservesOwnershipBreakIdentities_receivingDestination incoming
                  · intro current
                    cases changed : (current != replacement) with
                    | false =>
                        simp
                        exact preservesOwnershipBreakIdentities_pure _
                    | true =>
                        simp
                        apply preservesOwnershipBreakIdentities_bind
                        · exact preservesOwnershipBreakIdentities_lift _ _
                        · intro _; exact preservesOwnershipBreakIdentities_pure _
          | completion token =>
              cases carrier with
              | register value => exact preservesOwnershipBreakIdentities_stop _
              | pendingNamed pending =>
                  cases mismatch : (token != pending) with
                  | false => simp [mismatch]; exact preservesOwnershipBreakIdentities_pure _
                  | true => simp [mismatch]; exact preservesOwnershipBreakIdentities_stop _
              | completed replacement =>
                  change PreservesOwnershipBreakIdentities (completionLanding origin token replacement)
                  exact preservesOwnershipBreakIdentities_completionLanding origin token replacement
    · intro _; exact preservesOwnershipBreakIdentities_pure _

theorem preservesOwnershipBreakIdentities_finishChannel (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (carrier : Carrier) (result : Ty) : PreservesOwnershipBreakIdentities (finishChannel layout origin carrier result) := by
  unfold finishChannel
  cases carrier with
  | register value => exact preservesOwnershipBreakIdentities_pure _
  | pendingNamed token => exact preservesOwnershipBreakIdentities_stop _
  | completed id =>
      apply preservesOwnershipBreakIdentities_bind
      · exact stateQuery_preservesOwnershipBreakIdentities _ (stateQuery_getDestination id)
      · intro destination
        simp only
        split
        · exact preservesOwnershipBreakIdentities_lift _ _
        · split <;> split
          all_goals
            first
              | exact preservesOwnershipBreakIdentities_lift _ _
              | (apply preservesOwnershipBreakIdentities_bind
                 · exact preservesOwnershipBreakIdentities_lift _ _
                 · intro _
                   apply preservesOwnershipBreakIdentities_bind
                   · exact stateQuery_preservesOwnershipBreakIdentities _ (stateQuery_receivingLayout layout destination.capability.layout)
                   · intro receiving
                     apply preservesOwnershipBreakIdentities_bind
                     · exact preservesOwnershipBreakIdentities_lift _ _
                     · intro _; exact preservesOwnershipBreakIdentities_lift _ _)

theorem preservesOwnershipBreakIdentities_finishChannels (layout : LayoutEnv) (channels : List Channel) (types : List Ty)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    PreservesOwnershipBreakIdentities (finishChannels layout channels types carriers origin) := by
  unfold finishChannels
  apply preservesOwnershipBreakIdentities_bind
  · exact preservesOwnershipBreakIdentities_landCarriersInto origin channels carriers
  · intro _
    split
    · exact preservesOwnershipBreakIdentities_stop _
    · apply preservesOwnershipBreakIdentities_bind
      · apply preservesOwnershipBreakIdentities_listForIn
        intro item _
        rcases item with ⟨carrier, result⟩
        apply preservesOwnershipBreakIdentities_bind
        · exact preservesOwnershipBreakIdentities_finishChannel layout origin carrier result
        · intro _; exact preservesOwnershipBreakIdentities_pure _
      · intro _; exact preservesOwnershipBreakIdentities_pure _


end Goose.Proofs.ConstructionExecutionOwnership
