import Goose.Proofs.ExitExecutionActivationChannelsHelpers
import Goose.Proofs.ConstructionDeliveryFlowSoundnessCalls

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionDelivery
open Goose.Proofs.ConstructionExecutionOwnership

private theorem filtersActivationChannels_finishActivation (config : EvalConfig) (layout : LayoutEnv)
    (activation : RuntimeActivation) (resultTypes : List Ty) (origin : Goose.Core.OriginId)
    (action : EvalM (List Carrier))
    (actionChannels : PreservesActivationChannels action) (actionFresh : PreservesFresh action) :
    FiltersActivationChannels activation (finishActivation layout activation resultTypes origin action) := by
  intro state fresh
  have channels := actionChannels state fresh
  have freshAfter := actionFresh state fresh
  cases result : action state with
  | stop reason middle =>
      simp [finishActivation, result]
  | jump target kind middle =>
      simp [finishActivation, result]
  | ok carriers middle =>
      have middleChannels : ActivationChannelsProjection middle = ActivationChannelsProjection state := by
        simpa [ActivationChannelsOutcome, result] using channels
      have middleFresh : FreshActivations middle := by
        simpa [Goose.Proofs.Exit.stepState, result] using freshAfter
      let trimmed : ExecutionState := { middle with
        activations := middle.activations.filter (fun current => current.act != activation.act) }
      have trimmedChannels : ActivationChannelsProjection trimmed =
          (ActivationChannelsProjection state).filter (fun current => current.act != activation.act) := by
        rw [activationChannelsProjection_filter, middleChannels]
      have trimmedFresh : FreshActivations trimmed := by
        exact fresh_activation_filter middle _ middleFresh
      have finishedChannels := preservesActivationChannels_finishChannels config layout
        activation.channels resultTypes carriers origin trimmed trimmedFresh
      cases finished : finishChannels layout activation.channels resultTypes carriers origin trimmed with
      | stop reason final =>
          simp [finishActivation, result, trimmed, finished]
      | ok value final =>
          have finalChannels : ActivationChannelsProjection final = ActivationChannelsProjection trimmed := by
            simpa [ActivationChannelsOutcome, finished] using finishedChannels
          have actual : finishActivation layout activation resultTypes origin action state = .ok carriers final := by
            simp [finishActivation, result, trimmed, finished]
          simp only [actual]
          exact finalChannels.trans trimmedChannels
      | escape target value final =>
          have finalChannels : ActivationChannelsProjection final = ActivationChannelsProjection trimmed := by
            simpa [ActivationChannelsOutcome, finished] using finishedChannels
          have actual : finishActivation layout activation resultTypes origin action state = .escape target value final := by
            simp [finishActivation, result, trimmed, finished]
          simp only [actual]
          exact finalChannels.trans trimmedChannels
      | jump target kind final =>
          have actual : finishActivation layout activation resultTypes origin action state = .jump target kind final := by
            simp [finishActivation, result, trimmed, finished]
          exact False.elim ((finishActivation_no_jump layout activation resultTypes origin action state target kind final) actual)
  | escape target carriers middle =>
      have middleChannels : ActivationChannelsProjection middle = ActivationChannelsProjection state := by
        simpa [ActivationChannelsOutcome, result] using channels
      have middleFresh : FreshActivations middle := by
        simpa [Goose.Proofs.Exit.stepState, result] using freshAfter
      by_cases caught : target.activation = activation.act
      · let trimmed : ExecutionState := { middle with
          activations := middle.activations.filter (fun current => current.act != activation.act) }
        have trimmedChannels : ActivationChannelsProjection trimmed =
            (ActivationChannelsProjection state).filter (fun current => current.act != activation.act) := by
          rw [activationChannelsProjection_filter, middleChannels]
        have trimmedFresh : FreshActivations trimmed := by
          exact fresh_activation_filter middle _ middleFresh
        have finishedChannels := preservesActivationChannels_finishChannels config layout
          activation.channels resultTypes carriers origin trimmed trimmedFresh
        cases finished : finishChannels layout activation.channels resultTypes carriers origin trimmed with
        | stop reason final =>
            simp [finishActivation, result, caught, trimmed, finished]
        | ok value final =>
            have finalChannels : ActivationChannelsProjection final = ActivationChannelsProjection trimmed := by
              simpa [ActivationChannelsOutcome, finished] using finishedChannels
            have actual : finishActivation layout activation resultTypes origin action state = .ok carriers final := by
              simp [finishActivation, result, caught, trimmed, finished]
            simp only [actual]
            exact finalChannels.trans trimmedChannels
        | escape address value final =>
            have finalChannels : ActivationChannelsProjection final = ActivationChannelsProjection trimmed := by
              simpa [ActivationChannelsOutcome, finished] using finishedChannels
            have actual : finishActivation layout activation resultTypes origin action state = .escape address value final := by
              simp [finishActivation, result, caught, trimmed, finished]
            simp only [actual]
            exact finalChannels.trans trimmedChannels
        | jump jumpTarget jumpKind final =>
            have actual : finishActivation layout activation resultTypes origin action state = .jump jumpTarget jumpKind final := by
              simp [finishActivation, result, caught, trimmed, finished]
            exact False.elim ((finishActivation_no_jump layout activation resultTypes origin action state jumpTarget jumpKind final) actual)
      · have filteredChannels : ActivationChannelsProjection
            { middle with activations := middle.activations.filter (fun current => current.act != activation.act) } =
            (ActivationChannelsProjection state).filter (fun current => current.act != activation.act) := by
          rw [activationChannelsProjection_filter, middleChannels]
        have actual : finishActivation layout activation resultTypes origin action state =
            .escape target carriers { middle with
              activations := middle.activations.filter (fun current => current.act != activation.act) } := by
          simp [finishActivation, result, caught]
        simp only [actual]
        exact filteredChannels

theorem enterActivation_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) (origin : Goose.Core.OriginId) :
    FiltersActivationChannels environment
      (enterActivation (fuel + 1) config environment pre body origin) := by
  simp only [enterActivation]
  cases implementationFound : config.module.impls[environment.implementation]? with
  | none =>
      intro state fresh
      simp [fault, EvalM.stop]
  | some implementation =>
      exact filtersActivationChannels_finishActivation config config.layout environment
        (implementation.results.toList.map (·.ty)) origin
        (execActivationBody fuel config environment pre body)
        (previous.activationBody environment pre body)
        (previousFresh.activationBody environment pre body)

private theorem activationChannelsProjection_push (state : ExecutionState)
    (activation : RuntimeActivation) :
    ActivationChannelsProjection { state with activations := activation :: state.activations } =
      ownershipActivationChannels activation :: ActivationChannelsProjection state := by
  rfl

theorem preservesActivationChannels_freshPushFilter (make : Goose.Core.ActId → RuntimeActivation)
    (identifier : ∀ act, (make act).act = act) (enter : RuntimeActivation → EvalM α)
    (continuation : α → EvalM β)
    (filters : ∀ activation, FiltersActivationChannels activation (enter activation))
    (entersFresh : ∀ activation, PreservesFresh (enter activation))
    (continues : ∀ value, PreservesActivationChannels (continuation value))
    :
    PreservesActivationChannels (do
      let act ← freshAct
      let activation := make act
      let state ← EvalM.get
      EvalM.set { state with activations := activation :: state.activations }
      let value ← enter activation
      continuation value) := by
  intro state fresh
  have pushedFresh := fresh_activation_push state (make state.nextAct) fresh (identifier state.nextAct)
  let pushed : ExecutionState := { state with nextAct := state.nextAct + 1, activations := make state.nextAct :: state.activations }
  have projectionPushed : ActivationChannelsProjection pushed =
      ownershipActivationChannels (make state.nextAct) :: ActivationChannelsProjection state := by
    exact activationChannelsProjection_push { state with nextAct := state.nextAct + 1 } (make state.nextAct)
  have activationChannelId : (ownershipActivationChannels (make state.nextAct)).act = state.nextAct := by
    simp [ownershipActivationChannels, identifier]
  have enteredFresh := entersFresh (make state.nextAct) pushed pushedFresh
  have enteredChannels := filters (make state.nextAct) pushed pushedFresh
  cases entered : enter (make state.nextAct) pushed with
  | stop reason final =>
      simp [ActivationChannelsOutcome, freshAct, EvalM.get, EvalM.set, bind, pure, pushed, entered]
  | jump target kind final =>
      simp only [entered] at enteredChannels
  | escape address value final =>
      have finalChannels : ActivationChannelsProjection final =
          (ActivationChannelsProjection pushed).filter (fun current => current.act != (make state.nextAct).act) := by
        simpa [FiltersActivationChannels, entered] using enteredChannels
      have noCollision : ∀ current ∈ state.activations, current.act != state.nextAct := by
        intro current member
        have unequal : current.act ≠ state.nextAct := Nat.ne_of_lt (fresh.2 current member)
        simp [unequal]
      have filteredPush :
          (ActivationChannelsProjection pushed).filter (fun current => current.act != state.nextAct) =
            ActivationChannelsProjection state := by
        rw [projectionPushed]
        simp [ownershipActivationChannels, identifier]
        intro channels member
        obtain ⟨current, currentMember, projectionEqual⟩ := List.mem_map.mp member
        have unequal : current.act ≠ state.nextAct := by
          simpa using noCollision current currentMember
        have projectionAct : current.act = channels.act := by
          simpa [ownershipActivationChannels] using congrArg OwnershipActivationChannels.act projectionEqual
        rw [← projectionAct]
        exact unequal
      have filteredPushActivation :
          (ActivationChannelsProjection pushed).filter (fun current => current.act != (make state.nextAct).act) =
            ActivationChannelsProjection state := by
        simpa only [identifier] using filteredPush
      simp only [ActivationChannelsOutcome, freshAct_result, bind, EvalM.get, EvalM.set, pushed, entered]
      exact finalChannels.trans filteredPushActivation
  | ok value final =>
      have finalFresh : FreshActivations final := by
        simpa [Goose.Proofs.Exit.stepState, entered] using enteredFresh
      have finalChannels : ActivationChannelsProjection final =
          (ActivationChannelsProjection pushed).filter (fun current => current.act != (make state.nextAct).act) := by
        simpa [FiltersActivationChannels, entered] using enteredChannels
      have noCollision : ∀ current ∈ state.activations, current.act != state.nextAct := by
        intro current member
        have unequal : current.act ≠ state.nextAct := Nat.ne_of_lt (fresh.2 current member)
        simp [unequal]
      have filteredPush :
          (ActivationChannelsProjection pushed).filter (fun current => current.act != state.nextAct) =
            ActivationChannelsProjection state := by
        rw [projectionPushed]
        simp [ownershipActivationChannels, identifier]
        intro channels member
        obtain ⟨current, currentMember, projectionEqual⟩ := List.mem_map.mp member
        have unequal : current.act ≠ state.nextAct := by
          simpa using noCollision current currentMember
        have projectionAct : current.act = channels.act := by
          simpa [ownershipActivationChannels] using congrArg OwnershipActivationChannels.act projectionEqual
        rw [← projectionAct]
        exact unequal
      have continuedChannels := continues value final finalFresh
      cases continued : continuation value final with
      | stop reason after => simp [ActivationChannelsOutcome, freshAct, EvalM.get, EvalM.set, bind, pure, pushed, entered, continued]
      | ok output after | escape address output after | jump target kind after =>
          have continuedProjection : ActivationChannelsProjection after = ActivationChannelsProjection final := by
            simpa [ActivationChannelsOutcome, continued] using continuedChannels
          have filteredPushActivation :
              (ActivationChannelsProjection pushed).filter (fun current => current.act != (make state.nextAct).act) =
                ActivationChannelsProjection state := by
            simpa only [identifier] using filteredPush
          simp only [ActivationChannelsOutcome, freshAct_result, bind, EvalM.get, EvalM.set, pushed, entered, continued]
          exact continuedProjection.trans (finalChannels.trans filteredPushActivation)

end Goose.Proofs.ExitExecution
