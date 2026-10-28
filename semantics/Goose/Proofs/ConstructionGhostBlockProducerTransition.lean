import Goose.Proofs.ConstructionGhostBlockValueChannels

namespace Goose.Proofs.ConstructionGhostBlockProducerTransition
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

def prepareBlockProducerChannels (channels : List Channel) (origin : Goose.Core.OriginId) : EvalM (List Channel) :=
  channels.mapM fun channel => match channel with
    | .register ty => pure (.register ty)
    | .construct destination => do pure (.construct (← liftConstruction origin (renewReceivingDestination destination)))
    | .completion token => pure (.completion token)

def blockProducerStart (environment : RuntimeActivation) (channels : List Channel) (before : ExecutionState) : ExecutionState :=
  let target : BreakTarget := ⟨before.nextScope, environment.act, .block, channels⟩
  { before with nextScope := before.nextScope + 1, breaks := target :: before.breaks }

theorem blockProducer_afterChannels (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (block : Block) (origin : Goose.Core.OriginId) (channels planned : List Channel) (before ready : ExecutionState)
    (prepared : prepareBlockProducerChannels channels origin before = .ok planned ready) :
    evalProduce (fuel + 1) config environment channels (.blockE block origin) before =
      withBreakTarget environment.act .block planned
        (do let (flow, carriers) ← execResultBlock fuel config environment planned block
            match flow with
            | .normal _ => pure carriers
            | _ => fault .flow)
        (fun kind => do
          match kind with
          | .breakValue carriers => landCarriersInto origin planned carriers; pure carriers
          | .continueLoop => fault .flow) ready := by
  simp only [evalProduce, expressionOrigin, bind]
  change (prepareBlockProducerChannels channels origin >>= fun planned =>
    withBreakTarget environment.act .block planned
      (do let (flow, carriers) ← execResultBlock fuel config environment planned block
          match flow with
          | .normal _ => pure carriers
          | _ => fault .flow)
      (fun kind => do
        match kind with
        | .breakValue carriers => landCarriersInto origin planned carriers; pure carriers
        | .continueLoop => fault .flow)) before = _
  simp only [bind, prepared]

theorem withBlockTarget_resultPrefix (environment : RuntimeActivation) (channels : List Channel)
    (action : EvalM α) (receive : JumpKind → EvalM α) (before : ExecutionState)
    (received : ∀ kind, PreservesConstructionInvariant
      (PrefixInvariant (Goose.Proofs.Exit.stepState (action (blockProducerStart environment channels before))).construction.events) (receive kind)) :
    EventPrefix (Goose.Proofs.Exit.stepState (action (blockProducerStart environment channels before))).construction.events
      (Goose.Proofs.Exit.stepState (withBreakTarget environment.act .block channels action receive before)).construction.events := by
  cases result : action (blockProducerStart environment channels before) with
  | ok value state =>
      simp only [blockProducerStart] at result
      simp [withBreakTarget, result, mapStepState, Goose.Proofs.Exit.stepState, eventPrefix_refl]
  | stop reason state =>
      simp only [blockProducerStart] at result
      simp [withBreakTarget, result, mapStepState, Goose.Proofs.Exit.stepState, eventPrefix_refl]
  | escape address carriers state =>
      simp only [blockProducerStart] at result
      simp [withBreakTarget, result, mapStepState, Goose.Proofs.Exit.stepState, eventPrefix_refl]
  | jump target kind state =>
      simp only [blockProducerStart] at result received
      rw [result] at received
      by_cases caught : target = before.nextScope
      · subst target
        apply (eventPrefix_iff_isPrefix _ _).mpr
        have kept := received kind { state with breaks := state.breaks.filter (fun entry => entry.id != before.nextScope) }
          (by simpa [Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using (List.prefix_rfl : state.construction.events <+: state.construction.events))
        simpa [withBreakTarget, result, mapStepState, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant] using kept
      · simp [withBreakTarget, result, mapStepState, caught, Goose.Proofs.Exit.stepState, eventPrefix_refl]

theorem blockProducer_resultBlockPrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (block : Block) (origin : Goose.Core.OriginId) (channels planned : List Channel) (before ready : ExecutionState)
    (prepared : prepareBlockProducerChannels channels origin before = .ok planned ready) :
    EventPrefix (Goose.Proofs.Exit.stepState (execResultBlock fuel config environment planned block
      (blockProducerStart environment planned ready))).construction.events
      (Goose.Proofs.Exit.stepState (evalProduce (fuel + 1) config environment channels (.blockE block origin) before)).construction.events := by
  rw [blockProducer_afterChannels fuel config environment block origin channels planned before ready prepared]
  let action : EvalM (List Carrier) := do
    let (flow, carriers) ← execResultBlock fuel config environment planned block
    match flow with
    | .normal _ => pure carriers
    | _ => fault .flow
  let receive : JumpKind → EvalM (List Carrier) := fun kind => do
    match kind with
    | .breakValue carriers => landCarriersInto origin planned carriers; pure carriers
    | .continueLoop => fault .flow
  have same : (Goose.Proofs.Exit.stepState (action (blockProducerStart environment planned ready))).construction.events =
      (Goose.Proofs.Exit.stepState (execResultBlock fuel config environment planned block
        (blockProducerStart environment planned ready))).construction.events := by
    simp only [action, bind]
    cases execResultBlock fuel config environment planned block (blockProducerStart environment planned ready) with
    | ok pair state => cases pair with | mk flow carriers => cases flow <;> rfl
    | stop | escape | jump => rfl
  have received : ∀ kind, PreservesConstructionInvariant
      (PrefixInvariant (Goose.Proofs.Exit.stepState (action (blockProducerStart environment planned ready))).construction.events) (receive kind) := by
    intro kind
    cases kind with
    | breakValue carriers =>
        apply preservesConstructionInvariant_bind
        · exact preservesConstructionInvariant_landCarriersInto _ _ _
        · intro ignored; exact preservesConstructionInvariant_pure _
    | continueLoop => exact preservesConstructionInvariant_fault _
  have kept := withBlockTarget_resultPrefix environment planned action receive ready received
  rw [same] at kept
  exact kept

#print axioms blockProducer_resultBlockPrefix
#print axioms withBlockTarget_resultPrefix
#print axioms blockProducer_afterChannels
end Goose.Proofs.ConstructionGhostBlockProducerTransition
