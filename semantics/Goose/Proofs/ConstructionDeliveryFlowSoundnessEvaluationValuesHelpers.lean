import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationContext
import Goose.Proofs.ConstructionDeliveryFlowSoundnessDispatch
import Goose.Proofs.ConstructionDeliveryFlowSoundnessHelpers
import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumpsRender
import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesRender
import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesOwners

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

elab "evaluation_values_intro" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isForall do throwError "expected callback"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro))

elab "evaluation_values_zeta" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``ControlFlowAction do throwError "expected control flow"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.isLet do throwError "expected local action binding"
  Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))

private theorem evaluation_values_readStoredMap (fuel : Nat) (layout : LayoutEnv) (stored : StoredValue)
    (indices : List Nat) :
    ControlFlowAction activation [normalFlow] (fun _ => normalFlow)
      (indices.mapM (readStoredElement fuel layout stored)) :=
  controlFlow_normal _
    (breakFrame_listMapM indices _ (fun index => breakFrame_readStoredElement fuel layout stored index))
    (neverJumps_listMapM indices _ (fun index => neverJumps_readStoredElement fuel layout stored index))

macro "evaluation_values_frame" : tactic => `(tactic|
  first
    | apply breakFrame_getDestination
    | apply breakFrame_getStorage
    | apply breakFrame_receivingLayout
    | apply breakFrame_storedDestination
    | apply breakFrame_receivingDestination
    | apply breakFrame_completedDestination
    | apply breakFrame_completedReceivingDestination
    | apply breakFrame_rootOf
    | apply breakFrame_sampledStored
    | apply breakFrame_storedPathRun
    | apply breakFrame_readStoredElement
    | apply breakFrame_readValuePath
    | apply breakFrame_readLoc
    | apply breakFrame_writeValuePath
    | apply breakFrame_writeLoc
    | apply breakFrame_newDestination
    | apply breakFrame_channelsFor
    | apply breakFrame_carrierValue
    | apply breakFrame_singleCarrier
    | apply breakFrame_publishCarriers
    | apply breakFrame_arrayLength
    | apply breakFrame_bindRoot
    | apply breakFrame_bindStaticRoot
    | apply breakFrame_setObjectOrdinal
    | apply breakFrame_reserveRootObject
    | apply breakFrame_freshScope
    | apply breakFrame_freshAct
    | apply breakFrame_emitStdout
    | apply breakFrame_expectInt
    | apply breakFrame_expectBool
    | apply breakFrame_expectRef
    | apply breakFrame_sameIntType
    | apply breakFrame_comparable
    | apply breakFrame_readRun
    | apply breakFrame_copyValue
    | apply breakFrame_deliverCarriers
    | apply breakFrame_repeatElement
    | apply breakFrame_cleanupDestination
    | apply breakFrame_cleanupReceivingDestination
    | apply breakFrame_prepareNamedCarrierAt
    | apply breakFrame_prepareNamedCarrier
    | apply breakFrame_materializeNamedCarriers
    | apply breakFrame_ownerDestination
    | apply breakFrame_publishOwner
    | apply breakFrame_openElementReceiving
    | apply breakFrame_publishElementReceiving
    | apply breakFrame_truncateOwner
    | apply breakFrame_appendFixedValues
    | apply breakFrame_appendRun
    | apply breakFrame_renderAny
    | apply breakFrame_renderElements
    | apply breakFrame_renderStored
    | apply breakFrame_renderView
    | apply breakFrame_getImplementation
    | apply breakFrame_liftExcept
    | apply breakFrame_liftLayout
    | exact breakFrame_pure _
    | exact breakFrame_stop _
    | exact breakFrame_get
    | apply breakFrame_liftConstruction)

macro "evaluation_values_noJump" : tactic => `(tactic|
  first
    | apply neverJumps_getDestination
    | apply neverJumps_getStorage
    | apply neverJumps_receivingLayout
    | apply neverJumps_storedDestination
    | apply neverJumps_receivingDestination
    | apply neverJumps_completedDestination
    | apply neverJumps_completedReceivingDestination
    | apply neverJumps_rootOf
    | apply neverJumps_sampledStored
    | apply neverJumps_storedPathRun
    | apply neverJumps_readStoredElement
    | apply neverJumps_readValuePath
    | apply neverJumps_readLoc
    | apply neverJumps_writeValuePath
    | apply neverJumps_writeLoc
    | apply neverJumps_newDestination
    | apply neverJumps_channelsFor
    | apply neverJumps_carrierValue
    | apply neverJumps_singleCarrier
    | apply neverJumps_publishCarriers
    | apply neverJumps_arrayLength
    | apply neverJumps_bindRoot
    | apply neverJumps_bindStaticRoot
    | apply neverJumps_setObjectOrdinal
    | apply neverJumps_reserveRootObject
    | apply neverJumps_freshScope
    | apply neverJumps_freshAct
    | apply neverJumps_emitStdout
    | apply neverJumps_expectInt
    | apply neverJumps_expectBool
    | apply neverJumps_expectRef
    | apply neverJumps_sameIntType
    | apply neverJumps_comparable
    | apply neverJumps_readRun
    | apply neverJumps_copyValue
    | apply neverJumps_deliverCarriers
    | apply neverJumps_repeatElement
    | apply neverJumps_cleanupDestination
    | apply neverJumps_cleanupReceivingDestination
    | apply neverJumps_prepareNamedCarrierAt
    | apply neverJumps_prepareNamedCarrier
    | apply neverJumps_materializeNamedCarriers
    | apply neverJumps_ownerDestination
    | apply neverJumps_publishOwner
    | apply neverJumps_openElementReceiving
    | apply neverJumps_publishElementReceiving
    | apply neverJumps_truncateOwner
    | apply neverJumps_appendFixedValues
    | apply neverJumps_appendRun
    | apply neverJumps_renderAny
    | apply neverJumps_renderElements
    | apply neverJumps_renderStored
    | apply neverJumps_renderView
    | apply neverJumps_getImplementation
    | apply neverJumps_liftExcept
    | apply neverJumps_liftLayout
    | exact neverJumps_pure _
    | exact neverJumps_stop _
    | exact neverJumps_get
    | apply neverJumps_lift)

macro "evaluation_values_leaf" : tactic => `(tactic|
  (apply controlFlow_normal <;> first | evaluation_values_frame | evaluation_values_noJump))

macro "evaluation_values_normal" : tactic => `(tactic|
  repeat' first
    | exact evaluation_values_readStoredMap _ _ _ _
    | (solve | evaluation_values_leaf)
    | exact controlFlow_pure [normalFlow] (fun _ => normalFlow) _ (List.mem_singleton_self _)
    | exact controlFlow_stop [normalFlow] (fun _ => normalFlow) _
    | (with_reducible apply controlFlow_prefix)
    | evaluation_values_zeta
    | evaluation_values_intro
    | split)

end Goose.Proofs.ConstructionDelivery
