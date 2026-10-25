import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesExtension
import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesOwners
import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesRender
import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesCleanup
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesContext
import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesCopy
import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesActivation

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem breakFrame_materializedDestination (fuel : Nat) (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (origin : Goose.Core.OriginId) (count : Nat) (value : Value) :
    BreakFrameAction (materializedDestination fuel layout owner ty origin count value) := by
  unfold materializedDestination
  apply breakFrame_bind
  · exact breakFrame_newDestination _ _ _ _ _ _ _
  · intro destination
    apply breakFrame_bind
    · exact breakFrame_copyValue _ _ _ _ _ _
    · intro _; exact breakFrame_completedReceivingDestination _

theorem breakFrame_constructLocal (declarations : DeclarationEnv) (owner : Goose.Core.ActId) (ty : Ty)
    (origin : Goose.Core.OriginId) (expression : Expr) (construct : Goose.Core.DestinationId → EvalM Unit)
    (body : ∀ destination, BreakFrameAction (construct destination)) :
    BreakFrameAction (constructLocal declarations owner ty origin expression construct) := by
  unfold constructLocal
  apply breakFrame_bind
  · exact breakFrame_newDestination _ _ _ _ _ _ _
  · intro destination
    apply breakFrame_bind
    · exact body destination
    · intro _
      apply breakFrame_bind
      · exact breakFrame_completedReceivingDestination _
      · intro completed
        apply breakFrame_bind
        · exact breakFrame_publishCarriers _ _
        · intro _; exact breakFrame_pure _

private theorem breakFrame_fault (kind : Goose.Core.FaultKind) :
    BreakFrameAction (fault (α := α) kind) := by
  intro state _
  exact BreakStackFrame.refl state

private theorem breakFrame_timeout : BreakFrameAction (timeout (α := α)) := by
  intro state _
  exact BreakStackFrame.refl state

private theorem breakFrame_abortAt (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId) :
    BreakFrameAction (abortAt (α := α) kind origin) := by
  intro state _
  exact BreakStackFrame.refl state

elab "evaluation_frame_head " previous:ident : tactic => do
  let target := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  if target.isForall then
    Lean.Elab.Tactic.evalTactic (← `(tactic| intro))
    return
  unless target.getAppFn.isConstOf ``BreakFrameAction do throwError "expected break frame"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  let action := action.consumeMData
  if action.isLet then
    Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))
    return
  let some name := action.getAppFn.constName? | throwError "expected named action"
  let key := (name.toString.splitOn ".").getLast!
  match key with
  | "evalValue" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).value))
  | "evalBound" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).bound))
  | "evalPlace" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).place))
  | "evalView" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).view))
  | "evalProduce" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).produce))
  | "evalOperands" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).operands))
  | "buildExpr" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).build))
  | "buildElement" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).element))
  | "evalArguments" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).arguments))
  | "invokeCall" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).call))
  | "enterActivation" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).activation))
  | "execActivationBody" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).activationBody))
  | "execResultBlock" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).resultBlock))
  | "execResultBlockWith" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).resultBlockWith))
  | "execBlock" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).block))
  | "execStmts" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).statements))
  | "execStmt" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).statement))
  | "evalPrintArg" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).printArgument))
  | "execWhile" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).whileLoop))
  | "execRange" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).rangeLoop))
  | "execEach" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).eachLoop))
  | "loopBody" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).loop))
  | "pushValue" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply ($previous).push))
  | "pure" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_pure))
  | "stop" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_stop))
  | "get" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_get))
  | "freshScope" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_freshScope))
  | "freshAct" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_freshAct))
  | "getDestination" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_getDestination))
  | "getStorage" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_getStorage))
  | "storedDestination" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply breakFrame_storedDestination))
  | "receivingDestination" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_receivingDestination))
  | "completedDestination" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_completedDestination))
  | "completedReceivingDestination" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_completedReceivingDestination))
  | "rootOf" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_rootOf))
  | "currentBreak" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_currentBreak))
  | "sampledStored" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_sampledStored))
  | "arrayLength" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_arrayLength))
  | "liftExcept" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_liftExcept))
  | "liftLayout" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_liftLayout))
  | "liftConstruction" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_liftConstruction))
  | "expectInt" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_expectInt))
  | "expectBool" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_expectBool))
  | "expectRef" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_expectRef))
  | "sameIntType" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_sameIntType))
  | "comparable" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_comparable))
  | "receivingLayout" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_receivingLayout))
  | "receivingAction" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_receivingAction))
  | "landCarriersInto" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_landCarriersInto))
  | "readStoredElement" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_readStoredElement))
  | "readLoc" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_readLoc))
  | "bindRoot" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_bindRoot))
  | "bindStaticRoot" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_bindStaticRoot))
  | "singleCarrier" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_singleCarrier))
  | "carrierValue" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_carrierValue))
  | "publishCarriers" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_publishCarriers))
  | "newDestination" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_newDestination))
  | "channelsFor" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_channelsFor))
  | "bindAll" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_bindAll))
  | "emitStdout" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_emitStdout))
  | "getImplementation" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_getImplementation))
  | "enclosingActivation" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_enclosingActivation))
  | "targetActivation" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_targetActivation))
  | "selectCompletionChannel" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_selectCompletionChannel))
  | "exitSource" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_exitSource))
  | "exitChannels" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_exitChannels))
  | "materializeOwnedCarriers" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_materializeOwnedCarriers))
  | "copyValue" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_copyValue))
  | "deliverCarriers" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_deliverCarriers))
  | "ownerDestination" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_ownerDestination))
  | "publishOwner" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_publishOwner))
  | "openElementReceiving" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_openElementReceiving))
  | "publishElementReceiving" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_publishElementReceiving))
  | "repeatElement" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_repeatElement))
  | "truncateOwner" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_truncateOwner))
  | "appendFixedValues" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_appendFixedValues))
  | "appendRun" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_appendRun))
  | "writeLoc" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_writeLoc))
  | "readRun" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_readRun))
  | "renderAny" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_renderAny))
  | "renderView" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_renderView))
  | "prepareNamedCarrierAt" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_prepareNamedCarrierAt))
  | "prepareNamedCarrier" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_prepareNamedCarrier))
  | "materializeNamedCarriers" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_materializeNamedCarriers))
  | "materializedDestination" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_materializedDestination))
  | "returned" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_returned))
  | "escaped" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_escaped))
  | "jump" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_jump))
  | "constructLocal" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_constructLocal))
  | "withOwnerExtension" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_withOwnerExtension))
  | "protectDestination" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_protectDestination))
  | "finishActivation" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_finishActivation))
  | "execResultScope" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_execResultScope))
  | "withScope" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_withScope))
  | "withBreakTarget" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_withBreakTarget))
  | "withCompletionChannels" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_withCompletionChannels))
  | "withExitChannels" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_withExitChannels))
  | "materializeProducer" => Lean.Elab.Tactic.evalTactic (← `(tactic| with_reducible apply breakFrame_materializeProducer))
  | "fault" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply breakFrame_fault))
  | "timeout" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply breakFrame_timeout))
  | "abortAt" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply breakFrame_abortAt))
  | "ite" => Lean.Elab.Tactic.evalTactic (← `(tactic| split))
  | "mapM" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply breakFrame_listMapM))
  | "forIn" => Lean.Elab.Tactic.evalTactic (← `(tactic|
      first | apply breakFrame_listForIn | apply breakFrame_arrayForIn | apply breakFrame_rangeForIn))
  | "bind" =>
      let bindArguments := action.getAppArgs
      let some bound := bindArguments[bindArguments.size - 2]? | throwError "expected bound action"
      let boundKey := bound.getAppFn.constName?.map (fun n => (n.toString.splitOn ".").getLast!)
      match boundKey with
      | some "fault" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply breakFrame_fault_bind))
      | some "timeout" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply breakFrame_timeout_bind))
      | some "abortAt" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply breakFrame_abortAt_bind))
      | some "get" => Lean.Elab.Tactic.evalTactic (← `(tactic|
          first | apply breakFrame_allocateActivation | apply breakFrame_mapActivations | apply breakFrame_bind))
      | _ => Lean.Elab.Tactic.evalTactic (← `(tactic| apply breakFrame_bind))
  | _ => throwError "unrecognized frame action {name}"

syntax "evaluation_frame " ident : tactic
macro_rules
  | `(tactic| evaluation_frame $previous:ident) => `(tactic|
      repeat' first
        | assumption
        | evaluation_frame_head $previous
        | evaluation_frame_conditional
        | evaluation_frame_zeta
        | evaluation_frame_intro
        | split)

end Goose.Proofs.ConstructionDelivery
