import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumpsExtension
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationFramesHelpers
import Goose.Proofs.ConstructionDeliveryFlowSoundnessTargets

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

local elab "noJump_conditional" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``NeverJumps do throwError "expected jump exclusion"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.getAppFn.isConstOf ``ite do throwError "expected conditional action"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply neverJumps_conditional))

local elab "noJump_intro" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isForall do throwError "expected callback"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro))

local elab "noJump_zeta" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``NeverJumps do throwError "expected jump exclusion"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.isLet do throwError "expected local action binding"
  Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))

local macro "noJump_runtime_step" : tactic => `(tactic|
  first
    | exact neverJumps_pure _
    | exact neverJumps_stop _
    | exact neverJumps_get
    | exact neverJumps_set _
    | exact neverJumps_rootOf _ _
    | exact neverJumps_getDestination _
    | exact neverJumps_getStorage _
    | exact neverJumps_receivingLayout _ _
    | exact neverJumps_liftExcept _
    | exact neverJumps_liftLayout _
    | (with_reducible apply neverJumps_lift)
    | (with_reducible apply neverJumps_bind)
    | (with_reducible apply neverJumps_forIn)
    | (with_reducible apply neverJumps_listMapM)
    | noJump_conditional
    | noJump_zeta
    | noJump_intro
    | split
    | unfold receivingDestination)

local macro "noJump_runtime" : tactic => `(tactic| repeat' noJump_runtime_step)

theorem neverJumps_getImplementation (config : EvalConfig) (context : Goose.Core.ContextId) : NeverJumps (getImplementation config context) := by
  unfold getImplementation
  repeat' first
    | exact neverJumps_exitSource _ _ _
    | noJump_runtime_step

theorem neverJumps_enclosingActivation (environment : RuntimeActivation) : NeverJumps (enclosingActivation environment) := by
  unfold enclosingActivation
  repeat' first
    | exact neverJumps_exitSource _ _ _
    | noJump_runtime_step

theorem neverJumps_targetActivation (config : EvalConfig) (target : Nat) : NeverJumps (targetActivation config target) := by
  unfold targetActivation
  repeat' first
    | exact neverJumps_exitSource _ _ _
    | noJump_runtime_step

theorem neverJumps_exitSource (source : RuntimeActivation) (incoming : Goose.Core.DestinationId) (operand : Expr) : NeverJumps (exitSource source incoming operand) := by
  unfold exitSource
  noJump_runtime

theorem neverJumps_selectCompletionChannel (source : RuntimeActivation) (operand : Expr) (channel : Channel) : NeverJumps (selectCompletionChannel source operand channel) := by
  unfold selectCompletionChannel
  repeat' first
    | exact neverJumps_exitSource _ _ _
    | noJump_runtime_step

theorem neverJumps_exitChannels (source activation : RuntimeActivation) (operands : List Expr) (origin : Goose.Core.OriginId) : NeverJumps (exitChannels source activation operands origin) := by
  unfold exitChannels
  repeat' first
    | exact neverJumps_exitSource _ _ _
    | noJump_runtime_step

theorem neverJumps_materializeOwnedCarriers (origin : Goose.Core.OriginId) (tokens : List ExitReservationId) (carriers : List Carrier) : NeverJumps (materializeOwnedCarriers origin tokens carriers) := by
  unfold materializeOwnedCarriers
  repeat' first
    | exact neverJumps_exitSource _ _ _
    | noJump_runtime_step

#print axioms neverJumps_getImplementation
#print axioms neverJumps_enclosingActivation
#print axioms neverJumps_targetActivation
#print axioms neverJumps_exitSource
#print axioms neverJumps_selectCompletionChannel
#print axioms neverJumps_exitChannels
#print axioms neverJumps_materializeOwnedCarriers

end Goose.Proofs.ConstructionDelivery
