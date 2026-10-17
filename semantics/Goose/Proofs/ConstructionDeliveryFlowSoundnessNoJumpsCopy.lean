import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumps
import Init.Data.Range.Lemmas

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem neverJumps_arrayForIn (items : Array α) (initial : β)
    (action : α → β → EvalM (ForInStep β))
    (body : ∀ item value, NeverJumps (action item value)) :
    NeverJumps (forIn items initial action) := by
  rw [← Array.forIn_toList]
  exact neverJumps_forIn items.toList initial action body

theorem neverJumps_rangeForIn (range : Std.Legacy.Range) (initial : β)
    (action : Nat → β → EvalM (ForInStep β))
    (body : ∀ index value, NeverJumps (action index value)) :
    NeverJumps (forIn range initial action) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact neverJumps_forIn _ initial action body

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

local macro "copy_noJump_step" : tactic => `(tactic|
  first
    | exact neverJumps_pure _
    | exact neverJumps_stop _
    | exact neverJumps_get
    | exact neverJumps_getDestination _
    | exact neverJumps_getStorage _
    | exact neverJumps_receivingLayout _ _
    | exact neverJumps_liftExcept _
    | exact neverJumps_liftLayout _
    | (with_reducible apply neverJumps_lift)
    | exact neverJumps_readLoc _ _ _
    | exact neverJumps_sampledStored _
    | exact neverJumps_storedPathRun _
    | exact neverJumps_completedReceivingDestination _
    | exact neverJumps_storedDestination _
    | (with_reducible apply neverJumps_arrayForIn)
    | (with_reducible apply neverJumps_rangeForIn)
    | (with_reducible apply neverJumps_bind)
    | (with_reducible apply neverJumps_forIn)
    | (with_reducible apply neverJumps_listMapM)
    | noJump_conditional
    | noJump_zeta
    | noJump_intro
    | split
    | unfold receivingDestination)

local macro "copy_noJump" : tactic => `(tactic| repeat' copy_noJump_step)

theorem neverJumps_readRun (fuel : Nat) (layout : LayoutEnv) (view : RuntimeView) :
    NeverJumps (readRun fuel layout view) := by
  unfold readRun
  copy_noJump

theorem neverJumps_copyValue (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (value : Value) (origin : Goose.Core.OriginId) (source : Option Goose.Core.CopySource) :
    NeverJumps (copyValue fuel layout destination value origin source) := by
  cases fuel <;> simp only [copyValue] <;> copy_noJump

theorem neverJumps_deliverCarriers (fuel : Nat) (layout : LayoutEnv) (channels : List Channel)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    NeverJumps (deliverCarriers fuel layout channels carriers origin) := by
  unfold deliverCarriers
  repeat' first
    | exact neverJumps_copyValue _ _ _ _ _ _
    | copy_noJump_step

theorem neverJumps_repeatElement (fuel : Nat) (layout : LayoutEnv) (parent : Goose.Core.DestinationId)
    (element : Ty) (source : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    NeverJumps (repeatElement fuel layout parent element source origin) := by
  cases fuel <;> simp only [repeatElement] <;> copy_noJump

#print axioms neverJumps_arrayForIn
#print axioms neverJumps_rangeForIn
#print axioms neverJumps_readRun
#print axioms neverJumps_copyValue
#print axioms neverJumps_deliverCarriers
#print axioms neverJumps_repeatElement

end Goose.Proofs.ConstructionDelivery
