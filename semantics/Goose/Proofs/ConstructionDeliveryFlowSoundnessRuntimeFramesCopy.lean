import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFrames
import Init.Data.Range.Lemmas

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem breakFrame_arrayForIn (items : Array α) (initial : β)
    (action : α → β → EvalM (ForInStep β))
    (body : ∀ item value, BreakFrameAction (action item value)) :
    BreakFrameAction (forIn items initial action) := by
  rw [← Array.forIn_toList]
  exact breakFrame_listForIn items.toList initial action body

theorem breakFrame_rangeForIn (range : Std.Legacy.Range) (initial : β)
    (action : Nat → β → EvalM (ForInStep β))
    (body : ∀ index value, BreakFrameAction (action index value)) :
    BreakFrameAction (forIn range initial action) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact breakFrame_listForIn _ initial action body

private theorem breakFrame_conditional (condition : Prop) [Decidable condition]
    (yes no : EvalM α) (left : BreakFrameAction yes) (right : BreakFrameAction no) :
    BreakFrameAction (if condition then yes else no) := by
  split <;> assumption

local elab "frame_conditional" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``BreakFrameAction do throwError "expected break frame"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.getAppFn.isConstOf ``ite do throwError "expected conditional action"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply breakFrame_conditional))

local elab "frame_intro" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isForall do throwError "expected callback"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro))

local elab "frame_zeta" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``BreakFrameAction do throwError "expected break frame"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.isLet do throwError "expected local action binding"
  Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))

local macro "copy_frame_step" : tactic => `(tactic|
  first
    | exact breakFrame_pure _
    | exact breakFrame_stop _
    | exact breakFrame_get
    | exact breakFrame_getDestination _
    | exact breakFrame_getStorage _
    | exact breakFrame_receivingLayout _ _
    | exact breakFrame_liftExcept _
    | exact breakFrame_liftLayout _
    | (with_reducible apply breakFrame_liftConstruction)
    | exact breakFrame_readLoc _ _ _
    | exact breakFrame_sampledStored _
    | exact breakFrame_storedPathRun _
    | exact breakFrame_completedReceivingDestination _
    | exact breakFrame_storedDestination _
    | (with_reducible apply breakFrame_arrayForIn)
    | (with_reducible apply breakFrame_rangeForIn)
    | (with_reducible apply breakFrame_bind)
    | (with_reducible apply breakFrame_listForIn)
    | (with_reducible apply breakFrame_listMapM)
    | frame_conditional
    | frame_zeta
    | frame_intro
    | split
    | unfold receivingDestination)

local macro "copy_frame" : tactic => `(tactic| repeat' copy_frame_step)

theorem breakFrame_readRun (fuel : Nat) (layout : LayoutEnv) (view : RuntimeView) :
    BreakFrameAction (readRun fuel layout view) := by
  unfold readRun
  copy_frame

theorem breakFrame_copyValue (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (value : Value) (origin : Goose.Core.OriginId) (source : Option Goose.Core.CopySource) :
    BreakFrameAction (copyValue fuel layout destination value origin source) := by
  cases fuel <;> simp only [copyValue] <;> copy_frame

theorem breakFrame_deliverCarriers (fuel : Nat) (layout : LayoutEnv) (channels : List Channel)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    BreakFrameAction (deliverCarriers fuel layout channels carriers origin) := by
  unfold deliverCarriers
  repeat' first
    | exact breakFrame_copyValue _ _ _ _ _ _
    | copy_frame_step

theorem breakFrame_repeatElement (fuel : Nat) (layout : LayoutEnv) (parent : Goose.Core.DestinationId)
    (element : Ty) (source : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    BreakFrameAction (repeatElement fuel layout parent element source origin) := by
  cases fuel <;> simp only [repeatElement] <;> copy_frame

#print axioms breakFrame_arrayForIn
#print axioms breakFrame_rangeForIn
#print axioms breakFrame_readRun
#print axioms breakFrame_copyValue
#print axioms breakFrame_deliverCarriers
#print axioms breakFrame_repeatElement

end Goose.Proofs.ConstructionDelivery
