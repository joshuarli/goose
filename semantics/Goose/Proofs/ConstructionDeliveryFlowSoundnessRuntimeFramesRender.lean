import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesCopy

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

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
    | exact breakFrame_expectInt _
    | exact breakFrame_readRun _ _ _
    | exact breakFrame_readStoredElement _ _ _ _
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

private theorem breakFrame_renderValue (value : Value) : BreakFrameAction (renderValue value) := by
  cases value <;> simp only [renderValue] <;> copy_frame

private theorem renderFrames (fuel : Nat) :
    (∀ layout position value, BreakFrameAction (renderAny fuel layout position value)) ∧
    (∀ layout values, BreakFrameAction (renderElements fuel layout values)) ∧
    (∀ layout position stored, BreakFrameAction (renderStored fuel layout position stored)) ∧
    (∀ layout position view, BreakFrameAction (renderView fuel layout position view)) := by
  induction fuel with
  | zero =>
      repeat' constructor
      all_goals intros
      all_goals simp only [renderAny, renderElements, renderStored, renderView]
      all_goals exact breakFrame_stop _
  | succ fuel previous =>
      rcases previous with ⟨anyFrame, elementsFrame, storedFrame, viewFrame⟩
      repeat' constructor
      all_goals intros
      all_goals simp only [renderAny, renderElements, renderStored, renderView]
      all_goals repeat' first
        | exact anyFrame _ _ _
        | exact elementsFrame _ _
        | exact storedFrame _ _ _
        | exact viewFrame _ _ _
        | exact breakFrame_renderValue _
        | copy_frame_step

theorem breakFrame_renderAny (fuel : Nat) (layout : LayoutEnv) (position : RenderPosition) (value : Value) :
    BreakFrameAction (renderAny fuel layout position value) := (renderFrames fuel).1 layout position value

theorem breakFrame_renderElements (fuel : Nat) (layout : LayoutEnv) (values : List Value) :
    BreakFrameAction (renderElements fuel layout values) := (renderFrames fuel).2.1 layout values

theorem breakFrame_renderStored (fuel : Nat) (layout : LayoutEnv) (position : RenderPosition) (stored : StoredValue) :
    BreakFrameAction (renderStored fuel layout position stored) := (renderFrames fuel).2.2.1 layout position stored

theorem breakFrame_renderView (fuel : Nat) (layout : LayoutEnv) (position : RenderPosition) (view : RuntimeView) :
    BreakFrameAction (renderView fuel layout position view) := (renderFrames fuel).2.2.2 layout position view

#print axioms breakFrame_renderAny
#print axioms breakFrame_renderElements
#print axioms breakFrame_renderStored
#print axioms breakFrame_renderView

end Goose.Proofs.ConstructionDelivery
