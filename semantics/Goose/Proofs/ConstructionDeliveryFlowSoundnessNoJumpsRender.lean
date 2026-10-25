import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumpsCopy

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
    | exact neverJumps_expectInt _
    | exact neverJumps_readRun _ _ _
    | exact neverJumps_readStoredElement _ _ _ _
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

private theorem neverJumps_renderValue (value : Value) : NeverJumps (renderValue value) := by
  cases value <;> simp only [renderValue] <;> copy_noJump

private theorem renderNoJumps (fuel : Nat) :
    (∀ layout position value, NeverJumps (renderAny fuel layout position value)) ∧
    (∀ layout values, NeverJumps (renderElements fuel layout values)) ∧
    (∀ layout position stored, NeverJumps (renderStored fuel layout position stored)) ∧
    (∀ layout position view, NeverJumps (renderView fuel layout position view)) := by
  induction fuel with
  | zero =>
      repeat' constructor
      all_goals intros
      all_goals simp only [renderAny, renderElements, renderStored, renderView]
      all_goals exact neverJumps_stop _
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
        | exact neverJumps_renderValue _
        | copy_noJump_step

theorem neverJumps_renderAny (fuel : Nat) (layout : LayoutEnv) (position : RenderPosition) (value : Value) :
    NeverJumps (renderAny fuel layout position value) := (renderNoJumps fuel).1 layout position value

theorem neverJumps_renderElements (fuel : Nat) (layout : LayoutEnv) (values : List Value) :
    NeverJumps (renderElements fuel layout values) := (renderNoJumps fuel).2.1 layout values

theorem neverJumps_renderStored (fuel : Nat) (layout : LayoutEnv) (position : RenderPosition) (stored : StoredValue) :
    NeverJumps (renderStored fuel layout position stored) := (renderNoJumps fuel).2.2.1 layout position stored

theorem neverJumps_renderView (fuel : Nat) (layout : LayoutEnv) (position : RenderPosition) (view : RuntimeView) :
    NeverJumps (renderView fuel layout position view) := (renderNoJumps fuel).2.2.2 layout position view

#print axioms neverJumps_renderAny
#print axioms neverJumps_renderElements
#print axioms neverJumps_renderStored
#print axioms neverJumps_renderView

end Goose.Proofs.ConstructionDelivery
