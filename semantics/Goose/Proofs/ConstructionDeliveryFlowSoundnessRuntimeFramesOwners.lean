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
    | exact breakFrame_writeLoc _ _ _ _
    | exact breakFrame_newDestination _ _ _ _ _ _ _
    | exact breakFrame_completedDestination _
    | exact breakFrame_publishCarriers _ _
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

theorem breakFrame_cleanupDestination (origin : Goose.Core.OriginId) (id : Goose.Core.DestinationId)
    (carriers : List Carrier) : BreakFrameAction (cleanupDestination origin id carriers) := by
  unfold cleanupDestination
  copy_frame

theorem breakFrame_cleanupReceivingDestination (origin : Goose.Core.OriginId) (id : Goose.Core.DestinationId)
    (carriers : List Carrier) : BreakFrameAction (cleanupReceivingDestination origin id carriers) := by
  unfold cleanupReceivingDestination
  apply breakFrame_bind
  · exact breakFrame_receivingDestination _
  · intro current; exact breakFrame_cleanupDestination _ _ _

theorem breakFrame_prepareNamedCarrierAt (origin : Goose.Core.OriginId) (token : ExitReservationId)
    (incoming : Goose.Core.DestinationId) (stored : StoredValue) :
    BreakFrameAction (prepareNamedCarrierAt origin token incoming stored) := by
  unfold prepareNamedCarrierAt
  copy_frame

theorem breakFrame_prepareNamedCarrier (origin : Goose.Core.OriginId) (incoming : Goose.Core.DestinationId)
    (stored : StoredValue) : BreakFrameAction (prepareNamedCarrier origin incoming stored) := by
  unfold prepareNamedCarrier
  copy_frame

theorem breakFrame_materializeNamedCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    BreakFrameAction (materializeNamedCarriers origin carriers) := by
  unfold materializeNamedCarriers
  copy_frame

theorem breakFrame_ownerDestination (layout : LayoutEnv) (stored : StoredValue)
    (request : Goose.Core.ConstructionRequest) (knownCount : Option Nat) (origin : Goose.Core.OriginId) :
    BreakFrameAction (ownerDestination layout stored request knownCount origin) := by
  unfold ownerDestination
  copy_frame

theorem breakFrame_publishOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (stored : StoredValue) (id : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    BreakFrameAction (publishOwner fuel layout location stored id origin) := by
  cases fuel <;> simp only [publishOwner] <;> copy_frame

theorem breakFrame_openElementReceiving (layout : LayoutEnv) (owner : Goose.Core.ActId) (location : Goose.Core.Loc)
    (stored : StoredValue) (element : Ty) (knownCount : Option Nat) (origin : Goose.Core.OriginId) :
    BreakFrameAction (openElementReceiving layout owner location stored element knownCount origin) := by
  unfold openElementReceiving
  copy_frame

theorem breakFrame_publishElementReceiving (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (stored : StoredValue) (id : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    BreakFrameAction (publishElementReceiving fuel layout location stored id origin) := by
  cases fuel <;> simp only [publishElementReceiving] <;> copy_frame

theorem breakFrame_truncateOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (count : Nat) (origin : Goose.Core.OriginId) :
    BreakFrameAction (truncateOwner fuel layout location count origin) := by
  cases fuel <;> simp only [truncateOwner] <;> copy_frame

theorem breakFrame_appendFixedValues (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (values : List Value) (origin : Goose.Core.OriginId) :
    BreakFrameAction (appendFixedValues fuel layout location values origin) := by
  cases fuel <;> simp only [appendFixedValues]
  all_goals repeat' first
    | exact breakFrame_ownerDestination _ _ _ _ _
    | exact breakFrame_publishOwner _ _ _ _ _ _
    | copy_frame_step

theorem breakFrame_appendRun (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (view : RuntimeView) (origin : Goose.Core.OriginId) :
    BreakFrameAction (appendRun fuel layout location view origin) := by
  cases fuel <;> simp only [appendRun]
  all_goals repeat' first
    | exact breakFrame_ownerDestination _ _ _ _ _
    | exact breakFrame_publishOwner _ _ _ _ _ _
    | copy_frame_step

#print axioms breakFrame_cleanupDestination
#print axioms breakFrame_cleanupReceivingDestination
#print axioms breakFrame_prepareNamedCarrierAt
#print axioms breakFrame_prepareNamedCarrier
#print axioms breakFrame_materializeNamedCarriers
#print axioms breakFrame_ownerDestination
#print axioms breakFrame_publishOwner
#print axioms breakFrame_openElementReceiving
#print axioms breakFrame_publishElementReceiving
#print axioms breakFrame_truncateOwner
#print axioms breakFrame_appendFixedValues
#print axioms breakFrame_appendRun

end Goose.Proofs.ConstructionDelivery
