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
    | exact neverJumps_writeLoc _ _ _ _
    | exact neverJumps_newDestination _ _ _ _ _ _ _
    | exact neverJumps_completedDestination _
    | exact neverJumps_publishCarriers _ _
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

theorem neverJumps_cleanupDestination (origin : Goose.Core.OriginId) (id : Goose.Core.DestinationId)
    (carriers : List Carrier) : NeverJumps (cleanupDestination origin id carriers) := by
  unfold cleanupDestination
  copy_noJump

theorem neverJumps_cleanupReceivingDestination (origin : Goose.Core.OriginId) (id : Goose.Core.DestinationId)
    (carriers : List Carrier) : NeverJumps (cleanupReceivingDestination origin id carriers) := by
  unfold cleanupReceivingDestination
  apply neverJumps_bind
  · exact neverJumps_receivingDestination _
  · intro current; exact neverJumps_cleanupDestination _ _ _

theorem neverJumps_prepareNamedCarrierAt (origin : Goose.Core.OriginId) (token : ExitReservationId)
    (incoming : Goose.Core.DestinationId) (stored : StoredValue) :
    NeverJumps (prepareNamedCarrierAt origin token incoming stored) := by
  unfold prepareNamedCarrierAt
  copy_noJump

theorem neverJumps_prepareNamedCarrier (origin : Goose.Core.OriginId) (incoming : Goose.Core.DestinationId)
    (stored : StoredValue) : NeverJumps (prepareNamedCarrier origin incoming stored) := by
  unfold prepareNamedCarrier
  copy_noJump

theorem neverJumps_materializeNamedCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    NeverJumps (materializeNamedCarriers origin carriers) := by
  unfold materializeNamedCarriers
  copy_noJump

theorem neverJumps_ownerDestination (layout : LayoutEnv) (stored : StoredValue)
    (request : Goose.Core.ConstructionRequest) (knownCount : Option Nat) (origin : Goose.Core.OriginId) :
    NeverJumps (ownerDestination layout stored request knownCount origin) := by
  unfold ownerDestination
  copy_noJump

theorem neverJumps_publishOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (stored : StoredValue) (id : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    NeverJumps (publishOwner fuel layout location stored id origin) := by
  cases fuel <;> simp only [publishOwner] <;> copy_noJump

theorem neverJumps_openElementReceiving (layout : LayoutEnv) (owner : Goose.Core.ActId) (location : Goose.Core.Loc)
    (stored : StoredValue) (element : Ty) (knownCount : Option Nat) (origin : Goose.Core.OriginId) :
    NeverJumps (openElementReceiving layout owner location stored element knownCount origin) := by
  unfold openElementReceiving
  copy_noJump

theorem neverJumps_publishElementReceiving (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (stored : StoredValue) (id : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    NeverJumps (publishElementReceiving fuel layout location stored id origin) := by
  cases fuel <;> simp only [publishElementReceiving] <;> copy_noJump

theorem neverJumps_truncateOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (count : Nat) (origin : Goose.Core.OriginId) :
    NeverJumps (truncateOwner fuel layout location count origin) := by
  cases fuel <;> simp only [truncateOwner] <;> copy_noJump

theorem neverJumps_appendFixedValues (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (values : List Value) (origin : Goose.Core.OriginId) :
    NeverJumps (appendFixedValues fuel layout location values origin) := by
  cases fuel <;> simp only [appendFixedValues]
  all_goals repeat' first
    | exact neverJumps_ownerDestination _ _ _ _ _
    | exact neverJumps_publishOwner _ _ _ _ _ _
    | copy_noJump_step

theorem neverJumps_appendRun (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (view : RuntimeView) (origin : Goose.Core.OriginId) :
    NeverJumps (appendRun fuel layout location view origin) := by
  cases fuel <;> simp only [appendRun]
  all_goals repeat' first
    | exact neverJumps_ownerDestination _ _ _ _ _
    | exact neverJumps_publishOwner _ _ _ _ _ _
    | copy_noJump_step

#print axioms neverJumps_cleanupDestination
#print axioms neverJumps_cleanupReceivingDestination
#print axioms neverJumps_prepareNamedCarrierAt
#print axioms neverJumps_prepareNamedCarrier
#print axioms neverJumps_materializeNamedCarriers
#print axioms neverJumps_ownerDestination
#print axioms neverJumps_publishOwner
#print axioms neverJumps_openElementReceiving
#print axioms neverJumps_publishElementReceiving
#print axioms neverJumps_truncateOwner
#print axioms neverJumps_appendFixedValues
#print axioms neverJumps_appendRun

end Goose.Proofs.ConstructionDelivery
