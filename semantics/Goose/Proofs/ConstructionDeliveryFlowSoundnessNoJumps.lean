import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntime
import Lean.Elab.Tactic

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem neverJumps_set (state : ExecutionState) : NeverJumps (EvalM.set state) := by
  intro before target kind after impossible
  cases impossible

theorem neverJumps_freshScope : NeverJumps freshScope := by
  intro before target kind after impossible
  cases impossible

theorem neverJumps_freshAct : NeverJumps freshAct := by
  intro before target kind after impossible
  cases impossible

theorem neverJumps_liftExcept (action : Except Goose.Core.Stop α) : NeverJumps (liftExcept action) := by
  cases action with
  | ok value => exact neverJumps_pure _
  | error reason => exact neverJumps_stop _

theorem neverJumps_liftLayout (action : Except LayoutFault α) : NeverJumps (liftLayout action) := by
  cases action with
  | ok value => exact neverJumps_pure _
  | error reason => cases reason <;> exact neverJumps_stop _

theorem neverJumps_getStorage (id : Goose.Core.StorageId) : NeverJumps (getStorage id) := by
  unfold getStorage
  apply neverJumps_bind
  · exact neverJumps_get
  · intro state
    split
    · exact neverJumps_pure _
    · exact neverJumps_stop _

private theorem neverJumps_mapMLoop (items : List α) (action : α → EvalM β)
    (body : ∀ item, NeverJumps (action item)) (accumulator : List β) :
    NeverJumps (List.mapM.loop action items accumulator) := by
  induction items generalizing accumulator with
  | nil => exact neverJumps_pure _
  | cons item rest ih =>
      change NeverJumps (do
        let value ← action item
        List.mapM.loop action rest (value :: accumulator))
      apply neverJumps_bind
      · exact body item
      · intro value; exact ih (value :: accumulator)

theorem neverJumps_listMapM (items : List α) (action : α → EvalM β)
    (body : ∀ item, NeverJumps (action item)) :
    NeverJumps (items.mapM action) :=
  neverJumps_mapMLoop items action body []

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

theorem neverJumps_storedDestination (id : Goose.Core.DestinationId) : NeverJumps (storedDestination id) := by
  unfold storedDestination
  noJump_runtime

theorem neverJumps_receivingDestination (id : Goose.Core.DestinationId) : NeverJumps (receivingDestination id) :=
  neverJumps_lift _ _

theorem neverJumps_completedDestination (id : Goose.Core.DestinationId) : NeverJumps (completedDestination id) := by
  unfold completedDestination
  noJump_runtime

theorem neverJumps_completedReceivingDestination (id : Goose.Core.DestinationId) :
    NeverJumps (completedReceivingDestination id) := by
  apply neverJumps_bind
  · exact neverJumps_receivingDestination _
  · intro current; exact neverJumps_completedDestination current

theorem neverJumps_setObjectOrdinal (root : Goose.Core.RootInst) (ordinal : Goose.Core.StorageId) :
    NeverJumps (setObjectOrdinal root ordinal) := by
  intro state target kind after impossible
  cases impossible

theorem neverJumps_bindStaticRoot (root : Goose.Core.RootInst) (value : Value) :
    NeverJumps (bindStaticRoot root value) := by
  intro state target kind after impossible
  cases impossible

theorem neverJumps_reserveRootObject (root : Goose.Core.RootInst) :
    NeverJumps (reserveRootObject root) := by
  unfold reserveRootObject
  noJump_runtime
  exact neverJumps_setObjectOrdinal _ _

theorem neverJumps_bindRoot (root : Goose.Core.RootInst) (value : Value) :
    NeverJumps (bindRoot root value) := by
  unfold bindRoot
  noJump_runtime
  all_goals first
    | exact neverJumps_bindStaticRoot _ _
    | exact neverJumps_setObjectOrdinal _ _
    | exact neverJumps_reserveRootObject _
    | (cases value <;> noJump_runtime)
  all_goals first
    | exact neverJumps_bindStaticRoot _ _
    | exact neverJumps_setObjectOrdinal _ _
    | exact neverJumps_reserveRootObject _

theorem neverJumps_rootOf (environment : RuntimeActivation) (localVar : Goose.Core.VarId) :
    NeverJumps (rootOf environment localVar) := by
  unfold rootOf
  noJump_runtime

theorem neverJumps_currentBreak (act : Goose.Core.ActId) (scope : Option BreakScope) :
    NeverJumps (currentBreak act scope) := by
  unfold currentBreak
  noJump_runtime

theorem neverJumps_sampledStored (stored : StoredValue) : NeverJumps (sampledStored stored) := by
  unfold sampledStored
  noJump_runtime

theorem neverJumps_storedPathRun (stored : StoredValue) : NeverJumps (storedPathRun stored) := by
  unfold storedPathRun
  apply neverJumps_bind
  · exact neverJumps_sampledStored _
  · intro value; exact neverJumps_pure _

theorem neverJumps_readStoredElement (fuel : Nat) (layout : LayoutEnv)
    (stored : StoredValue) (index : Nat) : NeverJumps (readStoredElement fuel layout stored index) := by
  unfold readStoredElement
  apply neverJumps_bind
  · exact neverJumps_storedPathRun _
  · intro value
    noJump_runtime

theorem neverJumps_readValuePath (fuel : Nat) (layout : LayoutEnv) (value : Value)
    (path : List Nat) : NeverJumps (readValuePath fuel layout value path) := by
  induction fuel generalizing value path with
  | zero => exact neverJumps_stop _
  | succ fuel ih =>
      cases path with
      | nil => exact neverJumps_pure _
      | cons index rest =>
          cases value <;> simp only [readValuePath] <;> noJump_runtime
          all_goals first
            | exact neverJumps_readStoredElement _ _ _ _
            | exact ih _ _

theorem neverJumps_readLoc (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc) :
    NeverJumps (readLoc fuel layout location) := by
  unfold readLoc
  noJump_runtime
  exact neverJumps_readValuePath _ _ _ _

theorem neverJumps_receivingAction (origin : Goose.Core.OriginId) (incoming : Goose.Core.DestinationId)
    (action : Goose.Core.DestinationId → ConstructionM α) :
    NeverJumps (receivingAction origin incoming action) :=
  neverJumps_lift _ _

theorem neverJumps_newDestination (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (storage : Option Goose.Core.StorageId) (knownCount : Option Nat) :
    NeverJumps (newDestination layout owner ty request origin storage knownCount) := by
  unfold newDestination
  noJump_runtime

theorem neverJumps_channelsFor (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (results : List ResultDescriptor) (origin : Goose.Core.OriginId) :
    NeverJumps (channelsFor layout owner results origin) := by
  unfold channelsFor
  apply neverJumps_listMapM
  intro descriptor
  cases descriptor.request <;> noJump_runtime
  all_goals exact neverJumps_newDestination _ _ _ _ _ _ _

theorem neverJumps_carrierValue (carrier : Carrier) : NeverJumps (carrierValue carrier) := by
  cases carrier <;> unfold carrierValue <;> noJump_runtime
  exact neverJumps_storedDestination _

theorem neverJumps_singleCarrier (carriers : List Carrier) : NeverJumps (singleCarrier carriers) := by
  unfold singleCarrier
  noJump_runtime

theorem neverJumps_publishCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    NeverJumps (publishCarriers origin carriers) := by
  unfold publishCarriers
  noJump_runtime

theorem neverJumps_arrayLength (value : Value) : NeverJumps (arrayLength value) := by
  cases value <;> unfold arrayLength <;> noJump_runtime
  exact neverJumps_sampledStored _

theorem neverJumps_bindAll (act : Goose.Core.ActId) (scope : Goose.Core.ScopeInst)
    (values : List (Goose.Core.VarId × Value)) : NeverJumps (bindAll act scope values) := by
  unfold bindAll
  noJump_runtime
  exact neverJumps_bindRoot _ _

theorem neverJumps_emitStdout (bytes : ByteArray) : NeverJumps (emitStdout bytes) :=
  neverJumps_lift _ _

theorem neverJumps_expectInt (value : Value) : NeverJumps (expectInt value) := by
  cases value <;> unfold expectInt <;> noJump_runtime

theorem neverJumps_expectBool (value : Value) : NeverJumps (expectBool value) := by
  cases value <;> unfold expectBool <;> noJump_runtime

theorem neverJumps_expectRef (value : Value) : NeverJumps (expectRef value) := by
  cases value <;> unfold expectRef <;> noJump_runtime

theorem neverJumps_sameIntType (left right : Goose.Core.IntTy) : NeverJumps (sameIntType left right) := by
  unfold sameIntType
  noJump_runtime

theorem neverJumps_comparable (left right : Value) : NeverJumps (comparable left right) := by
  cases left <;> cases right <;> unfold comparable <;> noJump_runtime
  exact neverJumps_sameIntType _ _

private theorem neverJumps_updateStorage (id : Goose.Core.StorageId)
    (update : ReceivingStorage → ReceivingStorage) (result : α) :
    NeverJumps (do
      let state ← EvalM.get
      let some storage := state.construction.storage[id]? | fault .danglingRoot
      EvalM.set { state with construction := { state.construction with
        storage := state.construction.storage.set! id (update storage) } }
      pure result) := by
  noJump_runtime

theorem neverJumps_writeValuePath (fuel : Nat) (layout : LayoutEnv) (value : Value)
    (path : List Nat) (replacement : Value) :
    NeverJumps (writeValuePath fuel layout value path replacement) := by
  induction fuel generalizing value path replacement with
  | zero => exact neverJumps_stop _
  | succ fuel ih =>
      cases path with
      | nil => exact neverJumps_pure _
      | cons index rest =>
          cases value <;> simp only [writeValuePath]
          all_goals repeat' first
            | exact neverJumps_storedPathRun _
            | exact neverJumps_readStoredElement _ _ _ _
            | exact neverJumps_updateStorage _ _ _
            | exact ih _ _ _
            | noJump_runtime_step

theorem neverJumps_writeLoc (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (replacement : Value) : NeverJumps (writeLoc fuel layout location replacement) := by
  unfold writeLoc
  repeat' first
    | exact neverJumps_writeValuePath _ _ _ _ _
    | exact neverJumps_bindRoot _ _
    | noJump_runtime_step

#print axioms neverJumps_set
#print axioms neverJumps_freshScope
#print axioms neverJumps_freshAct
#print axioms neverJumps_liftExcept
#print axioms neverJumps_liftLayout
#print axioms neverJumps_getStorage
#print axioms neverJumps_listMapM
#print axioms neverJumps_storedDestination
#print axioms neverJumps_receivingDestination
#print axioms neverJumps_completedDestination
#print axioms neverJumps_completedReceivingDestination
#print axioms neverJumps_setObjectOrdinal
#print axioms neverJumps_bindStaticRoot
#print axioms neverJumps_reserveRootObject
#print axioms neverJumps_bindRoot
#print axioms neverJumps_rootOf
#print axioms neverJumps_currentBreak
#print axioms neverJumps_sampledStored
#print axioms neverJumps_storedPathRun
#print axioms neverJumps_readStoredElement
#print axioms neverJumps_readValuePath
#print axioms neverJumps_readLoc
#print axioms neverJumps_receivingAction
#print axioms neverJumps_newDestination
#print axioms neverJumps_channelsFor
#print axioms neverJumps_carrierValue
#print axioms neverJumps_singleCarrier
#print axioms neverJumps_publishCarriers
#print axioms neverJumps_arrayLength
#print axioms neverJumps_bindAll
#print axioms neverJumps_emitStdout
#print axioms neverJumps_expectInt
#print axioms neverJumps_expectBool
#print axioms neverJumps_expectRef
#print axioms neverJumps_sameIntType
#print axioms neverJumps_comparable
#print axioms neverJumps_writeValuePath
#print axioms neverJumps_writeLoc

end Goose.Proofs.ConstructionDelivery
