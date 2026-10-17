import Goose.Proofs.ConstructionDeliveryFlowSoundnessFrames
import Lean.Elab.Tactic

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem breakFrame_liftExcept (action : Except Goose.Core.Stop α) : BreakFrameAction (liftExcept action) := by
  cases action with
  | ok value => exact breakFrame_pure _
  | error reason => exact breakFrame_stop _

theorem breakFrame_liftLayout (action : Except LayoutFault α) : BreakFrameAction (liftLayout action) := by
  cases action with
  | ok value => exact breakFrame_pure _
  | error reason => cases reason <;> exact breakFrame_stop _

theorem breakFrame_getDestination (id : Goose.Core.DestinationId) : BreakFrameAction (getDestination id) := by
  unfold getDestination
  apply breakFrame_bind
  · exact breakFrame_get
  · intro state
    split
    · exact breakFrame_pure _
    · exact breakFrame_stop _

theorem breakFrame_getStorage (id : Goose.Core.StorageId) : BreakFrameAction (getStorage id) := by
  unfold getStorage
  apply breakFrame_bind
  · exact breakFrame_get
  · intro state
    split
    · exact breakFrame_pure _
    · exact breakFrame_stop _

theorem breakFrame_receivingLayout (layout : LayoutEnv) (ty : Ty) : BreakFrameAction (receivingLayout layout ty) := by
  cases ty <;> simp only [receivingLayout]
  all_goals first | exact breakFrame_pure _ | exact breakFrame_stop _ | skip
  split
  · exact breakFrame_pure _
  · exact breakFrame_stop _

theorem breakFrame_listForIn (items : List α) (initial : β)
    (action : α → β → EvalM (ForInStep β))
    (body : ∀ item value, BreakFrameAction (action item value)) :
    BreakFrameAction (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact breakFrame_pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply breakFrame_bind
      · exact body item initial
      · intro step
        cases step with
        | done value => exact breakFrame_pure _
        | yield value => exact ih value

private theorem breakFrame_mapMLoop (items : List α) (action : α → EvalM β)
    (body : ∀ item, BreakFrameAction (action item)) (accumulator : List β) :
    BreakFrameAction (List.mapM.loop action items accumulator) := by
  induction items generalizing accumulator with
  | nil => exact breakFrame_pure _
  | cons item rest ih =>
      change BreakFrameAction (do
        let value ← action item
        List.mapM.loop action rest (value :: accumulator))
      apply breakFrame_bind
      · exact body item
      · intro value; exact ih (value :: accumulator)

theorem breakFrame_listMapM (items : List α) (action : α → EvalM β)
    (body : ∀ item, BreakFrameAction (action item)) :
    BreakFrameAction (items.mapM action) :=
  breakFrame_mapMLoop items action body []

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

local macro "frame_runtime_step" : tactic => `(tactic|
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
    | (with_reducible apply breakFrame_bind)
    | (with_reducible apply breakFrame_listForIn)
    | (with_reducible apply breakFrame_listMapM)
    | frame_conditional
    | frame_zeta
    | frame_intro
    | split
    | unfold receivingDestination)

local macro "frame_runtime" : tactic => `(tactic| repeat' frame_runtime_step)

theorem breakFrame_storedDestination (id : Goose.Core.DestinationId) : BreakFrameAction (storedDestination id) := by
  unfold storedDestination
  frame_runtime

theorem breakFrame_receivingDestination (id : Goose.Core.DestinationId) : BreakFrameAction (receivingDestination id) :=
  breakFrame_liftConstruction _ _

theorem breakFrame_completedDestination (id : Goose.Core.DestinationId) : BreakFrameAction (completedDestination id) := by
  unfold completedDestination
  frame_runtime

theorem breakFrame_completedReceivingDestination (id : Goose.Core.DestinationId) :
    BreakFrameAction (completedReceivingDestination id) := by
  apply breakFrame_bind
  · exact breakFrame_receivingDestination _
  · intro current; exact breakFrame_completedDestination current

theorem breakFrame_finishChannel (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (carrier : Carrier) (result : Ty) : BreakFrameAction (finishChannel layout origin carrier result) := by
  cases carrier <;> unfold finishChannel <;> frame_runtime

theorem breakFrame_landCarriersInto (origin : Goose.Core.OriginId)
    (channels : List Channel) (carriers : List Carrier) :
    BreakFrameAction (landCarriersInto origin channels carriers) := by
  unfold landCarriersInto
  frame_runtime

theorem breakFrame_finishChannels (layout : LayoutEnv) (channels : List Channel)
    (types : List Ty) (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    BreakFrameAction (finishChannels layout channels types carriers origin) := by
  unfold finishChannels
  apply breakFrame_bind
  · exact breakFrame_landCarriersInto origin channels carriers
  · intro _
    frame_runtime
    exact breakFrame_finishChannel _ _ _ _

theorem breakFrame_setObjectOrdinal (root : Goose.Core.RootInst) (ordinal : Goose.Core.StorageId) :
    BreakFrameAction (setObjectOrdinal root ordinal) := by
  intro state _
  change BreakStackFrame state
    { state with objectOrdinals := (root, ordinal) :: state.objectOrdinals.filter (fun entry => entry.1 != root) }
  exact ⟨Nat.le_refl _, rfl⟩

theorem breakFrame_bindStaticRoot (root : Goose.Core.RootInst) (value : Value) :
    BreakFrameAction (bindStaticRoot root value) := by
  intro state _
  change BreakStackFrame state
    { state with objects := (root, value) :: state.objects.filter (fun entry => entry.1 != root) }
  exact ⟨Nat.le_refl _, rfl⟩

theorem breakFrame_reserveRootObject (root : Goose.Core.RootInst) :
    BreakFrameAction (reserveRootObject root) := by
  unfold reserveRootObject
  frame_runtime
  exact breakFrame_setObjectOrdinal _ _

theorem breakFrame_bindRoot (root : Goose.Core.RootInst) (value : Value) :
    BreakFrameAction (bindRoot root value) := by
  unfold bindRoot
  frame_runtime
  all_goals first
    | exact breakFrame_bindStaticRoot _ _
    | exact breakFrame_setObjectOrdinal _ _
    | exact breakFrame_reserveRootObject _
    | (cases value <;> frame_runtime)
  all_goals first
    | exact breakFrame_bindStaticRoot _ _
    | exact breakFrame_setObjectOrdinal _ _
    | exact breakFrame_reserveRootObject _

theorem breakFrame_rootOf (environment : RuntimeActivation) (localVar : Goose.Core.VarId) :
    BreakFrameAction (rootOf environment localVar) := by
  unfold rootOf
  frame_runtime

theorem breakFrame_currentBreak (act : Goose.Core.ActId) (scope : Option BreakScope) :
    BreakFrameAction (currentBreak act scope) := by
  unfold currentBreak
  frame_runtime

theorem breakFrame_sampledStored (stored : StoredValue) : BreakFrameAction (sampledStored stored) := by
  unfold sampledStored
  frame_runtime

theorem breakFrame_storedPathRun (stored : StoredValue) : BreakFrameAction (storedPathRun stored) := by
  unfold storedPathRun
  apply breakFrame_bind
  · exact breakFrame_sampledStored _
  · intro value; exact breakFrame_pure _

theorem breakFrame_readStoredElement (fuel : Nat) (layout : LayoutEnv)
    (stored : StoredValue) (index : Nat) : BreakFrameAction (readStoredElement fuel layout stored index) := by
  unfold readStoredElement
  apply breakFrame_bind
  · exact breakFrame_storedPathRun _
  · intro value
    frame_runtime

theorem breakFrame_readValuePath (fuel : Nat) (layout : LayoutEnv) (value : Value)
    (path : List Nat) : BreakFrameAction (readValuePath fuel layout value path) := by
  induction fuel generalizing value path with
  | zero => exact breakFrame_stop _
  | succ fuel ih =>
      cases path with
      | nil => exact breakFrame_pure _
      | cons index rest =>
          cases value <;> simp only [readValuePath] <;> frame_runtime
          all_goals first
            | exact breakFrame_readStoredElement _ _ _ _
            | exact ih _ _

theorem breakFrame_readLoc (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc) :
    BreakFrameAction (readLoc fuel layout location) := by
  unfold readLoc
  frame_runtime
  exact breakFrame_readValuePath _ _ _ _

theorem breakFrame_receivingAction (origin : Goose.Core.OriginId) (incoming : Goose.Core.DestinationId)
    (action : Goose.Core.DestinationId → ConstructionM α) :
    BreakFrameAction (receivingAction origin incoming action) :=
  breakFrame_liftConstruction _ _

theorem breakFrame_newDestination (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (storage : Option Goose.Core.StorageId) (knownCount : Option Nat) :
    BreakFrameAction (newDestination layout owner ty request origin storage knownCount) := by
  unfold newDestination
  frame_runtime

theorem breakFrame_channelsFor (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (results : List ResultDescriptor) (origin : Goose.Core.OriginId) :
    BreakFrameAction (channelsFor layout owner results origin) := by
  unfold channelsFor
  apply breakFrame_listMapM
  intro descriptor
  cases descriptor.request <;> frame_runtime
  all_goals exact breakFrame_newDestination _ _ _ _ _ _ _

theorem breakFrame_carrierValue (carrier : Carrier) : BreakFrameAction (carrierValue carrier) := by
  cases carrier <;> unfold carrierValue <;> frame_runtime
  exact breakFrame_storedDestination _

theorem breakFrame_singleCarrier (carriers : List Carrier) : BreakFrameAction (singleCarrier carriers) := by
  unfold singleCarrier
  frame_runtime

theorem breakFrame_publishCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    BreakFrameAction (publishCarriers origin carriers) := by
  unfold publishCarriers
  frame_runtime

theorem breakFrame_arrayLength (value : Value) : BreakFrameAction (arrayLength value) := by
  cases value <;> unfold arrayLength <;> frame_runtime
  exact breakFrame_sampledStored _

theorem breakFrame_bindAll (act : Goose.Core.ActId) (scope : Goose.Core.ScopeInst)
    (values : List (Goose.Core.VarId × Value)) : BreakFrameAction (bindAll act scope values) := by
  unfold bindAll
  frame_runtime
  exact breakFrame_bindRoot _ _

theorem breakFrame_emitStdout (bytes : ByteArray) : BreakFrameAction (emitStdout bytes) :=
  breakFrame_liftConstruction _ _

theorem breakFrame_expectInt (value : Value) : BreakFrameAction (expectInt value) := by
  cases value <;> unfold expectInt <;> frame_runtime

theorem breakFrame_expectBool (value : Value) : BreakFrameAction (expectBool value) := by
  cases value <;> unfold expectBool <;> frame_runtime

theorem breakFrame_expectRef (value : Value) : BreakFrameAction (expectRef value) := by
  cases value <;> unfold expectRef <;> frame_runtime

theorem breakFrame_sameIntType (left right : Goose.Core.IntTy) : BreakFrameAction (sameIntType left right) := by
  unfold sameIntType
  frame_runtime

theorem breakFrame_comparable (left right : Value) : BreakFrameAction (comparable left right) := by
  cases left <;> cases right <;> unfold comparable <;> frame_runtime
  exact breakFrame_sameIntType _ _

private theorem breakFrame_updateStorage (id : Goose.Core.StorageId)
    (update : ReceivingStorage → ReceivingStorage) (result : α) :
    BreakFrameAction (do
      let state ← EvalM.get
      let some storage := state.construction.storage[id]? | fault .danglingRoot
      EvalM.set { state with construction := { state.construction with
        storage := state.construction.storage.set! id (update storage) } }
      pure result) := by
  intro state _
  dsimp only [bind, Bind.bind, EvalM.get]
  cases found : state.construction.storage[id]? with
  | none => exact ⟨Nat.le_refl _, rfl⟩
  | some storage => exact ⟨Nat.le_refl _, rfl⟩

theorem breakFrame_writeValuePath (fuel : Nat) (layout : LayoutEnv) (value : Value)
    (path : List Nat) (replacement : Value) :
    BreakFrameAction (writeValuePath fuel layout value path replacement) := by
  induction fuel generalizing value path replacement with
  | zero => exact breakFrame_stop _
  | succ fuel ih =>
      cases path with
      | nil => exact breakFrame_pure _
      | cons index rest =>
          cases value <;> simp only [writeValuePath]
          all_goals repeat' first
            | exact breakFrame_storedPathRun _
            | exact breakFrame_readStoredElement _ _ _ _
            | exact breakFrame_updateStorage _ _ _
            | exact ih _ _ _
            | frame_runtime_step

theorem breakFrame_writeLoc (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (replacement : Value) : BreakFrameAction (writeLoc fuel layout location replacement) := by
  unfold writeLoc
  repeat' first
    | exact breakFrame_writeValuePath _ _ _ _ _
    | exact breakFrame_bindRoot _ _
    | frame_runtime_step

#print axioms breakFrame_liftExcept
#print axioms breakFrame_liftLayout
#print axioms breakFrame_getDestination
#print axioms breakFrame_getStorage
#print axioms breakFrame_receivingLayout
#print axioms breakFrame_listForIn
#print axioms breakFrame_listMapM
#print axioms breakFrame_storedDestination
#print axioms breakFrame_receivingDestination
#print axioms breakFrame_completedDestination
#print axioms breakFrame_completedReceivingDestination
#print axioms breakFrame_finishChannel
#print axioms breakFrame_landCarriersInto
#print axioms breakFrame_finishChannels
#print axioms breakFrame_setObjectOrdinal
#print axioms breakFrame_bindStaticRoot
#print axioms breakFrame_reserveRootObject
#print axioms breakFrame_bindRoot
#print axioms breakFrame_rootOf
#print axioms breakFrame_currentBreak
#print axioms breakFrame_sampledStored
#print axioms breakFrame_storedPathRun
#print axioms breakFrame_readStoredElement
#print axioms breakFrame_readValuePath
#print axioms breakFrame_readLoc
#print axioms breakFrame_receivingAction
#print axioms breakFrame_newDestination
#print axioms breakFrame_channelsFor
#print axioms breakFrame_carrierValue
#print axioms breakFrame_singleCarrier
#print axioms breakFrame_publishCarriers
#print axioms breakFrame_arrayLength
#print axioms breakFrame_bindAll
#print axioms breakFrame_emitStdout
#print axioms breakFrame_expectInt
#print axioms breakFrame_expectBool
#print axioms breakFrame_expectRef
#print axioms breakFrame_sameIntType
#print axioms breakFrame_comparable

#print axioms breakFrame_writeValuePath
#print axioms breakFrame_writeLoc

end Goose.Proofs.ConstructionDelivery
