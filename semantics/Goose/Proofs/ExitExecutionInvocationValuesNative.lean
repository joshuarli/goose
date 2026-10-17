import Goose.Proofs.ExitExecutionInvocationProducersEscapeSupport

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

macro "value_never_escapes_step" : tactic => `(tactic|
  first
    | with_reducible exact producerNeverEscapes_readLoc _ _ _
    | with_reducible exact producerNeverEscapes_storedPathRun _
    | with_reducible exact producerNeverEscapes_sampledStored _
    | with_reducible exact producerNeverEscapes_readStoredElement _ _ _ _
    | producer_never_escapes_runtime_step)

macro "value_never_escapes" : tactic => `(tactic| repeat' value_never_escapes_step)

theorem valueNeverEscapes_expectInt (value : Value) : ProducerNeverEscapes (expectInt value) := by
  cases value <;> simp only [expectInt] <;> value_never_escapes

theorem valueNeverEscapes_expectBool (value : Value) : ProducerNeverEscapes (expectBool value) := by
  cases value <;> simp only [expectBool] <;> value_never_escapes

theorem valueNeverEscapes_expectRef (value : Value) : ProducerNeverEscapes (expectRef value) := by
  cases value <;> simp only [expectRef] <;> value_never_escapes

theorem valueNeverEscapes_sameIntType (first second : Goose.Core.IntTy) :
    ProducerNeverEscapes (sameIntType first second) := by
  unfold sameIntType
  value_never_escapes

theorem valueNeverEscapes_comparable (first second : Value) : ProducerNeverEscapes (comparable first second) := by
  cases first <;> cases second <;> simp only [comparable]
  all_goals repeat' first | exact valueNeverEscapes_sameIntType _ _ | value_never_escapes_step

theorem valueNeverEscapes_renderValue (value : Value) : ProducerNeverEscapes (renderValue value) := by
  cases value <;> simp only [renderValue] <;> value_never_escapes

theorem valueNeverEscapes_freshScope : ProducerNeverEscapes freshScope := by
  unfold freshScope
  value_never_escapes

theorem valueNeverEscapes_setObjectOrdinal (root : Goose.Core.RootInst) (ordinal : Nat) :
    ProducerNeverEscapes (setObjectOrdinal root ordinal) := by
  unfold setObjectOrdinal
  value_never_escapes

theorem valueNeverEscapes_reserveRootObject (root : Goose.Core.RootInst) :
    ProducerNeverEscapes (reserveRootObject root) := by
  unfold reserveRootObject
  repeat' first | exact valueNeverEscapes_setObjectOrdinal _ _ | value_never_escapes_step

theorem valueNeverEscapes_bindStaticRoot (root : Goose.Core.RootInst) (value : Value) :
    ProducerNeverEscapes (bindStaticRoot root value) := by
  unfold bindStaticRoot
  value_never_escapes

theorem valueNeverEscapes_bindRoot (root : Goose.Core.RootInst) (value : Value) :
    ProducerNeverEscapes (bindRoot root value) := by
  unfold bindRoot
  repeat' first
    | exact valueNeverEscapes_bindStaticRoot _ _
    | exact valueNeverEscapes_reserveRootObject _
    | exact valueNeverEscapes_setObjectOrdinal _ _
    | value_never_escapes_step

theorem valueNeverEscapes_arrayLength (value : Value) : ProducerNeverEscapes (arrayLength value) := by
  unfold arrayLength
  value_never_escapes

theorem valueNeverEscapes_readRun (fuel : Nat) (layout : LayoutEnv) (view : RuntimeView) :
    ProducerNeverEscapes (readRun fuel layout view) := by
  unfold readRun
  value_never_escapes

theorem valueNeverEscapes_getImplementation (config : EvalConfig) (context : Goose.Core.ContextId) :
    ProducerNeverEscapes (getImplementation config context) := by
  unfold getImplementation
  value_never_escapes

theorem valueNeverEscapes_channelsFor (layout : LayoutEnv) (owner : Nat) (results : List ResultDescriptor)
    (origin : Goose.Core.OriginId) : ProducerNeverEscapes (channelsFor layout owner results origin) := by
  unfold channelsFor
  repeat' first | exact producerNeverEscapes_newDestination _ _ _ _ _ _ _ | value_never_escapes_step

theorem valueNeverEscapes_publishCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    ProducerNeverEscapes (publishCarriers origin carriers) := by
  unfold publishCarriers
  value_never_escapes

theorem valueNeverEscapes_writeValuePath (fuel : Nat) (layout : LayoutEnv) (value : Value)
    (path : List Nat) (replacement : Value) : ProducerNeverEscapes (writeValuePath fuel layout value path replacement) := by
  induction fuel generalizing value path with
  | zero => exact producerNeverEscapes_timeout
  | succ fuel ih =>
    cases path with
    | nil => exact producerNeverEscapes_pure _
    | cons index rest =>
      cases value <;> simp only [writeValuePath]
      all_goals repeat' first | exact ih _ _ | value_never_escapes_step

theorem valueNeverEscapes_writeLoc (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc) (value : Value) :
    ProducerNeverEscapes (writeLoc fuel layout location value) := by
  unfold writeLoc
  repeat' first
    | exact valueNeverEscapes_writeValuePath _ _ _ _ _
    | exact valueNeverEscapes_bindRoot _ _
    | value_never_escapes_step

theorem valueNeverEscapes_truncateOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (count : Nat) (origin : Goose.Core.OriginId) : ProducerNeverEscapes (truncateOwner fuel layout location count origin) := by
  cases fuel with
  | zero => exact producerNeverEscapes_timeout
  | succ fuel =>
    simp only [truncateOwner]
    repeat' first | exact valueNeverEscapes_writeLoc _ _ _ _ | value_never_escapes_step

theorem valueNeverEscapes_rendering (fuel : Nat) (layout : LayoutEnv) :
    (∀ position value, ProducerNeverEscapes (renderAny fuel layout position value)) ∧
    (∀ values, ProducerNeverEscapes (renderElements fuel layout values)) ∧
    (∀ position stored, ProducerNeverEscapes (renderStored fuel layout position stored)) ∧
    (∀ position view, ProducerNeverEscapes (renderView fuel layout position view)) := by
  induction fuel with
  | zero => exact ⟨fun _ _ => producerNeverEscapes_timeout, fun _ => producerNeverEscapes_timeout,
      fun _ _ => producerNeverEscapes_timeout, fun _ _ => producerNeverEscapes_timeout⟩
  | succ fuel ih =>
    rcases ih with ⟨any, elements, stored, view⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals intros
    all_goals simp only [renderAny, renderElements, renderStored, renderView]
    all_goals repeat' first
      | exact any _ _
      | exact elements _
      | exact stored _ _
      | exact view _ _
      | exact valueNeverEscapes_renderValue _
      | exact valueNeverEscapes_expectInt _
      | exact valueNeverEscapes_readRun _ _ _
      | value_never_escapes_step

theorem valueNeverEscapes_renderAny (fuel : Nat) (layout : LayoutEnv) (position : RenderPosition) (value : Value) :
    ProducerNeverEscapes (renderAny fuel layout position value) := (valueNeverEscapes_rendering fuel layout).1 _ _

theorem valueNeverEscapes_renderView (fuel : Nat) (layout : LayoutEnv) (position : RenderPosition) (view : RuntimeView) :
    ProducerNeverEscapes (renderView fuel layout position view) := (valueNeverEscapes_rendering fuel layout).2.2.2 _ _

theorem valueNeverEscapes_readStoredElements (fuel : Nat) (layout : LayoutEnv) (stored : StoredValue) (indices : List Nat) :
    ProducerNeverEscapes (indices.mapM (readStoredElement fuel layout stored)) :=
  producerNeverEscapes_listMapM _ _ (fun _ => producerNeverEscapes_readStoredElement _ _ _ _)

theorem valueNeverEscapes_numericResult (ty : Goose.Core.IntTy) (origin : Goose.Core.OriginId)
    (result : Except Goose.Core.NumAbort Int) : ProducerNeverEscapes
      (match result with
      | .ok value => pure (Value.int ty value)
      | .error reason => abortAt (Goose.Core.AbortKind.ofNum reason) origin) := by
  cases result with
  | ok value => exact producerNeverEscapes_pure _
  | error reason => intro state address carriers final impossible; cases impossible

end Goose.Proofs.ExitExecution
