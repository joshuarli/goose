import Goose.Proofs.ExitExecutionInvocationValuesNative

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem statementNeverEscapes_completedDestination (destination : Nat) :
    ProducerNeverEscapes (completedDestination destination) := by
  unfold completedDestination
  producer_never_escapes_runtime

macro "statement_native_step" : tactic => `(tactic|
  first
    | exact producerNeverEscapes_newDestination _ _ _ _ _ _ _
    | exact producerNeverEscapes_storedDestination _
    | exact statementNeverEscapes_completedDestination _
    | exact valueNeverEscapes_writeLoc _ _ _ _
    | exact valueNeverEscapes_bindRoot _ _
    | exact valueNeverEscapes_publishCarriers _ _
    | exact valueNeverEscapes_arrayLength _
    | exact producerNeverEscapes_copyValue _ _ _ _ _ _
    | exact producerNeverEscapes_completedReceivingDestination _
    | value_never_escapes_step)

macro "statement_native" : tactic => `(tactic| repeat' statement_native_step)

theorem statementNeverEscapes_emitStdout (bytes : ByteArray) : ProducerNeverEscapes (emitStdout bytes) := by
  exact producerNeverEscapes_liftConstruction _ _

theorem statementNeverEscapes_freshAct : ProducerNeverEscapes freshAct := by
  unfold freshAct
  statement_native

theorem statementNeverEscapes_materializedDestination (fuel : Nat) (layout : LayoutEnv)
    (owner : Goose.Core.ActId) (ty : Ty) (origin : Goose.Core.OriginId) (count : Nat) (value : Value) :
    ProducerNeverEscapes (materializedDestination fuel layout owner ty origin count value) := by
  unfold materializedDestination
  statement_native

theorem statementNeverEscapes_ownerDestination (layout : LayoutEnv) (stored : StoredValue)
    (request : Goose.Core.ConstructionRequest) (count : Option Nat) (origin : Goose.Core.OriginId) :
    ProducerNeverEscapes (ownerDestination layout stored request count origin) := by
  unfold ownerDestination
  statement_native

theorem statementNeverEscapes_openElementReceiving (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (location : Goose.Core.Loc) (stored : StoredValue) (element : Ty) (count : Option Nat)
    (origin : Goose.Core.OriginId) :
    ProducerNeverEscapes (openElementReceiving layout owner location stored element count origin) := by
  unfold openElementReceiving
  statement_native

theorem statementNeverEscapes_restoreCompletedOwner (snapshot : PendingDestination) (destination : Nat)
    (carried : List Nat) : ProducerNeverEscapes (restoreCompletedOwner snapshot destination carried) := by
  unfold restoreCompletedOwner
  statement_native

theorem statementNeverEscapes_publishOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (stored : StoredValue) (destination : Nat) (origin : Goose.Core.OriginId) :
    ProducerNeverEscapes (publishOwner fuel layout location stored destination origin) := by
  cases fuel <;> simp only [publishOwner]
  all_goals statement_native

theorem statementNeverEscapes_publishElementReceiving (fuel : Nat) (layout : LayoutEnv)
    (location : Goose.Core.Loc) (stored : StoredValue) (destination : Nat) (origin : Goose.Core.OriginId) :
    ProducerNeverEscapes (publishElementReceiving fuel layout location stored destination origin) := by
  cases fuel <;> simp only [publishElementReceiving]
  all_goals statement_native

theorem statementNeverEscapes_appendFixedValues (fuel : Nat) (layout : LayoutEnv)
    (location : Goose.Core.Loc) (values : List Value) (origin : Goose.Core.OriginId) :
    ProducerNeverEscapes (appendFixedValues fuel layout location values origin) := by
  cases fuel <;> simp only [appendFixedValues]
  all_goals repeat' first
    | exact statementNeverEscapes_ownerDestination _ _ _ _ _
    | exact statementNeverEscapes_publishOwner _ _ _ _ _ _
    | statement_native_step

theorem statementNeverEscapes_appendRun (fuel : Nat) (layout : LayoutEnv)
    (location : Goose.Core.Loc) (view : RuntimeView) (origin : Goose.Core.OriginId) :
    ProducerNeverEscapes (appendRun fuel layout location view origin) := by
  cases fuel <;> simp only [appendRun]
  all_goals repeat' first
    | exact statementNeverEscapes_ownerDestination _ _ _ _ _
    | exact statementNeverEscapes_publishOwner _ _ _ _ _ _
    | statement_native_step

theorem statementNeverEscapes_stop (reason : Goose.Core.Stop) : ProducerNeverEscapes (EvalM.stop (α := α) reason) := by
  intro state address carriers final impossible
  cases impossible

theorem statementNeverEscapes_currentBreak (act : Goose.Core.ActId) (scope : Option BreakScope) :
    ProducerNeverEscapes (currentBreak act scope) := by
  unfold currentBreak
  statement_native

theorem statementNeverEscapes_jump (target : Nat) (kind : JumpKind) :
    ProducerNeverEscapes (jump (α := α) target kind) := by
  intro state address carriers final impossible
  cases impossible

macro "statement_never_escapes" : tactic => `(tactic|
  repeat' first
    | exact statementNeverEscapes_emitStdout _
    | exact statementNeverEscapes_stop _
    | exact statementNeverEscapes_currentBreak _ _
    | exact statementNeverEscapes_jump _ _
    | exact statementNeverEscapes_freshAct
    | exact statementNeverEscapes_materializedDestination _ _ _ _ _ _ _
    | exact statementNeverEscapes_ownerDestination _ _ _ _ _
    | exact statementNeverEscapes_openElementReceiving _ _ _ _ _ _ _
    | exact statementNeverEscapes_restoreCompletedOwner _ _ _
    | exact statementNeverEscapes_publishOwner _ _ _ _ _ _
    | exact statementNeverEscapes_publishElementReceiving _ _ _ _ _ _
    | exact statementNeverEscapes_appendFixedValues _ _ _ _ _
    | exact statementNeverEscapes_appendRun _ _ _ _ _
    | exact valueNeverEscapes_truncateOwner _ _ _ _ _
    | exact valueNeverEscapes_expectInt _
    | exact valueNeverEscapes_expectBool _
    | exact valueNeverEscapes_expectRef _
    | exact valueNeverEscapes_sameIntType _ _
    | statement_native_step)

end Goose.Proofs.ExitExecution
