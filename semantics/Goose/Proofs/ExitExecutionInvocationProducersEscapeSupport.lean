import Goose.Proofs.ExitExecutionInvocation

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

abbrev ProducerNeverEscapes (action : EvalM α) : Prop :=
  ∀ (state : ExecutionState) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState),
    action state ≠ .escape address carriers final

theorem producerNeverEscapes_pure (value : α) : ProducerNeverEscapes (pure value) := by
  intro state address carriers final impossible
  cases impossible

theorem producerNeverEscapes_get : ProducerNeverEscapes EvalM.get := by
  intro state address carriers final impossible
  cases impossible

theorem producerNeverEscapes_set (next : ExecutionState) : ProducerNeverEscapes (EvalM.set next) := by
  intro state address carriers final impossible
  cases impossible

theorem producerNeverEscapes_fault (kind : Goose.Core.FaultKind) : ProducerNeverEscapes (fault (α := α) kind) := by
  intro state address carriers final impossible
  cases impossible

theorem producerNeverEscapes_timeout : ProducerNeverEscapes (timeout (α := α)) := by
  intro state address carriers final impossible
  cases impossible

theorem producerNeverEscapes_liftConstruction (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    ProducerNeverEscapes (liftConstruction origin action) := by
  intro state address carriers final impossible
  cases result : action state.construction <;>
    simp only [liftConstruction, result] at impossible <;> cases impossible

theorem producerNeverEscapes_liftLayout (action : Except LayoutFault α) : ProducerNeverEscapes (liftLayout action) := by
  intro state address carriers final impossible
  cases action with
  | ok value => cases impossible
  | error kind => cases kind <;> cases impossible

theorem producerNeverEscapes_liftExcept (action : Except Goose.Core.Stop α) : ProducerNeverEscapes (liftExcept action) := by
  intro state address carriers final impossible
  cases action <;> cases impossible

theorem producerNeverEscapes_bind (action : EvalM α) (next : α → EvalM β)
    (first : ProducerNeverEscapes action) (remaining : ∀ value, ProducerNeverEscapes (next value)) :
    ProducerNeverEscapes (action >>= next) := by
  intro state address carriers final impossible
  cases evaluated : action state with
  | ok value after =>
      exact remaining value after address carriers final (by simpa only [bind, evaluated] using impossible)
  | stop reason after | jump target kind after =>
      simp only [bind, evaluated] at impossible
      cases impossible
  | escape target payload after => exact first state target payload after evaluated

theorem producerNeverEscapes_listMapM (items : List α) (action : α → EvalM β)
    (each : ∀ item, ProducerNeverEscapes (action item)) : ProducerNeverEscapes (items.mapM action) := by
  induction items with
  | nil => exact producerNeverEscapes_pure _
  | cons item rest ih =>
      rw [List.mapM_cons]
      apply producerNeverEscapes_bind
      · exact each item
      · intro value
        apply producerNeverEscapes_bind
        · exact ih
        · intro values; exact producerNeverEscapes_pure _

theorem producerNeverEscapes_listForIn (items : List α) (initial : β)
    (action : α → β → EvalM (ForInStep β))
    (each : ∀ item current, ProducerNeverEscapes (action item current)) :
    ProducerNeverEscapes (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact producerNeverEscapes_pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply producerNeverEscapes_bind
      · exact each item initial
      · intro step
        cases step with
        | done value => exact producerNeverEscapes_pure _
        | yield value => exact ih value

theorem producerNeverEscapes_arrayForIn (items : Array α) (initial : β)
    (action : α → β → EvalM (ForInStep β))
    (each : ∀ item current, ProducerNeverEscapes (action item current)) :
    ProducerNeverEscapes (forIn items initial action) := by
  rw [← Array.forIn_toList]
  exact producerNeverEscapes_listForIn _ _ _ each

theorem producerNeverEscapes_rangeForIn (items : Std.Legacy.Range) (initial : β)
    (action : Nat → β → EvalM (ForInStep β))
    (each : ∀ item current, ProducerNeverEscapes (action item current)) :
    ProducerNeverEscapes (forIn items initial action) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact producerNeverEscapes_listForIn _ _ _ each

macro "producer_never_escapes_step" : tactic => `(tactic|
  first
    | with_reducible assumption
    | with_reducible exact producerNeverEscapes_pure _
    | with_reducible exact producerNeverEscapes_get
    | with_reducible exact producerNeverEscapes_set _
    | with_reducible exact producerNeverEscapes_fault _
    | with_reducible exact producerNeverEscapes_timeout
    | with_reducible exact producerNeverEscapes_liftConstruction _ _
    | with_reducible exact producerNeverEscapes_liftLayout _
    | with_reducible exact producerNeverEscapes_liftExcept _
    | with_reducible apply producerNeverEscapes_bind
    | with_reducible apply producerNeverEscapes_listMapM
    | with_reducible apply producerNeverEscapes_listForIn
    | with_reducible apply producerNeverEscapes_arrayForIn
    | with_reducible apply producerNeverEscapes_rangeForIn
    | dsimp only
    | split
    | intro)

macro "producer_never_escapes_base" : tactic => `(tactic|
  repeat' producer_never_escapes_step)

theorem producerNeverEscapes_getDestination (id : Nat) : ProducerNeverEscapes (getDestination id) := by
  unfold getDestination
  producer_never_escapes_base

theorem producerNeverEscapes_getStorage (id : Nat) : ProducerNeverEscapes (getStorage id) := by
  unfold getStorage
  producer_never_escapes_base

theorem producerNeverEscapes_rootOf (environment : RuntimeActivation) (localVar : Nat) :
    ProducerNeverEscapes (rootOf environment localVar) := by
  unfold rootOf
  producer_never_escapes_base

theorem producerNeverEscapes_receivingLayout (layout : LayoutEnv) (ty : Ty) :
    ProducerNeverEscapes (receivingLayout layout ty) := by
  cases ty <;> simp only [receivingLayout]
  all_goals producer_never_escapes_base

theorem producerNeverEscapes_receivingDestination (id : Nat) : ProducerNeverEscapes (receivingDestination id) :=
  producerNeverEscapes_liftConstruction _ _

theorem producerNeverEscapes_receivingAction (origin : Goose.Core.OriginId) (id : Nat)
    (action : Nat → ConstructionM α) : ProducerNeverEscapes (receivingAction origin id action) :=
  producerNeverEscapes_liftConstruction _ _

macro "producer_never_escapes_runtime_step" : tactic => `(tactic|
  first
    | with_reducible exact producerNeverEscapes_getDestination _
    | with_reducible exact producerNeverEscapes_getStorage _
    | with_reducible exact producerNeverEscapes_rootOf _ _
    | with_reducible exact producerNeverEscapes_receivingLayout _ _
    | with_reducible exact producerNeverEscapes_receivingDestination _
    | with_reducible exact producerNeverEscapes_receivingAction _ _ _
    | producer_never_escapes_step)

macro "producer_never_escapes_runtime" : tactic => `(tactic|
  repeat' producer_never_escapes_runtime_step)

theorem producerNeverEscapes_completedReceivingDestination (id : Nat) :
    ProducerNeverEscapes (completedReceivingDestination id) := by
  unfold completedReceivingDestination completedDestination
  producer_never_escapes_runtime

theorem producerNeverEscapes_sampledStored (stored : StoredValue) : ProducerNeverEscapes (sampledStored stored) := by
  unfold sampledStored
  producer_never_escapes_runtime

theorem producerNeverEscapes_storedPathRun (stored : StoredValue) : ProducerNeverEscapes (storedPathRun stored) := by
  unfold storedPathRun
  apply producerNeverEscapes_bind
  · exact producerNeverEscapes_sampledStored _
  · intro value; producer_never_escapes_runtime

theorem producerNeverEscapes_readStoredElement (fuel : Nat) (layout : LayoutEnv) (stored : StoredValue) (index : Nat) :
    ProducerNeverEscapes (readStoredElement fuel layout stored index) := by
  unfold readStoredElement
  apply producerNeverEscapes_bind
  · exact producerNeverEscapes_storedPathRun _
  · intro value; producer_never_escapes_runtime

theorem producerNeverEscapes_readValuePath (fuel : Nat) (layout : LayoutEnv) (value : Value) (path : List Nat) :
    ProducerNeverEscapes (readValuePath fuel layout value path) := by
  induction fuel generalizing value path with
  | zero => exact producerNeverEscapes_timeout
  | succ fuel ih =>
      cases path with
      | nil => exact producerNeverEscapes_pure _
      | cons index rest =>
          simp only [readValuePath]
          cases value
          all_goals repeat' first
            | exact ih _ _
            | exact producerNeverEscapes_readStoredElement _ _ _ _
            | producer_never_escapes_runtime_step

theorem producerNeverEscapes_readLoc (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc) :
    ProducerNeverEscapes (readLoc fuel layout location) := by
  unfold readLoc
  apply producerNeverEscapes_bind
  · exact producerNeverEscapes_get
  · intro state
    split
    · exact producerNeverEscapes_readValuePath _ _ _ _
    · exact producerNeverEscapes_fault _

theorem producerNeverEscapes_newDestination (layout : LayoutEnv) (owner : Nat) (ty : Ty)
    (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (storage : Option Nat) (knownCount : Option Nat) :
    ProducerNeverEscapes (newDestination layout owner ty request origin storage knownCount) := by
  unfold newDestination
  producer_never_escapes_runtime

theorem producerNeverEscapes_storedDestination (id : Nat) : ProducerNeverEscapes (storedDestination id) := by
  unfold storedDestination
  producer_never_escapes_runtime

theorem producerNeverEscapes_carrierValue (carrier : Carrier) : ProducerNeverEscapes (carrierValue carrier) := by
  cases carrier <;> simp only [carrierValue]
  all_goals repeat' first | exact producerNeverEscapes_storedDestination _ | producer_never_escapes_runtime_step

theorem producerNeverEscapes_singleCarrier (carriers : List Carrier) : ProducerNeverEscapes (singleCarrier carriers) := by
  unfold singleCarrier
  producer_never_escapes_runtime

theorem producerNeverEscapes_cleanupReceivingDestination (origin : Goose.Core.OriginId) (id : Nat) (carriers : List Carrier) :
    ProducerNeverEscapes (cleanupReceivingDestination origin id carriers) := by
  unfold cleanupReceivingDestination cleanupDestination
  producer_never_escapes_runtime

theorem producerNeverEscapes_exitSource (environment : RuntimeActivation) (id : Nat) (expression : Expr) :
    ProducerNeverEscapes (exitSource environment id expression) := by
  unfold exitSource
  producer_never_escapes_runtime

theorem producerNeverEscapes_selectCompletionChannel (environment : RuntimeActivation) (expression : Expr) (channel : Channel) :
    ProducerNeverEscapes (selectCompletionChannel environment expression channel) := by
  cases channel <;> simp only [selectCompletionChannel]
  all_goals repeat' first | exact producerNeverEscapes_exitSource _ _ _ | producer_never_escapes_runtime_step

theorem producerNeverEscapes_prepareNamedCarrierAt (origin : Goose.Core.OriginId) (token id : Nat) (stored : StoredValue) :
    ProducerNeverEscapes (prepareNamedCarrierAt origin token id stored) := by
  unfold prepareNamedCarrierAt
  producer_never_escapes_runtime

theorem producerNeverEscapes_prepareNamedCarrier (origin : Goose.Core.OriginId) (id : Nat) (stored : StoredValue) :
    ProducerNeverEscapes (prepareNamedCarrier origin id stored) := by
  unfold prepareNamedCarrier
  producer_never_escapes_runtime

theorem producerNeverEscapes_copyValue (fuel : Nat) (layout : LayoutEnv) (destination : Nat) (value : Value)
    (origin : Goose.Core.OriginId) (source : Option Goose.Core.CopySource) :
    ProducerNeverEscapes (copyValue fuel layout destination value origin source) := by
  cases fuel with
  | zero => exact producerNeverEscapes_timeout
  | succ fuel =>
      simp only [copyValue]
      repeat' first
        | exact producerNeverEscapes_readLoc _ _ _
        | exact producerNeverEscapes_sampledStored _
        | exact producerNeverEscapes_storedPathRun _
        | producer_never_escapes_runtime_step

theorem producerNeverEscapes_repeatElement (fuel : Nat) (layout : LayoutEnv) (destination : Nat) (element : Ty)
    (source : Nat) (origin : Goose.Core.OriginId) :
    ProducerNeverEscapes (repeatElement fuel layout destination element source origin) := by
  cases fuel with
  | zero => exact producerNeverEscapes_timeout
  | succ fuel =>
      simp only [repeatElement]
      repeat' first | exact producerNeverEscapes_storedDestination _ | producer_never_escapes_runtime_step

end Goose.Proofs.ExitExecution
