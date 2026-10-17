import Goose.Proofs.ExitExecution
import Goose.Proofs.OwnershipAmbientRuntimeFrames

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

def ActivationChannelsProjection (state : ExecutionState) : List OwnershipActivationChannels :=
  state.activations.map ownershipActivationChannels

def ActivationChannelsOutcome (expected : List OwnershipActivationChannels) :
    ExecutionStep α → Prop
  | .ok _ state | .escape _ _ state | .jump _ _ state =>
      ActivationChannelsProjection state = expected
  | .stop _ _ => True

def PreservesActivationChannels (action : EvalM α) : Prop :=
  ∀ state, FreshActivations state →
    ActivationChannelsOutcome (ActivationChannelsProjection state) (action state)

def ActivationChannelsFrame (action : EvalM α) : Prop :=
  ∀ state, ActivationChannelsProjection (Goose.Proofs.Exit.stepState (action state)) =
    ActivationChannelsProjection state

def FiltersActivationChannels (activation : RuntimeActivation) (action : EvalM α) : Prop :=
  ∀ state, FreshActivations state →
    match action state with
    | .ok _ final | .escape _ _ final =>
        ActivationChannelsProjection final =
          (ActivationChannelsProjection state).filter (fun current => current.act != activation.act)
    | .stop _ _ => True
    | .jump _ _ _ => False

theorem activationChannelsProjection_map (state : ExecutionState)
    (change : RuntimeActivation → RuntimeActivation)
    (unchanged : ∀ activation, ownershipActivationChannels (change activation) = ownershipActivationChannels activation) :
    ActivationChannelsProjection { state with activations := state.activations.map change } =
      ActivationChannelsProjection state := by
  simp only [ActivationChannelsProjection, List.map_map]
  exact List.map_congr_left (fun activation _ => unchanged activation)

theorem activationChannelsProjection_filter (state : ExecutionState) (act : Goose.Core.ActId) :
    ActivationChannelsProjection { state with activations := state.activations.filter (fun current => current.act != act) } =
      (ActivationChannelsProjection state).filter (fun current => current.act != act) := by
  simp only [ActivationChannelsProjection]
  exact (List.filter_map (f := ownershipActivationChannels)
    (p := fun activation => activation.act != act) (l := state.activations)).symm

theorem activationChannelsOutcome_of_frame (expected : List OwnershipActivationChannels)
    (action : EvalM α) (state : ExecutionState)
    (frame : ActivationChannelsProjection (Goose.Proofs.Exit.stepState (action state)) = expected) :
    ActivationChannelsOutcome expected (action state) := by
  cases result : action state with
  | stop reason final => exact True.intro
  | ok value final | escape address value final | jump target value final =>
      simpa [ActivationChannelsOutcome, Goose.Proofs.Exit.stepState, result] using frame

theorem preservesActivationChannels_of_frame (action : EvalM α) (frame : ActivationChannelsFrame action) :
    PreservesActivationChannels action := by
  intro state _
  exact activationChannelsOutcome_of_frame _ action state (frame state)

theorem preservesActivationChannels_of_stateQuery (action : EvalM α) (query : StateQuery action) :
    PreservesActivationChannels action := by
  apply preservesActivationChannels_of_frame
  intro state
  rw [query state]

theorem activationChannelsFrame_of_activations_eq (action : EvalM α)
    (same : ∀ state, (Goose.Proofs.Exit.stepState (action state)).activations = state.activations) :
    ActivationChannelsFrame action := by
  intro state
  simp only [ActivationChannelsProjection, same state]

theorem preservesActivationChannels_stateUpdate (update : ExecutionState → ExecutionState)
    (unchanged : ∀ state, ActivationChannelsProjection (update state) = ActivationChannelsProjection state) :
    PreservesActivationChannels (do
      let state ← EvalM.get
      EvalM.set (update state)) := by
  intro state _
  simp only [EvalM.get, bind, EvalM.set, ActivationChannelsOutcome, unchanged]

theorem preservesActivationChannels_get : PreservesActivationChannels EvalM.get :=
  preservesActivationChannels_of_stateQuery _ stateQuery_get

theorem preservesActivationChannels_freshAct : PreservesActivationChannels freshAct := by
  apply preservesActivationChannels_of_frame
  intro state
  simp [ActivationChannelsProjection, freshAct, EvalM.get, EvalM.set, bind, pure,
    Goose.Proofs.Exit.stepState]

theorem preservesActivationChannels_freshScope : PreservesActivationChannels freshScope := by
  apply preservesActivationChannels_of_frame
  intro state
  simp [ActivationChannelsProjection, freshScope, EvalM.get, EvalM.set, bind, pure,
    Goose.Proofs.Exit.stepState]

theorem preservesActivationChannels_liftConstruction (origin : Goose.Core.OriginId)
    (action : ConstructionM α) : PreservesActivationChannels (liftConstruction origin action) := by
  apply preservesActivationChannels_of_frame
  intro state
  unfold ActivationChannelsProjection liftConstruction
  cases action state.construction <;> rfl

theorem preservesActivationChannels_liftLayout (action : Except LayoutFault α) :
    PreservesActivationChannels (liftLayout action) :=
  preservesActivationChannels_of_stateQuery _ (stateQuery_liftLayout action)

theorem preservesActivationChannels_setObjectOrdinal (root : Goose.Core.RootInst)
    (ordinal : Goose.Core.StorageId) : PreservesActivationChannels (setObjectOrdinal root ordinal) := by
  unfold setObjectOrdinal
  apply preservesActivationChannels_stateUpdate
  intro state
  rfl

theorem preservesActivationChannels_bindStaticRoot (root : Goose.Core.RootInst) (value : Value) :
    PreservesActivationChannels (bindStaticRoot root value) := by
  unfold bindStaticRoot
  exact preservesActivationChannels_stateUpdate (fun current => { current with
    objects := (root, value) :: current.objects.filter (fun entry => entry.1 != root) }) (by intro current; rfl)

theorem preservesActivationChannels_pure (value : α) : PreservesActivationChannels (pure value) := by
  intro state _
  exact rfl

theorem preservesActivationChannels_stop (reason : Goose.Core.Stop) :
    PreservesActivationChannels (EvalM.stop (α := α) reason) := by
  intro state _
  exact True.intro

theorem preservesActivationChannels_fault (kind : Goose.Core.FaultKind) :
    PreservesActivationChannels (fault (α := α) kind) := by
  exact preservesActivationChannels_stop _

theorem preservesActivationChannels_timeout : PreservesActivationChannels (timeout (α := α)) :=
  preservesActivationChannels_stop _

theorem preservesActivationChannels_abortAt (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (abortAt (α := α) kind origin) :=
  preservesActivationChannels_stop _

theorem preservesActivationChannels_bind (action : EvalM α) (next : α → EvalM β)
    (first : PreservesActivationChannels action) (firstFresh : PreservesFresh action)
    (remaining : ∀ value, PreservesActivationChannels (next value)) :
    PreservesActivationChannels (action >>= next) := by
  intro state fresh
  have firstChannels := first state fresh
  have firstFresh := firstFresh state fresh
  cases result : action state with
  | stop reason final => simp [ActivationChannelsOutcome, bind, result]
  | escape address carriers final =>
      simp only [ActivationChannelsOutcome, result] at firstChannels
      simpa [ActivationChannelsOutcome, bind, result] using firstChannels
  | jump target kind final =>
      simp only [ActivationChannelsOutcome, result] at firstChannels
      simpa [ActivationChannelsOutcome, bind, result] using firstChannels
  | ok value final =>
      simp only [ActivationChannelsOutcome, result] at firstChannels
      have firstSame : ActivationChannelsProjection final = ActivationChannelsProjection state := firstChannels
      have finalFresh : FreshActivations final := by
        simpa [Goose.Proofs.Exit.stepState, result] using firstFresh
      have nextChannels := remaining value final finalFresh
      cases nextResult : next value final with
      | stop reason after => simp [ActivationChannelsOutcome, bind, result, nextResult]
      | ok output after | escape address output after | jump target output after =>
          simp only [ActivationChannelsOutcome, nextResult] at nextChannels
          simpa [ActivationChannelsOutcome, bind, result, nextResult] using nextChannels.trans firstSame

theorem preservesActivationChannels_listMapM (action : α → EvalM β) (items : List α)
    (channels : ∀ item, PreservesActivationChannels (action item))
    (fresh : ∀ item, PreservesFresh (action item)) :
    PreservesActivationChannels (items.mapM action) := by
  induction items with
  | nil => exact preservesActivationChannels_pure _
  | cons item rest ih =>
      rw [List.mapM_cons]
      apply preservesActivationChannels_bind
      · exact channels item
      · exact fresh item
      · intro value
        apply preservesActivationChannels_bind
        · exact ih
        · exact preservesFresh_listMapM action rest fresh
        · intro values
          exact preservesActivationChannels_pure _

theorem preservesActivationChannels_listForIn (action : α → β → EvalM (ForInStep β))
    (items : List α) (initial : β)
    (channels : ∀ item value, PreservesActivationChannels (action item value))
    (fresh : ∀ item value, PreservesFresh (action item value)) :
    PreservesActivationChannels (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact preservesActivationChannels_pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply preservesActivationChannels_bind
      · exact channels item initial
      · exact fresh item initial
      · intro step
        cases step with
        | done value => exact preservesActivationChannels_pure _
        | yield value => exact ih value

theorem preservesActivationChannels_arrayForIn (action : α → β → EvalM (ForInStep β))
    (items : Array α) (initial : β)
    (channels : ∀ item value, PreservesActivationChannels (action item value))
    (fresh : ∀ item value, PreservesFresh (action item value)) :
    PreservesActivationChannels (forIn items initial action) := by
  rw [← Array.forIn_toList]
  exact preservesActivationChannels_listForIn action items.toList initial channels fresh

theorem preservesActivationChannels_rangeForIn (action : Nat → β → EvalM (ForInStep β))
    (range : Std.Legacy.Range) (initial : β)
    (channels : ∀ index value, PreservesActivationChannels (action index value))
    (fresh : ∀ index value, PreservesFresh (action index value)) :
    PreservesActivationChannels (forIn range initial action) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact preservesActivationChannels_listForIn action _ initial channels fresh

theorem preservesActivationChannels_conditional (condition : Prop) [Decidable condition]
    (yes no : EvalM α) (left : PreservesActivationChannels yes) (right : PreservesActivationChannels no) :
    PreservesActivationChannels (if condition then yes else no) := by
  split <;> assumption

theorem preservesActivationChannels_mapActivations (change : RuntimeActivation → RuntimeActivation)
    (action : EvalM α)
    (unchanged : ∀ activation, ownershipActivationChannels (change activation) = ownershipActivationChannels activation)
    (body : PreservesActivationChannels action) :
    PreservesActivationChannels (do
      let state ← EvalM.get
      EvalM.set { state with activations := state.activations.map change }
      action) := by
  intro state fresh
  let changed := { state with activations := state.activations.map change }
  have changedFresh : FreshActivations changed := by
    simpa only [changed, EvalM.get, EvalM.set, bind, pure, Goose.Proofs.Exit.stepState] using
      fresh_activations_map state change (fun activation => by
        have equal := congrArg OwnershipActivationChannels.act (unchanged activation)
        exact equal) fresh
  have channels := body changed changedFresh
  cases evaluated : action changed with
  | stop reason final => simp [ActivationChannelsOutcome, EvalM.get, EvalM.set, bind, changed, evaluated]
  | ok value final | escape address value final | jump target value final =>
      have changedProjection : ActivationChannelsProjection changed = ActivationChannelsProjection state := by
        exact activationChannelsProjection_map state change unchanged
      simpa [ActivationChannelsOutcome, EvalM.get, EvalM.set, bind, pure, changed, evaluated, changedProjection] using channels

theorem activationChannelsProjection_releaseScope (state : ExecutionState)
    (activation : RuntimeActivation) (scope scopeInst : Nat) :
    ActivationChannelsProjection (releaseScopeState activation scope scopeInst state) =
      ActivationChannelsProjection state := by
  simp only [ActivationChannelsProjection, releaseScopeState, List.map_map]
  congr 1
  funext current
  dsimp only [Function.comp_apply]
  split <;> rfl

theorem preservesActivationChannels_withScope (activation : RuntimeActivation) (scope scopeInst : Nat)
    (action : EvalM α) (body : PreservesActivationChannels action) :
    PreservesActivationChannels (withScope activation scope scopeInst action) := by
  intro state fresh
  have channels := body state fresh
  cases result : action state with
  | stop reason final => simp [ActivationChannelsOutcome, withScope, result]
  | ok value final | escape address carriers final | jump target kind final =>
      have released : ActivationChannelsProjection (releaseScopeState activation scope scopeInst final) =
          ActivationChannelsProjection final := activationChannelsProjection_releaseScope final activation scope scopeInst
      simpa [ActivationChannelsOutcome, withScope, result, releaseScope, EvalM.get, EvalM.set, bind, pure,
        Goose.Proofs.Exit.stepState, released] using channels

end Goose.Proofs.ExitExecution
