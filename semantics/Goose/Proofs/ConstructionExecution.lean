import Goose.Construct.Eval
import Goose.Construct.Validate
import Goose.Proofs.Construct
import Goose.Proofs.ExitExecution

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecution
open Goose.Construct
open Goose.Proofs.ExitExecution

def EventPrefix (before after : List Goose.Core.ConstructionEvent) : Prop :=
  ∃ suffix, after = before ++ suffix

theorem eventPrefix_refl (events : List Goose.Core.ConstructionEvent) : EventPrefix events events :=
  ⟨[], by simp⟩

theorem eventPrefix_iff_isPrefix (before after : List Goose.Core.ConstructionEvent) :
    EventPrefix before after ↔ before <+: after := by
  constructor
  · rintro ⟨suffix, equal⟩
    exact ⟨suffix, equal.symm⟩
  · rintro ⟨suffix, equal⟩
    exact ⟨suffix, equal.symm⟩

theorem eventPrefix_trans (before middle after : List Goose.Core.ConstructionEvent)
    (first : EventPrefix before middle) (second : EventPrefix middle after) :
    EventPrefix before after := by
  obtain ⟨left, rfl⟩ := first
  obtain ⟨right, rfl⟩ := second
  exact ⟨left ++ right, by simp [List.append_assoc]⟩

def KeepsEventPrefix (action : EvalM α) : Prop :=
  ∀ state, EventPrefix state.construction.events
    (Goose.Proofs.Exit.stepState (action state)).construction.events

theorem stateQuery_keepsEventPrefix (action : EvalM α)
    (query : Goose.Proofs.ExitExecution.StateQuery action) : KeepsEventPrefix action := by
  intro state
  rw [query state]
  exact eventPrefix_refl _

theorem keepsEventPrefix_pure (value : α) : KeepsEventPrefix (pure value) :=
  stateQuery_keepsEventPrefix _ (Goose.Proofs.ExitExecution.stateQuery_pure value)

theorem keepsEventPrefix_stop (reason : Goose.Core.Stop) : KeepsEventPrefix (EvalM.stop (α := α) reason) :=
  stateQuery_keepsEventPrefix _ (Goose.Proofs.ExitExecution.stateQuery_stop reason)

theorem keepsEventPrefix_get : KeepsEventPrefix EvalM.get :=
  stateQuery_keepsEventPrefix _ Goose.Proofs.ExitExecution.stateQuery_get

theorem keepsEventPrefix_bind (action : EvalM α) (next : α → EvalM β)
    (first : KeepsEventPrefix action) (remaining : ∀ value, KeepsEventPrefix (next value)) :
    KeepsEventPrefix (action >>= next) := by
  intro state
  have keptPrefix := first state
  cases result : action state with
  | ok value final =>
      simp only [bind, result]
      exact eventPrefix_trans _ _ _
        (by simpa only [result, Goose.Proofs.Exit.stepState] using keptPrefix)
        (remaining value final)
  | stop reason final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using keptPrefix
  | escape address carriers final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using keptPrefix
  | jump target kind final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using keptPrefix

theorem keepsEventPrefix_listMapM (action : α → EvalM β) (items : List α)
    (kept : ∀ item, KeepsEventPrefix (action item)) : KeepsEventPrefix (items.mapM action) := by
  induction items with
  | nil => exact keepsEventPrefix_pure []
  | cons head tail remaining =>
      rw [List.mapM_cons]
      apply keepsEventPrefix_bind
      · exact kept head
      · intro value
        apply keepsEventPrefix_bind
        · exact remaining
        · intro _; exact keepsEventPrefix_pure _

theorem keepsEventPrefix_listForIn (action : α → β → EvalM (ForInStep β)) (items : List α)
    (initial : β) (kept : ∀ item current, KeepsEventPrefix (action item current)) :
    KeepsEventPrefix (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact keepsEventPrefix_pure _
  | cons head tail remaining =>
      simp only [List.forIn_cons]
      apply keepsEventPrefix_bind
      · exact kept head initial
      · intro step
        cases step with
        | done value => exact keepsEventPrefix_pure _
        | yield value => exact remaining value

theorem keepsEventPrefix_arrayForIn (action : α → β → EvalM (ForInStep β)) (items : Array α)
    (initial : β) (kept : ∀ item current, KeepsEventPrefix (action item current)) :
    KeepsEventPrefix (forIn items initial action) := by
  rw [← Array.forIn_toList]
  exact keepsEventPrefix_listForIn action items.toList initial kept

theorem keepsEventPrefix_rangeForIn (action : Nat → β → EvalM (ForInStep β))
    (range : Std.Legacy.Range) (initial : β)
    (kept : ∀ item current, KeepsEventPrefix (action item current)) :
    KeepsEventPrefix (forIn range initial action) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact keepsEventPrefix_listForIn action _ initial kept

theorem wholeRun_terminal_skips_continuation (fuel : Nat) (config : EvalConfig)
    (initial terminal : ExecutionState) (reason : Goose.Core.Stop) (next : Unit → EvalM α)
    (stopped : runModule fuel config initial = .stop reason terminal) :
    (runModule fuel config >>= next) initial = .stop reason terminal := by
  simp only [bind, stopped]

theorem keepsEventPrefix_liftConstruction (origin : Goose.Core.OriginId) (action : ConstructionM α)
    (kept : ∀ state, EventPrefix state.events (action state).finalState.events) :
    KeepsEventPrefix (liftConstruction origin action) := by
  intro state
  have keptEvents := kept state.construction
  cases result : action state.construction with
  | ok value final =>
      simpa only [liftConstruction, result, ConstructionResult.finalState,
        Goose.Proofs.Exit.stepState] using keptEvents
  | fault kind final =>
      simpa only [liftConstruction, result, ConstructionResult.finalState,
        Goose.Proofs.Exit.stepState] using keptEvents

theorem keepsEventPrefix_get_bind (next : ExecutionState → EvalM α)
    (kept : ∀ state, EventPrefix state.construction.events
      (Goose.Proofs.Exit.stepState (next state state)).construction.events) :
    KeepsEventPrefix (EvalM.get >>= next) := kept

theorem keepsEventPrefix_liftConstruction_of_isPrefix (origin : Goose.Core.OriginId)
    (action : ConstructionM α)
    (kept : ∀ state, state.events <+: (action state).finalState.events) :
    KeepsEventPrefix (liftConstruction origin action) :=
  keepsEventPrefix_liftConstruction origin action fun state =>
    (eventPrefix_iff_isPrefix _ _).mpr (kept state)

theorem keepsEventPrefix_setObjectOrdinal (root : Goose.Core.RootInst) (ordinal : Goose.Core.StorageId) :
    KeepsEventPrefix (setObjectOrdinal root ordinal) := by
  intro state
  exact eventPrefix_refl _

theorem keepsEventPrefix_bindStaticRoot (root : Goose.Core.RootInst) (value : Value) :
    KeepsEventPrefix (bindStaticRoot root value) := by
  intro state
  exact eventPrefix_refl _

theorem keepsEventPrefix_freshAct : KeepsEventPrefix freshAct := by
  intro state
  exact eventPrefix_refl _

theorem keepsEventPrefix_freshScope : KeepsEventPrefix freshScope := by
  intro state
  exact eventPrefix_refl _

theorem keepsEventPrefix_returned (activation : Goose.Core.ActId) (carriers : List Carrier) :
    KeepsEventPrefix (returned (α := α) activation carriers) := by
  intro state
  exact eventPrefix_refl _

theorem keepsEventPrefix_escaped (address : ExitAddress) (carriers : List Carrier) :
    KeepsEventPrefix (escaped (α := α) address carriers) := by
  intro state
  exact eventPrefix_refl _

theorem keepsEventPrefix_jump (target : Nat) (kind : JumpKind) :
    KeepsEventPrefix (jump (α := α) target kind) := by
  intro state
  exact eventPrefix_refl _

theorem keepsEventPrefix_withScope (activation : RuntimeActivation) (scope scopeInst : Nat)
    (action : EvalM α) (kept : KeepsEventPrefix action) :
    KeepsEventPrefix (withScope activation scope scopeInst action) := by
  intro state
  have keptEvents := kept state
  cases result : action state <;>
    simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind, pure,
      Goose.Proofs.Exit.stepState, releaseScopeState] using keptEvents

theorem keepsEventPrefix_writeValuePath (fuel : Nat) (layout : LayoutEnv)
    (value : Value) (path : List Nat) (replacement : Value) :
    KeepsEventPrefix (writeValuePath fuel layout value path replacement) := by
  induction fuel generalizing value path replacement with
  | zero => exact keepsEventPrefix_stop _
  | succ fuel remaining =>
      cases path with
      | nil => exact keepsEventPrefix_pure _
      | cons index rest =>
          cases value with
          | fixed elements | record id elements =>
              simp only [writeValuePath]
              cases present : elements[index]? with
              | none => exact keepsEventPrefix_stop _
              | some child =>
                  apply keepsEventPrefix_bind
                  · exact remaining child rest replacement
                  · intro written; exact keepsEventPrefix_pure _
          | int _ _ | bool _ | unit | ref _ | slice _ _ _ => exact keepsEventPrefix_stop _
          | stored stored =>
              unfold writeValuePath
              apply keepsEventPrefix_bind
              · exact stateQuery_keepsEventPrefix _ (stateQuery_storedPathRun stored)
              · intro sampled
                rcases sampled with ⟨bytes, run⟩
                simp only
                apply keepsEventPrefix_bind
                · exact stateQuery_keepsEventPrefix _ (stateQuery_liftLayout _)
                · intro interval
                  rcases interval with ⟨start, finish⟩
                  simp only
                  apply keepsEventPrefix_bind
                  · exact stateQuery_keepsEventPrefix _ (stateQuery_readStoredElement fuel layout stored index)
                  · intro child
                    split
                    · split
                      · exact keepsEventPrefix_stop _
                      · apply keepsEventPrefix_bind
                        · exact remaining child rest replacement
                        · intro _; exact keepsEventPrefix_pure _
                    · apply keepsEventPrefix_bind
                      · exact remaining child rest replacement
                      · intro written
                        apply keepsEventPrefix_bind
                        · exact stateQuery_keepsEventPrefix _ (stateQuery_liftExcept _)
                        · intro part
                          split
                          · exact keepsEventPrefix_stop _
                          · apply keepsEventPrefix_get_bind
                            intro state
                            cases present : state.construction.storage[stored.storage]? with
                            | none => exact eventPrefix_refl _
                            | some receiving => exact eventPrefix_refl _

theorem keepsEventPrefix_reserveStorage (origin : Goose.Core.OriginId) (bytes : ByteArray) (count : Nat) :
    KeepsEventPrefix (liftConstruction origin (reserveStorage bytes count)) := by
  apply keepsEventPrefix_liftConstruction
  intro state
  exact eventPrefix_refl _

theorem keepsEventPrefix_reserveRootObject (root : Goose.Core.RootInst) :
    KeepsEventPrefix (reserveRootObject root) := by
  unfold reserveRootObject
  apply keepsEventPrefix_bind
  · exact keepsEventPrefix_get
  · intro state
    split
    · exact keepsEventPrefix_pure _
    · apply keepsEventPrefix_bind
      · exact keepsEventPrefix_reserveStorage _ _ _
      · intro ordinal
        apply keepsEventPrefix_bind
        · exact keepsEventPrefix_setObjectOrdinal _ _
        · intro _; exact keepsEventPrefix_pure _

theorem keepsEventPrefix_bindRoot (root : Goose.Core.RootInst) (value : Value) :
    KeepsEventPrefix (bindRoot root value) := by
  unfold bindRoot
  apply keepsEventPrefix_bind
  · exact keepsEventPrefix_get
  · intro state
    split
    · cases value <;> apply keepsEventPrefix_bind
      all_goals first
        | exact keepsEventPrefix_setObjectOrdinal _ _
        | exact keepsEventPrefix_reserveRootObject _
        | (intro _; exact keepsEventPrefix_bindStaticRoot _ _)
    · exact keepsEventPrefix_bindStaticRoot _ _

theorem keepsEventPrefix_writeLoc (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (replacement : Value) : KeepsEventPrefix (writeLoc fuel layout location replacement) := by
  unfold writeLoc
  apply keepsEventPrefix_bind
  · exact keepsEventPrefix_get
  · intro state
    cases present : state.objects.lookup location.root with
    | none => exact keepsEventPrefix_stop _
    | some value =>
        apply keepsEventPrefix_bind
        · exact keepsEventPrefix_writeValuePath fuel layout value location.path replacement
        · intro written; exact keepsEventPrefix_bindRoot _ _

theorem keepsEventPrefix_withBreakTarget (act : Goose.Core.ActId) (scope : BreakScope)
    (channels : List Channel) (action : EvalM α) (receive : JumpKind → EvalM α)
    (kept : KeepsEventPrefix action) (received : ∀ kind, KeepsEventPrefix (receive kind)) :
    KeepsEventPrefix (withBreakTarget act scope channels action receive) := by
  intro state
  let target : BreakTarget := ⟨state.nextScope, act, scope, channels⟩
  let installed : ExecutionState := { state with
    nextScope := state.nextScope + 1, breaks := target :: state.breaks }
  have keptEvents := kept installed
  cases result : action installed with
  | ok value final =>
      simpa [withBreakTarget, installed, target, result, mapStepState, Goose.Proofs.Exit.stepState] using keptEvents
  | stop reason final =>
      simpa [withBreakTarget, installed, target, result, mapStepState, Goose.Proofs.Exit.stepState] using keptEvents
  | escape address carriers final =>
      simpa [withBreakTarget, installed, target, result, mapStepState, Goose.Proofs.Exit.stepState] using keptEvents
  | jump actual kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at keptEvents
      let removed : ExecutionState := { final with breaks := final.breaks.filter (fun entry => entry.id != state.nextScope) }
      by_cases caught : actual = state.nextScope
      · have after := eventPrefix_trans _ _ _ keptEvents (received kind removed)
        simpa [withBreakTarget, installed, target, result, caught, removed, mapStepState,
          Goose.Proofs.Exit.stepState] using after
      · simpa [withBreakTarget, installed, target, result, caught, removed, mapStepState,
          Goose.Proofs.Exit.stepState] using keptEvents

theorem keepsEventPrefix_releaseScope (environment : RuntimeActivation) (scope scopeInst : Nat) :
    KeepsEventPrefix (releaseScope environment scope scopeInst) := by
  intro state
  exact eventPrefix_refl _

theorem keepsEventPrefix_bindAll (act : Goose.Core.ActId) (scopeInst : Goose.Core.ScopeInst)
    (values : List (Goose.Core.VarId × Value)) : KeepsEventPrefix (bindAll act scopeInst values) := by
  unfold bindAll
  apply keepsEventPrefix_bind
  · apply keepsEventPrefix_listForIn
    intro entry current
    rcases entry with ⟨localVar, value⟩
    apply keepsEventPrefix_bind
    · exact keepsEventPrefix_bindRoot _ _
    · intro _; exact keepsEventPrefix_pure _
  · intro _; exact keepsEventPrefix_pure _

theorem keepsEventPrefix_allocateActivation (make : Goose.Core.ActId → RuntimeActivation)
    (action : RuntimeActivation → EvalM α)
    (kept : ∀ activation, KeepsEventPrefix (action activation)) :
    KeepsEventPrefix (do
      let act ← freshAct
      let activation := make act
      let state ← EvalM.get
      EvalM.set { state with activations := activation :: state.activations }
      action activation) := by
  intro state
  simpa [freshAct, EvalM.get, EvalM.set, bind, pure, Goose.Proofs.Exit.stepState] using
    kept (make state.nextAct)
      { state with nextAct := state.nextAct + 1, activations := make state.nextAct :: state.activations }

theorem keepsEventPrefix_emitStdout (bytes : ByteArray) : KeepsEventPrefix (emitStdout bytes) := by
  apply keepsEventPrefix_liftConstruction
  intro state
  exact eventPrefix_refl _

theorem rejected_publication_preserves_execution (state : ExecutionState)
    (destinations : List Goose.Core.DestinationId) (kind : ConstructionFault)
    (origin : Goose.Core.OriginId)
    (rejected : preflightPublication state.construction destinations = .error kind) :
    liftConstruction origin (publishOperation destinations) state =
      .stop (match kind with
        | .capacity => .abort .capacity origin
        | .storage => .fault .danglingRoot
        | .destination => .fault .unbound
        | .ownership | .protocol => .fault .flow) state := by
  rw [liftConstruction, Goose.Proofs.Construct.publication_rejection_keeps_prefix
    state.construction destinations kind rejected]
  cases kind <;> rfl

theorem terminal_receiver_scope_activation (layout : LayoutEnv) (activation : RuntimeActivation)
    (resultTypes : List Ty) (scope scopeInst : Nat) (origin : Goose.Core.OriginId)
    (destination : Goose.Core.DestinationId) (action : EvalM (List Carrier))
    (state terminal : ExecutionState) (reason : Goose.Core.Stop)
    (stopped : action state = .stop reason terminal) :
    finishActivation layout activation resultTypes origin
      (withScope activation scope scopeInst (protectDestination origin destination action)) state =
        .stop reason terminal := by
  simp [finishActivation, withScope, protectDestination, stopped]

end Goose.Proofs.ConstructionExecution
