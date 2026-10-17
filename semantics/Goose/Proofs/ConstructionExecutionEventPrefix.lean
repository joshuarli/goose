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

macro "kernel_events" : tactic => `(tactic|
  (apply keepsEventPrefix_liftConstruction_of_isPrefix
   first
     | with_reducible exact reserveStorage_events_prefix _ _
     | with_reducible exact appendStdout_events_prefix _
     | with_reducible exact adaptDestinationType_events_prefix _ _
     | with_reducible exact restoreReceivingLayout_events_prefix _ _
     | with_reducible exact removeConstructionHeader_events_prefix _
     | with_reducible exact landExitReplacement_events_prefix _
     | with_reducible exact abandonPreservingExit_events_prefix _ _
     | with_reducible exact recordCopy_events_prefix _ _
     | with_reducible exact writeElement_events_prefix _ _
     | with_reducible exact finishDestination_events_prefix _
     | with_reducible exact attachChild_events_prefix _ _
     | with_reducible exact attachExtension_events_prefix _ _
     | with_reducible exact attachElementExtension_events_prefix _ _
     | with_reducible exact publishElementDestination_events_prefix _
     | with_reducible exact retireRepeatedSource_events_prefix _ _
     | with_reducible exact truncateConstructionStorage_events_prefix _ _ _ _ _ _
     | with_reducible exact prepareNamedBinding_events_prefix _ _
     | with_reducible exact fitStagedDestination_events_prefix _
     | with_reducible exact openChild_events_prefix _ _ _
     | with_reducible exact openExtension_events_prefix _ _ _
     | with_reducible exact openElementExtension_events_prefix _ _ _ _ _
     | with_reducible exact openExitReplacement_events_prefix _
     | with_reducible exact openDestination_events_prefix _ _ _ _
     | with_reducible exact openDestinationDirect_events_prefix _ _ _ _
     | with_reducible exact publishOperation_events_prefix _
     | with_reducible exact abandonDestination_events_prefix _
     | with_reducible exact stageDestination_events_prefix _
     | with_reducible exact abandonTree_events_prefix _
     | with_reducible exact adaptConstructionDestination_events_prefix _ _ _
     | with_reducible exact finishConstructionAdaptation_events_prefix _
     | with_reducible exact normalizeProducerDestination_events_prefix _ _
  ))

theorem keepsEventPrefix_newDestination (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (storage : Option Goose.Core.StorageId) (knownCount : Option Nat) :
    KeepsEventPrefix (newDestination layout owner ty request origin storage knownCount) := by
  unfold newDestination
  cases storage with
  | none =>
      apply keepsEventPrefix_bind
      · kernel_events
      · intro storage
        apply keepsEventPrefix_bind
        · exact stateQuery_keepsEventPrefix _ (stateQuery_receivingLayout layout ty)
        · intro receiving; kernel_events
  | some storage =>
      apply keepsEventPrefix_bind
      · exact keepsEventPrefix_pure _
      · intro storage
        apply keepsEventPrefix_bind
        · exact stateQuery_keepsEventPrefix _ (stateQuery_receivingLayout layout ty)
        · intro receiving; kernel_events

theorem keepsEventPrefix_channelsFor (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (results : List ResultDescriptor) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (channelsFor layout owner results origin) := by
  unfold channelsFor
  apply keepsEventPrefix_listMapM
  intro descriptor
  cases descriptor.request with
  | register => exact keepsEventPrefix_pure _
  | value | elementRun =>
      apply keepsEventPrefix_bind
      · exact keepsEventPrefix_newDestination _ _ _ _ _ _ _
      · intro destination; exact keepsEventPrefix_pure _

theorem keepsEventPrefix_publishCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    KeepsEventPrefix (publishCarriers origin carriers) := by kernel_events

theorem keepsEventPrefix_ownerDestination (layout : LayoutEnv) (stored : StoredValue)
    (request : Goose.Core.ConstructionRequest) (count : Option Nat) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (ownerDestination layout stored request count origin) := by
  unfold ownerDestination
  cases stored.destination with
  | none => exact keepsEventPrefix_newDestination _ _ _ _ _ _ _
  | some id =>
      apply keepsEventPrefix_bind
      · exact stateQuery_keepsEventPrefix _ (stateQuery_getDestination id)
      · intro destination
        cases destination.progress <;> first
          | kernel_events
          | exact keepsEventPrefix_newDestination _ _ _ _ _ _ _
          | exact keepsEventPrefix_stop _

theorem keepsEventPrefix_publishOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (stored : StoredValue) (id : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (publishOwner fuel layout location stored id origin) := by
  cases fuel with
  | zero => exact keepsEventPrefix_stop _
  | succ fuel =>
      unfold publishOwner
      apply keepsEventPrefix_bind
      · exact stateQuery_keepsEventPrefix _ (stateQuery_getDestination id)
      · intro destination
        cases destination.use with
        | replacement old => exact keepsEventPrefix_stop _
        | child parent =>
            apply keepsEventPrefix_bind
            · kernel_events
            · intro _
              apply keepsEventPrefix_bind
              · exact stateQuery_keepsEventPrefix _ (stateQuery_storedDestination parent)
              · intro value; exact keepsEventPrefix_writeLoc fuel layout location _
        | receiver =>
            apply keepsEventPrefix_bind
            · exact keepsEventPrefix_publishCarriers _ _
            · intro _
              apply keepsEventPrefix_bind
              · exact stateQuery_keepsEventPrefix _ (stateQuery_getStorage stored.storage)
              · intro receiving; exact keepsEventPrefix_writeLoc fuel layout location _

theorem keepsEventPrefix_repeatElement (fuel : Nat) (layout : LayoutEnv) (parent : Goose.Core.DestinationId)
    (element : Ty) (source : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (repeatElement fuel layout parent element source origin) := by
  cases fuel with
  | zero => exact keepsEventPrefix_stop _
  | succ fuel =>
      unfold repeatElement
      apply keepsEventPrefix_bind
      · exact stateQuery_keepsEventPrefix _ (stateQuery_storedDestination source)
      · intro stored
        apply keepsEventPrefix_bind
        · exact stateQuery_keepsEventPrefix _ (stateQuery_getStorage stored.storage)
        · intro receiving
          apply keepsEventPrefix_bind
          · exact stateQuery_keepsEventPrefix _ (stateQuery_liftLayout _)
          · intro finish
            apply keepsEventPrefix_bind
            · kernel_events
            · intro _; kernel_events

theorem fixed_writes_keepEventPrefix (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (element : Ty) (origin : Goose.Core.OriginId) (values : Array Value) :
    KeepsEventPrefix (forIn values PUnit.unit fun value _ => do
      let bytes ← liftExcept (fixedBytes fuel layout element value)
      liftConstruction origin (writeElement destination bytes)
      pure (.yield PUnit.unit)) := by
  apply keepsEventPrefix_arrayForIn
  intro value _
  apply keepsEventPrefix_bind
  · exact stateQuery_keepsEventPrefix _ (stateQuery_liftExcept _)
  · intro bytes
    apply keepsEventPrefix_bind
    · kernel_events
    · intro _; exact keepsEventPrefix_pure _

theorem packed_writes_keepEventPrefix (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (bytes : ByteArray) (run : SampledRun) (start count : Nat) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (forIn ([0:count] : Std.Legacy.Range) PUnit.unit fun index _ => do
      let (low, high) ← liftLayout (elementInterval fuel layout bytes run (start + index))
      liftConstruction origin (writeElement destination (bytes.extract low high))
      pure (.yield PUnit.unit)) := by
  apply keepsEventPrefix_rangeForIn
  intro index _
  apply keepsEventPrefix_bind
  · exact stateQuery_keepsEventPrefix _ (stateQuery_liftLayout _)
  · intro interval
    rcases interval with ⟨low, high⟩
    simp only
    apply keepsEventPrefix_bind
    · kernel_events
    · intro _; exact keepsEventPrefix_pure _

theorem keepsEventPrefix_copyValue (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (value : Value) (origin : Goose.Core.OriginId) (source : Option Goose.Core.CopySource) :
    KeepsEventPrefix (copyValue fuel layout destination value origin source) := by
  cases fuel with
  | zero => exact keepsEventPrefix_stop _
  | succ fuel =>
      unfold copyValue
      apply keepsEventPrefix_bind
      · exact stateQuery_keepsEventPrefix _ (stateQuery_getDestination destination)
      · intro pending
        cases elementFound : elementType pending.capability.logicalType with
        | none => exact keepsEventPrefix_stop _
        | some element =>
            cases value with
            | int _ _ | bool _ | unit | record _ _ | ref _ => exact keepsEventPrefix_stop _
            | stored stored =>
                apply keepsEventPrefix_bind
                · exact stateQuery_keepsEventPrefix _ (stateQuery_sampledStored stored)
                · intro sampled
                  rcases sampled with ⟨bytes, run⟩
                  simp only
                  split
                  · exact keepsEventPrefix_stop _
                  · apply keepsEventPrefix_bind
                    · kernel_events
                    · intro _
                      apply keepsEventPrefix_bind
                      · simpa only [Nat.zero_add] using packed_writes_keepEventPrefix fuel layout destination bytes run 0 run.count origin
                      · intro _; kernel_events
            | fixed values =>
                cases source with
                | none =>
                    apply keepsEventPrefix_bind
                    · exact fixed_writes_keepEventPrefix fuel layout destination element origin values
                    · intro _; kernel_events
                | some source =>
                    apply keepsEventPrefix_bind
                    · kernel_events
                    · intro _
                      apply keepsEventPrefix_bind
                      · exact fixed_writes_keepEventPrefix fuel layout destination element origin values
                      · intro _; kernel_events
            | slice location start count =>
                apply keepsEventPrefix_bind
                · exact stateQuery_keepsEventPrefix _ (stateQuery_readLoc fuel layout location)
                · intro backing
                  cases source with
                  | none => exact keepsEventPrefix_stop _
                  | some source =>
                      cases backing with
                      | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ => exact keepsEventPrefix_stop _
                      | stored stored =>
                          apply keepsEventPrefix_bind
                          · exact stateQuery_keepsEventPrefix _ (stateQuery_storedPathRun stored)
                          · intro sampled
                            rcases sampled with ⟨bytes, run⟩
                            simp only
                            split
                            · exact keepsEventPrefix_stop _
                            · split
                              · exact keepsEventPrefix_stop _
                              · apply keepsEventPrefix_bind
                                · kernel_events
                                · intro _
                                  apply keepsEventPrefix_bind
                                  · exact packed_writes_keepEventPrefix fuel layout destination bytes run start count origin
                                  · intro _; kernel_events
                      | fixed values =>
                          simp only
                          split
                          · exact keepsEventPrefix_stop _
                          · apply keepsEventPrefix_bind
                            · kernel_events
                            · intro _
                              apply keepsEventPrefix_bind
                              · exact fixed_writes_keepEventPrefix fuel layout destination element origin (values.extract start (start + count))
                              · intro _; kernel_events

theorem keepsEventPrefix_deliverCarriers (fuel : Nat) (layout : LayoutEnv) (channels : List Channel)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (deliverCarriers fuel layout channels carriers origin) := by
  unfold deliverCarriers
  split
  · exact keepsEventPrefix_stop _
  · apply keepsEventPrefix_listMapM
    intro item
    rcases item with ⟨channel, carrier⟩
    cases channel <;> cases carrier <;> first
      | exact keepsEventPrefix_pure _
      | exact keepsEventPrefix_stop _
      | (apply keepsEventPrefix_bind
         · exact keepsEventPrefix_copyValue _ _ _ _ _ _
         · intro _; exact keepsEventPrefix_pure _)

theorem keepsEventPrefix_cleanupDestination (origin : Goose.Core.OriginId)
    (id : Goose.Core.DestinationId) (carriers : List Carrier) :
    KeepsEventPrefix (cleanupDestination origin id carriers) := by
  unfold cleanupDestination
  apply keepsEventPrefix_bind
  · exact stateQuery_keepsEventPrefix _ (stateQuery_getDestination id)
  · intro destination
    split
    · exact keepsEventPrefix_pure _
    · apply keepsEventPrefix_bind
      · exact keepsEventPrefix_get
      · intro state
        split
        · kernel_events
        · split
          · exact keepsEventPrefix_pure _
          · kernel_events

theorem keepsEventPrefix_landCarrier (origin : Goose.Core.OriginId) (carrier : Carrier) :
    KeepsEventPrefix (landCarrier origin carrier) := by
  unfold landCarrier
  cases carrier with
  | register value => exact keepsEventPrefix_pure _
  | completed id =>
      apply keepsEventPrefix_bind
      · exact stateQuery_keepsEventPrefix _ (stateQuery_getDestination id)
      · intro destination
        cases destination.use with
        | replacement old => kernel_events
        | receiver | child parent => exact keepsEventPrefix_pure _

theorem keepsEventPrefix_landCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    KeepsEventPrefix (landCarriers origin carriers) := by
  unfold landCarriers
  apply keepsEventPrefix_bind
  · apply keepsEventPrefix_listForIn
    intro carrier _
    apply keepsEventPrefix_bind
    · exact keepsEventPrefix_landCarrier origin carrier
    · intro _; exact keepsEventPrefix_pure _
  · intro _; exact keepsEventPrefix_pure _

theorem keepsEventPrefix_finishChannel (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (carrier : Carrier) (result : Ty) : KeepsEventPrefix (finishChannel layout origin carrier result) := by
  unfold finishChannel
  cases carrier with
  | register value => exact keepsEventPrefix_pure _
  | completed id =>
      apply keepsEventPrefix_bind
      · exact stateQuery_keepsEventPrefix _ (stateQuery_getDestination id)
      · intro destination
        simp only
        split
        · kernel_events
        · split <;> split
          all_goals
            first
              | kernel_events
              | (apply keepsEventPrefix_bind
                 · kernel_events
                 · intro _
                   apply keepsEventPrefix_bind
                   · exact stateQuery_keepsEventPrefix _ (stateQuery_receivingLayout layout destination.capability.layout)
                   · intro receiving
                     apply keepsEventPrefix_bind
                     · kernel_events
                     · intro _; kernel_events)

theorem keepsEventPrefix_finishChannels (layout : LayoutEnv) (types : List Ty)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (finishChannels layout types carriers origin) := by
  unfold finishChannels
  apply keepsEventPrefix_bind
  · exact keepsEventPrefix_landCarriers origin carriers
  · intro _
    split
    · exact keepsEventPrefix_stop _
    · apply keepsEventPrefix_bind
      · apply keepsEventPrefix_listForIn
        intro item _
        rcases item with ⟨carrier, result⟩
        apply keepsEventPrefix_bind
        · exact keepsEventPrefix_finishChannel layout origin carrier result
        · intro _; exact keepsEventPrefix_pure _
      · intro _; exact keepsEventPrefix_pure _

theorem keepsEventPrefix_truncateOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (count : Nat) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (truncateOwner fuel layout location count origin) := by
  cases fuel with
  | zero => exact keepsEventPrefix_stop _
  | succ fuel =>
      unfold truncateOwner
      apply keepsEventPrefix_bind
      · exact stateQuery_keepsEventPrefix _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact keepsEventPrefix_stop _
        | stored stored =>
            apply keepsEventPrefix_bind
            · exact stateQuery_keepsEventPrefix _ (stateQuery_sampledStored stored)
            · intro sampled
              rcases sampled with ⟨bytes, run⟩
              simp only
              split
              · exact keepsEventPrefix_stop _
              · apply keepsEventPrefix_bind
                · exact stateQuery_keepsEventPrefix _ (stateQuery_liftLayout _)
                · intro finish
                  cases stored.destination with
                  | none =>
                      apply keepsEventPrefix_bind
                      · exact keepsEventPrefix_pure _
                      · intro owner
                        apply keepsEventPrefix_bind
                        · kernel_events
                        · intro _; exact keepsEventPrefix_writeLoc _ _ _ _
                  | some id =>
                      apply keepsEventPrefix_bind
                      · exact stateQuery_keepsEventPrefix _ (stateQuery_getDestination id)
                      · intro pending
                        apply keepsEventPrefix_bind
                        · exact keepsEventPrefix_pure _
                        · intro owner
                          apply keepsEventPrefix_bind
                          · kernel_events
                          · intro _; exact keepsEventPrefix_writeLoc _ _ _ _

theorem keepsEventPrefix_appendFixedValues (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (values : List Value) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (appendFixedValues fuel layout location values origin) := by
  cases fuel with
  | zero => exact keepsEventPrefix_stop _
  | succ fuel =>
      unfold appendFixedValues
      apply keepsEventPrefix_bind
      · exact stateQuery_keepsEventPrefix _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact keepsEventPrefix_stop _
        | stored stored =>
            simp only
            cases elementFound : elementType stored.ty with
            | none => exact keepsEventPrefix_stop _
            | some element =>
                apply keepsEventPrefix_bind
                · apply keepsEventPrefix_listMapM
                  intro value; exact stateQuery_keepsEventPrefix _ (stateQuery_liftExcept _)
                · intro parts
                  apply keepsEventPrefix_bind
                  · exact keepsEventPrefix_ownerDestination _ _ _ _ _
                  · intro destination
                    apply keepsEventPrefix_bind
                    · apply keepsEventPrefix_listForIn
                      intro bytes state
                      apply keepsEventPrefix_bind
                      · kernel_events
                      · intro _; exact keepsEventPrefix_pure _
                    · intro _
                      apply keepsEventPrefix_bind
                      · kernel_events
                      · intro _
                        apply keepsEventPrefix_bind
                        · exact stateQuery_keepsEventPrefix _ (stateQuery_completedDestination destination)
                        · intro completed; exact keepsEventPrefix_publishOwner _ _ _ _ _ _

theorem keepsEventPrefix_appendRun (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (view : RuntimeView) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (appendRun fuel layout location view origin) := by
  cases fuel with
  | zero => exact keepsEventPrefix_stop _
  | succ fuel =>
      unfold appendRun
      apply keepsEventPrefix_bind
      · exact stateQuery_keepsEventPrefix _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact keepsEventPrefix_stop _
        | stored stored =>
            apply keepsEventPrefix_bind
            · exact stateQuery_keepsEventPrefix _ (stateQuery_readLoc fuel layout view.location)
            · intro source
              apply keepsEventPrefix_bind
              · exact keepsEventPrefix_ownerDestination _ _ _ _ _
              · intro destination
                have finish : KeepsEventPrefix (do
                    liftConstruction origin (finishDestination destination)
                    let completed ← completedDestination destination
                    publishOwner fuel layout location stored completed origin) := by
                  apply keepsEventPrefix_bind
                  · kernel_events
                  · intro _
                    apply keepsEventPrefix_bind
                    · exact stateQuery_keepsEventPrefix _ (stateQuery_completedDestination destination)
                    · intro completed; exact keepsEventPrefix_publishOwner _ _ _ _ _ _
                cases source with
                | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ =>
                    apply keepsEventPrefix_bind
                    · exact keepsEventPrefix_stop _
                    · intro _; exact finish
                | stored source =>
                      apply keepsEventPrefix_bind
                      · exact stateQuery_keepsEventPrefix _ (stateQuery_sampledStored source)
                      · intro sampled
                        rcases sampled with ⟨bytes, run⟩
                        apply keepsEventPrefix_bind
                        · kernel_events
                        · intro _
                          apply keepsEventPrefix_bind
                          · exact packed_writes_keepEventPrefix fuel layout destination bytes run view.start view.count origin
                          · intro _; exact finish
                | fixed values =>
                      simp only
                      cases elementFound : elementType stored.ty with
                      | none =>
                          apply keepsEventPrefix_bind
                          · exact keepsEventPrefix_stop _
                          · intro _; exact finish
                      | some element =>
                        apply keepsEventPrefix_bind
                        ·
                          apply keepsEventPrefix_rangeForIn
                          intro index current
                          split
                          · apply keepsEventPrefix_bind
                            · exact stateQuery_keepsEventPrefix _ (stateQuery_liftExcept _)
                            · intro bytes
                              apply keepsEventPrefix_bind
                              · kernel_events
                              · intro _; exact keepsEventPrefix_pure _
                          · apply keepsEventPrefix_bind
                            · exact keepsEventPrefix_stop _
                            · intro _; exact keepsEventPrefix_pure _
                        · intro _; exact finish

theorem keepsEventPrefix_constructLocal (declarations : DeclarationEnv) (owner : Goose.Core.ActId) (ty : Ty)
    (origin : Goose.Core.OriginId) (expression : Expr) (construct : Goose.Core.DestinationId → EvalM Unit)
    (preserved : ∀ destination, KeepsEventPrefix (construct destination)) :
    KeepsEventPrefix (constructLocal declarations owner ty origin expression construct) := by
  unfold constructLocal
  apply keepsEventPrefix_bind
  · exact keepsEventPrefix_newDestination _ _ _ _ _ _ _
  · intro destination
    apply keepsEventPrefix_bind
    · exact preserved destination
    · intro _
      apply keepsEventPrefix_bind
      · exact stateQuery_keepsEventPrefix _ (stateQuery_completedDestination destination)
      · intro completed
        apply keepsEventPrefix_bind
        · exact keepsEventPrefix_publishCarriers _ _
        · intro _; exact keepsEventPrefix_pure _

theorem keepsEventPrefix_exitChannels (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) : KeepsEventPrefix (exitChannels source activation operands origin) := by
  unfold exitChannels
  split
  · exact keepsEventPrefix_stop _
  · apply keepsEventPrefix_listMapM
    intro item
    rcases item with ⟨channel, operand⟩
    cases channel with
    | register ty => exact keepsEventPrefix_pure _
    | construct id =>
        apply keepsEventPrefix_bind
        · exact stateQuery_keepsEventPrefix _ (stateQuery_getDestination id)
        · intro destination
          have finish (alias : Bool) : KeepsEventPrefix
              (if (match destination.progress with | .open 0 => true | _ => false) || alias then
                pure (Channel.construct id)
              else do pure (Channel.construct (← liftConstruction origin (openExitReplacement id)))) := by
            split <;> split
            all_goals first
              | exact keepsEventPrefix_pure _
              | (apply keepsEventPrefix_bind
                 · kernel_events
                 · intro _; exact keepsEventPrefix_pure _)
          cases operand <;> first
            | (apply keepsEventPrefix_bind
               · exact keepsEventPrefix_pure _
               · intro alias; exact finish alias)
            | (apply keepsEventPrefix_bind
               · exact stateQuery_keepsEventPrefix _ (stateQuery_rootOf _ _)
               · intro root
                 apply keepsEventPrefix_bind
                 · exact keepsEventPrefix_get
                 · intro state
                   split
                   all_goals
                     apply keepsEventPrefix_bind
                     · exact keepsEventPrefix_pure _
                     · intro alias; exact finish alias)

theorem keepsEventPrefix_openElementReceiving (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (location : Goose.Core.Loc) (stored : StoredValue) (element : Ty) (known : Option Nat)
    (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (openElementReceiving layout owner location stored element known origin) := by
  unfold openElementReceiving
  apply keepsEventPrefix_bind
  · exact stateQuery_keepsEventPrefix _ (stateQuery_sampledStored stored)
  · intro sampled
    rcases sampled with ⟨bytes, run⟩
    apply keepsEventPrefix_bind
    · exact stateQuery_keepsEventPrefix _ (stateQuery_receivingLayout layout element)
    · intro receiving
      cases stored.destination with
      | none => kernel_events
      | some id =>
          apply keepsEventPrefix_bind
          · exact stateQuery_keepsEventPrefix _ (stateQuery_getDestination id)
          · intro pending
            cases pending.progress <;> first
              | kernel_events
              | exact keepsEventPrefix_stop _

theorem keepsEventPrefix_publishElementReceiving (fuel : Nat) (layout : LayoutEnv)
    (location : Goose.Core.Loc) (stored : StoredValue) (destination : Goose.Core.DestinationId)
    (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (publishElementReceiving fuel layout location stored destination origin) := by
  cases fuel with
  | zero => exact keepsEventPrefix_stop _
  | succ fuel =>
      unfold publishElementReceiving
      apply keepsEventPrefix_bind
      · exact stateQuery_keepsEventPrefix _ (stateQuery_getDestination destination)
      · intro pending
        cases pending.use with
        | replacement _ => exact keepsEventPrefix_stop _
        | child parent =>
            apply keepsEventPrefix_bind
            · kernel_events
            · intro _
              apply keepsEventPrefix_bind
              · exact stateQuery_keepsEventPrefix _ (stateQuery_storedDestination parent)
              · intro value; exact keepsEventPrefix_writeLoc _ _ _ _
        | receiver =>
            apply keepsEventPrefix_bind
            · kernel_events
            · intro _
              apply keepsEventPrefix_bind
              · exact stateQuery_keepsEventPrefix _ (stateQuery_getStorage stored.storage)
              · intro value; exact keepsEventPrefix_writeLoc _ _ _ _

theorem keepsEventPrefix_protectDestination (origin : Goose.Core.OriginId)
    (id : Goose.Core.DestinationId) (action : EvalM α) (kept : KeepsEventPrefix action) :
    KeepsEventPrefix (protectDestination origin id action) := by
  intro state
  have after := kept state
  cases result : action state with
  | ok value final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using after
  | stop reason final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using after
  | escape address carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      have cleaned := eventPrefix_trans _ _ _ after
        (keepsEventPrefix_cleanupDestination origin id carriers final)
      cases cleanup : cleanupDestination origin id carriers final <;>
        simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned
  | jump target kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      cases kind with
      | breakValue carriers =>
          have cleaned := eventPrefix_trans _ _ _ after
            (keepsEventPrefix_cleanupDestination origin id carriers final)
          cases cleanup : cleanupDestination origin id carriers final <;>
            simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned
      | continueLoop =>
          have cleaned := eventPrefix_trans _ _ _ after
            (keepsEventPrefix_cleanupDestination origin id [] final)
          cases cleanup : cleanupDestination origin id [] final <;>
            simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned

theorem keepsEventPrefix_finishActivation (layout : LayoutEnv) (activation : RuntimeActivation)
    (types : List Ty) (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (kept : KeepsEventPrefix action) :
    KeepsEventPrefix (finishActivation layout activation types origin action) := by
  intro state
  have after := kept state
  cases result : action state with
  | ok carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      let trimmed : ExecutionState := { final with
        activations := final.activations.filter (fun current => current.act != activation.act) }
      have completed := eventPrefix_trans _ _ _ after
        (keepsEventPrefix_finishChannels layout types carriers origin trimmed)
      cases finished : finishChannels layout types carriers origin trimmed <;>
        simpa [finishActivation, result, trimmed, finished, Goose.Proofs.Exit.stepState] using completed
  | stop reason final => simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using after
  | jump target kind final => simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using after
  | escape address carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      by_cases caught : address.activation = activation.act
      · let trimmed : ExecutionState := { final with
          activations := final.activations.filter (fun current => current.act != activation.act) }
        have completed := eventPrefix_trans _ _ _ after
          (keepsEventPrefix_finishChannels layout types carriers origin trimmed)
        cases finished : finishChannels layout types carriers origin trimmed <;>
          simpa [finishActivation, result, caught, trimmed, finished, Goose.Proofs.Exit.stepState] using completed
      · simpa [finishActivation, result, caught, Goose.Proofs.Exit.stepState] using after

structure EvaluationKeepsEventPrefix (fuel : Nat) (config : EvalConfig) : Prop where
  value : ∀ environment expression, KeepsEventPrefix (evalValue fuel config environment expression)
  bound : ∀ environment count defaultValue operand, KeepsEventPrefix (evalBound fuel config environment count defaultValue operand)
  place : ∀ environment operand, KeepsEventPrefix (evalPlace fuel config environment operand)
  view : ∀ environment operand, KeepsEventPrefix (evalView fuel config environment operand)
  produce : ∀ environment channels operand, KeepsEventPrefix (evalProduce fuel config environment channels operand)
  operands : ∀ environment channels expressions, KeepsEventPrefix (evalOperands fuel config environment channels expressions)
  build : ∀ environment destination expression, KeepsEventPrefix (buildExpr fuel config environment destination expression)
  element : ∀ environment destination element expression, KeepsEventPrefix (buildElement fuel config environment destination element expression)
  arguments : ∀ environment vars params args, KeepsEventPrefix (evalArguments fuel config environment vars params args)
  call : ∀ environment context args channels origin, KeepsEventPrefix (invokeCall fuel config environment context args channels origin)
  activation : ∀ environment pre body origin, KeepsEventPrefix (enterActivation fuel config environment pre body origin)
  activationBody : ∀ environment pre body, KeepsEventPrefix (execActivationBody fuel config environment pre body)
  resultBlock : ∀ environment channels body, KeepsEventPrefix (execResultBlock fuel config environment channels body)
  resultBlockWith : ∀ environment pre channels body, KeepsEventPrefix (execResultBlockWith fuel config environment pre channels body)
  block : ∀ environment pre channels body, KeepsEventPrefix (execBlock fuel config environment pre channels body)
  statements : ∀ environment statements, KeepsEventPrefix (execStmts fuel config environment statements)
  statement : ∀ environment statement, KeepsEventPrefix (execStmt fuel config environment statement)
  printArgument : ∀ environment argument, KeepsEventPrefix (evalPrintArg fuel config environment argument)
  whileLoop : ∀ environment condition body, KeepsEventPrefix (execWhile fuel config environment condition body)
  rangeLoop : ∀ environment var ty first last body, KeepsEventPrefix (execRange fuel config environment var ty first last body)
  eachLoop : ∀ environment var index byRef body view current, KeepsEventPrefix (execEach fuel config environment var index byRef body view current)
  loop : ∀ environment pre body, KeepsEventPrefix (loopBody fuel config environment pre body)
  push : ∀ environment owner expression origin, KeepsEventPrefix (pushValue fuel config environment owner expression origin)

theorem evaluationKeepsEventPrefix_zero (config : EvalConfig) : EvaluationKeepsEventPrefix 0 config := by
  constructor
  all_goals intros
  all_goals simp [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands,
    buildExpr, buildElement, evalArguments, invokeCall, enterActivation, execActivationBody,
    execResultBlock, execResultBlockWith, execBlock, execStmts, execStmt, evalPrintArg,
    execWhile, execRange, execEach, loopBody, pushValue, timeout, EvalM.stop,
    KeepsEventPrefix, EventPrefix, Goose.Proofs.Exit.stepState, bind]

private theorem evalBound_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (count : Nat) (defaultValue : Int) (operand : Bound) :
    KeepsEventPrefix (evalBound (fuel + 1) config environment count defaultValue operand) := by
  cases operand with
  | omitted => simpa only [evalBound] using keepsEventPrefix_pure defaultValue
  | expr expression | fromEnd expression =>
      simp only [evalBound]
      apply keepsEventPrefix_bind
      · exact previous.value _ _
      · intro value
        apply keepsEventPrefix_bind
        · exact stateQuery_keepsEventPrefix _ (stateQuery_expectInt value)
        · intro pair; exact keepsEventPrefix_pure _

private theorem evalPlace_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation) (operand : Place) :
    KeepsEventPrefix (evalPlace (fuel + 1) config environment operand) := by
  cases operand with
  | var localVar =>
      simp only [evalPlace]
      apply keepsEventPrefix_bind
      · exact stateQuery_keepsEventPrefix _ (stateQuery_rootOf _ _)
      · intro _; exact keepsEventPrefix_pure _
  | global global => simpa only [evalPlace] using keepsEventPrefix_pure (Goose.Core.Loc.mk (.global global) [])
  | deref expression =>
      simp only [evalPlace]
      apply keepsEventPrefix_bind
      · exact previous.value _ _
      · intro value; exact stateQuery_keepsEventPrefix _ (stateQuery_expectRef value)
  | elem view expression origin =>
      simp only [evalPlace]
      apply keepsEventPrefix_bind
      · exact previous.view _ _
      · intro view
        apply keepsEventPrefix_bind
        · exact previous.value _ _
        · intro value
          apply keepsEventPrefix_bind
          · exact stateQuery_keepsEventPrefix _ (stateQuery_expectInt value)
          · intro pair
            rcases pair with ⟨ty, index⟩
            split
            · exact keepsEventPrefix_pure _
            · exact keepsEventPrefix_stop _
  | field place index =>
      simp only [evalPlace]
      apply keepsEventPrefix_bind
      · exact previous.place _ _
      · intro _; exact keepsEventPrefix_pure _

private theorem evalView_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation) (operand : View) :
    KeepsEventPrefix (evalView (fuel + 1) config environment operand) := by
  cases operand with
  | of place =>
      simp only [evalView]
      apply keepsEventPrefix_bind
      · exact previous.place _ _
      · intro location
        apply keepsEventPrefix_bind
        · exact stateQuery_keepsEventPrefix _ (stateQuery_readLoc _ _ _)
        · intro value
          apply keepsEventPrefix_bind
          · exact stateQuery_keepsEventPrefix _ (stateQuery_arrayLength value)
          · intro pair
            rcases pair with ⟨count, dynamic⟩
            exact keepsEventPrefix_pure _
  | val expression =>
      simp only [evalView]
      apply keepsEventPrefix_bind
      · exact previous.value _ _
      · intro value
        cases value <;> first
          | exact keepsEventPrefix_pure _
          | (apply keepsEventPrefix_bind
             · exact stateQuery_keepsEventPrefix _ (stateQuery_arrayLength _)
             · intro pair
               rcases pair with ⟨count, dynamic⟩
               apply keepsEventPrefix_bind
               · exact keepsEventPrefix_freshScope
               · intro index
                 apply keepsEventPrefix_bind
                 · exact keepsEventPrefix_bindRoot _ _
                 · intro _; exact keepsEventPrefix_pure _)

private theorem evalOperands_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr) :
    KeepsEventPrefix (evalOperands (fuel + 1) config environment channels operands) := by
  cases channels <;> cases operands <;> simp only [evalOperands]
  all_goals first
    | exact keepsEventPrefix_pure _
    | exact keepsEventPrefix_stop _
    | (apply keepsEventPrefix_bind
       · exact previous.produce _ _ _
       · intro carriers
         apply keepsEventPrefix_bind
         · exact stateQuery_keepsEventPrefix _ (stateQuery_singleCarrier carriers)
         · intro carrier
           apply keepsEventPrefix_bind
           · exact previous.operands _ _ _
           · intro _; exact keepsEventPrefix_pure _)

private theorem evalPrintArg_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation) (argument : PrintArg) :
    KeepsEventPrefix (evalPrintArg (fuel + 1) config environment argument) := by
  cases argument with
  | text text => simpa only [evalPrintArg] using keepsEventPrefix_pure text.toUTF8
  | expr expression =>
      simp only [evalPrintArg]
      apply keepsEventPrefix_bind
      · exact previous.value _ _
      · intro value; exact stateQuery_keepsEventPrefix _ ((rendering_stateQueries fuel config.layout).1 _ _)
  | view view =>
      simp only [evalPrintArg]
      apply keepsEventPrefix_bind
      · exact previous.view _ _
      · intro view; exact stateQuery_keepsEventPrefix _ ((rendering_stateQueries fuel config.layout).2.2.2 _ _)

private theorem evalArguments_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameters : List Param) (arguments : List Arg) :
    KeepsEventPrefix (evalArguments (fuel + 1) config environment vars parameters arguments) := by
  cases parameters with
  | nil =>
      cases arguments <;> simp only [evalArguments]
      · exact keepsEventPrefix_pure _
      · exact keepsEventPrefix_stop _
  | cons parameter parameters =>
      cases arguments with
      | nil => simpa only [evalArguments, fault] using keepsEventPrefix_stop (Goose.Core.Stop.fault .arity)
      | cons argument arguments =>
          have finish (value : Value) : KeepsEventPrefix (do
              let values ← evalArguments fuel config environment vars parameters arguments
              pure (value :: values)) := by
            apply keepsEventPrefix_bind
            · exact previous.arguments _ _ _ _
            · intro _; exact keepsEventPrefix_pure _
          cases argument with
          | byVal expression =>
              simp only [evalArguments]
              apply keepsEventPrefix_bind
              · exact previous.value _ _
              · intro value; exact finish value
          | byRef mutability place =>
              simp only [evalArguments]
              apply keepsEventPrefix_bind
              · exact previous.place _ _
              · intro location
                apply keepsEventPrefix_bind
                · exact keepsEventPrefix_pure _
                · intro value; exact finish value
          | construct expression =>
              simp only [evalArguments]
              split
              · apply keepsEventPrefix_bind
                · apply keepsEventPrefix_constructLocal
                  intro destination; exact previous.build _ _ _
                · intro carrier
                  apply keepsEventPrefix_bind
                  · exact stateQuery_keepsEventPrefix _ (stateQuery_carrierValue carrier)
                  · intro value; exact finish value
              · apply keepsEventPrefix_bind
                · exact keepsEventPrefix_stop _
                · intro value; exact finish value

private theorem execStmts_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (statements : List Stmt) : KeepsEventPrefix (execStmts (fuel + 1) config environment statements) := by
  cases statements with
  | nil => simpa only [execStmts] using keepsEventPrefix_pure (Flow.normal .unit)
  | cons statement statements =>
      simp only [execStmts]
      apply keepsEventPrefix_bind
      · exact previous.statement _ _
      · intro flow
        cases flow with
        | normal value => exact previous.statements _ _
        | breaking value | continuing => exact keepsEventPrefix_pure _

private theorem execResultBlock_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (body : Block) :
    KeepsEventPrefix (execResultBlock (fuel + 1) config environment channels body) := by
  simpa only [execResultBlock] using previous.resultBlockWith environment [] channels body

private theorem execActivationBody_keepsEventPrefix (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (preserved : KeepsEventPrefix (execResultBlockWith fuel config environment pre environment.channels body)) :
    KeepsEventPrefix (execActivationBody fuel config environment pre body) := by
  unfold execActivationBody
  apply keepsEventPrefix_bind
  · exact preserved
  · intro result
    rcases result with ⟨flow, carriers⟩
    cases flow <;> first | exact keepsEventPrefix_pure _ | exact keepsEventPrefix_stop _

private theorem enterActivation_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (enterActivation (fuel + 1) config environment pre body origin) := by
  simp only [enterActivation]
  split
  · apply keepsEventPrefix_finishActivation
    exact previous.activationBody _ _ _
  · exact keepsEventPrefix_stop _

private theorem keepsEventPrefix_mapActivations (change : RuntimeActivation → RuntimeActivation)
    (action : EvalM α) (kept : KeepsEventPrefix action) :
    KeepsEventPrefix (do
      let state ← EvalM.get
      EvalM.set { state with activations := state.activations.map change }
      action) := by
  intro state
  simpa [EvalM.get, EvalM.set, bind, pure] using
    kept { state with activations := state.activations.map change }

private theorem keepsEventPrefix_fault (kind : Goose.Core.FaultKind) :
    KeepsEventPrefix (fault (α := α) kind) := keepsEventPrefix_stop _

private theorem keepsEventPrefix_timeout : KeepsEventPrefix (timeout (α := α)) := keepsEventPrefix_stop _

private theorem keepsEventPrefix_abortAt (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (abortAt (α := α) kind origin) := keepsEventPrefix_stop _

private theorem keepsEventPrefix_fault_bind (kind : Goose.Core.FaultKind) (next : α → EvalM β) :
    KeepsEventPrefix (fault kind >>= next) := fun _ => eventPrefix_refl _

private theorem keepsEventPrefix_timeout_bind (next : α → EvalM β) :
    KeepsEventPrefix (timeout >>= next) := fun _ => eventPrefix_refl _

private theorem keepsEventPrefix_abortAt_bind (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId)
    (next : α → EvalM β) : KeepsEventPrefix (abortAt kind origin >>= next) := fun _ => eventPrefix_refl _

local syntax "prefix_eval" ident : tactic
macro_rules
  | `(tactic| prefix_eval $previous:ident) => `(tactic|
  repeat' first
    | with_reducible assumption
    | with_reducible exact keepsEventPrefix_pure _
    | with_reducible exact keepsEventPrefix_stop _
    | with_reducible exact keepsEventPrefix_fault _
    | with_reducible exact keepsEventPrefix_timeout
    | with_reducible exact keepsEventPrefix_abortAt _ _
    | with_reducible exact keepsEventPrefix_fault_bind _ _
    | with_reducible exact keepsEventPrefix_timeout_bind _
    | with_reducible exact keepsEventPrefix_abortAt_bind _ _ _
    | with_reducible exact keepsEventPrefix_get
    | kernel_events
    | with_reducible exact keepsEventPrefix_bindRoot _ _
    | with_reducible exact keepsEventPrefix_bindStaticRoot _ _
    | with_reducible exact keepsEventPrefix_reserveRootObject _
    | with_reducible exact keepsEventPrefix_setObjectOrdinal _ _
    | with_reducible exact keepsEventPrefix_newDestination _ _ _ _ _ _ _
    | with_reducible exact keepsEventPrefix_channelsFor _ _ _ _
    | with_reducible exact keepsEventPrefix_freshAct
    | with_reducible exact keepsEventPrefix_freshScope
    | with_reducible exact keepsEventPrefix_returned _ _
    | with_reducible exact keepsEventPrefix_escaped _ _
    | with_reducible exact keepsEventPrefix_jump _ _
    | with_reducible exact keepsEventPrefix_emitStdout _
    | with_reducible exact keepsEventPrefix_publishCarriers _ _
    | with_reducible exact keepsEventPrefix_copyValue _ _ _ _ _ _
    | with_reducible exact keepsEventPrefix_deliverCarriers _ _ _ _ _
    | with_reducible exact keepsEventPrefix_ownerDestination _ _ _ _ _
    | with_reducible exact keepsEventPrefix_publishOwner _ _ _ _ _ _
    | with_reducible exact keepsEventPrefix_openElementReceiving _ _ _ _ _ _ _
    | with_reducible exact keepsEventPrefix_publishElementReceiving _ _ _ _ _ _
    | with_reducible exact keepsEventPrefix_repeatElement _ _ _ _ _ _
    | with_reducible exact keepsEventPrefix_truncateOwner _ _ _ _ _
    | with_reducible exact keepsEventPrefix_appendFixedValues _ _ _ _ _
    | with_reducible exact keepsEventPrefix_appendRun _ _ _ _ _
    | with_reducible exact keepsEventPrefix_writeLoc _ _ _ _
    | with_reducible exact keepsEventPrefix_landCarriers _ _
    | with_reducible exact keepsEventPrefix_bindAll _ _ _
    | with_reducible exact keepsEventPrefix_exitChannels _ _ _ _
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_rootOf _ _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_expectInt _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_expectBool _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_expectRef _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_sameIntType _ _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_comparable _ _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_readLoc _ _ _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_arrayLength _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_getDestination _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_getStorage _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_sampledStored _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_readStoredElement _ _ _ _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_carrierValue _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_singleCarrier _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_completedDestination _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_storedDestination _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_receivingLayout _ _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_getImplementation _ _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_enclosingActivation _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_targetActivation _ _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_currentBreak _ _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_liftExcept _)
    | with_reducible exact stateQuery_keepsEventPrefix _ (stateQuery_liftLayout _)
    | with_reducible exact ($previous).value _ _
    | with_reducible exact ($previous).bound _ _ _ _
    | with_reducible exact ($previous).place _ _
    | with_reducible exact ($previous).view _ _
    | with_reducible exact ($previous).produce _ _ _
    | with_reducible exact ($previous).operands _ _ _
    | with_reducible exact ($previous).build _ _ _
    | with_reducible exact ($previous).element _ _ _ _
    | with_reducible exact ($previous).arguments _ _ _ _
    | with_reducible exact ($previous).call _ _ _ _ _
    | with_reducible exact ($previous).activation _ _ _ _
    | with_reducible exact ($previous).activationBody _ _ _
    | with_reducible exact ($previous).resultBlock _ _ _
    | with_reducible exact ($previous).resultBlockWith _ _ _ _
    | with_reducible exact ($previous).block _ _ _ _
    | with_reducible exact ($previous).statements _ _
    | with_reducible exact ($previous).statement _ _
    | with_reducible exact ($previous).printArgument _ _
    | with_reducible exact ($previous).whileLoop _ _ _
    | with_reducible exact ($previous).rangeLoop _ _ _ _ _ _
    | with_reducible exact ($previous).eachLoop _ _ _ _ _ _ _
    | with_reducible exact ($previous).loop _ _ _
    | with_reducible exact ($previous).push _ _ _ _
    | with_reducible apply keepsEventPrefix_allocateActivation
    | with_reducible apply keepsEventPrefix_mapActivations
    | with_reducible apply keepsEventPrefix_protectDestination
    | with_reducible apply keepsEventPrefix_withScope
    | with_reducible apply keepsEventPrefix_finishActivation
    | with_reducible apply keepsEventPrefix_withBreakTarget
    | with_reducible apply keepsEventPrefix_constructLocal
    | with_reducible apply keepsEventPrefix_bind
    | with_reducible apply keepsEventPrefix_listMapM
    | with_reducible apply keepsEventPrefix_listForIn
    | with_reducible apply keepsEventPrefix_arrayForIn
    | with_reducible apply keepsEventPrefix_rangeForIn
    | with_reducible split
    | with_reducible rfl
    | with_reducible intro)

private theorem evalValue_lit_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (_previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (ty : Goose.Core.IntTy) (value : Int) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.lit ty value)) := by
  simp only [evalValue]
  prefix_eval _previous

private theorem evalValue_bool_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (_previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (value : Bool) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.bool value)) := by
  simp only [evalValue]
  prefix_eval _previous

private theorem evalValue_read_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (place : Place) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.read place)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_ref_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (place : Place) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.ref mutability place)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_slice_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (view : View) (lo hi : Bound) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.slice mutability view lo hi origin)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_len_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (view : View) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.len view)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_un_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.UnOp) (expression : Expr) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.un operation expression origin)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_bin_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.BinOp) (first second : Expr) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.bin operation first second origin)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_cmp_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.CmpOp) (first second : Expr) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.cmp operation first second)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_and_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (first second : Expr) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.and first second)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_or_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (first second : Expr) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.or first second)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_not_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (expression : Expr) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.not expression)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_conv_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (kind : Goose.Core.ConvKind) (target : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.conv kind target expression origin)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_call_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.call context arguments origin)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_push_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Option Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.push owner expression origin)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_pop_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (owner : Place) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.pop owner origin)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_ifE_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.ifE condition yes no origin)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_blockE_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (body : Block) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.blockE body origin)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_arrLit_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.arrLit ty operands origin)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_fill_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (ty : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.fill ty expression origin)) := by
  cases ty <;> simp only [evalValue]
  all_goals prefix_eval previous

private theorem evalValue_structLit_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.structLit ty operands)) := by
  cases ty <;> simp only [evalValue]
  all_goals prefix_eval previous

private theorem evalValue_bytes_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.bytes ty bytes origin)) := by
  cases ty <;> try simp only [evalValue]
  all_goals prefix_eval previous
  case slice mutability element =>
    cases element <;> try simp only [evalValue]
    all_goals prefix_eval previous
    case int ty =>
      cases ty <;> simp only [evalValue]
      all_goals prefix_eval previous

private theorem evalValue_str_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (ty : Ty) (arguments : List PrintArg) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.str ty arguments origin)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_copy_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (ty : Ty) (source : Place) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.copy ty source origin)) := by
  simp only [evalValue]
  prefix_eval previous

private theorem evalValue_resultLocal_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (_previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.resultLocal localVar origin)) := by
  simp only [evalValue]
  prefix_eval _previous

private theorem evalValue_values_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (operands : List Expr) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment (Expr.values operands)) := by
  cases operands with
  | nil => simpa only [evalValue] using keepsEventPrefix_pure Value.unit
  | cons expression operands =>
      cases operands <;> simp only [evalValue]
      all_goals prefix_eval previous

private theorem evalValue_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation) (expression : Expr) :
    KeepsEventPrefix (evalValue (fuel + 1) config environment expression) := by
  cases expression with
  | lit ty value => exact evalValue_lit_keepsEventPrefix_succ fuel config previous environment ty value
  | bool value => exact evalValue_bool_keepsEventPrefix_succ fuel config previous environment value
  | read place => exact evalValue_read_keepsEventPrefix_succ fuel config previous environment place
  | ref mutability place => exact evalValue_ref_keepsEventPrefix_succ fuel config previous environment mutability place
  | slice mutability view lo hi origin => exact evalValue_slice_keepsEventPrefix_succ fuel config previous environment mutability view lo hi origin
  | len view => exact evalValue_len_keepsEventPrefix_succ fuel config previous environment view
  | un operation expression origin => exact evalValue_un_keepsEventPrefix_succ fuel config previous environment operation expression origin
  | bin operation first second origin => exact evalValue_bin_keepsEventPrefix_succ fuel config previous environment operation first second origin
  | cmp operation first second => exact evalValue_cmp_keepsEventPrefix_succ fuel config previous environment operation first second
  | and first second => exact evalValue_and_keepsEventPrefix_succ fuel config previous environment first second
  | or first second => exact evalValue_or_keepsEventPrefix_succ fuel config previous environment first second
  | not expression => exact evalValue_not_keepsEventPrefix_succ fuel config previous environment expression
  | conv kind target expression origin => exact evalValue_conv_keepsEventPrefix_succ fuel config previous environment kind target expression origin
  | call context arguments origin => exact evalValue_call_keepsEventPrefix_succ fuel config previous environment context arguments origin
  | push owner expression origin => exact evalValue_push_keepsEventPrefix_succ fuel config previous environment owner expression origin
  | pop owner origin => exact evalValue_pop_keepsEventPrefix_succ fuel config previous environment owner origin
  | ifE condition yes no origin => exact evalValue_ifE_keepsEventPrefix_succ fuel config previous environment condition yes no origin
  | blockE body origin => exact evalValue_blockE_keepsEventPrefix_succ fuel config previous environment body origin
  | arrLit ty operands origin => exact evalValue_arrLit_keepsEventPrefix_succ fuel config previous environment ty operands origin
  | fill ty expression origin => exact evalValue_fill_keepsEventPrefix_succ fuel config previous environment ty expression origin
  | structLit ty operands => exact evalValue_structLit_keepsEventPrefix_succ fuel config previous environment ty operands
  | bytes ty bytes origin => exact evalValue_bytes_keepsEventPrefix_succ fuel config previous environment ty bytes origin
  | str ty arguments origin => exact evalValue_str_keepsEventPrefix_succ fuel config previous environment ty arguments origin
  | copy ty source origin => exact evalValue_copy_keepsEventPrefix_succ fuel config previous environment ty source origin
  | resultLocal localVar origin => exact evalValue_resultLocal_keepsEventPrefix_succ fuel config previous environment localVar origin
  | values operands => exact evalValue_values_keepsEventPrefix_succ fuel config previous environment operands

private theorem buildElement_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (element : Ty) (expression : Expr) :
    KeepsEventPrefix (buildElement (fuel + 1) config environment destination element expression) := by
  simp only [buildElement]
  prefix_eval previous

private theorem execWhile_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (condition : Expr) (body : Block) :
    KeepsEventPrefix (execWhile (fuel + 1) config environment condition body) := by
  simp only [execWhile]
  prefix_eval previous

private theorem execRange_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (ty : Goose.Core.IntTy) (first last : Int) (body : Block) :
    KeepsEventPrefix (execRange (fuel + 1) config environment var ty first last body) := by
  simp only [execRange]
  prefix_eval previous

private theorem execEach_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block)
    (view : RuntimeView) (current : Nat) :
    KeepsEventPrefix (execEach (fuel + 1) config environment var index byRef body view current) := by
  simp only [execEach]
  prefix_eval previous

private theorem loopBody_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    KeepsEventPrefix (loopBody (fuel + 1) config environment pre body) := by
  simp only [loopBody]
  prefix_eval previous

private theorem pushValue_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (pushValue (fuel + 1) config environment owner expression origin) := by
  simp only [pushValue]
  prefix_eval previous

set_option maxHeartbeats 2000000 in
private theorem evalProduce_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (expression : Expr) :
    KeepsEventPrefix (evalProduce (fuel + 1) config environment channels expression) := by
  cases channels with
  | nil =>
      cases expression <;> simp only [evalProduce]
      all_goals prefix_eval previous
  | cons channel channels =>
      cases channels with
      | nil =>
          cases channel <;> cases expression <;> simp only [evalProduce]
          all_goals prefix_eval previous
      | cons second channels =>
          cases expression <;> simp only [evalProduce]
          all_goals prefix_eval previous

set_option maxHeartbeats 2000000 in
private theorem buildExpr_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (expression : Expr) :
    KeepsEventPrefix (buildExpr (fuel + 1) config environment destination expression) := by
  cases expression <;> try simp only [buildExpr]
  all_goals prefix_eval previous
  case fill ty expression origin =>
    cases ty <;> simp only [buildExpr]
    all_goals prefix_eval previous
  case values operands =>
    cases operands with
    | nil =>
        simp only [buildExpr]
        prefix_eval previous
    | cons expression operands =>
        cases operands <;> simp only [buildExpr]
        all_goals prefix_eval previous

set_option maxHeartbeats 2000000 in
private theorem execStmt_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation) (statement : Stmt) :
    KeepsEventPrefix (execStmt (fuel + 1) config environment statement) := by
  cases statement <;> try simp only [execStmt]
  all_goals prefix_eval previous
  case ifS condition yes no origin =>
    cases no <;> simp only [execStmt]
    all_goals prefix_eval previous

private theorem execBlock_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    KeepsEventPrefix (execBlock (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execBlock]
  prefix_eval previous

private theorem execResultBlockWith_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    KeepsEventPrefix (execResultBlockWith (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execResultBlockWith]
  prefix_eval previous

private theorem invokeCall_keepsEventPrefix_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationKeepsEventPrefix fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) :
    KeepsEventPrefix (invokeCall (fuel + 1) config environment context arguments channels origin) := by
  simp only [invokeCall]
  apply keepsEventPrefix_bind
  · exact stateQuery_keepsEventPrefix _ (stateQuery_getImplementation config context)
  · intro implementation
    rcases implementation with ⟨id, implementation⟩
    split
    · prefix_eval previous
    · apply keepsEventPrefix_bind
      · prefix_eval previous
      · intro callableChannels
        apply keepsEventPrefix_bind
        · exact previous.arguments _ _ _ _
        · intro values
          apply keepsEventPrefix_bind
          · exact keepsEventPrefix_get
          · intro state
            split
            · prefix_eval previous
            · apply keepsEventPrefix_allocateActivation
                (make := fun act => ⟨id, act, implementation.vars, [], callableChannels⟩)
                (action := fun activation => do
                  let carriers ← enterActivation fuel config activation
                    ((implementation.params.toList.zip values).map fun item => (item.1.var, item.2))
                    implementation.body origin
                  deliverCarriers fuel config.layout channels carriers origin)
              intro activation
              prefix_eval previous

theorem evaluation_keepsEventPrefix (fuel : Nat) (config : EvalConfig) :
    EvaluationKeepsEventPrefix fuel config := by
  induction fuel with
  | zero => exact evaluationKeepsEventPrefix_zero config
  | succ fuel previous =>
      refine {
        value := evalValue_keepsEventPrefix_succ fuel config previous
        bound := evalBound_keepsEventPrefix_succ fuel config previous
        place := evalPlace_keepsEventPrefix_succ fuel config previous
        view := evalView_keepsEventPrefix_succ fuel config previous
        produce := evalProduce_keepsEventPrefix_succ fuel config previous
        operands := evalOperands_keepsEventPrefix_succ fuel config previous
        build := buildExpr_keepsEventPrefix_succ fuel config previous
        element := buildElement_keepsEventPrefix_succ fuel config previous
        arguments := evalArguments_keepsEventPrefix_succ fuel config previous
        call := invokeCall_keepsEventPrefix_succ fuel config previous
        activation := enterActivation_keepsEventPrefix_succ fuel config previous
        activationBody := ?_
        resultBlock := execResultBlock_keepsEventPrefix_succ fuel config previous
        resultBlockWith := execResultBlockWith_keepsEventPrefix_succ fuel config previous
        block := execBlock_keepsEventPrefix_succ fuel config previous
        statements := execStmts_keepsEventPrefix_succ fuel config previous
        statement := execStmt_keepsEventPrefix_succ fuel config previous
        printArgument := evalPrintArg_keepsEventPrefix_succ fuel config previous
        whileLoop := execWhile_keepsEventPrefix_succ fuel config previous
        rangeLoop := execRange_keepsEventPrefix_succ fuel config previous
        eachLoop := execEach_keepsEventPrefix_succ fuel config previous
        loop := loopBody_keepsEventPrefix_succ fuel config previous
        push := pushValue_keepsEventPrefix_succ fuel config previous }
      intro environment pre body
      apply execActivationBody_keepsEventPrefix
      exact execResultBlockWith_keepsEventPrefix_succ fuel config previous environment pre environment.channels body

theorem initGlobals_keepsEventPrefix (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId) :
    KeepsEventPrefix (initGlobals fuel config globals) := by
  have previous := evaluation_keepsEventPrefix fuel config
  induction globals with
  | nil => simpa only [initGlobals] using keepsEventPrefix_pure ()
  | cons global globals preserved =>
      simp only [initGlobals]
      prefix_eval previous

theorem runModule_keepsEventPrefix (fuel : Nat) (config : EvalConfig) :
    KeepsEventPrefix (runModule fuel config) := by
  have previous := evaluation_keepsEventPrefix fuel config
  unfold runModule
  apply keepsEventPrefix_bind
  · exact initGlobals_keepsEventPrefix _ _ _
  · intro _
    prefix_eval previous

theorem runModule_terminal_prefix (fuel : Nat) (config : EvalConfig)
    (initial terminal : ExecutionState) (reason : Goose.Core.Stop) (next : Unit → EvalM α)
    (stopped : runModule fuel config initial = .stop reason terminal) :
    EventPrefix initial.construction.events terminal.construction.events ∧
    (runModule fuel config >>= next) initial = .stop reason terminal := by
  have kept := runModule_keepsEventPrefix fuel config initial
  simp only [stopped, Goose.Proofs.Exit.stepState] at kept
  exact ⟨kept, wholeRun_terminal_skips_continuation fuel config initial terminal reason next stopped⟩

end Goose.Proofs.ConstructionExecution
