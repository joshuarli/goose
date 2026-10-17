import Goose.Construct.Eval
import Goose.Construct.Validate
import Goose.Proofs.Construct
import Goose.Proofs.ExitExecution

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecution
open Goose.Construct
open Goose.Proofs.ExitExecution

def ConstructionBegins (state : ExecutionState) : Prop := DestinationBegins state.construction

def PreservesConstructionBegins (action : EvalM α) : Prop :=
  ∀ state, ConstructionBegins state → ConstructionBegins (Goose.Proofs.Exit.stepState (action state))

theorem stateQuery_preservesConstructionBegins (action : EvalM α) (query : StateQuery action) :
    PreservesConstructionBegins action := by
  intro state valid
  rw [query state]
  exact valid

theorem preservesConstructionBegins_lift (origin : Goose.Core.OriginId) (action : ConstructionM α)
    (preserved : PreservesDestinationBegins action) :
    PreservesConstructionBegins (liftConstruction origin action) := by
  intro state valid
  have after := preserved state.construction valid
  cases result : action state.construction <;>
    simpa only [ConstructionBegins, liftConstruction, result, ConstructionResult.finalState,
      Goose.Proofs.Exit.stepState] using after

macro "kernel_begins" : tactic => `(tactic|
  (with_reducible apply preservesConstructionBegins_lift
   with_reducible exact FramesDestinationBegins.preserves _ (reserveStorage_destination_begins_frame _ _)))

theorem preservesConstructionBegins_pure (value : α) : PreservesConstructionBegins (pure value) := by
  intro state fresh
  exact fresh

theorem preservesConstructionBegins_stop (reason : Goose.Core.Stop) :
    PreservesConstructionBegins (EvalM.stop (α := α) reason) := by
  intro state fresh
  exact fresh

theorem preservesConstructionBegins_get : PreservesConstructionBegins EvalM.get := by
  intro state fresh
  exact fresh

theorem preservesConstructionBegins_get_bind (next : ExecutionState → EvalM α)
    (preserved : ∀ state, ConstructionBegins state →
      ConstructionBegins (Goose.Proofs.Exit.stepState (next state state))) :
    PreservesConstructionBegins (EvalM.get >>= next) := preserved

theorem preservesConstructionBegins_bind (action : EvalM α) (next : α → EvalM β)
    (first : PreservesConstructionBegins action) (remaining : ∀ value, PreservesConstructionBegins (next value)) :
    PreservesConstructionBegins (action >>= next) := by
  intro state fresh
  have preserved := first state fresh
  cases result : action state with
  | ok value final =>
      simp only [result, Goose.Proofs.Exit.stepState] at preserved
      simpa only [bind, result] using remaining value final preserved
  | stop reason final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved
  | escape target carriers final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved
  | jump target kind final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved

theorem preservesConstructionBegins_listMapM (action : α → EvalM β) (items : List α)
    (preserved : ∀ item, PreservesConstructionBegins (action item)) : PreservesConstructionBegins (items.mapM action) := by
  induction items with
  | nil => exact preservesConstructionBegins_pure _
  | cons item rest ih =>
      rw [List.mapM_cons]
      apply preservesConstructionBegins_bind
      · exact preserved item
      · intro value
        apply preservesConstructionBegins_bind
        · exact ih
        · intro values; exact preservesConstructionBegins_pure _

theorem preservesConstructionBegins_listForIn (action : α → β → EvalM (ForInStep β)) (items : List α)
    (initial : β) (preserved : ∀ item value, PreservesConstructionBegins (action item value)) :
    PreservesConstructionBegins (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact preservesConstructionBegins_pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply preservesConstructionBegins_bind
      · exact preserved item initial
      · intro step
        cases step with
        | done value => exact preservesConstructionBegins_pure _
        | yield value => exact ih value

theorem preservesConstructionBegins_arrayForIn (action : α → β → EvalM (ForInStep β)) (items : Array α)
    (initial : β) (preserved : ∀ item value, PreservesConstructionBegins (action item value)) :
    PreservesConstructionBegins (forIn items initial action) := by
  rw [← Array.forIn_toList]
  exact preservesConstructionBegins_listForIn action items.toList initial preserved

theorem preservesConstructionBegins_rangeForIn (action : Nat → β → EvalM (ForInStep β))
    (range : Std.Legacy.Range) (initial : β)
    (preserved : ∀ index value, PreservesConstructionBegins (action index value)) :
    PreservesConstructionBegins (forIn range initial action) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact preservesConstructionBegins_listForIn action _ initial preserved

theorem preservesConstructionBegins_setObjectOrdinal (root : Goose.Core.RootInst) (ordinal : Goose.Core.StorageId) :
    PreservesConstructionBegins (setObjectOrdinal root ordinal) := by
  intro state fresh
  exact fresh

theorem preservesConstructionBegins_bindStaticRoot (root : Goose.Core.RootInst) (value : Value) :
    PreservesConstructionBegins (bindStaticRoot root value) := by
  intro state fresh
  exact fresh

theorem preservesConstructionBegins_reserveRootObject (root : Goose.Core.RootInst) : PreservesConstructionBegins (reserveRootObject root) := by
  unfold reserveRootObject
  apply preservesConstructionBegins_bind
  · exact preservesConstructionBegins_get
  · intro state
    cases state.objectOrdinals.lookup root with
    | some ordinal => exact preservesConstructionBegins_pure _
    | none =>
        apply preservesConstructionBegins_bind
        · kernel_begins
        · intro ordinal
          apply preservesConstructionBegins_bind
          · exact preservesConstructionBegins_setObjectOrdinal root ordinal
          · intro _; exact preservesConstructionBegins_pure _

theorem preservesConstructionBegins_bindRoot (root : Goose.Core.RootInst) (value : Value) : PreservesConstructionBegins (bindRoot root value) := by
  unfold bindRoot
  apply preservesConstructionBegins_bind
  · exact preservesConstructionBegins_get
  · intro state
    split
    · cases value <;> apply preservesConstructionBegins_bind
      all_goals first
        | exact preservesConstructionBegins_setObjectOrdinal _ _
        | exact preservesConstructionBegins_reserveRootObject _
        | (intro _
           apply preservesConstructionBegins_bind
           · exact preservesConstructionBegins_pure _
           · intro _; exact preservesConstructionBegins_bindStaticRoot root _)
        | (intro _; exact preservesConstructionBegins_bindStaticRoot root _)
    · exact preservesConstructionBegins_bindStaticRoot root value

theorem preservesConstructionBegins_writeValuePath (fuel : Nat) (layout : LayoutEnv)
    (value : Value) (path : List Nat) (replacement : Value) :
    PreservesConstructionBegins (writeValuePath fuel layout value path replacement) := by
  induction fuel generalizing value path replacement with
  | zero => exact preservesConstructionBegins_stop _
  | succ fuel ih =>
      cases path with
      | nil => exact preservesConstructionBegins_pure _
      | cons index rest =>
          cases value with
          | fixed elements | record id elements =>
              simp only [writeValuePath]
              cases present : elements[index]? with
              | none => exact preservesConstructionBegins_stop _
              | some child =>
                  apply preservesConstructionBegins_bind
                  · exact ih child rest replacement
                  · intro written; exact preservesConstructionBegins_pure _
          | int _ _ | bool _ | unit | ref _ | slice _ _ _ => exact preservesConstructionBegins_stop _
          | stored stored =>
              unfold writeValuePath
              apply preservesConstructionBegins_bind
              · exact stateQuery_preservesConstructionBegins _ (stateQuery_storedPathRun stored)
              · intro sampled
                rcases sampled with ⟨bytes, run⟩
                simp only
                apply preservesConstructionBegins_bind
                · exact stateQuery_preservesConstructionBegins _ (stateQuery_liftLayout _)
                · intro interval
                  rcases interval with ⟨start, finish⟩
                  simp only
                  apply preservesConstructionBegins_bind
                  · exact stateQuery_preservesConstructionBegins _ (stateQuery_readStoredElement fuel layout stored index)
                  · intro child
                    split
                    · split
                      · exact preservesConstructionBegins_stop _
                      · apply preservesConstructionBegins_bind
                        · exact ih child rest replacement
                        · intro _; exact preservesConstructionBegins_pure _
                    · apply preservesConstructionBegins_bind
                      · exact ih child rest replacement
                      · intro written
                        apply preservesConstructionBegins_bind
                        · exact stateQuery_preservesConstructionBegins _ (stateQuery_liftExcept _)
                        · intro part
                          split
                          · exact preservesConstructionBegins_stop _
                          · apply preservesConstructionBegins_get_bind
                            intro state fresh
                            cases present : state.construction.storage[stored.storage]? with
                            | none => exact fresh
                            | some receiving => exact fresh

theorem preservesConstructionBegins_writeLoc (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (replacement : Value) : PreservesConstructionBegins (writeLoc fuel layout location replacement) := by
  unfold writeLoc
  apply preservesConstructionBegins_bind
  · exact preservesConstructionBegins_get
  · intro state
    cases present : state.objects.lookup location.root with
    | none => exact preservesConstructionBegins_stop _
    | some value =>
        apply preservesConstructionBegins_bind
        · exact preservesConstructionBegins_writeValuePath fuel layout value location.path replacement
        · intro written; exact preservesConstructionBegins_bindRoot location.root written

theorem preservesConstructionBegins_bindAll (act : Goose.Core.ActId) (scopeInst : Goose.Core.ScopeInst)
    (values : List (Goose.Core.VarId × Value)) : PreservesConstructionBegins (bindAll act scopeInst values) := by
  unfold bindAll
  apply preservesConstructionBegins_bind
  · apply preservesConstructionBegins_listForIn
    intro item _
    rcases item with ⟨localVar, value⟩
    apply preservesConstructionBegins_bind
    · exact preservesConstructionBegins_bindRoot _ value
    · intro _; exact preservesConstructionBegins_pure _
  · intro _; exact preservesConstructionBegins_pure _

theorem preservesConstructionBegins_freshAct : PreservesConstructionBegins freshAct :=
  fun _ valid => valid

theorem preservesConstructionBegins_freshScope : PreservesConstructionBegins freshScope :=
  fun _ valid => valid

theorem preservesConstructionBegins_returned (act : Goose.Core.ActId) (carriers : List Carrier) :
    PreservesConstructionBegins (returned (α := α) act carriers) := fun _ valid => valid

theorem preservesConstructionBegins_escaped (address : ExitAddress) (carriers : List Carrier) :
    PreservesConstructionBegins (escaped (α := α) address carriers) := fun _ valid => valid

theorem preservesConstructionBegins_jump (target : Nat) (kind : JumpKind) :
    PreservesConstructionBegins (jump (α := α) target kind) := fun _ valid => valid

theorem constructionBegins_scope_release (state : ExecutionState) (environment : RuntimeActivation)
    (scope scopeInst : Nat) (valid : ConstructionBegins state) :
    ConstructionBegins (releaseScopeState environment scope scopeInst state) := valid

theorem constructionBegins_activation_filter (state : ExecutionState)
    (predicate : RuntimeActivation → Bool) (valid : ConstructionBegins state) :
    ConstructionBegins { state with activations := state.activations.filter predicate } := valid

macro "kernel_begin_frame" : tactic => `(tactic|
  (with_reducible apply preservesConstructionBegins_lift
   first
     | with_reducible exact FramesDestinationBegins.preserves _ (reserveStorage_destination_begins_frame _ _)
     | with_reducible exact FramesDestinationBegins.preserves _ (appendStdout_destination_begins_frame _)
     | with_reducible exact FramesDestinationBegins.preserves _ (adaptDestinationType_destination_begins_frame _ _)
     | with_reducible exact FramesDestinationBegins.preserves _ (restoreReceivingLayout_destination_begins_frame _ _)
     | with_reducible exact FramesDestinationBegins.preserves _ (removeConstructionHeader_destination_begins_frame _)
     | with_reducible exact FramesDestinationBegins.preserves _ (landExitReplacement_destination_begins_frame _)
     | with_reducible exact FramesDestinationBegins.preserves _ (abandonPreservingExit_destination_begins_frame _ _)
     | with_reducible exact FramesDestinationBegins.preserves _ (recordCopy_destination_begins_frame _ _)
     | with_reducible exact FramesDestinationBegins.preserves _ (writeElement_destination_begins_frame _ _)
     | with_reducible exact FramesDestinationBegins.preserves _ (finishDestination_destination_begins_frame _)
     | with_reducible exact FramesDestinationBegins.preserves _ (attachChild_destination_begins_frame _ _)
     | with_reducible exact FramesDestinationBegins.preserves _ (attachExtension_destination_begins_frame _ _)
     | with_reducible exact FramesDestinationBegins.preserves _ (attachElementExtension_destination_begins_frame _ _)
     | with_reducible exact FramesDestinationBegins.preserves _ (publishElementDestination_destination_begins_frame _)
     | with_reducible exact FramesDestinationBegins.preserves _ (retireRepeatedSource_destination_begins_frame _ _)
     | with_reducible exact FramesDestinationBegins.preserves _ (truncateConstructionStorage_destination_begins_frame _ _ _ _ _ _)
     | with_reducible exact FramesDestinationBegins.preserves _ (prepareNamedBinding_destination_begins_frame _ _)
     | with_reducible exact FramesDestinationBegins.preserves _ (fitStagedDestination_destination_begins_frame _)
     | with_reducible exact FramesDestinationBegins.preserves _ (publishOperation_destination_begins_frame _)
     | with_reducible exact FramesDestinationBegins.preserves _ (abandonDestination_destination_begins_frame _)
     | with_reducible exact FramesDestinationBegins.preserves _ (stageDestination_destination_begins_frame _)
     | with_reducible exact FramesDestinationBegins.preserves _ (abandonTree_destination_begins_frame _)
     | with_reducible exact FramesDestinationBegins.preserves _ (adaptConstructionDestination_destination_begins_frame _ _ _)
     | with_reducible exact FramesDestinationBegins.preserves _ (finishConstructionAdaptation_destination_begins_frame _)
     | with_reducible exact FramesDestinationBegins.preserves _ (normalizeProducerDestination_destination_begins_frame _ _)
  ))

theorem preservesConstructionBegins_publishCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    PreservesConstructionBegins (publishCarriers origin carriers) := by
  unfold publishCarriers
  kernel_begin_frame

theorem preservesConstructionBegins_publishOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (stored : StoredValue) (id : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (publishOwner fuel layout location stored id origin) := by
  cases fuel with
  | zero => exact preservesConstructionBegins_stop _
  | succ fuel =>
      unfold publishOwner
      apply preservesConstructionBegins_bind
      · exact stateQuery_preservesConstructionBegins _ (stateQuery_getDestination id)
      · intro destination
        cases destination.use with
        | replacement old => exact preservesConstructionBegins_stop _
        | child parent =>
            apply preservesConstructionBegins_bind
            · kernel_begin_frame
            · intro _
              apply preservesConstructionBegins_bind
              · exact stateQuery_preservesConstructionBegins _ (stateQuery_storedDestination parent)
              · intro value; exact preservesConstructionBegins_writeLoc fuel layout location _
        | receiver =>
            apply preservesConstructionBegins_bind
            · exact preservesConstructionBegins_publishCarriers _ _
            · intro _
              apply preservesConstructionBegins_bind
              · exact stateQuery_preservesConstructionBegins _ (stateQuery_getStorage stored.storage)
              · intro receiving; exact preservesConstructionBegins_writeLoc fuel layout location _

theorem preservesConstructionBegins_repeatElement (fuel : Nat) (layout : LayoutEnv) (parent : Goose.Core.DestinationId)
    (element : Ty) (source : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (repeatElement fuel layout parent element source origin) := by
  cases fuel with
  | zero => exact preservesConstructionBegins_stop _
  | succ fuel =>
      unfold repeatElement
      apply preservesConstructionBegins_bind
      · exact stateQuery_preservesConstructionBegins _ (stateQuery_storedDestination source)
      · intro stored
        apply preservesConstructionBegins_bind
        · exact stateQuery_preservesConstructionBegins _ (stateQuery_getStorage stored.storage)
        · intro receiving
          apply preservesConstructionBegins_bind
          · exact stateQuery_preservesConstructionBegins _ (stateQuery_liftLayout _)
          · intro finish
            apply preservesConstructionBegins_bind
            · kernel_begin_frame
            · intro _; kernel_begin_frame

theorem fixed_writes_preserveConstructionBegins (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (element : Ty) (origin : Goose.Core.OriginId) (values : Array Value) :
    PreservesConstructionBegins (forIn values PUnit.unit fun value _ => do
      let bytes ← liftExcept (fixedBytes fuel layout element value)
      liftConstruction origin (writeElement destination bytes)
      pure (.yield PUnit.unit)) := by
  apply preservesConstructionBegins_arrayForIn
  intro value _
  apply preservesConstructionBegins_bind
  · exact stateQuery_preservesConstructionBegins _ (stateQuery_liftExcept _)
  · intro bytes
    apply preservesConstructionBegins_bind
    · kernel_begin_frame
    · intro _; exact preservesConstructionBegins_pure _

theorem packed_writes_preserveConstructionBegins (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (bytes : ByteArray) (run : SampledRun) (start count : Nat) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (forIn ([0:count] : Std.Legacy.Range) PUnit.unit fun index _ => do
      let (low, high) ← liftLayout (elementInterval fuel layout bytes run (start + index))
      liftConstruction origin (writeElement destination (bytes.extract low high))
      pure (.yield PUnit.unit)) := by
  apply preservesConstructionBegins_rangeForIn
  intro index _
  apply preservesConstructionBegins_bind
  · exact stateQuery_preservesConstructionBegins _ (stateQuery_liftLayout _)
  · intro interval
    rcases interval with ⟨low, high⟩
    simp only
    apply preservesConstructionBegins_bind
    · kernel_begin_frame
    · intro _; exact preservesConstructionBegins_pure _

theorem preservesConstructionBegins_copyValue (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (value : Value) (origin : Goose.Core.OriginId) (source : Option Goose.Core.CopySource) :
    PreservesConstructionBegins (copyValue fuel layout destination value origin source) := by
  cases fuel with
  | zero => exact preservesConstructionBegins_stop _
  | succ fuel =>
      unfold copyValue
      apply preservesConstructionBegins_bind
      · exact stateQuery_preservesConstructionBegins _ (stateQuery_getDestination destination)
      · intro pending
        cases elementFound : elementType pending.capability.logicalType with
        | none => exact preservesConstructionBegins_stop _
        | some element =>
            cases value with
            | int _ _ | bool _ | unit | record _ _ | ref _ => exact preservesConstructionBegins_stop _
            | stored stored =>
                apply preservesConstructionBegins_bind
                · exact stateQuery_preservesConstructionBegins _ (stateQuery_sampledStored stored)
                · intro sampled
                  rcases sampled with ⟨bytes, run⟩
                  simp only
                  split
                  · exact preservesConstructionBegins_stop _
                  · apply preservesConstructionBegins_bind
                    · kernel_begin_frame
                    · intro _
                      apply preservesConstructionBegins_bind
                      · simpa only [Nat.zero_add] using packed_writes_preserveConstructionBegins fuel layout destination bytes run 0 run.count origin
                      · intro _; kernel_begin_frame
            | fixed values =>
                cases source with
                | none =>
                    apply preservesConstructionBegins_bind
                    · exact fixed_writes_preserveConstructionBegins fuel layout destination element origin values
                    · intro _; kernel_begin_frame
                | some source =>
                    apply preservesConstructionBegins_bind
                    · kernel_begin_frame
                    · intro _
                      apply preservesConstructionBegins_bind
                      · exact fixed_writes_preserveConstructionBegins fuel layout destination element origin values
                      · intro _; kernel_begin_frame
            | slice location start count =>
                apply preservesConstructionBegins_bind
                · exact stateQuery_preservesConstructionBegins _ (stateQuery_readLoc fuel layout location)
                · intro backing
                  cases source with
                  | none => exact preservesConstructionBegins_stop _
                  | some source =>
                      cases backing with
                      | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ => exact preservesConstructionBegins_stop _
                      | stored stored =>
                          apply preservesConstructionBegins_bind
                          · exact stateQuery_preservesConstructionBegins _ (stateQuery_storedPathRun stored)
                          · intro sampled
                            rcases sampled with ⟨bytes, run⟩
                            simp only
                            split
                            · exact preservesConstructionBegins_stop _
                            · split
                              · exact preservesConstructionBegins_stop _
                              · apply preservesConstructionBegins_bind
                                · kernel_begin_frame
                                · intro _
                                  apply preservesConstructionBegins_bind
                                  · exact packed_writes_preserveConstructionBegins fuel layout destination bytes run start count origin
                                  · intro _; kernel_begin_frame
                      | fixed values =>
                          simp only
                          split
                          · exact preservesConstructionBegins_stop _
                          · apply preservesConstructionBegins_bind
                            · kernel_begin_frame
                            · intro _
                              apply preservesConstructionBegins_bind
                              · exact fixed_writes_preserveConstructionBegins fuel layout destination element origin (values.extract start (start + count))
                              · intro _; kernel_begin_frame

theorem preservesConstructionBegins_deliverCarriers (fuel : Nat) (layout : LayoutEnv) (channels : List Channel)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (deliverCarriers fuel layout channels carriers origin) := by
  unfold deliverCarriers
  split
  · exact preservesConstructionBegins_stop _
  · apply preservesConstructionBegins_listMapM
    intro item
    rcases item with ⟨channel, carrier⟩
    cases channel <;> cases carrier <;> first
      | exact preservesConstructionBegins_pure _
      | exact preservesConstructionBegins_stop _
      | (apply preservesConstructionBegins_bind
         · exact preservesConstructionBegins_copyValue _ _ _ _ _ _
         · intro _; exact preservesConstructionBegins_pure _)

theorem preservesConstructionBegins_cleanupDestination (origin : Goose.Core.OriginId)
    (id : Goose.Core.DestinationId) (carriers : List Carrier) :
    PreservesConstructionBegins (cleanupDestination origin id carriers) := by
  unfold cleanupDestination
  apply preservesConstructionBegins_bind
  · exact stateQuery_preservesConstructionBegins _ (stateQuery_getDestination id)
  · intro destination
    split
    · exact preservesConstructionBegins_pure _
    · apply preservesConstructionBegins_bind
      · exact preservesConstructionBegins_get
      · intro state
        split
        · kernel_begin_frame
        · split
          · exact preservesConstructionBegins_pure _
          · kernel_begin_frame

theorem preservesConstructionBegins_protectDestination (origin : Goose.Core.OriginId)
    (id : Goose.Core.DestinationId) (action : EvalM α) (preserved : PreservesConstructionBegins action) :
    PreservesConstructionBegins (protectDestination origin id action) := by
  intro state valid
  have after := preserved state valid
  cases result : action state with
  | ok value final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using after
  | stop reason final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      have cleaned := preservesConstructionBegins_cleanupDestination origin id carriers final after
      cases cleanup : cleanupDestination origin id carriers final <;>
        simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned
  | jump target kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      cases kind with
      | breakValue carriers =>
          have cleaned := preservesConstructionBegins_cleanupDestination origin id carriers final after
          cases cleanup : cleanupDestination origin id carriers final <;>
            simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned
      | continueLoop =>
          have cleaned := preservesConstructionBegins_cleanupDestination origin id [] final after
          cases cleanup : cleanupDestination origin id [] final <;>
            simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned

theorem preservesConstructionBegins_landCarrier (origin : Goose.Core.OriginId) (carrier : Carrier) :
    PreservesConstructionBegins (landCarrier origin carrier) := by
  unfold landCarrier
  cases carrier with
  | register value => exact preservesConstructionBegins_pure _
  | completed id =>
      apply preservesConstructionBegins_bind
      · exact stateQuery_preservesConstructionBegins _ (stateQuery_getDestination id)
      · intro destination
        cases destination.use with
        | replacement old => kernel_begin_frame
        | receiver | child parent => exact preservesConstructionBegins_pure _

theorem preservesConstructionBegins_landCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    PreservesConstructionBegins (landCarriers origin carriers) := by
  unfold landCarriers
  apply preservesConstructionBegins_bind
  · apply preservesConstructionBegins_listForIn
    intro carrier _
    apply preservesConstructionBegins_bind
    · exact preservesConstructionBegins_landCarrier origin carrier
    · intro _; exact preservesConstructionBegins_pure _
  · intro _; exact preservesConstructionBegins_pure _

theorem preservesConstructionBegins_finishChannel (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (carrier : Carrier) (result : Ty) : PreservesConstructionBegins (finishChannel layout origin carrier result) := by
  unfold finishChannel
  cases carrier with
  | register value => exact preservesConstructionBegins_pure _
  | completed id =>
      apply preservesConstructionBegins_bind
      · exact stateQuery_preservesConstructionBegins _ (stateQuery_getDestination id)
      · intro destination
        simp only
        split
        · kernel_begin_frame
        · split <;> split
          all_goals
            first
              | kernel_begin_frame
              | (apply preservesConstructionBegins_bind
                 · kernel_begin_frame
                 · intro _
                   apply preservesConstructionBegins_bind
                   · exact stateQuery_preservesConstructionBegins _ (stateQuery_receivingLayout layout destination.capability.layout)
                   · intro receiving
                     apply preservesConstructionBegins_bind
                     · kernel_begin_frame
                     · intro _; kernel_begin_frame)

theorem preservesConstructionBegins_finishChannels (layout : LayoutEnv) (types : List Ty)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (finishChannels layout types carriers origin) := by
  unfold finishChannels
  apply preservesConstructionBegins_bind
  · exact preservesConstructionBegins_landCarriers origin carriers
  · intro _
    split
    · exact preservesConstructionBegins_stop _
    · apply preservesConstructionBegins_bind
      · apply preservesConstructionBegins_listForIn
        intro item _
        rcases item with ⟨carrier, result⟩
        apply preservesConstructionBegins_bind
        · exact preservesConstructionBegins_finishChannel layout origin carrier result
        · intro _; exact preservesConstructionBegins_pure _
      · intro _; exact preservesConstructionBegins_pure _

theorem preservesConstructionBegins_withScope (activation : RuntimeActivation) (scope scopeInst : Nat)
    (action : EvalM α) (preserved : PreservesConstructionBegins action) :
    PreservesConstructionBegins (withScope activation scope scopeInst action) := by
  intro state valid
  have after := preserved state valid
  cases result : action state with
  | ok value final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using constructionBegins_scope_release final activation scope scopeInst after
  | stop reason final =>
      simpa [withScope, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using constructionBegins_scope_release final activation scope scopeInst after
  | jump target kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using constructionBegins_scope_release final activation scope scopeInst after

theorem preservesConstructionBegins_finishActivation (layout : LayoutEnv) (activation : RuntimeActivation)
    (types : List Ty) (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (preserved : PreservesConstructionBegins action) :
    PreservesConstructionBegins (finishActivation layout activation types origin action) := by
  intro state valid
  have after := preserved state valid
  cases result : action state with
  | ok carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      let trimmed : ExecutionState := { final with
        activations := final.activations.filter (fun current => current.act != activation.act) }
      have trimmedValid : ConstructionBegins trimmed := constructionBegins_activation_filter final _ after
      have landedValid := preservesConstructionBegins_finishChannels layout types carriers origin trimmed trimmedValid
      cases finished : finishChannels layout types carriers origin trimmed <;>
        simpa [finishActivation, result, trimmed, finished, Goose.Proofs.Exit.stepState] using landedValid
  | stop reason final =>
      simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using after
  | jump target kind final =>
      simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      by_cases caught : target.activation = activation.act
      · let trimmed : ExecutionState := { final with
          activations := final.activations.filter (fun current => current.act != activation.act) }
        have trimmedValid : ConstructionBegins trimmed := constructionBegins_activation_filter final _ after
        have landedValid := preservesConstructionBegins_finishChannels layout types carriers origin trimmed trimmedValid
        cases finished : finishChannels layout types carriers origin trimmed <;>
          simpa [finishActivation, result, caught, trimmed, finished, Goose.Proofs.Exit.stepState] using landedValid
      · simpa [finishActivation, result, caught, Goose.Proofs.Exit.stepState] using
          constructionBegins_activation_filter final (fun current => current.act != activation.act) after

theorem preservesConstructionBegins_withBreakTarget (act : Goose.Core.ActId) (scope : BreakScope)
    (channels : List Channel) (action : EvalM α) (receive : JumpKind → EvalM α)
    (preserved : PreservesConstructionBegins action) (received : ∀ kind, PreservesConstructionBegins (receive kind)) :
    PreservesConstructionBegins (withBreakTarget act scope channels action receive) := by
  intro state valid
  let target : BreakTarget := ⟨state.nextScope, act, scope, channels⟩
  let installed : ExecutionState := { state with
    nextScope := state.nextScope + 1, breaks := target :: state.breaks }
  have installedValid : ConstructionBegins installed := valid
  have after := preserved installed installedValid
  cases result : action installed with
  | ok value final =>
      simpa [withBreakTarget, installed, target, result, mapStepState, Goose.Proofs.Exit.stepState, ConstructionBegins] using after
  | stop reason final =>
      simpa [withBreakTarget, installed, target, result, mapStepState, Goose.Proofs.Exit.stepState, ConstructionBegins] using after
  | escape activation carriers final =>
      simpa [withBreakTarget, installed, target, result, mapStepState, Goose.Proofs.Exit.stepState, ConstructionBegins] using after
  | jump actual kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      let removed : ExecutionState := { final with breaks := final.breaks.filter (fun entry => entry.id != state.nextScope) }
      have removedValid : ConstructionBegins removed := after
      by_cases caught : actual = state.nextScope
      · simpa [withBreakTarget, installed, target, result, caught, removed, mapStepState,
          Goose.Proofs.Exit.stepState] using received kind removed removedValid
      · simpa [withBreakTarget, installed, target, result, caught, removed, mapStepState,
          Goose.Proofs.Exit.stepState] using removedValid

theorem preservesConstructionBegins_truncateOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (count : Nat) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (truncateOwner fuel layout location count origin) := by
  cases fuel with
  | zero => exact preservesConstructionBegins_stop _
  | succ fuel =>
      unfold truncateOwner
      apply preservesConstructionBegins_bind
      · exact stateQuery_preservesConstructionBegins _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact preservesConstructionBegins_stop _
        | stored stored =>
            apply preservesConstructionBegins_bind
            · exact stateQuery_preservesConstructionBegins _ (stateQuery_sampledStored stored)
            · intro sampled
              rcases sampled with ⟨bytes, run⟩
              simp only
              split
              · exact preservesConstructionBegins_stop _
              · apply preservesConstructionBegins_bind
                · exact stateQuery_preservesConstructionBegins _ (stateQuery_liftLayout _)
                · intro finish
                  cases stored.destination with
                  | none =>
                      apply preservesConstructionBegins_bind
                      · exact preservesConstructionBegins_pure _
                      · intro owner
                        apply preservesConstructionBegins_bind
                        · kernel_begin_frame
                        · intro _; exact preservesConstructionBegins_writeLoc _ _ _ _
                  | some id =>
                      apply preservesConstructionBegins_bind
                      · exact stateQuery_preservesConstructionBegins _ (stateQuery_getDestination id)
                      · intro pending
                        apply preservesConstructionBegins_bind
                        · exact preservesConstructionBegins_pure _
                        · intro owner
                          apply preservesConstructionBegins_bind
                          · kernel_begin_frame
                          · intro _; exact preservesConstructionBegins_writeLoc _ _ _ _

theorem preservesConstructionBegins_publishElementReceiving (fuel : Nat) (layout : LayoutEnv)
    (location : Goose.Core.Loc) (stored : StoredValue) (destination : Goose.Core.DestinationId)
    (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (publishElementReceiving fuel layout location stored destination origin) := by
  cases fuel with
  | zero => exact preservesConstructionBegins_stop _
  | succ fuel =>
      unfold publishElementReceiving
      apply preservesConstructionBegins_bind
      · exact stateQuery_preservesConstructionBegins _ (stateQuery_getDestination destination)
      · intro pending
        cases pending.use with
        | replacement _ => exact preservesConstructionBegins_stop _
        | child parent =>
            apply preservesConstructionBegins_bind
            · kernel_begin_frame
            · intro _
              apply preservesConstructionBegins_bind
              · exact stateQuery_preservesConstructionBegins _ (stateQuery_storedDestination parent)
              · intro value; exact preservesConstructionBegins_writeLoc _ _ _ _
        | receiver =>
            apply preservesConstructionBegins_bind
            · kernel_begin_frame
            · intro _
              apply preservesConstructionBegins_bind
              · exact stateQuery_preservesConstructionBegins _ (stateQuery_getStorage stored.storage)
              · intro value; exact preservesConstructionBegins_writeLoc _ _ _ _

macro "kernel_begin_operation" : tactic => `(tactic|
  first
    | kernel_begin_frame
    | (with_reducible apply preservesConstructionBegins_lift
       first
         | with_reducible exact openDestination_destination_begins _ _ _ _
         | with_reducible exact openDestinationDirect_destination_begins _ _ _ _
         | with_reducible exact openChild_destination_begins _ _ _
         | with_reducible exact openExtension_destination_begins _ _ _
         | with_reducible exact openElementExtension_destination_begins _ _ _ _ _
         | with_reducible exact openExitReplacement_destination_begins _))

theorem preservesConstructionBegins_emitStdout (bytes : ByteArray) :
    PreservesConstructionBegins (emitStdout bytes) := by
  unfold emitStdout
  kernel_begin_frame

theorem preservesConstructionBegins_allocateActivation (make : Goose.Core.ActId → RuntimeActivation)
    (action : RuntimeActivation → EvalM α)
    (preserved : ∀ activation, PreservesConstructionBegins (action activation)) :
    PreservesConstructionBegins (do
      let act ← freshAct
      let activation := make act
      let state ← EvalM.get
      EvalM.set { state with activations := activation :: state.activations }
      action activation) := by
  intro state valid
  simpa [freshAct, EvalM.get, EvalM.set, bind, pure, ConstructionBegins] using
    preserved (make state.nextAct)
      { state with nextAct := state.nextAct + 1, activations := make state.nextAct :: state.activations } valid

theorem preservesConstructionBegins_newDestination (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (storage : Option Goose.Core.StorageId) (knownCount : Option Nat) :
    PreservesConstructionBegins (newDestination layout owner ty request origin storage knownCount) := by
  unfold newDestination
  cases storage with
  | none =>
      apply preservesConstructionBegins_bind
      · kernel_begin_operation
      · intro storage
        apply preservesConstructionBegins_bind
        · exact stateQuery_preservesConstructionBegins _ (stateQuery_receivingLayout layout ty)
        · intro receiving; kernel_begin_operation
  | some storage =>
      apply preservesConstructionBegins_bind
      · exact preservesConstructionBegins_pure _
      · intro storage
        apply preservesConstructionBegins_bind
        · exact stateQuery_preservesConstructionBegins _ (stateQuery_receivingLayout layout ty)
        · intro receiving; kernel_begin_operation

theorem preservesConstructionBegins_channelsFor (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (results : List ResultDescriptor) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (channelsFor layout owner results origin) := by
  unfold channelsFor
  apply preservesConstructionBegins_listMapM
  intro descriptor
  cases descriptor.request with
  | register => exact preservesConstructionBegins_pure _
  | value | elementRun =>
      apply preservesConstructionBegins_bind
      · exact preservesConstructionBegins_newDestination _ _ _ _ _ _ _
      · intro destination; exact preservesConstructionBegins_pure _

theorem preservesConstructionBegins_ownerDestination (layout : LayoutEnv) (stored : StoredValue)
    (request : Goose.Core.ConstructionRequest) (count : Option Nat) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (ownerDestination layout stored request count origin) := by
  unfold ownerDestination
  cases stored.destination with
  | none => exact preservesConstructionBegins_newDestination _ _ _ _ _ _ _
  | some id =>
      apply preservesConstructionBegins_bind
      · exact stateQuery_preservesConstructionBegins _ (stateQuery_getDestination id)
      · intro destination
        cases destination.progress <;> first
          | kernel_begin_operation
          | exact preservesConstructionBegins_newDestination _ _ _ _ _ _ _
          | exact preservesConstructionBegins_stop _

theorem preservesConstructionBegins_appendFixedValues (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (values : List Value) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (appendFixedValues fuel layout location values origin) := by
  cases fuel with
  | zero => exact preservesConstructionBegins_stop _
  | succ fuel =>
      unfold appendFixedValues
      apply preservesConstructionBegins_bind
      · exact stateQuery_preservesConstructionBegins _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact preservesConstructionBegins_stop _
        | stored stored =>
            simp only
            cases elementFound : elementType stored.ty with
            | none => exact preservesConstructionBegins_stop _
            | some element =>
                apply preservesConstructionBegins_bind
                · apply preservesConstructionBegins_listMapM
                  intro value; exact stateQuery_preservesConstructionBegins _ (stateQuery_liftExcept _)
                · intro parts
                  apply preservesConstructionBegins_bind
                  · exact preservesConstructionBegins_ownerDestination _ _ _ _ _
                  · intro destination
                    apply preservesConstructionBegins_bind
                    · apply preservesConstructionBegins_listForIn
                      intro bytes state
                      apply preservesConstructionBegins_bind
                      · kernel_begin_operation
                      · intro _; exact preservesConstructionBegins_pure _
                    · intro _
                      apply preservesConstructionBegins_bind
                      · kernel_begin_operation
                      · intro _
                        apply preservesConstructionBegins_bind
                        · exact stateQuery_preservesConstructionBegins _ (stateQuery_completedDestination destination)
                        · intro completed; exact preservesConstructionBegins_publishOwner _ _ _ _ _ _

theorem preservesConstructionBegins_appendRun (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (view : RuntimeView) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (appendRun fuel layout location view origin) := by
  cases fuel with
  | zero => exact preservesConstructionBegins_stop _
  | succ fuel =>
      unfold appendRun
      apply preservesConstructionBegins_bind
      · exact stateQuery_preservesConstructionBegins _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact preservesConstructionBegins_stop _
        | stored stored =>
            apply preservesConstructionBegins_bind
            · exact stateQuery_preservesConstructionBegins _ (stateQuery_readLoc fuel layout view.location)
            · intro source
              apply preservesConstructionBegins_bind
              · exact preservesConstructionBegins_ownerDestination _ _ _ _ _
              · intro destination
                have finish : PreservesConstructionBegins (do
                    liftConstruction origin (finishDestination destination)
                    let completed ← completedDestination destination
                    publishOwner fuel layout location stored completed origin) := by
                  apply preservesConstructionBegins_bind
                  · kernel_begin_operation
                  · intro _
                    apply preservesConstructionBegins_bind
                    · exact stateQuery_preservesConstructionBegins _ (stateQuery_completedDestination destination)
                    · intro completed; exact preservesConstructionBegins_publishOwner _ _ _ _ _ _
                cases source with
                | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ =>
                    apply preservesConstructionBegins_bind
                    · exact preservesConstructionBegins_stop _
                    · intro _; exact finish
                | stored source =>
                      apply preservesConstructionBegins_bind
                      · exact stateQuery_preservesConstructionBegins _ (stateQuery_sampledStored source)
                      · intro sampled
                        rcases sampled with ⟨bytes, run⟩
                        apply preservesConstructionBegins_bind
                        · kernel_begin_operation
                        · intro _
                          apply preservesConstructionBegins_bind
                          · exact packed_writes_preserveConstructionBegins fuel layout destination bytes run view.start view.count origin
                          · intro _; exact finish
                | fixed values =>
                      simp only
                      cases elementFound : elementType stored.ty with
                      | none =>
                          apply preservesConstructionBegins_bind
                          · exact preservesConstructionBegins_stop _
                          · intro _; exact finish
                      | some element =>
                        apply preservesConstructionBegins_bind
                        ·
                          apply preservesConstructionBegins_rangeForIn
                          intro index current
                          split
                          · apply preservesConstructionBegins_bind
                            · exact stateQuery_preservesConstructionBegins _ (stateQuery_liftExcept _)
                            · intro bytes
                              apply preservesConstructionBegins_bind
                              · kernel_begin_operation
                              · intro _; exact preservesConstructionBegins_pure _
                          · apply preservesConstructionBegins_bind
                            · exact preservesConstructionBegins_stop _
                            · intro _; exact preservesConstructionBegins_pure _
                        · intro _; exact finish

theorem preservesConstructionBegins_constructLocal (declarations : DeclarationEnv) (owner : Goose.Core.ActId) (ty : Ty)
    (origin : Goose.Core.OriginId) (expression : Expr) (construct : Goose.Core.DestinationId → EvalM Unit)
    (preserved : ∀ destination, PreservesConstructionBegins (construct destination)) :
    PreservesConstructionBegins (constructLocal declarations owner ty origin expression construct) := by
  unfold constructLocal
  apply preservesConstructionBegins_bind
  · exact preservesConstructionBegins_newDestination _ _ _ _ _ _ _
  · intro destination
    apply preservesConstructionBegins_bind
    · exact preserved destination
    · intro _
      apply preservesConstructionBegins_bind
      · exact stateQuery_preservesConstructionBegins _ (stateQuery_completedDestination destination)
      · intro completed
        apply preservesConstructionBegins_bind
        · exact preservesConstructionBegins_publishCarriers _ _
        · intro _; exact preservesConstructionBegins_pure _

theorem preservesConstructionBegins_exitChannels (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) : PreservesConstructionBegins (exitChannels source activation operands origin) := by
  unfold exitChannels
  split
  · exact preservesConstructionBegins_stop _
  · apply preservesConstructionBegins_listMapM
    intro item
    rcases item with ⟨channel, operand⟩
    cases channel with
    | register ty => exact preservesConstructionBegins_pure _
    | construct id =>
        apply preservesConstructionBegins_bind
        · exact stateQuery_preservesConstructionBegins _ (stateQuery_getDestination id)
        · intro destination
          have finish (alias : Bool) : PreservesConstructionBegins
              (if (match destination.progress with | .open 0 => true | _ => false) || alias then
                pure (Channel.construct id)
              else do pure (Channel.construct (← liftConstruction origin (openExitReplacement id)))) := by
            split <;> split
            all_goals first
              | exact preservesConstructionBegins_pure _
              | (apply preservesConstructionBegins_bind
                 · kernel_begin_operation
                 · intro _; exact preservesConstructionBegins_pure _)
          cases operand <;> first
            | (apply preservesConstructionBegins_bind
               · exact preservesConstructionBegins_pure _
               · intro alias; exact finish alias)
            | (apply preservesConstructionBegins_bind
               · exact stateQuery_preservesConstructionBegins _ (stateQuery_rootOf _ _)
               · intro root
                 apply preservesConstructionBegins_bind
                 · exact preservesConstructionBegins_get
                 · intro state
                   split
                   all_goals
                     apply preservesConstructionBegins_bind
                     · exact preservesConstructionBegins_pure _
                     · intro alias; exact finish alias)

theorem preservesConstructionBegins_openElementReceiving (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (location : Goose.Core.Loc) (stored : StoredValue) (element : Ty) (known : Option Nat)
    (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (openElementReceiving layout owner location stored element known origin) := by
  unfold openElementReceiving
  apply preservesConstructionBegins_bind
  · exact stateQuery_preservesConstructionBegins _ (stateQuery_sampledStored stored)
  · intro sampled
    rcases sampled with ⟨bytes, run⟩
    apply preservesConstructionBegins_bind
    · exact stateQuery_preservesConstructionBegins _ (stateQuery_receivingLayout layout element)
    · intro receiving
      cases stored.destination with
      | none => kernel_begin_operation
      | some id =>
          apply preservesConstructionBegins_bind
          · exact stateQuery_preservesConstructionBegins _ (stateQuery_getDestination id)
          · intro pending
            cases pending.progress <;> first
              | kernel_begin_operation
              | exact preservesConstructionBegins_stop _

structure EvaluationPreservesConstructionBegins (fuel : Nat) (config : EvalConfig) : Prop where
  value : ∀ environment expression, PreservesConstructionBegins (evalValue fuel config environment expression)
  bound : ∀ environment count defaultValue operand, PreservesConstructionBegins (evalBound fuel config environment count defaultValue operand)
  place : ∀ environment operand, PreservesConstructionBegins (evalPlace fuel config environment operand)
  view : ∀ environment operand, PreservesConstructionBegins (evalView fuel config environment operand)
  produce : ∀ environment channels operand, PreservesConstructionBegins (evalProduce fuel config environment channels operand)
  operands : ∀ environment channels expressions, PreservesConstructionBegins (evalOperands fuel config environment channels expressions)
  build : ∀ environment destination expression, PreservesConstructionBegins (buildExpr fuel config environment destination expression)
  element : ∀ environment destination element expression, PreservesConstructionBegins (buildElement fuel config environment destination element expression)
  arguments : ∀ environment vars params args, PreservesConstructionBegins (evalArguments fuel config environment vars params args)
  call : ∀ environment context args channels origin, PreservesConstructionBegins (invokeCall fuel config environment context args channels origin)
  activation : ∀ environment pre body origin, PreservesConstructionBegins (enterActivation fuel config environment pre body origin)
  activationBody : ∀ environment pre body, PreservesConstructionBegins (execActivationBody fuel config environment pre body)
  resultBlock : ∀ environment channels body, PreservesConstructionBegins (execResultBlock fuel config environment channels body)
  resultBlockWith : ∀ environment pre channels body, PreservesConstructionBegins (execResultBlockWith fuel config environment pre channels body)
  block : ∀ environment pre channels body, PreservesConstructionBegins (execBlock fuel config environment pre channels body)
  statements : ∀ environment statements, PreservesConstructionBegins (execStmts fuel config environment statements)
  statement : ∀ environment statement, PreservesConstructionBegins (execStmt fuel config environment statement)
  printArgument : ∀ environment argument, PreservesConstructionBegins (evalPrintArg fuel config environment argument)
  whileLoop : ∀ environment condition body, PreservesConstructionBegins (execWhile fuel config environment condition body)
  rangeLoop : ∀ environment var ty first last body, PreservesConstructionBegins (execRange fuel config environment var ty first last body)
  eachLoop : ∀ environment var index byRef body view current, PreservesConstructionBegins (execEach fuel config environment var index byRef body view current)
  loop : ∀ environment pre body, PreservesConstructionBegins (loopBody fuel config environment pre body)
  push : ∀ environment owner expression origin, PreservesConstructionBegins (pushValue fuel config environment owner expression origin)

theorem evaluationPreservesConstructionBegins_zero (config : EvalConfig) : EvaluationPreservesConstructionBegins 0 config := by
  constructor
  all_goals intros
  all_goals simp [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands,
    buildExpr, buildElement, evalArguments, invokeCall, enterActivation, execActivationBody,
    execResultBlock, execResultBlockWith, execBlock, execStmts, execStmt, evalPrintArg,
    execWhile, execRange, execEach, loopBody, pushValue, timeout, EvalM.stop,
    PreservesConstructionBegins, Goose.Proofs.Exit.stepState, bind]

private theorem evalBound_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (count : Nat) (defaultValue : Int) (operand : Bound) :
    PreservesConstructionBegins (evalBound (fuel + 1) config environment count defaultValue operand) := by
  cases operand with
  | omitted => simpa only [evalBound] using preservesConstructionBegins_pure defaultValue
  | expr expression | fromEnd expression =>
      simp only [evalBound]
      apply preservesConstructionBegins_bind
      · exact previous.value _ _
      · intro value
        apply preservesConstructionBegins_bind
        · exact stateQuery_preservesConstructionBegins _ (stateQuery_expectInt value)
        · intro pair; exact preservesConstructionBegins_pure _

private theorem evalPlace_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation) (operand : Place) :
    PreservesConstructionBegins (evalPlace (fuel + 1) config environment operand) := by
  cases operand with
  | var localVar =>
      simp only [evalPlace]
      apply preservesConstructionBegins_bind
      · exact stateQuery_preservesConstructionBegins _ (stateQuery_rootOf _ _)
      · intro _; exact preservesConstructionBegins_pure _
  | global global => simpa only [evalPlace] using preservesConstructionBegins_pure (Goose.Core.Loc.mk (.global global) [])
  | deref expression =>
      simp only [evalPlace]
      apply preservesConstructionBegins_bind
      · exact previous.value _ _
      · intro value; exact stateQuery_preservesConstructionBegins _ (stateQuery_expectRef value)
  | elem view expression origin =>
      simp only [evalPlace]
      apply preservesConstructionBegins_bind
      · exact previous.view _ _
      · intro view
        apply preservesConstructionBegins_bind
        · exact previous.value _ _
        · intro value
          apply preservesConstructionBegins_bind
          · exact stateQuery_preservesConstructionBegins _ (stateQuery_expectInt value)
          · intro pair
            rcases pair with ⟨ty, index⟩
            split
            · exact preservesConstructionBegins_pure _
            · exact preservesConstructionBegins_stop _
  | field place index =>
      simp only [evalPlace]
      apply preservesConstructionBegins_bind
      · exact previous.place _ _
      · intro _; exact preservesConstructionBegins_pure _

private theorem evalView_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation) (operand : View) :
    PreservesConstructionBegins (evalView (fuel + 1) config environment operand) := by
  cases operand with
  | of place =>
      simp only [evalView]
      apply preservesConstructionBegins_bind
      · exact previous.place _ _
      · intro location
        apply preservesConstructionBegins_bind
        · exact stateQuery_preservesConstructionBegins _ (stateQuery_readLoc _ _ _)
        · intro value
          apply preservesConstructionBegins_bind
          · exact stateQuery_preservesConstructionBegins _ (stateQuery_arrayLength value)
          · intro pair
            rcases pair with ⟨count, dynamic⟩
            exact preservesConstructionBegins_pure _
  | val expression =>
      simp only [evalView]
      apply preservesConstructionBegins_bind
      · exact previous.value _ _
      · intro value
        cases value <;> first
          | exact preservesConstructionBegins_pure _
          | (apply preservesConstructionBegins_bind
             · exact stateQuery_preservesConstructionBegins _ (stateQuery_arrayLength _)
             · intro pair
               rcases pair with ⟨count, dynamic⟩
               apply preservesConstructionBegins_bind
               · exact preservesConstructionBegins_freshScope
               · intro index
                 apply preservesConstructionBegins_bind
                 · exact preservesConstructionBegins_bindRoot _ _
                 · intro _; exact preservesConstructionBegins_pure _)

private theorem evalOperands_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr) :
    PreservesConstructionBegins (evalOperands (fuel + 1) config environment channels operands) := by
  cases channels <;> cases operands <;> simp only [evalOperands]
  all_goals first
    | exact preservesConstructionBegins_pure _
    | exact preservesConstructionBegins_stop _
    | (apply preservesConstructionBegins_bind
       · exact previous.produce _ _ _
       · intro carriers
         apply preservesConstructionBegins_bind
         · exact stateQuery_preservesConstructionBegins _ (stateQuery_singleCarrier carriers)
         · intro carrier
           apply preservesConstructionBegins_bind
           · exact previous.operands _ _ _
           · intro _; exact preservesConstructionBegins_pure _)

private theorem evalPrintArg_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation) (argument : PrintArg) :
    PreservesConstructionBegins (evalPrintArg (fuel + 1) config environment argument) := by
  cases argument with
  | text text => simpa only [evalPrintArg] using preservesConstructionBegins_pure text.toUTF8
  | expr expression =>
      simp only [evalPrintArg]
      apply preservesConstructionBegins_bind
      · exact previous.value _ _
      · intro value; exact stateQuery_preservesConstructionBegins _ ((rendering_stateQueries fuel config.layout).1 _ _)
  | view view =>
      simp only [evalPrintArg]
      apply preservesConstructionBegins_bind
      · exact previous.view _ _
      · intro view; exact stateQuery_preservesConstructionBegins _ ((rendering_stateQueries fuel config.layout).2.2.2 _ _)

private theorem evalArguments_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameters : List Param) (arguments : List Arg) :
    PreservesConstructionBegins (evalArguments (fuel + 1) config environment vars parameters arguments) := by
  cases parameters with
  | nil =>
      cases arguments <;> simp only [evalArguments]
      · exact preservesConstructionBegins_pure _
      · exact preservesConstructionBegins_stop _
  | cons parameter parameters =>
      cases arguments with
      | nil => simpa only [evalArguments, fault] using preservesConstructionBegins_stop (Goose.Core.Stop.fault .arity)
      | cons argument arguments =>
          have finish (value : Value) : PreservesConstructionBegins (do
              let values ← evalArguments fuel config environment vars parameters arguments
              pure (value :: values)) := by
            apply preservesConstructionBegins_bind
            · exact previous.arguments _ _ _ _
            · intro _; exact preservesConstructionBegins_pure _
          cases argument with
          | byVal expression =>
              simp only [evalArguments]
              apply preservesConstructionBegins_bind
              · exact previous.value _ _
              · intro value; exact finish value
          | byRef mutability place =>
              simp only [evalArguments]
              apply preservesConstructionBegins_bind
              · exact previous.place _ _
              · intro location
                apply preservesConstructionBegins_bind
                · exact preservesConstructionBegins_pure _
                · intro value; exact finish value
          | construct expression =>
              simp only [evalArguments]
              split
              · apply preservesConstructionBegins_bind
                · apply preservesConstructionBegins_constructLocal
                  intro destination; exact previous.build _ _ _
                · intro carrier
                  apply preservesConstructionBegins_bind
                  · exact stateQuery_preservesConstructionBegins _ (stateQuery_carrierValue carrier)
                  · intro value; exact finish value
              · apply preservesConstructionBegins_bind
                · exact preservesConstructionBegins_stop _
                · intro value; exact finish value

private theorem execStmts_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (statements : List Stmt) : PreservesConstructionBegins (execStmts (fuel + 1) config environment statements) := by
  cases statements with
  | nil => simpa only [execStmts] using preservesConstructionBegins_pure (Flow.normal .unit)
  | cons statement statements =>
      simp only [execStmts]
      apply preservesConstructionBegins_bind
      · exact previous.statement _ _
      · intro flow
        cases flow with
        | normal value => exact previous.statements _ _
        | breaking value | continuing => exact preservesConstructionBegins_pure _

private theorem execResultBlock_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (body : Block) :
    PreservesConstructionBegins (execResultBlock (fuel + 1) config environment channels body) := by
  simpa only [execResultBlock] using previous.resultBlockWith environment [] channels body

private theorem execActivationBody_preservesConstructionBegins (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (preserved : PreservesConstructionBegins (execResultBlockWith fuel config environment pre environment.channels body)) :
    PreservesConstructionBegins (execActivationBody fuel config environment pre body) := by
  unfold execActivationBody
  apply preservesConstructionBegins_bind
  · exact preserved
  · intro result
    rcases result with ⟨flow, carriers⟩
    cases flow <;> first | exact preservesConstructionBegins_pure _ | exact preservesConstructionBegins_stop _

private theorem enterActivation_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (enterActivation (fuel + 1) config environment pre body origin) := by
  simp only [enterActivation]
  split
  · apply preservesConstructionBegins_finishActivation
    exact previous.activationBody _ _ _
  · exact preservesConstructionBegins_stop _

private theorem preservesConstructionBegins_mapActivations (change : RuntimeActivation → RuntimeActivation)
    (action : EvalM α) (preserved : PreservesConstructionBegins action) :
    PreservesConstructionBegins (do
      let state ← EvalM.get
      EvalM.set { state with activations := state.activations.map change }
      action) := by
  intro state valid
  simpa [EvalM.get, EvalM.set, bind, pure] using
    preserved { state with activations := state.activations.map change } valid

private theorem preservesConstructionBegins_fault (kind : Goose.Core.FaultKind) :
    PreservesConstructionBegins (fault (α := α) kind) := preservesConstructionBegins_stop _

private theorem preservesConstructionBegins_timeout :
    PreservesConstructionBegins (timeout (α := α)) := preservesConstructionBegins_stop _

private theorem preservesConstructionBegins_abortAt (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (abortAt (α := α) kind origin) := preservesConstructionBegins_stop _

private theorem preservesConstructionBegins_fault_bind (kind : Goose.Core.FaultKind) (next : α → EvalM β) :
    PreservesConstructionBegins (fault kind >>= next) := fun _ valid => valid

private theorem preservesConstructionBegins_timeout_bind (next : α → EvalM β) :
    PreservesConstructionBegins (timeout >>= next) := fun _ valid => valid

private theorem preservesConstructionBegins_abortAt_bind (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId)
    (next : α → EvalM β) : PreservesConstructionBegins (abortAt kind origin >>= next) := fun _ valid => valid

local syntax "begins_eval" ident : tactic
macro_rules
  | `(tactic| begins_eval $previous:ident) => `(tactic|
  repeat' first
    | with_reducible assumption
    | with_reducible exact preservesConstructionBegins_pure _
    | with_reducible exact preservesConstructionBegins_stop _
    | with_reducible exact preservesConstructionBegins_fault _
    | with_reducible exact preservesConstructionBegins_timeout
    | with_reducible exact preservesConstructionBegins_abortAt _ _
    | with_reducible exact preservesConstructionBegins_fault_bind _ _
    | with_reducible exact preservesConstructionBegins_timeout_bind _
    | with_reducible exact preservesConstructionBegins_abortAt_bind _ _ _
    | with_reducible exact preservesConstructionBegins_get
    | kernel_begin_operation
    | with_reducible exact preservesConstructionBegins_bindRoot _ _
    | with_reducible exact preservesConstructionBegins_bindStaticRoot _ _
    | with_reducible exact preservesConstructionBegins_reserveRootObject _
    | with_reducible exact preservesConstructionBegins_setObjectOrdinal _ _
    | with_reducible exact preservesConstructionBegins_newDestination _ _ _ _ _ _ _
    | with_reducible exact preservesConstructionBegins_channelsFor _ _ _ _
    | with_reducible exact preservesConstructionBegins_freshAct
    | with_reducible exact preservesConstructionBegins_freshScope
    | with_reducible exact preservesConstructionBegins_returned _ _
    | with_reducible exact preservesConstructionBegins_escaped _ _
    | with_reducible exact preservesConstructionBegins_jump _ _
    | with_reducible exact preservesConstructionBegins_emitStdout _
    | with_reducible exact preservesConstructionBegins_publishCarriers _ _
    | with_reducible exact preservesConstructionBegins_copyValue _ _ _ _ _ _
    | with_reducible exact preservesConstructionBegins_deliverCarriers _ _ _ _ _
    | with_reducible exact preservesConstructionBegins_ownerDestination _ _ _ _ _
    | with_reducible exact preservesConstructionBegins_publishOwner _ _ _ _ _ _
    | with_reducible exact preservesConstructionBegins_openElementReceiving _ _ _ _ _ _ _
    | with_reducible exact preservesConstructionBegins_publishElementReceiving _ _ _ _ _ _
    | with_reducible exact preservesConstructionBegins_repeatElement _ _ _ _ _ _
    | with_reducible exact preservesConstructionBegins_truncateOwner _ _ _ _ _
    | with_reducible exact preservesConstructionBegins_appendFixedValues _ _ _ _ _
    | with_reducible exact preservesConstructionBegins_appendRun _ _ _ _ _
    | with_reducible exact preservesConstructionBegins_writeLoc _ _ _ _
    | with_reducible exact preservesConstructionBegins_landCarriers _ _
    | with_reducible exact preservesConstructionBegins_bindAll _ _ _
    | with_reducible exact preservesConstructionBegins_exitChannels _ _ _ _
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_rootOf _ _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_expectInt _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_expectBool _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_expectRef _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_sameIntType _ _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_comparable _ _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_readLoc _ _ _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_arrayLength _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_getDestination _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_getStorage _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_sampledStored _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_readStoredElement _ _ _ _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_carrierValue _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_singleCarrier _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_completedDestination _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_storedDestination _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_receivingLayout _ _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_getImplementation _ _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_enclosingActivation _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_targetActivation _ _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_currentBreak _ _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_liftExcept _)
    | with_reducible exact stateQuery_preservesConstructionBegins _ (stateQuery_liftLayout _)
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
    | with_reducible apply preservesConstructionBegins_allocateActivation
    | with_reducible apply preservesConstructionBegins_mapActivations
    | with_reducible apply preservesConstructionBegins_protectDestination
    | with_reducible apply preservesConstructionBegins_withScope
    | with_reducible apply preservesConstructionBegins_finishActivation
    | with_reducible apply preservesConstructionBegins_withBreakTarget
    | with_reducible apply preservesConstructionBegins_constructLocal
    | with_reducible apply preservesConstructionBegins_bind
    | with_reducible apply preservesConstructionBegins_listMapM
    | with_reducible apply preservesConstructionBegins_listForIn
    | with_reducible apply preservesConstructionBegins_arrayForIn
    | with_reducible apply preservesConstructionBegins_rangeForIn
    | with_reducible split
    | with_reducible rfl
    | with_reducible intro)

private theorem evalValue_lit_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (_previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (ty : Goose.Core.IntTy) (value : Int) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.lit ty value)) := by
  simp only [evalValue]
  begins_eval _previous

private theorem evalValue_bool_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (_previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (value : Bool) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.bool value)) := by
  simp only [evalValue]
  begins_eval _previous

private theorem evalValue_read_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (place : Place) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.read place)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_ref_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (place : Place) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.ref mutability place)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_slice_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (mutability : Goose.Core.Mutability) (view : View) (lo hi : Bound) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.slice mutability view lo hi origin)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_len_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (view : View) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.len view)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_un_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.UnOp) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.un operation expression origin)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_bin_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.BinOp) (first second : Expr) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.bin operation first second origin)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_cmp_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.CmpOp) (first second : Expr) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.cmp operation first second)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_and_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (first second : Expr) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.and first second)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_or_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (first second : Expr) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.or first second)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_not_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (expression : Expr) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.not expression)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_conv_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (kind : Goose.Core.ConvKind) (target : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.conv kind target expression origin)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_call_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.call context arguments origin)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_push_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Option Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.push owner expression origin)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_pop_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (owner : Place) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.pop owner origin)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_ifE_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (condition : Expr) (yes no : Block) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.ifE condition yes no origin)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_blockE_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (body : Block) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.blockE body origin)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_arrLit_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.arrLit ty operands origin)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_fill_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (ty : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.fill ty expression origin)) := by
  cases ty <;> simp only [evalValue]
  all_goals begins_eval previous

private theorem evalValue_structLit_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (ty : Ty) (operands : List Expr) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.structLit ty operands)) := by
  cases ty <;> simp only [evalValue]
  all_goals begins_eval previous

private theorem evalValue_bytes_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.bytes ty bytes origin)) := by
  cases ty <;> try simp only [evalValue]
  all_goals begins_eval previous
  case slice mutability element =>
    cases element <;> try simp only [evalValue]
    all_goals begins_eval previous
    case int ty =>
      cases ty <;> simp only [evalValue]
      all_goals begins_eval previous

private theorem evalValue_str_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (ty : Ty) (arguments : List PrintArg) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.str ty arguments origin)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_copy_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (ty : Ty) (source : Place) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.copy ty source origin)) := by
  simp only [evalValue]
  begins_eval previous

private theorem evalValue_resultLocal_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (_previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.resultLocal localVar origin)) := by
  simp only [evalValue]
  begins_eval _previous

private theorem evalValue_values_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (operands : List Expr) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment (Expr.values operands)) := by
  cases operands with
  | nil => simpa only [evalValue] using preservesConstructionBegins_pure Value.unit
  | cons expression operands =>
      cases operands <;> simp only [evalValue]
      all_goals begins_eval previous

private theorem evalValue_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation) (expression : Expr) :
    PreservesConstructionBegins (evalValue (fuel + 1) config environment expression) := by
  cases expression with
  | lit ty value => exact evalValue_lit_preservesConstructionBegins_succ fuel config previous environment ty value
  | bool value => exact evalValue_bool_preservesConstructionBegins_succ fuel config previous environment value
  | read place => exact evalValue_read_preservesConstructionBegins_succ fuel config previous environment place
  | ref mutability place => exact evalValue_ref_preservesConstructionBegins_succ fuel config previous environment mutability place
  | slice mutability view lo hi origin => exact evalValue_slice_preservesConstructionBegins_succ fuel config previous environment mutability view lo hi origin
  | len view => exact evalValue_len_preservesConstructionBegins_succ fuel config previous environment view
  | un operation expression origin => exact evalValue_un_preservesConstructionBegins_succ fuel config previous environment operation expression origin
  | bin operation first second origin => exact evalValue_bin_preservesConstructionBegins_succ fuel config previous environment operation first second origin
  | cmp operation first second => exact evalValue_cmp_preservesConstructionBegins_succ fuel config previous environment operation first second
  | and first second => exact evalValue_and_preservesConstructionBegins_succ fuel config previous environment first second
  | or first second => exact evalValue_or_preservesConstructionBegins_succ fuel config previous environment first second
  | not expression => exact evalValue_not_preservesConstructionBegins_succ fuel config previous environment expression
  | conv kind target expression origin => exact evalValue_conv_preservesConstructionBegins_succ fuel config previous environment kind target expression origin
  | call context arguments origin => exact evalValue_call_preservesConstructionBegins_succ fuel config previous environment context arguments origin
  | push owner expression origin => exact evalValue_push_preservesConstructionBegins_succ fuel config previous environment owner expression origin
  | pop owner origin => exact evalValue_pop_preservesConstructionBegins_succ fuel config previous environment owner origin
  | ifE condition yes no origin => exact evalValue_ifE_preservesConstructionBegins_succ fuel config previous environment condition yes no origin
  | blockE body origin => exact evalValue_blockE_preservesConstructionBegins_succ fuel config previous environment body origin
  | arrLit ty operands origin => exact evalValue_arrLit_preservesConstructionBegins_succ fuel config previous environment ty operands origin
  | fill ty expression origin => exact evalValue_fill_preservesConstructionBegins_succ fuel config previous environment ty expression origin
  | structLit ty operands => exact evalValue_structLit_preservesConstructionBegins_succ fuel config previous environment ty operands
  | bytes ty bytes origin => exact evalValue_bytes_preservesConstructionBegins_succ fuel config previous environment ty bytes origin
  | str ty arguments origin => exact evalValue_str_preservesConstructionBegins_succ fuel config previous environment ty arguments origin
  | copy ty source origin => exact evalValue_copy_preservesConstructionBegins_succ fuel config previous environment ty source origin
  | resultLocal localVar origin => exact evalValue_resultLocal_preservesConstructionBegins_succ fuel config previous environment localVar origin
  | values operands => exact evalValue_values_preservesConstructionBegins_succ fuel config previous environment operands

private theorem buildElement_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (element : Ty) (expression : Expr) :
    PreservesConstructionBegins (buildElement (fuel + 1) config environment destination element expression) := by
  simp only [buildElement]
  begins_eval previous

private theorem execWhile_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (condition : Expr) (body : Block) :
    PreservesConstructionBegins (execWhile (fuel + 1) config environment condition body) := by
  simp only [execWhile]
  begins_eval previous

private theorem execRange_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (ty : Goose.Core.IntTy) (first last : Int) (body : Block) :
    PreservesConstructionBegins (execRange (fuel + 1) config environment var ty first last body) := by
  simp only [execRange]
  begins_eval previous

private theorem execEach_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block)
    (view : RuntimeView) (current : Nat) :
    PreservesConstructionBegins (execEach (fuel + 1) config environment var index byRef body view current) := by
  simp only [execEach]
  begins_eval previous

private theorem loopBody_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    PreservesConstructionBegins (loopBody (fuel + 1) config environment pre body) := by
  simp only [loopBody]
  begins_eval previous

private theorem pushValue_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (pushValue (fuel + 1) config environment owner expression origin) := by
  simp only [pushValue]
  begins_eval previous

set_option maxHeartbeats 2000000 in
private theorem evalProduce_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (expression : Expr) :
    PreservesConstructionBegins (evalProduce (fuel + 1) config environment channels expression) := by
  cases channels with
  | nil =>
      cases expression <;> simp only [evalProduce]
      all_goals begins_eval previous
  | cons channel channels =>
      cases channels with
      | nil =>
          cases channel <;> cases expression <;> simp only [evalProduce]
          all_goals begins_eval previous
      | cons second channels =>
          cases expression <;> simp only [evalProduce]
          all_goals begins_eval previous

set_option maxHeartbeats 2000000 in
private theorem buildExpr_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (expression : Expr) :
    PreservesConstructionBegins (buildExpr (fuel + 1) config environment destination expression) := by
  cases expression <;> try simp only [buildExpr]
  all_goals begins_eval previous
  case fill ty expression origin =>
    cases ty <;> simp only [buildExpr]
    all_goals begins_eval previous
  case values operands =>
    cases operands with
    | nil =>
        simp only [buildExpr]
        begins_eval previous
    | cons expression operands =>
        cases operands <;> simp only [buildExpr]
        all_goals begins_eval previous

set_option maxHeartbeats 2000000 in
private theorem execStmt_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation) (statement : Stmt) :
    PreservesConstructionBegins (execStmt (fuel + 1) config environment statement) := by
  cases statement <;> try simp only [execStmt]
  all_goals begins_eval previous
  case ifS condition yes no origin =>
    cases no <;> simp only [execStmt]
    all_goals begins_eval previous

private theorem execBlock_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    PreservesConstructionBegins (execBlock (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execBlock]
  begins_eval previous

private theorem execResultBlockWith_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    PreservesConstructionBegins (execResultBlockWith (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execResultBlockWith]
  begins_eval previous

private theorem invokeCall_preservesConstructionBegins_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionBegins fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) :
    PreservesConstructionBegins (invokeCall (fuel + 1) config environment context arguments channels origin) := by
  simp only [invokeCall]
  apply preservesConstructionBegins_bind
  · exact stateQuery_preservesConstructionBegins _ (stateQuery_getImplementation config context)
  · intro implementation
    rcases implementation with ⟨id, implementation⟩
    split
    · begins_eval previous
    · apply preservesConstructionBegins_bind
      · begins_eval previous
      · intro callableChannels
        apply preservesConstructionBegins_bind
        · exact previous.arguments _ _ _ _
        · intro values
          apply preservesConstructionBegins_bind
          · exact preservesConstructionBegins_get
          · intro state
            split
            · begins_eval previous
            · apply preservesConstructionBegins_allocateActivation
                (make := fun act => ⟨id, act, implementation.vars, [], callableChannels⟩)
                (action := fun activation => do
                  let carriers ← enterActivation fuel config activation
                    ((implementation.params.toList.zip values).map fun item => (item.1.var, item.2))
                    implementation.body origin
                  deliverCarriers fuel config.layout channels carriers origin)
              intro activation
              begins_eval previous

theorem evaluation_preservesConstructionBegins (fuel : Nat) (config : EvalConfig) :
    EvaluationPreservesConstructionBegins fuel config := by
  induction fuel with
  | zero => exact evaluationPreservesConstructionBegins_zero config
  | succ fuel previous =>
      refine {
        value := evalValue_preservesConstructionBegins_succ fuel config previous
        bound := evalBound_preservesConstructionBegins_succ fuel config previous
        place := evalPlace_preservesConstructionBegins_succ fuel config previous
        view := evalView_preservesConstructionBegins_succ fuel config previous
        produce := evalProduce_preservesConstructionBegins_succ fuel config previous
        operands := evalOperands_preservesConstructionBegins_succ fuel config previous
        build := buildExpr_preservesConstructionBegins_succ fuel config previous
        element := buildElement_preservesConstructionBegins_succ fuel config previous
        arguments := evalArguments_preservesConstructionBegins_succ fuel config previous
        call := invokeCall_preservesConstructionBegins_succ fuel config previous
        activation := enterActivation_preservesConstructionBegins_succ fuel config previous
        activationBody := ?_
        resultBlock := execResultBlock_preservesConstructionBegins_succ fuel config previous
        resultBlockWith := execResultBlockWith_preservesConstructionBegins_succ fuel config previous
        block := execBlock_preservesConstructionBegins_succ fuel config previous
        statements := execStmts_preservesConstructionBegins_succ fuel config previous
        statement := execStmt_preservesConstructionBegins_succ fuel config previous
        printArgument := evalPrintArg_preservesConstructionBegins_succ fuel config previous
        whileLoop := execWhile_preservesConstructionBegins_succ fuel config previous
        rangeLoop := execRange_preservesConstructionBegins_succ fuel config previous
        eachLoop := execEach_preservesConstructionBegins_succ fuel config previous
        loop := loopBody_preservesConstructionBegins_succ fuel config previous
        push := pushValue_preservesConstructionBegins_succ fuel config previous }
      intro environment pre body
      apply execActivationBody_preservesConstructionBegins
      exact execResultBlockWith_preservesConstructionBegins_succ fuel config previous environment pre environment.channels body

theorem initGlobals_preservesConstructionBegins (fuel : Nat) (config : EvalConfig) (globals : List Goose.Core.GlobalId) :
    PreservesConstructionBegins (initGlobals fuel config globals) := by
  have previous := evaluation_preservesConstructionBegins fuel config
  induction globals with
  | nil => simpa only [initGlobals] using preservesConstructionBegins_pure ()
  | cons global globals preserved =>
      simp only [initGlobals]
      begins_eval previous

theorem runModule_preservesConstructionBegins (fuel : Nat) (config : EvalConfig) :
    PreservesConstructionBegins (runModule fuel config) := by
  have previous := evaluation_preservesConstructionBegins fuel config
  unfold runModule
  apply preservesConstructionBegins_bind
  · exact initGlobals_preservesConstructionBegins _ _ _
  · intro _
    begins_eval previous

theorem runModule_destinationBeginIds (fuel : Nat) (config : EvalConfig) :
    destinationBeginIds (Goose.Proofs.Exit.stepState
      (runModule fuel config .initial)).construction.events =
      List.range (Goose.Proofs.Exit.stepState
        (runModule fuel config .initial)).construction.destinations.size :=
  runModule_preservesConstructionBegins fuel config .initial initial_destination_begins

theorem runModule_distinctDestinationBegins (fuel : Nat) (config : EvalConfig) :
    (destinationBeginIds (Goose.Proofs.Exit.stepState
      (runModule fuel config .initial)).construction.events).Nodup :=
  DestinationBegins.distinct _ (runModule_destinationBeginIds fuel config)

theorem runModule_destinationBegins_cover (fuel : Nat) (config : EvalConfig)
    (id : Goose.Core.DestinationId) :
    id ∈ destinationBeginIds (Goose.Proofs.Exit.stepState
      (runModule fuel config .initial)).construction.events ↔
      id < (Goose.Proofs.Exit.stepState
        (runModule fuel config .initial)).construction.destinations.size :=
  DestinationBegins.covers _ (runModule_destinationBeginIds fuel config) id

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
