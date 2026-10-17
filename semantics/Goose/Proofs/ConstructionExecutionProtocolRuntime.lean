import Goose.Construct.Eval
import Goose.Construct.Validate
import Goose.Proofs.Construct
import Goose.Proofs.ConstructionExecutionProtocolQueries
import Goose.Proofs.ConstructionExecutionProtocolKernel

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

variable {predicate : ConstructionState → Prop} [primitives : ConstructionProtocolPrimitives predicate]
include primitives

theorem stateQuery_preservesConstructionInvariant (action : EvalM α) (query : StateQuery action) :
    (PreservesConstructionInvariant predicate) action := by
  intro state valid
  rw [query state]
  exact valid

theorem preservesConstructionInvariant_lift (origin : Goose.Core.OriginId) (action : ConstructionM α)
    (preserved : ∀ state, predicate state → predicate (action state).finalState) :
    (PreservesConstructionInvariant predicate) (liftConstruction origin action) := by
  intro state valid
  have after := preserved state.construction valid
  cases result : action state.construction <;>
    simpa only [ExecutionInvariant, liftConstruction, result, ConstructionResult.finalState,
      Goose.Proofs.Exit.stepState] using after

macro "kernel_protocol" : tactic => `(tactic|
  (with_reducible apply preservesConstructionInvariant_lift
   with_reducible exact ConstructionProtocolPrimitives.preserves _ (by constructor)))

theorem preservesConstructionInvariant_pure (value : α) : (PreservesConstructionInvariant predicate) (pure value) := by
  intro state fresh
  exact fresh

theorem preservesConstructionInvariant_stop (reason : Goose.Core.Stop) :
    (PreservesConstructionInvariant predicate) (EvalM.stop (α := α) reason) := by
  intro state fresh
  exact fresh

theorem preservesConstructionInvariant_get : (PreservesConstructionInvariant predicate) EvalM.get := by
  intro state fresh
  exact fresh

theorem preservesConstructionInvariant_get_bind (next : ExecutionState → EvalM α)
    (preserved : ∀ state, (ExecutionInvariant predicate) state →
      (ExecutionInvariant predicate) (Goose.Proofs.Exit.stepState (next state state))) :
    (PreservesConstructionInvariant predicate) (EvalM.get >>= next) := preserved

theorem preservesConstructionInvariant_bind (action : EvalM α) (next : α → EvalM β)
    (first : (PreservesConstructionInvariant predicate) action) (remaining : ∀ value, (PreservesConstructionInvariant predicate) (next value)) :
    (PreservesConstructionInvariant predicate) (action >>= next) := by
  intro state fresh
  have preserved := first state fresh
  cases result : action state with
  | ok value final =>
      simp only [result, Goose.Proofs.Exit.stepState] at preserved
      simpa only [bind, result] using remaining value final preserved
  | stop reason final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved
  | escape target carriers final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved
  | jump target kind final => simpa only [bind, result, Goose.Proofs.Exit.stepState] using preserved

theorem preservesConstructionInvariant_listMapM (action : α → EvalM β) (items : List α)
    (preserved : ∀ item, (PreservesConstructionInvariant predicate) (action item)) : (PreservesConstructionInvariant predicate) (items.mapM action) := by
  induction items with
  | nil => exact preservesConstructionInvariant_pure _
  | cons item rest ih =>
      rw [List.mapM_cons]
      apply preservesConstructionInvariant_bind
      · exact preserved item
      · intro value
        apply preservesConstructionInvariant_bind
        · exact ih
        · intro values; exact preservesConstructionInvariant_pure _

theorem preservesConstructionInvariant_listForIn (action : α → β → EvalM (ForInStep β)) (items : List α)
    (initial : β) (preserved : ∀ item value, (PreservesConstructionInvariant predicate) (action item value)) :
    (PreservesConstructionInvariant predicate) (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact preservesConstructionInvariant_pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply preservesConstructionInvariant_bind
      · exact preserved item initial
      · intro step
        cases step with
        | done value => exact preservesConstructionInvariant_pure _
        | yield value => exact ih value

theorem preservesConstructionInvariant_arrayForIn (action : α → β → EvalM (ForInStep β)) (items : Array α)
    (initial : β) (preserved : ∀ item value, (PreservesConstructionInvariant predicate) (action item value)) :
    (PreservesConstructionInvariant predicate) (forIn items initial action) := by
  rw [← Array.forIn_toList]
  exact preservesConstructionInvariant_listForIn action items.toList initial preserved

theorem preservesConstructionInvariant_rangeForIn (action : Nat → β → EvalM (ForInStep β))
    (range : Std.Legacy.Range) (initial : β)
    (preserved : ∀ index value, (PreservesConstructionInvariant predicate) (action index value)) :
    (PreservesConstructionInvariant predicate) (forIn range initial action) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact preservesConstructionInvariant_listForIn action _ initial preserved

theorem preservesConstructionInvariant_setObjectOrdinal (root : Goose.Core.RootInst) (ordinal : Goose.Core.StorageId) :
    (PreservesConstructionInvariant predicate) (setObjectOrdinal root ordinal) := by
  intro state fresh
  exact fresh

theorem preservesConstructionInvariant_bindStaticRoot (root : Goose.Core.RootInst) (value : Value) :
    (PreservesConstructionInvariant predicate) (bindStaticRoot root value) := by
  intro state fresh
  exact fresh

theorem preservesConstructionInvariant_reserveRootObject (root : Goose.Core.RootInst) : (PreservesConstructionInvariant predicate) (reserveRootObject root) := by
  unfold reserveRootObject
  apply preservesConstructionInvariant_bind
  · exact preservesConstructionInvariant_get
  · intro state
    cases state.objectOrdinals.lookup root with
    | some ordinal => exact preservesConstructionInvariant_pure _
    | none =>
        apply preservesConstructionInvariant_bind
        · kernel_protocol
        · intro ordinal
          apply preservesConstructionInvariant_bind
          · exact preservesConstructionInvariant_setObjectOrdinal root ordinal
          · intro _; exact preservesConstructionInvariant_pure _

theorem preservesConstructionInvariant_bindRoot (root : Goose.Core.RootInst) (value : Value) : (PreservesConstructionInvariant predicate) (bindRoot root value) := by
  unfold bindRoot
  apply preservesConstructionInvariant_bind
  · exact preservesConstructionInvariant_get
  · intro state
    split
    · cases value <;> apply preservesConstructionInvariant_bind
      all_goals first
        | exact preservesConstructionInvariant_setObjectOrdinal _ _
        | exact preservesConstructionInvariant_reserveRootObject _
        | (intro _
           apply preservesConstructionInvariant_bind
           · exact preservesConstructionInvariant_pure _
           · intro _; exact preservesConstructionInvariant_bindStaticRoot root _)
        | (intro _; exact preservesConstructionInvariant_bindStaticRoot root _)
    · exact preservesConstructionInvariant_bindStaticRoot root value

theorem preservesConstructionInvariant_writeValuePath (fuel : Nat) (layout : LayoutEnv)
    (value : Value) (path : List Nat) (replacement : Value) :
    (PreservesConstructionInvariant predicate) (writeValuePath fuel layout value path replacement) := by
  induction fuel generalizing value path replacement with
  | zero => exact preservesConstructionInvariant_stop _
  | succ fuel ih =>
      cases path with
      | nil => exact preservesConstructionInvariant_pure _
      | cons index rest =>
          cases value with
          | fixed elements | record id elements =>
              simp only [writeValuePath]
              cases present : elements[index]? with
              | none => exact preservesConstructionInvariant_stop _
              | some child =>
                  apply preservesConstructionInvariant_bind
                  · exact ih child rest replacement
                  · intro written; exact preservesConstructionInvariant_pure _
          | int _ _ | bool _ | unit | ref _ | slice _ _ _ => exact preservesConstructionInvariant_stop _
          | stored stored =>
              unfold writeValuePath
              apply preservesConstructionInvariant_bind
              · exact stateQuery_preservesConstructionInvariant _ (stateQuery_storedPathRun stored)
              · intro sampled
                rcases sampled with ⟨bytes, run⟩
                simp only
                apply preservesConstructionInvariant_bind
                · exact stateQuery_preservesConstructionInvariant _ (stateQuery_liftLayout _)
                · intro interval
                  rcases interval with ⟨start, finish⟩
                  simp only
                  apply preservesConstructionInvariant_bind
                  · exact stateQuery_preservesConstructionInvariant _ (stateQuery_readStoredElement fuel layout stored index)
                  · intro child
                    split
                    · split
                      · exact preservesConstructionInvariant_stop _
                      · apply preservesConstructionInvariant_bind
                        · exact ih child rest replacement
                        · intro _; exact preservesConstructionInvariant_pure _
                    · apply preservesConstructionInvariant_bind
                      · exact ih child rest replacement
                      · intro written
                        apply preservesConstructionInvariant_bind
                        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_liftExcept _)
                        · intro part
                          split
                          · exact preservesConstructionInvariant_stop _
                          · apply preservesConstructionInvariant_get_bind
                            intro state fresh
                            cases present : state.construction.storage[stored.storage]? with
                            | none => exact fresh
                            | some receiving =>
                                exact (ConstructionProtocolPrimitives.storageFrame
                                  (predicate := predicate) state.construction _
                                  (by simp [Array.set!_eq_setIfInBounds]) fresh)

theorem preservesConstructionInvariant_writeLoc (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (replacement : Value) : (PreservesConstructionInvariant predicate) (writeLoc fuel layout location replacement) := by
  unfold writeLoc
  apply preservesConstructionInvariant_bind
  · exact preservesConstructionInvariant_get
  · intro state
    cases present : state.objects.lookup location.root with
    | none => exact preservesConstructionInvariant_stop _
    | some value =>
        apply preservesConstructionInvariant_bind
        · exact preservesConstructionInvariant_writeValuePath fuel layout value location.path replacement
        · intro written; exact preservesConstructionInvariant_bindRoot location.root written

theorem preservesConstructionInvariant_bindAll (act : Goose.Core.ActId) (scopeInst : Goose.Core.ScopeInst)
    (values : List (Goose.Core.VarId × Value)) : (PreservesConstructionInvariant predicate) (bindAll act scopeInst values) := by
  unfold bindAll
  apply preservesConstructionInvariant_bind
  · apply preservesConstructionInvariant_listForIn
    intro item _
    rcases item with ⟨localVar, value⟩
    apply preservesConstructionInvariant_bind
    · exact preservesConstructionInvariant_bindRoot _ value
    · intro _; exact preservesConstructionInvariant_pure _
  · intro _; exact preservesConstructionInvariant_pure _

theorem preservesConstructionInvariant_freshAct : (PreservesConstructionInvariant predicate) freshAct :=
  fun _ valid => valid

theorem preservesConstructionInvariant_freshScope : (PreservesConstructionInvariant predicate) freshScope :=
  fun _ valid => valid

theorem preservesConstructionInvariant_returned (act : Goose.Core.ActId) (carriers : List Carrier) :
    (PreservesConstructionInvariant predicate) (returned (α := α) act carriers) := fun _ valid => valid

theorem preservesConstructionInvariant_escaped (address : ExitAddress) (carriers : List Carrier) :
    (PreservesConstructionInvariant predicate) (escaped (α := α) address carriers) := fun _ valid => valid

theorem preservesConstructionInvariant_jump (target : Nat) (kind : JumpKind) :
    (PreservesConstructionInvariant predicate) (jump (α := α) target kind) := fun _ valid => valid

theorem constructionInvariant_scope_release (state : ExecutionState) (environment : RuntimeActivation)
    (scope scopeInst : Nat) (valid : (ExecutionInvariant predicate) state) :
    (ExecutionInvariant predicate) (releaseScopeState environment scope scopeInst state) := valid

theorem constructionInvariant_activation_filter (state : ExecutionState)
    (selection : RuntimeActivation → Bool) (valid : (ExecutionInvariant predicate) state) :
    (ExecutionInvariant predicate) { state with activations := state.activations.filter selection } := valid

theorem preservesConstructionInvariant_publishCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    (PreservesConstructionInvariant predicate) (publishCarriers origin carriers) := by
  unfold publishCarriers
  kernel_protocol

theorem preservesConstructionInvariant_publishOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (stored : StoredValue) (id : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (publishOwner fuel layout location stored id origin) := by
  cases fuel with
  | zero => exact preservesConstructionInvariant_stop _
  | succ fuel =>
      unfold publishOwner
      apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination id)
      · intro destination
        cases destination.use with
        | replacement old => exact preservesConstructionInvariant_stop _
        | child parent =>
            apply preservesConstructionInvariant_bind
            · kernel_protocol
            · intro _
              apply preservesConstructionInvariant_bind
              · exact stateQuery_preservesConstructionInvariant _ (stateQuery_storedDestination parent)
              · intro value; exact preservesConstructionInvariant_writeLoc fuel layout location _
        | receiver =>
            apply preservesConstructionInvariant_bind
            · exact preservesConstructionInvariant_publishCarriers _ _
            · intro _
              apply preservesConstructionInvariant_bind
              · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getStorage stored.storage)
              · intro receiving; exact preservesConstructionInvariant_writeLoc fuel layout location _

theorem preservesConstructionInvariant_repeatElement (fuel : Nat) (layout : LayoutEnv) (parent : Goose.Core.DestinationId)
    (element : Ty) (source : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (repeatElement fuel layout parent element source origin) := by
  cases fuel with
  | zero => exact preservesConstructionInvariant_stop _
  | succ fuel =>
      unfold repeatElement
      apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_storedDestination source)
      · intro stored
        apply preservesConstructionInvariant_bind
        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getStorage stored.storage)
        · intro receiving
          apply preservesConstructionInvariant_bind
          · exact stateQuery_preservesConstructionInvariant _ (stateQuery_liftLayout _)
          · intro finish
            apply preservesConstructionInvariant_bind
            · kernel_protocol
            · intro _; kernel_protocol

theorem fixed_writes_preserveConstructionInvariant (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (element : Ty) (origin : Goose.Core.OriginId) (values : Array Value) :
    (PreservesConstructionInvariant predicate) (forIn values PUnit.unit fun value _ => do
      let bytes ← liftExcept (fixedBytes fuel layout element value)
      liftConstruction origin (writeElement destination bytes)
      pure (.yield PUnit.unit)) := by
  apply preservesConstructionInvariant_arrayForIn
  intro value _
  apply preservesConstructionInvariant_bind
  · exact stateQuery_preservesConstructionInvariant _ (stateQuery_liftExcept _)
  · intro bytes
    apply preservesConstructionInvariant_bind
    · kernel_protocol
    · intro _; exact preservesConstructionInvariant_pure _

theorem packed_writes_preserveConstructionInvariant (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (bytes : ByteArray) (run : SampledRun) (start count : Nat) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (forIn ([0:count] : Std.Legacy.Range) PUnit.unit fun index _ => do
      let (low, high) ← liftLayout (elementInterval fuel layout bytes run (start + index))
      liftConstruction origin (writeElement destination (bytes.extract low high))
      pure (.yield PUnit.unit)) := by
  apply preservesConstructionInvariant_rangeForIn
  intro index _
  apply preservesConstructionInvariant_bind
  · exact stateQuery_preservesConstructionInvariant _ (stateQuery_liftLayout _)
  · intro interval
    rcases interval with ⟨low, high⟩
    simp only
    apply preservesConstructionInvariant_bind
    · kernel_protocol
    · intro _; exact preservesConstructionInvariant_pure _

theorem preservesConstructionInvariant_copyValue (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (value : Value) (origin : Goose.Core.OriginId) (source : Option Goose.Core.CopySource) :
    (PreservesConstructionInvariant predicate) (copyValue fuel layout destination value origin source) := by
  cases fuel with
  | zero => exact preservesConstructionInvariant_stop _
  | succ fuel =>
      unfold copyValue
      apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination destination)
      · intro pending
        cases elementFound : elementType pending.capability.logicalType with
        | none => exact preservesConstructionInvariant_stop _
        | some element =>
            cases value with
            | int _ _ | bool _ | unit | record _ _ | ref _ => exact preservesConstructionInvariant_stop _
            | stored stored =>
                apply preservesConstructionInvariant_bind
                · exact stateQuery_preservesConstructionInvariant _ (stateQuery_sampledStored stored)
                · intro sampled
                  rcases sampled with ⟨bytes, run⟩
                  simp only
                  split
                  · exact preservesConstructionInvariant_stop _
                  · apply preservesConstructionInvariant_bind
                    · kernel_protocol
                    · intro _
                      apply preservesConstructionInvariant_bind
                      · simpa only [Nat.zero_add] using packed_writes_preserveConstructionInvariant fuel layout destination bytes run 0 run.count origin
                      · intro _; kernel_protocol
            | fixed values =>
                cases source with
                | none =>
                    apply preservesConstructionInvariant_bind
                    · exact fixed_writes_preserveConstructionInvariant fuel layout destination element origin values
                    · intro _; kernel_protocol
                | some source =>
                    apply preservesConstructionInvariant_bind
                    · kernel_protocol
                    · intro _
                      apply preservesConstructionInvariant_bind
                      · exact fixed_writes_preserveConstructionInvariant fuel layout destination element origin values
                      · intro _; kernel_protocol
            | slice location start count =>
                apply preservesConstructionInvariant_bind
                · exact stateQuery_preservesConstructionInvariant _ (stateQuery_readLoc fuel layout location)
                · intro backing
                  cases source with
                  | none => exact preservesConstructionInvariant_stop _
                  | some source =>
                      cases backing with
                      | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ => exact preservesConstructionInvariant_stop _
                      | stored stored =>
                          apply preservesConstructionInvariant_bind
                          · exact stateQuery_preservesConstructionInvariant _ (stateQuery_storedPathRun stored)
                          · intro sampled
                            rcases sampled with ⟨bytes, run⟩
                            simp only
                            split
                            · exact preservesConstructionInvariant_stop _
                            · split
                              · exact preservesConstructionInvariant_stop _
                              · apply preservesConstructionInvariant_bind
                                · kernel_protocol
                                · intro _
                                  apply preservesConstructionInvariant_bind
                                  · exact packed_writes_preserveConstructionInvariant fuel layout destination bytes run start count origin
                                  · intro _; kernel_protocol
                      | fixed values =>
                          simp only
                          split
                          · exact preservesConstructionInvariant_stop _
                          · apply preservesConstructionInvariant_bind
                            · kernel_protocol
                            · intro _
                              apply preservesConstructionInvariant_bind
                              · exact fixed_writes_preserveConstructionInvariant fuel layout destination element origin (values.extract start (start + count))
                              · intro _; kernel_protocol

theorem preservesConstructionInvariant_deliverCarriers (fuel : Nat) (layout : LayoutEnv) (channels : List Channel)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (deliverCarriers fuel layout channels carriers origin) := by
  unfold deliverCarriers
  split
  · exact preservesConstructionInvariant_stop _
  · apply preservesConstructionInvariant_listMapM
    intro item
    rcases item with ⟨channel, carrier⟩
    cases channel <;> cases carrier <;> first
      | exact preservesConstructionInvariant_pure _
      | exact preservesConstructionInvariant_stop _
      | (apply preservesConstructionInvariant_bind
         · exact preservesConstructionInvariant_copyValue _ _ _ _ _ _
         · intro _; exact preservesConstructionInvariant_pure _)

theorem preservesConstructionInvariant_cleanupDestination (origin : Goose.Core.OriginId)
    (id : Goose.Core.DestinationId) (carriers : List Carrier) :
    (PreservesConstructionInvariant predicate) (cleanupDestination origin id carriers) := by
  unfold cleanupDestination
  apply preservesConstructionInvariant_bind
  · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination id)
  · intro destination
    split
    · exact preservesConstructionInvariant_pure _
    · apply preservesConstructionInvariant_bind
      · exact preservesConstructionInvariant_get
      · intro state
        split
        · kernel_protocol
        · split
          · exact preservesConstructionInvariant_pure _
          · kernel_protocol

theorem preservesConstructionInvariant_protectDestination (origin : Goose.Core.OriginId)
    (id : Goose.Core.DestinationId) (action : EvalM α) (preserved : (PreservesConstructionInvariant predicate) action) :
    (PreservesConstructionInvariant predicate) (protectDestination origin id action) := by
  intro state valid
  have after := preserved state valid
  cases result : action state with
  | ok value final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using after
  | stop reason final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      have cleaned := preservesConstructionInvariant_cleanupDestination origin id carriers final after
      cases cleanup : cleanupDestination origin id carriers final <;>
        simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned
  | jump target kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      cases kind with
      | breakValue carriers =>
          have cleaned := preservesConstructionInvariant_cleanupDestination origin id carriers final after
          cases cleanup : cleanupDestination origin id carriers final <;>
            simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned
      | continueLoop =>
          have cleaned := preservesConstructionInvariant_cleanupDestination origin id [] final after
          cases cleanup : cleanupDestination origin id [] final <;>
            simpa [protectDestination, result, cleanup, Goose.Proofs.Exit.stepState] using cleaned

theorem preservesConstructionInvariant_landCarrier (origin : Goose.Core.OriginId) (carrier : Carrier) :
    (PreservesConstructionInvariant predicate) (landCarrier origin carrier) := by
  unfold landCarrier
  cases carrier with
  | register value => exact preservesConstructionInvariant_pure _
  | completed id =>
      apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination id)
      · intro destination
        cases destination.use with
        | replacement old => kernel_protocol
        | receiver | child parent => exact preservesConstructionInvariant_pure _

theorem preservesConstructionInvariant_landCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    (PreservesConstructionInvariant predicate) (landCarriers origin carriers) := by
  unfold landCarriers
  apply preservesConstructionInvariant_bind
  · apply preservesConstructionInvariant_listForIn
    intro carrier _
    apply preservesConstructionInvariant_bind
    · exact preservesConstructionInvariant_landCarrier origin carrier
    · intro _; exact preservesConstructionInvariant_pure _
  · intro _; exact preservesConstructionInvariant_pure _

theorem preservesConstructionInvariant_finishChannel (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (carrier : Carrier) (result : Ty) : (PreservesConstructionInvariant predicate) (finishChannel layout origin carrier result) := by
  unfold finishChannel
  cases carrier with
  | register value => exact preservesConstructionInvariant_pure _
  | completed id =>
      apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination id)
      · intro destination
        simp only
        split
        · kernel_protocol
        · split <;> split
          all_goals
            first
              | kernel_protocol
              | (apply preservesConstructionInvariant_bind
                 · kernel_protocol
                 · intro _
                   apply preservesConstructionInvariant_bind
                   · exact stateQuery_preservesConstructionInvariant _ (stateQuery_receivingLayout layout destination.capability.layout)
                   · intro receiving
                     apply preservesConstructionInvariant_bind
                     · kernel_protocol
                     · intro _; kernel_protocol)

theorem preservesConstructionInvariant_finishChannels (layout : LayoutEnv) (types : List Ty)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (finishChannels layout types carriers origin) := by
  unfold finishChannels
  apply preservesConstructionInvariant_bind
  · exact preservesConstructionInvariant_landCarriers origin carriers
  · intro _
    split
    · exact preservesConstructionInvariant_stop _
    · apply preservesConstructionInvariant_bind
      · apply preservesConstructionInvariant_listForIn
        intro item _
        rcases item with ⟨carrier, result⟩
        apply preservesConstructionInvariant_bind
        · exact preservesConstructionInvariant_finishChannel layout origin carrier result
        · intro _; exact preservesConstructionInvariant_pure _
      · intro _; exact preservesConstructionInvariant_pure _

theorem preservesConstructionInvariant_withScope (activation : RuntimeActivation) (scope scopeInst : Nat)
    (action : EvalM α) (preserved : (PreservesConstructionInvariant predicate) action) :
    (PreservesConstructionInvariant predicate) (withScope activation scope scopeInst action) := by
  intro state valid
  have after := preserved state valid
  cases result : action state with
  | ok value final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using constructionInvariant_scope_release final activation scope scopeInst after
  | stop reason final =>
      simpa [withScope, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using constructionInvariant_scope_release final activation scope scopeInst after
  | jump target kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      simpa [withScope, result, releaseScope, EvalM.get, EvalM.set, bind,
        Goose.Proofs.Exit.stepState] using constructionInvariant_scope_release final activation scope scopeInst after

theorem preservesConstructionInvariant_finishActivation (layout : LayoutEnv) (activation : RuntimeActivation)
    (types : List Ty) (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (preserved : (PreservesConstructionInvariant predicate) action) :
    (PreservesConstructionInvariant predicate) (finishActivation layout activation types origin action) := by
  intro state valid
  have after := preserved state valid
  cases result : action state with
  | ok carriers final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      let trimmed : ExecutionState := { final with
        activations := final.activations.filter (fun current => current.act != activation.act) }
      have trimmedValid : (ExecutionInvariant predicate) trimmed := constructionInvariant_activation_filter final _ after
      have landedValid := preservesConstructionInvariant_finishChannels layout types carriers origin trimmed trimmedValid
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
        have trimmedValid : (ExecutionInvariant predicate) trimmed := constructionInvariant_activation_filter final _ after
        have landedValid := preservesConstructionInvariant_finishChannels layout types carriers origin trimmed trimmedValid
        cases finished : finishChannels layout types carriers origin trimmed <;>
          simpa [finishActivation, result, caught, trimmed, finished, Goose.Proofs.Exit.stepState] using landedValid
      · simpa [finishActivation, result, caught, Goose.Proofs.Exit.stepState] using
          constructionInvariant_activation_filter final (fun current => current.act != activation.act) after

theorem preservesConstructionInvariant_withBreakTarget (act : Goose.Core.ActId) (scope : BreakScope)
    (channels : List Channel) (action : EvalM α) (receive : JumpKind → EvalM α)
    (preserved : (PreservesConstructionInvariant predicate) action) (received : ∀ kind, (PreservesConstructionInvariant predicate) (receive kind)) :
    (PreservesConstructionInvariant predicate) (withBreakTarget act scope channels action receive) := by
  intro state valid
  let target : BreakTarget := ⟨state.nextScope, act, scope, channels⟩
  let installed : ExecutionState := { state with
    nextScope := state.nextScope + 1, breaks := target :: state.breaks }
  have installedValid : (ExecutionInvariant predicate) installed := valid
  have after := preserved installed installedValid
  cases result : action installed with
  | ok value final =>
      simpa [withBreakTarget, installed, target, result, mapStepState, Goose.Proofs.Exit.stepState, ExecutionInvariant] using after
  | stop reason final =>
      simpa [withBreakTarget, installed, target, result, mapStepState, Goose.Proofs.Exit.stepState, ExecutionInvariant] using after
  | escape activation carriers final =>
      simpa [withBreakTarget, installed, target, result, mapStepState, Goose.Proofs.Exit.stepState, ExecutionInvariant] using after
  | jump actual kind final =>
      simp only [result, Goose.Proofs.Exit.stepState] at after
      let removed : ExecutionState := { final with breaks := final.breaks.filter (fun entry => entry.id != state.nextScope) }
      have removedValid : (ExecutionInvariant predicate) removed := after
      by_cases caught : actual = state.nextScope
      · simpa [withBreakTarget, installed, target, result, caught, removed, mapStepState,
          Goose.Proofs.Exit.stepState] using received kind removed removedValid
      · simpa [withBreakTarget, installed, target, result, caught, removed, mapStepState,
          Goose.Proofs.Exit.stepState] using removedValid

theorem preservesConstructionInvariant_truncateOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (count : Nat) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (truncateOwner fuel layout location count origin) := by
  cases fuel with
  | zero => exact preservesConstructionInvariant_stop _
  | succ fuel =>
      unfold truncateOwner
      apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact preservesConstructionInvariant_stop _
        | stored stored =>
            apply preservesConstructionInvariant_bind
            · exact stateQuery_preservesConstructionInvariant _ (stateQuery_sampledStored stored)
            · intro sampled
              rcases sampled with ⟨bytes, run⟩
              simp only
              split
              · exact preservesConstructionInvariant_stop _
              · apply preservesConstructionInvariant_bind
                · exact stateQuery_preservesConstructionInvariant _ (stateQuery_liftLayout _)
                · intro finish
                  cases stored.destination with
                  | none =>
                      apply preservesConstructionInvariant_bind
                      · exact preservesConstructionInvariant_pure _
                      · intro owner
                        apply preservesConstructionInvariant_bind
                        · kernel_protocol
                        · intro _; exact preservesConstructionInvariant_writeLoc _ _ _ _
                  | some id =>
                      apply preservesConstructionInvariant_bind
                      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination id)
                      · intro pending
                        apply preservesConstructionInvariant_bind
                        · exact preservesConstructionInvariant_pure _
                        · intro owner
                          apply preservesConstructionInvariant_bind
                          · kernel_protocol
                          · intro _; exact preservesConstructionInvariant_writeLoc _ _ _ _

theorem preservesConstructionInvariant_publishElementReceiving (fuel : Nat) (layout : LayoutEnv)
    (location : Goose.Core.Loc) (stored : StoredValue) (destination : Goose.Core.DestinationId)
    (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (publishElementReceiving fuel layout location stored destination origin) := by
  cases fuel with
  | zero => exact preservesConstructionInvariant_stop _
  | succ fuel =>
      unfold publishElementReceiving
      apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination destination)
      · intro pending
        cases pending.use with
        | replacement _ => exact preservesConstructionInvariant_stop _
        | child parent =>
            apply preservesConstructionInvariant_bind
            · kernel_protocol
            · intro _
              apply preservesConstructionInvariant_bind
              · exact stateQuery_preservesConstructionInvariant _ (stateQuery_storedDestination parent)
              · intro value; exact preservesConstructionInvariant_writeLoc _ _ _ _
        | receiver =>
            apply preservesConstructionInvariant_bind
            · kernel_protocol
            · intro _
              apply preservesConstructionInvariant_bind
              · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getStorage stored.storage)
              · intro value; exact preservesConstructionInvariant_writeLoc _ _ _ _

theorem preservesConstructionInvariant_emitStdout (bytes : ByteArray) :
    (PreservesConstructionInvariant predicate) (emitStdout bytes) := by
  unfold emitStdout
  kernel_protocol

theorem preservesConstructionInvariant_allocateActivation (make : Goose.Core.ActId → RuntimeActivation)
    (action : RuntimeActivation → EvalM α)
    (preserved : ∀ activation, (PreservesConstructionInvariant predicate) (action activation)) :
    (PreservesConstructionInvariant predicate) (do
      let act ← freshAct
      let activation := make act
      let state ← EvalM.get
      EvalM.set { state with activations := activation :: state.activations }
      action activation) := by
  intro state valid
  simpa [freshAct, EvalM.get, EvalM.set, bind, pure, ExecutionInvariant] using
    preserved (make state.nextAct)
      { state with nextAct := state.nextAct + 1, activations := make state.nextAct :: state.activations } valid

theorem preservesConstructionInvariant_newDestination (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (storage : Option Goose.Core.StorageId) (knownCount : Option Nat) :
    (PreservesConstructionInvariant predicate) (newDestination layout owner ty request origin storage knownCount) := by
  unfold newDestination
  cases storage with
  | none =>
      apply preservesConstructionInvariant_bind
      · kernel_protocol
      · intro storage
        apply preservesConstructionInvariant_bind
        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_receivingLayout layout ty)
        · intro receiving; kernel_protocol
  | some storage =>
      apply preservesConstructionInvariant_bind
      · exact preservesConstructionInvariant_pure _
      · intro storage
        apply preservesConstructionInvariant_bind
        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_receivingLayout layout ty)
        · intro receiving; kernel_protocol

theorem preservesConstructionInvariant_channelsFor (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (results : List ResultDescriptor) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (channelsFor layout owner results origin) := by
  unfold channelsFor
  apply preservesConstructionInvariant_listMapM
  intro descriptor
  cases descriptor.request with
  | register => exact preservesConstructionInvariant_pure _
  | value | elementRun =>
      apply preservesConstructionInvariant_bind
      · exact preservesConstructionInvariant_newDestination _ _ _ _ _ _ _
      · intro destination; exact preservesConstructionInvariant_pure _

theorem preservesConstructionInvariant_ownerDestination (layout : LayoutEnv) (stored : StoredValue)
    (request : Goose.Core.ConstructionRequest) (count : Option Nat) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (ownerDestination layout stored request count origin) := by
  unfold ownerDestination
  cases stored.destination with
  | none => exact preservesConstructionInvariant_newDestination _ _ _ _ _ _ _
  | some id =>
      apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination id)
      · intro destination
        cases destination.progress <;> first
          | kernel_protocol
          | exact preservesConstructionInvariant_newDestination _ _ _ _ _ _ _
          | exact preservesConstructionInvariant_stop _

theorem preservesConstructionInvariant_appendFixedValues (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (values : List Value) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (appendFixedValues fuel layout location values origin) := by
  cases fuel with
  | zero => exact preservesConstructionInvariant_stop _
  | succ fuel =>
      unfold appendFixedValues
      apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact preservesConstructionInvariant_stop _
        | stored stored =>
            simp only
            cases elementFound : elementType stored.ty with
            | none => exact preservesConstructionInvariant_stop _
            | some element =>
                apply preservesConstructionInvariant_bind
                · apply preservesConstructionInvariant_listMapM
                  intro value; exact stateQuery_preservesConstructionInvariant _ (stateQuery_liftExcept _)
                · intro parts
                  apply preservesConstructionInvariant_bind
                  · exact preservesConstructionInvariant_ownerDestination _ _ _ _ _
                  · intro destination
                    apply preservesConstructionInvariant_bind
                    · apply preservesConstructionInvariant_listForIn
                      intro bytes state
                      apply preservesConstructionInvariant_bind
                      · kernel_protocol
                      · intro _; exact preservesConstructionInvariant_pure _
                    · intro _
                      apply preservesConstructionInvariant_bind
                      · kernel_protocol
                      · intro _
                        apply preservesConstructionInvariant_bind
                        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_completedDestination destination)
                        · intro completed; exact preservesConstructionInvariant_publishOwner _ _ _ _ _ _

theorem preservesConstructionInvariant_appendRun (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (view : RuntimeView) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (appendRun fuel layout location view origin) := by
  cases fuel with
  | zero => exact preservesConstructionInvariant_stop _
  | succ fuel =>
      unfold appendRun
      apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact preservesConstructionInvariant_stop _
        | stored stored =>
            apply preservesConstructionInvariant_bind
            · exact stateQuery_preservesConstructionInvariant _ (stateQuery_readLoc fuel layout view.location)
            · intro source
              apply preservesConstructionInvariant_bind
              · exact preservesConstructionInvariant_ownerDestination _ _ _ _ _
              · intro destination
                have finish : (PreservesConstructionInvariant predicate) (do
                    liftConstruction origin (finishDestination destination)
                    let completed ← completedDestination destination
                    publishOwner fuel layout location stored completed origin) := by
                  apply preservesConstructionInvariant_bind
                  · kernel_protocol
                  · intro _
                    apply preservesConstructionInvariant_bind
                    · exact stateQuery_preservesConstructionInvariant _ (stateQuery_completedDestination destination)
                    · intro completed; exact preservesConstructionInvariant_publishOwner _ _ _ _ _ _
                cases source with
                | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ =>
                    apply preservesConstructionInvariant_bind
                    · exact preservesConstructionInvariant_stop _
                    · intro _; exact finish
                | stored source =>
                      apply preservesConstructionInvariant_bind
                      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_sampledStored source)
                      · intro sampled
                        rcases sampled with ⟨bytes, run⟩
                        apply preservesConstructionInvariant_bind
                        · kernel_protocol
                        · intro _
                          apply preservesConstructionInvariant_bind
                          · exact packed_writes_preserveConstructionInvariant fuel layout destination bytes run view.start view.count origin
                          · intro _; exact finish
                | fixed values =>
                      simp only
                      cases elementFound : elementType stored.ty with
                      | none =>
                          apply preservesConstructionInvariant_bind
                          · exact preservesConstructionInvariant_stop _
                          · intro _; exact finish
                      | some element =>
                        apply preservesConstructionInvariant_bind
                        ·
                          apply preservesConstructionInvariant_rangeForIn
                          intro index current
                          split
                          · apply preservesConstructionInvariant_bind
                            · exact stateQuery_preservesConstructionInvariant _ (stateQuery_liftExcept _)
                            · intro bytes
                              apply preservesConstructionInvariant_bind
                              · kernel_protocol
                              · intro _; exact preservesConstructionInvariant_pure _
                          · apply preservesConstructionInvariant_bind
                            · exact preservesConstructionInvariant_stop _
                            · intro _; exact preservesConstructionInvariant_pure _
                        · intro _; exact finish

theorem preservesConstructionInvariant_constructLocal (declarations : DeclarationEnv) (owner : Goose.Core.ActId) (ty : Ty)
    (origin : Goose.Core.OriginId) (expression : Expr) (construct : Goose.Core.DestinationId → EvalM Unit)
    (preserved : ∀ destination, (PreservesConstructionInvariant predicate) (construct destination)) :
    (PreservesConstructionInvariant predicate) (constructLocal declarations owner ty origin expression construct) := by
  unfold constructLocal
  apply preservesConstructionInvariant_bind
  · exact preservesConstructionInvariant_newDestination _ _ _ _ _ _ _
  · intro destination
    apply preservesConstructionInvariant_bind
    · exact preserved destination
    · intro _
      apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_completedDestination destination)
      · intro completed
        apply preservesConstructionInvariant_bind
        · exact preservesConstructionInvariant_publishCarriers _ _
        · intro _; exact preservesConstructionInvariant_pure _

theorem preservesConstructionInvariant_exitChannels (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) : (PreservesConstructionInvariant predicate) (exitChannels source activation operands origin) := by
  unfold exitChannels
  split
  · exact preservesConstructionInvariant_stop _
  · apply preservesConstructionInvariant_listMapM
    intro item
    rcases item with ⟨channel, operand⟩
    cases channel with
    | register ty => exact preservesConstructionInvariant_pure _
    | construct id =>
        apply preservesConstructionInvariant_bind
        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination id)
        · intro destination
          have finish (alias : Bool) : (PreservesConstructionInvariant predicate)
              (if (match destination.progress with | .open 0 => true | _ => false) || alias then
                pure (Channel.construct id)
              else do pure (Channel.construct (← liftConstruction origin (openExitReplacement id)))) := by
            split <;> split
            all_goals first
              | exact preservesConstructionInvariant_pure _
              | (apply preservesConstructionInvariant_bind
                 · kernel_protocol
                 · intro _; exact preservesConstructionInvariant_pure _)
          cases operand <;> first
            | (apply preservesConstructionInvariant_bind
               · exact preservesConstructionInvariant_pure _
               · intro alias; exact finish alias)
            | (apply preservesConstructionInvariant_bind
               · exact stateQuery_preservesConstructionInvariant _ (stateQuery_rootOf _ _)
               · intro root
                 apply preservesConstructionInvariant_bind
                 · exact preservesConstructionInvariant_get
                 · intro state
                   split
                   all_goals
                     apply preservesConstructionInvariant_bind
                     · exact preservesConstructionInvariant_pure _
                     · intro alias; exact finish alias)

theorem preservesConstructionInvariant_openElementReceiving (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (location : Goose.Core.Loc) (stored : StoredValue) (element : Ty) (known : Option Nat)
    (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (openElementReceiving layout owner location stored element known origin) := by
  unfold openElementReceiving
  apply preservesConstructionInvariant_bind
  · exact stateQuery_preservesConstructionInvariant _ (stateQuery_sampledStored stored)
  · intro sampled
    rcases sampled with ⟨bytes, run⟩
    apply preservesConstructionInvariant_bind
    · exact stateQuery_preservesConstructionInvariant _ (stateQuery_receivingLayout layout element)
    · intro receiving
      cases stored.destination with
      | none => kernel_protocol
      | some id =>
          apply preservesConstructionInvariant_bind
          · exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination id)
          · intro pending
            cases pending.progress <;> first
              | kernel_protocol
              | exact preservesConstructionInvariant_stop _

end Goose.Proofs.ConstructionExecutionProtocol
