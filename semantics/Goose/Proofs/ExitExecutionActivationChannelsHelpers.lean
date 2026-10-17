import Goose.Proofs.ExitExecutionActivationChannelsContext

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem preservesActivationChannels_reserveRootObject (root : Goose.Core.RootInst) :
    PreservesActivationChannels (reserveRootObject root) := by
  unfold reserveRootObject
  apply preservesActivationChannels_bind EvalM.get _ preservesActivationChannels_get preservesFresh_get
  intro state
  cases present : state.objectOrdinals.lookup root with
  | some ordinal => exact preservesActivationChannels_pure ordinal
  | none =>
      apply preservesActivationChannels_bind (liftConstruction 0 reserveStorage) _
        (preservesActivationChannels_liftConstruction 0 reserveStorage)
        (preservesFresh_lift 0 reserveStorage)
      intro ordinal
      apply preservesActivationChannels_bind (setObjectOrdinal root ordinal) _
        (preservesActivationChannels_setObjectOrdinal root ordinal)
        (preservesFresh_setObjectOrdinal root ordinal)
      intro _
      exact preservesActivationChannels_pure ordinal

theorem preservesActivationChannels_bindRoot (root : Goose.Core.RootInst) (value : Value) :
    PreservesActivationChannels (bindRoot root value) := by
  unfold bindRoot
  apply preservesActivationChannels_bind EvalM.get _ preservesActivationChannels_get preservesFresh_get
  intro state
  cases present : state.objectOrdinals.lookup root with
  | some ordinal => exact preservesActivationChannels_bindStaticRoot root value
  | none =>
      cases value with
      | stored stored =>
          apply preservesActivationChannels_bind (setObjectOrdinal root (stored.object.getD stored.storage)) _
            (preservesActivationChannels_setObjectOrdinal root _)
            (preservesFresh_setObjectOrdinal root _)
          intro _
          exact preservesActivationChannels_bindStaticRoot root (.stored stored)
      | int _ _ | bool _ | unit | fixed _ | record _ _ | slice _ _ _ | ref _ =>
          apply preservesActivationChannels_bind (reserveRootObject root) _
            (preservesActivationChannels_reserveRootObject root) (preservesFresh_reserveRootObject root)
          intro _
          exact preservesActivationChannels_bindStaticRoot root _

theorem preservesActivationChannels_newDestination (module : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (storage : Option Goose.Core.StorageId) (knownCount : Option Nat) :
    PreservesActivationChannels (newDestination module owner ty request origin storage knownCount) := by
  cases storage with
  | some storage =>
      simp only [newDestination]
      apply preservesActivationChannels_bind (receivingLayout module ty) _
      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_receivingLayout module ty)
      · exact stateQuery_preservesFresh _ (stateQuery_receivingLayout module ty)
      · intro layout
        exact preservesActivationChannels_liftConstruction origin
          (openDestination storage ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ layout knownCount)
  | none =>
      simp only [newDestination]
      apply preservesActivationChannels_bind (liftConstruction origin reserveStorage) _
      · exact preservesActivationChannels_liftConstruction origin reserveStorage
      · exact preservesFresh_lift origin reserveStorage
      · intro storage
        apply preservesActivationChannels_bind (receivingLayout module ty) _
        · exact preservesActivationChannels_of_stateQuery _ (stateQuery_receivingLayout module ty)
        · exact stateQuery_preservesFresh _ (stateQuery_receivingLayout module ty)
        · intro layout
          exact preservesActivationChannels_liftConstruction origin
            (openDestination storage ⟨0, ⟨.local owner 0 0, []⟩, ty, ty, request, 0, owner⟩ layout knownCount)

theorem preservesActivationChannels_channelsFor (module : LayoutEnv) (owner : Goose.Core.ActId)
    (results : List ResultDescriptor) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (channelsFor module owner results origin) := by
  unfold channelsFor
  apply preservesActivationChannels_listMapM
  · intro descriptor
    cases request : descriptor.request with
    | register => exact preservesActivationChannels_pure _
    | value =>
        apply preservesActivationChannels_bind
          (newDestination module owner descriptor.ty .value origin none none) _
        · exact preservesActivationChannels_newDestination module owner descriptor.ty .value origin none none
        · exact preservesFresh_newDestination module owner descriptor.ty .value origin none none
        · intro destination
          exact preservesActivationChannels_pure _
    | elementRun =>
        apply preservesActivationChannels_bind
          (newDestination module owner descriptor.ty .elementRun origin none none) _
        · exact preservesActivationChannels_newDestination module owner descriptor.ty .elementRun origin none none
        · exact preservesFresh_newDestination module owner descriptor.ty .elementRun origin none none
        · intro destination
          exact preservesActivationChannels_pure _
  · intro descriptor
    cases request : descriptor.request with
    | register => exact preservesFresh_pure _
    | value =>
        apply preservesFresh_bind (newDestination module owner descriptor.ty .value origin none none)
        · exact preservesFresh_newDestination module owner descriptor.ty .value origin none none
        · intro _; exact preservesFresh_pure _
    | elementRun =>
        apply preservesFresh_bind (newDestination module owner descriptor.ty .elementRun origin none none)
        · exact preservesFresh_newDestination module owner descriptor.ty .elementRun origin none none
        · intro _; exact preservesFresh_pure _

theorem preservesActivationChannels_publishCarriers (origin : Goose.Core.OriginId)
    (carriers : List Carrier) : PreservesActivationChannels (publishCarriers origin carriers) := by
  unfold publishCarriers
  apply preservesActivationChannels_bind (carriers.mapM fun carrier => match carrier with
    | .completed destination => pure (some destination)
    | .register _ => pure none
    | .pendingNamed _ => fault .flow) _
  · apply preservesActivationChannels_listMapM
    · intro carrier
      cases carrier with
      | completed destination => exact preservesActivationChannels_pure _
      | register value => exact preservesActivationChannels_pure _
      | pendingNamed ticket => exact preservesActivationChannels_fault _
    · intro carrier
      cases carrier with
      | completed destination => exact preservesFresh_pure _
      | register value => exact preservesFresh_pure _
      | pendingNamed ticket => exact preservesFresh_stop _
  · exact preservesFresh_listMapM _ _ (by
      intro carrier
      cases carrier with
      | completed destination => exact preservesFresh_pure _
      | register value => exact preservesFresh_pure _
      | pendingNamed ticket => exact preservesFresh_stop _)
  · intro ids
    exact preservesActivationChannels_liftConstruction origin (publishOperation (ids.filterMap id))

theorem stateQuery_completedReceivingDestination (id : Goose.Core.DestinationId) :
    StateQuery (completedReceivingDestination id) := by
  unfold completedReceivingDestination
  apply stateQuery_bind
  · exact stateQuery_receivingDestination id
  · intro current
    exact stateQuery_completedDestination current

theorem preservesActivationChannels_completedReceivingDestination (id : Goose.Core.DestinationId) :
    PreservesActivationChannels (completedReceivingDestination id) :=
  preservesActivationChannels_of_stateQuery _ (stateQuery_completedReceivingDestination id)

theorem preservesActivationChannels_cleanupDestination (config : EvalConfig)
    (origin : Goose.Core.OriginId) (id : Goose.Core.DestinationId) (carriers : List Carrier) :
    PreservesActivationChannels (cleanupDestination origin id carriers) := by
  unfold cleanupDestination
  have fresh0 := evaluationPreservesFresh_zero config
  have channels0 := evaluationActivationChannels_zero config
  activation_channels_eval fresh0 channels0

theorem preservesActivationChannels_cleanupReceivingDestination (config : EvalConfig)
    (origin : Goose.Core.OriginId) (incoming : Goose.Core.DestinationId) (carriers : List Carrier) :
    PreservesActivationChannels (cleanupReceivingDestination origin incoming carriers) := by
  unfold cleanupReceivingDestination
  apply preservesActivationChannels_bind (receivingDestination incoming) _
  · exact preservesActivationChannels_of_stateQuery _ (stateQuery_receivingDestination incoming)
  · exact stateQuery_preservesFresh _ (stateQuery_receivingDestination incoming)
  · intro current
    exact preservesActivationChannels_cleanupDestination config origin current carriers

theorem preservesActivationChannels_receivingDestination (id : Goose.Core.DestinationId) :
    PreservesActivationChannels (receivingDestination id) :=
  preservesActivationChannels_of_stateQuery _ (stateQuery_receivingDestination id)

theorem preservesActivationChannels_receivingAction (origin : Goose.Core.OriginId)
    (incoming : Goose.Core.DestinationId) (action : Goose.Core.DestinationId → ConstructionM α) :
    PreservesActivationChannels (receivingAction origin incoming action) := by
  unfold receivingAction
  exact preservesActivationChannels_liftConstruction origin _

theorem preservesActivationChannels_selectCompletionChannel (source : RuntimeActivation)
    (operand : Expr) (channel : Channel) :
    PreservesActivationChannels (selectCompletionChannel source operand channel) := by
  cases channel with
  | register _ | construct _ => exact preservesActivationChannels_pure _
  | completion token =>
      unfold selectCompletionChannel
      apply preservesActivationChannels_bind EvalM.get _ preservesActivationChannels_get preservesFresh_get
      intro state
      cases found : state.construction.exitReservations[token]? with
      | none => exact preservesActivationChannels_fault _
      | some entry =>
          cases entry with
          | waiting incoming =>
              apply preservesActivationChannels_bind (exitSource source incoming operand) _
              · exact preservesActivationChannels_of_stateQuery _ (stateQuery_exitSource source incoming operand)
              · exact stateQuery_preservesFresh _ (stateQuery_exitSource source incoming operand)
              · intro kind
                apply preservesActivationChannels_bind
                  (liftConstruction (expressionOrigin operand) (selectWaitingExitDestination token kind)) _
                · exact preservesActivationChannels_liftConstruction _ _
                · exact preservesFresh_lift _ _
                · intro selected; exact preservesActivationChannels_pure _
          | active _ _ _ _ | restored | released => exact preservesActivationChannels_fault _

private theorem preservesActivationChannels_updateStorage (id : Goose.Core.StorageId)
    (update : ReceivingStorage → ReceivingStorage) (result : α) :
    PreservesActivationChannels (do
      let state ← EvalM.get
      let some storage := state.construction.storage[id]? | fault .danglingRoot
      EvalM.set { state with construction := { state.construction with
        storage := state.construction.storage.set! id (update storage) } }
      pure result) := by
  intro state fresh
  dsimp only [bind, Bind.bind, EvalM.get]
  cases found : state.construction.storage[id]? with
  | none => exact preservesActivationChannels_fault .danglingRoot state fresh
  | some storage =>
      simp [ActivationChannelsOutcome, EvalM.set, pure, ActivationChannelsProjection]

theorem preservesActivationChannels_liftExcept (action : Except Goose.Core.Stop α) :
    PreservesActivationChannels (liftExcept action) :=
  preservesActivationChannels_of_stateQuery _ (stateQuery_liftExcept action)

theorem preservesActivationChannels_writeValuePath (fuel : Nat) (layout : LayoutEnv)
    (value : Value) (path : List Nat) (replacement : Value) :
    PreservesActivationChannels (writeValuePath fuel layout value path replacement) := by
  induction fuel generalizing value path replacement with
  | zero => exact preservesActivationChannels_stop _
  | succ fuel ih =>
      cases path with
      | nil => exact preservesActivationChannels_pure _
      | cons index rest =>
          cases value with
          | fixed elements | record _ elements =>
              simp only [writeValuePath]
              cases present : elements[index]? with
              | none => exact preservesActivationChannels_stop _
              | some child =>
                  apply preservesActivationChannels_bind (writeValuePath fuel layout child rest replacement) _
                  · exact ih child rest replacement
                  · exact preservesFresh_writeValuePath fuel layout child rest replacement
                  · intro written
                    exact preservesActivationChannels_pure _
          | stored stored =>
              unfold writeValuePath
              apply preservesActivationChannels_bind (storedPathRun stored) _
              · exact preservesActivationChannels_of_stateQuery _ (stateQuery_storedPathRun stored)
              · exact stateQuery_preservesFresh _ (stateQuery_storedPathRun stored)
              · intro sampled
                rcases sampled with ⟨bytes, run⟩
                simp only
                apply preservesActivationChannels_bind (liftLayout (elementInterval fuel layout bytes run index)) _
                · exact preservesActivationChannels_liftLayout _
                · exact stateQuery_preservesFresh _ (stateQuery_liftLayout _)
                · intro interval
                  rcases interval with ⟨start, finish⟩
                  simp only
                  apply preservesActivationChannels_bind (readStoredElement fuel layout stored index) _
                  · exact preservesActivationChannels_of_stateQuery _ (stateQuery_readStoredElement fuel layout stored index)
                  · exact stateQuery_preservesFresh _ (stateQuery_readStoredElement fuel layout stored index)
                  · intro child
                    split
                    · split
                      · exact preservesActivationChannels_stop _
                      · apply preservesActivationChannels_bind (writeValuePath fuel layout child rest replacement) _
                        · exact ih child rest replacement
                        · exact preservesFresh_writeValuePath fuel layout child rest replacement
                        · intro _; exact preservesActivationChannels_pure _
                    · apply preservesActivationChannels_bind (writeValuePath fuel layout child rest replacement) _
                      · exact ih child rest replacement
                      · exact preservesFresh_writeValuePath fuel layout child rest replacement
                      · intro written
                        dsimp only [bind, Bind.bind]
                        apply preservesActivationChannels_bind (liftExcept (fixedBytes fuel layout run.element written)) _
                        · exact preservesActivationChannels_liftExcept _
                        · exact stateQuery_preservesFresh _ (stateQuery_liftExcept _)
                        · intro part
                          split
                          · exact preservesActivationChannels_stop _
                          · exact preservesActivationChannels_updateStorage stored.storage _ _
          | int _ _ | bool _ | unit | ref _ | slice _ _ _ => exact preservesActivationChannels_stop _

theorem preservesActivationChannels_writeLoc (fuel : Nat) (layout : LayoutEnv)
    (location : Goose.Core.Loc) (replacement : Value) :
    PreservesActivationChannels (writeLoc fuel layout location replacement) := by
  unfold writeLoc
  apply preservesActivationChannels_bind EvalM.get _
  · exact preservesActivationChannels_get
  · exact preservesFresh_get
  · intro state
    cases present : state.objects.lookup location.root with
    | none => exact preservesActivationChannels_stop _
    | some value =>
        apply preservesActivationChannels_bind (writeValuePath fuel layout value location.path replacement) _
        · exact preservesActivationChannels_writeValuePath _ _ _ _ _
        · exact preservesFresh_writeValuePath _ _ _ _ _
        · intro written
          exact preservesActivationChannels_bindRoot location.root written

macro "activation_channels_runtime" : tactic => `(tactic|
  repeat' first
    | assumption
    | exact preservesActivationChannels_pure _
    | exact preservesActivationChannels_stop _
    | exact preservesActivationChannels_fault _
    | exact preservesActivationChannels_timeout
    | exact preservesActivationChannels_get
    | exact preservesActivationChannels_liftConstruction _ _
    | exact preservesActivationChannels_liftLayout _
    | exact preservesActivationChannels_liftExcept _
    | exact preservesActivationChannels_writeLoc _ _ _ _
    | exact preservesActivationChannels_of_stateQuery _ (stateQuery_readLoc _ _ _)
    | exact preservesActivationChannels_of_stateQuery _ (stateQuery_storedPathRun _)
    | exact preservesActivationChannels_of_stateQuery _ (stateQuery_sampledStored _)
    | exact preservesActivationChannels_of_stateQuery _ (stateQuery_arrayLength _)
    | exact preservesActivationChannels_of_stateQuery _ (stateQuery_getDestination _)
    | exact stateQuery_preservesFresh _ (stateQuery_readLoc _ _ _)
    | exact stateQuery_preservesFresh _ (stateQuery_storedPathRun _)
    | exact stateQuery_preservesFresh _ (stateQuery_sampledStored _)
    | exact stateQuery_preservesFresh _ (stateQuery_arrayLength _)
    | exact stateQuery_preservesFresh _ (stateQuery_getDestination _)
    | exact stateQuery_preservesFresh _ (stateQuery_liftExcept _)
    | exact stateQuery_preservesFresh _ (stateQuery_liftLayout _)
    | exact preservesFresh_lift _ _
    | exact preservesFresh_writeLoc _ _ _ _
    | exact preservesFresh_get
    | exact preservesFresh_pure _
    | exact preservesFresh_stop _
    | apply preservesActivationChannels_bind
    | apply preservesActivationChannels_conditional
    | rfl)

theorem preservesActivationChannels_truncateOwner (fuel : Nat) (layout : LayoutEnv)
    (location : Goose.Core.Loc) (count : Nat) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (truncateOwner fuel layout location count origin) := by
  cases fuel with
  | zero => exact preservesActivationChannels_stop _
  | succ fuel =>
      unfold truncateOwner
      apply preservesActivationChannels_bind
      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_readLoc fuel layout location)
      · exact stateQuery_preservesFresh _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ =>
            exact preservesActivationChannels_stop _
        | stored stored =>
            apply preservesActivationChannels_bind
            · exact preservesActivationChannels_of_stateQuery _ (stateQuery_sampledStored stored)
            · exact stateQuery_preservesFresh _ (stateQuery_sampledStored stored)
            · intro sampled
              rcases sampled with ⟨bytes, run⟩
              simp only
              split
              · exact preservesActivationChannels_stop _
              · apply preservesActivationChannels_bind (liftLayout (elementsEnd fuel layout run.element count bytes run.byteStart)) _
                · exact preservesActivationChannels_liftLayout _
                · exact stateQuery_preservesFresh _ (stateQuery_liftLayout _)
                · intro finish
                  cases stored.destination with
                  | none =>
                      dsimp only [bind, Bind.bind]
                      apply preservesActivationChannels_bind (liftConstruction origin
                        (truncateConstructionStorage stored.storage stored.start finish count none
                          (match stored.ty with | .limited _ _ => true | _ => false))) _
                      · exact preservesActivationChannels_liftConstruction _ _
                      · exact preservesFresh_lift _ _
                      · intro _
                        exact preservesActivationChannels_writeLoc fuel layout location
                          (.stored ⟨stored.storage, stored.start, stored.ty, count, none,
                            stored.object, stored.path, stored.writtenCount⟩)
                  | some id =>
                      apply preservesActivationChannels_bind (getDestination id) _
                      · exact preservesActivationChannels_of_stateQuery _ (stateQuery_getDestination id)
                      · exact stateQuery_preservesFresh _ (stateQuery_getDestination id)
                      · intro destination
                        dsimp only [bind, Bind.bind]
                        apply preservesActivationChannels_bind (liftConstruction origin
                        (truncateConstructionStorage stored.storage stored.start finish count
                          (match destination.progress with | .published _ => none | _ => some id)
                            (match stored.ty with | .limited _ _ => true | _ => false))) _
                        · exact preservesActivationChannels_liftConstruction _ _
                        · exact preservesFresh_lift _ _
                        · intro _
                          exact preservesActivationChannels_writeLoc fuel layout location
                            (.stored ⟨stored.storage, stored.start, stored.ty, count, some id,
                              stored.object, stored.path, stored.writtenCount⟩)

theorem preservesActivationChannels_constructLocal (declarations : DeclarationEnv)
    (owner : Goose.Core.ActId) (ty : Ty) (origin : Goose.Core.OriginId) (expression : Expr)
    (construct : Goose.Core.DestinationId → EvalM Unit)
    (channels : ∀ destination, PreservesActivationChannels (construct destination))
    (fresh : ∀ destination, PreservesFresh (construct destination)) :
    PreservesActivationChannels
      (constructLocal declarations owner ty origin expression construct) := by
  unfold constructLocal
  apply preservesActivationChannels_bind
    (newDestination (LayoutEnv.ofModule declarations.module) owner ty .value origin none
      (producerCount? declarations expression)) _
  · exact preservesActivationChannels_newDestination _ _ _ _ _ _ _
  · exact preservesFresh_newDestination _ _ _ _ _ _ _
  · intro destination
    apply preservesActivationChannels_bind (construct destination) _ (channels destination) (fresh destination)
    intro _
    apply preservesActivationChannels_bind (completedReceivingDestination destination) _
    · exact preservesActivationChannels_of_stateQuery _ (stateQuery_completedReceivingDestination destination)
    · exact preservesFresh_completedReceivingDestination destination
    · intro completed
      apply preservesActivationChannels_bind (publishCarriers origin [.completed completed])
        (fun _ => pure (Carrier.completed completed))
      · exact preservesActivationChannels_publishCarriers origin [.completed completed]
      · exact preservesFresh_publishCarriers origin [.completed completed]
      · intro _
        exact preservesActivationChannels_pure _

macro "activation_channels_helper_eval_core " fresh:ident channels:ident : tactic => `(tactic|
  activation_channels_eval $fresh $channels <;>
  all_goals repeat' first
    | exact preservesActivationChannels_reserveRootObject _
    | exact preservesActivationChannels_bindRoot _ _
    | exact preservesActivationChannels_newDestination _ _ _ _ _ _ _
    | exact preservesActivationChannels_channelsFor _ _ _ _
    | exact preservesActivationChannels_publishCarriers _ _
    | exact preservesActivationChannels_receivingDestination _
    | exact preservesActivationChannels_completedReceivingDestination _
    | exact preservesActivationChannels_selectCompletionChannel _ _ _
    | exact preservesActivationChannels_truncateOwner _ _ _ _ _
    | exact preservesActivationChannels_writeLoc _ _ _ _
    | apply preservesActivationChannels_constructLocal
      all_goals intro destination
      all_goals first
        | exact ($channels).build _ _ _
        | exact ($fresh).build _ _ _)

theorem preservesActivationChannels_prepareNamedCarrierAt (config : EvalConfig)
    (origin : Goose.Core.OriginId) (token : ExitReservationId)
    (incoming : Goose.Core.DestinationId) (stored : StoredValue) :
    PreservesActivationChannels (prepareNamedCarrierAt origin token incoming stored) := by
  unfold prepareNamedCarrierAt
  have fresh0 := evaluationPreservesFresh_zero config
  have channels0 := evaluationActivationChannels_zero config
  activation_channels_helper_eval_core fresh0 channels0

theorem preservesActivationChannels_prepareNamedCarrier (config : EvalConfig)
    (origin : Goose.Core.OriginId) (incoming : Goose.Core.DestinationId) (stored : StoredValue) :
    PreservesActivationChannels (prepareNamedCarrier origin incoming stored) := by
  unfold prepareNamedCarrier
  have fresh0 := evaluationPreservesFresh_zero config
  have channels0 := evaluationActivationChannels_zero config
  activation_channels_helper_eval_core fresh0 channels0

theorem preservesActivationChannels_landCarriersInto (config : EvalConfig)
    (origin : Goose.Core.OriginId) (channels : List Channel) (carriers : List Carrier) :
    PreservesActivationChannels (landCarriersInto origin channels carriers) := by
  unfold landCarriersInto
  have fresh0 := evaluationPreservesFresh_zero config
  have channels0 := evaluationActivationChannels_zero config
  activation_channels_helper_eval_core fresh0 channels0

theorem preservesActivationChannels_withBreakTarget (act : Goose.Core.ActId) (scope : BreakScope)
    (channels : List Channel) (action : EvalM α) (receive : JumpKind → EvalM α)
    (preserved : PreservesActivationChannels action) (freshAction : PreservesFresh action)
    (received : ∀ kind, PreservesActivationChannels (receive kind)) :
    PreservesActivationChannels (withBreakTarget act scope channels action receive) := by
  intro state fresh
  let target : BreakTarget := ⟨state.nextScope, act, scope, channels⟩
  let installed : ExecutionState := { state with nextScope := state.nextScope + 1, breaks := target :: state.breaks }
  have installedFresh : FreshActivations installed := fresh
  have installedProjection : ActivationChannelsProjection installed = ActivationChannelsProjection state := rfl
  have actionChannels := preserved installed installedFresh
  cases evaluated : action installed with
  | stop reason final => simp [ActivationChannelsOutcome, withBreakTarget, installed, target, evaluated, mapStepState]
  | ok value final =>
      have finalProjection : ActivationChannelsProjection final = ActivationChannelsProjection installed := by
        simpa [ActivationChannelsOutcome, evaluated] using actionChannels
      have finalToState : ActivationChannelsProjection final = ActivationChannelsProjection state :=
        finalProjection.trans installedProjection
      have cleanedToState : ActivationChannelsProjection
          { final with breaks := final.breaks.filter (fun entry => entry.id != state.nextScope) } =
          ActivationChannelsProjection state := finalToState
      simp only [ActivationChannelsOutcome, withBreakTarget, installed, target, evaluated, mapStepState]
      change ActivationChannelsProjection
        { final with breaks := final.breaks.filter (fun entry => entry.id != state.nextScope) } =
        ActivationChannelsProjection state
      exact cleanedToState
  | escape exit values final =>
      have finalProjection : ActivationChannelsProjection final = ActivationChannelsProjection installed := by
        simpa [ActivationChannelsOutcome, evaluated] using actionChannels
      have finalToState : ActivationChannelsProjection final = ActivationChannelsProjection state :=
        finalProjection.trans installedProjection
      have cleanedToState : ActivationChannelsProjection
          { final with breaks := final.breaks.filter (fun entry => entry.id != state.nextScope) } =
          ActivationChannelsProjection state := finalToState
      simp only [ActivationChannelsOutcome, withBreakTarget, installed, target, evaluated, mapStepState]
      change ActivationChannelsProjection
        { final with breaks := final.breaks.filter (fun entry => entry.id != state.nextScope) } =
        ActivationChannelsProjection state
      exact cleanedToState
  | jump actual kind final =>
      have finalProjection : ActivationChannelsProjection final = ActivationChannelsProjection installed := by
        simpa [ActivationChannelsOutcome, evaluated] using actionChannels
      have finalFresh : FreshActivations final := by
        simpa [Goose.Proofs.Exit.stepState, evaluated] using freshAction installed installedFresh
      let removed : ExecutionState := { final with breaks := final.breaks.filter (fun entry => entry.id != state.nextScope) }
      have removedFresh : FreshActivations removed := by
        simpa [removed, FreshActivations] using finalFresh
      have removedToState : ActivationChannelsProjection removed = ActivationChannelsProjection state := by
        calc
          ActivationChannelsProjection removed = ActivationChannelsProjection final := rfl
          _ = ActivationChannelsProjection installed := finalProjection
          _ = ActivationChannelsProjection state := installedProjection
      by_cases caught : actual = state.nextScope
      · subst actual
        have receivedChannels := received kind removed removedFresh
        cases receiveResult : receive kind removed with
        | stop reason after => simp [ActivationChannelsOutcome, withBreakTarget, installed, target, evaluated, mapStepState, removed, receiveResult]
        | ok value after =>
            have afterProjection : ActivationChannelsProjection after = ActivationChannelsProjection removed := by
              simpa [ActivationChannelsOutcome, receiveResult] using receivedChannels
            have afterToState := afterProjection.trans removedToState
            simp only [ActivationChannelsOutcome, withBreakTarget, installed, target, evaluated, mapStepState, removed, receiveResult,
              beq_self_eq_true, ite_true]
            change ActivationChannelsProjection after = ActivationChannelsProjection state
            exact afterToState
        | escape exit values after =>
            have afterProjection : ActivationChannelsProjection after = ActivationChannelsProjection removed := by
              simpa [ActivationChannelsOutcome, receiveResult] using receivedChannels
            have afterToState := afterProjection.trans removedToState
            simp only [ActivationChannelsOutcome, withBreakTarget, installed, target, evaluated, mapStepState, removed, receiveResult,
              beq_self_eq_true, ite_true]
            change ActivationChannelsProjection after = ActivationChannelsProjection state
            exact afterToState
        | jump jumpTarget jumpKind after =>
            have afterProjection : ActivationChannelsProjection after = ActivationChannelsProjection removed := by
              simpa [ActivationChannelsOutcome, receiveResult] using receivedChannels
            have afterToState := afterProjection.trans removedToState
            simp only [ActivationChannelsOutcome, withBreakTarget, installed, target, evaluated, mapStepState, removed, receiveResult,
              beq_self_eq_true, ite_true]
            change ActivationChannelsProjection after = ActivationChannelsProjection state
            exact afterToState
      · have notCaughtBool : (actual == state.nextScope) = false :=
          Bool.eq_false_iff.mpr (fun equal => caught (beq_iff_eq.mp equal))
        have finalToState : ActivationChannelsProjection final = ActivationChannelsProjection state :=
          finalProjection.trans installedProjection
        have cleanedToState : ActivationChannelsProjection removed = ActivationChannelsProjection state :=
          removedToState
        simp only [ActivationChannelsOutcome, withBreakTarget, installed, target, evaluated, mapStepState,
          notCaughtBool, Bool.false_eq_true, ite_false]
        change ActivationChannelsProjection removed = ActivationChannelsProjection state
        exact cleanedToState

theorem preservesActivationChannels_protectDestination (config : EvalConfig)
    (origin : Goose.Core.OriginId) (id : Goose.Core.DestinationId) (action : EvalM α)
    (preserved : PreservesActivationChannels action) (freshAction : PreservesFresh action) :
    PreservesActivationChannels (protectDestination origin id action) := by
  intro state fresh
  have cleanupOutcome (carriers : List Carrier) (final : ExecutionState)
      (finalFresh : FreshActivations final)
      (before : ActivationChannelsProjection final = ActivationChannelsProjection state) :
      ActivationChannelsOutcome (ActivationChannelsProjection state)
        (cleanupReceivingDestination origin id carriers final) := by
    have cleaned := preservesActivationChannels_cleanupReceivingDestination config origin id carriers final finalFresh
    cases result : cleanupReceivingDestination origin id carriers final with
    | stop reason after => exact True.intro
    | ok value after =>
        have afterProjection : ActivationChannelsProjection after = ActivationChannelsProjection final := by
          simpa [ActivationChannelsOutcome, result] using cleaned
        simpa [ActivationChannelsOutcome, result] using afterProjection.trans before
    | escape target values after =>
        have afterProjection : ActivationChannelsProjection after = ActivationChannelsProjection final := by
          simpa [ActivationChannelsOutcome, result] using cleaned
        simpa [ActivationChannelsOutcome, result] using afterProjection.trans before
    | jump target kind after =>
        have afterProjection : ActivationChannelsProjection after = ActivationChannelsProjection final := by
          simpa [ActivationChannelsOutcome, result] using cleaned
        simpa [ActivationChannelsOutcome, result] using afterProjection.trans before
  have actionOutcome := preserved state fresh
  have actionFreshness := freshAction state fresh
  cases result : action state with
  | stop reason final => simp [ActivationChannelsOutcome, protectDestination, result]
  | ok value final =>
      have before : ActivationChannelsProjection final = ActivationChannelsProjection state := by
        simpa [ActivationChannelsOutcome, result] using actionOutcome
      simpa [ActivationChannelsOutcome, protectDestination, result] using before
  | escape target carriers final =>
      have before : ActivationChannelsProjection final = ActivationChannelsProjection state := by
        simpa [ActivationChannelsOutcome, result] using actionOutcome
      have finalFresh : FreshActivations final := by
        simpa [Goose.Proofs.Exit.stepState, result] using actionFreshness
      have cleanup := cleanupOutcome carriers final finalFresh before
      cases cleaned : cleanupReceivingDestination origin id carriers final with
      | stop reason after => simp [ActivationChannelsOutcome, protectDestination, result, cleaned]
      | ok value after =>
          simp [ActivationChannelsOutcome, protectDestination, result, cleaned] at cleanup ⊢
          exact cleanup
      | escape address value after =>
          simp [ActivationChannelsOutcome, protectDestination, result, cleaned] at cleanup ⊢
          exact cleanup
      | jump target kind after =>
          simp [ActivationChannelsOutcome, protectDestination, result, cleaned] at cleanup ⊢
          exact cleanup
  | jump target kind final =>
      have before : ActivationChannelsProjection final = ActivationChannelsProjection state := by
        simpa [ActivationChannelsOutcome, result] using actionOutcome
      have finalFresh : FreshActivations final := by
        simpa [Goose.Proofs.Exit.stepState, result] using actionFreshness
      cases kind with
      | breakValue carriers =>
          have cleanup := cleanupOutcome carriers final finalFresh before
          cases cleaned : cleanupReceivingDestination origin id carriers final with
          | stop reason after => simp [ActivationChannelsOutcome, protectDestination, result, cleaned]
          | ok value after =>
              simp [ActivationChannelsOutcome, protectDestination, result, cleaned] at cleanup ⊢
              exact cleanup
          | escape address value after =>
              simp [ActivationChannelsOutcome, protectDestination, result, cleaned] at cleanup ⊢
              exact cleanup
          | jump target kind after =>
              simp [ActivationChannelsOutcome, protectDestination, result, cleaned] at cleanup ⊢
              exact cleanup
      | continueLoop =>
          have cleanup := cleanupOutcome [] final finalFresh before
          cases cleaned : cleanupReceivingDestination origin id [] final with
          | stop reason after => simp [ActivationChannelsOutcome, protectDestination, result, cleaned]
          | ok value after =>
              simp [ActivationChannelsOutcome, protectDestination, result, cleaned] at cleanup ⊢
              exact cleanup
          | escape address value after =>
              simp [ActivationChannelsOutcome, protectDestination, result, cleaned] at cleanup ⊢
              exact cleanup
          | jump target kind after =>
              simp [ActivationChannelsOutcome, protectDestination, result, cleaned] at cleanup ⊢
              exact cleanup

theorem preservesActivationChannels_finishChannel (config : EvalConfig) (layout : LayoutEnv)
    (origin : Goose.Core.OriginId) (carrier : Carrier) (result : Ty) :
    PreservesActivationChannels (finishChannel layout origin carrier result) := by
  unfold finishChannel
  have fresh0 := evaluationPreservesFresh_zero config
  have channels0 := evaluationActivationChannels_zero config
  activation_channels_eval fresh0 channels0

macro "activation_channels_helper_eval " fresh:ident channels:ident config:ident : tactic => `(tactic|
  activation_channels_helper_eval_core $fresh $channels <;>
  all_goals repeat' first
    | exact preservesActivationChannels_prepareNamedCarrierAt $config _ _ _ _
    | exact preservesActivationChannels_prepareNamedCarrier $config _ _ _
    | exact preservesActivationChannels_landCarriersInto $config _ _ _
    | exact preservesActivationChannels_receivingAction _ _ _
    | exact preservesActivationChannels_finishChannel $config _ _ _ _
    | apply preservesActivationChannels_protectDestination $config
      · activation_channels_helper_eval_core $fresh $channels
      · (solve | activation_channels_fresh $fresh))

theorem preservesActivationChannels_finishChannels (config : EvalConfig) (layout : LayoutEnv)
    (channels : List Channel) (resultTypes : List Ty) (carriers : List Carrier)
    (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (finishChannels layout channels resultTypes carriers origin) := by
  unfold finishChannels
  apply preservesActivationChannels_bind (landCarriersInto origin channels carriers) _
  · exact preservesActivationChannels_landCarriersInto config origin channels carriers
  · exact preservesFresh_landCarriersInto origin channels carriers
  · intro _
    by_cases arity : carriers.length != resultTypes.length
    · simp only [arity]
      exact preservesActivationChannels_fault _
    · simp only [arity]
      apply preservesActivationChannels_bind
      · apply preservesActivationChannels_listForIn
        · intro pair accumulator
          rcases pair with ⟨carrier, result⟩
          apply preservesActivationChannels_bind (finishChannel layout origin carrier result) _
          · exact preservesActivationChannels_finishChannel config layout origin carrier result
          · exact preservesFresh_finishChannel layout origin carrier result
          · intro _; exact preservesActivationChannels_pure _
        · intro pair accumulator
          rcases pair with ⟨carrier, result⟩
          apply preservesFresh_bind (finishChannel layout origin carrier result)
          · exact preservesFresh_finishChannel layout origin carrier result
          · intro _; exact preservesFresh_pure _
      · exact preservesFresh_listForIn _ _ _ (by
          intro pair accumulator
          rcases pair with ⟨carrier, result⟩
          apply preservesFresh_bind (finishChannel layout origin carrier result)
          · exact preservesFresh_finishChannel layout origin carrier result
          · intro _; exact preservesFresh_pure _)
      · intro _; exact preservesActivationChannels_pure _

def NoActivationChannelJump (action : EvalM α) : Prop :=
  ∀ state target kind final, action state ≠ .jump target kind final

theorem noActivationChannelJump_pure (value : α) : NoActivationChannelJump (pure value) := by
  intro state target kind final
  simp [pure]

theorem noActivationChannelJump_stop (reason : Goose.Core.Stop) :
    NoActivationChannelJump (EvalM.stop (α := α) reason) := by
  intro state target kind final
  simp [EvalM.stop]

theorem noActivationChannelJump_fault (kind : Goose.Core.FaultKind) :
    NoActivationChannelJump (fault (α := α) kind) := by
  exact noActivationChannelJump_stop _

theorem noActivationChannelJump_get : NoActivationChannelJump EvalM.get := by
  intro state target kind final
  simp [EvalM.get]

theorem noActivationChannelJump_bind (action : EvalM α) (next : α → EvalM β)
    (head : NoActivationChannelJump action)
    (tail : ∀ value, NoActivationChannelJump (next value)) :
    NoActivationChannelJump (action >>= next) := by
  intro state target kind final
  cases evaluated : action state with
  | ok value middle =>
      simpa [bind, evaluated] using tail value middle target kind final
  | stop reason middle => simp [bind, evaluated]
  | escape address carriers middle => simp [bind, evaluated]
  | jump actual jumpKind middle =>
      have impossible := head state actual jumpKind middle
      exact False.elim (impossible evaluated)

theorem noActivationChannelJump_liftConstruction (origin : Goose.Core.OriginId)
    (action : ConstructionM α) : NoActivationChannelJump (liftConstruction origin action) := by
  intro state target kind final
  unfold liftConstruction
  cases result : action state.construction <;> simp

theorem noActivationChannelJump_listForIn (action : α → β → EvalM (ForInStep β))
    (items : List α) (initial : β)
    (body : ∀ item value, NoActivationChannelJump (action item value)) :
    NoActivationChannelJump (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact noActivationChannelJump_pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply noActivationChannelJump_bind
      · exact body item initial
      · intro step
        cases step with
        | done value => exact noActivationChannelJump_pure _
        | yield value => exact ih value


end Goose.Proofs.ExitExecution
