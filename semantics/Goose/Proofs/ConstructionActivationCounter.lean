import Goose.Proofs.ExitExecution

namespace Goose.Proofs.ConstructionActivationCounter
open Goose.Construct Goose.Proofs.ExitExecution

def PreservesActivationCounter (action : EvalM α) : Prop :=
  ∀ state, state.nextAct ≤ (Goose.Proofs.Exit.stepState (action state)).nextAct

theorem counter_pure (value : α) : PreservesActivationCounter (pure value) := by
  intro state
  exact Nat.le_refl _

theorem counter_stop (reason : Goose.Core.Stop) : PreservesActivationCounter (EvalM.stop (α := α) reason) := by
  intro state
  exact Nat.le_refl _

theorem counter_bind (action : EvalM α) (next : α → EvalM β)
    (first : PreservesActivationCounter action) (remaining : ∀ value, PreservesActivationCounter (next value)) :
    PreservesActivationCounter (action >>= next) := by
  intro state
  have prior := first state
  cases result : action state with
  | ok value middle =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    have after := remaining value middle
    simp only [bind, result]
    exact Nat.le_trans prior after
  | stop reason after | escape address carriers after | jump target kind after =>
    simpa only [bind, result, Goose.Proofs.Exit.stepState] using prior

theorem counter_stateQuery (action : EvalM α) (query : StateQuery action) : PreservesActivationCounter action := by
  intro state
  rw [query state]
  exact Nat.le_refl _

theorem counter_freshAct : PreservesActivationCounter freshAct := by
  intro state
  simp [freshAct, EvalM.get, EvalM.set, bind, pure, Goose.Proofs.Exit.stepState]

theorem counter_freshScope : PreservesActivationCounter freshScope := by
  intro state
  simp [freshScope, EvalM.get, EvalM.set, bind, pure, Goose.Proofs.Exit.stepState]

theorem counter_lift (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    PreservesActivationCounter (liftConstruction origin action) := by
  intro state
  cases result : action state.construction <;> simp [liftConstruction, result, Goose.Proofs.Exit.stepState]

theorem counter_get : PreservesActivationCounter EvalM.get := by
  intro state
  exact Nat.le_refl _

theorem counter_setObjectOrdinal (root : Goose.Core.RootInst) (ordinal : Goose.Core.StorageId) :
    PreservesActivationCounter (setObjectOrdinal root ordinal) := by
  intro state
  simp [setObjectOrdinal, EvalM.get, EvalM.set, bind, Goose.Proofs.Exit.stepState]

theorem counter_bindStaticRoot (root : Goose.Core.RootInst) (value : Value) :
    PreservesActivationCounter (bindStaticRoot root value) := by
  intro state
  simp [bindStaticRoot, EvalM.get, EvalM.set, bind, Goose.Proofs.Exit.stepState]

theorem counter_reserveRootObject (root : Goose.Core.RootInst) :
    PreservesActivationCounter (reserveRootObject root) := by
  simp only [reserveRootObject]
  apply counter_bind
  · exact counter_get
  · intro state
    cases lookup : state.objectOrdinals.lookup root with
    | some ordinal => simp only [lookup]; exact counter_pure _
    | none =>
      simp only [lookup]
      apply counter_bind
      · exact counter_lift _ _
      · intro ordinal
        apply counter_bind
        · exact counter_setObjectOrdinal root ordinal
        · intro ignored
          exact counter_pure _

theorem counter_bindRoot (root : Goose.Core.RootInst) (value : Value) :
    PreservesActivationCounter (bindRoot root value) := by
  simp only [bindRoot]
  apply counter_bind
  · exact counter_get
  · intro state
    cases lookup : state.objectOrdinals.lookup root with
    | some ordinal => simp [lookup]; exact counter_bindStaticRoot root value
    | none =>
      simp only [lookup, Option.isNone_none, ↓reduceIte]
      cases value with
      | stored stored =>
        apply counter_bind
        · exact counter_setObjectOrdinal root _
        · intro ignored
          exact counter_bindStaticRoot root _
      | _ =>
        apply counter_bind
        · exact counter_reserveRootObject root
        · intro ignored
          exact counter_bindStaticRoot root _

#print axioms counter_bindRoot
theorem counter_listMapM (action : α → EvalM β) (items : List α)
    (preserved : ∀ item, PreservesActivationCounter (action item)) : PreservesActivationCounter (items.mapM action) := by
  induction items with
  | nil => exact counter_pure _
  | cons item rest ih =>
      rw [List.mapM_cons]
      apply counter_bind
      · exact preserved item
      · intro value
        apply counter_bind
        · exact ih
        · intro values; exact counter_pure _

theorem counter_listForIn (action : α → β → EvalM (ForInStep β)) (items : List α)
    (initial : β) (preserved : ∀ item value, PreservesActivationCounter (action item value)) :
    PreservesActivationCounter (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact counter_pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply counter_bind
      · exact preserved item initial
      · intro step
        cases step with
        | done value => exact counter_pure _
        | yield value => exact ih value

theorem counter_arrayForIn (action : α → β → EvalM (ForInStep β)) (items : Array α)
    (initial : β) (preserved : ∀ item value, PreservesActivationCounter (action item value)) :
    PreservesActivationCounter (forIn items initial action) := by
  rw [← Array.forIn_toList]
  exact counter_listForIn action items.toList initial preserved

theorem counter_rangeForIn (action : Nat → β → EvalM (ForInStep β))
    (range : Std.Legacy.Range) (initial : β)
    (preserved : ∀ index value, PreservesActivationCounter (action index value)) :
    PreservesActivationCounter (forIn range initial action) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact counter_listForIn action _ initial preserved

theorem counter_bindAll (act : Goose.Core.ActId) (scopeInst : Goose.Core.ScopeInst)
    (values : List (Goose.Core.VarId × Value)) : PreservesActivationCounter (bindAll act scopeInst values) := by
  unfold bindAll
  apply counter_bind
  · apply counter_listForIn
    intro item _
    rcases item with ⟨localVar, value⟩
    apply counter_bind
    · exact counter_bindRoot _ value
    · intro ignored; exact counter_pure _
  · intro ignored; exact counter_pure _

theorem counter_get_bind (next : ExecutionState → EvalM α)
    (preserved : ∀ state, state.nextAct ≤ (Goose.Proofs.Exit.stepState (next state state)).nextAct) :
    PreservesActivationCounter (EvalM.get >>= next) := preserved

theorem counter_writeValuePath (fuel : Nat) (layout : LayoutEnv)
    (value : Value) (path : List Nat) (replacement : Value) :
    PreservesActivationCounter (writeValuePath fuel layout value path replacement) := by
  induction fuel generalizing value path replacement with
  | zero => exact counter_stop _
  | succ fuel ih =>
      cases path with
      | nil => exact counter_pure _
      | cons index rest =>
          cases value with
          | fixed elements | record id elements =>
              simp only [writeValuePath]
              cases present : elements[index]? with
              | none => exact counter_stop _
              | some child =>
                  apply counter_bind
                  · exact ih child rest replacement
                  · intro written; exact counter_pure _
          | int _ _ | bool _ | unit | ref _ | slice _ _ _ => exact counter_stop _
          | stored stored =>
              unfold writeValuePath
              apply counter_bind
              · exact counter_stateQuery _ (stateQuery_storedPathRun stored)
              · intro sampled
                rcases sampled with ⟨bytes, run⟩
                simp only
                apply counter_bind
                · exact counter_stateQuery _ (stateQuery_liftLayout _)
                · intro interval
                  rcases interval with ⟨start, finish⟩
                  simp only
                  apply counter_bind
                  · exact counter_stateQuery _ (stateQuery_readStoredElement fuel layout stored index)
                  · intro child
                    split
                    · split
                      · exact counter_stop _
                      · apply counter_bind
                        · exact ih child rest replacement
                        · intro _; exact counter_pure _
                    · apply counter_bind
                      · exact ih child rest replacement
                      · intro written
                        apply counter_bind
                        · exact counter_stateQuery _ (stateQuery_liftExcept _)
                        · intro part
                          split
                          · exact counter_stop _
                          · apply counter_get_bind
                            intro state
                            cases present : state.construction.storage[stored.storage]? <;>
                              simp [present, EvalM.set, bind, pure, fault, EvalM.stop, Goose.Proofs.Exit.stepState]

theorem counter_writeLoc (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (replacement : Value) : PreservesActivationCounter (writeLoc fuel layout location replacement) := by
  unfold writeLoc
  apply counter_bind
  · exact counter_get
  · intro state
    cases present : state.objects.lookup location.root with
    | none => exact counter_stop _
    | some value =>
        apply counter_bind
        · exact counter_writeValuePath fuel layout value location.path replacement
        · intro written; exact counter_bindRoot location.root written

theorem counter_mapActivations (change : RuntimeActivation → RuntimeActivation) (action : EvalM α)
    (preserved : PreservesActivationCounter action) :
    PreservesActivationCounter (do
      let state ← EvalM.get
      EvalM.set { state with activations := state.activations.map change }
      action) := by
  intro state
  simpa [EvalM.get, EvalM.set, bind, pure] using preserved { state with activations := state.activations.map change }

theorem counter_withScope (environment : RuntimeActivation) (scope scopeInst : Nat) (action : EvalM α)
    (preserved : PreservesActivationCounter action) : PreservesActivationCounter (withScope environment scope scopeInst action) := by
  intro state
  have after := preserved state
  cases result : action state with
  | ok value final =>
    simpa [withScope, result, releaseScope, releaseScopeState, EvalM.get, EvalM.set, bind,
      Goose.Proofs.Exit.stepState] using after
  | stop reason final => simpa [withScope, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
    simpa [withScope, result, releaseScope, releaseScopeState, EvalM.get, EvalM.set, bind,
      Goose.Proofs.Exit.stepState] using after
  | jump target kind final =>
    simpa [withScope, result, releaseScope, releaseScopeState, EvalM.get, EvalM.set, bind,
      Goose.Proofs.Exit.stepState] using after

#print axioms counter_withScope
theorem counter_fault (reason : Goose.Core.FaultKind) : PreservesActivationCounter (fault (α := α) reason) :=
  counter_stop _

theorem counter_abortAt (reason : Goose.Core.AbortKind) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (abortAt (α := α) reason origin) := counter_stop _

theorem counter_fixedWrites (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (element : Ty) (origin : Goose.Core.OriginId) (values : Array Value) :
    PreservesActivationCounter (forIn values PUnit.unit fun value _ => do
      let bytes ← liftExcept (fixedBytes fuel layout element value)
      liftConstruction origin (writeElement destination bytes)
      pure (.yield PUnit.unit)) := by
  apply counter_arrayForIn
  intro value _
  apply counter_bind
  · exact counter_stateQuery _ (stateQuery_liftExcept _)
  · intro bytes
    apply counter_bind
    · exact counter_lift _ _
    · intro _; exact counter_pure _

theorem counter_packedWrites (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (bytes : ByteArray) (run : SampledRun) (start count : Nat) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (forIn ([0:count] : Std.Legacy.Range) PUnit.unit fun index _ => do
      let (low, high) ← liftLayout (elementInterval fuel layout bytes run (start + index))
      liftConstruction origin (writeElement destination (bytes.extract low high))
      pure (.yield PUnit.unit)) := by
  apply counter_rangeForIn
  intro index _
  apply counter_bind
  · exact counter_stateQuery _ (stateQuery_liftLayout _)
  · intro interval
    rcases interval with ⟨low, high⟩
    simp only
    apply counter_bind
    · exact counter_lift _ _
    · intro _; exact counter_pure _

theorem counter_copyValue (fuel : Nat) (layout : LayoutEnv) (destination : Goose.Core.DestinationId)
    (value : Value) (origin : Goose.Core.OriginId) (source : Option Goose.Core.CopySource) :
    PreservesActivationCounter (copyValue fuel layout destination value origin source) := by
  cases fuel with
  | zero => exact counter_stop _
  | succ fuel =>
      unfold copyValue
      apply counter_bind
      · exact counter_lift _ _
      · intro current
        apply counter_bind
        · exact counter_stateQuery _ (stateQuery_getDestination current)
        · intro pending
          cases elementFound : elementType pending.capability.logicalType with
          | none => exact counter_stop _
          | some element =>
              cases value with
              | int _ _ | bool _ | unit | record _ _ | ref _ => exact counter_stop _
              | stored stored =>
                  apply counter_bind
                  · exact counter_stateQuery _ (stateQuery_sampledStored stored)
                  · intro sampled
                    rcases sampled with ⟨bytes, run⟩
                    simp only
                    split
                    · exact counter_stop _
                    · apply counter_bind
                      · exact counter_lift _ _
                      · intro _
                        apply counter_bind
                        · simpa only [Nat.zero_add] using counter_packedWrites fuel layout current bytes run 0 run.count origin
                        · intro _; exact counter_lift _ _
              | fixed values =>
                  cases source with
                  | none =>
                      apply counter_bind
                      · exact counter_fixedWrites fuel layout current element origin values
                      · intro _; exact counter_lift _ _
                  | some source =>
                      apply counter_bind
                      · exact counter_lift _ _
                      · intro _
                        apply counter_bind
                        · exact counter_fixedWrites fuel layout current element origin values
                        · intro _; exact counter_lift _ _
              | slice location start count =>
                  apply counter_bind
                  · exact counter_stateQuery _ (stateQuery_readLoc fuel layout location)
                  · intro backing
                    cases source with
                    | none => exact counter_stop _
                    | some source =>
                        cases backing with
                        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ => exact counter_stop _
                        | stored stored =>
                            apply counter_bind
                            · exact counter_stateQuery _ (stateQuery_storedPathRun stored)
                            · intro sampled
                              rcases sampled with ⟨bytes, run⟩
                              simp only
                              split
                              · exact counter_stop _
                              · split
                                · exact counter_stop _
                                · apply counter_bind
                                  · exact counter_lift _ _
                                  · intro _
                                    apply counter_bind
                                    · exact counter_packedWrites fuel layout current bytes run start count origin
                                    · intro _; exact counter_lift _ _
                        | fixed values =>
                            simp only
                            split
                            · exact counter_stop _
                            · apply counter_bind
                              · exact counter_lift _ _
                              · intro _
                                apply counter_bind
                                · exact counter_fixedWrites fuel layout current element origin (values.extract start (start + count))
                                · intro _; exact counter_lift _ _

theorem counter_newDestination (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (ty : Ty) (request : Goose.Core.ConstructionRequest) (origin : Goose.Core.OriginId)
    (storage : Option Goose.Core.StorageId) (knownCount : Option Nat) :
    PreservesActivationCounter (newDestination layout owner ty request origin storage knownCount) := by
  unfold newDestination
  cases storage with
  | none =>
      apply counter_bind
      · exact counter_lift _ _
      · intro storage
        apply counter_bind
        · exact counter_stateQuery _ (stateQuery_receivingLayout layout ty)
        · intro receiving; exact counter_lift _ _
  | some storage =>
      apply counter_bind
      · exact counter_pure _
      · intro storage
        apply counter_bind
        · exact counter_stateQuery _ (stateQuery_receivingLayout layout ty)
        · intro receiving; exact counter_lift _ _

theorem counter_channelsFor (layout : LayoutEnv) (owner : Goose.Core.ActId)
    (results : List ResultDescriptor) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (channelsFor layout owner results origin) := by
  unfold channelsFor
  apply counter_listMapM
  intro descriptor
  cases descriptor.request with
  | register => exact counter_pure _
  | value | elementRun =>
      apply counter_bind
      · exact counter_newDestination _ _ _ _ _ _ _
      · intro destination; exact counter_pure _

theorem counter_completedReceivingDestination (id : Goose.Core.DestinationId) :
    PreservesActivationCounter (completedReceivingDestination id) := by
  unfold completedReceivingDestination
  apply counter_bind
  · exact counter_lift _ _
  · intro current
    exact counter_stateQuery _ (stateQuery_completedDestination current)

theorem counter_publishCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    PreservesActivationCounter (publishCarriers origin carriers) := by
  unfold publishCarriers
  apply counter_bind
  · apply counter_stateQuery
    apply stateQuery_listMapM
    intro carrier
    cases carrier with
    | register value => exact stateQuery_pure _
    | completed id => exact stateQuery_pure _
    | pendingNamed token => exact stateQuery_stop _
  · intro ids
    exact counter_lift _ _

theorem counter_deliverCarriers (fuel : Nat) (layout : LayoutEnv) (channels : List Channel)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (deliverCarriers fuel layout channels carriers origin) := by
  unfold deliverCarriers
  split
  · exact counter_stop _
  · apply counter_listMapM
    intro item
    rcases item with ⟨channel, carrier⟩
    cases channel <;> cases carrier <;> first
      | exact counter_pure _
      | exact counter_stop _
      | (apply counter_bind
         · exact counter_copyValue _ _ _ _ _ _
         · intro _
           apply counter_bind
           · exact counter_completedReceivingDestination _
           · intro _; exact counter_pure _)

theorem counter_receivingAction (origin : Goose.Core.OriginId)
    (incoming : Goose.Core.DestinationId) (action : Goose.Core.DestinationId → ConstructionM α) :
    PreservesActivationCounter (receivingAction origin incoming action) := by
  unfold receivingAction
  exact counter_lift _ _

theorem counter_repeatElement (fuel : Nat) (layout : LayoutEnv) (parent : Goose.Core.DestinationId)
    (element : Ty) (source : Goose.Core.DestinationId) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (repeatElement fuel layout parent element source origin) := by
  cases fuel with
  | zero => exact counter_stop _
  | succ fuel =>
      unfold repeatElement
      apply counter_bind
      · exact counter_lift _ _
      · intro current
        apply counter_bind
        · exact counter_stateQuery _ (stateQuery_storedDestination source)
        · intro stored
          apply counter_bind
          · exact counter_stateQuery _ (stateQuery_getStorage stored.storage)
          · intro storage
            apply counter_bind
            · exact counter_stateQuery _ (stateQuery_liftLayout _)
            · intro finish
              apply counter_bind
              · exact counter_lift _ _
              · intro _; exact counter_lift _ _

theorem counter_receivingDestination (id : Goose.Core.DestinationId) :
    PreservesActivationCounter (receivingDestination id) := by
  exact counter_lift _ _

private def completionLanding (origin : Goose.Core.OriginId) (token : ExitReservationId)
    (replacement : Goose.Core.DestinationId) : EvalM (ForInStep PUnit) := do
  let some (.active _ _ selected _) := (← EvalM.get).construction.exitReservations[token]? | fault .flow
  let receiving ← receivingDestination selected
  if receiving != replacement then
    liftConstruction origin (landExitReplacementInto receiving replacement)
  pure (.yield PUnit.unit)

private theorem counter_completionLanding (origin : Goose.Core.OriginId)
    (token : ExitReservationId) (replacement : Goose.Core.DestinationId) :
    PreservesActivationCounter (completionLanding origin token replacement) := by
  unfold completionLanding
  apply counter_bind
  · exact counter_get
  · intro state
    cases found : state.construction.exitReservations[token]? with
    | none => exact counter_fault .flow
    | some reservation =>
        cases reservation with
        | waiting incoming => exact counter_fault .flow
        | active role incoming selected snapshot =>
            apply counter_bind
            · exact counter_receivingDestination selected
            · intro receiving
              cases changed : (receiving != replacement) with
              | false => simp; exact counter_pure _
              | true =>
                  simp
                  apply counter_bind
                  · exact counter_lift _ _
                  · intro _; exact counter_pure _
        | restored | released => exact counter_fault .flow

theorem counter_landCarriersInto (origin : Goose.Core.OriginId) (channels : List Channel)
    (carriers : List Carrier) : PreservesActivationCounter (landCarriersInto origin channels carriers) := by
  unfold landCarriersInto
  split
  · exact counter_stop _
  · simp only [bind]
    apply counter_bind
    · apply counter_listForIn
      intro item _
      cases item with
      | mk channel carrier =>
          simp only
          cases channel with
          | register ty =>
              cases carrier with
              | register value => exact counter_pure _
              | completed id | pendingNamed _ => exact counter_stop _
          | construct incoming =>
              cases carrier with
              | register value | pendingNamed _ => exact counter_stop _
              | completed replacement =>
                  simp only
                  apply counter_bind
                  · exact counter_receivingDestination incoming
                  · intro current
                    cases changed : (current != replacement) with
                    | false =>
                        simp
                        exact counter_pure _
                    | true =>
                        simp
                        apply counter_bind
                        · exact counter_lift _ _
                        · intro _; exact counter_pure _
          | completion token =>
              cases carrier with
              | register value => exact counter_stop _
              | pendingNamed pending =>
                  cases mismatch : (token != pending) with
                  | false => simp [mismatch]; exact counter_pure _
                  | true => simp [mismatch]; exact counter_stop _
              | completed replacement =>
                  change PreservesActivationCounter (completionLanding origin token replacement)
                  exact counter_completionLanding origin token replacement
    · intro _; exact counter_pure _

theorem counter_finishChannel (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (carrier : Carrier) (result : Ty) : PreservesActivationCounter (finishChannel layout origin carrier result) := by
  unfold finishChannel
  cases carrier with
  | register value => exact counter_pure _
  | pendingNamed token => exact counter_stop _
  | completed id =>
      apply counter_bind
      · exact counter_stateQuery _ (stateQuery_getDestination id)
      · intro destination
        simp only
        split
        · exact counter_lift _ _
        · split <;> split
          all_goals
            first
              | exact counter_lift _ _
              | (apply counter_bind
                 · exact counter_lift _ _
                 · intro _
                   apply counter_bind
                   · exact counter_stateQuery _ (stateQuery_receivingLayout layout destination.capability.layout)
                   · intro receiving
                     apply counter_bind
                     · exact counter_lift _ _
                     · intro _; exact counter_lift _ _)

theorem counter_finishChannels (layout : LayoutEnv) (channels : List Channel) (types : List Ty)
    (carriers : List Carrier) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (finishChannels layout channels types carriers origin) := by
  unfold finishChannels
  apply counter_bind
  · exact counter_landCarriersInto origin channels carriers
  · intro _
    split
    · exact counter_stop _
    · apply counter_bind
      · apply counter_listForIn
        intro item _
        rcases item with ⟨carrier, result⟩
        apply counter_bind
        · exact counter_finishChannel layout origin carrier result
        · intro _; exact counter_pure _
      · intro _; exact counter_pure _

theorem counter_finishActivation (layout : LayoutEnv) (activation : RuntimeActivation) (types : List Ty)
    (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (preserved : PreservesActivationCounter action) :
    PreservesActivationCounter (finishActivation layout activation types origin action) := by
  intro state
  have prior := preserved state
  cases result : action state with
  | ok carriers final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    let trimmed : ExecutionState := { final with activations := final.activations.filter (fun current => current.act != activation.act) }
    have after := counter_finishChannels layout activation.channels types carriers origin trimmed
    cases finished : finishChannels layout activation.channels types carriers origin trimmed <;>
      simp only [finished, Goose.Proofs.Exit.stepState] at after <;>
      simpa [finishActivation, result, trimmed, finished, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
  | stop reason final => simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using prior
  | jump target kind final => simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using prior
  | escape target carriers final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    by_cases caught : target.activation = activation.act
    · let trimmed : ExecutionState := { final with activations := final.activations.filter (fun current => current.act != activation.act) }
      have after := counter_finishChannels layout activation.channels types carriers origin trimmed
      cases finished : finishChannels layout activation.channels types carriers origin trimmed <;>
        simp only [finished, Goose.Proofs.Exit.stepState] at after <;>
        simpa [finishActivation, result, caught, trimmed, finished, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
    · simpa [finishActivation, result, caught, Goose.Proofs.Exit.stepState] using prior

#print axioms counter_finishActivation
theorem counter_cleanupDestination (origin : Goose.Core.OriginId)
    (id : Goose.Core.DestinationId) (carriers : List Carrier) :
    PreservesActivationCounter (cleanupDestination origin id carriers) := by
  unfold cleanupDestination
  apply counter_bind
  · exact counter_stateQuery _ (stateQuery_getDestination id)
  · intro destination
    split
    · exact counter_pure _
    · apply counter_bind
      · exact counter_get
      · intro state
        split
        · exact counter_lift _ _
        · split
          · exact counter_pure _
          · exact counter_lift _ _

theorem counter_cleanupReceivingDestination (origin : Goose.Core.OriginId)
    (incoming : Goose.Core.DestinationId) (carriers : List Carrier) :
    PreservesActivationCounter (cleanupReceivingDestination origin incoming carriers) := by
  unfold cleanupReceivingDestination
  apply counter_bind
  · exact counter_lift _ _
  · intro current
    exact counter_cleanupDestination origin current carriers

#print axioms counter_cleanupReceivingDestination
theorem counter_protectDestination (origin : Goose.Core.OriginId) (destination : Goose.Core.DestinationId)
    (action : EvalM α) (preserved : PreservesActivationCounter action) :
    PreservesActivationCounter (protectDestination origin destination action) := by
  intro state
  have prior := preserved state
  cases result : action state with
  | ok value final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using prior
  | stop reason final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using prior
  | escape target carriers final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    have after := counter_cleanupReceivingDestination origin destination carriers final
    cases cleaned : cleanupReceivingDestination origin destination carriers final <;>
      simp only [cleaned, Goose.Proofs.Exit.stepState] at after <;>
      simpa [protectDestination, result, cleaned, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
  | jump target kind final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    cases kind with
    | breakValue carriers =>
      have after := counter_cleanupReceivingDestination origin destination carriers final
      cases cleaned : cleanupReceivingDestination origin destination carriers final <;>
        simp only [cleaned, Goose.Proofs.Exit.stepState] at after <;>
        simpa [protectDestination, result, cleaned, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
    | continueLoop =>
      have after := counter_cleanupReceivingDestination origin destination [] final
      cases cleaned : cleanupReceivingDestination origin destination [] final <;>
        simp only [cleaned, Goose.Proofs.Exit.stepState] at after <;>
        simpa [protectDestination, result, cleaned, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after

#print axioms counter_protectDestination
theorem counter_materializeProducer (fuel : Nat) (declarations : DeclarationEnv)
    (expression : Expr) (evaluate : EvalM Value) (preserved : PreservesActivationCounter evaluate) :
    PreservesActivationCounter (materializeProducer fuel declarations expression evaluate) := by
  unfold materializeProducer
  split
  · exact counter_pure _
  · apply counter_bind
    · exact preserved
    · intro value
      cases value <;> first | exact counter_pure _ | exact counter_stop _

theorem counter_materializedDestination (fuel : Nat) (layout : LayoutEnv)
    (owner : Goose.Core.ActId) (ty : Ty) (origin : Goose.Core.OriginId)
    (count : Nat) (value : Value) :
    PreservesActivationCounter (materializedDestination fuel layout owner ty origin count value) := by
  unfold materializedDestination
  apply counter_bind
  · exact counter_newDestination _ _ _ _ _ _ _
  · intro destination
    apply counter_bind
    · exact counter_copyValue _ _ _ _ _ _
    · intro ignored
      exact counter_completedReceivingDestination _

theorem counter_constructLocal (declarations : DeclarationEnv) (owner : Goose.Core.ActId) (ty : Ty)
    (origin : Goose.Core.OriginId) (expression : Expr) (construct : Goose.Core.DestinationId → EvalM Unit)
    (preserved : ∀ destination, PreservesActivationCounter (construct destination)) :
    PreservesActivationCounter (constructLocal declarations owner ty origin expression construct) := by
  unfold constructLocal
  apply counter_bind
  · exact counter_newDestination _ _ _ _ _ _ _
  · intro destination
    apply counter_bind
    · exact preserved destination
    · intro _
      apply counter_bind
      · exact counter_completedReceivingDestination destination
      · intro completed
        apply counter_bind
        · exact counter_publishCarriers _ _
        · intro _; exact counter_pure _

theorem counter_execResultScope (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (block : Block)
    (statementsAction : RuntimeActivation → List Stmt → EvalM Flow)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier))
    (statementsPreserved : ∀ runtime statements, PreservesActivationCounter (statementsAction runtime statements))
    (tailPreserved : ∀ runtime expression, PreservesActivationCounter (tailAction runtime expression)) :
    PreservesActivationCounter (execResultScope environment pre channels block statementsAction tailAction) := by
  cases block with
  | mk scope statements value =>
    unfold execResultScope
    apply counter_bind
    · exact counter_freshScope
    · intro scopeInst
      apply counter_mapActivations
      apply counter_withScope
      apply counter_bind
      · exact counter_bindAll _ _ _
      · intro ignored
        apply counter_bind
        · exact statementsPreserved _ _
        · intro flow
          cases flow with
          | normal result =>
            cases value with
            | some expression =>
              dsimp only
              apply counter_bind
              · exact tailPreserved _ _
              · intro ignored; exact counter_pure _
            | none =>
              dsimp only
              split
              · exact counter_pure _
              · split
                · exact counter_pure _
                · exact counter_stop _
          | breaking result | continuing => dsimp only; exact counter_pure _

#print axioms counter_execResultScope
theorem counter_materializeOwnedCarriers (origin : Goose.Core.OriginId)
    (tokens : List ExitReservationId) (carriers : List Carrier) :
    PreservesActivationCounter (materializeOwnedCarriers origin tokens carriers) := by
  unfold materializeOwnedCarriers
  apply counter_listMapM
  intro carrier
  cases carrier with
  | register value => exact counter_pure _
  | completed id => exact counter_pure _
  | pendingNamed token =>
      by_cases owns : tokens.contains token = true
      · simp only [owns]
        apply counter_bind
        · exact counter_lift _ _
        · intro id; exact counter_pure _
      · simp only [owns]
        exact counter_pure _

private theorem counter_cleanupResult (cleanup : EvalM Unit) (resume : ExecutionState → ExecutionStep α)
    (frame : ∀ state, Goose.Proofs.Exit.stepState (resume state) = state)
    (preserved : PreservesActivationCounter cleanup) (state : ExecutionState) :
    state.nextAct ≤ (Goose.Proofs.Exit.stepState (match cleanup state with
      | .ok () after => resume after
      | .stop reason after => .stop reason after
      | .escape target carriers after => .escape target carriers after
      | .jump target kind after => .jump target kind after)).nextAct := by
  have checked := preserved state
  cases evaluated : cleanup state with
  | ok ignored final =>
    cases ignored
    simp only [evaluated, Goose.Proofs.Exit.stepState] at checked
    change state.nextAct ≤ (Goose.Proofs.Exit.stepState (resume final)).nextAct
    rw [frame]
    exact checked
  | stop reason final | escape target carriers final | jump target kind final =>
    simpa only [evaluated, Goose.Proofs.Exit.stepState] using checked

theorem counter_withCompletionChannels (channels : List Channel)
    (origin : Goose.Core.OriginId) (action : List Channel → EvalM (List Carrier))
    (preserved : ∀ planned, PreservesActivationCounter (action planned)) :
    PreservesActivationCounter (withCompletionChannels channels origin action) := by
  let setup : EvalM (List Channel × List ExitReservationId) := do
    let planned ← channels.mapM fun channel => match channel with
      | .construct incoming => do
          let token ← liftConstruction origin (waitExitDestination incoming)
          pure (Channel.completion token, some token)
      | .register ty => pure (Channel.register ty, none)
      | .completion _ => fault .flow
    pure (planned.map Prod.fst, planned.filterMap Prod.snd)
  have setupPreserved : PreservesActivationCounter setup := by
    apply counter_bind
    · apply counter_listMapM
      intro channel
      cases channel <;> repeat' first
        | exact counter_pure _
        | exact counter_stop _
        | exact counter_lift _ _
        | apply counter_bind
        | intro
    · intro ignored
      exact counter_pure _
  intro state
  change state.nextAct ≤ (Goose.Proofs.Exit.stepState (match setup state with
    | .ok (planned, tokens) prepared => _
    | .stop reason after => .stop reason after
    | .escape target carriers after => .escape target carriers after
    | .jump target kind after => .jump target kind after)).nextAct
  have preparedCounter := setupPreserved state
  cases prepared : setup state with
  | stop reason after | escape target carriers after | jump target kind after =>
    simpa only [prepared, Goose.Proofs.Exit.stepState] using preparedCounter
  | ok pair after =>
    rcases pair with ⟨planned, tokens⟩
    simp only [prepared, Goose.Proofs.Exit.stepState] at preparedCounter
    let evaluatedAction := do materializeOwnedCarriers origin tokens (← action planned)
    have actionPreserved : PreservesActivationCounter evaluatedAction := by
      apply counter_bind
      · exact preserved planned
      · exact counter_materializeOwnedCarriers origin tokens
    have evaluatedCounter := actionPreserved after
    cases evaluated : evaluatedAction after
    all_goals simp only [evaluated, Goose.Proofs.Exit.stepState] at evaluatedCounter
    all_goals have evaluatedResult := evaluated
    all_goals dsimp only [evaluatedAction] at evaluatedResult
    all_goals simp only [evaluatedResult]
    all_goals
      apply Nat.le_trans (Nat.le_trans preparedCounter evaluatedCounter)
      apply counter_cleanupResult
      · exact fun _ => rfl
      · simp only [Bool.false_eq_true, ↓reduceIte]
        apply counter_bind
        · apply counter_listForIn
          intro token accumulator
          repeat' first
            | exact counter_pure _
            | exact counter_lift _ _
            | apply counter_bind
            | intro
        · intro ignored
          exact counter_pure _

#print axioms counter_withCompletionChannels
theorem counter_allocateActivation (make : Goose.Core.ActId → RuntimeActivation)
    (action : RuntimeActivation → EvalM α) (preserved : ∀ activation, PreservesActivationCounter (action activation)) :
    PreservesActivationCounter (do
      let act ← freshAct
      let activation := make act
      let state ← EvalM.get
      EvalM.set { state with activations := activation :: state.activations }
      action activation) := by
  intro state
  have after := preserved (make state.nextAct)
    { state with nextAct := state.nextAct + 1, activations := make state.nextAct :: state.activations }
  simp only [freshAct, EvalM.get, EvalM.set, bind, pure, Goose.Proofs.Exit.stepState]
  exact Nat.le_trans (Nat.le_succ _) after

theorem counter_withBreakTarget (act : Goose.Core.ActId) (scope : BreakScope) (channels : List Channel)
    (action : EvalM α) (receive : JumpKind → EvalM α)
    (preserved : PreservesActivationCounter action) (received : ∀ kind, PreservesActivationCounter (receive kind)) :
    PreservesActivationCounter (withBreakTarget act scope channels action receive) := by
  intro state
  let id := state.nextScope
  let pushed := { state with nextScope := id + 1, breaks := (⟨id, act, scope, channels⟩ : BreakTarget) :: state.breaks }
  have prior := preserved pushed
  cases result : action pushed with
  | ok value final => simpa [withBreakTarget, pushed, id, result, mapStepState, Goose.Proofs.Exit.stepState] using prior
  | stop reason final => simpa [withBreakTarget, pushed, id, result, mapStepState, Goose.Proofs.Exit.stepState] using prior
  | escape address carriers final => simpa [withBreakTarget, pushed, id, result, mapStepState, Goose.Proofs.Exit.stepState] using prior
  | jump target kind final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    by_cases caught : target = id
    · let cleaned := { final with breaks := final.breaks.filter (fun entry => entry.id != id) }
      have after := received kind cleaned
      simpa [withBreakTarget, pushed, id, result, caught, mapStepState, cleaned, Goose.Proofs.Exit.stepState] using
        Nat.le_trans prior after
    · simpa [withBreakTarget, pushed, id, result, caught, mapStepState, Goose.Proofs.Exit.stepState] using prior

#print axioms counter_withBreakTarget
theorem counter_truncateOwner (fuel : Nat) (layout : LayoutEnv) (location : Goose.Core.Loc)
    (count : Nat) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (truncateOwner fuel layout location count origin) := by
  cases fuel with
  | zero => exact counter_stop _
  | succ fuel =>
      unfold truncateOwner
      apply counter_bind
      · exact counter_stateQuery _ (stateQuery_readLoc fuel layout location)
      · intro value
        cases value with
        | int _ _ | bool _ | unit | record _ _ | ref _ | slice _ _ _ | fixed _ => exact counter_stop _
        | stored stored =>
            apply counter_bind
            · exact counter_stateQuery _ (stateQuery_sampledStored stored)
            · intro sampled
              rcases sampled with ⟨bytes, run⟩
              simp only
              split
              · exact counter_stop _
              · apply counter_bind
                · exact counter_stateQuery _ (stateQuery_liftLayout _)
                · intro finish
                  cases stored.destination with
                  | none =>
                      apply counter_bind
                      · exact counter_pure _
                      · intro owner
                        apply counter_bind
                        · exact counter_lift _ _
                        · intro _; exact counter_writeLoc _ _ _ _
                  | some id =>
                      apply counter_bind
                      · exact counter_stateQuery _ (stateQuery_getDestination id)
                      · intro pending
                        apply counter_bind
                        · exact counter_pure _
                        · intro owner
                          apply counter_bind
                          · exact counter_lift _ _
                          · intro _; exact counter_writeLoc _ _ _ _

structure EvaluationPreservesActivationCounter (fuel : Nat) (config : EvalConfig) : Prop where
  value : ∀ environment expression, PreservesActivationCounter (evalValue fuel config environment expression)
  bound : ∀ environment count defaultValue operand, PreservesActivationCounter (evalBound fuel config environment count defaultValue operand)
  place : ∀ environment operand, PreservesActivationCounter (evalPlace fuel config environment operand)
  view : ∀ environment operand, PreservesActivationCounter (evalView fuel config environment operand)
  produce : ∀ environment channels operand, PreservesActivationCounter (evalProduce fuel config environment channels operand)
  operands : ∀ environment channels expressions, PreservesActivationCounter (evalOperands fuel config environment channels expressions)
  build : ∀ environment destination expression, PreservesActivationCounter (buildExpr fuel config environment destination expression)
  element : ∀ environment destination element expression, PreservesActivationCounter (buildElement fuel config environment destination element expression)
  arguments : ∀ environment vars params args, PreservesActivationCounter (evalArguments fuel config environment vars params args)
  call : ∀ environment context args channels origin, PreservesActivationCounter (invokeCall fuel config environment context args channels origin)
  activation : ∀ environment pre body origin, PreservesActivationCounter (enterActivation fuel config environment pre body origin)
  activationBody : ∀ environment pre body, PreservesActivationCounter (execActivationBody fuel config environment pre body)
  resultBlock : ∀ environment channels body, PreservesActivationCounter (execResultBlock fuel config environment channels body)
  resultBlockWith : ∀ environment pre channels body, PreservesActivationCounter (execResultBlockWith fuel config environment pre channels body)
  block : ∀ environment pre channels body, PreservesActivationCounter (execBlock fuel config environment pre channels body)
  statements : ∀ environment statements, PreservesActivationCounter (execStmts fuel config environment statements)
  statement : ∀ environment statement, PreservesActivationCounter (execStmt fuel config environment statement)
  printArgument : ∀ environment argument, PreservesActivationCounter (evalPrintArg fuel config environment argument)
  whileLoop : ∀ environment condition body, PreservesActivationCounter (execWhile fuel config environment condition body)
  rangeLoop : ∀ environment var ty first last body, PreservesActivationCounter (execRange fuel config environment var ty first last body)
  eachLoop : ∀ environment var index byRef body view current, PreservesActivationCounter (execEach fuel config environment var index byRef body view current)
  loop : ∀ environment pre body, PreservesActivationCounter (loopBody fuel config environment pre body)
  push : ∀ environment owner expression origin, PreservesActivationCounter (pushValue fuel config environment owner expression origin)


theorem evaluationCounter_zero (config : EvalConfig) : EvaluationPreservesActivationCounter 0 config := by
  constructor <;> intros <;>
    simp only [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands, buildExpr, buildElement,
      evalArguments, invokeCall, enterActivation, execActivationBody, execResultBlock, execResultBlockWith,
      execBlock, execStmts, execStmt, evalPrintArg, execWhile, execRange, execEach, loopBody, pushValue,
      timeout, counter_stop]

theorem evalBound_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (count : Nat) (defaultValue : Int) (operand : Bound) :
    PreservesActivationCounter (evalBound (fuel + 1) config environment count defaultValue operand) := by
  cases operand with
  | omitted => simpa only [evalBound] using counter_pure defaultValue
  | expr expression | fromEnd expression =>
      simp only [evalBound]
      apply counter_bind
      · exact previous.value _ _
      · intro value
        apply counter_bind
        · exact counter_stateQuery _ (stateQuery_expectInt value)
        · intro pair; exact counter_pure _

theorem evalPlace_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (operand : Place) :
    PreservesActivationCounter (evalPlace (fuel + 1) config environment operand) := by
  cases operand with
  | var localVar =>
      simp only [evalPlace]
      apply counter_bind
      · exact counter_stateQuery _ (stateQuery_rootOf _ _)
      · intro _; exact counter_pure _
  | global global => simpa only [evalPlace] using counter_pure (Goose.Core.Loc.mk (.global global) [])
  | deref expression =>
      simp only [evalPlace]
      apply counter_bind
      · exact previous.value _ _
      · intro value; exact counter_stateQuery _ (stateQuery_expectRef value)
  | elem view expression origin =>
      simp only [evalPlace]
      apply counter_bind
      · exact previous.view _ _
      · intro view
        apply counter_bind
        · exact previous.value _ _
        · intro value
          apply counter_bind
          · exact counter_stateQuery _ (stateQuery_expectInt value)
          · intro pair
            rcases pair with ⟨ty, index⟩
            split
            · exact counter_pure _
            · exact counter_stop _
  | field place index =>
      simp only [evalPlace]
      apply counter_bind
      · exact previous.place _ _
      · intro _; exact counter_pure _

theorem evalView_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (operand : View) :
    PreservesActivationCounter (evalView (fuel + 1) config environment operand) := by
  cases operand with
  | of place =>
      simp only [evalView]
      apply counter_bind
      · exact previous.place _ _
      · intro location
        apply counter_bind
        · exact counter_stateQuery _ (stateQuery_readLoc _ _ _)
        · intro value
          apply counter_bind
          · exact counter_stateQuery _ (stateQuery_arrayLength value)
          · intro pair
            rcases pair with ⟨count, dynamic⟩
            exact counter_pure _
  | val expression =>
      simp only [evalView]
      apply counter_bind
      · exact previous.value _ _
      · intro value
        cases value <;> first
          | exact counter_pure _
          | (apply counter_bind
             · exact counter_stateQuery _ (stateQuery_arrayLength _)
             · intro pair
               rcases pair with ⟨count, dynamic⟩
               apply counter_bind
               · exact counter_freshScope
               · intro index
                 apply counter_bind
                 · exact counter_bindRoot _ _
                 · intro _; exact counter_pure _)

theorem evalOperands_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr) :
    PreservesActivationCounter (evalOperands (fuel + 1) config environment channels operands) := by
  cases channels <;> cases operands <;> simp only [evalOperands]
  all_goals first
    | exact counter_pure _
    | exact counter_stop _
    | (apply counter_bind
       · exact previous.produce _ _ _
       · intro carriers
         apply counter_bind
         · exact counter_stateQuery _ (stateQuery_singleCarrier carriers)
         · intro carrier
           apply counter_bind
           · exact previous.operands _ _ _
           · intro _; exact counter_pure _)

theorem evalPrintArg_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (argument : PrintArg) :
    PreservesActivationCounter (evalPrintArg (fuel + 1) config environment argument) := by
  cases argument with
  | text text => simpa only [evalPrintArg] using counter_pure text.toUTF8
  | expr expression =>
      simp only [evalPrintArg]
      apply counter_bind
      · exact previous.value _ _
      · intro value; exact counter_stateQuery _ ((rendering_stateQueries fuel config.layout).1 _ _)
  | view view =>
      simp only [evalPrintArg]
      apply counter_bind
      · exact previous.view _ _
      · intro view; exact counter_stateQuery _ ((rendering_stateQueries fuel config.layout).2.2.2 _ _)

theorem evalArguments_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameters : List Param) (arguments : List Arg) :
    PreservesActivationCounter (evalArguments (fuel + 1) config environment vars parameters arguments) := by
  cases parameters with
  | nil =>
      cases arguments <;> simp only [evalArguments]
      · exact counter_pure _
      · exact counter_stop _
  | cons parameter parameters =>
      cases arguments with
      | nil => simpa only [evalArguments, fault] using counter_stop (Goose.Core.Stop.fault .arity)
      | cons argument arguments =>
          have finish (value : Value) : PreservesActivationCounter (do
              let values ← evalArguments fuel config environment vars parameters arguments
              pure (value :: values)) := by
            apply counter_bind
            · exact previous.arguments _ _ _ _
            · intro _; exact counter_pure _
          cases argument with
          | byVal expression =>
              simp only [evalArguments]
              apply counter_bind
              · exact previous.value _ _
              · intro value; exact finish value
          | byRef mutability place =>
              simp only [evalArguments]
              apply counter_bind
              · exact previous.place _ _
              · intro location
                apply counter_bind
                · exact counter_pure _
                · intro value; exact finish value
          | construct expression =>
              simp only [evalArguments]
              split
              · apply counter_bind
                · apply counter_materializeProducer
                  exact previous.value _ _
                · intro materialized
                  have finishCarrier (carrier : Carrier) : PreservesActivationCounter (do
                      let value ← carrierValue carrier
                      let values ← evalArguments fuel config environment vars parameters arguments
                      pure (value :: values)) := by
                    apply counter_bind
                    · exact counter_stateQuery _ (stateQuery_carrierValue carrier)
                    · intro value; exact finish value
                  cases materialized with
                  | none =>
                      apply counter_bind
                      · apply counter_constructLocal
                        intro destination; exact previous.build _ _ _
                      · exact finishCarrier
                  | some source =>
                      apply counter_bind
                      · exact counter_materializedDestination _ _ _ _ _ _ _
                      · intro destination
                        apply counter_bind
                        · exact counter_publishCarriers _ _
                        · intro ignored
                          apply counter_bind
                          · exact counter_pure _
                          · exact finishCarrier
              · apply counter_bind
                · exact counter_stop _
                · intro value; exact finish value

theorem execStmts_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (statements : List Stmt) : PreservesActivationCounter (execStmts (fuel + 1) config environment statements) := by
  cases statements with
  | nil => simpa only [execStmts] using counter_pure (Flow.normal .unit)
  | cons statement statements =>
      simp only [execStmts]
      apply counter_bind
      · exact previous.statement _ _
      · intro flow
        cases flow with
        | normal value => exact previous.statements _ _
        | breaking value | continuing => exact counter_pure _

theorem execResultBlock_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (body : Block) :
    PreservesActivationCounter (execResultBlock (fuel + 1) config environment channels body) := by
  simpa only [execResultBlock] using previous.resultBlockWith environment [] channels body

theorem enterActivation_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (enterActivation (fuel + 1) config environment pre body origin) := by
  simp only [enterActivation]
  split
  · apply counter_finishActivation
    exact previous.activationBody _ _ _
  · exact counter_stop _

theorem execBlock_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    PreservesActivationCounter (execBlock (fuel + 1) config environment pre channels body) := by
  cases body with
  | mk scope statements value =>
    simp only [execBlock]
    apply counter_bind
    · exact counter_freshScope
    · intro scopeInst
      apply counter_withScope
      apply counter_bind
      · exact counter_bindAll _ _ _
      · intro ignored
        apply counter_bind
        · exact previous.statements _ _
        · intro flow
          cases flow with
          | normal result =>
            cases value with
            | none => exact counter_pure _
            | some expression =>
              dsimp only
              split
              · apply counter_bind
                · exact previous.value _ _
                · intro value; exact counter_pure _
              · apply counter_bind
                · exact previous.produce _ _ _
                · intro carriers
                  apply counter_bind
                  · exact counter_stateQuery _ (stateQuery_singleCarrier carriers)
                  · intro carrier
                    apply counter_bind
                    · exact counter_stateQuery _ (stateQuery_carrierValue carrier)
                    · intro value; exact counter_pure _
          | breaking result | continuing => exact counter_pure _

theorem execResultBlockWith_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    PreservesActivationCounter (execResultBlockWith (fuel + 1) config environment pre channels body) := by
  simp only [execResultBlockWith]
  apply counter_execResultScope
  · exact previous.statements
  · exact fun environment expression => previous.produce environment channels expression

#print axioms execBlock_counter_succ
#print axioms execResultBlockWith_counter_succ
theorem execActivationBody_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    PreservesActivationCounter (execActivationBody (fuel + 1) config environment pre body) := by
  simp only [execActivationBody]
  apply counter_bind
  · apply counter_execResultScope
    · exact previous.statements
    · intro runtime expression
      apply counter_withCompletionChannels
      intro channels
      exact previous.produce runtime channels expression
  · intro result
    rcases result with ⟨flow, carriers⟩
    cases flow with
    | normal value => exact counter_pure _
    | breaking value | continuing => exact counter_fault _

#print axioms execActivationBody_counter_succ
theorem invokeCall_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (invokeCall (fuel + 1) config environment context arguments channels origin) := by
  simp only [invokeCall]
  apply counter_bind
  · exact counter_stateQuery _ (stateQuery_getImplementation config context)
  · intro implementation
    rcases implementation with ⟨id, implementation⟩
    split
    · exact counter_stop _
    · apply counter_bind
      · apply counter_listMapM
        intro item
        rcases item with ⟨channel, result⟩
        cases channel <;> cases result.request <;> repeat' first
          | exact counter_pure _
          | exact counter_stop _
          | exact counter_lift _ _
          | apply counter_bind
          | intro
      · intro callableChannels
        apply counter_bind
        · exact previous.arguments _ _ _ _
        · intro values
          apply counter_bind
          · apply counter_listMapM
            intro channel
            cases channel <;> repeat' first
              | exact counter_pure _
              | exact counter_stop _
              | exact counter_lift _ _
              | apply counter_bind
              | intro
          · intro renewed
            apply counter_bind
            · exact counter_get
            · intro state
              split
              · exact counter_stop _
              · apply counter_allocateActivation
                  (make := fun act => ⟨id, act, implementation.vars, [], renewed⟩)
                  (action := fun activation => do
                    let carriers ← enterActivation fuel config activation
                      ((implementation.params.toList.zip values).map fun item => (item.1.var, item.2))
                      implementation.body origin
                    deliverCarriers fuel config.layout channels carriers origin)
                intro activation
                apply counter_bind
                · exact previous.activation _ _ _ _
                · intro carriers
                  exact counter_deliverCarriers _ _ _ _ _

#print axioms invokeCall_counter_succ
local macro "counter_channel" : tactic => `(tactic|
  repeat' first
    | exact counter_pure _
    | exact counter_stop _
    | exact counter_get
    | exact counter_lift _ _
    | exact counter_stateQuery _ (stateQuery_receivingDestination _)
    | exact counter_stateQuery _ (stateQuery_getDestination _)
    | exact counter_stateQuery _ (stateQuery_exitSource _ _ _)
    | apply counter_bind
    | dsimp only
    | split
    | intro)

theorem counter_selectCompletionChannel (source : RuntimeActivation) (operand : Expr)
    (channel : Channel) : PreservesActivationCounter (selectCompletionChannel source operand channel) := by
  cases channel <;> simp only [selectCompletionChannel]
  all_goals counter_channel

theorem counter_prepareNamedCarrier (origin : Goose.Core.OriginId)
    (incoming : Goose.Core.DestinationId) (stored : StoredValue) :
    PreservesActivationCounter (prepareNamedCarrier origin incoming stored) := by
  unfold prepareNamedCarrier
  counter_channel

theorem counter_prepareNamedCarrierAt (origin : Goose.Core.OriginId)
    (token : ExitReservationId) (incoming : Goose.Core.DestinationId) (stored : StoredValue) :
    PreservesActivationCounter (prepareNamedCarrierAt origin token incoming stored) := by
  unfold prepareNamedCarrierAt
  counter_channel

theorem counter_conditional (condition : Prop) [Decidable condition]
    (yes no : EvalM α) (left : PreservesActivationCounter yes) (right : PreservesActivationCounter no) :
    PreservesActivationCounter (if condition then yes else no) := by
  split <;> assumption

elab "counter_conditional_step" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``PreservesActivationCounter do throwError "expected counter action"
  let args := target.getAppArgs
  let some action := args[args.size - 1]? | throwError "expected action"
  unless action.getAppFn.isConstOf ``ite do throwError "expected conditional"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply counter_conditional))

syntax "counter_eval_simple" ident : tactic
macro_rules
  | `(tactic| counter_eval_simple $previous:ident) => `(tactic|
    repeat' first
      | with_reducible assumption
      | counter_conditional_step
      | with_reducible exact counter_pure _
      | with_reducible exact counter_stop _
      | with_reducible exact counter_lift _ _
      | with_reducible exact counter_fault _
      | with_reducible exact counter_abortAt _ _
      | with_reducible exact counter_freshScope
      | with_reducible exact counter_bindRoot _ _
      | with_reducible exact counter_bindStaticRoot _ _
      | with_reducible exact counter_publishCarriers _ _
      | with_reducible exact counter_channelsFor _ _ _ _
      | with_reducible exact counter_copyValue _ _ _ _ _ _
      | with_reducible exact counter_receivingDestination _
      | with_reducible exact counter_repeatElement _ _ _ _ _ _
      | with_reducible exact counter_newDestination _ _ _ _ _ _ _
      | with_reducible exact counter_get
      | with_reducible exact counter_selectCompletionChannel _ _ _
      | with_reducible exact counter_prepareNamedCarrier _ _ _
      | with_reducible exact counter_prepareNamedCarrierAt _ _ _ _
      | with_reducible exact counter_landCarriersInto _ _ _
      | with_reducible exact counter_truncateOwner _ _ _ _ _
      | with_reducible exact counter_stateQuery _ (stateQuery_getImplementation _ _)
      | with_reducible exact counter_stateQuery _ (stateQuery_sampledStored _)
      | with_reducible exact counter_stateQuery _ (stateQuery_readStoredElement _ _ _ _)
      | with_reducible exact counter_stateQuery _ (stateQuery_expectInt _)
      | with_reducible exact counter_stateQuery _ (stateQuery_enclosingActivation _)
      | with_reducible exact counter_stateQuery _ (stateQuery_targetActivation _ _)
      | with_reducible exact counter_stateQuery _ (stateQuery_currentBreak _ _)
      | with_reducible exact counter_stateQuery _ (stateQuery_expectRef _)
      | with_reducible exact counter_stateQuery _ (stateQuery_sameIntType _ _)
      | with_reducible exact counter_stateQuery _ (stateQuery_comparable _ _)
      | with_reducible exact counter_stateQuery _ (stateQuery_rootOf _ _)
      | with_reducible exact counter_stateQuery _ (stateQuery_singleCarrier _)
      | with_reducible exact counter_stateQuery _ (stateQuery_carrierValue _)
      | with_reducible exact counter_stateQuery _ (stateQuery_getStorage _)
      | with_reducible exact counter_stateQuery _ (stateQuery_getDestination _)
      | with_reducible exact counter_stateQuery _ (stateQuery_storedDestination _)
      | with_reducible exact counter_receivingAction _ _ _
      | with_reducible exact counter_completedReceivingDestination _
      | with_reducible exact counter_stateQuery _ (stateQuery_receivingLayout _ _)
      | with_reducible exact counter_stateQuery _ (stateQuery_liftExcept _)
      | with_reducible exact counter_stateQuery _ (stateQuery_expectBool _)
      | with_reducible exact counter_stateQuery _ (stateQuery_readLoc _ _ _)
      | with_reducible exact counter_stateQuery _ (stateQuery_arrayLength _)
      | with_reducible exact ($previous).value _ _
      | with_reducible exact ($previous).bound _ _ _ _
      | with_reducible exact ($previous).place _ _
      | with_reducible exact ($previous).view _ _
      | with_reducible exact ($previous).produce _ _ _
      | with_reducible exact ($previous).operands _ _ _
      | with_reducible exact ($previous).element _ _ _ _
      | with_reducible exact ($previous).printArgument _ _
      | with_reducible exact ($previous).resultBlock _ _ _
      | with_reducible exact ($previous).resultBlockWith _ _ _ _
      | with_reducible exact ($previous).call _ _ _ _ _
      | with_reducible exact ($previous).block _ _ _ _
      | with_reducible exact ($previous).push _ _ _ _
      | with_reducible exact ($previous).build _ _ _
      | with_reducible exact ($previous).loop _ _ _
      | with_reducible exact ($previous).whileLoop _ _ _
      | with_reducible exact ($previous).rangeLoop _ _ _ _ _ _
      | with_reducible exact ($previous).eachLoop _ _ _ _ _ _ _
      | with_reducible apply counter_withBreakTarget
      | with_reducible apply counter_protectDestination
      | with_reducible apply counter_withCompletionChannels
      | with_reducible apply counter_constructLocal
      | with_reducible apply counter_listForIn
      | with_reducible apply counter_arrayForIn
      | with_reducible apply counter_rangeForIn
      | with_reducible apply counter_listMapM
      | with_reducible apply counter_bind
      | with_reducible split
      | with_reducible rfl
      | with_reducible intro)

theorem buildElement_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (element : Ty) (expression : Expr) :
    PreservesActivationCounter (buildElement (fuel + 1) config environment destination element expression) := by
  simp only [buildElement]
  counter_eval_simple previous

#print axioms buildElement_counter_succ
set_option maxHeartbeats 2000000 in
theorem evalValue_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (expression : Expr) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment expression) := by
  cases expression
  all_goals try simp only [evalValue]
  all_goals counter_eval_simple previous
  case fill ty expression origin =>
    cases ty <;> simp only [evalValue] <;> counter_eval_simple previous
  case structLit ty operands =>
    cases ty <;> simp only [evalValue] <;> counter_eval_simple previous
  case bytes ty bytes origin =>
    cases ty <;> try simp only [evalValue]
    all_goals counter_eval_simple previous
    case slice mutability element =>
      cases element <;> try simp only [evalValue]
      all_goals counter_eval_simple previous
      case int ty =>
        cases ty <;> simp only [evalValue] <;> counter_eval_simple previous
  case values operands =>
    cases operands with
    | nil => simpa only [evalValue] using counter_pure Value.unit
    | cons expression operands =>
      cases operands <;> simp only [evalValue] <;> counter_eval_simple previous

#print axioms evalValue_counter_succ
set_option maxHeartbeats 2000000 in
theorem evalProduce_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (expression : Expr) :
    PreservesActivationCounter (evalProduce (fuel + 1) config environment channels expression) := by
  cases expression <;> simp only [evalProduce]
  all_goals counter_eval_simple previous

#print axioms evalProduce_counter_succ
set_option maxHeartbeats 2000000 in
theorem buildExpr_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (expression : Expr) :
    PreservesActivationCounter (buildExpr (fuel + 1) config environment destination expression) := by
  cases expression <;> try simp only [buildExpr]
  all_goals counter_eval_simple previous

#print axioms buildExpr_counter_succ
theorem execWhile_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (condition : Expr) (body : Block) :
    PreservesActivationCounter (execWhile (fuel + 1) config environment condition body) := by
  simp only [execWhile]
  apply counter_bind
  · exact previous.value _ _
  · intro value
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_expectBool value)
    · intro selected
      cases selected with
      | false => exact counter_pure _
      | true =>
        apply counter_bind
        · exact previous.loop _ _ _
        · intro flow
          cases flow with
          | normal value | continuing => exact previous.whileLoop _ _ _
          | breaking value => exact counter_pure _

theorem execRange_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (ty : Goose.Core.IntTy) (first last : Int) (body : Block) :
    PreservesActivationCounter (execRange (fuel + 1) config environment var ty first last body) := by
  simp only [execRange]
  split
  · apply counter_bind
    · exact previous.loop _ _ _
    · intro flow
      cases flow with
      | normal value | continuing => exact previous.rangeLoop _ _ _ _ _ _
      | breaking value => exact counter_pure _
  · exact counter_pure _

theorem execEach_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block)
    (view : RuntimeView) (current : Nat) :
    PreservesActivationCounter (execEach (fuel + 1) config environment var index byRef body view current) := by
  simp only [execEach]
  counter_eval_simple previous

theorem loopBody_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    PreservesActivationCounter (loopBody (fuel + 1) config environment pre body) := by
  simp only [loopBody]
  apply counter_withBreakTarget
  · exact previous.block _ _ _ _
  · intro kind
    cases kind with
    | continueLoop => exact counter_pure _
    | breakValue carriers =>
      cases carriers with
      | nil => exact counter_pure _
      | cons first rest =>
        apply counter_bind
        · exact counter_stateQuery _ (stateQuery_singleCarrier _)
        · intro carrier
          apply counter_bind
          · exact counter_stateQuery _ (stateQuery_carrierValue carrier)
          · intro value; exact counter_pure _

#print axioms execEach_counter_succ
#print axioms loopBody_counter_succ
theorem evalValue_not_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (expression : Expr) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.not expression)) :=
  evalValue_counter_succ fuel config previous environment (.not expression)

theorem evalValue_cmp_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.CmpOp) (first second : Expr) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.cmp operation first second)) :=
  evalValue_counter_succ fuel config previous environment (.cmp operation first second)

#print axioms evalValue_not_counter
#print axioms evalValue_cmp_counter
theorem evalValue_un_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.UnOp) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.un operation expression origin)) :=
  evalValue_counter_succ fuel config previous environment (.un operation expression origin)

theorem evalValue_bin_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.BinOp) (first second : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.bin operation first second origin)) :=
  evalValue_counter_succ fuel config previous environment (.bin operation first second origin)

theorem evalValue_conv_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (kind : Goose.Core.ConvKind) (target : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.conv kind target expression origin)) :=
  evalValue_counter_succ fuel config previous environment (.conv kind target expression origin)

#print axioms evalValue_conv_counter
theorem evalValue_and_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (first second : Expr) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.and first second)) :=
  evalValue_counter_succ fuel config previous environment (.and first second)

theorem evalValue_or_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (first second : Expr) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.or first second)) :=
  evalValue_counter_succ fuel config previous environment (.or first second)

#print axioms evalValue_bin_counter
#print axioms evalValue_and_counter
theorem freshActs_distinct_across (action : EvalM α) (preserved : PreservesActivationCounter action)
    (before afterFirst afterAction afterSecond : ExecutionState) (first second : Goose.Core.ActId) (value : α)
    (firstStep : freshAct before = .ok first afterFirst)
    (actionStep : action afterFirst = .ok value afterAction)
    (secondStep : freshAct afterAction = .ok second afterSecond) : first < second := by
  have firstExact : freshAct before = .ok before.nextAct { before with nextAct := before.nextAct + 1 } := by rfl
  have secondExact : freshAct afterAction = .ok afterAction.nextAct { afterAction with nextAct := afterAction.nextAct + 1 } := by rfl
  have firstId : first = before.nextAct := (ExecutionStep.ok.inj (firstStep.symm.trans firstExact)).1
  have firstState : afterFirst = { before with nextAct := before.nextAct + 1 } :=
    (ExecutionStep.ok.inj (firstStep.symm.trans firstExact)).2
  have secondId : second = afterAction.nextAct := (ExecutionStep.ok.inj (secondStep.symm.trans secondExact)).1
  have monotone := preserved afterFirst
  simp only [actionStep, Goose.Proofs.Exit.stepState] at monotone
  rw [firstId, secondId]
  rw [firstState] at monotone
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) monotone

private def allocationWitness : EvalM (Goose.Core.ActId × Goose.Core.ActId) := do
  let first ← freshAct
  emitStdout ⟨#[65]⟩
  let second ← freshAct
  pure (first, second)

private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem allocationWitness_execution :
    ∃ state, allocationWitness .initial = .ok (0, 1) state ∧
      state.construction.stdout.data.toList = [65] := by
  refine ⟨witnessState (allocationWitness .initial), ?_, ?_⟩ <;>
    unfold allocationWitness witnessState <;> cbv

#print axioms allocationWitness_execution
#print axioms freshActs_distinct_across
#print axioms evaluationCounter_zero
#print axioms counter_bind
#print axioms counter_freshAct
#print axioms counter_lift
end Goose.Proofs.ConstructionActivationCounter
