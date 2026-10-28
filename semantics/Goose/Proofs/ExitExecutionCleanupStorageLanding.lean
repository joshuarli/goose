import Goose.Proofs.ExitExecutionCleanupStoragePrefixes
import Goose.Proofs.ConstructionExecutionProtocolExitFrames
import Lean
import Init.Data.Range.Lemmas

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Core

open Lean Elab Term Meta in
elab "cleanup_source_head " declaration:ident : term => do
  let information ← getConstInfo declaration.getId
  forallTelescope information.type fun _ body => do
    unless body.isAppOf ``Eq do throwError "expected a source operation equation"
    return body.getAppArgs[1]!.getAppFn

private abbrev sourceProtectedAbandonment : List PendingDestination → ConstructionM Unit :=
  cleanup_source_head Goose.Construct.protectedAbandonment_nil_transition

private abbrev sourceLandCompleted : DestinationId → DestinationId → Nat → PendingDestination →
    PendingDestination → Option (DestinationId × PendingDestination) → ConstructionM Unit :=
  cleanup_source_head Goose.Construct.landCompletedReplacement_transition

private abbrev sourceDestinationLookup : DestinationId → ConstructionM PendingDestination :=
  cleanup_source_head Goose.Construct.lookupDestination_result

private abbrev sourceStorageLookup : StorageId → ConstructionM ReceivingStorage :=
  cleanup_source_head Goose.Construct.lookupStorage_result

private abbrev sourceDestinationReplace : DestinationId → PendingDestination → ConstructionM Unit :=
  cleanup_source_head Goose.Construct.replaceDestination_result

private abbrev sourceEventEmit : ConstructionEvent → ConstructionM Unit :=
  cleanup_source_head Goose.Construct.emit_result

private abbrev sourceWritableDestination : DestinationId → ConstructionM PendingDestination :=
  cleanup_source_head Goose.Construct.writableDestination_result

private abbrev sourceStorageReplace : StorageId → ReceivingStorage → ConstructionM Unit :=
  cleanup_source_head Goose.Construct.replaceStorage_result

private theorem sourceProtectedAbandonment_storage (items : List PendingDestination) :
    ∀ state, (sourceProtectedAbandonment items state).finalState.storage = state.storage := by
  induction items with
  | nil => intro state; rw [sourceProtectedAbandonment, protectedAbandonment_nil_transition]; rfl
  | cons destination rest ih =>
      intro state
      rw [sourceProtectedAbandonment, protectedAbandonment_cons_transition]
      split
      · exact ih _
      · rfl

private theorem sourceDestinationLookup_storage (id : DestinationId) :
    ConstructionCleanupStorage (sourceDestinationLookup id) := by
  apply ConstructionCleanupStorage.of_storage_eq
  intro state
  simp only [sourceDestinationLookup, lookupDestination_result]
  cases state.destinations[id]? <;> rfl

private theorem sourceStorageLookup_storage (id : StorageId) :
    ConstructionCleanupStorage (sourceStorageLookup id) := by
  apply ConstructionCleanupStorage.of_storage_eq
  intro state
  simp only [sourceStorageLookup, lookupStorage_result]
  cases state.storage[id]? <;> rfl

private theorem sourceDestinationReplace_storage (id : DestinationId) (destination : PendingDestination) :
    ConstructionCleanupStorage (sourceDestinationReplace id destination) := by
  apply ConstructionCleanupStorage.of_storage_eq
  intro state
  simp only [sourceDestinationReplace, replaceDestination_result]
  split <;> rfl

private theorem sourceEventEmit_storage (event : ConstructionEvent) :
    ConstructionCleanupStorage (sourceEventEmit event) := by
  apply ConstructionCleanupStorage.of_storage_eq
  intro state
  simp only [sourceEventEmit, emit_result]
  rfl

private theorem sourceWritableDestination_storage (id : DestinationId) :
    ConstructionCleanupStorage (sourceWritableDestination id) :=
  .of_storage_eq _ (fun state => congrArg ConstructionState.storage
    (writableDestination_finalState id state))

private theorem sourceStorageLookup_state (id : StorageId) :
    ∀ state, (sourceStorageLookup id state).finalState = state := by
  intro state
  simp only [sourceStorageLookup, lookupStorage_result]
  cases state.storage[id]? <;> rfl

private theorem sourceStorageLookup_present (id : StorageId) (state : ConstructionState)
    (storage : ReceivingStorage) (observed : sourceStorageLookup id state = .ok storage state) :
    state.storage[id]? = some storage := by
  rw [sourceStorageLookup, lookupStorage_result] at observed
  cases found : state.storage[id]? with
  | none => simp only [found] at observed; cases observed
  | some current =>
      simp only [found, ConstructionResult.ok.injEq] at observed
      cases observed.1
      rfl

private theorem splice_preserves_prefix (bytes suffix : ByteArray) (finish : Nat)
    (bounded : finish ≤ bytes.size) :
    (bytes.extract 0 finish ++ suffix).extract 0 finish = bytes.extract 0 finish := by
  apply ByteArray.extract_append_eq_left
  simp only [ByteArray.size_extract, Nat.sub_zero, Nat.min_eq_left bounded]

theorem landReceivingStorage_storage (id : StorageId) (receivingStart payloadStart : Nat) :
    ConstructionCleanupStorage (landReceivingStorage id receivingStart payloadStart) := by
  intro state
  unfold landReceivingStorage
  cases found : state.storage[id]? with
  | none => simp only [found]; exact ⟨[], .refl _⟩
  | some previous =>
      simp only [found]
      by_cases first : receivingStart ≤ payloadStart
      · by_cases second : payloadStart ≤ previous.bytes.size
        · simp only [first, second, decide_true, Bool.true_and, ↓reduceIte, ConstructionResult.finalState]
          exact ⟨[⟨id, receivingStart⟩], .rewrite _ _ _ _ _ found rfl
            (splice_preserves_prefix previous.bytes _ receivingStart (Nat.le_trans first second))⟩
        · simp [first, second, ConstructionResult.finalState]
          exact ⟨[], .refl _⟩
      · simp [first, ConstructionResult.finalState]
        exact ⟨[], .refl _⟩

theorem removeConstructionHeader_storage (id : DestinationId) :
    ConstructionCleanupStorage (removeConstructionHeader id) := by
  intro state
  unfold removeConstructionHeader
  simp only [bind, writableDestination_result]
  cases found : state.destinations[id]? with
  | none => exact ⟨[], .refl _⟩
  | some destination =>
      cases writable : destinationCanWrite state id with
      | false => simp only [writable, Bool.false_eq_true, ↓reduceIte]; exact ⟨[], .refl _⟩
      | true =>
          simp only [writable, ↓reduceIte]
          cases progress : destination.progress <;>
            simp only [progress, ConstructionM.fail, bind, ConstructionResult.finalState]
          case built count =>
            by_cases header : (destination.layout == .packed && destination.capability.request == .value) = true
            · simp only [hasPrefix_result, header, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                lookupStorage_result, bind]
              cases stored : state.storage[destination.storage]? with
              | none => simp only [stored]; exact ⟨[], .refl _⟩
              | some previous =>
                  simp only [stored, bind]
                  by_cases overflow : destination.capability.start + 4 > previous.bytes.size
                  · simp only [overflow, ↓reduceIte]; exact ⟨[], .refl _⟩
                  · simp only [overflow, ↓reduceIte]
                    have prefixBound : destination.capability.start ≤ previous.bytes.size := by omega
                    have prefixFrame := splice_preserves_prefix previous.bytes
                      (previous.bytes.extract (destination.capability.start + 4) previous.bytes.size)
                      destination.capability.start prefixBound
                    simp only [replaceStorage_result, bind]
                    by_cases storageBound : destination.storage < state.storage.size
                    · simp only [storageBound, ↓reduceIte, replaceDestination_result, bind]
                      by_cases destinationBound : id < state.destinations.size
                      · simp only [destinationBound, ↓reduceIte, emit_result, ConstructionResult.finalState]
                        exact ⟨[⟨destination.storage, destination.capability.start⟩],
                          .rewrite _ _ _ _ _ stored rfl prefixFrame⟩
                      · simp only [destinationBound, ↓reduceIte, ConstructionResult.finalState]
                        exact ⟨[⟨destination.storage, destination.capability.start⟩],
                          .rewrite _ _ _ _ _ stored rfl prefixFrame⟩
                    · simp only [storageBound, ↓reduceIte, ConstructionResult.finalState]
                      exact ⟨[], .refl _⟩
            · simp [hasPrefix_result, header, bind, ConstructionM.fail, ConstructionResult.finalState]
              exact ⟨[], .refl _⟩
          all_goals exact ⟨[], .refl _⟩

private theorem sourceLandCompleted_storage (id old : DestinationId) (count : Nat)
    (replacement superseded : PendingDestination)
    (parentUpdate : Option (DestinationId × PendingDestination)) :
    ConstructionCleanupStorage (sourceLandCompleted id old count replacement superseded parentUpdate) := by
  simp only [sourceLandCompleted, landCompletedReplacement_transition]
  repeat' first
    | with_reducible exact ConstructionCleanupStorage.of_storage_eq _ (fun _ => rfl)
    | with_reducible exact sourceDestinationLookup_storage _
    | with_reducible exact sourceStorageLookup_storage _
    | with_reducible exact sourceDestinationReplace_storage _ _
    | with_reducible exact sourceEventEmit_storage _
    | with_reducible exact landReceivingStorage_storage _ _ _
    | with_reducible exact ConstructionCleanupStorage.of_storage_eq _ (sourceProtectedAbandonment_storage _)
    | with_reducible apply ConstructionCleanupStorage.bind
    | split
    | (guard_target = ∀ _, ConstructionCleanupStorage _; intro value)

theorem commitExitReplacement_storage (receiving : Option DestinationId) (id : DestinationId) :
    ConstructionCleanupStorage (commitExitReplacement receiving id) := by
  unfold commitExitReplacement
  repeat' first
    | with_reducible exact ConstructionCleanupStorage.of_storage_eq _ (fun _ => rfl)
    | with_reducible exact sourceDestinationLookup_storage _
    | with_reducible exact sourceLandCompleted_storage _ _ _ _ _ _
    | solve
      | apply ConstructionCleanupStorage.of_storage_eq
        intro current
        rw [Goose.Proofs.ConstructionExecutionProtocol.exitLandingAnchor_finalState]
    | with_reducible apply ConstructionCleanupStorage.bind
    | split
    | (guard_target = ∀ _, ConstructionCleanupStorage _; intro value)

theorem landExitReplacementChain_storage (id : DestinationId) :
    ConstructionCleanupStorage (landExitReplacementChain id) :=
  commitExitReplacement_storage none id

theorem landExitReplacementInto_storage (receiving id : DestinationId) :
    ConstructionCleanupStorage (landExitReplacementInto receiving id) :=
  commitExitReplacement_storage (some receiving) id

open Lean Elab Term in
elab "cleanup_patch_count_source" : term => do
  let information ← getConstInfo ``Goose.Construct.normalizeProducerDestination
  let some value := information.value? | throwError "expected a native construction definition"
  let some operation := value.find? (fun expression =>
    match expression with
    | .const name _ => name.toString.endsWith ".patchCount"
    | _ => false) | throwError "expected the native count patch operation"
  return operation

abbrev sourcePatchCount : ByteArray → Nat → Nat → ByteArray := cleanup_patch_count_source

open Lean Elab Tactic in
elab "unfold_cleanup_patch" : tactic => do
  let information ← getConstInfo ``Goose.Construct.normalizeProducerDestination
  let some value := information.value? | throwError "expected a native construction definition"
  let some operation := value.find? (fun expression =>
    match expression with
    | .const name _ => name.toString.endsWith ".patchCount"
    | _ => false) | throwError "expected the native count patch operation"
  evalTactic (← `(tactic| unfold $(mkIdent operation.constName!)))

private theorem byteSet_preserves_prefix (bytes : ByteArray) (finish index : Nat) (value : UInt8)
    (bounded : finish ≤ bytes.size) (outside : finish ≤ index) :
    (bytes.set! index value).extract 0 finish = bytes.extract 0 finish := by
  suffices same : (bytes.set! index value).extract 0 (0 + finish) = bytes.extract 0 (0 + finish) by
    simpa only [Nat.zero_add] using same
  apply (ByteArray.extract_eq_extract_iff_getElem
    (as := bytes.set! index value) (bs := bytes) (i := 0) (j := 0) (len := finish)
    (by simpa using bounded) (by simpa using bounded)).2
  intro selected inside
  simp only [Nat.zero_add]
  exact ByteArray.getElem_set!_ne bytes index selected value (by omega) (by omega)

private theorem sourcePatchCount_expansion (bytes : ByteArray) (start count : Nat) :
    sourcePatchCount bytes start count =
      (((bytes.set! (start + 0) (UInt8.ofNat (count / 2 ^ (0 * 8) % 256))).set!
        (start + 1) (UInt8.ofNat (count / 2 ^ (1 * 8) % 256))).set!
        (start + 2) (UInt8.ofNat (count / 2 ^ (2 * 8) % 256))).set!
        (start + 3) (UInt8.ofNat (count / 2 ^ (3 * 8) % 256)) := by
  unfold sourcePatchCount
  unfold_cleanup_patch
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rfl

theorem sourcePatchCount_prefix (bytes : ByteArray) (finish start count : Nat)
    (bounded : finish ≤ bytes.size) (outside : finish ≤ start) :
    (sourcePatchCount bytes start count).extract 0 finish = bytes.extract 0 finish := by
  rw [sourcePatchCount_expansion]
  let first := bytes.set! (start + 0) (UInt8.ofNat (count / 2 ^ (0 * 8) % 256))
  let second := first.set! (start + 1) (UInt8.ofNat (count / 2 ^ (1 * 8) % 256))
  let third := second.set! (start + 2) (UInt8.ofNat (count / 2 ^ (2 * 8) % 256))
  calc
    _ = third.extract 0 finish := byteSet_preserves_prefix third finish (start + 3) _
      (by simpa only [third, second, first, ByteArray.size_set!] using bounded) (by omega)
    _ = second.extract 0 finish := byteSet_preserves_prefix second finish (start + 2) _
      (by simpa only [second, first, ByteArray.size_set!] using bounded) (by omega)
    _ = first.extract 0 finish := byteSet_preserves_prefix first finish (start + 1) _
      (by simpa only [first, ByteArray.size_set!] using bounded) (by omega)
    _ = bytes.extract 0 finish := byteSet_preserves_prefix bytes finish (start + 0) _ bounded (by omega)

theorem normalizeProducerDestination_storage (id : DestinationId) (producerType : Goose.Construct.Ty) :
    ConstructionCleanupStorage (normalizeProducerDestination id producerType) := by
  unfold normalizeProducerDestination
  apply ConstructionCleanupStorage.bind
  · exact sourceWritableDestination_storage id
  · intro destination
    cases adaptation : destination.adaptation with
    | none => exact .fail .protocol
    | some receiving =>
      cases progress : destination.progress with
      | built count =>
        apply ConstructionCleanupStorage.ite
        · exact .fail .protocol
        · apply ConstructionCleanupStorage.ite
          · exact .fail .protocol
          · apply ConstructionCleanupStorage.ite
            · apply ConstructionCleanupStorage.ite
              · exact .fail .protocol
              · apply ConstructionCleanupStorage.query_bind
                · exact sourceStorageLookup_state destination.storage
                · intro state storage observed
                  have stored := sourceStorageLookup_present destination.storage state storage observed
                  apply ConstructionCleanupStorage.ite_at
                  · intro overflow
                    exact ⟨[], .refl _⟩
                  · intro overflow
                    apply ConstructionCleanupStorage.bind_at
                    · simp only [sourceStorageReplace, replaceStorage_result]
                      by_cases bounded : destination.storage < state.storage.size
                      · simp only [bounded, ↓reduceIte, ConstructionResult.finalState]
                        refine ⟨[⟨destination.storage, receiving.start⟩],
                          .rewrite _ _ _ _ _ stored rfl ?_⟩
                        apply sourcePatchCount_prefix
                        all_goals omega
                      · simp only [bounded, ↓reduceIte, ConstructionResult.finalState]
                        exact ⟨[], .refl _⟩
                    · intro _
                      apply ConstructionCleanupStorage.bind
                      · exact sourceDestinationLookup_storage id
                      · intro current
                        exact sourceDestinationReplace_storage _ _
            · apply ConstructionCleanupStorage.ite
              · apply ConstructionCleanupStorage.bind (removeConstructionHeader id)
                · exact removeConstructionHeader_storage id
                · intro _
                  apply ConstructionCleanupStorage.bind
                  · exact sourceDestinationLookup_storage id
                  · intro current
                    exact sourceDestinationReplace_storage _ _
              · apply ConstructionCleanupStorage.bind
                · exact sourceDestinationLookup_storage id
                · intro current
                  exact sourceDestinationReplace_storage _ _
      | _ => exact .fail .protocol

theorem adaptDestinationType_storage (id : DestinationId) (ty : Goose.Construct.Ty) :
    ConstructionCleanupStorage (adaptDestinationType id ty) := by
  unfold adaptDestinationType
  apply ConstructionCleanupStorage.bind
  · exact sourceWritableDestination_storage id
  · intro destination
    cases destination.progress <;> first
      | (apply ConstructionCleanupStorage.ite
         · exact .fail .protocol
         · exact sourceDestinationReplace_storage _ _)
      | exact .fail .protocol

theorem restoreReceivingLayout_storage (id : DestinationId) (layout : ReceivingLayout) :
    ConstructionCleanupStorage (restoreReceivingLayout id layout) := by
  unfold restoreReceivingLayout
  apply ConstructionCleanupStorage.bind
  · exact sourceWritableDestination_storage id
  · intro destination
    cases destination.progress with
    | built count =>
      apply ConstructionCleanupStorage.ite
      · exact .fail .protocol
      · exact sourceDestinationReplace_storage _ _
    | _ => exact .fail .protocol

end Goose.Proofs.ExitExecution
