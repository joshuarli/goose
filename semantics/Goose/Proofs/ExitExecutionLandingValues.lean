import Goose.Proofs.ExitExecutionValuePrefixReads
import Goose.Proofs.ExitExecutionLandingPayload

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation

inductive RelocatedReadValue (source receiving : Nat) : Value → Value → Prop
  | fixed (value : Value) (data : ∀ stored, ¬StoredOccurrence value stored) :
      RelocatedReadValue source receiving value value
  | stored (value : StoredValue) (offset : Nat) (start : value.start = source + offset) :
      RelocatedReadValue source receiving (.stored value) (.stored { value with start := receiving + offset })

theorem sampledStored_start_transport (stored : StoredValue) (receiving : Nat)
    (before after : ExecutionState) (original current : ReceivingStorage) (run : SampledRun)
    (originalStorage : before.construction.storage[stored.storage]? = some original)
    (currentStorage : after.construction.storage[stored.storage]? = some current)
    (count : current.publishedCount = original.publishedCount)
    (destination : ∀ id, stored.destination = some id →
      after.construction.destinations[id]? = before.construction.destinations[id]?)
    (sampled : sampledStored stored before = .ok (original.bytes, run) before) :
    stored.start ≤ run.byteStart ∧
      sampledStored { stored with start := receiving } after =
        .ok (current.bytes, { run with byteStart := receiving + (run.byteStart - stored.start) }) after := by
  cases selected : stored.destination with
  | none =>
    cases element : elementType stored.ty <;>
      simp only [sampledStored, getStorage, EvalM.get, bind, pure, originalStorage,
        currentStorage, selected, element, fault, EvalM.stop] at sampled ⊢
    · cases sampled
    · cases sampled
      simp only [Nat.add_sub_cancel_left]
      exact ⟨by omega, True.intro⟩
  | some id =>
    have same := destination id selected
    cases found : before.construction.destinations[id]? with
    | none =>
      simp only [sampledStored, getStorage, getDestination, EvalM.get, bind, pure,
        originalStorage, selected, found, fault, EvalM.stop] at sampled
      cases sampled
    | some pending =>
      cases progress : pending.progress <;> cases element : elementType stored.ty <;>
        simp only [sampledStored, getStorage, getDestination, EvalM.get, bind, pure,
          originalStorage, currentStorage, selected, same, found, progress, element,
          progressCount, fault, EvalM.stop, count] at sampled ⊢ <;>
        first | (solve | cases sampled) | (cases sampled; simp only [Nat.add_sub_cancel_left]; exact ⟨by omega, True.intro⟩)

theorem readStoredElement_relocated_success (fuel backingFuel : Nat) (module : Module)
    (accepted : validate module = .ok ()) (before after : ExecutionState)
    (stored : StoredValue) (landedStart source receiving count runStart length index finish : Nat)
    (element : Ty) (original current : ByteArray) (value : Value)
    (originalRun : storedPathRun stored before = .ok (original, ⟨source + runStart, length, element⟩) before)
    (currentRun : storedPathRun { stored with start := landedStart } after =
      .ok (current, ⟨receiving + runStart, length, element⟩) after)
    (backing : elementsEnd backingFuel (.ofModule module) element length original (source + runStart) = .ok (source + finish))
    (inside : finish ≤ count) (equal : RelocatedBytes original current source receiving count)
    (observed : readStoredElement fuel (.ofModule module) stored index before = .ok value before) :
    ∃ relocated, readStoredElement fuel (.ofModule module) { stored with start := landedStart } index after =
      .ok relocated after ∧ RelocatedReadValue source receiving value relocated := by
  simp only [readStoredElement, originalRun, currentRun, bind] at observed ⊢
  cases interval : elementInterval fuel (.ofModule module) original ⟨source + runStart, length, element⟩ index with
  | error reason =>
    cases reason <;> simp only [interval, liftLayout, fault, timeout, EvalM.stop] at observed <;> cases observed
  | ok pair =>
    obtain ⟨first, last⟩ := pair
    obtain ⟨indexBound, prefixRead, elementRead⟩ := elementInterval_result_inv fuel (.ofModule module)
      original ⟨source + runStart, length, element⟩ index first last interval
    have firstLower := elementsEnd_monotone fuel (.ofModule module) element index original (source + runStart) first prefixRead
    have lastBound := elementInterval_within_run fuel backingFuel (.ofModule module) original
      ⟨source + runStart, length, element⟩ index first last (source + finish) interval backing
    have lastLower := packedEnd_monotone fuel (.ofModule module) element original first last elementRead
    let startOffset := first - source
    let endOffset := last - source
    have firstEq : first = source + startOffset := by dsimp only [startOffset]; omega
    have lastEq : last = source + endOffset := by dsimp only [endOffset]; omega
    rw [firstEq, lastEq] at interval elementRead
    have translated := equal.elementInterval fuel (.ofModule module) element length runStart index
      startOffset endOffset interval (by dsimp only [endOffset]; omega)
    simp only [interval, translated, liftLayout, pure] at observed ⊢
    cases nonfixed : element.nonfixed with
    | false =>
      simp only [nonfixed, Bool.false_eq_true, ↓reduceIte] at observed ⊢
      cases decoded : fixedValue fuel (.ofModule module) element original (source + startOffset) with
      | error reason => simp only [decoded, Goose.Construct.liftExcept, EvalM.stop] at observed; cases observed
      | ok data =>
        obtain ⟨width, size, widthEnd⟩ := fixedValue_backed_width fuel fuel (.ofModule module) element
          original (source + startOffset) (source + endOffset) data nonfixed elementRead decoded
        have decodedEqual := equal.fixedValue fuel (.ofModule module) (validated_fixedLayoutFieldBounds module accepted)
          element width startOffset size (by dsimp only [startOffset, endOffset] at *; omega)
        simp only [decodedEqual, decoded, Goose.Construct.liftExcept, pure] at observed ⊢
        cases observed
        refine ⟨value, rfl, .fixed value ?_⟩
        exact fixedValue_no_storedOccurrence fuel (.ofModule module) element original (source + startOffset) value decoded
    | true =>
      simp only [nonfixed, ↓reduceIte] at observed ⊢
      cases sampled : samplePacked element original (source + startOffset) with
      | error reason =>
        cases reason <;> simp only [sampled, fault, timeout, EvalM.stop] at observed <;> cases observed
      | ok run =>
        have runLower := samplePacked_start_bound element original (source + startOffset) run sampled
        let runOffset := run.byteStart - source
        have runEq : run.byteStart = source + runOffset := by dsimp only [runOffset]; omega
        have normalizedSample : samplePacked element original (source + startOffset) =
            .ok ⟨source + runOffset, run.count, run.element⟩ := by
          rw [← runEq]
          exact sampled
        have sampledEqual := equal.samplePacked fuel (.ofModule module) element startOffset endOffset
          runOffset run.count run.element elementRead (by dsimp only [endOffset]; omega) normalizedSample
        simp only [sampled, sampledEqual] at observed ⊢
        cases observed
        refine ⟨.stored ⟨stored.storage, receiving + startOffset, element, run.count, none,
          some (stored.object.getD stored.storage), stored.path ++ [index], run.count⟩, rfl, ?_⟩
        exact .stored _ startOffset rfl

theorem landReceivingStorage_stored_read (fuel backingFuel : Nat) (module : Module)
    (accepted : validate module = .ok ()) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (stored : StoredValue) (storage : ReceivingStorage)
    (receiving finish index : Nat) (run : SampledRun) (value : Value)
    (present : before.construction.storage[stored.storage]? = some storage)
    (sampled : sampledStored stored before = .ok (storage.bytes, run) before)
    (backing : elementsEnd backingFuel (.ofModule module) run.element
      (storedWrittenRun stored run).count storage.bytes run.byteStart = .ok finish)
    (ordered : receiving ≤ stored.start) (inside : finish ≤ storage.bytes.size)
    (observed : readStoredElement fuel (.ofModule module) stored index before = .ok value before) :
    ∃ after relocated,
      liftConstruction origin (landReceivingStorage stored.storage receiving stored.start) before = .ok () after ∧
      readStoredElement fuel (.ofModule module) { stored with start := receiving } index after = .ok relocated after ∧
      RelocatedReadValue stored.start receiving value relocated := by
  have sourceLower := (sampledStored_start_transport stored receiving before before storage storage run
    present present rfl (fun _ _ => rfl) sampled).1
  have runLower := elementsEnd_monotone backingFuel (.ofModule module) run.element
    (storedWrittenRun stored run).count storage.bytes run.byteStart finish backing
  have sourceInside : stored.start ≤ storage.bytes.size := by omega
  let current := storage.landExit receiving stored.start
  let after : ExecutionState := { before with construction :=
    { before.construction with storage := before.construction.storage.set! stored.storage current } }
  have currentFound : after.construction.storage[stored.storage]? = some current := by
    have bound := (Array.getElem?_eq_some_iff.mp present).1
    simp only [after, Array.set!, Array.getElem?_setIfInBounds_self_of_lt bound]
  obtain ⟨_, transported⟩ := sampledStored_start_transport stored receiving before after storage current run
    present currentFound rfl (fun _ _ => rfl) sampled
  let runStart := run.byteStart - stored.start
  let endOffset := finish - stored.start
  have runEq : run.byteStart = stored.start + runStart := by dsimp only [runStart]; omega
  have endEq : finish = stored.start + endOffset := by dsimp only [endOffset]; omega
  have originalRun : storedPathRun stored before =
      .ok (storage.bytes, ⟨stored.start + runStart, (storedWrittenRun stored run).count, run.element⟩) before := by
    simp only [storedPathRun, sampled, bind, pure]
    rw [← runEq]
    rfl
  have currentRun : storedPathRun { stored with start := receiving } after =
      .ok (current.bytes, ⟨receiving + runStart, (storedWrittenRun stored run).count, run.element⟩) after := by
    simp only [storedPathRun, transported, bind, pure]
    simp only [storedWrittenRun]
    rfl
  have measured : elementsEnd backingFuel (.ofModule module) run.element
      (storedWrittenRun stored run).count storage.bytes (stored.start + runStart) = .ok (stored.start + endOffset) := by
    rw [← runEq, ← endEq]
    exact backing
  obtain ⟨relocated, read, related⟩ := readStoredElement_relocated_success fuel backingFuel module accepted
    before after stored receiving stored.start receiving (storage.bytes.size - stored.start)
    runStart (storedWrittenRun stored run).count index endOffset run.element storage.bytes current.bytes value
    originalRun currentRun measured (by dsimp only [endOffset]; omega)
    (landingBytes_relocated storage.bytes receiving stored.start ordered sourceInside) observed
  refine ⟨after, relocated, ?_, read, related⟩
  have landed := landReceivingStorage_success before.construction stored.storage storage receiving stored.start
    present ordered sourceInside
  simp only [liftConstruction, landed]
  rfl

#print axioms sampledStored_start_transport
#print axioms readStoredElement_relocated_success
#print axioms landReceivingStorage_stored_read

end Goose.Proofs.ExitExecution
