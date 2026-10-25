import Goose.Proofs.ExitExecutionValidatedLayout
import Goose.Proofs.ExitExecutionStoragePrefixOutcomes

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem samplePacked_prefix_of_packedEnd (fuel : Nat) (layout : LayoutEnv) (ty : Ty)
    (before after : ByteArray) (start finish limit : Nat)
    (equal : BytePrefixEqual before after limit)
    (scanned : packedEnd fuel layout ty before start = .ok finish) (inside : finish ≤ limit) :
    samplePacked ty after start = samplePacked ty before start := by
  cases ty <;> try rfl
  case varr element =>
    cases fuel with
    | zero => cases scanned
    | succ fuel =>
        simp only [packedEnd, fixedByteSize?] at scanned
        cases counted : readCount before start with
        | error reason => simp only [counted, bind, Except.bind] at scanned; cases scanned
        | ok count =>
            simp only [counted, bind, Except.bind] at scanned
            have lower := elementsEnd_monotone fuel layout element count before (start + 4) finish scanned
            exact equal.samplePacked (.varr element) start (by omega)

private theorem fixedValue_width (fuel scanFuel : Nat) (layout : LayoutEnv) (ty : Ty)
    (bytes : ByteArray) (start finish : Nat) (value : Value)
    (fixed : ty.nonfixed = false)
    (scanned : packedEnd scanFuel layout ty bytes start = .ok finish)
    (decoded : fixedValue fuel layout ty bytes start = .ok value) :
    ∃ width, fixedByteSize? layout ty = some width ∧ start + width = finish := by
  cases scanFuel with
  | zero => cases scanned
  | succ scanFuel =>
    cases size : fixedByteSize? layout ty with
    | some width =>
        refine ⟨width, rfl, ?_⟩
        simp only [packedEnd, size] at scanned
        split at scanned
        · cases scanned
        · exact Except.ok.inj scanned
    | none =>
        cases fuel with
        | zero => cases decoded
        | succ fuel =>
            cases ty <;> try cases fixed
            all_goals try (simp only [fixedByteSize?] at size; cases size)
            case arr element count =>
              cases elementSize : fixedByteSize? layout element with
              | some width => simp only [fixedByteSize?, elementSize, Option.map_some] at size; cases size
              | none => simp only [fixedValue, elementSize] at decoded; cases decoded
            all_goals first | simp only [packedEnd, size] at scanned | simp only [packedEnd, fixedByteSize?] at scanned
            all_goals cases scanned

private theorem fixedValue_prefix_of_packedEnd (fuel scanFuel : Nat) (layout : LayoutEnv) (ty : Ty)
    (before after : ByteArray) (start finish limit : Nat)
    (equal : BytePrefixEqual before after limit) (fields : FixedLayoutFieldBounds layout)
    (fixed : ty.nonfixed = false)
    (scanned : packedEnd scanFuel layout ty before start = .ok finish) (inside : finish ≤ limit) :
    fixedValue fuel layout ty after start = fixedValue fuel layout ty before start := by
  cases scanFuel with
  | zero => cases scanned
  | succ scanFuel =>
    cases size : fixedByteSize? layout ty with
    | some width =>
        simp only [packedEnd, size] at scanned
        split at scanned
        · cases scanned
        · have endSize := Except.ok.inj scanned
          exact equal.fixedValue fuel layout fields ty width start size (by omega)
    | none =>
        cases fuel with
        | zero => rfl
        | succ fuel =>
            cases ty <;> try cases fixed
            all_goals try (simp only [fixedByteSize?] at size; cases size)
            case arr element count =>
              cases elementSize : fixedByteSize? layout element with
              | some width => simp only [fixedByteSize?, elementSize, Option.map_some] at size; cases size
              | none => simp only [fixedValue, elementSize]
            all_goals first
              | rfl
              | (simp only [packedEnd, size] at scanned; cases scanned)
              | (simp only [packedEnd, fixedByteSize?] at scanned; cases scanned)

theorem sampledStored_storage_transport (stored : StoredValue) (before after : ExecutionState)
    (original current : ReceivingStorage) (run : SampledRun)
    (originalStorage : before.construction.storage[stored.storage]? = some original)
    (currentStorage : after.construction.storage[stored.storage]? = some current)
    (count : current.publishedCount = original.publishedCount)
    (destination : ∀ id, stored.destination = some id →
      after.construction.destinations[id]? = before.construction.destinations[id]?)
    (sampled : sampledStored stored before = .ok (original.bytes, run) before) :
    sampledStored stored after = .ok (current.bytes, run) after := by
  cases selected : stored.destination with
  | none =>
      cases element : elementType stored.ty <;>
        simp only [sampledStored, getStorage, EvalM.get, bind, pure, originalStorage,
          currentStorage, selected, element, fault, EvalM.stop] at sampled ⊢
      · cases sampled
      · cases sampled; rfl
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
            first | (solve | cases sampled) | (cases sampled; rfl)

theorem readStoredElement_prefix_success (fuel backingFuel : Nat) (layout : LayoutEnv)
    (fields : FixedLayoutFieldBounds layout) (stored : StoredValue) (index : Nat)
    (before after : ExecutionState) (original current : ByteArray) (run : SampledRun)
    (finish : Nat) (value : Value)
    (originalRun : storedPathRun stored before = .ok (original, run) before)
    (currentRun : storedPathRun stored after = .ok (current, run) after)
    (backing : elementsEnd backingFuel layout run.element run.count original run.byteStart = .ok finish)
    (equal : BytePrefixEqual original current finish)
    (observed : readStoredElement fuel layout stored index before = .ok value before) :
    readStoredElement fuel layout stored index after = .ok value after := by
  simp only [readStoredElement, originalRun, currentRun, bind] at observed ⊢
  cases interval : elementInterval fuel layout original run index with
  | error reason =>
      cases reason <;> simp only [interval, liftLayout, fault, timeout, EvalM.stop] at observed <;>
        cases observed
  | ok pair =>
    obtain ⟨start, last⟩ := pair
    have within := elementInterval_within_run fuel backingFuel layout original run index start last finish interval backing
    have framed := equal.elementInterval fuel layout run index start last interval within
    simp only [interval, framed, liftLayout, pure] at observed ⊢
    have scanned := (elementInterval_result_inv fuel layout original run index start last interval).2.2
    cases nonfixed : run.element.nonfixed with
    | true =>
      have sampled := samplePacked_prefix_of_packedEnd fuel layout run.element original current start last finish equal scanned within
      simp only [nonfixed, ↓reduceIte, sampled] at observed ⊢
      cases sample : samplePacked run.element original start with
      | error reason =>
          cases reason <;> simp only [sample, fault, timeout, EvalM.stop] at observed <;>
            cases observed
      | ok packed =>
          simp only [sample] at observed ⊢
          cases observed
          rfl
    | false =>
      simp only [nonfixed, Bool.false_eq_true, ↓reduceIte] at observed ⊢
      cases decoded : fixedValue fuel layout run.element original start with
      | error reason => simp only [decoded, Goose.Construct.liftExcept, EvalM.stop] at observed; cases observed
      | ok decodedValue =>
          obtain ⟨width, size, endSize⟩ := fixedValue_width fuel fuel layout run.element original start last decodedValue nonfixed scanned decoded
          rw [equal.fixedValue fuel layout fields run.element width start size (by omega), decoded]
          simp only [decoded, Goose.Construct.liftExcept, pure] at observed ⊢
          cases observed
          rfl

theorem readStoredElement_prefix_observation (fuel backingFuel : Nat) (layout : LayoutEnv)
    (fields : FixedLayoutFieldBounds layout) (stored : StoredValue) (index : Nat)
    (before after : ExecutionState) (original current : ByteArray) (run : SampledRun)
    (finish : Nat)
    (originalRun : storedPathRun stored before = .ok (original, run) before)
    (currentRun : storedPathRun stored after = .ok (current, run) after)
    (backing : elementsEnd backingFuel layout run.element run.count original run.byteStart = .ok finish)
    (equal : BytePrefixEqual original current finish) :
    mapStepState (fun _ => ExecutionState.initial) (readStoredElement fuel layout stored index after) =
      mapStepState (fun _ => ExecutionState.initial) (readStoredElement fuel layout stored index before) := by
  simp only [readStoredElement, originalRun, currentRun, bind,
    equal.elementInterval_outcome fuel backingFuel layout run index finish backing (Nat.le_refl _)]
  cases interval : elementInterval fuel layout original run index with
  | error reason => cases reason <;> rfl
  | ok pair =>
    obtain ⟨start, last⟩ := pair
    simp only [liftLayout, pure]
    have within := elementInterval_within_run fuel backingFuel layout original run index start last finish interval backing
    have scanned := (elementInterval_result_inv fuel layout original run index start last interval).2.2
    cases nonfixed : run.element.nonfixed with
    | true =>
      have sampled := samplePacked_prefix_of_packedEnd fuel layout run.element original current start last finish equal scanned within
      simp only [↓reduceIte, sampled]
      cases sample : samplePacked run.element original start with
      | error reason => cases reason <;> rfl
      | ok packed => rfl
    | false =>
      have decoded := fixedValue_prefix_of_packedEnd fuel fuel layout run.element original current start last finish equal fields nonfixed scanned within
      simp only [Bool.false_eq_true, ↓reduceIte, decoded]
      cases fixedValue fuel layout run.element original start <;> rfl

#print axioms sampledStored_storage_transport
#print axioms readStoredElement_prefix_success
#print axioms readStoredElement_prefix_observation

end Goose.Proofs.ExitExecution
