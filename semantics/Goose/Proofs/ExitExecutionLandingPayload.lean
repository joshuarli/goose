import Goose.Construct.Destination
import Goose.Proofs.ExitExecutionStorageIntervals

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

structure RelocatedBytes (before after : ByteArray) (source receiving count : Nat) : Prop where
  sourceBound : source + count ≤ before.size
  receivingBound : receiving + count ≤ after.size
  bytes : after.extract receiving (receiving + count) = before.extract source (source + count)

theorem RelocatedBytes.getElem? {before after : ByteArray} {source receiving count : Nat}
    (equal : RelocatedBytes before after source receiving count) (index : Nat) (inside : index < count) :
    after.data[receiving + index]? = before.data[source + index]? := by
  have bytes := (ByteArray.extract_eq_extract_iff_getElem equal.receivingBound equal.sourceBound).mp equal.bytes index inside
  rw [Array.getElem?_eq_getElem (by simpa using Nat.lt_of_lt_of_le (Nat.add_lt_add_left inside receiving) equal.receivingBound),
    Array.getElem?_eq_getElem (by simpa using Nat.lt_of_lt_of_le (Nat.add_lt_add_left inside source) equal.sourceBound)]
  exact congrArg some bytes

theorem RelocatedBytes.readCount {before after : ByteArray} {source receiving count : Nat}
    (equal : RelocatedBytes before after source receiving count) (start : Nat) (inside : start + 4 ≤ count) :
    Goose.Construct.readCount after (receiving + start) = Goose.Construct.readCount before (source + start) := by
  have beforeSize := equal.sourceBound
  have afterSize := equal.receivingBound
  have beforeBound : ¬source + start + 4 > before.size := by omega
  have afterBound : ¬receiving + start + 4 > after.size := by omega
  simp only [Goose.Construct.readCount, beforeBound, afterBound, ↓reduceIte,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil, bind, pure, Nat.add_assoc]
  rw [equal.getElem? (start + 0) (by omega), equal.getElem? (start + 1) (by omega),
    equal.getElem? (start + 2) (by omega), equal.getElem? (start + 3) (by omega)]

private theorem layoutEnd_relocated (fuel : Nat) (layout : LayoutEnv)
    (before after : ByteArray) (source receiving count : Nat)
    (equal : RelocatedBytes before after source receiving count) :
    (∀ ty start finish, Goose.Construct.packedEnd fuel layout ty before (source + start) = .ok (source + finish) → finish ≤ count →
      Goose.Construct.packedEnd fuel layout ty after (receiving + start) = .ok (receiving + finish)) ∧
    (∀ ty length start finish, Goose.Construct.elementsEnd fuel layout ty length before (source + start) = .ok (source + finish) → finish ≤ count →
      Goose.Construct.elementsEnd fuel layout ty length after (receiving + start) = .ok (receiving + finish)) := by
  induction fuel with
  | zero => constructor <;> intro <;> simp [Goose.Construct.packedEnd, Goose.Construct.elementsEnd] at *
  | succ fuel ih =>
    constructor
    · intro ty start finish observed inside
      simp only [Goose.Construct.packedEnd] at observed ⊢
      cases fixed : fixedByteSize? layout ty with
      | some width =>
        simp only [fixed] at observed ⊢
        split at observed
        · cases observed
        · have endSize := Except.ok.inj observed
          have bound := equal.receivingBound
          have fits : ¬receiving + start + width > after.size := by omega
          simp only [fits, ↓reduceIte, pure, Except.pure]
          congr 1
          omega
      | none =>
        simp only [fixed] at observed ⊢
        cases ty <;> try cases observed
        case arr element length => exact ih.2 element length start finish observed inside
        case varr element =>
          cases counted : Goose.Construct.readCount before (source + start) with
          | error reason => simp only [counted, bind, Except.bind] at observed; cases observed
          | ok length =>
            simp only [counted, bind, Except.bind, Nat.add_assoc] at observed
            have lower := elementsEnd_monotone fuel layout element length before (source + (start + 4)) (source + finish) observed
            simp only [equal.readCount start (by omega), counted, bind, Except.bind, Nat.add_assoc]
            exact ih.2 element length (start + 4) finish observed inside
    · intro ty length start finish observed inside
      cases length with
      | zero =>
        have same := Except.ok.inj observed
        have sameOffset : start = finish := by omega
        subst finish
        rfl
      | succ length =>
        simp only [Goose.Construct.elementsEnd] at observed ⊢
        cases next : Goose.Construct.packedEnd fuel layout ty before (source + start) with
        | error reason => simp only [next, bind, Except.bind] at observed; cases observed
        | ok middle =>
          simp only [next, bind, Except.bind] at observed
          have lower := packedEnd_monotone fuel layout ty before (source + start) middle next
          have upper := elementsEnd_monotone fuel layout ty length before middle (source + finish) observed
          let offset := middle - source
          have middleEq : middle = source + offset := by dsimp only [offset]; omega
          rw [middleEq] at next observed
          simp only [ih.1 ty start offset next (by omega), bind, Except.bind]
          exact ih.2 ty length offset finish observed inside

theorem RelocatedBytes.packedEnd {before after : ByteArray} {source receiving count : Nat}
    (equal : RelocatedBytes before after source receiving count) (fuel : Nat) (layout : LayoutEnv)
    (ty : Ty) (start finish : Nat)
    (observed : Goose.Construct.packedEnd fuel layout ty before (source + start) = .ok (source + finish)) (inside : finish ≤ count) :
    Goose.Construct.packedEnd fuel layout ty after (receiving + start) = .ok (receiving + finish) :=
  (layoutEnd_relocated fuel layout before after source receiving count equal).1 ty start finish observed inside

theorem RelocatedBytes.elementsEnd {before after : ByteArray} {source receiving count : Nat}
    (equal : RelocatedBytes before after source receiving count) (fuel : Nat) (layout : LayoutEnv)
    (ty : Ty) (length start finish : Nat)
    (observed : Goose.Construct.elementsEnd fuel layout ty length before (source + start) = .ok (source + finish)) (inside : finish ≤ count) :
    Goose.Construct.elementsEnd fuel layout ty length after (receiving + start) = .ok (receiving + finish) :=
  (layoutEnd_relocated fuel layout before after source receiving count equal).2 ty length start finish observed inside

theorem landingBytes_relocated (bytes : ByteArray) (receiving source : Nat)
    (ordered : receiving ≤ source) (inside : source ≤ bytes.size) :
    RelocatedBytes bytes (landingBytes bytes receiving source) source receiving (bytes.size - source) := by
  have prefixSize : (bytes.extract 0 receiving).size = receiving := by
    simp only [ByteArray.size_extract, Nat.sub_zero, Nat.min_eq_left (Nat.le_trans ordered inside)]
  have suffixSize : (bytes.extract source bytes.size).size = bytes.size - source := by
    simp only [ByteArray.size_extract, Nat.min_self]
  refine ⟨by omega, ?_, ?_⟩
  · simp only [landingBytes, ByteArray.size_append, prefixSize, suffixSize]
    exact Nat.le_refl _
  · have sourceEnd : source + (bytes.size - source) = bytes.size := by omega
    rw [sourceEnd]
    unfold landingBytes
    exact ByteArray.extract_append_eq_right (by exact prefixSize.symm)
      (by rw [prefixSize, suffixSize])

theorem landingBytes_prefix (bytes : ByteArray) (receiving source : Nat)
    (ordered : receiving ≤ source) (inside : source ≤ bytes.size) :
    BytePrefixEqual bytes (landingBytes bytes receiving source) receiving := by
  apply BytePrefixEqual.of_extract_eq _ _ _ (Nat.le_trans ordered inside)
  unfold landingBytes
  apply ByteArray.extract_append_eq_left
  simp only [ByteArray.size_extract, Nat.sub_zero, Nat.min_eq_left (Nat.le_trans ordered inside)]

theorem RelocatedBytes.elementInterval {before after : ByteArray} {source receiving count : Nat}
    (equal : RelocatedBytes before after source receiving count) (fuel : Nat) (layout : LayoutEnv)
    (element : Ty) (length runStart index start finish : Nat)
    (observed : Goose.Construct.elementInterval fuel layout before ⟨source + runStart, length, element⟩ index =
      .ok (source + start, source + finish)) (inside : finish ≤ count) :
    Goose.Construct.elementInterval fuel layout after ⟨receiving + runStart, length, element⟩ index =
      .ok (receiving + start, receiving + finish) := by
  obtain ⟨indexBound, first, last⟩ := elementInterval_result_inv fuel layout before
    ⟨source + runStart, length, element⟩ index (source + start) (source + finish) observed
  have lower := packedEnd_monotone fuel layout element before (source + start) (source + finish) last
  have prefixRead := equal.elementsEnd fuel layout element index runStart start first (by omega)
  have elementRead := equal.packedEnd fuel layout element start finish last inside
  simp only [Goose.Construct.elementInterval, Nat.not_le_of_gt indexBound, ↓reduceIte,
    prefixRead, elementRead, bind, Except.bind, pure, Except.pure]

theorem RelocatedBytes.samplePacked {before after : ByteArray} {source receiving count : Nat}
    (equal : RelocatedBytes before after source receiving count) (fuel : Nat) (layout : LayoutEnv)
    (ty : Ty) (start finish runStart length : Nat) (element : Ty)
    (scanned : Goose.Construct.packedEnd fuel layout ty before (source + start) = .ok (source + finish))
    (inside : finish ≤ count)
    (sampled : Goose.Construct.samplePacked ty before (source + start) = .ok ⟨source + runStart, length, element⟩) :
    Goose.Construct.samplePacked ty after (receiving + start) = .ok ⟨receiving + runStart, length, element⟩ := by
  cases ty <;> try (solve | cases sampled)
  case arr child size =>
    simp only [Goose.Construct.samplePacked, pure, Except.pure, Except.ok.injEq, SampledRun.mk.injEq, Nat.add_left_cancel_iff] at sampled
    obtain ⟨rfl, rfl, rfl⟩ := sampled
    rfl
  case varr child =>
    cases fuel with
    | zero => cases scanned
    | succ fuel =>
      simp only [Goose.Construct.packedEnd, fixedByteSize?] at scanned
      cases counted : Goose.Construct.readCount before (source + start) with
      | error reason => simp only [counted, bind, Except.bind] at scanned; cases scanned
      | ok size =>
        simp only [counted, bind, Except.bind, Nat.add_assoc] at scanned
        have lower := elementsEnd_monotone fuel layout child size before (source + (start + 4)) (source + finish) scanned
        simp only [Goose.Construct.samplePacked, counted, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq, SampledRun.mk.injEq, Nat.add_assoc, Nat.add_left_cancel_iff] at sampled
        obtain ⟨rfl, rfl, rfl⟩ := sampled
        simp only [Goose.Construct.samplePacked, equal.readCount start (by omega), counted,
          bind, Except.bind, pure, Except.pure, Nat.add_assoc]

theorem landingBytes_elementsEnd (fuel : Nat) (layout : LayoutEnv) (ty : Ty) (length : Nat)
    (bytes : ByteArray) (receiving source finish : Nat)
    (ordered : receiving ≤ source)
    (observed : Goose.Construct.elementsEnd fuel layout ty length bytes source = .ok finish) (inside : finish ≤ bytes.size) :
    Goose.Construct.elementsEnd fuel layout ty length (landingBytes bytes receiving source) receiving =
      .ok (receiving + (finish - source)) := by
  have lower := elementsEnd_monotone fuel layout ty length bytes source finish observed
  have sourceBound : source ≤ bytes.size := by omega
  have result := (landingBytes_relocated bytes receiving source ordered sourceBound).elementsEnd
    fuel layout ty length 0 (finish - source) (by simpa only [Nat.add_zero, Nat.add_sub_of_le lower] using observed) (by omega)
  simpa only [Nat.add_zero] using result

theorem landReceivingStorage_success (state : ConstructionState) (id : Nat)
    (storage : ReceivingStorage) (receiving source : Nat)
    (present : state.storage[id]? = some storage) (ordered : receiving ≤ source)
    (inside : source ≤ storage.bytes.size) :
    landReceivingStorage id receiving source state = .ok ()
      { state with storage := state.storage.set! id (storage.landExit receiving source) } := by
  simp only [landReceivingStorage, present, ordered, inside, decide_true, Bool.true_and, ↓reduceIte]

theorem landReceivingStorage_payload_backing (fuel : Nat) (layout : LayoutEnv) (ty : Ty)
    (length : Nat) (state : ConstructionState) (id : Nat) (storage : ReceivingStorage)
    (receiving source finish : Nat) (present : state.storage[id]? = some storage)
    (ordered : receiving ≤ source)
    (backing : Goose.Construct.elementsEnd fuel layout ty length storage.bytes source = .ok finish)
    (inside : finish ≤ storage.bytes.size) :
    ∃ after, landReceivingStorage id receiving source state = .ok () after ∧
      after.storage[id]? = some (storage.landExit receiving source) ∧
      Goose.Construct.elementsEnd fuel layout ty length
        (storage.landExit receiving source).bytes receiving = .ok (receiving + (finish - source)) := by
  have lower := elementsEnd_monotone fuel layout ty length storage.bytes source finish backing
  refine ⟨{ state with storage := state.storage.set! id (storage.landExit receiving source) },
    landReceivingStorage_success state id storage receiving source present ordered (by omega), ?_, ?_⟩
  · have bound := (Array.getElem?_eq_some_iff.mp present).1
    simp only [Array.set!, Array.getElem?_setIfInBounds_self_of_lt bound]
  · exact landingBytes_elementsEnd fuel layout ty length storage.bytes receiving source finish ordered backing inside

#print axioms RelocatedBytes.readCount
#print axioms RelocatedBytes.packedEnd
#print axioms RelocatedBytes.elementsEnd
#print axioms landingBytes_relocated
#print axioms landingBytes_prefix
#print axioms RelocatedBytes.elementInterval
#print axioms RelocatedBytes.samplePacked
#print axioms landingBytes_elementsEnd
#print axioms landReceivingStorage_success
#print axioms landReceivingStorage_payload_backing

end Goose.Proofs.ExitExecution
