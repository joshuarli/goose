import Goose.Construct.Layout
import Init.Data.ByteArray.Lemmas
import Init.Data.Range.Lemmas

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

structure BytePrefixEqual (before after : ByteArray) (finish : Nat) : Prop where
  beforeBound : finish ≤ before.size
  afterBound : finish ≤ after.size
  bytes : after.extract 0 finish = before.extract 0 finish

theorem BytePrefixEqual.of_extract_eq (before after : ByteArray) (finish : Nat)
    (bound : finish ≤ before.size)
    (bytes : after.extract 0 finish = before.extract 0 finish) :
    BytePrefixEqual before after finish := by
  have sizes := congrArg ByteArray.size bytes
  simp only [ByteArray.size_extract, Nat.sub_zero, Nat.min_eq_left bound] at sizes
  exact ⟨bound, by omega, bytes⟩

theorem BytePrefixEqual.getElem? {before after : ByteArray} {finish : Nat}
    (equal : BytePrefixEqual before after finish) (index : Nat) (inside : index < finish) :
    after.data[index]? = before.data[index]? := by
  have bytes := (ByteArray.extract_eq_extract_iff_getElem
    (as := after) (bs := before) (i := 0) (j := 0) (len := finish)
    (by simpa using equal.afterBound) (by simpa using equal.beforeBound)).mp
    (by simpa using equal.bytes) index inside
  simp only [Nat.zero_add] at bytes
  rw [Array.getElem?_eq_getElem (by simpa using Nat.lt_of_lt_of_le inside equal.afterBound),
    Array.getElem?_eq_getElem (by simpa using Nat.lt_of_lt_of_le inside equal.beforeBound)]
  exact congrArg some bytes

theorem BytePrefixEqual.readCount {before after : ByteArray} {finish : Nat}
    (equal : BytePrefixEqual before after finish) (start : Nat) (inside : start + 4 ≤ finish) :
    Goose.Construct.readCount after start = Goose.Construct.readCount before start := by
  have beforeSize := equal.beforeBound
  have afterSize := equal.afterBound
  have beforeBound : ¬start + 4 > before.size := by omega
  have afterBound : ¬start + 4 > after.size := by omega
  simp only [Goose.Construct.readCount, beforeBound, afterBound, ↓reduceIte,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [List.range'_succ, List.range'_zero, List.forIn_cons, List.forIn_nil, bind, pure]
  rw [equal.getElem? (start + 0) (by omega), equal.getElem? (start + 1) (by omega),
    equal.getElem? (start + 2) (by omega), equal.getElem? (start + 3) (by omega)]

private theorem layoutEnd_monotone (fuel : Nat) (layout : LayoutEnv) (bytes : ByteArray) :
    (∀ ty start finish, Goose.Construct.packedEnd fuel layout ty bytes start = .ok finish → start ≤ finish) ∧
    (∀ ty count start finish, Goose.Construct.elementsEnd fuel layout ty count bytes start = .ok finish → start ≤ finish) := by
  induction fuel with
  | zero => constructor <;> intro <;> simp [Goose.Construct.packedEnd, Goose.Construct.elementsEnd]
  | succ fuel ih =>
    constructor
    · intro ty start finish observed
      simp only [Goose.Construct.packedEnd] at observed
      cases fixed : fixedByteSize? layout ty with
      | some width =>
          simp only [fixed] at observed
          split at observed
          · cases observed
          · cases observed; omega
      | none =>
          simp only [fixed] at observed
          cases ty <;> try cases observed
          case arr element count => exact ih.2 element count start finish observed
          case varr element =>
            cases counted : Goose.Construct.readCount bytes start with
            | error reason => simp only [counted, bind, Except.bind] at observed; cases observed
            | ok count =>
                simp only [counted, bind, Except.bind] at observed
                have bound := ih.2 element count (start + 4) finish observed
                omega
    · intro ty count start finish observed
      cases count with
      | zero => cases observed; exact Nat.le_refl _
      | succ count =>
          simp only [Goose.Construct.elementsEnd] at observed
          cases next : Goose.Construct.packedEnd fuel layout ty bytes start with
          | error reason => simp only [next, bind, Except.bind] at observed; cases observed
          | ok middle =>
              simp only [next, bind, Except.bind] at observed
              exact Nat.le_trans (ih.1 ty start middle next) (ih.2 ty count middle finish observed)

theorem packedEnd_monotone (fuel : Nat) (layout : LayoutEnv) (ty : Ty)
    (bytes : ByteArray) (start finish : Nat)
    (observed : Goose.Construct.packedEnd fuel layout ty bytes start = .ok finish) : start ≤ finish :=
  (layoutEnd_monotone fuel layout bytes).1 ty start finish observed

theorem elementsEnd_monotone (fuel : Nat) (layout : LayoutEnv) (ty : Ty) (count : Nat)
    (bytes : ByteArray) (start finish : Nat)
    (observed : Goose.Construct.elementsEnd fuel layout ty count bytes start = .ok finish) : start ≤ finish :=
  (layoutEnd_monotone fuel layout bytes).2 ty count start finish observed

private theorem layoutEnd_prefix (fuel : Nat) (layout : LayoutEnv)
    (before after : ByteArray) (limit : Nat) (equal : BytePrefixEqual before after limit) :
    (∀ ty start finish, Goose.Construct.packedEnd fuel layout ty before start = .ok finish → finish ≤ limit →
      Goose.Construct.packedEnd fuel layout ty after start = .ok finish) ∧
    (∀ ty count start finish, Goose.Construct.elementsEnd fuel layout ty count before start = .ok finish → finish ≤ limit →
      Goose.Construct.elementsEnd fuel layout ty count after start = .ok finish) := by
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
          · cases observed
            have bound := equal.afterBound
            have fits : ¬start + width > after.size := by omega
            simp only [fits, ↓reduceIte, pure]
            rfl
      | none =>
          simp only [fixed] at observed ⊢
          cases ty <;> try cases observed
          case arr element count => exact ih.2 element count start finish observed inside
          case varr element =>
            cases counted : Goose.Construct.readCount before start with
            | error reason => simp only [counted, bind, Except.bind] at observed; cases observed
            | ok count =>
                simp only [counted, bind, Except.bind] at observed
                have lower := elementsEnd_monotone fuel layout element count before (start + 4) finish observed
                rw [equal.readCount start (by omega), counted]
                exact ih.2 element count (start + 4) finish observed inside
    · intro ty count start finish observed inside
      cases count with
      | zero => exact observed
      | succ count =>
          simp only [Goose.Construct.elementsEnd] at observed ⊢
          cases next : Goose.Construct.packedEnd fuel layout ty before start with
          | error reason => simp only [next, bind, Except.bind] at observed; cases observed
          | ok middle =>
              simp only [next, bind, Except.bind] at observed
              have lower := elementsEnd_monotone fuel layout ty count before middle finish observed
              rw [ih.1 ty start middle next (by omega)]
              exact ih.2 ty count middle finish observed inside

theorem BytePrefixEqual.packedEnd {before after : ByteArray} {limit : Nat}
    (equal : BytePrefixEqual before after limit) (fuel : Nat) (layout : LayoutEnv)
    (ty : Ty) (start finish : Nat)
    (observed : Goose.Construct.packedEnd fuel layout ty before start = .ok finish) (inside : finish ≤ limit) :
    Goose.Construct.packedEnd fuel layout ty after start = .ok finish :=
  (layoutEnd_prefix fuel layout before after limit equal).1 ty start finish observed inside

theorem BytePrefixEqual.elementsEnd {before after : ByteArray} {limit : Nat}
    (equal : BytePrefixEqual before after limit) (fuel : Nat) (layout : LayoutEnv)
    (ty : Ty) (count start finish : Nat)
    (observed : Goose.Construct.elementsEnd fuel layout ty count before start = .ok finish) (inside : finish ≤ limit) :
    Goose.Construct.elementsEnd fuel layout ty count after start = .ok finish :=
  (layoutEnd_prefix fuel layout before after limit equal).2 ty count start finish observed inside

theorem BytePrefixEqual.elementInterval {before after : ByteArray} {limit : Nat}
    (equal : BytePrefixEqual before after limit) (fuel : Nat) (layout : LayoutEnv)
    (run : SampledRun) (index start finish : Nat)
    (observed : Goose.Construct.elementInterval fuel layout before run index = .ok (start, finish))
    (inside : finish ≤ limit) :
    Goose.Construct.elementInterval fuel layout after run index = .ok (start, finish) := by
  simp only [Goose.Construct.elementInterval] at observed ⊢
  split at observed
  · cases observed
  · rename_i bounded
    simp only [bounded, ↓reduceIte]
    cases scanned : Goose.Construct.elementsEnd fuel layout run.element index before run.byteStart with
    | error reason => simp only [scanned, bind, Except.bind] at observed; cases observed
    | ok first =>
        simp only [scanned, bind, Except.bind] at observed
        cases last : Goose.Construct.packedEnd fuel layout run.element before first with
        | error reason => simp only [last] at observed; cases observed
        | ok final =>
            simp only [last] at observed
            have same : (first, final) = (start, finish) := by exact Except.ok.inj observed
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
            have lower := packedEnd_monotone fuel layout run.element before first final last
            simp only [equal.elementsEnd fuel layout run.element index run.byteStart first scanned (by omega),
              bind, Except.bind, equal.packedEnd fuel layout run.element first final last inside]
            rfl

theorem BytePrefixEqual.samplePacked {before after : ByteArray} {limit : Nat}
    (equal : BytePrefixEqual before after limit) (ty : Ty) (start : Nat)
    (inside : start + 4 ≤ limit) :
    Goose.Construct.samplePacked ty after start = Goose.Construct.samplePacked ty before start := by
  cases ty <;> first | rfl | (simp only [Goose.Construct.samplePacked]; rw [equal.readCount start inside])

#print axioms BytePrefixEqual.readCount
#print axioms packedEnd_monotone
#print axioms elementsEnd_monotone
#print axioms BytePrefixEqual.packedEnd
#print axioms BytePrefixEqual.elementsEnd
#print axioms BytePrefixEqual.elementInterval
#print axioms BytePrefixEqual.samplePacked

end Goose.Proofs.ExitExecution
