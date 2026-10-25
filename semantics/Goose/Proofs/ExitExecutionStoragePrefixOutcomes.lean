import Goose.Proofs.ExitExecutionStorageIntervals

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem layoutEnd_prefix_outcomes (fuel : Nat) (layout : LayoutEnv)
    (before after : ByteArray) (limit : Nat) (equal : BytePrefixEqual before after limit) :
    (∀ backingFuel ty start finish, Goose.Construct.packedEnd backingFuel layout ty before start = .ok finish →
      finish ≤ limit → Goose.Construct.packedEnd fuel layout ty after start = Goose.Construct.packedEnd fuel layout ty before start) ∧
    (∀ backingFuel ty count start finish, Goose.Construct.elementsEnd backingFuel layout ty count before start = .ok finish →
      finish ≤ limit → Goose.Construct.elementsEnd fuel layout ty count after start = Goose.Construct.elementsEnd fuel layout ty count before start) := by
  induction fuel with
  | zero => exact ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  | succ fuel ih =>
    constructor
    · intro backingFuel ty start finish backing inside
      cases backingFuel with
      | zero => cases backing
      | succ backingFuel =>
        simp only [Goose.Construct.packedEnd] at backing ⊢
        cases size : fixedByteSize? layout ty with
        | some width =>
          simp only [size] at backing ⊢
          split at backing
          · cases backing
          · have endSize := Except.ok.inj backing
            have beforeSize := equal.beforeBound
            have afterSize := equal.afterBound
            have left : ¬start + width > before.size := by omega
            have right : ¬start + width > after.size := by omega
            simp only [left, right, ↓reduceIte]
        | none =>
          simp only [size] at backing ⊢
          cases ty <;> try cases backing
          case arr element count => exact ih.2 backingFuel element count start finish backing inside
          case varr element =>
            cases counted : readCount before start with
            | error reason => simp only [counted, bind, Except.bind] at backing; cases backing
            | ok count =>
              simp only [counted, bind, Except.bind] at backing
              have lower := elementsEnd_monotone backingFuel layout element count before (start + 4) finish backing
              simp only [equal.readCount start (by omega), counted, bind, Except.bind]
              exact ih.2 backingFuel element count (start + 4) finish backing inside
    · intro backingFuel ty count start finish backing inside
      cases backingFuel with
      | zero => cases backing
      | succ backingFuel =>
        cases count with
        | zero => rfl
        | succ count =>
          simp only [Goose.Construct.elementsEnd] at backing ⊢
          cases first : Goose.Construct.packedEnd backingFuel layout ty before start with
          | error reason => simp only [first, bind, Except.bind] at backing; cases backing
          | ok middle =>
            simp only [first, bind, Except.bind] at backing
            have lower := elementsEnd_monotone backingFuel layout ty count before middle finish backing
            rw [ih.1 backingFuel ty start middle first (by omega)]
            cases requested : Goose.Construct.packedEnd fuel layout ty before start with
            | error reason => rfl
            | ok point =>
              have same := packedEnd_success_unique fuel backingFuel layout ty before start point middle requested first
              subst point
              exact ih.2 backingFuel ty count middle finish backing inside

theorem BytePrefixEqual.packedEnd_outcome {before after : ByteArray} {limit : Nat}
    (equal : BytePrefixEqual before after limit) (fuel backingFuel : Nat) (layout : LayoutEnv)
    (ty : Ty) (start finish : Nat)
    (backing : Goose.Construct.packedEnd backingFuel layout ty before start = .ok finish) (inside : finish ≤ limit) :
    Goose.Construct.packedEnd fuel layout ty after start = Goose.Construct.packedEnd fuel layout ty before start :=
  (layoutEnd_prefix_outcomes fuel layout before after limit equal).1 backingFuel ty start finish backing inside

theorem BytePrefixEqual.elementsEnd_outcome {before after : ByteArray} {limit : Nat}
    (equal : BytePrefixEqual before after limit) (fuel backingFuel : Nat) (layout : LayoutEnv)
    (ty : Ty) (count start finish : Nat)
    (backing : Goose.Construct.elementsEnd backingFuel layout ty count before start = .ok finish) (inside : finish ≤ limit) :
    Goose.Construct.elementsEnd fuel layout ty count after start = Goose.Construct.elementsEnd fuel layout ty count before start :=
  (layoutEnd_prefix_outcomes fuel layout before after limit equal).2 backingFuel ty count start finish backing inside

theorem elementsEnd_element_backing (fuel : Nat) (layout : LayoutEnv) (ty : Ty)
    (bytes : ByteArray) (total start finish index : Nat)
    (backing : Goose.Construct.elementsEnd fuel layout ty total bytes start = .ok finish) (inside : index < total) :
    ∃ elementFuel first last,
      Goose.Construct.elementsEnd fuel layout ty index bytes start = .ok first ∧
      Goose.Construct.packedEnd elementFuel layout ty bytes first = .ok last ∧ last ≤ finish := by
  induction fuel generalizing total start index with
  | zero => cases backing
  | succ fuel ih =>
    cases total with
    | zero => omega
    | succ total =>
      simp only [Goose.Construct.elementsEnd] at backing
      cases first : Goose.Construct.packedEnd fuel layout ty bytes start with
      | error reason => simp only [first, bind, Except.bind] at backing; cases backing
      | ok middle =>
        simp only [first, bind, Except.bind] at backing
        cases index with
        | zero =>
          exact ⟨fuel, start, middle, rfl, first,
            elementsEnd_monotone fuel layout ty total bytes middle finish backing⟩
        | succ index =>
          obtain ⟨elementFuel, point, last, scanned, element, bounded⟩ :=
            ih total middle index backing (by omega)
          refine ⟨elementFuel, point, last, ?_, element, bounded⟩
          simp only [Goose.Construct.elementsEnd, first, bind, Except.bind, scanned]

theorem BytePrefixEqual.elementInterval_outcome {before after : ByteArray} {limit : Nat}
    (equal : BytePrefixEqual before after limit) (fuel backingFuel : Nat) (layout : LayoutEnv)
    (run : SampledRun) (index finish : Nat)
    (backing : Goose.Construct.elementsEnd backingFuel layout run.element run.count before run.byteStart = .ok finish)
    (inside : finish ≤ limit) :
    Goose.Construct.elementInterval fuel layout after run index = Goose.Construct.elementInterval fuel layout before run index := by
  unfold Goose.Construct.elementInterval
  split
  · rfl
  · rename_i indexBound
    obtain ⟨elementFuel, first, last, scanned, element, bounded⟩ :=
      elementsEnd_element_backing backingFuel layout run.element before run.count run.byteStart finish index backing (by omega)
    have firstBound := packedEnd_monotone elementFuel layout run.element before first last element
    rw [equal.elementsEnd_outcome fuel backingFuel layout run.element index run.byteStart first scanned (by omega)]
    cases requested : Goose.Construct.elementsEnd fuel layout run.element index before run.byteStart with
    | error reason => rfl
    | ok point =>
      have same := elementsEnd_success_unique fuel backingFuel layout run.element index before run.byteStart point first requested scanned
      subst point
      simp only [bind, Except.bind,
        equal.packedEnd_outcome fuel elementFuel layout run.element first last element (by omega)]

#print axioms BytePrefixEqual.packedEnd_outcome
#print axioms BytePrefixEqual.elementsEnd_outcome
#print axioms elementsEnd_element_backing
#print axioms BytePrefixEqual.elementInterval_outcome

end Goose.Proofs.ExitExecution
