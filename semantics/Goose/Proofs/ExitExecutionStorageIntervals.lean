import Goose.Proofs.ExitExecutionStoragePrefixReads

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem layoutEnd_compare (fuel : Nat) (layout : LayoutEnv) (bytes : ByteArray) :
    (∀ other ty start finish final,
      packedEnd fuel layout ty bytes start = .ok finish →
      packedEnd other layout ty bytes start = .ok final → finish = final) ∧
    (∀ other ty count total start finish final,
      elementsEnd fuel layout ty count bytes start = .ok finish →
      elementsEnd other layout ty total bytes start = .ok final → count ≤ total →
      finish ≤ final ∧ (count = total → finish = final)) := by
  induction fuel with
  | zero => constructor <;> intro <;> simp [packedEnd, elementsEnd] at *
  | succ fuel ih =>
    constructor
    · intro other ty start finish final left right
      cases other with
      | zero => cases right
      | succ other =>
        simp only [packedEnd] at left right
        cases fixed : fixedByteSize? layout ty with
        | some width =>
            simp only [fixed] at left right
            split at left
            · cases left
            · rename_i fits
              simp only [fits, ↓reduceIte] at right
              exact (Except.ok.inj left).symm.trans (Except.ok.inj right)
        | none =>
            simp only [fixed] at left right
            cases ty <;> try cases left
            case arr element count =>
              exact (ih.2 other element count count start finish final left right (Nat.le_refl _)).2 rfl
            case varr element =>
              cases counted : readCount bytes start with
              | error reason => simp only [counted, bind, Except.bind] at left; cases left
              | ok count =>
                  simp only [counted, bind, Except.bind] at left right
                  exact (ih.2 other element count count (start + 4) finish final left right (Nat.le_refl _)).2 rfl
    · intro other ty count total start finish final left right bounded
      cases other with
      | zero => cases right
      | succ other =>
        cases count with
        | zero =>
            have same := Except.ok.inj left
            subst finish
            refine ⟨elementsEnd_monotone (other + 1) layout ty total bytes start final right, ?_⟩
            intro same
            subst total
            exact Except.ok.inj right
        | succ count =>
            cases total with
            | zero => omega
            | succ total =>
              simp only [elementsEnd] at left right
              cases first : packedEnd fuel layout ty bytes start with
              | error reason => simp only [first, bind, Except.bind] at left; cases left
              | ok middle =>
                simp only [first, bind, Except.bind] at left
                cases second : packedEnd other layout ty bytes start with
                | error reason => simp only [second, bind, Except.bind] at right; cases right
                | ok last =>
                  simp only [second, bind, Except.bind] at right
                  have same := ih.1 other ty start middle last first second
                  subst last
                  obtain ⟨order, exactCount⟩ := ih.2 other ty count total middle finish final left right (by omega)
                  exact ⟨order, fun counts => exactCount (by omega)⟩

theorem packedEnd_success_unique (fuel other : Nat) (layout : LayoutEnv) (ty : Ty)
    (bytes : ByteArray) (start finish final : Nat)
    (left : packedEnd fuel layout ty bytes start = .ok finish)
    (right : packedEnd other layout ty bytes start = .ok final) : finish = final :=
  (layoutEnd_compare fuel layout bytes).1 other ty start finish final left right

theorem elementsEnd_prefix_bound (fuel other : Nat) (layout : LayoutEnv) (ty : Ty)
    (count total : Nat) (bytes : ByteArray) (start finish final : Nat)
    (left : elementsEnd fuel layout ty count bytes start = .ok finish)
    (right : elementsEnd other layout ty total bytes start = .ok final)
    (bounded : count ≤ total) : finish ≤ final :=
  ((layoutEnd_compare fuel layout bytes).2 other ty count total start finish final left right bounded).1

theorem elementsEnd_success_unique (fuel other : Nat) (layout : LayoutEnv) (ty : Ty)
    (count : Nat) (bytes : ByteArray) (start finish final : Nat)
    (left : elementsEnd fuel layout ty count bytes start = .ok finish)
    (right : elementsEnd other layout ty count bytes start = .ok final) : finish = final :=
  ((layoutEnd_compare fuel layout bytes).2 other ty count count start finish final left right (Nat.le_refl _)).2 rfl

private theorem elementEnd_bound (fuel : Nat) (layout : LayoutEnv) (ty : Ty) (bytes : ByteArray) :
    ∀ other elementFuel index total start first finish final,
      elementsEnd fuel layout ty index bytes start = .ok first →
      packedEnd elementFuel layout ty bytes first = .ok finish →
      elementsEnd other layout ty total bytes start = .ok final →
      index < total → finish ≤ final := by
  induction fuel with
  | zero => intro; simp [elementsEnd]
  | succ fuel ih =>
    intro other elementFuel index total start first finish final scanned element whole inside
    cases other with
    | zero => cases whole
    | succ other =>
      cases total with
      | zero => omega
      | succ total =>
        simp only [elementsEnd] at whole
        cases firstWhole : packedEnd other layout ty bytes start with
        | error reason => simp only [firstWhole, bind, Except.bind] at whole; cases whole
        | ok middle =>
          simp only [firstWhole, bind, Except.bind] at whole
          cases index with
          | zero =>
              have same : start = first := Except.ok.inj scanned
              subst first
              have sameEnd := packedEnd_success_unique elementFuel other layout ty bytes start finish middle element firstWhole
              subst finish
              exact elementsEnd_monotone other layout ty total bytes middle final whole
          | succ index =>
              simp only [elementsEnd] at scanned
              cases firstPrefix : packedEnd fuel layout ty bytes start with
              | error reason => simp only [firstPrefix, bind, Except.bind] at scanned; cases scanned
              | ok next =>
                  simp only [firstPrefix, bind, Except.bind] at scanned
                  have same := packedEnd_success_unique fuel other layout ty bytes start next middle firstPrefix firstWhole
                  subst next
                  exact ih other elementFuel index total middle first finish final scanned element whole (by omega)

theorem elementInterval_within_run (fuel backingFuel : Nat) (layout : LayoutEnv)
    (bytes : ByteArray) (run : SampledRun) (index start finish final : Nat)
    (interval : elementInterval fuel layout bytes run index = .ok (start, finish))
    (backing : elementsEnd backingFuel layout run.element run.count bytes run.byteStart = .ok final) :
    finish ≤ final := by
  simp only [elementInterval] at interval
  split at interval
  · cases interval
  · rename_i inside
    cases scanned : elementsEnd fuel layout run.element index bytes run.byteStart with
    | error reason => simp only [scanned, bind, Except.bind] at interval; cases interval
    | ok first =>
      simp only [scanned, bind, Except.bind] at interval
      cases element : packedEnd fuel layout run.element bytes first with
      | error reason => simp only [element] at interval; cases interval
      | ok last =>
          simp only [element] at interval
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj interval)
          exact elementEnd_bound fuel layout run.element bytes backingFuel fuel index run.count
            run.byteStart first last final scanned element backing (by omega)

theorem elementInterval_prefix_transport (fuel backingFuel : Nat) (layout : LayoutEnv)
    (before after : ByteArray) (run : SampledRun) (index start finish final : Nat)
    (equal : BytePrefixEqual before after final)
    (interval : elementInterval fuel layout before run index = .ok (start, finish))
    (backing : elementsEnd backingFuel layout run.element run.count before run.byteStart = .ok final) :
    elementInterval fuel layout after run index = .ok (start, finish) :=
  equal.elementInterval fuel layout run index start finish interval
    (elementInterval_within_run fuel backingFuel layout before run index start finish final interval backing)

theorem elementInterval_result_inv (fuel : Nat) (layout : LayoutEnv) (bytes : ByteArray)
    (run : SampledRun) (index start finish : Nat)
    (interval : elementInterval fuel layout bytes run index = .ok (start, finish)) :
    index < run.count ∧ elementsEnd fuel layout run.element index bytes run.byteStart = .ok start ∧
      packedEnd fuel layout run.element bytes start = .ok finish := by
  simp only [elementInterval] at interval
  split at interval
  · cases interval
  · rename_i inside
    cases first : elementsEnd fuel layout run.element index bytes run.byteStart with
    | error reason => simp only [first, bind, Except.bind] at interval; cases interval
    | ok begin =>
      simp only [first, bind, Except.bind] at interval
      cases ending : packedEnd fuel layout run.element bytes begin with
      | error reason => simp only [ending] at interval; cases interval
      | ok endByte =>
        simp only [ending] at interval
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj interval)
        exact ⟨by omega, rfl, ending⟩

#print axioms packedEnd_success_unique
#print axioms elementsEnd_prefix_bound
#print axioms elementsEnd_success_unique
#print axioms elementInterval_within_run
#print axioms elementInterval_prefix_transport
#print axioms elementInterval_result_inv

end Goose.Proofs.ExitExecution
