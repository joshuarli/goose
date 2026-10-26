import Goose.Construct.Layout

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepresentation
open Goose.Construct

private theorem layoutEnd_succFuel (fuel : Nat) (layout : LayoutEnv) (bytes : ByteArray) :
    (∀ ty start finish, packedEnd fuel layout ty bytes start = .ok finish →
      packedEnd (fuel + 1) layout ty bytes start = .ok finish) ∧
    (∀ ty count start finish, elementsEnd fuel layout ty count bytes start = .ok finish →
      elementsEnd (fuel + 1) layout ty count bytes start = .ok finish) := by
  induction fuel with
  | zero => constructor <;> intros <;> contradiction
  | succ fuel ih =>
    constructor
    · intro ty start finish checked
      simp only [packedEnd] at checked ⊢
      cases fixed : fixedByteSize? layout ty with
      | some width => simpa only [fixed] using checked
      | none =>
        simp only [fixed] at checked ⊢
        cases ty <;> try cases checked
        case arr element count => exact ih.2 element count start finish checked
        case varr element =>
          cases counted : readCount bytes start with
          | error reason => simp only [counted, bind, Except.bind] at checked; cases checked
          | ok count =>
            simp only [counted, bind, Except.bind] at checked ⊢
            exact ih.2 element count (start + 4) finish checked
    · intro ty count start finish checked
      cases count with
      | zero => exact checked
      | succ count =>
        simp only [elementsEnd] at checked ⊢
        cases first : packedEnd fuel layout ty bytes start with
        | error reason => simp only [first, bind, Except.bind] at checked; cases checked
        | ok middle =>
          simp only [first, bind, Except.bind] at checked
          rw [ih.1 ty start middle first]
          exact ih.2 ty count middle finish checked

theorem packedEnd_refuel (fuel larger : Nat) (layout : LayoutEnv) (ty : Ty)
    (bytes : ByteArray) (start finish : Nat) (bounded : fuel ≤ larger)
    (checked : packedEnd fuel layout ty bytes start = .ok finish) :
    packedEnd larger layout ty bytes start = .ok finish := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bounded
  clear bounded
  induction extra with
  | zero => exact checked
  | succ extra ih => exact (layoutEnd_succFuel (fuel + extra) layout bytes).1 ty start finish ih

theorem elementsEnd_refuel (fuel larger : Nat) (layout : LayoutEnv) (ty : Ty)
    (count : Nat) (bytes : ByteArray) (start finish : Nat) (bounded : fuel ≤ larger)
    (checked : elementsEnd fuel layout ty count bytes start = .ok finish) :
    elementsEnd larger layout ty count bytes start = .ok finish := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le bounded
  clear bounded
  induction extra with
  | zero => exact checked
  | succ extra ih => exact (layoutEnd_succFuel (fuel + extra) layout bytes).2 ty count start finish ih

theorem elementsEnd_append_one (fuel elementFuel : Nat) (layout : LayoutEnv) (ty : Ty)
    (count : Nat) (bytes : ByteArray) (start middle finish : Nat)
    (run : elementsEnd fuel layout ty count bytes start = .ok middle)
    (last : packedEnd elementFuel layout ty bytes middle = .ok finish) :
    ∃ larger, elementsEnd larger layout ty (count + 1) bytes start = .ok finish := by
  induction fuel generalizing count start with
  | zero => cases run
  | succ fuel ih =>
    cases count with
    | zero =>
      have same : start = middle := Except.ok.inj run
      subst start
      have element := packedEnd_refuel elementFuel (elementFuel + 1) layout ty bytes middle finish (Nat.le_succ _) last
      exact ⟨elementFuel + 2, by simp only [elementsEnd, element, bind, Except.bind]⟩
    | succ count =>
      simp only [elementsEnd] at run
      cases first : packedEnd fuel layout ty bytes start with
      | error reason => simp only [first, bind, Except.bind] at run; cases run
      | ok next =>
        simp only [first, bind, Except.bind] at run
        obtain ⟨restFuel, rest⟩ := ih count next run
        have first := packedEnd_refuel fuel (fuel + restFuel) layout ty bytes start next (by omega) first
        have rest := elementsEnd_refuel restFuel (fuel + restFuel) layout ty (count + 1) bytes next finish (by omega) rest
        exact ⟨fuel + restFuel + 1, by simp only [elementsEnd, first, bind, Except.bind, rest]⟩

#print axioms packedEnd_refuel
#print axioms elementsEnd_append_one

end Goose.Proofs.ConstructionRepresentation
