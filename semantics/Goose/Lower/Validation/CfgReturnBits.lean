import Goose.GIR.Validate

namespace Goose.Lower.Validation

open Goose.GIR

def ReturnBitsLE (left right : Array Bool) : Prop :=
  left.size = right.size ∧ ∀ (index : Nat), left[index]? = some true → right[index]? = some true

theorem ReturnBitsLE.refl (bits : Array Bool) : ReturnBitsLE bits bits :=
  ⟨rfl, fun _ found => found⟩

theorem ReturnBitsLE.trans {one two three : Array Bool}
    (first : ReturnBitsLE one two) (second : ReturnBitsLE two three) : ReturnBitsLE one three :=
  ⟨first.1.trans second.1, fun index found => second.2 index (first.2 index found)⟩

theorem ReturnBitsLE.replicate_false (bits : Array Bool) :
    ReturnBitsLE (Array.replicate bits.size false) bits := by
  refine ⟨by simp, ?_⟩
  intro index found
  simp only [Array.getElem?_replicate] at found
  split at found <;> simp_all

private theorem list_return_count {left right : List Bool}
    (length : left.length = right.length)
    (retains : ∀ (index : Nat), left[index]? = some true → right[index]? = some true) :
    left.count true ≤ right.count true ∧ (left.count true = right.count true → left = right) := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
    cases right with
    | nil => simp at length
    | cons next rest =>
      have tails : tail.length = rest.length := by simpa using length
      have retainTail : ∀ (index : Nat), tail[index]? = some true → rest[index]? = some true := by
        intro index found
        simpa using retains (index + 1) (by simpa using found)
      have previous := ih tails retainTail
      have first := retains 0
      cases head <;> cases next
      · simpa using previous
      · simp
        constructor <;> omega
      · simp at first
      · simpa [List.count_cons] using previous

theorem ReturnBitsLE.count {left right : Array Bool} (order : ReturnBitsLE left right) :
    left.count true ≤ right.count true ∧ (left.count true = right.count true → left = right) := by
  have result := list_return_count (left := left.toList) (right := right.toList)
    (by simpa using order.1) (by simpa using order.2)
  refine ⟨by simpa using result.1, ?_⟩
  intro equal
  apply Array.toList_inj.mp
  exact result.2 (by simpa using equal)

theorem ReturnBitsLE.strict {left right : Array Bool} (order : ReturnBitsLE left right)
    (different : left ≠ right) : left.count true < right.count true := by
  have counted := order.count
  have unequal : left.count true ≠ right.count true := fun same => different (counted.2 same)
  omega

theorem ReturnBitsLE.getD {left right : Array Bool} (order : ReturnBitsLE left right)
    (index : Nat) (returns : left[index]?.getD true = true) : right[index]?.getD true = true := by
  cases first : left[index]? with
  | none =>
    have missing : right[index]? = none := Array.getElem?_eq_none_iff.mpr (by
      rw [← order.1]
      exact Array.getElem?_eq_none_iff.mp first)
    simp [missing]
  | some value =>
    cases value with
    | false => simp [first] at returns
    | true => simp [order.2 index first]

end Goose.Lower.Validation
