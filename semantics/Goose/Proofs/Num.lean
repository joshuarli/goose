namespace Goose.Proofs.Num

/-- Euclidean remainder is nonnegative and below the divisor's magnitude. -/
theorem emod_range (a b : Int) (h : b ≠ 0) :
    0 ≤ a % b ∧ a % b < (b.natAbs : Int) := by
  refine ⟨Int.emod_nonneg a h, ?_⟩
  have := Int.emod_lt a h
  omega

end Goose.Proofs.Num
