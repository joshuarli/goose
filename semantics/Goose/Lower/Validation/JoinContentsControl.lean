import Goose.Lower.Validation.JoinContentsAuthority

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ContentsEvidence.fresh_zero {le : LEnv} {state : LS} {value : ValueId}
    (evidence : ContentsEvidence le state value) : FreshContentsEvidence le 0 state value := by
  obtain ⟨authorized, closed, noninteger, member⟩ := evidence
  exact ⟨authorized, closed, noninteger, member, fun _ _ => Nat.zero_le _⟩

theorem joinValue_contents {le : LEnv} {before after : LS} {endT endF : Option BlockId}
    {valueT valueF value : ValueId} {ty : VTy}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (targets : TargetsBounded before)
    (thenBound : ∀ block, endT = some block → block < before.blocks.size)
    (elseBound : ∀ block, endF = some block → block < before.blocks.size)
    (thenTyped : endT.isSome = true → before.vals[valueT]? = some (some ty))
    (elseTyped : endF.isSome = true → before.vals[valueF]? = some (some ty))
    (noninteger : ∀ intTy, ty ≠ .data (.int intTy))
    (thenEvidence : endT.isSome = true → ContentsEvidence le before valueT)
    (elseEvidence : endF.isSome = true → ContentsEvidence le before valueF)
    (run : joinValue endT valueT endF valueF le before = (value, after))
    (live : after.cur.isSome = true) :
    ContentsEvidence le after value ∧
      (endT.isSome = true → ContentsEvidence le after valueT) ∧
      (endF.isSome = true → ContentsEvidence le after valueF) := by
  have result := joinValue_freshContents checked bounded targets thenBound elseBound thenTyped elseTyped
    noninteger (Nat.zero_le _) (fun active => (thenEvidence active).fresh_zero)
    (fun active => (elseEvidence active).fresh_zero)
  rw [run] at result
  obtain ⟨joined, left, right⟩ := result live
  exact ⟨joined.forget, fun active => (left active).forget, fun active => (right active).forget⟩

theorem joinValue_freshContents_run {le : LEnv} {before after : LS} {endT endF : Option BlockId}
    {valueT valueF value : ValueId} {ty : VTy} {first : Nat}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (targets : TargetsBounded before)
    (thenBound : ∀ block, endT = some block → block < before.blocks.size)
    (elseBound : ∀ block, endF = some block → block < before.blocks.size)
    (thenTyped : endT.isSome = true → before.vals[valueT]? = some (some ty))
    (elseTyped : endF.isSome = true → before.vals[valueF]? = some (some ty))
    (noninteger : ∀ intTy, ty ≠ .data (.int intTy))
    (lower : first ≤ before.vals.size)
    (thenEvidence : endT.isSome = true → FreshContentsEvidence le first before valueT)
    (elseEvidence : endF.isSome = true → FreshContentsEvidence le first before valueF)
    (run : joinValue endT valueT endF valueF le before = (value, after))
    (live : after.cur.isSome = true) :
    FreshContentsEvidence le first after value ∧
      (endT.isSome = true → FreshContentsEvidence le first after valueT) ∧
      (endF.isSome = true → FreshContentsEvidence le first after valueF) := by
  have result := joinValue_freshContents checked bounded targets thenBound elseBound thenTyped elseTyped
    noninteger lower thenEvidence elseEvidence
  rw [run] at result
  exact result live

#print axioms joinValue_contents
#print axioms joinValue_freshContents_run
#print axioms ContentsClosed.patchBrs_avoiding_target
#print axioms FreshContentsEvidence.patchBrs_before

end Goose.Lower.Validation
