import Goose.Lower.Validation.JoinContentsAllocation

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem joinLive_freshContents {le : LEnv} {before : LS}
    {incoming : List (BlockId × ValueId)} {ty : VTy} {first : Nat}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (targets : TargetsBounded before) (nonempty : 0 < before.blocks.size)
    (typed : before.vals[(incoming.headD (0, 0)).2]? = some (some ty))
    (noninteger : ∀ intTy, ty ≠ .data (.int intTy))
    (lower : first ≤ before.vals.size)
    (evidence : ∀ pair ∈ incoming, FreshContentsEvidence le first before pair.2) :
    let action : B ValueId := do
      let valueTy ← valTy (incoming.headD (0, 0)).2
      let (join, params) ← newBlock [valueTy]
      patchBrs join incoming
      setCur (some join)
      pure (params.headD 0)
    let (value, after) := action le before
    FreshContentsEvidence le first after value ∧
      ∀ pair ∈ incoming, FreshContentsEvidence le first after pair.2 := by
  obtain ⟨authorized, closed, oldNoninteger, arguments, fresh⟩ := FreshContentsEvidence.common incoming evidence
  simp only [bind_run, valTy_of_recorded typed, newBlock1_run]
  let allocated : LS :=
    { before with
      blocks := before.blocks.push ⟨[(before.vals.size, ty)], #[]⟩
      vals := before.vals.push (some ty) }
  have allocation : newBlock [ty] le before = ((before.blocks.size, [before.vals.size]), allocated) :=
    newBlock1_run ty le before
  have allocatedDense := dense_newBlock [ty] le before _ allocated allocation checked bounded
  have expanded := closed.newJoin checked bounded targets nonempty allocation
  have oldBound : ∀ value, authorized value → value < before.vals.size := by
    intro value member
    simpa only [permissionFunc_numValues checked le] using closed.bounded value member
  have expandedNoninteger := oldNoninteger.newJoin checked allocation oldBound noninteger
  cases patched : patchBrs before.blocks.size incoming le allocated with
  | mk patchResult middle =>
      have finalClosed := expanded.patchBrs incoming allocatedDense.1 allocatedDense.2.1 patched
        (fun pair member => Or.inl (arguments pair member))
      have finalNoninteger := expandedNoninteger.patchBrs incoming patched
      have finalFresh : ∀ value, authorized value ∨ value = before.vals.size → first ≤ value := by
        intro value member
        exact member.elim (fresh value) (fun same => same ▸ lower)
      simp only [setCur_run, pure_run, List.headD_cons]
      constructor
      · exact ⟨_, finalClosed, finalNoninteger, Or.inr rfl, finalFresh⟩
      · intro pair member
        exact ⟨_, finalClosed, finalNoninteger, Or.inl (arguments pair member), finalFresh⟩

theorem joinValue_freshContents {le : LEnv} {before : LS} {endT endF : Option BlockId}
    {valueT valueF : ValueId} {ty : VTy} {first : Nat}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (targets : TargetsBounded before)
    (thenBound : ∀ block, endT = some block → block < before.blocks.size)
    (elseBound : ∀ block, endF = some block → block < before.blocks.size)
    (thenTyped : endT.isSome = true → before.vals[valueT]? = some (some ty))
    (elseTyped : endF.isSome = true → before.vals[valueF]? = some (some ty))
    (noninteger : ∀ intTy, ty ≠ .data (.int intTy))
    (lower : first ≤ before.vals.size)
    (thenEvidence : endT.isSome = true → FreshContentsEvidence le first before valueT)
    (elseEvidence : endF.isSome = true → FreshContentsEvidence le first before valueF) :
    let (value, after) := joinValue endT valueT endF valueF le before
    after.cur.isSome = true → FreshContentsEvidence le first after value ∧
      (endT.isSome = true → FreshContentsEvidence le first after valueT) ∧
      (endF.isSome = true → FreshContentsEvidence le first after valueF) := by
  cases endT with
  | none =>
      cases endF with
      | none => simp [joinValue, bind_run, setCur_run, pure_run]
      | some block =>
          have result := joinLive_freshContents (incoming := [(block, valueF)]) checked bounded targets
            (Nat.zero_lt_of_lt (elseBound block rfl)) (elseTyped rfl) noninteger lower
            (by intro pair member; obtain rfl := List.mem_singleton.mp member; exact elseEvidence rfl)
          intro live
          exact ⟨result.1, by simp, fun _ => result.2 (block, valueF) (by simp)⟩
  | some block =>
      cases endF with
      | none =>
          have result := joinLive_freshContents (incoming := [(block, valueT)]) checked bounded targets
            (Nat.zero_lt_of_lt (thenBound block rfl)) (thenTyped rfl) noninteger lower
            (by intro pair member; obtain rfl := List.mem_singleton.mp member; exact thenEvidence rfl)
          intro live
          exact ⟨result.1, fun _ => result.2 (block, valueT) (by simp), by simp⟩
      | some other =>
          have result := joinLive_freshContents (incoming := [(block, valueT), (other, valueF)]) checked bounded targets
            (Nat.zero_lt_of_lt (thenBound block rfl)) (thenTyped rfl) noninteger lower (by
              intro pair member
              rcases List.mem_cons.mp member with rfl | member
              · exact thenEvidence rfl
              · have same := List.mem_singleton.mp member
                subst pair
                exact elseEvidence rfl)
          intro live
          exact ⟨result.1, fun _ => result.2 (block, valueT) (by simp), fun _ => result.2 (other, valueF) (by simp)⟩

#print axioms joinLive_freshContents
#print axioms joinValue_freshContents

end Goose.Lower.Validation
