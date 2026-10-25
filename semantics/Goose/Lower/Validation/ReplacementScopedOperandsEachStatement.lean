import Goose.Lower.Validation.ReplacementScopedOperandsWrites

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem rhsOperands_eachStatement (floor : Nat) (loop : Option LoopCtx)
    (slot : VarId) (index : Option VarId) (view : View) (byRef : Bool)
    (body : Core.Block) (origin : OriginId)
    (sourceChild : RhsOperandsRun floor (lowerEachSource view)) (bodyChild : RhsBlockChild floor body) :
    RhsOperandsRun floor (lowerStmt loop (.forEach slot index view byRef body origin)) := by
  intro env before bound
  let sourced := lowerEachSource view env before
  let regrown := regrowOf sourced.1.1 env sourced.2
  let sampled := eachSampled regrown.1 sourced.1.2 env regrown.2
  let started := emitDef (.constInt .i64 0) env sampled.2
  have sourcedBound := Nat.le_trans bound (advB_lowerEachSource view env before sourced.1 sourced.2 rfl).vals
  have regrownBound := Nat.le_trans sourcedBound (advB_regrowOf sourced.1.1 env sourced.2 regrown.1 regrown.2 rfl).vals
  have sampledBound := Nat.le_trans regrownBound (advB_eachSampled regrown.1 sourced.1.2 env regrown.2 sampled.1 sampled.2 rfl).vals
  have startedBound := Nat.le_trans sampledBound (advB_emitDef _ env sampled.2 started.1 started.2 rfl).vals
  have viewFresh : RhsValueFresh floor regrown.2 sourced.1.2 := by
    intro live
    have sourceLive := live_before (rhs_regrowOf_dead _) rfl live
    exact (rhs_eachSource_fresh floor view bound rfl sourceLive).2
  simp only [lowerStmt]
  apply (sourceChild env before bound).bind
  apply (RhsOperandsAt.of_blocks (congrArg LS.blocks (rhs_regrowOf_state _ _ _))).bind
  apply (rhsOperands_eachSampled floor env regrown.2 regrown.1 sourced.1.2 viewFresh).bind
  apply (RhsOperandsAt.emitDef _ _ _ _ (by simp [Op.uses])).bind
  apply RhsOperandsAt.whenLive
  intro block active
  have startedLive : started.2.cur.isSome = true := congrArg Option.isSome active
  have sampledLive := live_before (dead_emitDef _) rfl startedLive
  have regrownLive := live_before (rhs_eachSampled_dead _ _) rfl sampledLive
  have sourcedLive := live_before (rhs_regrowOf_dead _) rfl regrownLive
  have sourceFresh : (∀ address, sourced.1.1 = some address → floor ≤ address) ∧ floor ≤ sourced.1.2 := rhs_eachSource_fresh floor view bound (rfl : lowerEachSource view env before = sourced) sourcedLive
  have ownerFresh : regrown.1 = true → floor ≤ sourced.1.1.getD 0 := by
    intro growing
    have ownerExists := rhs_regrowOf_hasOwner (env := env) (before := sourced.2)
      (after := regrown.2) (show regrowOf sourced.1.1 env sourced.2 = (true, regrown.2) from
        by rw [← growing])
    cases ownerAt : sourced.1.1 with
    | none => simp [ownerAt] at ownerExists
    | some address => simpa [ownerAt] using sourceFresh.1 address ownerAt
  have sampledFresh : regrown.1 = false → floor ≤ sampled.1 := by
    intro fixed
    have sampleRun : emitDef (.viewLen sourced.1.2) env regrown.2 = sampled := by
      simpa only [sampled, eachSampled, fixed, Bool.false_eq_true, ↓reduceIte]
    exact RhsValueFresh.output regrownBound (freshValue_emitDef _) sampleRun sampledLive
  have startFresh : floor ≤ started.1 := RhsValueFresh.output sampledBound (freshValue_emitDef _) (rfl : emitDef _ env sampled.2 = started) startedLive
  apply (RhsOperandsAt.newBlock _ _ _ _).bindRun
  intro header allocated allocation
  have counterFresh : floor ≤ header.2.headD 0 := by
    have ids := congrArg Prod.fst allocation
    rw [newBlock1_run] at ids
    have equal : started.2.vals.size = header.2.headD 0 := by
      simpa using congrArg (fun pair => pair.2.headD 0) ids
    exact equal ▸ startedBound
  have allocatedBound := Nat.le_trans startedBound (advB_newBlock1 _ env started.2 header allocated allocation).vals
  apply (RhsOperandsAt.emitTerm floor env allocated (.br header.1 [started.1])
    (by simpa only [Term.uses, List.mem_singleton] using fun _ value equal => equal ▸ startFresh)).bind
  apply (RhsOperandsAt.setCur _ _ _ _).bind
  apply rhsOperands_lowerEach floor regrown.1 sourced.1.1 sampled.1 header.1 (header.2.headD 0)
    (fun depth exit => do
      let element ← emitDef (.refElem sourced.1.2 (header.2.headD 0))
      let value ← eachElemValue slot byRef element
      lowerBlock (some ⟨depth, exit, .next header.1 .i64 (header.2.headD 0)⟩)
        ((slot, value, origin) :: (match (generalizing := false) index with
          | some other => [(other, header.2.headD 0, origin)] | none => [])) false body)
    ownerFresh sampledFresh counterFresh
  · intro depth exit
    exact AdvB.bind (advB_emitDef _) fun element =>
      AdvB.bind (advB_eachElemValue slot byRef element) fun _ => advB_lowerBlock _ _ _ _
  · intro depth exit env state stateBound
    let reference := emitDef (.refElem sourced.1.2 (header.2.headD 0)) env state
    let value := eachElemValue slot byRef reference.1 env reference.2
    have referenceBound := Nat.le_trans stateBound (advB_emitDef _ env state reference.1 reference.2 rfl).vals
    have valueBound := Nat.le_trans referenceBound (advB_eachElemValue slot byRef reference.1 env reference.2 value.1 value.2 rfl).vals
    have referenceFresh := RhsValueFresh.output stateBound (freshValue_emitDef _) (rfl : emitDef _ env state = reference)
    have valueFresh := RhsValueFresh.eachElemValue referenceBound referenceFresh (rfl : eachElemValue slot byRef reference.1 env reference.2 = value)
    apply (RhsOperandsAt.emitDef floor env state (.refElem sourced.1.2 (header.2.headD 0))
      (by
        intro _ used member
        simp only [Op.uses, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact sourceFresh.2
        · exact counterFresh)).bind
    apply (rhsOperands_eachElemValue floor env reference.2 slot byRef reference.1 referenceFresh).bind
    apply bodyChild (some ⟨depth, exit, .next header.1 .i64 (header.2.headD 0)⟩)
      ((slot, value.1, origin) :: (match (generalizing := false) index with
        | some other => [(other, header.2.headD 0, origin)] | none => [])) false env value.2 valueBound counterFresh
    intro live entry member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact valueFresh live
    · cases index with
      | none => simp at member
      | some other =>
        have equal : entry = (other, header.2.headD 0, origin) := List.mem_singleton.mp member
        subst entry
        exact counterFresh
  · exact Nat.le_trans allocatedBound (advB_emitTerm (.br header.1 [started.1]) env allocated _ _ rfl).vals

end Goose.Lower.Validation
