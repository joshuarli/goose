import Goose.Lower.Validation.ReplacementSourceSitesBranches

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

variable {targets : List BlockId}

theorem ReplacementSitesAt.header_generated {le : LEnv} {before : LS} (types : List VTy) (arguments : List ValueId)
    {tail : BlockId → List ValueId → B α} (generated : GeneratedBuilderState before)
    (child : ∀ header parameters state, GeneratedBuilderState state → header < state.blocks.size →
      ReplacementSitesAt (targets := header :: targets) le state (tail header parameters)) :
    ReplacementSitesAt (targets := targets) le before (do
      let (header, parameters) ← Goose.Lower.newBlock types
      Goose.Lower.emitTerm (.br header arguments)
      Goose.Lower.setCur (some header)
      tail header parameters) := by
  let allocated := Goose.Lower.newBlock types le before
  let closed := Goose.Lower.emitTerm (.br allocated.1.1 arguments) le allocated.2
  let entered := Goose.Lower.setCur (some allocated.1.1) le closed.2
  have allocatedGenerated := generated.newBlock types
    (show Goose.Lower.newBlock types le before = allocated from rfl)
  have id : allocated.1.1 = before.blocks.size := by simp [allocated, newBlock_run_general]
  have size : allocated.2.blocks.size = before.blocks.size + 1 := by simp [allocated, newBlock_run_general]
  have bound : allocated.1.1 < allocated.2.blocks.size := by rw [id, size]; nat_omega
  have closedGenerated := allocatedGenerated.emitTerm (.br allocated.1.1 arguments)
    (by intro target member; have same : target = allocated.1.1 := by simpa [Term.successors] using member
        rw [same]; exact bound)
    (show Goose.Lower.emitTerm _ le allocated.2 = closed from rfl)
  have closedFacts := dense_emitTerm (.br allocated.1.1 arguments) le allocated.2 closed.1 closed.2 rfl
    allocatedGenerated.dense allocatedGenerated.live
  have laterBound := Nat.lt_of_lt_of_le bound closedFacts.2.2
  have enteredGenerated := closedGenerated.setCur (some allocated.1.1)
    (by intro current same; cases same; exact laterBound)
    (show Goose.Lower.setCur _ le closed.2 = entered from rfl)
  let opened : B (BlockId × List ValueId) := do
    let pair ← Goose.Lower.newBlock types
    Goose.Lower.emitTerm (.br pair.1 arguments)
    Goose.Lower.setCur (some pair.1)
    Pure.pure pair
  change ReplacementSitesAt (targets := targets) le before
    (opened >>= fun pair => tail pair.1 pair.2)
  refine ReplacementSitesAt.reserve_prefix [allocated.1.1] ?_ ?_ ?_ ?_
  · intro target member
    have same : target = allocated.1.1 := by simpa using member
    rw [same, id]
    exact Nat.le_refl _
  · change ReplacementSitesFree (targets := [allocated.1.1] ++ targets) le before _
    apply (ReplacementSitesFree.newBlock _ _ _).bind
    apply (ReplacementSitesFree.emitTerm _ _ _ (by
      intro target member
      have same : target = allocated.1.1 := by simpa [Term.successors] using member
      rw [same]
      exact Or.inl (List.mem_cons_self))).bind
    apply (ReplacementSitesFree.setCur _ _ _).bind
    exact ReplacementSitesFree.pure _ _ _
  · intro target member
    have same : target = allocated.1.1 := by simpa using member
    rw [same]
    exact laterBound
  · exact child allocated.1.1 allocated.1.2 entered.2 enteredGenerated laterBound

end Goose.Lower.Validation
