import Goose.Lower.Validation.ReplacementSourceSitesBranches

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

variable {root : DemandNode} {targets : List BlockId}

theorem ReplacementSitesAt.shortCircuit_generated {le : LEnv} {before : LS} (isAnd : Bool) (condition : ValueId)
    {rhs : B ValueId} (generated : GeneratedBuilderState before)
    (child : ∀ state, GeneratedBuilderState state → ReplacementSitesAt (root := root) (targets := (before.blocks.size + 1) :: targets) le state rhs) :
    ReplacementSitesAt (root := root) (targets := targets) le before (Goose.Lower.shortCircuit isAnd condition rhs) := by
  let forked := Goose.Lower.scFork isAnd condition le before
  let entered := Goose.Lower.setCur (some forked.1.1) le forked.2
  have allocatedGenerated := generated.scFork isAnd condition
    (show Goose.Lower.scFork isAnd condition le before = forked from rfl)
  have ids : forked.1 = (before.blocks.size, before.blocks.size + 1, before.vals.size) ∧
      forked.2.blocks.size = before.blocks.size + 2 := scFork_ids rfl
  have rhsBound : forked.1.1 < forked.2.blocks.size := by
    simp only [ids.1, ids.2]
    nat_omega
  have enteredGenerated := allocatedGenerated.setCur (some forked.1.1)
    (by intro current same; cases same; exact rhsBound)
    (show Goose.Lower.setCur _ le forked.2 = entered from rfl)
  unfold Goose.Lower.shortCircuit
  apply ReplacementSitesAt.whenLive
  intro block live
  let opened : B (BlockId × BlockId × ValueId) := do
    let triple ← Goose.Lower.scFork isAnd condition
    Goose.Lower.setCur (some triple.1)
    Pure.pure triple
  have openedValue : (opened le before).1 = forked.1 := by cases isAnd <;> rfl
  change ReplacementSitesAt (root := root) (targets := targets) le before (do
    let triple ← opened
    let value ← rhs
    Goose.Lower.emitTerm (.br triple.2.1 [value])
    Goose.Lower.setCur (some triple.2.1)
    Pure.pure triple.2.2)
  refine ReplacementSitesAt.reserve_prefix [forked.1.2.1] ?_ ?_ ?_ ?_
  · intro target member
    have same : target = forked.1.2.1 := by simpa using member
    simp only [same, ids.1]
    nat_omega
  · change ReplacementSitesFree (root := root) (targets := [forked.1.2.1] ++ targets) le before opened
    apply (ReplacementSitesFree.scFork _ _ _ _).bind
    apply (ReplacementSitesFree.setCur _ _ _).bind
    exact ReplacementSitesFree.pure _ _ _
  · intro target member
    have same : target = forked.1.2.1 := by simpa using member
    change target < forked.2.blocks.size
    simp only [same, ids.1, ids.2]
    nat_omega
  · have childChecked : ReplacementSitesAt (root := root) (targets := forked.1.2.1 :: targets) le entered.2 rhs := by
      simpa only [ids.1] using child entered.2 enteredGenerated
    apply childChecked.bind
    apply (ReplacementSitesAt.emitTerm _ _ _ (by
      intro target member
      have same : target = forked.1.2.1 := by simpa [Term.successors, openedValue] using member
      rw [same]
      exact Or.inl (List.mem_cons_self))).bind
    exact (ReplacementSitesAt.setCur _ _ _).bind (ReplacementSitesAt.pure _ _ _)

end Goose.Lower.Validation
