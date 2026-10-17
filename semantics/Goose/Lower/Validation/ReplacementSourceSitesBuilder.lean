import Goose.Lower.Validation.ReplacementSourceSitesEvidence

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

variable {targets : List BlockId}

def NotReplacement : Inst → Prop
  | .eff (.replace _ _ _) => False
  | _ => True

theorem EmitsOnly.members {property : Inst → Prop} {before after : LS}
    (emitted : EmitsOnly property before after) {inst : Inst} (member : inst ∈ after.insts) :
    inst ∈ before.insts ∨ property inst := by
  obtain ⟨body, bodyMember, present⟩ := List.mem_flatMap.mp member
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp bodyMember)
  by_cases old : index < before.blocks.size
  · let previous := before.blocks[index]
    have previousRow : before.blocks[index]? = some previous := by simp [previous, old]
    obtain ⟨next, nextRow, _, tail, append, valid⟩ := emitted.old index previous previousRow
    have same : next = body := Option.some.inj (nextRow.symm.trans row)
    subst next
    rw [append] at present
    rcases List.mem_append.mp present with previousMember | tailMember
    · exact .inl (List.mem_flatMap.mpr
        ⟨previous, Array.mem_toList_iff.mpr (Array.mem_of_getElem? previousRow), previousMember⟩)
    · exact .inr (valid inst tailMember)
  · exact .inr (emitted.fresh index body row (Nat.le_of_not_gt old) inst present)

theorem ReplacementSitesBuilder.of_emits {le : LEnv} {before after : LS}
    (checked : ReplacementSitesBuilder (targets := targets) le before)
    (emitted : EmitsOnly NotReplacement before after) (types : TypePrefix before after)
    (preserved : ReplacementIntervalsPreserved targets before after) :
    ReplacementSitesBuilder (targets := targets) le after := by
  intro block body row position instruction lookup
  have contradictionOfFresh : NotReplacement instruction →
      ReplacementSourceAuthority (targets := targets) le after block position instruction := by
    intro fresh
    cases instruction with
    | eff effect => cases effect <;> first | exact True.intro | exact False.elim fresh
    | _ => exact True.intro
  by_cases old : block < before.blocks.size
  · let previous := before.blocks[block]
    have previousRow : before.blocks[block]? = some previous := by simp [previous, old]
    obtain ⟨next, nextRow, _, tail, append, valid⟩ := emitted.old block previous previousRow
    have same : next = body := Option.some.inj (nextRow.symm.trans row)
    subst next
    have listLookup : body.insts.toList[position]? = some instruction := by simpa using lookup
    rw [append, List.getElem?_append] at listLookup
    by_cases earlier : position < previous.insts.size
    · have prior : previous.insts[position]? = some instruction := by
        simpa [earlier] using listLookup
      exact (checked block previous previousRow position instruction prior).retained emitted.extension types preserved
    · apply contradictionOfFresh
      apply valid instruction
      have tailLookup : tail[position - previous.insts.size]? = some instruction := by
        simpa [earlier] using listLookup
      exact List.mem_of_getElem? tailLookup
  · apply contradictionOfFresh
    exact emitted.fresh block body row (Nat.le_of_not_gt old) instruction
      (by exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))

theorem ReplacementSitesBuilder.emitDef {le : LEnv} {before after : LS} {result : ValueId} {op : Op}
    (checked : ReplacementSitesBuilder (targets := targets) le before)
    (emitted : ∀ value, NotReplacement (.def value op))
    (run : emitDef op le before = (result, after)) : ReplacementSitesBuilder (targets := targets) le after :=
  checked.of_emits (emitsOnly_emitDef run (emitted _)) (types_emitDef op le before result after run)
    (.of_run (generatedTargetFrame_emitDef none op) run)

theorem ReplacementSitesBuilder.emitEffect {le : LEnv} {before after : LS} {result : Unit} {effect : Effect}
    (checked : ReplacementSitesBuilder (targets := targets) le before) (emitted : NotReplacement (.eff effect))
    (run : emitEffect effect le before = (result, after)) : ReplacementSitesBuilder (targets := targets) le after :=
  checked.of_emits (emitsOnly_emitEffect effect emitted le before result after run)
    (types_emitEffect effect le before result after run)
    (.of_run (generatedTargetFrame_emitEffect none effect) run)

theorem ReplacementSitesBuilder.emitTerm {le : LEnv} {before after : LS} {result : Unit} {term : Term}
    (checked : ReplacementSitesBuilder (targets := targets) le before)
    (allowed : ∀ target ∈ term.successors, target ∈ targets ∨ before.blocks.size ≤ target)
    (run : emitTerm term le before = (result, after)) : ReplacementSitesBuilder (targets := targets) le after :=
  checked.of_emits (emitsOnly_emitTerm term trivial le before result after run)
    (types_emitTerm term le before result after run)
    (.emitTerm run allowed)

theorem ReplacementSitesBuilder.patchTerm {le : LEnv} {before after : LS} {result : Unit}
    {block : BlockId} {term : Term} (checked : ReplacementSitesBuilder (targets := targets) le before)
    (run : patchTerm block term le before = (result, after))
    (allowed : ∀ target ∈ term.successors, target ∈ targets ∨ before.blocks.size ≤ target) : ReplacementSitesBuilder (targets := targets) le after := by
  have preserved := ReplacementIntervalsPreserved.patchTerm run allowed
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact checked.of_emits (.append before block (.term term) trivial) (.refl before) preserved

theorem ReplacementSitesBuilder.newBlock {le : LEnv} {before after : LS} {types : List VTy}
    {result : BlockId × List ValueId} (checked : ReplacementSitesBuilder (targets := targets) le before)
    (run : newBlock types le before = (result, after)) : ReplacementSitesBuilder (targets := targets) le after := by
  have preserved : ReplacementIntervalsPreserved targets before after :=
    .of_run (generatedTargetFrame_newBlock none types) run
  have typed := types_newBlock types le before result after run
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact checked.of_emits ((EmitsOnly.newBlock before _).trans (.of_blocks rfl)) typed preserved

end Goose.Lower.Validation
