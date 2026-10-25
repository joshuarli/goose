import Goose.Lower.Validation.ReplacementEmission

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem replacementRegion_current_contains {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner : ValueId} {origin : Option OriginId}
    {env : LEnv} {before cleared captured : LS} (live : LiveBound before)
    (clearRun : emitEffect (.clear owner origin) env before = ((), cleared))
    (emitted : EmitsOnly (ReplacementInstApart module types queries owner) cleared captured)
    (advance : cleared.Adv captured) {index : BlockId} {body : BlockB}
    (current : captured.cur = some index) (row : captured.blocks[index]? = some body) :
    owner ∈ transferEmptyBlock module types queries
      (ReplacementRegionFacts cleared captured owner index) (cfgBlock body) := by
  rcases advance.cur with stopped | same | ⟨fresh, selected, lower, upper⟩
  · simp [current] at stopped
  · have startCurrent : cleared.cur = some index := same.symm.trans current
    obtain ⟨head, tail, split, apart⟩ := emitsOnly_clear_current live clearRun emitted startCurrent row
    exact transferEmptyBlock_contains_clear split apart _
  · have equal : fresh = index := Option.some.inj (selected.symm.trans current)
    subst fresh
    apply transferEmptyBlock_retains_of_apart (emitted.fresh index body row lower)
    simp [ReplacementRegionFacts, lower, upper]

theorem replacementRegion_current_safe {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {valid : Array Bool} {owner runValue : ValueId}
    {origin clearOrigin : Option OriginId} {env : LEnv} {before cleared captured : LS}
    (live : LiveBound before)
    (clearRun : emitEffect (.clear owner clearOrigin) env before = ((), cleared))
    (emitted : EmitsOnly (ReplacementInstApart module types queries owner) cleared captured)
    (advance : cleared.Adv captured) {index : BlockId} {body : BlockB}
    (current : captured.cur = some index) (row : captured.blocks[index]? = some body)
    (ownerType : ∃ element, ownerTy types owner = some (.grow element) ∨ ownerTy types owner = some (.growshrink element))
    (fresh : valid[runValue]? = some true) :
    ReplacementSafe types valid
      (transferEmptyBlock module types queries (ReplacementRegionFacts cleared captured owner index) (cfgBlock body))
      (.eff (.replace owner runValue origin)) := by
  intro receiver value replacementOrigin same
  obtain ⟨rfl, rfl, rfl⟩ := Effect.replace.inj (Inst.eff.inj same)
  exact ⟨ownerType, fresh, replacementRegion_current_contains live clearRun emitted advance current row⟩

theorem checkReplace_after_independent_rhs {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {queries : ReplacementQueries} {valid : Array Bool}
    {owner runValue : ValueId} {origin clearOrigin : Option OriginId}
    {env : LEnv} {before cleared captured : LS} (live : LiveBound before)
    (clearRun : emitEffect (.clear owner clearOrigin) env before = ((), cleared))
    (emitted : EmitsOnly (ReplacementInstApart module types queries owner) cleared captured)
    (advance : cleared.Adv captured) {index : BlockId} {body : BlockB}
    (current : captured.cur = some index) (row : captured.blocks[index]? = some body)
    (ownerType : ∃ element, ownerTy types owner = some (.grow element) ∨ ownerTy types owner = some (.growshrink element))
    (fresh : valid[runValue]? = some true) (label : String) :
    checkReplace module func types queries valid label
      (transferEmptyBlock module types queries (ReplacementRegionFacts cleared captured owner index) (cfgBlock body))
      (.eff (.replace owner runValue origin)) = .ok () :=
  checkReplace_of_safe module func types queries valid label _ _
    (replacementRegion_current_safe live clearRun emitted advance current row ownerType fresh)

end Goose.Lower.Validation
