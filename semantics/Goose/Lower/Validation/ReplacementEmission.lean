import Goose.Lower.Validation.ReplacementEmissionEvidence
import Goose.Lower.Validation.ReplacementRegions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmitsOnly.extension {property : Inst → Prop} {before after : LS}
    (emitted : EmitsOnly property before after) : before.Ext after := by
  refine ⟨emitted.blocks, ?_⟩
  intro index body row
  obtain ⟨next, nextAt, params, tail, append, _⟩ := emitted.old index body row
  exact ⟨next, nextAt, params, tail, append⟩

theorem EmitsOnly.of_blocks {property : Inst → Prop} {before after : LS}
    (same : after.blocks = before.blocks) : EmitsOnly property before after := by
  constructor
  · simp only [same, Nat.le_refl]
  · intro index body row
    exact ⟨body, same ▸ row, rfl, [], by simp, by simp⟩
  · intro index body row lower inst member
    have bound := (Array.getElem?_eq_some_iff.mp row).1
    rw [same] at bound
    omega

theorem EmitsOnly.refl (property : Inst → Prop) (state : LS) : EmitsOnly property state state :=
  .of_blocks rfl

theorem EmitsOnly.trans {property : Inst → Prop} {before middle after : LS}
    (first : EmitsOnly property before middle) (second : EmitsOnly property middle after) :
    EmitsOnly property before after := by
  refine ⟨Nat.le_trans first.blocks second.blocks, ?_, ?_⟩
  · intro index body row
    obtain ⟨mid, midAt, midParams, head, firstAppend, firstProperty⟩ := first.old index body row
    obtain ⟨next, nextAt, nextParams, tail, secondAppend, secondProperty⟩ := second.old index mid midAt
    refine ⟨next, nextAt, nextParams.trans midParams, head ++ tail, ?_, ?_⟩
    · rw [secondAppend, firstAppend, List.append_assoc]
    · intro inst member
      rcases List.mem_append.mp member with previous | fresh
      · exact firstProperty inst previous
      · exact secondProperty inst fresh
  · intro index body row lower inst member
    by_cases old : index < middle.blocks.size
    · let mid := middle.blocks[index]
      have midAt : middle.blocks[index]? = some mid := by simp [mid, old]
      obtain ⟨next, nextAt, _, tail, append, tailProperty⟩ := second.old index mid midAt
      have same : next = body := Option.some.inj (nextAt.symm.trans row)
      subst next
      rw [append] at member
      rcases List.mem_append.mp member with previous | fresh
      · exact first.fresh index mid midAt lower inst previous
      · exact tailProperty inst fresh
    · exact second.fresh index body row (Nat.le_of_not_gt old) inst member

theorem EmitsOnly.append {property : Inst → Prop} (state : LS) (index : BlockId)
    (inst : Inst) (valid : property inst) :
    EmitsOnly property state { state with blocks := (state.blocks.modify index
      (fun body => { body with insts := body.insts.push inst })) } := by
  constructor
  · simp
  · intro other body row
    rw [Array.getElem?_modify, row]
    by_cases same : index = other
    · simp only [same, ↓reduceIte, Option.map_some]
      exact ⟨_, rfl, rfl, [inst], by simp, by simpa using valid⟩
    · simp only [same, ↓reduceIte]
      exact ⟨body, rfl, rfl, [], by simp, by simp⟩
  · intro other body row lower member present
    have bound := (Array.getElem?_eq_some_iff.mp row).1
    simp only [Array.size_modify] at bound
    omega

theorem EmitsOnly.newBlock {property : Inst → Prop} (state : LS) (params : List (ValueId × VTy)) :
    EmitsOnly property state { state with blocks := state.blocks.push ⟨params, #[]⟩ } := by
  constructor
  · simp
  · intro index body row
    have bound := (Array.getElem?_eq_some_iff.mp row).1
    refine ⟨body, ?_, rfl, [], by simp, by simp⟩
    rw [Array.getElem?_push]
    simp [Nat.ne_of_lt bound, row]
  · intro index body row lower inst member
    have bound := (Array.getElem?_eq_some_iff.mp row).1
    have same : index = state.blocks.size := by
      have upper : index < state.blocks.size + 1 := by simpa only [Array.size_push] using bound
      exact Nat.le_antisymm (Nat.le_of_lt_succ upper) lower
    subst index
    simp only [Array.getElem?_push_eq, Option.some.injEq] at row
    subst body
    simp at member

def EmitsOnlyRun (property : Inst → Prop) (action : B α) : Prop :=
  ∀ env before value after, action env before = (value, after) → EmitsOnly property before after

theorem EmitsOnlyRun.pure (property : Inst → Prop) (value : α) : EmitsOnlyRun property (pure value) := by
  intro env before result after run
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact .refl property before

theorem EmitsOnlyRun.bind {property : Inst → Prop} {action : B α} {next : α → B β}
    (first : EmitsOnlyRun property action) (second : ∀ value, EmitsOnlyRun property (next value)) :
    EmitsOnlyRun property (action >>= next) := by
  intro env before result after run
  obtain ⟨value, middle, firstRun, secondRun⟩ := bind_eq.mp run
  exact (first env before value middle firstRun).trans (second value env middle result after secondRun)

theorem emitsOnly_pushInst {property : Inst → Prop} (index : BlockId) (inst : Inst)
    (valid : property inst) : EmitsOnlyRun property (pushInst index inst) := by
  intro env before value after run
  change ((), { before with blocks := (before.blocks.modify index
    (fun body => { body with insts := body.insts.push inst })) }) = (value, after) at run
  cases run
  exact .append before index inst valid

theorem emitsOnly_emitEffect {property : Inst → Prop} (effect : Effect)
    (valid : property (.eff effect)) : EmitsOnlyRun property (emitEffect effect) := by
  intro env before value after run
  cases current : before.cur with
  | none =>
    rw [emitEffect_none _ _ current] at run
    cases run
    exact .refl _ _
  | some index =>
    rw [emitEffect_run _ _ current] at run
    cases run
    exact .append before index (.eff effect) valid

theorem emitsOnly_emitTerm {property : Inst → Prop} (term : Term)
    (valid : property (.term term)) : EmitsOnlyRun property (emitTerm term) := by
  intro env before value after run
  cases current : before.cur with
  | none =>
    rw [emitTerm_none _ _ current] at run
    cases run
    exact .refl _ _
  | some index =>
    rw [emitTerm_run _ _ current] at run
    cases run
    exact (EmitsOnly.append before index (.term term) valid).trans (.of_blocks rfl)

theorem emitsOnly_emitDef {property : Inst → Prop} {op : Op} {env : LEnv}
    {before after : LS} {value : ValueId} (run : emitDef op env before = (value, after))
    (valid : property (.def before.vals.size op)) : EmitsOnly property before after := by
  cases current : before.cur with
  | none =>
    rw [emitDef_none _ _ current] at run
    cases run
    exact .refl _ _
  | some index =>
    rw [emitDef_run _ _ current] at run
    cases run
    exact (EmitsOnly.append before index (.def before.vals.size op) valid).trans (.of_blocks rfl)

theorem emitsOnly_after_clear {property : Inst → Prop} {env : LEnv}
    {before cleared captured : LS} {owner : ValueId} {origin : Option OriginId}
    {index : BlockId} {body : BlockB}
    (current : before.cur = some index) (row : before.blocks[index]? = some body)
    (clearRun : emitEffect (.clear owner origin) env before = ((), cleared))
    (emitted : EmitsOnly property cleared captured) :
    ∃ next tail, captured.blocks[index]? = some next ∧
      next.insts.toList = body.insts.toList ++ (.eff (.clear owner origin) :: tail) ∧
      ∀ inst ∈ tail, property inst := by
  rw [emitEffect_run _ _ current] at clearRun
  cases clearRun
  have clearAt : (before.blocks.modify index
      (fun old => { old with insts := old.insts.push (.eff (.clear owner origin)) }))[index]? =
      some { body with insts := body.insts.push (.eff (.clear owner origin)) } := by
    rw [Array.getElem?_modify, row]
    simp
  obtain ⟨next, nextAt, _, tail, append, valid⟩ := emitted.old index _ clearAt
  refine ⟨next, tail, nextAt, ?_, valid⟩
  simpa [Array.toList_push, List.append_assoc] using append

theorem emitsOnly_clear_current {property : Inst → Prop} {env : LEnv}
    {before cleared captured : LS} {owner : ValueId} {origin : Option OriginId}
    (live : LiveBound before)
    (clearRun : emitEffect (.clear owner origin) env before = ((), cleared))
    (emitted : EmitsOnly property cleared captured)
    {index : BlockId} {body : BlockB}
    (current : cleared.cur = some index) (row : captured.blocks[index]? = some body) :
    ∃ head tail, body.insts.toList = head ++ (.eff (.clear owner origin) :: tail) ∧
      ∀ inst ∈ tail, property inst := by
  cases oldCurrent : before.cur with
  | none =>
    rw [emitEffect_none _ _ oldCurrent] at clearRun
    cases clearRun
    simp [oldCurrent] at current
  | some oldIndex =>
    have bound := live oldIndex oldCurrent
    let old := before.blocks[oldIndex]
    have oldAt : before.blocks[oldIndex]? = some old := by simp [old, bound]
    have sameCur : cleared.cur = some oldIndex := by
      rw [emitEffect_run _ _ oldCurrent] at clearRun
      cases clearRun
      exact oldCurrent
    have same : index = oldIndex := Option.some.inj (current.symm.trans sameCur)
    subst index
    obtain ⟨next, tail, nextAt, split, valid⟩ := emitsOnly_after_clear oldCurrent oldAt clearRun emitted
    have sameBody : next = body := Option.some.inj (nextAt.symm.trans row)
    subst next
    exact ⟨old.insts.toList, tail, split, valid⟩

theorem replacementRegion_closed_of_emission {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner : ValueId} {origin : Option OriginId}
    {env : LEnv} {before cleared captured after : LS} (live : LiveBound before)
    (clearRun : emitEffect (.clear owner origin) env before = ((), cleared))
    (emitted : EmitsOnly (ReplacementInstApart module types queries owner) cleared captured)
    (advance : cleared.Adv captured) (bounded : TargetsBounded cleared)
    (framed : IntervalEdgesFramed cleared captured after) (extension : captured.Ext after)
    (shaped : ∀ (index : BlockId) (body : BlockB), captured.blocks[index]? = some body → OpenBlock body ∨ ClosedBlock body)
    (closed : ∀ body ∈ after.blocks.toList, ClosedBlock body)
    {func : Func} (blocks : func.blocks = finishBlocks after.blocks) :
    EmptyFactsClosed module func types queries (ReplacementRegionFacts cleared captured owner) := by
  apply replacementRegion_closed advance bounded framed extension shaped closed blocks emitted.fresh
  intro index body current row
  obtain ⟨head, tail, split, valid⟩ := emitsOnly_clear_current live clearRun emitted current row
  exact ⟨head, tail, origin, split, valid⟩

end Goose.Lower.Validation
