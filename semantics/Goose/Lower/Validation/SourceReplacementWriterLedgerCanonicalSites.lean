import Goose.Lower.Validation.SourceReplacementWriterLedger
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSitePublish

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR ReplacementContentFlowSource

structure CanonicalSiteOccurrences (ownerRoot : Fragment) (ownerInitial baseline : LS)
    (env : PEnv) (root : DemandNode) (targets : List BlockId)
    (le : LEnv) (state : LS) (func : Func) (types : Array (Option VTy)) (upper : Prov)
    (block position owner value : Nat) (origin : OriginId) where
  site : SiteOccurrences env root targets le state func types upper block position owner value origin
  source : (∃ body, baseline.blocks[block]? = some body ∧
      body.insts[position]? = some (.eff (.replace owner value (some origin)))) ∨
    ∃ path loop, SourceLoweringAt ownerRoot le ownerInitial path
      (.statement loop (.assignWhole site.source.site.source.place site.source.site.source.rhs origin))
      site.source.site.source.initial

def CanonicalSiteOccurrences.retained {ownerRoot : Fragment} {ownerInitial baseline : LS}
    {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)}
    {old next : Prov} {block position owner value : Nat} {origin : OriginId}
    (source : CanonicalSiteOccurrences ownerRoot ownerInitial baseline env root targets le before func types old
      block position owner value origin)
    (extension : before.Ext after) (typePrefix : TypePrefix before after)
    (intervals : ReplacementIntervalsPreserved targets before after)
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    CanonicalSiteOccurrences ownerRoot ownerInitial baseline env root targets le after func types next
      block position owner value origin where
  site := source.site.retained extension typePrefix intervals growth retained
  source := source.source

def CanonicalSiteAuthority (ownerRoot : Fragment) (ownerInitial baseline : LS)
    (env : PEnv) (root : DemandNode) (targets : List BlockId)
    (le : LEnv) (state : LS) (func : Func) (types : Array (Option VTy)) (upper : Prov)
    (block position : Nat) : Inst → Prop
  | .eff (.replace owner value (some origin)) =>
      Nonempty (CanonicalSiteOccurrences ownerRoot ownerInitial baseline env root targets le state
        func types upper block position owner value origin)
  | .eff (.replace _ _ none) => False
  | _ => True

def CanonicalOccurrenceSitesBuilder (ownerRoot : Fragment) (ownerInitial baseline : LS)
    (env : PEnv) (root : DemandNode) (targets : List BlockId)
    (le : LEnv) (state : LS) (func : Func) (types : Array (Option VTy)) (upper : Prov) : Prop :=
  ∀ block body, state.blocks[block]? = some body → ∀ position instruction,
    body.insts[position]? = some instruction →
      CanonicalSiteAuthority ownerRoot ownerInitial baseline env root targets le state func types upper block position instruction

theorem CanonicalOccurrenceSitesBuilder.toOld {ownerRoot : Fragment} {ownerInitial baseline : LS}
    {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le state func types upper) :
    OccurrenceSitesBuilder env root targets le state func types upper := by
  intro block body row position instruction lookup
  have known := checked block body row position instruction lookup
  cases instruction with
  | eff effect =>
    cases effect <;> try exact known
    case replace owner value origin =>
      cases origin with
      | none => exact known
      | some origin => obtain ⟨source⟩ := known; exact ⟨source.site⟩
  | _ => exact known

theorem CanonicalOccurrenceSitesBuilder.initial {ownerRoot : Fragment} {ownerInitial initial : LS}
    {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (checked : OccurrenceSitesBuilder env root targets le initial func types upper) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial initial env root targets le initial func types upper := by
  intro block body row position instruction lookup
  have known := checked block body row position instruction lookup
  cases instruction with
  | eff effect =>
    cases effect <;> try exact known
    case replace owner value origin =>
      cases origin with
      | none => exact known
      | some origin =>
        obtain ⟨source⟩ := known
        exact ⟨⟨source,Or.inl ⟨body,row,lookup⟩⟩⟩
  | _ => exact known

variable {ownerRoot : Fragment} {ownerInitial baseline : LS} {env : PEnv} {root : DemandNode} {targets : List BlockId}
  {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)} {old next : Prov}

theorem CanonicalSiteAuthority.retained {block position : Nat} {inst : Inst}
    (valid : CanonicalSiteAuthority ownerRoot ownerInitial baseline env root targets le before func types old block position inst)
    (extension : before.Ext after) (typePrefix : TypePrefix before after)
    (preserved : ReplacementIntervalsPreserved targets before after)
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    CanonicalSiteAuthority ownerRoot ownerInitial baseline env root targets le after func types next block position inst := by
  cases inst with
  | eff effect =>
    cases effect <;> try exact valid
    case replace owner value origin =>
      cases origin with
      | none => exact valid
      | some origin =>
        obtain ⟨site⟩ := valid
        exact ⟨site.retained extension typePrefix preserved growth retained⟩
  | _ => exact valid

theorem CanonicalOccurrenceSitesBuilder.of_emits
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (emitted : EmitsOnly NotReplacement before after) (typePrefix : TypePrefix before after)
    (preserved : ReplacementIntervalsPreserved targets before after)
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le after func types next := by
  intro block body row position instruction lookup
  have contradictionOfFresh : NotReplacement instruction →
      CanonicalSiteAuthority ownerRoot ownerInitial baseline env root targets le after func types next block position instruction := by
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
      exact (checked block previous previousRow position instruction prior).retained emitted.extension typePrefix preserved growth retained
    · apply contradictionOfFresh
      apply valid instruction
      have tailLookup : tail[position - previous.insts.size]? = some instruction := by
        simpa [earlier] using listLookup
      exact List.mem_of_getElem? tailLookup
  · apply contradictionOfFresh
    exact emitted.fresh block body row (Nat.le_of_not_gt old) instruction
      (by exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))

theorem CanonicalOccurrenceSitesBuilder.emitDef {result : ValueId} {op : Op}
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (run : emitDef op le before = (result, after))
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le after func types next :=
  checked.of_emits (emitsOnly_emitDef run trivial) (types_emitDef op le before result after run)
    (.of_run (generatedTargetFrame_emitDef none op) run) growth retained

theorem CanonicalOccurrenceSitesBuilder.emitReplacement {ownerRoot : Fragment} {ownerInitial baseline : LS} {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)} {old next : Prov}
    {owner value : ValueId} {origin : OriginId}
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (run : Goose.Lower.emitEffect (.replace owner value (some origin)) le before = ((), after))
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index)
    (source : ∀ block body, before.cur = some block → before.blocks[block]? = some body →
      Nonempty (CanonicalSiteOccurrences ownerRoot ownerInitial baseline env root targets le after func types next block body.insts.size owner value origin)) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le after func types next := by
  have extension := (advB_emitEffect (.replace owner value (some origin)) le before () after run).ext
  have preserved : ReplacementIntervalsPreserved targets before after :=
    .of_run (generatedTargetFrame_emitEffect none _) run
  have typePrefix := types_emitEffect (.replace owner value (some origin)) le before () after run
  cases current : before.cur with
  | none =>
    rw [emitEffect_none _ _ current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    intro block body row position inst lookup
    exact (checked block body row position inst lookup).retained (.refl before) (.refl before)
      (fun _ _ _ _ framed => framed) growth retained
  | some index =>
    rw [emitEffect_run _ _ current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    intro block body row position instruction lookup
    change (before.blocks.modify index (fun body =>
      { body with insts := body.insts.push (.eff (.replace owner value (some origin))) }))[block]? = some body at row
    rw [Array.getElem?_modify] at row
    by_cases same : index = block
    · subst block
      simp only [ite_true] at row
      cases oldRow : before.blocks[index]? with
      | none => simp [oldRow] at row
      | some previous =>
        simp only [oldRow, Option.map_some, Option.some.injEq] at row
        subst body
        change (previous.insts.push (.eff (.replace owner value (some origin))))[position]? = some instruction at lookup
        by_cases fresh : position = previous.insts.size
        · subst position
          simp only [Array.getElem?_push_eq, Option.some.injEq] at lookup
          subst instruction
          exact source index previous current oldRow
        · rw [Array.getElem?_push, if_neg fresh] at lookup
          exact (checked index previous oldRow position instruction lookup).retained extension typePrefix preserved growth retained
    · simp only [same, ite_false] at row
      exact (checked block body row position instruction lookup).retained extension typePrefix preserved growth retained

theorem CanonicalOccurrenceSitesBuilder.mutationEffect {ownerRoot : Fragment} {ownerInitial baseline : LS} {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)} {old next : Prov}
    {result : Unit} {effect : Effect}
    (checked : CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le before func types old)
    (notReplacement : NotReplacement (.eff effect))
    (run : emitEffect effect le before = (result, after))
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    CanonicalOccurrenceSitesBuilder ownerRoot ownerInitial baseline env root targets le after func types next :=
  checked.of_emits (emitsOnly_emitEffect effect notReplacement le before result after run)
    (types_emitEffect effect le before result after run)
    (.of_run (generatedTargetFrame_emitEffect none effect) run) growth retained

#print axioms CanonicalOccurrenceSitesBuilder.of_emits
#print axioms CanonicalOccurrenceSitesBuilder.emitReplacement
#print axioms CanonicalSiteOccurrences.retained
#print axioms CanonicalOccurrenceSitesBuilder.toOld
#print axioms CanonicalOccurrenceSitesBuilder.initial

end Goose.Lower.Validation.SourceReplacementWriterLedger
