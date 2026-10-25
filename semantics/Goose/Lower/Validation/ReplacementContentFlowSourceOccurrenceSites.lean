import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrencePaths
import Goose.Lower.Validation.ReplacementSourceSitesBuilder

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

structure SiteOccurrences (env : PEnv) (root : DemandNode) (targets : List BlockId)
    (le : LEnv) (state : LS) (func : Func) (types : Array (Option VTy)) (upper : Prov)
    (block position owner value : Nat) (origin : OriginId) where
  source : ReservedReplacementSiteAt root targets le state block position owner value origin
  localEnv : PEnv
  access : localEnv.access = env.access
  before : RState
  ownerRoots : List RootRef
  addressed : RState
  ownerReplay : rpPlace localEnv source.site.source.place before = .ok (ownerRoots, addressed)
  ownerBound : owner < upper.vals.size
  ownerRefined : GIR.RootsRefine func (rootsAt upper.vals owner) ownerRoots
  rhs : OccurrenceLedger localEnv (.expression source.site.source.rhs) func types upper
    source.site.source.site.cleared source.site.source.site.captured
  clearedOperandUses : ∀ inst ∈ source.site.source.site.cleared.insts, ∀ input ∈ inst.uses,
    input < source.site.source.site.cleared.vals.size

def SiteOccurrences.retained {env : PEnv} {root : DemandNode} {targets : List BlockId}
    {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)}
    {old next : Prov} {block position owner value : Nat} {origin : OriginId}
    (site : SiteOccurrences env root targets le before func types old block position owner value origin)
    (extension : before.Ext after) (typePrefix : TypePrefix before after)
    (intervals : ReplacementIntervalsPreserved targets before after)
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    SiteOccurrences env root targets le after func types next block position owner value origin where
  source := site.source.retained extension typePrefix intervals
  localEnv := site.localEnv
  access := site.access
  before := site.before
  ownerRoots := site.ownerRoots
  addressed := site.addressed
  ownerReplay := site.ownerReplay
  ownerBound := Nat.lt_of_lt_of_le site.ownerBound growth
  ownerRefined := by rw [retained owner site.ownerBound]; exact site.ownerRefined
  rhs := site.rhs.retained growth retained
  clearedOperandUses := site.clearedOperandUses

def SiteAuthority (env : PEnv) (root : DemandNode) (targets : List BlockId)
    (le : LEnv) (state : LS) (func : Func) (types : Array (Option VTy)) (upper : Prov)
    (block position : Nat) : Inst → Prop
  | .eff (.replace owner value (some origin)) =>
      Nonempty (SiteOccurrences env root targets le state func types upper block position owner value origin)
  | .eff (.replace _ _ none) => False
  | _ => True

def OccurrenceSitesBuilder (env : PEnv) (root : DemandNode) (targets : List BlockId)
    (le : LEnv) (state : LS) (func : Func) (types : Array (Option VTy)) (upper : Prov) : Prop :=
  ∀ block body, state.blocks[block]? = some body → ∀ position instruction,
    body.insts[position]? = some instruction →
      SiteAuthority env root targets le state func types upper block position instruction

variable {env : PEnv} {root : DemandNode} {targets : List BlockId}
  {le : LEnv} {before after : LS} {func : Func} {types : Array (Option VTy)} {old next : Prov}

theorem SiteAuthority.retained {block position : Nat} {inst : Inst}
    (valid : SiteAuthority env root targets le before func types old block position inst)
    (extension : before.Ext after) (typePrefix : TypePrefix before after)
    (preserved : ReplacementIntervalsPreserved targets before after)
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    SiteAuthority env root targets le after func types next block position inst := by
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

theorem OccurrenceSitesBuilder.of_emits
    (checked : OccurrenceSitesBuilder env root targets le before func types old)
    (emitted : EmitsOnly NotReplacement before after) (typePrefix : TypePrefix before after)
    (preserved : ReplacementIntervalsPreserved targets before after)
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    OccurrenceSitesBuilder env root targets le after func types next := by
  intro block body row position instruction lookup
  have contradictionOfFresh : NotReplacement instruction →
      SiteAuthority env root targets le after func types next block position instruction := by
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

theorem OccurrenceSitesBuilder.emitDef {result : ValueId} {op : Op}
    (checked : OccurrenceSitesBuilder env root targets le before func types old)
    (run : emitDef op le before = (result, after))
    (growth : old.vals.size ≤ next.vals.size)
    (retained : ∀ index, index < old.vals.size → rootsAt next.vals index = rootsAt old.vals index) :
    OccurrenceSitesBuilder env root targets le after func types next :=
  checked.of_emits (emitsOnly_emitDef run trivial) (types_emitDef op le before result after run)
    (.of_run (generatedTargetFrame_emitDef none op) run) growth retained

#print axioms OccurrenceSitesBuilder.of_emits
#print axioms OccurrenceSitesBuilder.emitDef

#print axioms SiteOccurrences.retained

end Goose.Lower.Validation.ReplacementContentFlowSource
