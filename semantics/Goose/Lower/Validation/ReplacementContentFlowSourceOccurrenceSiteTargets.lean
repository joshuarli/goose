import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSites

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR

variable {env other : PEnv} {root : DemandNode} {targets : List BlockId}
  {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
  {block position owner value : Nat} {origin : OriginId}

def SiteOccurrences.weaken {fewer : List BlockId}
    (site : SiteOccurrences env root targets le state func types upper block position owner value origin)
    (included : ∀ target ∈ fewer, target ∈ targets) :
    SiteOccurrences env root fewer le state func types upper block position owner value origin :=
  { site with source := site.source.weaken included }

def SiteOccurrences.reserve
    (site : SiteOccurrences env root targets le state func types upper block position owner value origin)
    (target : BlockId) (fresh : state.blocks.size ≤ target) :
    SiteOccurrences env root (target :: targets) le state func types upper block position owner value origin :=
  { site with source := site.source.reserve target fresh }

def SiteOccurrences.access_eq
    (site : SiteOccurrences env root targets le state func types upper block position owner value origin)
    (same : env.access = other.access) :
    SiteOccurrences other root targets le state func types upper block position owner value origin :=
  { site with access := site.access.trans same }

theorem SiteAuthority.weaken {fewer : List BlockId} {inst : Inst}
    (valid : SiteAuthority env root targets le state func types upper block position inst)
    (included : ∀ target ∈ fewer, target ∈ targets) :
    SiteAuthority env root fewer le state func types upper block position inst := by
  cases inst with
  | eff effect =>
    cases effect <;> try exact valid
    case replace owner value origin =>
      cases origin with
      | none => exact valid
      | some origin => obtain ⟨site⟩ := valid; exact ⟨site.weaken included⟩
  | _ => exact valid

theorem SiteAuthority.reserve {inst : Inst}
    (valid : SiteAuthority env root targets le state func types upper block position inst)
    (target : BlockId) (fresh : state.blocks.size ≤ target) :
    SiteAuthority env root (target :: targets) le state func types upper block position inst := by
  cases inst with
  | eff effect =>
    cases effect <;> try exact valid
    case replace owner value origin =>
      cases origin with
      | none => exact valid
      | some origin => obtain ⟨site⟩ := valid; exact ⟨site.reserve target fresh⟩
  | _ => exact valid

theorem SiteAuthority.access_eq {inst : Inst}
    (valid : SiteAuthority env root targets le state func types upper block position inst)
    (same : env.access = other.access) :
    SiteAuthority other root targets le state func types upper block position inst := by
  cases inst with
  | eff effect =>
    cases effect <;> try exact valid
    case replace owner value origin =>
      cases origin with
      | none => exact valid
      | some origin => obtain ⟨site⟩ := valid; exact ⟨site.access_eq same⟩
  | _ => exact valid

theorem OccurrenceSitesBuilder.weaken {fewer : List BlockId}
    (checked : OccurrenceSitesBuilder env root targets le state func types upper)
    (included : ∀ target ∈ fewer, target ∈ targets) :
    OccurrenceSitesBuilder env root fewer le state func types upper :=
  fun block body row position inst lookup => (checked block body row position inst lookup).weaken included

theorem OccurrenceSitesBuilder.reserve
    (checked : OccurrenceSitesBuilder env root targets le state func types upper)
    (target : BlockId) (fresh : state.blocks.size ≤ target) :
    OccurrenceSitesBuilder env root (target :: targets) le state func types upper :=
  fun block body row position inst lookup => (checked block body row position inst lookup).reserve target fresh

theorem OccurrenceSitesBuilder.access_eq
    (checked : OccurrenceSitesBuilder env root targets le state func types upper)
    (same : env.access = other.access) :
    OccurrenceSitesBuilder other root targets le state func types upper :=
  fun block body row position inst lookup => (checked block body row position inst lookup).access_eq same

theorem OccurrenceSitesBuilder.of_notReplacement
    (absent : ∀ (block : Nat) (body : BlockB), state.blocks[block]? = some body → ∀ (position : Nat) (inst : Inst),
      body.insts[position]? = some inst → NotReplacement inst) :
    OccurrenceSitesBuilder env root targets le state func types upper := by
  intro block body row position inst lookup
  have valid := absent block body row position inst lookup
  cases inst with
  | eff effect => cases effect <;> first | exact True.intro | exact False.elim valid
  | _ => exact True.intro

#print axioms OccurrenceSitesBuilder.weaken
#print axioms OccurrenceSitesBuilder.reserve
#print axioms OccurrenceSitesBuilder.access_eq
#print axioms OccurrenceSitesBuilder.of_notReplacement

end Goose.Lower.Validation.ReplacementContentFlowSource
