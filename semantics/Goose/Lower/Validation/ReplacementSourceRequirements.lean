import Goose.Lower.Validation.ReplacementSourceSiteCheck

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

noncomputable def replacementSourceRequirements (le : LEnv) (state : LS) (module : GIR.Module)
    (types : Array (Option VTy)) (queries : ReplacementQueries) (block : BlockId) : List ValueId := by
  classical
  exact (List.range state.vals.size).filter fun owner =>
    ∃ value origin, ∃ site : AcceptedReplacementSite le state owner value origin,
      EmitsOnly (ReplacementInstApart module types queries owner) site.site.cleared site.site.captured ∧
      owner ∈ ReplacementRegionFacts site.site.cleared site.site.captured owner block

theorem replacementRegionFacts_member {before captured : LS} {owner value : ValueId} {block : BlockId}
    (member : value ∈ ReplacementRegionFacts before captured owner block) : value = owner := by
  unfold ReplacementRegionFacts at member
  split at member <;> simp_all

theorem replacementSourceRequirements_contains {le : LEnv} {state : LS}
    {module : GIR.Module} {types : Array (Option VTy)} {queries : ReplacementQueries}
    {owner value : ValueId} {origin : OriginId}
    (site : AcceptedReplacementSite le state owner value origin)
    (apart : EmitsOnly (ReplacementInstApart module types queries owner) site.site.cleared site.site.captured)
    (bounded : owner < state.vals.size) (block : BlockId) :
    ReplacementRegionFacts site.site.cleared site.site.captured owner block ⊆
      replacementSourceRequirements le state module types queries block := by
  classical
  intro other member
  have same := replacementRegionFacts_member member
  subst other
  exact List.mem_filter.mpr ⟨List.mem_range.mpr bounded, by
    simpa only [decide_eq_true_eq] using (show ∃ value origin, ∃ witness : AcceptedReplacementSite le state owner value origin,
      EmitsOnly (ReplacementInstApart module types queries owner) witness.site.cleared witness.site.captured ∧
      owner ∈ ReplacementRegionFacts witness.site.cleared witness.site.captured owner block from
        ⟨value, origin, site, apart, member⟩)⟩

theorem AcceptedReplacementSite.region_entry {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (site : AcceptedReplacementSite le state owner value origin) :
    ReplacementRegionFacts site.site.cleared site.site.captured owner 0 = [] := by
  have live := (dead_lowerExpr site.rhs).live_before site.site.rhsRun site.live
  cases current : site.site.cleared.cur with
  | none => simp [current] at live
  | some index =>
    exact replacementRegionFacts_entry (Nat.zero_lt_of_lt (site.cleared_generated.live index current))

theorem replacementSourceRequirements_entry (le : LEnv) (state : LS) (module : GIR.Module)
    (types : Array (Option VTy)) (queries : ReplacementQueries) :
    replacementSourceRequirements le state module types queries 0 = [] := by
  classical
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro owner member
  obtain ⟨_, known⟩ := List.mem_filter.mp member
  obtain ⟨value, origin, site, _, impossible⟩ := of_decide_eq_true known
  simpa only [site.region_entry, List.not_mem_nil] using impossible

theorem replacementSourceRequirements_closed {le : LEnv} {state : LS}
    {module : GIR.Module} {func : Func} {types : Array (Option VTy)} {queries : ReplacementQueries}
    (closed : ∀ body ∈ state.blocks.toList, ClosedBlock body)
    (blocks : func.blocks = finishBlocks state.blocks) :
    EmptyFactsClosed module func types queries (replacementSourceRequirements le state module types queries) := by
  classical
  intro source body row target args edge owner required
  obtain ⟨bounded, known⟩ := List.mem_filter.mp required
  obtain ⟨value, origin, site, apart, member⟩ := of_decide_eq_true known
  have carried := site.region_closed apart closed blocks source body row target args edge member
  exact transferEmptyEdge_mono func target args
    (transferEmptyBlock_mono module types queries body
      (replacementSourceRequirements_contains site apart (List.mem_range.mp bounded) source)) carried

theorem AcceptedReplacementSite.owner_bound {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (site : AcceptedReplacementSite le state owner value origin)
    {module : GIR.Module} {func : Func}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks) (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
    (structs : module.structs = le.mod.structs) (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state)
    (closed : ∀ body ∈ state.blocks.toList, ClosedBlock body) : owner < state.vals.size := by
  obtain ⟨⟨element, ownerType | ownerType⟩, _⟩ :=
    site.owner_fresh builder blocks slots globals sigs structs profile graphs closed
  all_goals
    have retained := valueTypes_eq_retained_of_source_graphs builder blocks slots globals sigs structs profile graphs
    by_cases bounded : owner < state.vals.size
    · exact bounded
    · have absent : state.vals[owner]? = none := Array.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt bounded)
      simp only [ownerTy, retained, absent] at ownerType
      contradiction

theorem ReplacementSiteAt.source_prefix_cleared {le : LEnv} {state : LS}
    {index position owner value : Nat} {origin : OriginId}
    (witness : ReplacementSiteAt le state index position owner value origin)
    {module : GIR.Module} {func : Func} {types : Array (Option VTy)} {queries : ReplacementQueries}
    (apart : EmitsOnly (ReplacementInstApart module types queries owner)
      witness.source.site.cleared witness.source.site.captured)
    (bounded : owner < state.vals.size)
    (blocks : func.blocks = finishBlocks state.blocks)
    {body : GIR.Block} (row : func.blocks[index]? = some body)
    {head tail : List Inst}
    (split : body.insts = head ++ .eff (.replace owner value (some origin)) :: tail)
    (positionAt : head.length = position) :
    owner ∈ head.foldl (transferEmptyInst module types queries)
      (replacementSourceRequirements le state module types queries index) :=
  transferEmptyBlock_mono module types queries (⟨[], head⟩ : GIR.Block)
    (replacementSourceRequirements_contains witness.source apart bounded index)
    (witness.prefix_cleared apart blocks row split positionAt)

#print axioms replacementSourceRequirements_contains
#print axioms replacementSourceRequirements_entry
#print axioms replacementSourceRequirements_closed
#print axioms AcceptedReplacementSite.owner_bound
#print axioms ReplacementSiteAt.source_prefix_cleared

end Goose.Lower.Validation
