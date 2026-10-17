import Goose.Lower.Validation.ReplacementEmission

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def replacementRequirements (regions : List (BlockId → List ValueId)) (block : BlockId) : List ValueId :=
  regions.flatMap (fun region => region block)

theorem replacementRequirements_contains {regions : List (BlockId → List ValueId)}
    {region : BlockId → List ValueId} (member : region ∈ regions) (block : BlockId) :
    region block ⊆ replacementRequirements regions block := by
  intro owner known
  exact List.mem_flatMap.mpr ⟨region, member, known⟩

theorem replacementRequirements_entry {regions : List (BlockId → List ValueId)}
    (entry : ∀ region ∈ regions, region 0 = []) : replacementRequirements regions 0 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro owner member
  obtain ⟨region, member, known⟩ := List.mem_flatMap.mp member
  simp [entry region member] at known

theorem replacementRequirements_closed {module : GIR.Module} {func : Func}
    {types : Array (Option VTy)} {queries : ReplacementQueries}
    {regions : List (BlockId → List ValueId)}
    (closed : ∀ region ∈ regions, EmptyFactsClosed module func types queries region) :
    EmptyFactsClosed module func types queries (replacementRequirements regions) := by
  intro source block row target args edge owner member
  obtain ⟨region, member, known⟩ := List.mem_flatMap.mp member
  have contains := transferEmptyBlock_mono module types queries block
    (replacementRequirements_contains member source)
  exact transferEmptyEdge_mono func target args contains
    (closed region member source block row target args edge known)

theorem replacementTrace_of_prefixes {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {valid : Array Bool} {facts : List ValueId} {insts : List Inst}
    (safe : ∀ head inst tail, insts = head ++ inst :: tail →
      ReplacementSafe types valid (head.foldl (transferEmptyInst module types queries) facts) inst) :
    ReplacementTrace module types queries valid facts insts := by
  induction insts generalizing facts with
  | nil => exact .nil facts
  | cons inst rest ih =>
    apply ReplacementTrace.cons
    · exact safe [] inst rest rfl
    · apply ih
      intro head next tail split
      exact safe (inst :: head) next tail (by simp [split])

theorem replacementTrace_of_regions {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {valid : Array Bool} {regions : List (BlockId → List ValueId)}
    {index : BlockId} {insts : List Inst}
    (sites : ∀ head owner run origin tail, insts = head ++ .eff (.replace owner run origin) :: tail →
      (∃ element, ownerTy types owner = some (.grow element) ∨ ownerTy types owner = some (.growshrink element)) ∧
      valid[run]? = some true ∧
      ∃ region ∈ regions, owner ∈ head.foldl (transferEmptyInst module types queries) (region index)) :
    ReplacementTrace module types queries valid (replacementRequirements regions index) insts := by
  apply replacementTrace_of_prefixes
  intro head inst tail split owner run origin same
  subst inst
  obtain ⟨ownerType, fresh, region, member, cleared⟩ := sites head owner run origin tail split
  refine ⟨ownerType, fresh, ?_⟩
  have mono := transferEmptyBlock_mono module types queries (⟨[], head⟩ : GIR.Block)
    (replacementRequirements_contains member index)
  exact mono cleared

theorem lowerContextAt_checkShrinkReplace_of_regions (module : Core.Module) (context : Core.Context)
    (impl : Core.Impl) (types : Array (Option VTy)) (provenance : Prov) (label : String)
    (regions : List (BlockId → List ValueId))
    (closed : ∀ region ∈ regions, EmptyFactsClosed (lower module) (lowerContextAt module context impl)
      types (replacementQueries (lower module) (lowerContextAt module context impl) types provenance) region)
    (entry : ∀ region ∈ regions, region 0 = [])
    (sites : ∀ (index : BlockId) (block : GIR.Block),
      (lowerContextAt module context impl).blocks[index]? = some block →
      ∀ head owner run origin tail, block.insts = head ++ .eff (.replace owner run origin) :: tail →
        (∃ element, ownerTy types owner = some (.grow element) ∨ ownerTy types owner = some (.growshrink element)) ∧
        (freshRuns (lowerContextAt module context impl) types)[run]? = some true ∧
        ∃ region ∈ regions, owner ∈ head.foldl
          (transferEmptyInst (lower module) types (replacementQueries (lower module) (lowerContextAt module context impl) types provenance))
          (region index)) :
    checkShrinkReplace (lower module) label (lowerContextAt module context impl) types provenance = .ok () := by
  apply lowerContextAt_checkShrinkReplace_of_required module context impl types provenance label
    (replacementRequirements regions) (replacementRequirements_closed closed) (replacementRequirements_entry entry)
  intro index block row
  exact replacementTrace_of_regions (sites index block row)

theorem lowerGlobal_checkShrinkReplace_of_regions (module : Core.Module) (global : Core.Global)
    (types : Array (Option VTy)) (provenance : Prov) (label : String)
    (regions : List (BlockId → List ValueId))
    (closed : ∀ region ∈ regions, EmptyFactsClosed (lower module) (lowerGlobal module global).init
      types (replacementQueries (lower module) (lowerGlobal module global).init types provenance) region)
    (entry : ∀ region ∈ regions, region 0 = [])
    (sites : ∀ (index : BlockId) (block : GIR.Block),
      (lowerGlobal module global).init.blocks[index]? = some block →
      ∀ head owner run origin tail, block.insts = head ++ .eff (.replace owner run origin) :: tail →
        (∃ element, ownerTy types owner = some (.grow element) ∨ ownerTy types owner = some (.growshrink element)) ∧
        (freshRuns (lowerGlobal module global).init types)[run]? = some true ∧
        ∃ region ∈ regions, owner ∈ head.foldl
          (transferEmptyInst (lower module) types (replacementQueries (lower module) (lowerGlobal module global).init types provenance))
          (region index)) :
    checkShrinkReplace (lower module) label (lowerGlobal module global).init types provenance = .ok () := by
  apply lowerGlobal_checkShrinkReplace_of_required module global types provenance label
    (replacementRequirements regions) (replacementRequirements_closed closed) (replacementRequirements_entry entry)
  intro index block row
  exact replacementTrace_of_regions (sites index block row)

end Goose.Lower.Validation
