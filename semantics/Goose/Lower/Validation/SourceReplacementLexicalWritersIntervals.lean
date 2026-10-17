import Goose.Lower.Validation.ReplacementSourceOperandBounds
import Goose.Lower.Validation.ReplacementScopedOperandsSites
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSites

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.GIR

private theorem instruction_def_member {state : LS} {index position value : Nat} {body : BlockB} {op : Op}
    (bodyAt : state.blocks[index]? = some body)
    (instructionAt : body.insts.toList[position]? = some (.def value op)) : value ∈ state.defs := by
  apply List.mem_flatMap.mpr
  refine ⟨body,Array.mem_toList_iff.mpr (Array.mem_of_getElem? bodyAt),?_⟩
  simp only [BlockB.defs,List.mem_append,List.mem_filterMap]
  exact Or.inr ⟨.def value op,List.mem_of_getElem? instructionAt,rfl⟩

theorem fresh_definition_interval {before captured : LS} {index position value : Nat}
    {body : BlockB} {op : Op}
    (initialDense : before.DenseDefinitions) (capturedDense : captured.DenseDefinitions)
    (extension : before.Ext captured)
    (bodyAt : captured.blocks[index]? = some body)
    (instructionAt : body.insts.toList[position]? = some (.def value op))
    (location : before.blocks.size ≤ index ∨
      ∃ initial, before.blocks[index]? = some initial ∧ initial.insts.size ≤ position) :
    before.vals.size ≤ value ∧ value < captured.vals.size := by
  constructor
  · by_cases inside : before.vals.size ≤ value
    · exact inside
    · exfalso
      have earlier : value < before.vals.size := Nat.lt_of_not_ge inside
      obtain ⟨initial,initialAt,earlierAt⟩ := old_instruction_site initialDense capturedDense extension bodyAt instructionAt earlier
      rcases location with newBlock | ⟨previous,previousAt,late⟩
      · exact Nat.not_lt_of_ge newBlock (Array.getElem?_eq_some_iff.mp initialAt).1
      · have same : previous = initial := Option.some.inj (previousAt.symm.trans initialAt)
        subst previous
        have bound := (List.getElem?_eq_some_iff.mp earlierAt).1
        have bound : position < initial.insts.size := by simpa using bound
        exact Nat.not_lt_of_ge late bound
  · exact List.mem_range.mp (capturedDense.subset (instruction_def_member bodyAt instructionAt))

theorem appended_instruction_captured_site {before current captured : LS} {index : Nat}
    {body : BlockB} {instruction : Inst}
    (initial : before.Ext current) (row : current.blocks[index]? = some body)
    (retained : (current.appendInst index instruction).Ext captured) :
    ∃ finalBody, captured.blocks[index]? = some finalBody ∧
      finalBody.insts.toList[body.insts.size]? = some instruction ∧
      (before.blocks.size ≤ index ∨
        ∃ initialBody, before.blocks[index]? = some initialBody ∧ initialBody.insts.size ≤ body.insts.size) := by
  have appendedRow : (current.appendInst index instruction).blocks[index]? =
      some {body with insts := body.insts.push instruction} := by
    simp [LS.appendInst,Array.getElem?_modify,row]
  obtain ⟨finalBody,finalAt,params,tail,append⟩ := retained.2 index _ appendedRow
  refine ⟨finalBody,finalAt,?_,?_⟩
  · rw [append]
    simp
  · by_cases earlier : index < before.blocks.size
    · let initialBody := before.blocks[index]
      have initialAt : before.blocks[index]? = some initialBody := by simp [initialBody,earlier]
      obtain ⟨next,nextAt,_,tail,append⟩ := initial.2 index initialBody initialAt
      have same : next = body := Option.some.inj (nextAt.symm.trans row)
      subst next
      refine Or.inr ⟨initialBody,initialAt,?_⟩
      have lengths := congrArg List.length append
      simp only [List.length_append,Array.length_toList] at lengths
      omega
    · exact Or.inl (Nat.le_of_not_gt earlier)

theorem effect_emission_captured_site {before current after captured : LS} {env : LEnv}
    {effect : Effect} {index : Nat} {body : BlockB}
    (initial : before.Ext current) (live : current.cur = some index)
    (row : current.blocks[index]? = some body)
    (run : emitEffect effect env current = ((),after)) (retained : after.Ext captured) :
    ∃ finalBody, captured.blocks[index]? = some finalBody ∧
      finalBody.insts.toList[body.insts.size]? = some (.eff effect) ∧
      (before.blocks.size ≤ index ∨
        ∃ initialBody, before.blocks[index]? = some initialBody ∧ initialBody.insts.size ≤ body.insts.size) := by
  rw [emitEffect_run effect env live] at run
  obtain ⟨_,same⟩ := Prod.mk.inj run
  subst after
  exact appended_instruction_captured_site initial row retained

theorem definition_emission_captured_site {before current after captured : LS} {env : LEnv}
    {op : Op} {value index : Nat} {body : BlockB}
    (initial : before.Ext current) (live : current.cur = some index)
    (row : current.blocks[index]? = some body)
    (run : emitDef op env current = (value,after)) (retained : after.Ext captured) :
    ∃ finalBody, captured.blocks[index]? = some finalBody ∧
      finalBody.insts.toList[body.insts.size]? = some (.def value op) ∧
      (before.blocks.size ≤ index ∨
        ∃ initialBody, before.blocks[index]? = some initialBody ∧ initialBody.insts.size ≤ body.insts.size) := by
  rw [emitDef_run op env live] at run
  obtain ⟨rfl,same⟩ := Prod.mk.inj run
  have blocks : after.blocks = (current.appendInst index (.def current.vals.size op)).blocks := by
    rw [← same]
    rfl
  have retained : (current.appendInst index (.def current.vals.size op)).Ext captured := by
    constructor
    · rw [← blocks]
      exact retained.1
    · intro block previous previousAt
      rw [← blocks] at previousAt
      exact retained.2 block previous previousAt
  exact appended_instruction_captured_site initial row retained

theorem instruction_operand_interval
    {env : PEnv} {root : DemandNode} {targets : List BlockId} {le : LEnv}
    {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {blockIndex sitePosition owner replacementValue : Nat} {origin : OriginId}
    (site : ReplacementContentFlowSource.SiteOccurrences env root targets le state func types upper
      blockIndex sitePosition owner replacementValue origin)
    (blocks : func.blocks = finishBlocks state.blocks)
    (ordered : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → ∀ input ∈ op.uses, input < value)
    {index position : Nat} {body : BlockB} {instruction : Inst}
    (bodyAt : site.source.site.source.site.captured.blocks[index]? = some body)
    (instructionAt : body.insts.toList[position]? = some instruction)
    (location : site.source.site.source.site.cleared.blocks.size ≤ index ∨
      ∃ initial, site.source.site.source.site.cleared.blocks[index]? = some initial ∧ initial.insts.size ≤ position) :
    ∀ value ∈ instruction.uses,
      site.source.site.source.site.cleared.vals.size ≤ value ∧
        value < site.source.site.source.site.captured.vals.size := by
  have emitted := lowerExpr_emitsFreshUses site.source.site.source.rhs
    site.source.site.source.site.rhsRun
  have lower := emitted.instruction_after_prefix bodyAt instructionAt location
  have capturedBounds := operands_source_lowerExpr site.source.site.source.rhs _ _ _ _
    site.source.site.source.site.rhsRun (site.cleared_operandBounds blocks ordered)
  have member : instruction ∈ site.source.site.source.site.captured.insts := by
    exact List.mem_flatMap.mpr ⟨body,Array.mem_toList_iff.mpr (Array.mem_of_getElem? bodyAt),
      List.mem_of_getElem? instructionAt⟩
  intro value used
  exact ⟨lower value used,capturedBounds.uses instruction member value used⟩

theorem call_result_interval
    {env : PEnv} {root : DemandNode} {targets : List BlockId} {le : LEnv}
    {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {blockIndex sitePosition owner replacementValue : Nat} {origin : OriginId}
    (site : ReplacementContentFlowSource.SiteOccurrences env root targets le state func types upper
      blockIndex sitePosition owner replacementValue origin)
    {index position value function : Nat} {arguments : List ValueId} {callOrigin : Option OriginId}
    {body : BlockB}
    (bodyAt : site.source.site.source.site.captured.blocks[index]? = some body)
    (instructionAt : body.insts.toList[position]? = some (.def value (.call function arguments callOrigin)))
    (location : site.source.site.source.site.cleared.blocks.size ≤ index ∨
      ∃ initial, site.source.site.source.site.cleared.blocks[index]? = some initial ∧ initial.insts.size ≤ position) :
    site.source.site.source.site.cleared.vals.size ≤ value ∧
      value < site.source.site.source.site.captured.vals.size := by
  exact fresh_definition_interval site.source.site.source.cleared_generated.dense
    site.source.site.source.captured_generated.dense
    (advB_lowerExpr _ _ _ _ _ site.source.site.source.site.rhsRun).ext bodyAt instructionAt location

theorem effect_operand_interval_of_emission
    {env : PEnv} {root : DemandNode} {targets : List BlockId} {le : LEnv}
    {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {blockIndex sitePosition owner replacementValue : Nat} {origin : OriginId}
    (site : ReplacementContentFlowSource.SiteOccurrences env root targets le state func types upper
      blockIndex sitePosition owner replacementValue origin)
    (blocks : func.blocks = finishBlocks state.blocks)
    (ordered : ∀ block ∈ func.blocks.toList, ∀ value op,
      Inst.def value op ∈ block.insts → ∀ input ∈ op.uses, input < value)
    {current after : LS} {effect : Effect} {index : Nat} {body : BlockB}
    (initial : site.source.site.source.site.cleared.Ext current)
    (live : current.cur = some index) (row : current.blocks[index]? = some body)
    (run : emitEffect effect le current = ((),after))
    (retained : after.Ext site.source.site.source.site.captured) :
    ∀ value ∈ effect.uses, site.source.site.source.site.cleared.vals.size ≤ value ∧
      value < site.source.site.source.site.captured.vals.size := by
  obtain ⟨capturedBody,capturedAt,instructionAt,location⟩ :=
    effect_emission_captured_site initial live row run retained
  exact instruction_operand_interval site blocks ordered capturedAt instructionAt location

theorem call_result_interval_of_emission
    {env : PEnv} {root : DemandNode} {targets : List BlockId} {le : LEnv}
    {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    {blockIndex sitePosition owner replacementValue : Nat} {origin : OriginId}
    (site : ReplacementContentFlowSource.SiteOccurrences env root targets le state func types upper
      blockIndex sitePosition owner replacementValue origin)
    {current after : LS} {value function index : Nat} {arguments : List ValueId}
    {callOrigin : Option OriginId} {body : BlockB}
    (initial : site.source.site.source.site.cleared.Ext current)
    (live : current.cur = some index) (row : current.blocks[index]? = some body)
    (run : emitDef (.call function arguments callOrigin) le current = (value,after))
    (retained : after.Ext site.source.site.source.site.captured) :
    site.source.site.source.site.cleared.vals.size ≤ value ∧
      value < site.source.site.source.site.captured.vals.size := by
  obtain ⟨capturedBody,capturedAt,instructionAt,location⟩ :=
    definition_emission_captured_site initial live row run retained
  exact call_result_interval site capturedAt instructionAt location

section Context

variable {module : Core.Module} {context : Context} {impl : Impl}
  {env : PEnv} {root : DemandNode} {targets : List BlockId}
  {types : Array (Option VTy)} {upper : Prov}
  {blockIndex sitePosition owner replacementValue : Nat} {origin : OriginId}
  (site : ReplacementContentFlowSource.SiteOccurrences env root targets
    (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
    (lowerContextAt module context impl) types upper blockIndex sitePosition owner replacementValue origin)

theorem context_slotInit_source_interval {current after : LS} {slot source index : Nat}
    {sourceOrigin : Option OriginId} {body : BlockB}
    (initial : site.source.site.source.site.cleared.Ext current)
    (live : current.cur = some index) (row : current.blocks[index]? = some body)
    (run : emitEffect (.slotInit slot source sourceOrigin)
      (lowerEnv module impl.vars impl.results.toList) current = ((),after))
    (retained : after.Ext site.source.site.source.site.captured) :
    site.source.site.source.site.cleared.vals.size ≤ source ∧
      source < site.source.site.source.site.captured.vals.size :=
  effect_operand_interval_of_emission site (cfg_context_blocks module context impl)
    (lowerContextAt_operand_bounds module context impl).2 initial live row run retained source
    (by simp [Effect.uses])

theorem context_store_source_interval {current after : LS} {address source index : Nat}
    {sourceOrigin : Option OriginId} {body : BlockB}
    (initial : site.source.site.source.site.cleared.Ext current)
    (live : current.cur = some index) (row : current.blocks[index]? = some body)
    (run : emitEffect (.store address source sourceOrigin)
      (lowerEnv module impl.vars impl.results.toList) current = ((),after))
    (retained : after.Ext site.source.site.source.site.captured) :
    site.source.site.source.site.cleared.vals.size ≤ source ∧
      source < site.source.site.source.site.captured.vals.size :=
  effect_operand_interval_of_emission site (cfg_context_blocks module context impl)
    (lowerContextAt_operand_bounds module context impl).2 initial live row run retained source
    (by simp [Effect.uses])

theorem context_call_result_interval {current after : LS} {value function index : Nat}
    {arguments : List ValueId} {callOrigin : Option OriginId} {body : BlockB}
    (initial : site.source.site.source.site.cleared.Ext current)
    (live : current.cur = some index) (row : current.blocks[index]? = some body)
    (run : emitDef (.call function arguments callOrigin)
      (lowerEnv module impl.vars impl.results.toList) current = (value,after))
    (retained : after.Ext site.source.site.source.site.captured) :
    site.source.site.source.site.cleared.vals.size ≤ value ∧
      value < site.source.site.source.site.captured.vals.size :=
  call_result_interval_of_emission site initial live row run retained

end Context

#print axioms fresh_definition_interval
#print axioms appended_instruction_captured_site
#print axioms effect_emission_captured_site
#print axioms definition_emission_captured_site
#print axioms instruction_operand_interval
#print axioms call_result_interval
#print axioms effect_operand_interval_of_emission
#print axioms call_result_interval_of_emission
#print axioms context_slotInit_source_interval
#print axioms context_store_source_interval
#print axioms context_call_result_interval

end Goose.Lower.Validation.SourceReplacementLexicalWriters
