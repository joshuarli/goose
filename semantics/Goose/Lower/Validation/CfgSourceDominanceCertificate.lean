import Goose.Lower.Validation.CfgSourceDominance

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Evidence

def LocalDefinitionBefore (body : GIR.Block) (value index : Nat) : Prop :=
  value ∈ body.params.map Prod.fst ∨
    ∃ prior op, prior < index ∧ body.insts[prior]? = some (.def value op)

def ImportedValues := BlockId → List ValueId

theorem predecessor_origin (func : Func) {target source : BlockId}
    (member : source ∈ (predecessors func)[target]?.getD []) :
    ∃ body, func.blocks[source]? = some body ∧ target ∈ body.terms.flatMap Term.successors := by
  let originated := fun table : Array (List BlockId) =>
    ∀ (target source : BlockId), source ∈ table[target]?.getD [] →
      ∃ body : GIR.Block, func.blocks[source]? = some body ∧ target ∈ body.terms.flatMap Term.successors
  have modify {table : Array (List BlockId)} (valid : originated table)
      (source target : BlockId) (origin : ∃ body, func.blocks[source]? = some body ∧
        target ∈ body.terms.flatMap Term.successors) :
      originated (table.modify target (source :: ·)) := by
    intro index prior present
    simp only [Array.getElem?_modify] at present
    split at present
    · rename_i same
      subst index
      cases row : table[target]? with
      | none => simp [row] at present
      | some entries =>
        simp only [row, Option.map_some, Option.getD_some, List.mem_cons] at present
        rcases present with rfl | present
        · exact origin
        · exact valid target prior (by simpa [row] using present)
    · exact valid index prior present
  have inner (source : BlockId) (body : GIR.Block) (row : func.blocks[source]? = some body)
      (targets : List BlockId) (subset : ∀ target ∈ targets, target ∈ body.terms.flatMap Term.successors)
      (table : Array (List BlockId)) (valid : originated table) :
      originated (targets.foldl (fun table target => if target < func.blocks.size then
        table.modify target (source :: ·) else table) table) := by
    induction targets generalizing table with
    | nil => exact valid
    | cons target rest ih =>
      rw [List.foldl_cons]
      apply ih (fun next member => subset next (by simp [member]))
      split
      · exact modify valid source target ⟨body, row, subset target (by simp)⟩
      · exact valid
  have outer (sources : List BlockId) (table : Array (List BlockId)) (valid : originated table) :
      originated (sources.foldl (fun table source => match func.blocks[source]? with
        | none => table
        | some body => (body.terms.flatMap Term.successors).foldl (fun table target =>
          if target < func.blocks.size then table.modify target (source :: ·) else table) table) table) := by
    induction sources generalizing table with
    | nil => exact valid
    | cons source rest ih =>
      rw [List.foldl_cons]
      apply ih
      cases row : func.blocks[source]? with
      | none => exact valid
      | some body => exact inner source body row _ (fun _ member => member) table valid
  have valid : originated (predecessors func) := by
    apply outer
    intro block prior present
    simp only [Array.getElem?_replicate] at present
    split at present <;> simp at present
  exact valid target source member

structure ImportedSSA (func : Func) (imports : ImportedValues) : Prop where
  entry : imports 0 = []
  foreign : ∀ block body, func.blocks[block]? = some body →
    ∀ value ∈ imports block, value ∉ body.defs
  operands : ∀ block (bound : block < func.blocks.size) inst index,
    (inst, index) ∈ func.blocks[block].insts.zipIdx → ∀ value ∈ inst.uses,
      value ∈ imports block ∨ LocalDefinitionBefore func.blocks[block] value index
  edges : ∀ target source body, source ∈ (predecessors func)[target]?.getD [] →
    func.blocks[source]? = some body → ∀ value ∈ imports target,
      value ∈ imports source ∨ value ∈ body.defs

theorem definitionAt_of_block_def {func : Func} {body : GIR.Block} {block value : Nat}
    (row : func.blocks[block]? = some body) (defined : value ∈ body.defs) :
    ∃ position, DefinitionAt func value block position := by
  rw [← definitionLocations_ids body block] at defined
  obtain ⟨⟨result, defining, position⟩, member, same⟩ := List.mem_map.mp defined
  change result = value at same
  subst result
  have own : defining = block := by
    simp only [Block.definitionLocations, List.mem_append] at member
    rcases member with parameter | instruction
    · obtain ⟨param, _, equal⟩ := List.mem_map.mp parameter
      exact congrArg (fun entry => entry.2.1) equal |>.symm
    · obtain ⟨⟨inst, index⟩, _, equal⟩ := List.mem_filterMap.mp instruction
      cases inst <;> simp_all
  subst defining
  refine ⟨position, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨(body, block), ?_, member⟩
  exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using row)

theorem definitionAt_block_def {func : Func} {value block : Nat} {position : Int}
    (site : DefinitionAt func value block position) :
    ∃ body, func.blocks[block]? = some body ∧ value ∈ body.defs := by
  obtain ⟨⟨body, defining⟩, blockMember, member⟩ := List.mem_flatMap.mp site
  have row := List.mk_mem_zipIdx_iff_getElem?.mp blockMember
  have own : defining = block := by
    simp only [Block.definitionLocations, List.mem_append] at member
    rcases member with parameter | instruction
    · obtain ⟨param, _, equal⟩ := List.mem_map.mp parameter
      exact congrArg (fun entry => entry.2.1) equal
    · obtain ⟨⟨inst, index⟩, _, equal⟩ := List.mem_filterMap.mp instruction
      cases inst <;> simp_all
  subst defining
  refine ⟨body, by simpa using row, ?_⟩
  rw [← definitionLocations_ids body block]
  exact List.mem_map.mpr ⟨(value, (block, position)), member, rfl⟩

theorem LocalDefinitionBefore.finished {func : Func} {body : GIR.Block}
    {value block index : Nat} (before : LocalDefinitionBefore body value index)
    (row : func.blocks[block]? = some body) : DefinitionBefore func value block index := by
  rcases before with parameter | ⟨prior, op, order, instruction⟩
  · exact definitionBefore_param row parameter
  · exact definitionBefore_def row instruction order

theorem ImportedSSA.region {func : Func} {imports : ImportedValues}
    (certificate : ImportedSSA func imports)
    (unique : (func.blocks.toList.flatMap GIR.Block.defs).Nodup)
    {value parent : Nat} {position : Int} (site : DefinitionAt func value parent position) :
    DominanceRegion (predecessors func) func.blocks.size parent
      (fun block => value ∈ imports block ∨ block = parent) := by
  obtain ⟨parentBody, parentRow, _⟩ := definitionAt_block_def site
  refine ⟨(Array.getElem?_eq_some_iff.mp parentRow).1, ?_, ?_⟩
  · intro member
    rcases member with imported | equal
    · simp [certificate.entry] at imported
    · exact equal.symm
  · intro block prior member different predecessor
    have imported : value ∈ imports block := member.resolve_right different
    have bound := predecessors_bounded func block prior predecessor
    have row : func.blocks[prior]? = some func.blocks[prior] := Array.getElem?_eq_getElem bound
    rcases certificate.edges block prior _ predecessor row value imported with inherited | defined
    · exact Or.inl inherited
    · obtain ⟨priorPosition, priorSite⟩ := definitionAt_of_block_def row defined
      exact Or.inr (congrArg Prod.fst (definitionAt_unique unique priorSite site))

theorem ImportedSSA.dominatingUses {func : Func} {imports : ImportedValues}
    (certificate : ImportedSSA func imports)
    (unique : (func.blocks.toList.flatMap GIR.Block.defs).Nodup)
    (complete : ∀ value, value < func.numValues → ∃ block position, DefinitionAt func value block position)
    (bounded : ∀ block (bound : block < func.blocks.size) inst index,
      (inst, index) ∈ func.blocks[block].insts.zipIdx →
      ∀ value ∈ inst.uses, value < func.numValues) : DominatingUses func := by
  intro block bound inst index instruction value operand
  have valueBound := bounded block bound inst index instruction value operand
  have row : func.blocks[block]? = some func.blocks[block] := Array.getElem?_eq_getElem bound
  rcases certificate.operands block bound inst index instruction value operand with imported | localBefore
  · obtain ⟨parent, position, site⟩ := complete value valueBound
    have different : parent ≠ block := by
      intro same
      subst parent
      obtain ⟨body, bodyRow, defined⟩ := definitionAt_block_def site
      exact certificate.foreign block body bodyRow value imported defined
    refine ⟨parent, position, cfgDefAt_of_unique_location unique valueBound site, ?_⟩
    simpa only [different, ite_false] using
      (certificate.region unique site).dominates bound (Or.inl imported)
  · obtain ⟨position, site, order⟩ := localBefore.finished row
    exact ⟨block, position, cfgDefAt_of_unique_location unique valueBound site,
      by simpa using order⟩

theorem ImportedSSA.checked {func : Func} {imports : ImportedValues}
    (certificate : ImportedSSA func imports)
    (unique : (func.blocks.toList.flatMap GIR.Block.defs).Nodup)
    (complete : ∀ value, value < func.numValues → ∃ block position, DefinitionAt func value block position)
    (bounded : ∀ block (bound : block < func.blocks.size) inst index,
      (inst, index) ∈ func.blocks[block].insts.zipIdx →
      ∀ value ∈ inst.uses, value < func.numValues) (label : String) :
    cfgUseScan label func = .ok () :=
  dominatingUses_checked func (certificate.dominatingUses unique complete bounded) label

end Goose.Lower.Validation
