import Goose.Lower.Validation.CfgUseDominance
import Goose.Lower.Validation.CfgTerminators

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Evidence

structure DominanceRegion (preds : Array (List BlockId)) (size parent : Nat)
    (contains : BlockId → Prop) : Prop where
  parentBound : parent < size
  entry : contains 0 → parent = 0
  predecessor : ∀ block prior, contains block → block ≠ parent →
    prior ∈ preds[block]?.getD [] → contains prior

theorem DominanceRegion.dominates {preds : Array (List BlockId)} {size parent : Nat}
    {contains : BlockId → Prop} (region : DominanceRegion preds size parent contains)
    {block : BlockId} (bound : block < size) (member : contains block) :
    PathDominates preds size block parent := by
  refine ⟨bound, region.parentBound, ?_⟩
  intro length walk
  have impossible : ∀ {length block}, PredWalk preds size parent length block →
      contains block → False := by
    intro length block path
    induction path with
    | entry _ avoids =>
      intro inside
      exact avoids (region.entry inside).symm
    | @next length prior block path _ avoids edge ih =>
      intro inside
      exact ih (region.predecessor block prior inside avoids edge)
  exact impossible walk member

theorem DominanceRegion.inter {preds : Array (List BlockId)} {size parent : Nat}
    {left right : BlockId → Prop}
    (one : DominanceRegion preds size parent left)
    (two : DominanceRegion preds size parent right) :
    DominanceRegion preds size parent (fun block => left block ∧ right block) := by
  refine ⟨one.parentBound, fun member => one.entry member.1, ?_⟩
  intro block prior member different edge
  exact ⟨one.predecessor block prior member.1 different edge,
    two.predecessor block prior member.2 different edge⟩

def DefinitionAt (func : Func) (value : ValueId) (block : BlockId) (position : Int) : Prop :=
  (value, (block, position)) ∈ func.definitionLocations

def DefinitionBefore (func : Func) (value : ValueId) (block : BlockId) (index : Nat) : Prop :=
  ∃ position, DefinitionAt func value block position ∧ position < (index : Int)

theorem definitionBefore_param {func : Func} {block : GIR.Block} {id value index : Nat}
    (row : func.blocks[id]? = some block) (parameter : value ∈ block.params.map Prod.fst) :
    DefinitionBefore func value id index := by
  exact ⟨-1, parameterLocation_mem row parameter, by omega⟩

theorem definitionBefore_def {func : Func} {block : GIR.Block} {id value prior index : Nat}
    {op : Op} (row : func.blocks[id]? = some block)
    (instruction : block.insts[prior]? = some (.def value op)) (order : prior < index) :
    DefinitionBefore func value id index := by
  refine ⟨(prior : Int), ?_, by omega⟩
  exact definitionLocation_mem (fn := func) (pt := (id, prior))
    (by simp only [instAt, row, Option.bind_some]; exact instruction)

theorem definitionBefore_mono {func : Func} {value block before after : Nat}
    (available : DefinitionBefore func value block before) (order : before ≤ after) :
    DefinitionBefore func value block after := by
  obtain ⟨position, site, earlier⟩ := available
  exact ⟨position, site, by omega⟩

theorem definitionAt_unique {func : Func}
    (unique : (func.blocks.toList.flatMap GIR.Block.defs).Nodup)
    {value leftBlock rightBlock : Nat} {leftPosition rightPosition : Int}
    (left : DefinitionAt func value leftBlock leftPosition)
    (right : DefinitionAt func value rightBlock rightPosition) :
    (leftBlock, leftPosition) = (rightBlock, rightPosition) := by
  rw [← definitionLocations_ids_func] at unique
  exact congrArg Prod.snd (entry_eq_of_nodup_ids unique left right rfl)

def writeDefinition (table : Array (Option (BlockId × Int)))
    (entry : ValueId × (BlockId × Int)) : Array (Option (BlockId × Int)) :=
  table.set! entry.1 (some entry.2)

theorem cfgDefAt_eq_locations (func : Func) :
    cfgDefAt func = func.definitionLocations.foldl writeDefinition
      (Array.replicate func.numValues none) := by
  unfold cfgDefAt Func.definitionLocations
  rw [← Array.foldl_toList, Array.toList_zipIdx, List.foldl_flatMap]
  congr 1
  funext table pair
  simp only [Block.definitionLocations, List.foldl_append, List.foldl_map,
    List.foldl_filterMap]
  congr 1
  funext acc instruction
  rcases instruction with ⟨inst, index⟩
  cases inst <;> rfl

theorem writeDefinition_size (table : Array (Option (BlockId × Int)))
    (entry : ValueId × (BlockId × Int)) : (writeDefinition table entry).size = table.size := by
  simp [writeDefinition]

theorem writeDefinition_lookup {table : Array (Option (BlockId × Int))}
    {value : ValueId} {site : BlockId × Int}
    (known : table[value]? = some (some site)) (entry : ValueId × (BlockId × Int))
    (agrees : entry.1 = value → entry.2 = site) :
    (writeDefinition table entry)[value]? = some (some site) := by
  by_cases same : entry.1 = value
  · have bound : value < table.size := (Array.getElem?_eq_some_iff.mp known).1
    simp [writeDefinition, Array.set!_eq_setIfInBounds, same, agrees same,
      Array.getElem?_setIfInBounds_self_of_lt bound]
  · simpa [writeDefinition, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne same] using known

theorem writeDefinitions_lookup {table : Array (Option (BlockId × Int))}
    {value : ValueId} {site : BlockId × Int}
    (known : table[value]? = some (some site)) (entries : List (ValueId × (BlockId × Int)))
    (agrees : ∀ entry ∈ entries, entry.1 = value → entry.2 = site) :
    (entries.foldl writeDefinition table)[value]? = some (some site) := by
  induction entries generalizing table with
  | nil => exact known
  | cons entry rest ih =>
    exact ih (writeDefinition_lookup known entry (agrees entry (by simp)))
      (fun next member => agrees next (by simp [member]))

theorem writeDefinitions_contains {entries : List (ValueId × (BlockId × Int))}
    {table : Array (Option (BlockId × Int))} {value : ValueId} {site : BlockId × Int}
    (present : (value, site) ∈ entries) (bound : value < table.size)
    (agrees : ∀ entry ∈ entries, entry.1 = value → entry.2 = site) :
    (entries.foldl writeDefinition table)[value]? = some (some site) := by
  induction entries generalizing table with
  | nil => simp at present
  | cons entry rest ih =>
    rcases List.mem_cons.mp present with same | member
    · subst entry
      apply writeDefinitions_lookup (entries := rest)
      · show (writeDefinition table (value, site))[value]? = some (some site)
        simp [writeDefinition, Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_self_of_lt bound]
      · intro next member
        exact agrees next (by simp [member])
    · apply ih member
      · simpa only [writeDefinition_size] using bound
      · intro next member
        exact agrees next (by simp [member])

theorem cfgDefAt_of_unique_location {func : Func}
    (unique : (func.blocks.toList.flatMap GIR.Block.defs).Nodup)
    {value block : Nat} {position : Int} (bound : value < func.numValues)
    (site : DefinitionAt func value block position) :
    (cfgDefAt func)[value]? = some (some (block, position)) := by
  rw [cfgDefAt_eq_locations]
  apply writeDefinitions_contains site (by simpa using bound)
  intro entry member same
  rcases entry with ⟨other, location⟩
  change other = value at same
  subst other
  exact definitionAt_unique unique member site

theorem dominatingUses_of_regions (func : Func)
    (sites : ∀ value block position, DefinitionAt func value block position →
      (cfgDefAt func)[value]? = some (some (block, position)))
    (operands : ∀ block (bound : block < func.blocks.size) inst index,
      (inst, index) ∈ func.blocks[block].insts.zipIdx → ∀ value ∈ inst.uses,
      DefinitionBefore func value block index ∨
        ∃ parent position, ∃ contains : BlockId → Prop, DefinitionAt func value parent position ∧
          parent ≠ block ∧
          DominanceRegion (predecessors func) func.blocks.size parent contains ∧ contains block) :
    DominatingUses func := by
  intro block bound inst index instruction value operand
  rcases operands block bound inst index instruction value operand with before | inherited
  · obtain ⟨position, site, order⟩ := before
    exact ⟨block, position, sites value block position site, by simpa using order⟩
  · obtain ⟨parent, position, contains, site, different, region, inside⟩ := inherited
    refine ⟨parent, position, sites value parent position site, ?_⟩
    simpa only [different, ite_false] using region.dominates bound inside

end Goose.Lower.Validation
