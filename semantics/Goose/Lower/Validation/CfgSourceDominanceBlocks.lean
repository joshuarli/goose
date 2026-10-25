import Goose.Lower.Validation.CfgSourceDominanceActions
import Goose.Lower.Validation.CfgTargetBounds
import Goose.Lower.Validation.CfgFrontier

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def extendImports (imports : ImportedValues) (block : BlockId) (values : List ValueId) : ImportedValues :=
  fun index => if index = block then values else imports index

def exitValues (state : LS) (imports : ImportedValues) (block : BlockId) : List ValueId :=
  imports block ++ ((state.blocks[block]?).map fun body => (cfgBlock body).defs).getD []

def currentValues (state : LS) (imports : ImportedValues) : List ValueId :=
  match state.cur with
  | none => []
  | some block => exitValues state imports block

theorem BuilderAvailable.exitValues {state : LS} {imports : ImportedValues} {block value : Nat}
    (available : BuilderAvailable state imports block value) : value ∈ exitValues state imports block := by
  obtain ⟨body, row, member⟩ := available
  simpa [Validation.exitValues, row] using member

theorem available_of_exitValues {state : LS} {imports : ImportedValues} {block value : Nat}
    (bound : block < state.blocks.size) (member : value ∈ exitValues state imports block) :
    BuilderAvailable state imports block value := by
  have row : state.blocks[block]? = some state.blocks[block] := Array.getElem?_eq_getElem bound
  exact ⟨state.blocks[block], row, by simpa [exitValues, row] using member⟩

theorem currentValues_bounded {state : LS} {imports : ImportedValues}
    (dense : state.DenseDefinitions) (liveBound : LiveBound state)
    (importsBounded : ∀ block, block < state.blocks.size →
      ∀ value ∈ imports block, value < state.vals.size) :
    ∀ value ∈ currentValues state imports, value < state.vals.size := by
  intro value member
  cases current : state.cur with
  | none => simp [currentValues, current] at member
  | some block =>
    have bound := liveBound block current
    have available := available_of_exitValues bound (by simpa [currentValues, current] using member)
    obtain ⟨body, row, imported | defined⟩ := available
    · exact importsBounded block bound value imported
    · apply dense.mem_lt
      apply List.mem_flatMap.mpr
      exact ⟨body, Array.mem_toList_iff.mpr (Array.mem_of_getElem? row), defined⟩

theorem BuilderImportedSSA.newBlock {state : LS} {imports : ImportedValues}
    (certificate : BuilderImportedSSA state imports) (targets : TargetsBounded state)
    (types : List VTy) (values : List ValueId)
    (entry : state.blocks.size = 0 → values = [])
    (bounded : ∀ value ∈ values, value < state.vals.size) (env : LEnv) :
    BuilderImportedSSA (newBlock types env state).2
      (extendImports imports state.blocks.size values) := by
  let params := ((List.range types.length).map (state.vals.size + ·)).zip types
  have freshParams : ∀ value ∈ values, value ∉ params.map Prod.fst := by
    intro value imported parameter
    have range : value ∈ (List.range types.length).map (state.vals.size + ·) := by
      have member := List.mem_map.mp parameter
      obtain ⟨pair, pairMember, equal⟩ := member
      exact equal ▸ List.of_mem_zip pairMember |>.1
    obtain ⟨index, _, same⟩ := List.mem_map.mp range
    have small := bounded value imported
    have large : state.vals.size ≤ value := by
      rw [← same]
      exact Nat.le_add_right _ _
    exact Nat.not_lt_of_ge large small
  have oldImports : ∀ block, block < state.blocks.size →
      extendImports imports state.blocks.size values block = imports block := by
    intro block bound
    simp [extendImports, Nat.ne_of_lt bound]
  have rows : ∀ (block : BlockId) (body : BlockB),
      (Goose.Lower.newBlock types env state).2.blocks[block]? = some body →
        (state.blocks[block]? = some body ∧ block < state.blocks.size) ∨
          (block = state.blocks.size ∧ body = ⟨params, #[]⟩) := by
    intro block body row
    change (state.blocks.push ⟨params, #[]⟩)[block]? = some body at row
    by_cases old : block < state.blocks.size
    · exact Or.inl ⟨by simpa [Array.getElem?_push, old, Nat.ne_of_lt old] using row, old⟩
    · have equal : block = state.blocks.size := by
        have bound : block < state.blocks.size + 1 := by
          simpa only [Array.size_push] using (Array.getElem?_eq_some_iff.mp row).1
        exact Nat.le_antisymm (Nat.le_of_lt_succ bound) (Nat.le_of_not_gt old)
      subst block
      exact Or.inr ⟨rfl, by simpa using row.symm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_cases zero : state.blocks.size = 0
    · simp [extendImports, zero, entry zero]
    · simpa [extendImports, Ne.symm zero] using certificate.entry
  · intro block body row value imported defined
    rcases rows block body row with ⟨oldRow, bound⟩ | ⟨rfl, rfl⟩
    · rw [oldImports block bound] at imported
      exact certificate.foreign block body oldRow value imported defined
    · have imported : value ∈ values := by simpa [extendImports] using imported
      exact freshParams value imported (by simpa [cfgBlock, GIR.Block.defs] using defined)
  · intro block body row index inst instruction value used
    rcases rows block body row with ⟨oldRow, bound⟩ | ⟨rfl, rfl⟩
    · rw [oldImports block bound]
      exact certificate.operands block body oldRow index inst instruction value used
    · simp at instruction
  · intro source body row target successor value imported
    rcases rows source body row with ⟨oldRow, sourceBound⟩ | ⟨rfl, rfl⟩
    · have targetBound := targets source body oldRow target successor
      rw [oldImports target targetBound] at imported
      rw [oldImports source sourceBound]
      exact certificate.edges source body oldRow target successor value imported
    · simp [cfgBlock, GIR.Block.terms] at successor

end Goose.Lower.Validation
