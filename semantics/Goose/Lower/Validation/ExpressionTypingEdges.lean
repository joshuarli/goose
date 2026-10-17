import Goose.Lower.Validation.ExpressionTypingFrame

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitTerm_frame_blocks {le : LEnv} {before after : LS} {result : Unit} {term : Term}
    {current : BlockId} (live : before.cur = some current)
    (run : emitTerm term le before = (result, after))
    {block : GIR.Block} (member : block ∈ (permissionFunc le after).blocks.toList) :
    ∃ old, old ∈ (permissionFunc le before).blocks.toList ∧ block.params = old.params ∧
      (block.insts = old.insts ∨ block.insts = old.insts ++ [.term term]) := by
  rw [emitTerm_run term le live] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  simp only [permissionFunc, Array.toList_map, Array.toList_modify, List.mem_map] at member
  obtain ⟨actual, member, rfl⟩ := member
  rcases list_mem_modify_cases _ _ _ member with unchanged | ⟨old, oldMember, shape⟩
  · refine ⟨⟨actual.params, actual.insts.toList⟩, ?_, rfl, Or.inl rfl⟩
    simp only [permissionFunc, Array.toList_map, List.mem_map]
    exact ⟨actual, unchanged, rfl⟩
  · subst actual
    refine ⟨⟨old.params, old.insts.toList⟩, ?_, rfl, Or.inr ?_⟩
    · simp only [permissionFunc, Array.toList_map, List.mem_map]
      exact ⟨old, oldMember, rfl⟩
    · simp

theorem emitTerm_frame_at {le : LEnv} {before after : LS} {result : Unit} {term : Term}
    {current target : BlockId} (live : before.cur = some current)
    (run : emitTerm term le before = (result, after)) {block : GIR.Block}
    (row : (permissionFunc le after).blocks[target]? = some block) :
    ∃ old, (permissionFunc le before).blocks[target]? = some old ∧ block.params = old.params := by
  rw [emitTerm_run term le live] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  simp only [permissionFunc, Array.getElem?_map, Array.getElem?_modify] at row ⊢
  by_cases same : current = target
  · simp only [same, ↓reduceIte] at row
    cases previous : before.blocks[target]? with
    | none => simp [previous] at row
    | some old =>
      simp only [previous, Option.map_some, Option.some.injEq] at row
      subst block
      exact ⟨⟨old.params, old.insts.toList⟩, by simp, rfl⟩
  · simp only [same, ↓reduceIte] at row
    cases previous : before.blocks[target]? with
    | none => simp [previous] at row
    | some old =>
      simp only [previous, Option.map_some, Option.some.injEq] at row
      subst block
      exact ⟨⟨old.params, old.insts.toList⟩, by simp, rfl⟩

theorem ContentsClosed.emitTerm {le : LEnv} {before after : LS}
    {result : Unit} {term : Term} {current : BlockId} {authorized : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitTerm term le before = (result, after))
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized)
    (edges : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ entry ∈ destination.params.zip edge.2, authorized entry.1.1 → authorized entry.2) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized := by
  have sameVals : after.vals = before.vals := by
    rw [emitTerm_run term le live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    rfl
  have afterDense := (dense_emitTerm term le before result after run checked bounded).1
  constructor
  · intro value member
    rw [permissionFunc_numValues afterDense le, sameVals]
    simpa only [permissionFunc_numValues checked le] using closed.bounded value member
  · intro block row param member permitted
    obtain ⟨old, oldRow, params⟩ := emitTerm_frame_at live run row
    rw [sameVals]
    exact closed.entry old oldRow param (by rw [← params]; exact member) permitted
  · intro block blockMember value op member permitted
    obtain ⟨old, oldMember, _, instructions⟩ := emitTerm_frame_blocks live run blockMember
    have oldInstruction : Inst.def value op ∈ old.insts := by
      rcases instructions with same | same
      · rw [same] at member; exact member
      · rw [same, List.mem_append, List.mem_singleton] at member
        rcases member with member | impossible
        · exact member
        · cases impossible
    exact (closed.definitions old oldMember value op oldInstruction permitted).retained
      (types_emitTerm term le before result after run)
  · intro block blockMember actual member edge edgeMember destination row entry entryMember permitted
    obtain ⟨old, oldMember, _, instructions⟩ := emitTerm_frame_blocks live run blockMember
    obtain ⟨oldDestination, oldRow, params⟩ := emitTerm_frame_at live run row
    have oldEntry : entry ∈ oldDestination.params.zip edge.2 := by rw [← params]; exact entryMember
    rcases instructions with same | same
    · rw [same] at member
      exact closed.edges old oldMember actual member edge edgeMember oldDestination oldRow entry oldEntry permitted
    · rw [same, List.mem_append, List.mem_singleton] at member
      rcases member with oldInstruction | equation
      · exact closed.edges old oldMember actual oldInstruction edge edgeMember oldDestination oldRow entry oldEntry permitted
      · have sameTerm := Inst.term.inj equation
        subst actual
        exact edges edge edgeMember oldDestination oldRow entry oldEntry permitted

#print axioms ContentsClosed.emitTerm

end Goose.Lower.Validation
