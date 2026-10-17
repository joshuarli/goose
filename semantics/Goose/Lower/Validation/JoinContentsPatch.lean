import Goose.Lower.Validation.ExpressionTypingFreshContents

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem join_patchTerm_frame_blocks {le : LEnv} {before after : LS} {result : Unit} {term : Term} {current : BlockId}
    (run : patchTerm current term le before = (result, after))
    {block : GIR.Block} (member : block ∈ (permissionFunc le after).blocks.toList) :
    ∃ old, old ∈ (permissionFunc le before).blocks.toList ∧ block.params = old.params ∧
      (block.insts = old.insts ∨ block.insts = old.insts ++ [.term term]) := by
  rw [patchTerm_run current term] at run
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

theorem join_patchTerm_frame_at {le : LEnv} {before after : LS} {result : Unit} {term : Term} {current : BlockId}
    {target : BlockId} (run : patchTerm current term le before = (result, after)) {block : GIR.Block}
    (row : (permissionFunc le after).blocks[target]? = some block) :
    ∃ old, (permissionFunc le before).blocks[target]? = some old ∧ block.params = old.params := by
  rw [patchTerm_run current term] at run
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

theorem ContentsClosed.patchTerm {le : LEnv} {before after : LS}
    {result : Unit} {term : Term} {current : BlockId} {authorized : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : patchTerm current term le before = (result, after))
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized)
    (edges : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ entry ∈ destination.params.zip edge.2, authorized entry.1.1 → authorized entry.2) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized := by
  have sameVals : after.vals = before.vals := by
    rw [patchTerm_run current term] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    rfl
  have afterDense := (dense_patchTerm current term le before result after run checked bounded).1
  constructor
  · intro value member
    rw [permissionFunc_numValues afterDense le, sameVals]
    simpa only [permissionFunc_numValues checked le] using closed.bounded value member
  · intro block row param member permitted
    obtain ⟨old, oldRow, params⟩ := join_patchTerm_frame_at run row
    rw [sameVals]
    exact closed.entry old oldRow param (by rw [← params]; exact member) permitted
  · intro block blockMember value op member permitted
    obtain ⟨old, oldMember, _, instructions⟩ := join_patchTerm_frame_blocks run blockMember
    have oldInstruction : Inst.def value op ∈ old.insts := by
      rcases instructions with same | same
      · rw [same] at member; exact member
      · rw [same, List.mem_append, List.mem_singleton] at member
        rcases member with member | impossible
        · exact member
        · cases impossible
    exact (closed.definitions old oldMember value op oldInstruction permitted).retained
      (types_patchTerm current term le before result after run)
  · intro block blockMember actual member edge edgeMember destination row entry entryMember permitted
    obtain ⟨old, oldMember, _, instructions⟩ := join_patchTerm_frame_blocks run blockMember
    obtain ⟨oldDestination, oldRow, params⟩ := join_patchTerm_frame_at run row
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


theorem NonIntegerParameters.patchTerm {le : LEnv} {before after : LS}
    {result : Unit} {term : Term} {current : BlockId} {authorized : ValueId → Prop}
    (run : patchTerm current term le before = (result, after))
    (checked : NonIntegerParameters (permissionFunc le before) authorized) :
    NonIntegerParameters (permissionFunc le after) authorized := by
  intro block blockMember param member permitted
  obtain ⟨old, oldMember, params, _⟩ := join_patchTerm_frame_blocks run blockMember
  exact checked old oldMember param (by rw [← params]; exact member) permitted

theorem FreshContentsEvidence.patchTerm_before {le : LEnv} {first : Nat} {before after : LS}
    {value current : Nat} {result : Unit} {term : Term}
    (evidence : FreshContentsEvidence le first before value)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : patchTerm current term le before = (result, after))
    (targets : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ param ∈ destination.params, param.1 < first) :
    FreshContentsEvidence le first after value := by
  obtain ⟨authorized, closed, noninteger, permitted, fresh⟩ := evidence
  refine ⟨authorized, closed.patchTerm checked bounded run ?_, noninteger.patchTerm run, permitted, fresh⟩
  intro edge member destination row entry belongs allowed
  have old := targets edge member destination row entry.1 (List.of_mem_zip belongs).1
  exact (Nat.not_lt_of_ge (fresh _ allowed) old).elim

theorem FreshContentsEvidence.emitTerm_before {le : LEnv} {first : Nat} {before after : LS}
    {value : ValueId} {result : Unit} {term : Term}
    (evidence : FreshContentsEvidence le first before value)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : emitTerm term le before = (result, after))
    (targets : ∀ edge ∈ term.permissionEdges, ∀ destination,
      (permissionFunc le before).blocks[edge.1]? = some destination →
      ∀ param ∈ destination.params, param.1 < first) :
    FreshContentsEvidence le first after value := by
  cases live : before.cur with
  | none =>
      rw [emitTerm_none term le live] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact evidence
  | some current =>
      obtain ⟨authorized, closed, noninteger, permitted, fresh⟩ := evidence
      refine ⟨authorized, closed.emitTerm checked bounded live run ?_, noninteger.emitTerm live run, permitted, fresh⟩
      intro edge member destination row entry belongs allowed
      have old := targets edge member destination row entry.1 (List.of_mem_zip belongs).1
      exact (Nat.not_lt_of_ge (fresh _ allowed) old).elim

theorem FreshContentsEvidence.setCur {le : LEnv} {first : Nat} {before after : LS}
    {value : ValueId} {result : Unit} {current : Option BlockId}
    (evidence : FreshContentsEvidence le first before value)
    (run : setCur current le before = (result, after)) : FreshContentsEvidence le first after value := by
  rw [setCur_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact evidence


end Goose.Lower.Validation
