import Goose.Lower.Validation.FreshRunSource

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem patchTerm_term_cases {env : LEnv} {before after : LS} {patched source : BlockId}
    {inserted term : Term} {result : Unit} {body : BlockB}
    (run : patchTerm patched inserted env before = (result, after))
    (row : after.blocks[source]? = some body) (member : Inst.term term ∈ body.insts.toList) :
    (∃ old, before.blocks[source]? = some old ∧ Inst.term term ∈ old.insts.toList) ∨
      (source = patched ∧ term = inserted) := by
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  change (before.blocks.modify patched fun block =>
    { block with insts := block.insts.push (.term inserted) })[source]? = some body at row
  rw [Array.getElem?_modify] at row
  by_cases same : patched = source
  · simp only [same, ite_true] at row
    cases oldAt : before.blocks[source]? with
    | none => simp [oldAt] at row
    | some old =>
      simp only [oldAt, Option.map_some, Option.some.injEq] at row
      subst body
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
      rcases member with previous | fresh
      · exact Or.inl ⟨old, rfl, previous⟩
      · exact Or.inr ⟨same.symm, Inst.term.inj fresh⟩
  · simp only [same, ite_false] at row
    exact Or.inl ⟨body, row, member⟩

theorem patchBrs_term_cases {env : LEnv} {before after : LS} {join source : BlockId}
    {pending : List (BlockId × ValueId)} {result : Unit} {body : BlockB} {term : Term}
    (run : patchBrs join pending env before = (result, after))
    (row : after.blocks[source]? = some body) (member : Inst.term term ∈ body.insts.toList) :
    (∃ old, before.blocks[source]? = some old ∧ Inst.term term ∈ old.insts.toList) ∨
      ∃ value, (source, value) ∈ pending ∧ term = .br join [value] := by
  induction pending generalizing before result after with
  | nil =>
    rw [patchBrs, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact Or.inl ⟨body, row, member⟩
  | cons head rest ih =>
    obtain ⟨block, value⟩ := head
    simp only [patchBrs, bind_eq] at run
    obtain ⟨_, middle, patched, tail⟩ := run
    rcases ih tail row with previous | fresh
    · obtain ⟨old, oldAt, oldMember⟩ := previous
      rcases patchTerm_term_cases patched oldAt oldMember with previous | inserted
      · exact Or.inl previous
      · obtain ⟨rfl, rfl⟩ := inserted
        exact Or.inr ⟨value, by simp, rfl⟩
    · obtain ⟨value, valueMember, rfl⟩ := fresh
      exact Or.inr ⟨value, by simp [valueMember], rfl⟩

theorem newBlock_term_cases {env : LEnv} {before after : LS} {types : List VTy}
    {result : BlockId × List ValueId} {source : BlockId} {body : BlockB} {term : Term}
    (run : newBlock types env before = (result, after))
    (row : after.blocks[source]? = some body) (member : Inst.term term ∈ body.insts.toList) :
    ∃ old, before.blocks[source]? = some old ∧ Inst.term term ∈ old.insts.toList := by
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  by_cases same : source = before.blocks.size
  · rw [Array.getElem?_push] at row
    simp only [same, ite_true] at row
    have equal := Option.some.inj row
    subst body
    simp at member
  · rw [Array.getElem?_push] at row
    simp only [same, ite_false] at row
    exact ⟨body, row, member⟩

theorem newBlock_no_incoming {env : LEnv} {before after : LS} {types : List VTy}
    {result : BlockId × List ValueId} (run : newBlock types env before = (result, after))
    (bounded : TargetsBounded before) :
    ∀ (source : BlockId) (body : BlockB) (term : Term), after.blocks[source]? = some body →
      Inst.term term ∈ body.insts.toList → result.1 ∉ term.successors := by
  intro source body term row member successor
  obtain ⟨old, oldAt, oldMember⟩ := newBlock_term_cases run row member
  have targetBound := bounded source old oldAt result.1 (by
    apply List.mem_flatMap.mpr
    exact ⟨term, List.mem_filterMap.mpr ⟨.term term, oldMember, rfl⟩, successor⟩)
  exact Nat.not_lt_of_ge (newBlock_fresh (LS.Ext.refl before) run) targetBound

theorem patchBrs_incoming_values {env : LEnv} {before after : LS} {join source : BlockId}
    {pending : List (BlockId × ValueId)} {result : Unit} {body : BlockB} {term : Term}
    (run : patchBrs join pending env before = (result, after))
    (noIncoming : ∀ (source : BlockId) (old : BlockB) (term : Term),
      before.blocks[source]? = some old → Inst.term term ∈ old.insts.toList → join ∉ term.successors)
    (row : after.blocks[source]? = some body) (member : Inst.term term ∈ body.insts.toList)
    {args : List ValueId} (edge : args ∈ edgeArgsTo term join)
    {value : ValueId} (argument : args[0]? = some value) : (source, value) ∈ pending := by
  rcases patchBrs_term_cases run row member with previous | inserted
  · obtain ⟨old, oldAt, oldMember⟩ := previous
    exact False.elim (noIncoming source old term oldAt oldMember (edgeArgsTo_successor edge))
  · obtain ⟨input, pendingMember, rfl⟩ := inserted
    have argsEqual : args = [input] := by simpa [edgeArgsTo] using edge
    subst args
    have same : input = value := by simpa using argument
    simpa only [same] using pendingMember

end Goose.Lower.Validation
