import Goose.Lower.Validation.ValueTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure EmittedTypePrefix (before after : LS) : Prop where
  size : before.vals.size ≤ after.vals.size
  lookup : ∀ value, value < before.vals.size → after.vals[value]? = before.vals[value]?

theorem EmittedTypePrefix.refl (state : LS) : EmittedTypePrefix state state :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem EmittedTypePrefix.trans {before middle after : LS}
    (first : EmittedTypePrefix before middle) (second : EmittedTypePrefix middle after) :
    EmittedTypePrefix before after := by
  refine ⟨Nat.le_trans first.size second.size, ?_⟩
  intro value bound
  exact (second.lookup value (Nat.lt_of_lt_of_le bound first.size)).trans (first.lookup value bound)

theorem EmittedTypePrefix.typed {before after : LS} (prefixProof : EmittedTypePrefix before after) :
    TypePrefix before after := by
  intro value type row
  rw [prefixProof.lookup value (Array.getElem?_eq_some_iff.mp row).1]
  exact row

theorem emittedTypePrefix_emitDef (op : Op) (le : LEnv) (before : LS) :
    EmittedTypePrefix before (emitDef op le before).2 := by
  cases live : before.cur with
  | none => rw [emitDef_none op le live]; exact .refl _
  | some block =>
    rw [emitDef_run op le live]
    refine ⟨by simp, ?_⟩
    intro value bound
    simp [Array.getElem?_push, Nat.ne_of_lt bound]

theorem emittedTypePrefix_newBlock (types : List VTy) (le : LEnv) (before : LS) :
    EmittedTypePrefix before (newBlock types le before).2 := by
  rw [newBlock_run_general]
  exact ⟨by simp [array_size_pushParamTypes], fun value bound => pushParamTypes_preserves_lookup _ _ _ bound⟩

inductive EmittedTrace (le : LEnv) (initial : LS) : LS → Prop where
  | refl : EmittedTrace le initial initial
  | preserve {before after : LS} {α : Type} (step : B α) (result : α)
      (prefixTrace : EmittedTrace le initial before) (run : step le before = (result, after))
      (retained : EmittedTypePrefix before after)
      (definitions : ∀ value op, .def value op ∈ after.insts → .def value op ∈ before.insts) :
      EmittedTrace le initial after
  | emit {before : LS} (prefixTrace : EmittedTrace le initial before) (op : Op) (type : VTy)
      (success : op.resultTy (tyEnv le before) = .ok type) :
      EmittedTrace le initial (emitDef op le before).2

theorem EmittedTrace.prefix {le : LEnv} {initial final : LS} (trace : EmittedTrace le initial final) :
    EmittedTypePrefix initial final := by
  induction trace with
  | refl => exact .refl _
  | preserve step result trace run retained definitions inductionHypothesis =>
    exact inductionHypothesis.trans retained
  | emit trace op type success inductionHypothesis => exact inductionHypothesis.trans (emittedTypePrefix_emitDef _ _ _)

theorem EmittedTrace.append {le : LEnv} {initial middle final : LS}
    (first : EmittedTrace le initial middle) (second : EmittedTrace le middle final) :
    EmittedTrace le initial final := by
  induction second with
  | refl => exact first
  | preserve step result trace run retained definitions inductionHypothesis =>
    exact .preserve step result inductionHypothesis run retained definitions
  | emit trace op type success inductionHypothesis => exact .emit inductionHypothesis op type success

def EmittedDefWitness (le : LEnv) (initial final : LS) (value : ValueId) (op : Op) : Prop :=
  ∃ site type block, EmittedTrace le initial site ∧ site.cur = some block ∧ value = site.vals.size ∧
    op.resultTy (tyEnv le site) = .ok type ∧ final.vals[value]? = some (some type) ∧
    EmittedTypePrefix site final

theorem EmittedDefWitness.retained {le : LEnv} {initial before after : LS} {value : ValueId} {op : Op}
    (witness : EmittedDefWitness le initial before value op) (retained : EmittedTypePrefix before after) :
    EmittedDefWitness le initial after value op := by
  obtain ⟨site, type, block, trace, live, fresh, success, recorded, sitePrefix⟩ := witness
  exact ⟨site, type, block, trace, live, fresh, success, retained.typed value type recorded, sitePrefix.trans retained⟩

theorem emittedDef_appendInst {before : LS} {block value : ValueId} {op : Op} {inst : Inst}
    (member : .def value op ∈ (before.appendInst block inst).insts) :
    .def value op ∈ before.insts ∨ .def value op = inst := by
  obtain ⟨body, bodyMember, instMember⟩ := List.mem_flatMap.mp member
  obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp bodyMember)
  change (before.blocks.modify block fun body => { body with insts := body.insts.push inst })[index]? = some body at lookup
  rw [Array.getElem?_modify] at lookup
  by_cases same : block = index
  · simp only [same, ↓reduceIte] at lookup
    cases oldRow : before.blocks[index]? with
    | none => simp [oldRow] at lookup
    | some old =>
      simp only [oldRow, Option.map_some, Option.some.injEq] at lookup
      subst body
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at instMember
      rcases instMember with previous | fresh
      · exact Or.inl (List.mem_flatMap.mpr ⟨old, Array.mem_toList_iff.mpr (Array.mem_of_getElem? oldRow), previous⟩)
      · exact Or.inr fresh
  · simp only [same, ↓reduceIte] at lookup
    exact Or.inl (List.mem_flatMap.mpr ⟨body, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), instMember⟩)

theorem EmittedTrace.definitions {le : LEnv} {initial final : LS}
    (trace : EmittedTrace le initial final) (empty : ∀ value op, .def value op ∉ initial.insts) :
    ∀ value op, .def value op ∈ final.insts → EmittedDefWitness le initial final value op := by
  induction trace with
  | refl => intro value op member; exact (empty value op member).elim
  | preserve step result trace run retained definitions inductionHypothesis =>
    intro value op member
    exact (inductionHypothesis value op (definitions value op member)).retained retained
  | @emit before trace op type success inductionHypothesis =>
    intro value emitted member
    cases live : before.cur with
    | none =>
      rw [emitDef_none op le live] at member ⊢
      exact inductionHypothesis value emitted member
    | some block =>
      have prefixProof := emittedTypePrefix_emitDef op le before
      have shape := member
      rw [emitDef_run op le live] at shape
      have split := emittedDef_appendInst (before := { before with vals := before.vals.push (some ((op.resultTy (tyEnv le before)).toOption.getD (.data .unit))) }) shape
      rcases split with previous | fresh
      · exact (inductionHypothesis value emitted previous).retained prefixProof
      · obtain ⟨rfl, rfl⟩ := Inst.def.inj fresh
        have recorded := emitDef_recorded live success
        have finalRecorded := recorded.2.2.1
        rw [recorded.1] at finalRecorded
        exact ⟨before, type, block, trace, live, rfl, success, finalRecorded, prefixProof⟩

def EmittedRun (action : B α) : Prop :=
  ∀ le before, EmittedTrace le before (action le before).2

theorem EmittedRun.pure (value : α) : EmittedRun (Pure.pure value) := by
  intro le before
  exact .refl

theorem EmittedRun.bind {first : B α} {next : α → B β}
    (firstTrace : EmittedRun first) (nextTrace : ∀ value, EmittedRun (next value)) : EmittedRun (first >>= next) := by
  intro le before
  exact (firstTrace le before).append (nextTrace (first le before).1 le (first le before).2)

theorem EmittedRun.emitDef (op : Op)
    (success : ∀ le before, ∃ type, op.resultTy (tyEnv le before) = .ok type) : EmittedRun (Goose.Lower.emitDef op) := by
  intro le before
  obtain ⟨type, typed⟩ := success le before
  exact .emit .refl op type typed


def emittedValueType (state : LS) (value : ValueId) : VTy :=
  (state.vals[value]?.getD none).getD (.data .unit)

theorem EmittedDefWitness.operation {le : LEnv} {initial final : LS} {value : ValueId} {op : Op}
    (witness : EmittedDefWitness le initial final value op)
    (bounded : ∀ operand ∈ op.uses, operand < value) :
    ∃ site block, EmittedTrace le initial site ∧ site.cur = some block ∧ value = site.vals.size ∧
      op.resultTy (tyEnv le site) = .ok (emittedValueType final value) ∧
      final.vals[value]? = some (some (emittedValueType final value)) ∧
      (∀ operand ∈ op.uses, (tyEnv le site).vals[operand]? = final.vals[operand]?) := by
  obtain ⟨site, type, block, trace, live, fresh, success, recorded, retained⟩ := witness
  have expected : emittedValueType final value = type := by simp [emittedValueType, recorded]
  refine ⟨site, block, trace, live, fresh, by simpa only [expected] using success,
    by simpa only [expected] using recorded, ?_⟩
  intro operand member
  exact (retained.lookup operand (by rw [← fresh]; exact bounded operand member)).symm

theorem EmittedTrace.operations {le : LEnv} {initial final : LS}
    (trace : EmittedTrace le initial final) (empty : ∀ value op, .def value op ∉ initial.insts)
    (bounded : ∀ value op, .def value op ∈ final.insts → ∀ operand ∈ op.uses, operand < value) :
    ∀ value op, .def value op ∈ final.insts →
    ∃ site block, EmittedTrace le initial site ∧ site.cur = some block ∧ value = site.vals.size ∧
      op.resultTy (tyEnv le site) = .ok (emittedValueType final value) ∧
      final.vals[value]? = some (some (emittedValueType final value)) ∧
      (∀ operand ∈ op.uses, (tyEnv le site).vals[operand]? = final.vals[operand]?) := by
  intro value op member
  exact (trace.definitions empty value op member).operation (bounded value op member)

end Goose.Lower.Validation
