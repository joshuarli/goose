import Goose.Lower.Validation.EmittedTypingBuilder
import Goose.Lower.Validation.DenseDefinitions
import Goose.Lower.Validation.OperandBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure EmittedCheckpoint (state : LS) : Prop where
  dense : state.DenseDefinitions
  live : LiveBound state
  operands : OperandBounds state

def EmittedCheckedSite (le : LEnv) (initial final : LS) (value : ValueId) (op : Op) : Prop :=
  ∃ site type block, EmittedTrace le initial site ∧ EmittedCheckpoint site ∧ site.Ext final ∧
    site.cur = some block ∧ value = site.vals.size ∧ op.resultTy (tyEnv le site) = .ok type ∧
    final.vals[value]? = some (some type) ∧ EmittedTypePrefix site final

theorem EmittedCheckedSite.retained {le : LEnv} {initial before after : LS} {value : ValueId} {op : Op}
    (witness : EmittedCheckedSite le initial before value op)
    (extension : before.Ext after) (retained : EmittedTypePrefix before after) :
    EmittedCheckedSite le initial after value op := by
  obtain ⟨site, type, block, trace, checkpoint, extended, live, fresh, success, recorded, oldPrefix⟩ := witness
  exact ⟨site, type, block, trace, checkpoint, extended.trans extension, live, fresh, success,
    retained.typed value type recorded, oldPrefix.trans retained⟩

structure EmittedBuilder (le : LEnv) (initial state : LS) : Prop where
  trace : EmittedTrace le initial state
  checkpoint : EmittedCheckpoint state
  sites : ∀ value op, .def value op ∈ state.insts → EmittedCheckedSite le initial state value op

theorem EmittedBuilder.of_preserving {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (action : B α)
    (trace : EmittedAt le before action) (extension : before.Ext (action le before).2)
    (checkpoint : EmittedCheckpoint (action le before).2)
    (definitions : ∀ value op, .def value op ∈ (action le before).2.insts → .def value op ∈ before.insts) :
    EmittedBuilder le initial (action le before).2 := by
  refine ⟨builder.trace.append trace, checkpoint, ?_⟩
  intro value op member
  exact (builder.sites value op (definitions value op member)).retained extension trace.prefix

theorem EmittedBuilder.emitDef {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (op : Op)
    (success : before.cur.isSome = true → ∃ type, op.resultTy (tyEnv le before) = .ok type)
    (uses : before.cur.isSome = true → ∀ value ∈ op.uses, value < before.vals.size) :
    EmittedBuilder le initial (Goose.Lower.emitDef op le before).2 := by
  have trace := EmittedAt.emitDef (le := le) (before := before) op success
  have dense := dense_emitDef op le before _ _ rfl builder.checkpoint.dense builder.checkpoint.live
  have checkpoint : EmittedCheckpoint (Goose.Lower.emitDef op le before).2 :=
    ⟨dense.1, dense.2.1, operands_emitDef rfl builder.checkpoint.operands uses⟩
  have extension := (advB_emitDef op le before _ _ rfl).ext
  refine ⟨builder.trace.append trace, checkpoint, ?_⟩
  intro value emitted member
  cases live : before.cur with
  | none =>
    rw [emitDef_none op le live] at member ⊢
    exact builder.sites value emitted member
  | some block =>
    have shape := member
    rw [emitDef_run op le live] at shape
    have split := emittedDef_appendInst (before := { before with vals := before.vals.push (some ((op.resultTy (tyEnv le before)).toOption.getD (.data .unit))) }) shape
    rcases split with previous | fresh
    · exact (builder.sites value emitted previous).retained extension trace.prefix
    · obtain ⟨rfl, rfl⟩ := Inst.def.inj fresh
      obtain ⟨type, typed⟩ := success (by simp [live])
      have recorded := emitDef_recorded live typed
      have finalRecorded := recorded.2.2.1
      rw [recorded.1] at finalRecorded
      exact ⟨before, type, block, builder.trace, builder.checkpoint, extension, live, rfl,
        typed, finalRecorded, trace.prefix⟩

theorem EmittedBuilder.emitEffect {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (effect : Effect)
    (uses : before.cur.isSome = true → ∀ value ∈ effect.uses, value < before.vals.size) :
    EmittedBuilder le initial (Goose.Lower.emitEffect effect le before).2 := by
  have dense := dense_emitEffect effect le before _ _ rfl builder.checkpoint.dense builder.checkpoint.live
  apply builder.of_preserving (Goose.Lower.emitEffect effect) (EmittedAt.emitEffect le before effect)
    (advB_emitEffect effect le before _ _ rfl).ext
    ⟨dense.1, dense.2.1, operands_emitEffect rfl builder.checkpoint.operands uses⟩
  intro value op member
  cases live : before.cur with
  | none => rw [emitEffect_none effect le live] at member; exact member
  | some block =>
    rw [emitEffect_run effect le live] at member
    rcases emittedDef_appendInst member with old | fresh
    · exact old
    · cases fresh

theorem EmittedBuilder.emitTerm {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (term : Term)
    (uses : before.cur.isSome = true → ∀ value ∈ term.uses, value < before.vals.size) :
    EmittedBuilder le initial (Goose.Lower.emitTerm term le before).2 := by
  have dense := dense_emitTerm term le before _ _ rfl builder.checkpoint.dense builder.checkpoint.live
  apply builder.of_preserving (Goose.Lower.emitTerm term) (EmittedAt.emitTerm le before term)
    (advB_emitTerm term le before _ _ rfl).ext
    ⟨dense.1, dense.2.1, operands_emitTerm rfl builder.checkpoint.operands uses⟩
  intro value op member
  cases live : before.cur with
  | none => rw [emitTerm_none term le live] at member; exact member
  | some block =>
    rw [emitTerm_run term le live] at member
    have same : .def value op ∈ (before.appendInst block (.term term)).insts := member
    rcases emittedDef_appendInst same with old | fresh
    · exact old
    · cases fresh

theorem EmittedBuilder.newBlock {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (types : List VTy) :
    EmittedBuilder le initial (Goose.Lower.newBlock types le before).2 := by
  have dense := dense_newBlock types le before _ _ rfl builder.checkpoint.dense builder.checkpoint.live
  have extension : before.Ext (Goose.Lower.newBlock types le before).2 := by
    rw [newBlock_run_general]
    exact (LS.Adv.newBlk before _ (by simp [array_size_pushParamTypes])).ext
  apply builder.of_preserving (Goose.Lower.newBlock types) (EmittedAt.newBlock le before types) extension
    ⟨dense.1, dense.2.1, operands_newBlock types le before _ _ rfl builder.checkpoint.operands⟩
  intro value op member
  rw [newBlock_run_general] at member
  simpa only [LS.insts, Array.toList_push, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, Array.toList_empty, List.nil_append, List.append_nil] using member


theorem EmittedBuilder.present {le : LEnv} {initial state : LS}
    (builder : EmittedBuilder le initial state) (present : EmittedTypesPresent initial) :
    EmittedTypesPresent state := builder.trace.present present

theorem EmittedCheckedSite.operation {le : LEnv} {initial final : LS} {value : ValueId} {op : Op}
    (witness : EmittedCheckedSite le initial final value op) (present : EmittedTypesPresent initial) :
    ∃ site block, EmittedTrace le initial site ∧ EmittedCheckpoint site ∧ site.Ext final ∧
      site.cur = some block ∧ value = site.vals.size ∧
      op.resultTy (tyEnv le site) = .ok (emittedValueType final value) ∧
      final.vals[value]? = some (some (emittedValueType final value)) ∧
      (∀ operand, operand < site.vals.size → site.vals[operand]? = some (some (emittedValueType final operand))) := by
  obtain ⟨site, type, block, trace, checkpoint, extension, live, fresh, success, recorded, retained⟩ := witness
  have expected : emittedValueType final value = type := by simp [emittedValueType, recorded]
  refine ⟨site, block, trace, checkpoint, extension, live, fresh,
    by simpa only [expected] using success, by simpa only [expected] using recorded, ?_⟩
  intro operand bound
  obtain ⟨operandType, sourceRow⟩ := trace.present present operand bound
  have finalRow := retained.typed operand operandType sourceRow
  simpa only [emittedValueType, finalRow, Option.getD_some] using sourceRow

theorem EmittedTrace.parameter_types {le : LEnv} {before final : LS} {types : List VTy}
    (trace : EmittedTrace le (Goose.Lower.newBlock types le before).2 final)
    {index : Nat} {type : VTy} (row : types[index]? = some type) :
    final.vals[before.vals.size + index]? = some (some type) := by
  have allocated := newBlock_parameter_types types le before index
  rw [row] at allocated
  exact trace.prefix.typed _ _ allocated


theorem EmittedBuilder.initState (le : LEnv) : EmittedBuilder le initState initState := by
  refine ⟨.refl, ⟨LS.denseDefinitions_initState, liveBound_initState, ?_⟩, ?_⟩
  · intro inst member
    change _ ∈ ([] : List Inst) at member
    cases member
  · intro value op member
    change _ ∈ ([] : List Inst) at member
    cases member

theorem EmittedBuilder.setCur {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (block : Option BlockId)
    (bound : ∀ current, block = some current → current < before.blocks.size) :
    EmittedBuilder le initial (Goose.Lower.setCur block le before).2 := by
  have dense := dense_setCur_at (le := le) (before := before) rfl builder.checkpoint.dense bound
  apply builder.of_preserving (Goose.Lower.setCur block) (EmittedAt.setCur le before block)
    (by exact LS.Ext.refl before)
    ⟨dense.1, dense.2.1, operands_setCur block le before _ _ rfl builder.checkpoint.operands⟩
  intro value op member
  exact member

theorem EmittedBuilder.patchTerm {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (block : BlockId) (term : Term)
    (uses : ∀ value ∈ term.uses, value < before.vals.size) :
    EmittedBuilder le initial (Goose.Lower.patchTerm block term le before).2 := by
  have dense := dense_patchTerm block term le before _ _ rfl builder.checkpoint.dense builder.checkpoint.live
  have extension : before.Ext (Goose.Lower.patchTerm block term le before).2 := by
    rw [patchTerm_run]
    exact (LS.Ext.refl before).modify (appends_push _) block
  apply builder.of_preserving (Goose.Lower.patchTerm block term) (EmittedAt.patchTerm le before block term)
    extension ⟨dense.1, dense.2.1, operands_patchTerm (le := le) (before := before) (block := block) (term := term) rfl builder.checkpoint.operands uses⟩
  intro value op member
  rw [patchTerm_run] at member
  rcases emittedDef_appendInst member with old | fresh
  · exact old
  · cases fresh

theorem EmittedBuilder.of_unchanged {le : LEnv} {initial before : LS}
    (builder : EmittedBuilder le initial before) (action : B α)
    (blocks : (action le before).2.blocks = before.blocks)
    (values : (action le before).2.vals = before.vals)
    (current : (action le before).2.cur = before.cur) :
    EmittedBuilder le initial (action le before).2 := by
  apply builder.of_preserving action
  · apply EmittedAt.of_preserving _ (EmittedTypePrefix.of_vals values)
    intro value op member
    simpa only [LS.insts, blocks] using member
  · simpa only [LS.Ext, blocks] using LS.Ext.refl before
  · constructor
    · simpa only [LS.DenseDefinitions, LS.defs, blocks, values] using builder.checkpoint.dense
    · intro block live
      rw [current] at live
      rw [blocks]
      exact builder.checkpoint.live block live
    · simpa only [OperandBounds, LS.insts, blocks, values] using builder.checkpoint.operands
  · intro value op member
    simpa only [LS.insts, blocks] using member

end Goose.Lower.Validation
