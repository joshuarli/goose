import Goose.Lower.Validation.StorageWalkTrace
import Goose.Lower.Validation.ScopeEdges

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def StorageWalkBlockTraces (slots : Array Slot) (entry exit : BlockId → List ScopeId)
    (blocks : Array BlockB) : Prop :=
  ∀ block body, blocks[block]? = some body →
    StorageWalkTrace slots (entry block) body.insts.toList (exit block)

structure StorageWalkBuilder (slots : Array Slot)
    (entry exit : BlockId → List ScopeId) (state : LS) : Prop where
  traces : StorageWalkBlockTraces slots entry exit state.blocks
  current : ∀ block, state.cur = some block → exit block = state.stack

theorem StorageWalkBlockTraces.append {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {blocks : Array BlockB}
    (traces : StorageWalkBlockTraces slots entry exit blocks)
    (block : BlockId) (inst : Inst) (out : List ScopeId)
    (step : StorageWalkTrace slots (exit block) [inst] out) :
    StorageWalkBlockTraces slots entry (fun other => if other = block then out else exit other)
      (blocks.modify block fun body => { body with insts := body.insts.push inst }) := by
  intro other body lookup
  simp only [Array.getElem?_modify] at lookup
  by_cases same : other = block
  · subst other
    simp only [ite_true] at lookup ⊢
    cases oldLookup : blocks[block]? with
    | none => simp [oldLookup] at lookup
    | some oldBody =>
      simp only [oldLookup, Option.map_some, Option.some.injEq] at lookup
      subst body
      simpa using (traces block oldBody oldLookup).append step
  · have distinct : block ≠ other := Ne.symm same
    simp only [distinct, ite_false] at lookup
    simpa only [same, ite_false] using traces other body lookup

theorem StorageWalkBuilder.emitDef {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (builder : StorageWalkBuilder slots entry exit before) (op : Op) (env : LEnv)
    (visible : ∀ result, StorageInstructionVisible slots before.stack (.def result op)) :
    StorageWalkBuilder slots entry exit (emitDef op env before).2 := by
  cases live : before.cur with
  | none => simpa only [emitDef_none op env live] using builder
  | some block =>
    rw [emitDef_run op env live]
    refine ⟨?_, builder.current⟩
    · have step : StorageWalkTrace slots (exit block) [.def before.vals.size op] (exit block) :=
        .neutral rfl (by rw [builder.current block live]; exact visible _) (.nil _)
      have extended := StorageWalkBlockTraces.append builder.traces block
        (.def before.vals.size op) (exit block) step
      have same : (fun other => if other = block then exit block else exit other) = exit := by
        funext other
        split <;> simp_all
      simpa only [same] using extended

theorem StorageWalkBuilder.emitNeutralEffect {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (builder : StorageWalkBuilder slots entry exit before) (effect : Effect)
    (neutral : scopeNeutral (.eff effect) = true) (env : LEnv)
    (visible : StorageInstructionVisible slots before.stack (.eff effect)) :
    StorageWalkBuilder slots entry exit (emitEffect effect env before).2 := by
  cases live : before.cur with
  | none => simpa only [emitEffect_none effect env live] using builder
  | some block =>
    rw [emitEffect_run effect env live]
    refine ⟨?_, builder.current⟩
    · have step : StorageWalkTrace slots (exit block) [.eff effect] (exit block) :=
        .neutral neutral (by rw [builder.current block live]; exact visible) (.nil _)
      have extended := StorageWalkBlockTraces.append builder.traces block
        (.eff effect) (exit block) step
      have same : (fun other => if other = block then exit block else exit other) = exit := by
        funext other
        split <;> simp_all
      simpa only [same] using extended

theorem StorageWalkBuilder.initState (slots : Array Slot)
    (entry exit : BlockId → List ScopeId) :
    StorageWalkBuilder slots entry exit initState := by
  constructor
  · intro block body lookup
    simp [Goose.Lower.initState] at lookup
  · intro block current
    cases current

end Goose.Lower.Validation
