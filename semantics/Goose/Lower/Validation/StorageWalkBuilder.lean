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

theorem StorageWalkBlockTraces.push {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {blocks : Array BlockB}
    (traces : StorageWalkBlockTraces slots entry exit blocks)
    (params : List (ValueId × VTy)) (stack : List ScopeId) :
    StorageWalkBlockTraces slots
      (fun block => if block = blocks.size then stack else entry block)
      (fun block => if block = blocks.size then stack else exit block)
      (blocks.push ⟨params, #[]⟩) := by
  intro block body lookup
  simp only [Array.getElem?_push] at lookup
  by_cases fresh : block = blocks.size
  · simp only [fresh, ite_true, Option.some.injEq] at lookup ⊢
    subst body
    exact .nil stack
  · simp only [fresh, ite_false] at lookup ⊢
    exact traces block body lookup

theorem StorageWalkBuilder.push {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (builder : StorageWalkBuilder slots entry exit before)
    (bound : ∀ block, before.cur = some block → block < before.blocks.size)
    (params : List (ValueId × VTy)) (vals : Array (Option VTy)) :
    StorageWalkBuilder slots
      (fun block => if block = before.blocks.size then before.stack else entry block)
      (fun block => if block = before.blocks.size then before.stack else exit block)
      { before with blocks := before.blocks.push ⟨params, #[]⟩, vals := vals } := by
  refine ⟨builder.traces.push params before.stack, ?_⟩
  intro block live
  have earlier := bound block live
  have distinct : block ≠ before.blocks.size := Nat.ne_of_lt earlier
  simp only [distinct, ite_false]
  exact builder.current block live

theorem StorageWalkBuilder.setCur {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (builder : StorageWalkBuilder slots entry exit before) (next : Option BlockId)
    (resume : ∀ block, next = some block → exit block = before.stack) (env : LEnv) :
    StorageWalkBuilder slots entry exit (setCur next env before).2 := by
  rw [setCur_run]
  exact ⟨builder.traces, resume⟩

theorem StorageWalkBuilder.newBlock {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (builder : StorageWalkBuilder slots entry exit before)
    (bound : ∀ block, before.cur = some block → block < before.blocks.size)
    (env : LEnv) (types : List VTy) :
    StorageWalkBuilder slots
      (fun block => if block = before.blocks.size then before.stack else entry block)
      (fun block => if block = before.blocks.size then before.stack else exit block)
      (newBlock types env before).2 := by
  exact builder.push bound (((List.range types.length).map (before.vals.size + ·)).zip types)
    (types.foldl (fun vals type => vals.push (some type)) before.vals)

theorem StorageWalkBuilder.emitTermTrace {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (builder : StorageWalkBuilder slots entry exit before) (term : Term)
    (trace : StorageWalkTrace slots before.stack [.term term] before.stack) (env : LEnv) :
    StorageWalkBuilder slots entry exit (emitTerm term env before).2 := by
  cases live : before.cur with
  | none => simpa only [emitTerm_none term env live] using builder
  | some block =>
    rw [emitTerm_run term env live]
    refine ⟨?_, ?_⟩
    · have step : StorageWalkTrace slots (exit block) [.term term] (exit block) := by
        rw [builder.current block live]
        exact trace
      have extended := StorageWalkBlockTraces.append builder.traces block
        (.term term) (exit block) step
      have same : (fun other => if other = block then exit block else exit other) = exit := by
        funext other
        split <;> simp_all
      simpa only [same] using extended
    · intro other current
      cases current

theorem StorageWalkBuilder.emitNeutralTerm {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (builder : StorageWalkBuilder slots entry exit before) (term : Term)
    (neutral : scopeNeutral (.term term) = true) (env : LEnv) :
    StorageWalkBuilder slots entry exit (emitTerm term env before).2 := by
  apply builder.emitTermTrace term _ env
  exact .neutral neutral trivial (.nil before.stack)

theorem StorageWalkBuilder.patchNeutralTerm {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (builder : StorageWalkBuilder slots entry exit before) (block : BlockId) (term : Term)
    (neutral : scopeNeutral (.term term) = true) (env : LEnv) :
    StorageWalkBuilder slots entry exit (patchTerm block term env before).2 := by
  rw [patchTerm_run]
  refine ⟨?_, builder.current⟩
  have step : StorageWalkTrace slots (exit block) [.term term] (exit block) :=
    .neutral neutral trivial (.nil _)
  have extended := StorageWalkBlockTraces.append builder.traces block (.term term) (exit block) step
  have same : (fun other => if other = block then exit block else exit other) = exit := by
    funext other
    split <;> simp_all
  simpa only [same] using extended

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
