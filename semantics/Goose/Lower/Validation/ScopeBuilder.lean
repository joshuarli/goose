import Goose.Lower.Frag
import Goose.Lower.Validation.ScopeGraph

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ScopeBlockTraces (parents : Array (Option ScopeId))
    (entry exit : BlockId → List ScopeId) (blocks : Array BlockB) : Prop :=
  ∀ block body, blocks[block]? = some body →
    ScopeTrace parents (entry block) body.insts.toList (exit block)

structure ScopeBuilder (parents : Array (Option ScopeId))
    (entry exit : BlockId → List ScopeId) (state : LS) : Prop where
  traces : ScopeBlockTraces parents entry exit state.blocks
  current : ∀ block, state.cur = some block → exit block = state.stack

theorem ScopeBlockTraces.append {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {blocks : Array BlockB}
    (traces : ScopeBlockTraces parents entry exit blocks)
    (block : BlockId) (inst : Inst) (out : List ScopeId)
    (step : ScopeTrace parents (exit block) [inst] out) :
    ScopeBlockTraces parents entry (fun other => if other = block then out else exit other)
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

theorem ScopeBuilder.emitDef {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : ScopeBuilder parents entry exit before) (op : Op) (env : LEnv) :
    ScopeBuilder parents entry exit (emitDef op env before).2 := by
  cases live : before.cur with
  | none => simpa [emitDef_none op env live] using valid
  | some block =>
    rw [emitDef_run op env live]
    refine ⟨?_, ?_⟩
    · have step : ScopeTrace parents (exit block) [.def before.vals.size op] (exit block) :=
        .neutral rfl (.nil _)
      have extended := valid.traces.append block (.def before.vals.size op) (exit block) step
      have same : (fun other => if other = block then exit block else exit other) = exit := by
        funext other
        split <;> simp_all
      simpa only [same] using extended
    · exact valid.current

theorem ScopeBuilder.emitNeutralEffect {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : ScopeBuilder parents entry exit before) (effect : Effect)
    (neutral : scopeNeutral (.eff effect) = true) (env : LEnv) :
    ScopeBuilder parents entry exit (emitEffect effect env before).2 := by
  cases live : before.cur with
  | none => simpa [emitEffect_none effect env live] using valid
  | some block =>
    rw [emitEffect_run effect env live]
    refine ⟨?_, ?_⟩
    · have step : ScopeTrace parents (exit block) [.eff effect] (exit block) :=
        .neutral neutral (.nil _)
      have extended := valid.traces.append block (.eff effect) (exit block) step
      have same : (fun other => if other = block then exit block else exit other) = exit := by
        funext other
        split <;> simp_all
      simpa only [same] using extended
    · exact valid.current

theorem ScopeBuilder.enter {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : ScopeBuilder parents entry exit before) (scope : ScopeId) (env : LEnv)
    (block : BlockId) (live : before.cur = some block)
    (parent : parents[scope]?.getD none = before.stack.head?) :
    ScopeBuilder parents entry (fun other => if other = block then scope :: exit block else exit other)
      ((emitEffect (.enter scope) >>= fun _ => pushScope scope) env before).2 := by
  rw [bind_run, emitEffect_run _ _ live, pushScope_run]
  dsimp only
  refine ⟨?_, ?_⟩
  · apply valid.traces.append block (.eff (.enter scope)) (scope :: exit block)
    apply ScopeTrace.enter
    · rw [valid.current block live]
      exact parent
    · exact .nil _
  · intro other current
    have same : other = block := Option.some.inj (current.symm.trans live)
    subst other
    simp [valid.current block live]

theorem ScopeBuilder.leave {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : ScopeBuilder parents entry exit before) (scope : ScopeId) (rest : List ScopeId)
    (env : LEnv) (block : BlockId) (live : before.cur = some block)
    (stack : before.stack = scope :: rest) :
    ScopeBuilder parents entry (fun other => if other = block then rest else exit other)
      ((emitEffect (.leave scope) >>= fun _ => popScope) env before).2 := by
  rw [bind_run, emitEffect_run _ _ live, popScope_run]
  dsimp only
  refine ⟨?_, ?_⟩
  · apply valid.traces.append block (.eff (.leave scope)) rest
    rw [valid.current block live, stack]
    exact .leave (.nil _)
  · intro other current
    have same : other = block := Option.some.inj (current.symm.trans live)
    subst other
    simp [stack]

def ScopeBuilder.finish {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : ScopeBuilder parents entry exit before) (initial : entry 0 = [])
    (edges : ∀ block body, before.blocks[block]? = some body →
      ∀ target ∈ (GIR.Block.mk body.params body.insts.toList).terms.flatMap Term.successors,
        entry target = exit block) (func : Func)
    (scopeTable : func.scopes = parents)
    (blocks : func.blocks = finishBlocks before.blocks) : ScopeGraph func := by
  refine ⟨entry, exit, initial, ?_, ?_⟩
  · intro block body lookup
    rw [blocks] at lookup
    simp only [finishBlocks, Array.getElem?_map] at lookup
    cases beforeLookup : before.blocks[block]? with
    | none => simp [beforeLookup] at lookup
    | some beforeBody =>
      simp only [beforeLookup, Option.map_some, Option.some.injEq] at lookup
      subst body
      rw [scopeTable]
      exact valid.traces block beforeBody beforeLookup
  · intro block body lookup target member
    rw [blocks] at lookup
    simp only [finishBlocks, Array.getElem?_map] at lookup
    cases beforeLookup : before.blocks[block]? with
    | none => simp [beforeLookup] at lookup
    | some beforeBody =>
      simp only [beforeLookup, Option.map_some, Option.some.injEq] at lookup
      subst body
      exact edges block beforeBody beforeLookup target member

end Goose.Lower.Validation
