import Goose.Lower.Frag
import Goose.GIR.Validate

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

inductive UnreachableCode (noReturn : ContextId → Bool) : List Inst → Prop
  | nil : UnreachableCode noReturn []
  | inst {code : List Inst} (prior : UnreachableCode noReturn code) (next : Inst)
      (ordinary : next ≠ .term .unreachable) : UnreachableCode noReturn (code ++ [next])
  | call {code : List Inst} (prior : UnreachableCode noReturn code)
      (value : ValueId) (callee : ContextId) (args : List ValueId) (origin : Option OriginId)
      (stops : noReturn callee = true) :
      UnreachableCode noReturn (code ++ [.def value (.call callee args origin), .term .unreachable])

theorem UnreachableCode.append {noReturn : ContextId → Bool} {left right : List Inst}
    (one : UnreachableCode noReturn left) (two : UnreachableCode noReturn right) :
    UnreachableCode noReturn (left ++ right) := by
  induction two with
  | nil => simpa using one
  | inst prior next ordinary ih => simpa [List.append_assoc] using ih.inst next ordinary
  | call prior value callee args origin stops ih =>
    simpa [List.append_assoc] using ih.call value callee args origin stops

theorem UnreachableCode.paired {noReturn : ContextId → Bool} {code : List Inst}
    (checked : UnreachableCode noReturn code) :
    ∀ index, code[index]? = some (.term .unreachable) →
      ∃ value callee args origin,
        (code.take index).getLast? = some (.def value (.call callee args origin)) ∧ noReturn callee = true := by
  induction checked with
  | nil => intro index found; simp at found
  | @inst code prior next ordinary ih =>
    intro index found
    by_cases old : index < code.length
    · rw [List.getElem?_append_left old] at found
      obtain ⟨value, callee, args, origin, last, stops⟩ := ih index found
      exact ⟨value, callee, args, origin, by simpa only [List.take_append_of_le_length (Nat.le_of_lt old)] using last, stops⟩
    · rw [List.getElem?_append_right (Nat.le_of_not_lt old)] at found
      cases offset : index - code.length with
      | zero =>
        simp only [offset, List.getElem?_cons_zero, Option.some.injEq] at found
        exact False.elim (ordinary found)
      | succ offset => simp [offset] at found
  | @call code prior value callee args origin stops ih =>
    intro index found
    by_cases old : index < code.length
    · rw [List.getElem?_append_left old] at found
      obtain ⟨oldValue, oldCallee, oldArgs, oldOrigin, last, stopped⟩ := ih index found
      exact ⟨oldValue, oldCallee, oldArgs, oldOrigin,
        by simpa only [List.take_append_of_le_length (Nat.le_of_lt old)] using last, stopped⟩
    · rw [List.getElem?_append_right (Nat.le_of_not_lt old)] at found
      cases offset : index - code.length with
      | zero => simp [offset] at found
      | succ rest =>
        cases rest with
        | zero =>
          have position : index = code.length + 1 := by omega
          subst index
          refine ⟨value, callee, args, origin, ?_, stops⟩
          simp [List.take_append, List.getLast?_append]
        | succ rest => simp [offset] at found

def BuilderUnreachable (noReturn : ContextId → Bool) (state : LS) : Prop :=
  ∀ (index : BlockId) (body : BlockB), state.blocks[index]? = some body →
    UnreachableCode noReturn body.insts.toList

theorem BuilderUnreachable.of_blocks {noReturn : ContextId → Bool} {before after : LS}
    (checked : BuilderUnreachable noReturn before) (blocks : after.blocks = before.blocks) :
    BuilderUnreachable noReturn after := by
  intro index body row
  rw [blocks] at row
  exact checked index body row

theorem BuilderUnreachable.modify {noReturn : ContextId → Bool} {state : LS}
    (checked : BuilderUnreachable noReturn state) (index : BlockId) (update : BlockB → BlockB)
    (preserves : ∀ body, state.blocks[index]? = some body → UnreachableCode noReturn (update body).insts.toList) :
    BuilderUnreachable noReturn { state with blocks := state.blocks.modify index update } := by
  intro position body row
  simp only [Array.getElem?_modify] at row
  by_cases same : index = position
  · simp only [same, ite_true, Option.map_eq_some_iff] at row
    obtain ⟨prior, found, rfl⟩ := row
    exact preserves prior (same ▸ found)
  · simp only [same, ite_false] at row
    exact checked position body row

theorem BuilderUnreachable.pushInst {noReturn : ContextId → Bool} {state : LS}
    (checked : BuilderUnreachable noReturn state) (index : BlockId) (inst : Inst)
    (ordinary : inst ≠ .term .unreachable) (env : LEnv) :
    BuilderUnreachable noReturn (pushInst index inst env state).2 := by
  apply checked.modify
  intro body row
  simpa using (checked index body row).inst inst ordinary

theorem BuilderUnreachable.emitDef {noReturn : ContextId → Bool} {state : LS}
    (checked : BuilderUnreachable noReturn state) (op : Op) (env : LEnv) :
    BuilderUnreachable noReturn (emitDef op env state).2 := by
  cases current : state.cur with
  | none => rw [emitDef_none op env current]; exact checked
  | some block =>
    apply (checked.pushInst block (.def state.vals.size op) (by intro same; cases same) env).of_blocks
    rw [emitDef_run op env current]
    rfl

theorem BuilderUnreachable.emitEffect {noReturn : ContextId → Bool} {state : LS}
    (checked : BuilderUnreachable noReturn state) (effect : Effect) (env : LEnv) :
    BuilderUnreachable noReturn (emitEffect effect env state).2 := by
  cases current : state.cur with
  | none => rw [emitEffect_none effect env current]; exact checked
  | some block =>
    apply (checked.pushInst block (.eff effect) (by intro same; cases same) env).of_blocks
    rw [emitEffect_run effect env current]
    rfl

theorem BuilderUnreachable.emitTerm {noReturn : ContextId → Bool} {state : LS}
    (checked : BuilderUnreachable noReturn state) (term : Term) (ordinary : term ≠ .unreachable) (env : LEnv) :
    BuilderUnreachable noReturn (emitTerm term env state).2 := by
  cases current : state.cur with
  | none => rw [emitTerm_none term env current]; exact checked
  | some block =>
    apply (checked.pushInst block (.term term) (by simpa using ordinary) env).of_blocks
    rw [emitTerm_run term env current]
    rfl

theorem BuilderUnreachable.patchTerm {noReturn : ContextId → Bool} {state : LS}
    (checked : BuilderUnreachable noReturn state) (block : BlockId) (term : Term)
    (ordinary : term ≠ .unreachable) (env : LEnv) : BuilderUnreachable noReturn (patchTerm block term env state).2 :=
  checked.pushInst block (.term term) (by simpa using ordinary) env

theorem BuilderUnreachable.newBlock {noReturn : ContextId → Bool} {state : LS}
    (checked : BuilderUnreachable noReturn state) (types : List VTy) (env : LEnv) :
    BuilderUnreachable noReturn (newBlock types env state).2 := by
  intro index body row
  change (state.blocks.push _)[index]? = some body at row
  rw [Array.getElem?_push] at row
  split at row
  · have same := Option.some.inj row
    subst body
    exact .nil
  · exact checked index body row

theorem BuilderUnreachable.setCur {noReturn : ContextId → Bool} {state : LS}
    (checked : BuilderUnreachable noReturn state) (current : Option BlockId) (env : LEnv) :
    BuilderUnreachable noReturn (setCur current env state).2 := checked.of_blocks rfl

theorem BuilderUnreachable.callPair {noReturn : ContextId → Bool} {state : LS}
    (checked : BuilderUnreachable noReturn state) (callee : ContextId) (args : List ValueId)
    (origin : Option OriginId) (stops : noReturn callee = true) (env : LEnv) :
    let action : B ValueId := do
      let value ← Goose.Lower.emitDef (.call callee args origin)
      Goose.Lower.emitTerm .unreachable
      pure value
    BuilderUnreachable noReturn (action env state).2 := by
  cases current : state.cur with
  | none =>
    simpa only [bind_run, emitDef_none _ env current, emitTerm_none _ env current, pure_run] using checked
  | some source =>
    let first := (Goose.Lower.emitDef (.call callee args origin) env state).2
    have firstCurrent : first.cur = some source := by
      dsimp only [first]
      rw [emitDef_run _ env current]
      exact current
    have firstBlocks : first.blocks = state.blocks.modify source
        (fun body => { body with insts := body.insts.push (.def state.vals.size (.call callee args origin)) }) := by
      dsimp only [first]
      rw [emitDef_run _ env current]
    simp only [bind_run, pure_run]
    change BuilderUnreachable noReturn (Goose.Lower.emitTerm .unreachable env first).2
    rw [emitTerm_run _ env firstCurrent]
    intro index body row
    change (first.blocks.modify source (fun body => { body with insts := body.insts.push (.term .unreachable) }))[index]? = some body at row
    rw [firstBlocks] at row
    simp only [Array.getElem?_modify] at row
    by_cases same : source = index
    · simp only [same, ite_true, Option.map_map, Option.map_eq_some_iff] at row
      obtain ⟨prior, found, rfl⟩ := row
      simpa [List.append_assoc] using (checked index prior found).call state.vals.size callee args origin stops
    · simp only [same, ite_false] at row
      exact checked index body row

def UnreachableRun (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) →
    BuilderUnreachable env.mod.noReturn before → BuilderUnreachable env.mod.noReturn after

theorem UnreachableRun.pure (value : α) : UnreachableRun (pure value) := by
  intro env before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem UnreachableRun.bind {first : B α} {next : α → B β}
    (one : UnreachableRun first) (two : ∀ value, UnreachableRun (next value)) : UnreachableRun (first >>= next) := by
  intro env before result after run checked
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  exact two value env middle result after nextRun (one env before value middle firstRun checked)

theorem UnreachableRun.of_blocks {action : B α}
    (blocks : ∀ env state, (action env state).2.blocks = state.blocks) : UnreachableRun action := by
  intro env before result after run checked
  have same := blocks env before
  rw [run] at same
  exact checked.of_blocks same

theorem unreachable_call (callee : ContextId) (args : List ValueId) (origin : Option OriginId) :
    UnreachableRun (do
      let value ← emitDef (.call callee args origin)
      if (← read).mod.noReturn callee then emitTerm .unreachable
      pure value) := by
  intro env before result after run checked
  simp only [bind_run, read_apply] at run
  change (if env.mod.noReturn callee then
    (do emitTerm .unreachable; pure (emitDef (.call callee args origin) env before).1)
    else pure (emitDef (.call callee args origin) env before).1)
    env (emitDef (.call callee args origin) env before).2 = (result, after) at run
  cases stops : env.mod.noReturn callee with
  | false =>
    rw [stops] at run
    simp only [Bool.false_eq_true, ite_false, pure_run] at run
    obtain ⟨_, same⟩ := Prod.mk.inj run
    exact (checked.emitDef (.call callee args origin) env).of_blocks (by rw [← same])
  | true =>
    rw [stops] at run
    simp only [ite_true] at run
    have paired := checked.callPair callee args origin stops env
    simp only [bind_run, pure_run] at paired
    simp only [bind_run, pure_run] at run
    obtain ⟨_, same⟩ := Prod.mk.inj run
    exact paired.of_blocks (by rw [← same])

end Goose.Lower.Validation
