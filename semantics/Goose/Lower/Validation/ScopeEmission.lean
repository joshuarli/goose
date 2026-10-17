import Goose.Lower.Frag
import Goose.Lower.Validation.ScopeWalk

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem leaveAll_emitted (scopes : List ScopeId) (env : LEnv) (before : LS)
    (block : BlockId) (body : BlockB) (live : before.cur = some block)
    (lookup : before.blocks[block]? = some body) :
    let after := (leaveAll scopes env before).2
    after.cur = before.cur ∧ after.stack = before.stack ∧ after.vals = before.vals ∧
      after.blocks[block]? = some { body with insts :=
        body.insts ++ (scopes.map fun scope => Inst.eff (.leave scope)).toArray } := by
  induction scopes generalizing before body with
  | nil => simpa [leaveAll, pure_run] using lookup
  | cons scope scopes ih =>
    rw [leaveAll, bind_run, emitEffect_run _ _ live]
    dsimp only
    have nextLookup :
        (before.blocks.modify block fun blk => { blk with insts := blk.insts.push (.eff (.leave scope)) })[block]? =
          some { body with insts := body.insts.push (.eff (.leave scope)) } := by
      simp [Array.getElem?_modify, lookup]
    have rest := ih { before with blocks := before.blocks.modify block (fun blk => { blk with insts := blk.insts.push (.eff (.leave scope)) }) }
      { body with insts := body.insts.push (.eff (.leave scope)) } live nextLookup
    simpa [List.map_cons] using rest

theorem leaveTo_emitted (depth : Nat) (env : LEnv) (before : LS)
    (block : BlockId) (body : BlockB) (live : before.cur = some block)
    (lookup : before.blocks[block]? = some body) :
    let after := (leaveTo depth env before).2
    after.cur = before.cur ∧ after.stack = before.stack ∧ after.vals = before.vals ∧
      after.blocks[block]? = some { body with insts := body.insts ++
        ((before.stack.take (before.stack.length - depth)).map
          fun scope => Inst.eff (.leave scope)).toArray } := by
  simpa [leaveTo, bind_run, get_apply] using
    leaveAll_emitted (before.stack.take (before.stack.length - depth)) env before block body live lookup

theorem leaveTo_scopeTrace (depth : Nat) (env : LEnv) (before : LS)
    (block : BlockId) (body : BlockB) (live : before.cur = some block)
    (lookup : before.blocks[block]? = some body) (parents : Array (Option ScopeId)) :
    ∃ afterBody, (leaveTo depth env before).2.blocks[block]? = some afterBody ∧
      afterBody.insts.toList = body.insts.toList ++
        ((before.stack.take (before.stack.length - depth)).map fun scope => Inst.eff (.leave scope)) ∧
      ScopeTrace parents before.stack
        (afterBody.insts.toList.drop body.insts.size)
        (before.stack.drop (before.stack.length - depth)) := by
  have emitted := leaveTo_emitted depth env before block body live lookup
  dsimp only at emitted
  refine ⟨_, emitted.2.2.2, ?_, ?_⟩
  · simp
  · simpa using ScopeTrace.leaveTo parents before.stack depth

theorem unwindTerm_emitted (depth : Nat) (term : Term) (env : LEnv) (before : LS)
    (block : BlockId) (body : BlockB) (live : before.cur = some block)
    (lookup : before.blocks[block]? = some body) :
    let after := ((leaveTo depth >>= fun _ => emitTerm term) env before).2
    after.cur = none ∧ after.stack = before.stack ∧ after.vals = before.vals ∧
      after.blocks[block]? = some { body with insts :=
        (body.insts ++ ((before.stack.take (before.stack.length - depth)).map
          fun scope => Inst.eff (.leave scope)).toArray).push (.term term) } := by
  have emitted := leaveTo_emitted depth env before block body live lookup
  dsimp only at emitted
  have current : (leaveTo depth env before).2.cur = some block := emitted.1.trans live
  simp only [bind_run]
  rw [emitTerm_run _ _ current]
  dsimp only
  refine ⟨rfl, emitted.2.1, emitted.2.2.1, ?_⟩
  simp [Array.getElem?_modify, emitted.2.2.2]

theorem unwindBranch_scopeTrace (depth : Nat) (target : BlockId) (arguments : List ValueId)
    (env : LEnv) (before : LS) (block : BlockId) (body : BlockB)
    (live : before.cur = some block) (lookup : before.blocks[block]? = some body)
    (parents : Array (Option ScopeId)) :
    let after := ((leaveTo depth >>= fun _ => emitTerm (.br target arguments)) env before).2
    after.cur = none ∧ ∃ afterBody, after.blocks[block]? = some afterBody ∧
      ScopeTrace parents before.stack (afterBody.insts.toList.drop body.insts.size)
        (before.stack.drop (before.stack.length - depth)) := by
  have emitted := unwindTerm_emitted depth (.br target arguments) env before block body live lookup
  dsimp only at emitted ⊢
  refine ⟨emitted.1, _, emitted.2.2.2, ?_⟩
  have trace := (ScopeTrace.leaveTo parents before.stack depth).append
    (.neutral (inst := .term (.br target arguments)) rfl (.nil _))
  simpa [List.drop_append] using trace

theorem unwindReturn_scopeTrace (values : List ValueId) (origin : Option OriginId)
    (env : LEnv) (before : LS) (block : BlockId) (body : BlockB)
    (live : before.cur = some block) (lookup : before.blocks[block]? = some body)
    (parents : Array (Option ScopeId)) :
    let after := ((leaveTo 0 >>= fun _ => emitTerm (.ret values origin)) env before).2
    after.cur = none ∧ ∃ afterBody, after.blocks[block]? = some afterBody ∧
      ScopeTrace parents before.stack (afterBody.insts.toList.drop body.insts.size) [] := by
  have emitted := unwindTerm_emitted 0 (.ret values origin) env before block body live lookup
  dsimp only at emitted ⊢
  refine ⟨emitted.1, _, emitted.2.2.2, ?_⟩
  simpa [List.drop_append] using ScopeTrace.leaveReturn parents before.stack values origin

theorem lowerStmt_returnNone_scopeTrace (lc : Option LoopCtx) (origin : OriginId)
    (env : LEnv) (before : LS) (block : BlockId) (body : BlockB)
    (live : before.cur = some block) (lookup : before.blocks[block]? = some body)
    (parents : Array (Option ScopeId)) :
    let after := (lowerStmt lc (.ret none origin) env before).2
    after.cur = none ∧ ∃ afterBody, after.blocks[block]? = some afterBody ∧
      ScopeTrace parents before.stack (afterBody.insts.toList.drop body.insts.size) [] := by
  simpa [lowerStmt, bind_run, pure_run] using
    unwindReturn_scopeTrace [] (some origin) env before block body live lookup parents

theorem lowerStmt_break_scopeTrace (loop : LoopCtx) (origin : OriginId)
    (env : LEnv) (before : LS) (block : BlockId) (body : BlockB)
    (live : before.cur = some block) (lookup : before.blocks[block]? = some body)
    (parents : Array (Option ScopeId)) :
    let after := (lowerStmt (some loop) (.brk origin) env before).2
    after.cur = none ∧ ∃ afterBody, after.blocks[block]? = some afterBody ∧
      ScopeTrace parents before.stack (afterBody.insts.toList.drop body.insts.size)
        (before.stack.drop (before.stack.length - loop.depth)) := by
  exact unwindBranch_scopeTrace loop.depth loop.breakTo [] env before block body live lookup parents

theorem lowerStmt_continueJump_scopeTrace (depth : Nat) (exit header : BlockId) (origin : OriginId)
    (env : LEnv) (before : LS) (block : BlockId) (body : BlockB)
    (live : before.cur = some block) (lookup : before.blocks[block]? = some body)
    (parents : Array (Option ScopeId)) :
    let after := (lowerStmt (some ⟨depth, exit, .jump header⟩) (.cont origin) env before).2
    after.cur = none ∧ ∃ afterBody, after.blocks[block]? = some afterBody ∧
      ScopeTrace parents before.stack (afterBody.insts.toList.drop body.insts.size)
        (before.stack.drop (before.stack.length - depth)) := by
  exact unwindBranch_scopeTrace depth header [] env before block body live lookup parents

theorem lowerStmt_continueNext_scopeTrace (depth : Nat) (exit header : BlockId)
    (type : IntTy) (counter : ValueId) (origin : OriginId)
    (env : LEnv) (before : LS) (block : BlockId) (body : BlockB)
    (live : before.cur = some block) (lookup : before.blocks[block]? = some body)
    (parents : Array (Option ScopeId)) :
    let after := (lowerStmt (some ⟨depth, exit, .next header type counter⟩) (.cont origin) env before).2
    after.cur = none ∧ ∃ afterBody, after.blocks[block]? = some afterBody ∧
      ScopeTrace parents before.stack (afterBody.insts.toList.drop body.insts.size)
        (before.stack.drop (before.stack.length - depth)) := by
  have emitted := leaveTo_emitted depth env before block body live lookup
  dsimp only at emitted ⊢
  have current : (leaveTo depth env before).2.cur = some block := emitted.1.trans live
  simp only [lowerStmt, bind_run]
  have currentNext : (emitDef (.next type counter) env (leaveTo depth env before).2).2.cur = some block := by
    rw [emitDef_run _ _ current]
    exact current
  rw [emitTerm_run _ _ currentNext]
  rw [emitDef_run _ _ current]
  dsimp only
  let leaves : Array Inst := ((before.stack.take (before.stack.length - depth)).map
    fun scope => Inst.eff (.leave scope)).toArray
  let value := (leaveTo depth env before).2.vals.size
  let afterBody : BlockB := { body with insts := ((body.insts ++ leaves).push (.def value (.next type counter))).push (.term (.br header [value])) }
  refine ⟨rfl, afterBody, ?_, ?_⟩
  · simp [afterBody, value, leaves, Array.getElem?_modify, emitted.2.2.2]
  · have trace := (ScopeTrace.leaveTo parents before.stack depth).append
      (.neutral (inst := .def (leaveTo depth env before).2.vals.size (.next type counter)) rfl
        (.neutral (inst := .term (.br header [(leaveTo depth env before).2.vals.size])) rfl (.nil _)))
    simpa [afterBody, value, leaves, List.drop_append] using trace

end Goose.Lower.Validation
