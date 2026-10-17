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

end Goose.Lower.Validation
