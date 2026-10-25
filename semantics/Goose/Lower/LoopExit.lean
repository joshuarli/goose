import Goose.Lower.Unwind

namespace Goose.Lower

open Goose.Core Goose.GIR

def prepareLoopExit (env : Env) (depth : Nat) : Flow → M Flow
  | .brk => do
    releaseScopes env (env.scopes.take (env.scopes.length - depth))
    pure .brk
  | .cont => do
    releaseScopes env (env.scopes.take (env.scopes.length - depth))
    pure .cont
  | flow => pure flow

structure JumpPost (before : GIR.Frame) (target : BlockId)
    (scopes : List (ScopeId × ScopeInst)) (pt : Pt) (after : GIR.Frame) : Prop where
  point : pt = (target, 0)
  values : after.vals = before.vals
  activation : after.act = before.act
  scopesEqual : after.scopes = scopes
  depth : after.depth = before.depth

theorem leaveTo_jump_sim (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (depth : Nat) (target : BlockId) (ls unwound ls' : LS) (u r : Unit) (pt : Pt) (fr : GIR.Frame)
    (hrel : Rel cfg env cx fr ls) (hleave : leaveTo depth le ls = (u, unwound))
    (hterm : emitTerm (.br target []) le unwound = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks)
    (htarget : ∃ block, cx.fn.blocks[target]? = some block ∧ block.params = []) :
    SimG cx pt fr (releaseScopes env (env.scopes.take (env.scopes.length - depth)))
      (fun _ pt' fr' => JumpPost fr target (env.scopes.drop (env.scopes.length - depth)) pt' fr') := by
  have hextUnwound := hext.of_adv (adv_emitTerm hterm)
  refine SimG.mono_goes (leaveTo_sim cfg env cx le depth ls unwound u pt fr
    hrel hleave hpp hextUnwound) fun _ ptUnwound frUnwound hpost => ?_
  obtain ⟨_, _, _, hinst⟩ := emitTerm_facts hterm hpost.pp hext
  obtain ⟨block, hblock, hparams⟩ := htarget
  exact ⟨(target, 0), frUnwound, goes_br0 hinst hblock hparams,
    ⟨rfl, hpost.values, hpost.activation, hpost.scopes, hpost.depth⟩⟩

theorem stmt_brk_prepared_sim (n : Nat) (loop : LoopCtx) (org : OriginId)
    (le : LEnv) (ls ls' : LS) (r : Unit) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : GIR.Frame) (hlow : lowerStmt (some loop) (.brk org) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (htarget : ∃ block, cx.fn.blocks[loop.breakTo]? = some block ∧ block.params = []) :
    SimG cx pt fr (execStmt n cfg env (.brk org) >>= prepareLoopExit env loop.depth)
      (fun flow pt' fr' => flow = .brk ∧
        JumpPost fr loop.breakTo (env.scopes.drop (env.scopes.length - loop.depth)) pt' fr') := by
  cases n with
  | zero => simp only [execStmt]; exact SimG.of_timeout_bind
  | succ n =>
    simp only [lowerStmt, bind_eq] at hlow
    obtain ⟨u, unwound, hleave, hterm⟩ := hlow
    simp only [execStmt, pure_bind, prepareLoopExit]
    refine SimG.bind (leaveTo_jump_sim cfg env cx le loop.depth loop.breakTo ls unwound ls' u r
      pt fr hrel hleave hterm hpp hext htarget) fun _ pt' fr' hpost => ?_
    exact SimG.ret ⟨rfl, hpost⟩

theorem stmt_cont_jump_prepared_sim (n : Nat) (loop : LoopCtx) (header : BlockId) (org : OriginId)
    (hheader : loop.cont = .jump header)
    (le : LEnv) (ls ls' : LS) (r : Unit) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : GIR.Frame) (hlow : lowerStmt (some loop) (.cont org) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (htarget : ∃ block, cx.fn.blocks[header]? = some block ∧ block.params = []) :
    SimG cx pt fr (execStmt n cfg env (.cont org) >>= prepareLoopExit env loop.depth)
      (fun flow pt' fr' => flow = .cont ∧
        JumpPost fr header (env.scopes.drop (env.scopes.length - loop.depth)) pt' fr') := by
  cases n with
  | zero => simp only [execStmt]; exact SimG.of_timeout_bind
  | succ n =>
    simp only [lowerStmt, hheader, bind_eq] at hlow
    obtain ⟨u, unwound, hleave, hterm⟩ := hlow
    simp only [execStmt, pure_bind, prepareLoopExit]
    refine SimG.bind (leaveTo_jump_sim cfg env cx le loop.depth header ls unwound ls' u r
      pt fr hrel hleave hterm hpp hext htarget) fun _ pt' fr' hpost => ?_
    exact SimG.ret ⟨rfl, hpost⟩

structure NextJumpPost (before : GIR.Frame) (header : BlockId) (counter : ValueId) (t : IntTy) (current : Int)
    (scopes : List (ScopeId × ScopeInst)) (pt : Pt) (after : GIR.Frame) : Prop where
  point : pt = (header, 0)
  values : Same counter before after
  counterValue : after.vals[counter]? = some (.val (.int t (current + 1)))
  activation : after.act = before.act
  scopesEqual : after.scopes = scopes
  depth : after.depth = before.depth

theorem stmt_cont_next_prepared_sim (n : Nat) (loop : LoopCtx) (header : BlockId)
    (hint t : IntTy) (counter : ValueId) (current : Int) (org : OriginId)
    (hheader : loop.cont = .next header hint counter)
    (le : LEnv) (ls ls' : LS) (r : Unit) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : GIR.Frame) (hcounter : fr.vals[counter]? = some (.val (.int t current)))
    (hcounterBound : counter < ls.vals.size)
    (hlow : lowerStmt (some loop) (.cont org) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (htarget : ∃ block, cx.fn.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int hint))]) :
    SimG cx pt fr (execStmt n cfg env (.cont org) >>= prepareLoopExit env loop.depth)
      (fun flow pt' fr' => flow = .cont ∧ NextJumpPost fr header counter t current
        (env.scopes.drop (env.scopes.length - loop.depth)) pt' fr') := by
  cases n with
  | zero => simp only [execStmt]; exact SimG.of_timeout_bind
  | succ n =>
    simp only [lowerStmt, hheader, bind_eq] at hlow
    obtain ⟨u, unwound, hleave, next, advanced, hnext, hterm⟩ := hlow
    have hextAdvanced := hext.of_adv (adv_emitTerm hterm)
    have hextUnwound := hextAdvanced.of_adv (adv_emitDef hnext)
    have hsim := leaveTo_sim cfg env cx le loop.depth ls unwound u pt fr
      hrel hleave hpp hextUnwound
    simp only [execStmt, pure_bind, prepareLoopExit]
    refine SimG.bind hsim fun _ ptUnwound frUnwound hunwind => ?_
    obtain ⟨hnextId, _, _, hppAdvanced, hnextInst⟩ := emitDef_facts hnext hunwind.pp hextAdvanced
    obtain ⟨_, _, _, htermInst⟩ := emitTerm_facts hterm hppAdvanced hext
    have hcounterUnwound : frUnwound.vals[counter]? = some (.val (.int t current)) := by
      rw [hunwind.values]
      exact hcounter
    have hnextPure : execPure cx frUnwound (.next hint counter) =
        pure (.val (.int t (current + 1))) := by
      simp [execPure, getVal_of hcounterUnwound, expectInt]
    have gnext := Goes.def_pure hnextInst (by simp) hnextPure
    obtain ⟨block, hblock, hparams⟩ := htarget
    let frNext := frUnwound.set next (.val (.int t (current + 1)))
    let frHeader := frNext.set counter (.val (.int t (current + 1)))
    have hnextCell : frNext.vals[next]? = some (.val (.int t (current + 1))) :=
      Frame.set_get _ _ _
    have gheader := goes_br1 htermInst hblock hparams hnextCell
    refine SimG.goes (gnext.trans gheader) (SimG.ret ?_)
    have hcounterNext : counter < next := by
      rw [hnextId, hunwind.builderValues]
      exact hcounterBound
    have hsameUnwound : Same counter fr frUnwound := by
      intro id _
      rw [hunwind.values]
    have hsameNext : Same counter frUnwound frNext :=
      Same.set frUnwound (Nat.le_of_lt hcounterNext) _
    have hsameHeader : Same counter frNext frHeader := Same.set frNext (Nat.le_refl _) _
    exact ⟨rfl, ⟨rfl, hsameUnwound.trans (hsameNext.trans hsameHeader (Nat.le_refl _))
      (Nat.le_refl _), Frame.set_get _ _ _, hunwind.activation, hunwind.scopes, hunwind.depth⟩⟩

end Goose.Lower
