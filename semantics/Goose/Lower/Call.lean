import Goose.Lower.Arguments
import Goose.Proofs.Lower
import Goose.Core.Sound.Stops

namespace Goose.Lower

open Goose.Core Goose.GIR
open Goose.Proofs.Lower (Agree enterFn_nil callFn_nil extT_finish startLS startLS_pp
  bodyTail lowerImplAt_blocks bodyTail_cases)

theorem implOfContext_run (c : ContextId) (le : LEnv) (ls : LS) :
    implOfContext c le ls = (((le.mod.contexts[c]?).map (·.impl)).getD 0, ls) := rfl

theorem implOfContext_lookup {m : Core.Module} {c : ContextId} {ctx : Context}
    (hctx : m.contexts[c]? = some ctx) (vars : Array LocalVar) (ls : LS) :
    implOfContext c (lowerEnv m vars) ls = (ctx.impl, ls) := by
  simp [implOfContext_run, lowerEnv, hctx]

theorem lookupFn_lower {m : Core.Module} {i : ImplId} {impl : Impl}
    (hi : m.impls[i]? = some impl) (profile : NumProfile) :
    lookupFn ⟨profile, lower m⟩ i = pure (lowerImplAt m i impl) := by
  simp [lookupFn, lower, Array.getElem?_mapIdx, hi]

def CalleeCallClaim (n : Nat) (cfg : Cfg) (c : ContextId) : Prop :=
  ∀ depth vals state,
    Agree (enterCall n cfg depth c vals)
      (fun fuel => callFn fuel ⟨cfg.profile, lower cfg.mod⟩ depth
        (((cfg.mod.contexts[c]?).map (·.impl)).getD 0) vals) state

private theorem agree_timeout {α : Type} (g : Nat → M α) (s : St) :
    Agree (timeout : M α) g s := by
  refine ⟨fun a after h => ?_, fun err after h hf => ?_⟩
  · simp [Goose.Core.timeout, M.stop] at h
  · simp [Goose.Core.timeout, M.stop] at h
    obtain ⟨rfl, _⟩ := h
    simp [IsFinal] at hf

private theorem agree_fault {α : Type} (k : FaultKind) (g : Nat → M α) (s : St) :
    Agree (fault k : M α) g s := by
  refine ⟨fun a after h => ?_, fun err after h hf => ?_⟩
  · simp [Goose.Core.fault, M.stop] at h
  · simp [Goose.Core.fault, M.stop] at h
    obtain ⟨rfl, _⟩ := h
    simp [IsFinal] at hf

theorem calleeCallClaim_zero (cfg : Cfg) (c : ContextId) : CalleeCallClaim 0 cfg c := by
  intro depth vals state
  simp only [enterCall]
  exact agree_timeout _ _

theorem enterCall_noReturn_never (cfg : Cfg) (c : ContextId)
    (h : cfg.mod.noReturn c = true) (n depth : Nat) (vals : List Val) :
    Core.Sound.Never (enterCall n cfg depth c vals) :=
  Core.Sound.noReturn_sound cfg.mod cfg.profile c h n depth vals

theorem call_noReturn_post {cfg : Cfg} {c : ContextId} {n depth : Nat} {vals : List Val}
    (hnr : cfg.mod.noReturn c = true) {cx : FnCtx} {pt : Pt} {fr : Frame}
    {post : Val → Pt → Frame → Prop}
    (h : SimG cx pt fr (enterCall n cfg depth c vals) post) :
    SimG cx pt fr (enterCall n cfg depth c vals) (fun _ _ _ => False) := by
  intro state
  exact ⟨fun value after hv =>
    (enterCall_noReturn_never cfg c hnr n depth vals state value after hv).elim,
    (h state).2⟩

theorem enterCall_nil_at (cfg : Cfg) (n depth : Nat) (hd : ¬ depth ≥ maxCallDepth)
    (c : ContextId) (ctx : Context) (impl : Impl)
    (hctx : cfg.mod.contexts[c]? = some ctx) (himpl : cfg.mod.impls[ctx.impl]? = some impl)
    (hp : impl.params = #[]) :
    enterCall (n + 1) cfg depth c [] =
      (freshAct >>= fun act =>
        execBlock n cfg ⟨impl.vars, act, [], depth + 1⟩ [] impl.body >>= expectReturned) := by
  simp [enterCall, hd, lookupContext, lookupImpl, hctx, himpl, hp]

theorem call_nil_agree (m : Core.Module) (c : ContextId) (ctx : Context) (impl : Impl)
    (depth : Nat) (hd : ¬ depth ≥ maxCallDepth)
    (hctx : m.contexts[c]? = some ctx) (himpl : m.impls[ctx.impl]? = some impl)
    (hp : impl.params = #[]) (hb : blockOk impl.body = true) (p : NumProfile) (n : Nat) (s : St) :
    Agree (enterCall n ⟨p, m⟩ depth c [])
      (fun k => callFn k ⟨p, lower m⟩ depth (((m.contexts[c]?).map (·.impl)).getD 0) []) s := by
  cases n with
  | zero =>
    refine ⟨fun a s1 h => ?_, fun e s1 h hf => ?_⟩
    · simp [enterCall, Goose.Core.timeout, M.stop] at h
    · simp [enterCall, Goose.Core.timeout, M.stop] at h
      obtain ⟨rfl, _⟩ := h
      exact absurd hf (by simp [IsFinal])
  | succ n' =>
    have hent : ((m.contexts[c]?).map (·.impl)).getD 0 = ctx.impl := by simp [hctx]
    have hfn : (lower m).funcs[ctx.impl]? = some (lowerImplAt m ctx.impl impl) := by
      simp [lower, himpl]
    rw [hent]
    rw [enterCall_nil_at ⟨p, m⟩ n' depth hd c ctx impl hctx himpl hp]
    let le := lowerEnv m impl.vars
    have hlow : lowerBlock none [] false impl.body le startLS =
        ((lowerBlock none [] false impl.body le startLS).1,
          (lowerBlock none [] false impl.body le startLS).2) := rfl
    generalize hr : (lowerBlock none [] false impl.body le startLS).1 = r at hlow
    generalize hl1 : (lowerBlock none [] false impl.body le startLS).2 = ls1 at hlow
    have hT : (lowerImplAt m ctx.impl impl).blocks = finishBlocks (bodyTail impl le r ls1).blocks := by
      rw [lowerImplAt_blocks m ctx.impl impl hp, hr, hl1]
    let cx : FnCtx := ⟨⟨p, lower m⟩, lowerImplAt m ctx.impl impl⟩
    have hextE : ExtT (bodyTail impl le r ls1) cx.fn.blocks := by
      show ExtT _ (lowerImplAt m ctx.impl impl).blocks
      rw [hT]; exact extT_finish _
    have hext1 : ExtT ls1 cx.fn.blocks :=
      hextE.of_adv (advB_finishFunction impl r le ls1
        (finishFunction impl r le ls1).1 (bodyTail impl le r ls1) rfl)
    have hext0 : ExtT startLS cx.fn.blocks := hext1.of_adv (advB_lowerBlock none [] false impl.body _ _ _ _ hlow)
    obtain ⟨blk0, hb0, hb0p⟩ := hext0.params (b := 0) (blk := ⟨[], #[]⟩) rfl
    have hb0p' : blk0.params = [] := hb0p
    have hpar : (lowerImplAt m ctx.impl impl).params = [] := by simp [lowerImplAt, hp]
    have hrel0 : ∀ act, Rel (⟨p, m⟩ : Cfg) (⟨impl.vars, act, [], depth + 1⟩ : Env) cx
        (⟨act, [], {}, depth + 1⟩ : Frame) startLS := fun act => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hclaim := (claims n').block none false impl.body hb le startLS r ls1 (0, 0) ⟨p, m⟩
      ⟨impl.vars, s.nextAct, [], depth + 1⟩ cx ⟨s.nextAct, [], {}, depth + 1⟩ hlow startLS_pp hext1 (hrel0 s.nextAct)
    have hclaim' := hclaim { s with nextAct := s.nextAct + 1 }
    have hcall : ∀ k0 : Nat, callFn (k0 + 2) ⟨p, lower m⟩ depth ctx.impl [] s =
        runAt cx (0, 0) ⟨s.nextAct, [], {}, depth + 1⟩ k0 { s with nextAct := s.nextAct + 1 } := by
      intro k0
      rw [show k0 + 2 = (k0 + 1) + 1 from rfl, callFn_nil _ _ _ hd _ _ hfn]
      exact enterFn_nil _ _ _ _ _ hpar hb0 hb0p'
    refine ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
    · have hc' : (execBlock n' ⟨p, m⟩ ⟨impl.vars, s.nextAct, [], depth + 1⟩ [] impl.body >>= expectReturned)
          { s with nextAct := s.nextAct + 1 } = .ok a s1 := hc
      rw [bind_apply] at hc'
      cases hcb : execBlock n' ⟨p, m⟩ ⟨impl.vars, s.nextAct, [], depth + 1⟩ [] impl.body
          { s with nextAct := s.nextAct + 1 } with
      | stop e s2 => rw [hcb] at hc'; cases hc'
      | ok flow s2 =>
        rw [hcb] at hc'
        obtain ⟨pt', fr', kk, ⟨v, hf, hU, P⟩, hrun⟩ := hclaim'.1 flow s2 hcb
        subst hf
        simp only [expectReturned, pure_apply] at hc'
        obtain ⟨rfl, rfl⟩ := Res.ok.inj hc'
        have hdiv := execBlock_success_not_divergent n' ⟨p, m⟩
          ⟨impl.vars, s.nextAct, [], depth + 1⟩ impl.body hb
          { s with nextAct := s.nextAct + 1 } s2 (.normal v) hcb
        rcases bodyTail_cases impl le r ls1 hdiv with ⟨hnone, -⟩ | ⟨b, hcur, hemit⟩
        · obtain ⟨blk, hc1, -⟩ := LS.pp_some P.pp
          rw [hnone] at hc1; cases hc1
        obtain ⟨-, -, -, hinst⟩ := emitTerm_facts hemit P.pp hextE
        refine ⟨kk + 3, fun k hk => ?_⟩
        obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 2 := ⟨k - 2, by omega⟩
        show callFn (k0 + 2) ⟨p, lower m⟩ depth (ctx.impl) [] s = _
        rw [hcall k0]
        obtain ⟨j, rfl⟩ : ∃ j, k0 = (j + 1) + kk := ⟨k0 - kk - 1, by omega⟩
        rw [hrun (j + 1)]
        cases hv : impl.body.value.isSome with
        | true =>
          have hcell : fr'.vals[r]? = some (.val v) := by
            refine P.has (r, .val v) ?_
            simp [blockCells, hv]
          have hi' : instAt cx.fn pt' = some (.term (.ret [r] none)) := by
            have := hinst; simp only [hv, ↓reduceIte] at this; exact this
          rw [runAt_ret1 hi' hcell j]
          rfl
        | false =>
          have hnone : impl.body.value = none := by simpa using hv
          have hi' : instAt cx.fn pt' = some (.term (.ret [] none)) := by
            have := hinst; simp only [hv, Bool.false_eq_true, ↓reduceIte] at this; exact this
          rw [runAt_ret0 hi' j, hU hnone]
          rfl
    · have hc' : (execBlock n' ⟨p, m⟩ ⟨impl.vars, s.nextAct, [], depth + 1⟩ [] impl.body >>= expectReturned)
          { s with nextAct := s.nextAct + 1 } = .stop e s1 := hc
      rw [bind_apply] at hc'
      cases hcb : execBlock n' ⟨p, m⟩ ⟨impl.vars, s.nextAct, [], depth + 1⟩ [] impl.body
          { s with nextAct := s.nextAct + 1 } with
      | stop e2 s2 =>
        rw [hcb] at hc'
        obtain ⟨rfl, rfl⟩ := Res.stop.inj hc'
        obtain ⟨kk, hrun⟩ := hclaim'.2 e2 s2 hcb hf
        refine ⟨kk + 2, fun k hk => ?_⟩
        obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 2 := ⟨k - 2, by omega⟩
        show callFn (k0 + 2) ⟨p, lower m⟩ depth (ctx.impl) [] s = _
        rw [hcall k0]
        obtain ⟨j, rfl⟩ : ∃ j, k0 = j + kk := ⟨k0 - kk, by omega⟩
        rw [hrun j]
      | ok flow s2 =>
        rw [hcb] at hc'
        obtain ⟨pt', fr', kk, ⟨v, hf', hU, P⟩, hrun⟩ := hclaim'.1 flow s2 hcb
        subst hf'
        simp only [expectReturned, pure_apply] at hc'
        cases hc'

theorem calleeCallClaim_nil {m : Core.Module} {c : ContextId} {ctx : Context} {impl : Impl}
    (hctx : m.contexts[c]? = some ctx) (himpl : m.impls[ctx.impl]? = some impl)
    (hp : impl.params = #[]) (hb : blockOk impl.body = true) (p : NumProfile) (n : Nat) :
    CalleeCallClaim n ⟨p, m⟩ c := by
  intro depth vals state
  cases n with
  | zero => exact calleeCallClaim_zero _ _ depth vals state
  | succ n =>
    by_cases hd : depth ≥ maxCallDepth
    · simp only [enterCall, hd, ite_true]
      exact agree_timeout _ _
    · cases vals with
      | nil => exact call_nil_agree m c ctx impl depth hd hctx himpl hp hb p (n + 1) state
      | cons v vals =>
        simp only [enterCall, hd, ite_false, lookupContext, lookupImpl, hctx, himpl,
          pure_bind, hp, Array.size_empty, List.length_cons, Nat.zero_ne_add_one, ite_false]
        exact agree_fault _ _ _

end Goose.Lower
