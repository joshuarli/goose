import Goose.Lower.Claims

/-!
The lowering preserves the meaning of Core modules in a fragment: every run of the Core
evaluator that finishes is matched by a run of the lowered module's interpreter at some fuel.
-/

namespace Goose.Proofs.Lower

open Goose.Core Goose.GIR Goose.Lower

/-- The computation `c` finishes in a state, or stops by an abort or an exit, and then `g k`
does the same in the same state for every large enough `k`. -/
def Agree (c : M α) (g : Nat → M α) (s : St) : Prop :=
  (∀ a s1, c s = .ok a s1 → ∃ K, ∀ k, K ≤ k → g k s = .ok a s1) ∧
  (∀ e s1, c s = .stop e s1 → IsFinal e → ∃ K, ∀ k, K ≤ k → g k s = .stop e s1)

theorem Agree.bind {c1 : M α} {g1 : Nat → M α} {c2 : α → M β} {g2 : α → Nat → M β} {s : St}
    (h1 : Agree c1 g1 s) (h2 : ∀ a s1, c1 s = .ok a s1 → Agree (c2 a) (g2 a) s1) :
    Agree (c1 >>= c2) (fun k => g1 k >>= fun a => g2 a k) s := by
  refine ⟨fun b s2 hc => ?_, fun e s2 hc hf => ?_⟩
  · rw [bind_apply] at hc
    cases hc1 : c1 s with
    | stop e s1 => rw [hc1] at hc; cases hc
    | ok a s1 =>
      rw [hc1] at hc
      obtain ⟨K1, hK1⟩ := h1.1 a s1 hc1
      obtain ⟨K2, hK2⟩ := (h2 a s1 hc1).1 b s2 hc
      refine ⟨max K1 K2, fun k hk => ?_⟩
      show (g1 k >>= fun a => g2 a k) s = _
      rw [bind_apply, hK1 k (Nat.le_trans (Nat.le_max_left _ _) hk)]
      exact hK2 k (Nat.le_trans (Nat.le_max_right _ _) hk)
  · rw [bind_apply] at hc
    cases hc1 : c1 s with
    | stop e1 s1 =>
      rw [hc1] at hc
      cases hc
      obtain ⟨K1, hK1⟩ := h1.2 e s2 hc1 hf
      refine ⟨K1, fun k hk => ?_⟩
      show (g1 k >>= fun a => g2 a k) s = _
      rw [bind_apply, hK1 k hk]
    | ok a s1 =>
      rw [hc1] at hc
      obtain ⟨K1, hK1⟩ := h1.1 a s1 hc1
      obtain ⟨K2, hK2⟩ := (h2 a s1 hc1).2 e s2 hc hf
      refine ⟨max K1 K2, fun k hk => ?_⟩
      show (g1 k >>= fun a => g2 a k) s = _
      rw [bind_apply, hK1 k (Nat.le_trans (Nat.le_max_left _ _) hk)]
      exact hK2 k (Nat.le_trans (Nat.le_max_right _ _) hk)

theorem Agree.refl (c : M α) (s : St) : Agree c (fun _ => c) s :=
  ⟨fun a s1 h => ⟨0, fun _ _ => h⟩, fun e s1 h _ => ⟨0, fun _ _ => h⟩⟩

/-- A function with no parameter whose entry block has none: running it from the start. -/
theorem enterFn_nil (cfg : GCfg) (fn : Func) (depth k0 : Nat) (s : St) {blk : GIR.Block}
    (hp : fn.params = []) (hb : fn.blocks[0]? = some blk) (hbp : blk.params = []) :
    enterFn (k0 + 1) cfg depth fn [] s =
      runAt ⟨cfg, fn⟩ (0, 0) ⟨s.nextAct, [], {}, depth⟩ k0 { s with nextAct := s.nextAct + 1 } := by
  have hi : instsAt fn (0, 0) = blk.insts := by simp [instsAt, hb]
  simp only [enterFn, hp, List.length_nil, List.map_nil, ↓reduceIte, enterBlock, hb, hbp, bindParams,
    pure_bind, runAt, hi]
  rfl

theorem callFn_nil (cfg : GCfg) (depth k : Nat) (hd : ¬ depth ≥ maxCallDepth) (f : FnId) (fn : Func)
    (hf : cfg.mod.funcs[f]? = some fn) (s : St) :
    callFn (k + 1) cfg depth f [] s = enterFn k cfg (depth + 1) fn [] s := by
  simp [callFn, hd, lookupFn, hf]

theorem extT_finish (ls : LS) : ExtT ls (finishBlocks ls.blocks) := by
  refine ⟨by simp [finishBlocks], fun i blk hi => ?_⟩
  refine ⟨⟨blk.params, blk.insts.toList⟩, ?_, rfl, [], by simp⟩
  simp [finishBlocks, Array.getElem?_map, hi]

/-- The state at the start of a function whose entry block has no parameter. -/
def startLS : LS := { blocks := #[⟨[], #[]⟩], vals := #[], cur := some 0, stack := [] }

theorem startLS_pp : startLS.pp = some (0, 0) := rfl

theorem lowerGlobal_blocks (m : Core.Module) (g : Core.Global) :
    (lowerGlobal m g).init.blocks = finishBlocks (emitTerm
      (.ret [(lowerExpr g.init (lowerEnv m #[]) startLS).1] (some g.org)) (lowerEnv m #[])
      (lowerExpr g.init (lowerEnv m #[]) startLS).2).2.blocks := rfl

theorem global_agree (m : Core.Module) (gl : Core.Global) (hg : exprOk gl.init = true) (p : NumProfile)
    (n : Nat) (s : St) :
    Agree (freshAct >>= fun act => evalExpr n ⟨p, m⟩ ⟨#[], act, [], 0⟩ gl.init)
      (fun k => enterFn k ⟨p, lower m⟩ 0 (lowerGlobal m gl).init []) s := by
  let le := lowerEnv m #[]
  have hlow : lowerExpr gl.init le startLS =
      ((lowerExpr gl.init le startLS).1, (lowerExpr gl.init le startLS).2) := rfl
  generalize hr : (lowerExpr gl.init le startLS).1 = r at hlow
  generalize hl1 : (lowerExpr gl.init le startLS).2 = ls1 at hlow
  have hT : (lowerGlobal m gl).init.blocks = finishBlocks (emitTerm (.ret [r] (some gl.org)) le ls1).2.blocks := by
    rw [lowerGlobal_blocks, hr, hl1]
  generalize hl2 : (emitTerm (.ret [r] (some gl.org)) le ls1).2 = ls2 at hT
  have hemit : emitTerm (.ret [r] (some gl.org)) le ls1 = ((), ls2) := by rw [← hl2]
  let cx : FnCtx := ⟨⟨p, lower m⟩, (lowerGlobal m gl).init⟩
  have hext2 : ExtT ls2 cx.fn.blocks := by show ExtT ls2 (lowerGlobal m gl).init.blocks; rw [hT]; exact extT_finish ls2
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (adv_emitTerm hemit)
  have hext0 : ExtT startLS cx.fn.blocks := hext1.of_adv (advB_lowerExpr gl.init _ _ _ _ hlow)
  obtain ⟨blk0, hb0, hb0p⟩ := hext0.params (b := 0) (blk := ⟨[], #[]⟩) rfl
  have hb0p' : blk0.params = [] := hb0p
  have hrel0 : ∀ act, Rel (⟨p, m⟩ : Cfg) (⟨#[], act, [], 0⟩ : Env) cx (⟨act, [], {}, 0⟩ : Frame) startLS :=
    fun act => ⟨rfl, by simp [cx, lowerGlobal], rfl, rfl, rfl, rfl⟩
  have hinit : (lowerGlobal m gl).init.params = [] := rfl
  have hclaim := (claims n).expr gl.init hg le startLS r ls1 (0, 0) ⟨p, m⟩ ⟨#[], s.nextAct, [], 0⟩ cx
    ⟨s.nextAct, [], {}, 0⟩ hlow startLS_pp hext1 (hrel0 s.nextAct)
  have hclaim' := hclaim { s with nextAct := s.nextAct + 1 }
  refine ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
  · have hc' : evalExpr n ⟨p, m⟩ ⟨#[], s.nextAct, [], 0⟩ gl.init { s with nextAct := s.nextAct + 1 } =
        .ok a s1 := hc
    obtain ⟨pt', fr', kk, P, hrun⟩ := hclaim'.1 a s1 hc'
    obtain ⟨-, -, -, hi⟩ := emitTerm_facts hemit P.pp hext2
    have hcell : fr'.vals[r]? = some (.val a) := P.has (r, _) (by simp)
    have hi' : instAt cx.fn pt' = some (.term (.ret [r] (some gl.org))) := hi
    refine ⟨kk + 2, fun k hk => ?_⟩
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    show enterFn (k0 + 1) ⟨p, lower m⟩ 0 (lowerGlobal m gl).init [] s = _
    rw [enterFn_nil _ _ _ _ _ hinit hb0 hb0p']
    obtain ⟨j, rfl⟩ : ∃ j, k0 = (j + 1) + kk := ⟨k0 - kk - 1, by omega⟩
    show runAt cx (0, 0) _ _ _ = _
    rw [hrun (j + 1), runAt_ret1 hi' hcell j]
    rfl
  · obtain ⟨kk, hrun⟩ := hclaim'.2 e s1 hc hf
    refine ⟨kk + 2, fun k hk => ?_⟩
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    show enterFn (k0 + 1) ⟨p, lower m⟩ 0 (lowerGlobal m gl).init [] s = _
    rw [enterFn_nil _ _ _ _ _ hinit hb0 hb0p']
    obtain ⟨j, rfl⟩ : ∃ j, k0 = j + kk := ⟨k0 - kk, by omega⟩
    show runAt cx (0, 0) _ _ _ = _
    rw [hrun j]

theorem enterCall_nil (cfg : Cfg) (n : Nat) (c : ContextId) (ctx : Context) (impl : Impl)
    (hctx : cfg.mod.contexts[c]? = some ctx) (himpl : cfg.mod.impls[ctx.impl]? = some impl)
    (hp : impl.params = #[]) :
    enterCall (n + 1) cfg 0 c [] =
      (freshAct >>= fun act =>
        execBlock n cfg ⟨impl.vars, act, [], 0 + 1⟩ [] impl.body >>= expectReturned) := by
  have hmaxd : ¬ ((0 : Nat) ≥ maxCallDepth) := by simp [maxCallDepth]
  simp [enterCall, hmaxd, lookupContext, lookupImpl, hctx, himpl, hp]

/-- What follows a function body in the lowering: a return, unless the body ended every path. -/
def bodyTail (impl : Impl) (le : LEnv) (v : ValueId) (ls1 : LS) : LS :=
  ((do
    if (← isLive) then
      emitTerm (.ret (if impl.body.value.isSome then [v] else []) none) : B Unit) le ls1).2

theorem lowerImpl_blocks (m : Core.Module) (impl : Impl) (hp : impl.params = #[]) :
    (lowerImpl m impl).blocks = finishBlocks (bodyTail impl (lowerEnv m impl.vars)
      (lowerBlock none [] false impl.body (lowerEnv m impl.vars) startLS).1
      (lowerBlock none [] false impl.body (lowerEnv m impl.vars) startLS).2).blocks := by
  rcases impl with ⟨name, params, results, vars, body, summary⟩
  simp only at hp
  subst hp
  rfl

theorem bodyTail_cases (impl : Impl) (le : LEnv) (v : ValueId) (ls1 : LS) :
    (ls1.cur = none ∧ bodyTail impl le v ls1 = ls1) ∨
    (∃ b, ls1.cur = some b ∧
      emitTerm (.ret (if impl.body.value.isSome then [v] else []) none) le ls1 =
        ((), bodyTail impl le v ls1)) := by
  cases hc : ls1.cur with
  | none =>
    left
    refine ⟨rfl, ?_⟩
    unfold bodyTail
    simp [bind_run, isLive_none hc, pure_run]
  | some b =>
    right
    refine ⟨b, rfl, ?_⟩
    unfold bodyTail
    simp [bind_run, isLive_run hc]

theorem entry_agree (m : Core.Module) (ctx : Context) (impl : Impl)
    (hctx : m.contexts[m.entry]? = some ctx) (himpl : m.impls[ctx.impl]? = some impl)
    (hp : impl.params = #[]) (hb : blockOk impl.body = true) (p : NumProfile) (n : Nat) (s : St) :
    Agree (enterCall n ⟨p, m⟩ 0 m.entry [])
      (fun k => callFn k ⟨p, lower m⟩ 0 (((m.contexts[m.entry]?).map (·.impl)).getD 0) []) s := by
  cases n with
  | zero =>
    refine ⟨fun a s1 h => ?_, fun e s1 h hf => ?_⟩
    · simp [enterCall, Goose.Core.timeout, M.stop] at h
    · simp [enterCall, Goose.Core.timeout, M.stop] at h
      obtain ⟨rfl, _⟩ := h
      exact absurd hf (by simp [IsFinal])
  | succ n' =>
    have hent : ((m.contexts[m.entry]?).map (·.impl)).getD 0 = ctx.impl := by simp [hctx]
    have hfn : (lower m).funcs[ctx.impl]? = some (lowerImpl m impl) := by simp [lower, himpl]
    have hmaxd : ¬ ((0 : Nat) ≥ maxCallDepth) := by simp [maxCallDepth]
    rw [hent]
    rw [enterCall_nil ⟨p, m⟩ n' m.entry ctx impl hctx himpl hp]
    let le := lowerEnv m impl.vars
    have hlow : lowerBlock none [] false impl.body le startLS =
        ((lowerBlock none [] false impl.body le startLS).1,
          (lowerBlock none [] false impl.body le startLS).2) := rfl
    generalize hr : (lowerBlock none [] false impl.body le startLS).1 = r at hlow
    generalize hl1 : (lowerBlock none [] false impl.body le startLS).2 = ls1 at hlow
    have hT : (lowerImpl m impl).blocks = finishBlocks (bodyTail impl le r ls1).blocks := by
      rw [lowerImpl_blocks m impl hp, hr, hl1]
    let cx : FnCtx := ⟨⟨p, lower m⟩, lowerImpl m impl⟩
    have hextE : ExtT (bodyTail impl le r ls1) cx.fn.blocks := by
      show ExtT _ (lowerImpl m impl).blocks
      rw [hT]; exact extT_finish _
    have hext1 : ExtT ls1 cx.fn.blocks := by
      rcases bodyTail_cases impl le r ls1 with ⟨-, h⟩ | ⟨b, -, h⟩
      · rw [h] at hextE; exact hextE
      · exact hextE.of_adv (adv_emitTerm h)
    have hext0 : ExtT startLS cx.fn.blocks := hext1.of_adv (advB_lowerBlock none [] false impl.body _ _ _ _ hlow)
    obtain ⟨blk0, hb0, hb0p⟩ := hext0.params (b := 0) (blk := ⟨[], #[]⟩) rfl
    have hb0p' : blk0.params = [] := hb0p
    have hpar : (lowerImpl m impl).params = [] := by simp [lowerImpl, hp]
    have hrel0 : ∀ act, Rel (⟨p, m⟩ : Cfg) (⟨impl.vars, act, [], 0 + 1⟩ : Env) cx
        (⟨act, [], {}, 0 + 1⟩ : Frame) startLS := fun act => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hclaim := (claims n').block none false impl.body hb le startLS r ls1 (0, 0) ⟨p, m⟩
      ⟨impl.vars, s.nextAct, [], 0 + 1⟩ cx ⟨s.nextAct, [], {}, 0 + 1⟩ hlow startLS_pp hext1 (hrel0 s.nextAct)
    have hclaim' := hclaim { s with nextAct := s.nextAct + 1 }
    have hcall : ∀ k0 : Nat, callFn (k0 + 2) ⟨p, lower m⟩ 0 ctx.impl [] s =
        runAt cx (0, 0) ⟨s.nextAct, [], {}, 0 + 1⟩ k0 { s with nextAct := s.nextAct + 1 } := by
      intro k0
      rw [show k0 + 2 = (k0 + 1) + 1 from rfl, callFn_nil _ _ _ hmaxd _ _ hfn]
      exact enterFn_nil _ _ _ _ _ hpar hb0 hb0p'
    refine ⟨fun a s1 hc => ?_, fun e s1 hc hf => ?_⟩
    · have hc' : (execBlock n' ⟨p, m⟩ ⟨impl.vars, s.nextAct, [], 0 + 1⟩ [] impl.body >>= expectReturned)
          { s with nextAct := s.nextAct + 1 } = .ok a s1 := hc
      rw [bind_apply] at hc'
      cases hcb : execBlock n' ⟨p, m⟩ ⟨impl.vars, s.nextAct, [], 0 + 1⟩ [] impl.body
          { s with nextAct := s.nextAct + 1 } with
      | stop e s2 => rw [hcb] at hc'; cases hc'
      | ok flow s2 =>
        rw [hcb] at hc'
        obtain ⟨pt', fr', kk, ⟨v, hf, hU, P⟩, hrun⟩ := hclaim'.1 flow s2 hcb
        subst hf
        simp only [expectReturned, pure_apply] at hc'
        obtain ⟨rfl, rfl⟩ := Res.ok.inj hc'
        rcases bodyTail_cases impl le r ls1 with ⟨hnone, -⟩ | ⟨b, hcur, hemit⟩
        · obtain ⟨blk, hc1, -⟩ := LS.pp_some P.pp
          rw [hnone] at hc1; cases hc1
        obtain ⟨-, -, -, hinst⟩ := emitTerm_facts hemit P.pp hextE
        refine ⟨kk + 3, fun k hk => ?_⟩
        obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 2 := ⟨k - 2, by omega⟩
        show callFn (k0 + 2) ⟨p, lower m⟩ 0 (ctx.impl) [] s = _
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
    · have hc' : (execBlock n' ⟨p, m⟩ ⟨impl.vars, s.nextAct, [], 0 + 1⟩ [] impl.body >>= expectReturned)
          { s with nextAct := s.nextAct + 1 } = .stop e s1 := hc
      rw [bind_apply] at hc'
      cases hcb : execBlock n' ⟨p, m⟩ ⟨impl.vars, s.nextAct, [], 0 + 1⟩ [] impl.body
          { s with nextAct := s.nextAct + 1 } with
      | stop e2 s2 =>
        rw [hcb] at hc'
        obtain ⟨rfl, rfl⟩ := Res.stop.inj hc'
        obtain ⟨kk, hrun⟩ := hclaim'.2 e2 s2 hcb hf
        refine ⟨kk + 2, fun k hk => ?_⟩
        obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 2 := ⟨k - 2, by omega⟩
        show callFn (k0 + 2) ⟨p, lower m⟩ 0 (ctx.impl) [] s = _
        rw [hcall k0]
        obtain ⟨j, rfl⟩ : ∃ j, k0 = j + kk := ⟨k0 - kk, by omega⟩
        rw [hrun j]
      | ok flow s2 =>
        rw [hcb] at hc'
        obtain ⟨pt', fr', kk, ⟨v, hf', hU, P⟩, hrun⟩ := hclaim'.1 flow s2 hcb
        subst hf'
        simp only [expectReturned, pure_apply] at hc'
        cases hc'

theorem initGlobals_agree (m : Core.Module) (p : NumProfile) (n : Nat)
    (hg : ∀ gl ∈ m.globals, exprOk gl.init = true) :
    ∀ (gs : List GlobalId), (∀ g ∈ gs, g < m.globals.size) → ∀ s,
      Agree (Goose.Core.initGlobals n ⟨p, m⟩ gs) (fun k => GIR.initGlobals k ⟨p, lower m⟩ gs) s
  | [], _, s => by
    simp only [Goose.Core.initGlobals, GIR.initGlobals]
    exact Agree.refl _ s
  | g :: rest, hgs, s => by
    have hlt : g < m.globals.size := hgs g (by simp)
    have hgl : m.globals[g]? = some m.globals[g] := by simp [hlt]
    have hlow : (lower m).globals[g]? = some (lowerGlobal m m.globals[g]) := by simp [lower, hlt]
    simp only [Goose.Core.initGlobals, GIR.initGlobals, Goose.Core.lookupGlobal, lookupInit, hgl, hlow,
      pure_bind]
    have hc : (freshAct >>= fun act => evalExpr n ⟨p, m⟩ ⟨#[], act, [], 0⟩ m.globals[g].init >>= fun v =>
        bindRoot (.global g) v >>= fun _ => Goose.Core.initGlobals n ⟨p, m⟩ rest) =
        ((freshAct >>= fun act => evalExpr n ⟨p, m⟩ ⟨#[], act, [], 0⟩ m.globals[g].init) >>= fun v =>
          bindRoot (.global g) v >>= fun _ => Goose.Core.initGlobals n ⟨p, m⟩ rest) := by
      simp [bind_assoc]
    rw [hc]
    exact Agree.bind (global_agree m m.globals[g] (hg _ (by simp)) p n s) fun v s1 _ =>
      Agree.bind (Agree.refl _ s1) fun _ s2 _ =>
        initGlobals_agree m p n hg rest (fun x hx => hgs x (by simp [hx])) s2

/-- The modules the simulation covers: every global's initializer and the entry function are in
the fragment, and the entry takes no parameter. -/
def moduleOk (m : Core.Module) : Bool :=
  m.globals.all (fun g => exprOk g.init) &&
  match m.contexts[m.entry]? with
  | some ctx =>
    match m.impls[ctx.impl]? with
    | some impl => impl.params.isEmpty && blockOk impl.body
    | none => false
  | none => false

theorem runModule_agree (m : Core.Module) (hm : moduleOk m = true) (p : NumProfile) (n : Nat) (s : St) :
    Agree (Goose.Core.runModule n ⟨p, m⟩) (fun k => GIR.runModule k ⟨p, lower m⟩) s := by
  simp only [moduleOk, Bool.and_eq_true] at hm
  obtain ⟨hglob0, hentry⟩ := hm
  have hglob : ∀ gl ∈ m.globals, exprOk gl.init = true := fun gl hgl =>
    (Array.all_eq_true_iff_forall_mem.mp hglob0) gl hgl
  cases hctx : m.contexts[m.entry]? with
  | none => simp [hctx] at hentry
  | some ctx =>
    cases himpl : m.impls[ctx.impl]? with
    | none => simp [hctx, himpl] at hentry
    | some impl =>
      simp only [hctx, himpl, Bool.and_eq_true] at hentry
      obtain ⟨hpe, hb⟩ := hentry
      have hp : impl.params = #[] := by simpa using hpe
      have hsz : (lower m).globals.size = m.globals.size := by simp [lower]
      have hent : (lower m).entry = ((m.contexts[m.entry]?).map (·.impl)).getD 0 := rfl
      simp only [Goose.Core.runModule, GIR.runModule, hsz, hent]
      exact Agree.bind (initGlobals_agree m p n hglob _ (fun g hg => by simpa using hg) s) fun _ s1 _ =>
        Agree.bind (entry_agree m ctx impl hctx himpl hp hb p n s1) fun _ s2 _ =>
          Agree.refl _ s2

/-- Stage one: the lowering preserves the meaning of the modules whose initializers and entry
use structured control (conditionals, short-circuit operators and block values among them), but no
loop, call or return. -/
theorem lower_correct_ctl (m : Core.Module) (hm : moduleOk m = true) (n : Nat) (p : NumProfile)
    (o : Outcome) (t : String) (h : eval n p m = .done o t) :
    ∃ k, GIR.run k p (lower m) = .done o t := by
  have hA := runModule_agree m hm p n St.initial
  unfold eval at h
  unfold GIR.run
  cases hr : Goose.Core.runModule n ⟨p, m⟩ St.initial with
  | ok a s =>
    rw [hr] at h
    simp only [Result.done.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨K, hK⟩ := hA.1 a s hr
    have hK' : GIR.runModule K ⟨p, lower m⟩ St.initial = Res.ok a s := hK K (Nat.le_refl _)
    exact ⟨K, by rw [hK']⟩
  | stop e s =>
    rw [hr] at h
    cases e with
    | abort k org =>
      simp only [Result.done.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨K, hK⟩ := hA.2 _ s hr trivial
      have hK' : GIR.runModule K ⟨p, lower m⟩ St.initial = Res.stop (Stop.abort k org) s :=
        hK K (Nat.le_refl _)
      exact ⟨K, by rw [hK']⟩
    | exit code =>
      simp only [Result.done.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨K, hK⟩ := hA.2 _ s hr trivial
      have hK' : GIR.runModule K ⟨p, lower m⟩ St.initial = Res.stop (Stop.exit code) s :=
        hK K (Nat.le_refl _)
      exact ⟨K, by rw [hK']⟩
    | fault k => simp at h
    | timeout => simp at h

end Goose.Proofs.Lower
