import Goose.Lower.Arguments
import Goose.Proofs.Lower
import Goose.Core.Sound.Stops
import Goose.Lower.Flow
import Goose.Lower.ControlNormal

namespace Goose.Lower

open Goose.Core Goose.GIR
open Goose.Proofs.Lower (Agree enterFn_nil callFn_nil extT_finish startLS startLS_pp
  bodyTail lowerImplAt_blocks bodyTail_cases exceptBind_ok_left coreForAll_ok)

def callEntryTypes (impl : Impl) : List VTy :=
  impl.params.toList.map fun p => .data (tyOfVar impl p.var)

def callEntry (impl : Impl) : LS :=
  { blocks := #[⟨(List.range impl.params.size).zip (callEntryTypes impl), #[]⟩],
    vals := (callEntryTypes impl).foldl (fun a t => a.push (some t)) #[],
    cur := some 0, stack := [] }

def callPre (impl : Impl) : List (SlotId × ValueId × OriginId) :=
  (impl.params.toList.zip (List.range impl.params.size)).map fun (p, v) =>
    (p.var, v, (impl.vars[p.var]?.map (·.org)).getD 0)

theorem callEntry_pp (impl : Impl) : (callEntry impl).pp = some (0, 0) := rfl

theorem lowerImplAt_call_blocks (m : Core.Module) (i : ImplId) (impl : Impl) :
    (lowerImplAt m i impl).blocks =
      finishBlocks (bodyTail impl (lowerEnv m impl.vars impl.results.toList)
        (lowerBlock none (callPre impl) false impl.body (lowerEnv m impl.vars impl.results.toList) (callEntry impl)).1
        (lowerBlock none (callPre impl) false impl.body (lowerEnv m impl.vars impl.results.toList) (callEntry impl)).2).blocks := by
  simp [lowerImplAt, callEntry, callEntryTypes, callPre, bodyTail, newBlock, initState,
    bind_run, setCur_run, set]
  rfl

theorem checkParam_scope {impl : Impl} {i : Nat} {p : Param}
    (hp : impl.params[i]? = some p) (h : checkParam impl i = .ok ()) :
    ∃ lv, impl.vars[p.var]? = some lv ∧ lv.scope = 0 := by
  unfold checkParam at h
  rw [hp] at h
  by_cases hvar : p.var = i
  · simp only [hvar, ite_true] at h
    cases hv : impl.vars[i]? with
    | none => simp [hv, reject] at h
    | some lv =>
      by_cases hs : lv.scope = 0
      · exact ⟨lv, by simpa [hvar] using hv, hs⟩
      · simp [hv, hs, reject, bind, Except.bind] at h
  · simp [hvar, reject, bind, Except.bind] at h

theorem checkImpl_paramScopes {m : Core.Module} {impl : Impl}
    (h : checkImpl m impl = .ok ()) :
    impl.body.scope = 0 ∧
      ∀ p ∈ impl.params.toList, ∃ lv, impl.vars[p.var]? = some lv ∧ lv.scope = impl.body.scope := by
  unfold checkImpl at h
  by_cases hmany : 1 < impl.results.size
  · simp [hmany, reject, bind, Except.bind] at h
  · simp only [ite_false, hmany] at h
    obtain ⟨_, _, h⟩ := exceptBind_ok_left h
    obtain ⟨_, hparams, h⟩ := exceptBind_ok_left h
    obtain ⟨_, _, h⟩ := exceptBind_ok_left h
    obtain ⟨_, _, h⟩ := exceptBind_ok_left h
    by_cases hbody : impl.body.scope = 0
    · refine ⟨hbody, fun p hp => ?_⟩
      obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp hp)
      have hbound : i ∈ List.range impl.params.size :=
        List.mem_range.mpr (Array.getElem?_eq_some_iff.mp hi).1
      have hparam := coreForAll_ok (List.range impl.params.size) (checkParam impl) hparams i hbound
      obtain ⟨lv, hlv, hscope⟩ := checkParam_scope hi hparam
      exact ⟨lv, hlv, hscope.trans hbody.symm⟩
    · simp [hbody, reject, bind, Except.bind] at h

theorem callPre_scopes {m : Core.Module} {impl : Impl} (h : checkImpl m impl = .ok ()) :
    ∀ p ∈ callPre impl, ∃ lv, impl.vars[p.1]? = some lv ∧ lv.scope = impl.body.scope := by
  intro p hp
  obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hp
  exact (checkImpl_paramScopes h).2 pair.1 ((List.of_mem_zip hpair).1)

def bindCallParams (fr : Frame) : List (ValueId × VTy) → List RVal → Frame
  | p :: ps, value :: values => bindCallParams (fr.set p.1 value) ps values
  | _, _ => fr

theorem bindParams_call (fr : Frame) (params : List (ValueId × VTy)) (values : List RVal) :
    bindParams fr params values = pure (bindCallParams fr params values) := by
  induction params generalizing fr values with
  | nil => cases values <;> rfl
  | cons p ps ih =>
    cases values with
    | nil => rfl
    | cons value values => simp only [bindParams, setCell_eq, pure_bind, ih, bindCallParams]

theorem bindCallParams_get_absent (fr : Frame) (params : List (ValueId × VTy))
    (values : List RVal) (id : ValueId) (h : id ∉ params.map Prod.fst) :
    (bindCallParams fr params values).vals[id]? = fr.vals[id]? := by
  induction params generalizing fr values with
  | nil => cases values <;> rfl
  | cons p ps ih =>
    cases values with
    | nil => rfl
    | cons value values =>
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [bindCallParams, ih _ _ h.2]
      simp [Frame.set, Std.HashMap.getElem?_insert, (Ne.symm h.1)]

theorem bindCallParams_has (fr : Frame) (params : List (ValueId × VTy))
    (values : List RVal) (hn : (params.map Prod.fst).Nodup) :
    ∀ p ∈ params.zip values, (bindCallParams fr params values).vals[p.1.1]? = some p.2 := by
  induction params generalizing fr values with
  | nil => simp
  | cons p ps ih =>
    cases values with
    | nil => simp
    | cons value values =>
      simp only [List.map_cons, List.nodup_cons] at hn
      intro pair hpair
      simp only [List.zip_cons_cons, List.mem_cons] at hpair
      rcases hpair with rfl | hpair
      · rw [bindCallParams, bindCallParams_get_absent _ _ _ _ hn.1]
        exact Frame.set_get _ _ _
      · exact ih _ _ hn.2 pair hpair

theorem bindCallParams_frame (fr : Frame) (params : List (ValueId × VTy))
    (values : List RVal) :
    (bindCallParams fr params values).act = fr.act ∧
    (bindCallParams fr params values).scopes = fr.scopes ∧
    (bindCallParams fr params values).depth = fr.depth := by
  induction params generalizing fr values with
  | nil => cases values <;> exact ⟨rfl, rfl, rfl⟩
  | cons p ps ih =>
    cases values with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons value values => exact ih _ _

theorem parameterPreRel (vars : Array LocalVar) (fr : Frame) :
    ∀ (params : List Param) (ids : List ValueId) (values : List Val),
    params.length = ids.length → params.length = values.length →
    (∀ pair ∈ ids.zip values, fr.vals[pair.1]? = some (.val pair.2)) →
    PreRel fr ((params.zip ids).map fun (p, id) =>
      (p.var, id, (vars[p.var]?.map (·.org)).getD 0))
      ((params.zip values).map fun (p, value) => (p.var, value))
  | [], [], [], _, _, _ => trivial
  | p :: params, id :: ids, value :: values, hi, hv, hc => by
    refine ⟨rfl, hc (id, value) (by simp), ?_⟩
    exact parameterPreRel vars fr params ids values (by simpa using hi) (by simpa using hv)
      (fun pair hpair => hc pair (by simp [hpair]))
  | [], _ :: _, _, hi, _, _ => by simp at hi
  | _ :: _, [], _, hi, _, _ => by simp at hi
  | [], [], _ :: _, _, hv, _ => by simp at hv
  | _ :: _, _ :: _, [], _, hv, _ => by simp at hv

theorem bindCallParams_zip_cells (fr : Frame) (ids : List ValueId) (tys : List VTy)
    (values : List Val) (ht : ids.length = tys.length) (hn : ids.Nodup) :
    ∀ pair ∈ ids.zip values,
      (bindCallParams fr (ids.zip tys) (values.map RVal.val)).vals[pair.1]? = some (.val pair.2) := by
  intro pair hpair
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hpair
  obtain ⟨hid, hval⟩ := List.getElem?_zip_eq_some.mp hi
  have hlt : i < tys.length := ht ▸ (List.getElem?_eq_some_iff.mp hid).1
  obtain ⟨ty, hty⟩ : ∃ ty, tys[i]? = some ty :=
    ⟨tys[i], by simp⟩
  have hparams : (ids.zip tys)[i]? = some (pair.1, ty) :=
    List.getElem?_zip_eq_some.mpr ⟨hid, hty⟩
  have hvalues : (values.map RVal.val)[i]? = some (.val pair.2) := by simp [hval]
  have hboth : ((ids.zip tys).zip (values.map RVal.val))[i]? =
      some ((pair.1, ty), .val pair.2) := List.getElem?_zip_eq_some.mpr ⟨hparams, hvalues⟩
  have hnodup : ((ids.zip tys).map Prod.fst).Nodup := by
    rw [List.map_fst_zip (Nat.le_of_eq ht)]
    exact hn
  exact bindCallParams_has fr (ids.zip tys) (values.map RVal.val) hnodup _
    (List.mem_iff_getElem?.mpr ⟨i, hboth⟩)

def callFrame (impl : Impl) (act : ActId) (depth : Nat) (values : List Val) : Frame :=
  bindCallParams ⟨act, [], {}, depth⟩ ((List.range impl.params.size).zip (callEntryTypes impl))
    (values.map RVal.val)

theorem callFrame_preRel (impl : Impl) (act : ActId) (depth : Nat) (values : List Val)
    (h : impl.params.size = values.length) :
    PreRel (callFrame impl act depth values) (callPre impl)
      ((impl.params.toList.zip values).map fun (p, value) => (p.var, value)) := by
  apply parameterPreRel impl.vars (callFrame impl act depth values)
  · simp
  · simpa using h
  · exact bindCallParams_zip_cells _ _ _ _ (by simp [callEntryTypes]) List.nodup_range

theorem callFrame_rel (m : Core.Module) (profile : NumProfile) (i : ImplId) (impl : Impl)
    (act : ActId) (depth : Nat) (values : List Val) :
    Rel ⟨profile, m⟩ ⟨impl.vars, act, [], depth⟩ ⟨⟨profile, lower m⟩, lowerImplAt m i impl⟩
      (callFrame impl act depth values) (callEntry impl) := by
  obtain ⟨ha, hs, hd⟩ := bindCallParams_frame ⟨act, [], {}, depth⟩
    ((List.range impl.params.size).zip (callEntryTypes impl)) (values.map RVal.val)
  exact ⟨rfl, rfl, ha, hs, hd, rfl⟩

theorem enterFn_call (m : Core.Module) (profile : NumProfile) (i : ImplId) (impl : Impl)
    (depth fuel : Nat) (values : List Val) (state : St)
    (hp : impl.params.size = values.length)
    (hext : ExtT (callEntry impl) (lowerImplAt m i impl).blocks) :
    enterFn (fuel + 1) ⟨profile, lower m⟩ depth (lowerImplAt m i impl) values state =
      runAt ⟨⟨profile, lower m⟩, lowerImplAt m i impl⟩ (0, 0)
        (callFrame impl state.nextAct depth values) fuel
        { state with nextAct := state.nextAct + 1 } := by
  obtain ⟨blk, hb, hbparams⟩ := hext.params (b := 0)
    (blk := ⟨(List.range impl.params.size).zip (callEntryTypes impl), #[]⟩) rfl
  have hparams : (lowerImplAt m i impl).params.length = values.length := by
    simpa [lowerImplAt] using hp
  have hblkparams : blk.params.length = values.length := by
    rw [hbparams]
    simp [callEntryTypes, hp]
  have hinsts : instsAt (lowerImplAt m i impl) (0, 0) = blk.insts := by simp [instsAt, hb]
  have hentrylen : ((List.range impl.params.size).zip (callEntryTypes impl)).length =
      values.length := by simp [callEntryTypes, hp]
  simp only [enterFn, hparams, ite_true, enterBlock, hb, List.length_map,
    hbparams, hentrylen, bindParams_call, pure_bind, runAt, hinsts]
  rfl

theorem implOfContext_lookup {m : Core.Module} {c : ContextId} {ctx : Context}
    (hctx : m.contexts[c]? = some ctx) (vars : Array LocalVar) (ls : LS) :
    implOfContext c (lowerEnv m vars []) ls = (ctx.impl, ls) := by
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
    let le := lowerEnv m impl.vars impl.results.toList
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

def CalleeBlockClaim (n : Nat) (cfg : Cfg) (i : ImplId) (impl : Impl) : Prop :=
  ∀ act depth values, impl.params.size = values.length →
    let env : Env := ⟨impl.vars, act, [], depth⟩
    let cx : FnCtx := ⟨⟨cfg.profile, lower cfg.mod⟩, lowerImplAt cfg.mod i impl⟩
    let fr := callFrame impl act depth values
    let body := lowerBlock none (callPre impl) false impl.body (lowerEnv cfg.mod impl.vars impl.results.toList)
      (callEntry impl)
    SimE cx (0, 0) fr
      (execBlock n cfg env ((impl.params.toList.zip values).map fun (p, value) => (p.var, value)) impl.body)
      (BlockFlowPost cfg env cx (callEntry impl) fr body.2 impl.body false body.1)

theorem calleeBlockClaim_flow {m : Core.Module} {i : ImplId} {impl : Impl}
    (hcheck : checkImpl m impl = .ok ()) (hok : flowBlockOk impl.body = true)
    (profile : NumProfile) (n : Nat) : CalleeBlockClaim n ⟨profile, m⟩ i impl := by
  intro act depth values hp
  let le := lowerEnv m impl.vars impl.results.toList
  let body := lowerBlock none (callPre impl) false impl.body le (callEntry impl)
  let cx : FnCtx := ⟨⟨profile, lower m⟩, lowerImplAt m i impl⟩
  let fr := callFrame impl act depth values
  let env : Env := ⟨impl.vars, act, [], depth⟩
  have hlow : lowerBlock none (callPre impl) false impl.body le (callEntry impl) = (body.1, body.2) := rfl
  have hextTail : ExtT (bodyTail impl le body.1 body.2) cx.fn.blocks := by
    rw [lowerImplAt_call_blocks]
    exact extT_finish _
  have hextBody : ExtT body.2 cx.fn.blocks := hextTail.of_adv
    (advB_finishFunction impl body.1 le body.2 (finishFunction impl body.1 le body.2).1
      (bodyTail impl le body.1 body.2) rfl)
  have hsim := (flowClaims n).block none (callPre impl)
    ((impl.params.toList.zip values).map fun (p, value) => (p.var, value)) false impl.body hok
    ⟨profile, m⟩ env (callPre_scopes hcheck) le (callEntry impl) body.2 body.1 (0, 0) cx fr
    hlow (callEntry_pp impl) hextBody (callFrame_rel m profile i impl act depth values)
    (callFrame_preRel impl act depth values hp)
  rw [prepareReturn_no_scopes env rfl] at hsim
  simp only [bind_pure] at hsim
  exact SimE.of_simG hsim

theorem calleeCallClaim_of_body {m : Core.Module} {c : ContextId} {ctx : Context} {impl : Impl}
    (hctx : m.contexts[c]? = some ctx) (himpl : m.impls[ctx.impl]? = some impl)
    (hok : flowBlockOk impl.body = true) (profile : NumProfile) (n : Nat)
    (hbody : CalleeBlockClaim n ⟨profile, m⟩ ctx.impl impl) :
    CalleeCallClaim (n + 1) ⟨profile, m⟩ c := by
  intro depth values state
  by_cases hd : depth ≥ maxCallDepth
  · simp only [enterCall, hd, ite_true]
    exact agree_timeout _ _
  · by_cases hp : impl.params.size = values.length
    · have hent : ((m.contexts[c]?).map (·.impl)).getD 0 = ctx.impl := by simp [hctx]
      rw [hent]
      simp only [enterCall, hd, ite_false, lookupContext, lookupImpl, hctx, himpl, pure_bind,
        hp, ite_true]
      let le := lowerEnv m impl.vars impl.results.toList
      let body := lowerBlock none (callPre impl) false impl.body le (callEntry impl)
      let cx : FnCtx := ⟨⟨profile, lower m⟩, lowerImplAt m ctx.impl impl⟩
      let env : Env := ⟨impl.vars, state.nextAct, [], depth + 1⟩
      let fr := callFrame impl state.nextAct (depth + 1) values
      let initial := { state with nextAct := state.nextAct + 1 }
      let pre := (impl.params.toList.zip values).map fun (p, value) => (p.var, value)
      have hlow : lowerBlock none (callPre impl) false impl.body le (callEntry impl) = (body.1, body.2) := rfl
      have hextTail : ExtT (bodyTail impl le body.1 body.2) cx.fn.blocks := by
        rw [lowerImplAt_call_blocks]
        exact extT_finish _
      have hextBody : ExtT body.2 cx.fn.blocks := hextTail.of_adv
        (advB_finishFunction impl body.1 le body.2 (finishFunction impl body.1 le body.2).1
          (bodyTail impl le body.1 body.2) rfl)
      have hextEntry : ExtT (callEntry impl) cx.fn.blocks := hextBody.of_adv
        (advB_lowerBlock none (callPre impl) false impl.body le (callEntry impl) body.1 body.2 hlow)
      have hrun : ∀ fuel, callFn (fuel + 2) ⟨profile, lower m⟩ depth ctx.impl values state =
          runAt cx (0, 0) fr fuel initial := by
        intro fuel
        rw [show fuel + 2 = (fuel + 1) + 1 from rfl, callFn]
        simp only [hd, ite_false, lookupFn_lower himpl, pure_bind]
        exact enterFn_call m profile ctx.impl impl (depth + 1) fuel values state hp hextEntry
      have hs := hbody state.nextAct (depth + 1) values hp initial
      refine ⟨fun value after h => ?_, fun err after h hf => ?_⟩
      · have h' : (execBlock n ⟨profile, m⟩ env pre impl.body >>= expectReturned) initial =
            .ok value after := h
        rw [bind_apply] at h'
        cases hb : execBlock n ⟨profile, m⟩ env pre impl.body initial with
        | stop err stopped => rw [hb] at h'; cases h'
        | ok flow finished =>
          rw [hb] at h'
          obtain ⟨pt', fr', hpost, hmore⟩ := hs.1 flow finished hb
          change BlockFlowPost ⟨profile, m⟩ env cx (callEntry impl) fr body.2 impl.body false body.1
            flow pt' fr' at hpost
          rcases hpost with ⟨normal, hflow, hunit, P⟩ | ⟨returned, org, hflow, hsite⟩
          · subst hflow
            simp only [expectReturned, pure_apply] at h'
            obtain ⟨rfl, rfl⟩ := Res.ok.inj h'
            have hdiv := execBlock_normal_not_divergent n ⟨profile, m⟩ env pre impl.body hok
              initial finished normal hb
            rcases bodyTail_cases impl le body.1 body.2 hdiv with ⟨hnone, _⟩ | ⟨b, hcur, hterm⟩
            · obtain ⟨blk, hc, _⟩ := LS.pp_some P.pp
              rw [hnone] at hc
              cases hc
            obtain ⟨_, _, _, hi⟩ := emitTerm_facts hterm P.pp hextTail
            change instAt cx.fn pt' = some (.term (.ret (if impl.body.value.isSome then [body.1] else []) none)) at hi
            have hreturn : runAt cx pt' fr' 1 finished = .ok normal finished := by
              cases hv : impl.body.value.isSome with
              | false =>
                have hnone : impl.body.value = none := by simpa using hv
                have hi' : instAt cx.fn pt' = some (.term (.ret [] none)) := by simpa [hv] using hi
                rw [runAt_ret0 hi' 0, hunit hnone]
                rfl
              | true =>
                have hcell : fr'.vals[body.1]? = some (.val normal) :=
                  P.has (body.1, .val normal) (by simp [blockCells, hv])
                have hi' : instAt cx.fn pt' = some (.term (.ret [body.1] none)) := by simpa [hv] using hi
                rw [runAt_ret1 hi' hcell 0]
                rfl
            obtain ⟨K, hK⟩ := hmore 1 (.ok normal finished) (NonTimeout.ok _ _) hreturn
            refine ⟨K + 2, fun fuel hfu => ?_⟩
            obtain ⟨extra, rfl⟩ : ∃ extra, fuel = extra + 2 := ⟨fuel - 2, by omega⟩
            change callFn (extra + 2) ⟨profile, lower m⟩ depth ctx.impl values state = _
            rw [hrun extra]
            exact hK extra (by omega)
          · subst hflow
            simp only [expectReturned, pure_apply] at h'
            obtain ⟨rfl, rfl⟩ := Res.ok.inj h'
            obtain ⟨K, hK⟩ := hmore 1 (.ok returned finished) (NonTimeout.ok _ _) (hsite.run finished 0)
            refine ⟨K + 2, fun fuel hfu => ?_⟩
            obtain ⟨extra, rfl⟩ : ∃ extra, fuel = extra + 2 := ⟨fuel - 2, by omega⟩
            change callFn (extra + 2) ⟨profile, lower m⟩ depth ctx.impl values state = _
            rw [hrun extra]
            exact hK extra (by omega)
      · have h' : (execBlock n ⟨profile, m⟩ env pre impl.body >>= expectReturned) initial =
            .stop err after := h
        rw [bind_apply] at h'
        cases hb : execBlock n ⟨profile, m⟩ env pre impl.body initial with
        | stop err' stopped =>
          rw [hb] at h'
          obtain ⟨rfl, rfl⟩ := Res.stop.inj h'
          obtain ⟨K, hK⟩ := hs.2 err' stopped hb hf
          refine ⟨K + 2, fun fuel hfu => ?_⟩
          obtain ⟨extra, rfl⟩ : ∃ extra, fuel = extra + 2 := ⟨fuel - 2, by omega⟩
          change callFn (extra + 2) ⟨profile, lower m⟩ depth ctx.impl values state = _
          rw [hrun extra]
          exact hK extra (by omega)
        | ok flow finished =>
          rw [hb] at h'
          cases flow <;> simp only [expectReturned, pure_apply, fault, M.stop] at h' <;>
            cases h' <;> simp [IsFinal] at hf
    · simp only [enterCall, hd, ite_false, lookupContext, lookupImpl, hctx, himpl, pure_bind,
        hp, ite_false]
      exact agree_fault _ _ _

theorem calleeCallClaim_flow {m : Core.Module} {c : ContextId} {ctx : Context} {impl : Impl}
    (hctx : m.contexts[c]? = some ctx) (himpl : m.impls[ctx.impl]? = some impl)
    (hcheck : checkImpl m impl = .ok ()) (hok : flowBlockOk impl.body = true)
    (profile : NumProfile) (n : Nat) : CalleeCallClaim n ⟨profile, m⟩ c := by
  cases n with
  | zero => exact calleeCallClaim_zero _ _
  | succ n =>
    exact calleeCallClaim_of_body hctx himpl hok profile n
      (calleeBlockClaim_flow hcheck hok profile n)

theorem expr_call_sim {n : Nat} {c : ContextId} {args : List Arg} {org : OriginId}
    (cfg : Cfg) (ha : ArgsEClaim n cfg args) (hc : CalleeCallClaim n cfg c)
    (le : LEnv) (ls ls' : LS) (r : ValueId) (pt : Pt) (env : Env) (cx : FnCtx) (fr : Frame)
    (hlow : lowerExpr (.call c args org) le ls = (r, ls')) (hpp : ls.pp = some pt)
    (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hmod : le.mod = cfg.mod) (hgir : cx.cfg.mod = lower cfg.mod) :
    SimE cx pt fr (evalExpr (n + 1) cfg env (.call c args org)) (fun value pt' fr' =>
      Post cfg env cx ls fr ls' fr' pt' [(r, .val value)]) := by
  obtain ⟨ids, middle, after, hargs, hdef, htail⟩ := lowerExpr_call_split hlow
  have hextAfter : ExtT after cx.fn.blocks := by
    rcases htail with ⟨_, hterm⟩ | ⟨_, rfl⟩
    · exact hext.of_adv (adv_emitTerm hterm)
    · exact hext
  have hextMiddle : ExtT middle cx.fn.blocks := hextAfter.of_adv (adv_emitDef hdef)
  simp only [evalExpr]
  refine SimE.bind (ha le ls ids middle pt env cx fr hargs hpp hextMiddle hrel hmod hgir)
    fun vals pt1 fr1 ⟨hlen, P⟩ => ?_
  have hread := mapList_getVal_cells hlen P.has
  have hi := (Post.def_leaf P hdef hextAfter (.val .unit)).2
  have hcall : ∀ state, EventualM (enterCall n cfg env.depth c vals)
      (fun fuel => callFn fuel cx.cfg fr1.depth
        (((le.mod.contexts[c]?).map (·.impl)).getD 0) vals) state := by
    intro state
    have hcfg : cx.cfg = ⟨cfg.profile, lower cfg.mod⟩ := by
      cases hgcfg : cx.cfg
      simp only [hgcfg] at hgir
      have hprof := P.rel.prof
      simp only [hgcfg] at hprof
      cases hgir
      cases hprof
      rfl
    rw [hmod, hcfg, P.rel.depth]
    exact hc env.depth vals state
  have hstep := SimE.call_step hi hread hcall
  rcases htail with ⟨hnr, _⟩ | ⟨_, rfl⟩
  · have hn : Core.Sound.Never (enterCall n cfg env.depth c vals) :=
      enterCall_noReturn_never cfg c (by simpa [hmod] using hnr) n env.depth vals
    exact SimE.of_stops hn (fun _ _ _ h => h) hstep
  · exact hstep.mono fun value pt' fr' ⟨hpt, hfr⟩ => by
      subst hpt; subst hfr
      exact (Post.def_leaf P hdef hext (.val value)).1

theorem exprEClaim_call {n : Nat} {cfg : Cfg} {c : ContextId} {args : List Arg} {org : OriginId}
    (ha : ArgsEClaim n cfg args) (hc : CalleeCallClaim n cfg c) :
    ExprEClaim (n + 1) cfg (.call c args org) := by
  intro le ls r ls' pt env cx fr hlow hpp hext hrel hmod hgir
  exact expr_call_sim cfg ha hc le ls ls' r pt env cx fr hlow hpp hext hrel hmod hgir

end Goose.Lower
