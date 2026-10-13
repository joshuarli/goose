import Goose.Lower.Claims
import Goose.Lower.Validate
import Goose.Lower.Finish
import Goose.Core.Validate
import Goose.GIR.Validate

/-!
The lowering preserves the meaning of Core modules in a fragment: every run of the Core
evaluator that finishes is matched by a run of the lowered module's interpreter at some fuel.
-/

namespace Goose.Proofs.Lower

open Goose.Core Goose.GIR Goose.Lower

/-! ### Validation facts -/

theorem exceptBind_ok_left {ε : Type} {α β : Type} {x : Except ε α} {f : α → Except ε β}
    {b : β} (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error e =>
    simp only [hx, bind, Except.bind] at h
    cases h
  | ok a =>
    simp only [hx, bind, Except.bind] at h
    exact ⟨a, rfl, h⟩

theorem coreForAll_ok {α : Type} (xs : List α) (f : α → Core.V Unit)
    (h : Core.forAll xs f = .ok ()) : ∀ x ∈ xs, f x = .ok () := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [Core.forAll] at h
    cases hfa : f a with
    | error e =>
      simp only [hfa, bind, Except.bind] at h
      cases h
    | ok u =>
      cases u
      simp only [hfa, bind, Except.bind, pure, Except.pure] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hfa
      · exact ih h x hx

/-- `Core.validate` exposes each check's successful result in order. -/
theorem core_validate_stages (m : Core.Module) (h : Core.validate m = .ok ()) :
    Core.checkStructTables m = .ok () ∧
    Core.checkEntry m = .ok () ∧
    Core.checkImplementationContexts m = .ok () ∧
    (∀ i gl, m.globals[i]? = some gl → Core.checkGlobal m i gl = .ok ()) ∧
    (∀ impl ∈ m.impls.toList, Core.checkImpl m impl = .ok ()) ∧
    (∀ ctx ∈ m.contexts.toList, Core.checkContext m ctx = .ok ()) ∧
    (∀ i, i < m.globals.size → Core.checkInitRoots m i = .ok ()) ∧
    Core.checkModuleDemand m = .ok () := by
  unfold Core.validate at h
  obtain ⟨_, hstruct, hrest⟩ := exceptBind_ok_left h
  obtain ⟨_, hentry, hrest⟩ := exceptBind_ok_left hrest
  obtain ⟨_, himplcontexts, hrest⟩ := exceptBind_ok_left hrest
  obtain ⟨_, hglobals, hrest⟩ := exceptBind_ok_left hrest
  obtain ⟨_, himpls, hrest⟩ := exceptBind_ok_left hrest
  obtain ⟨_, hcontexts, hrest⟩ := exceptBind_ok_left hrest
  obtain ⟨_, hroots, hdemand⟩ := exceptBind_ok_left hrest
  refine ⟨by simpa using hstruct, by simpa using hentry, by simpa using himplcontexts,
    ?_, ?_, ?_, ?_, hdemand⟩
  · intro i gl hgl
    have hi : i ∈ List.range m.globals.size := List.mem_range.mpr ((Array.getElem?_eq_some_iff.mp hgl).1)
    have hcheck := coreForAll_ok (List.range m.globals.size) (fun g =>
      match m.globals[g]? with
      | some gval => Core.checkGlobal m g gval
      | none => pure ()) hglobals i hi
    simpa [hgl] using hcheck
  · exact coreForAll_ok m.impls.toList (Core.checkImpl m) himpls
  · exact coreForAll_ok m.contexts.toList (Core.checkContext m) hcontexts
  · intro i hi
    exact coreForAll_ok (List.range m.globals.size) (Core.checkInitRoots m) hroots i (List.mem_range.mpr hi)

theorem checkEntry_shape {m : Core.Module} (h : Core.checkEntry m = .ok ()) :
    ∃ ctx impl, m.contexts[m.entry]? = some ctx ∧ m.impls[ctx.impl]? = some impl ∧
      impl.params.size = 0 ∧ impl.results.size = 0 := by
  unfold Core.checkEntry at h
  cases hctx : m.contexts[m.entry]? with
  | none => simp [hctx, Core.reject] at h
  | some ctx =>
    cases himpl : m.impls[ctx.impl]? with
    | none => simp [hctx, himpl, Core.reject] at h
    | some impl =>
      refine ⟨ctx, impl, rfl, himpl, ?_⟩
      simp [hctx, himpl, Core.reject] at h
      split at h
      · rename_i hp
        exact ⟨by simp [hp.1], by simp [hp.2]⟩
      · simp at h

theorem lower_preserves_module_headers (m : Core.Module) :
    (lower m).files = m.files ∧
    (lower m).origins = m.origins ∧
    (lower m).profile = m.profile ∧
    (lower m).structs = m.structs := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem lower_global_lookup (m : Core.Module) (i : Nat) :
    (lower m).globals[i]? = (m.globals[i]?).map (lowerGlobal m) := by
  simp [lower]

theorem lower_func_lookup (m : Core.Module) (i : Nat) :
    (lower m).funcs[i]? = (m.impls[i]?).map (fun impl => lowerImplAt m i impl) := by
  simp [lower]

theorem checkGlobal_origin {m : Core.Module} {i : Nat} {g : Core.Global}
    (h : Core.checkGlobal m i g = .ok ()) : g.org < m.origins.size := by
  by_cases ht : (g.ty.storable && !g.ty.isRefLike) = true
  · by_cases ho : g.org < m.origins.size
    · exact ho
    · simp [Core.checkGlobal, ht, ho, Core.reject, bind, Except.bind] at h
  · simp [Core.checkGlobal, ht, Core.reject, bind, Except.bind] at h

theorem checkImpl_localOrigins {m : Core.Module} {impl : Core.Impl}
    (h : Core.checkImpl m impl = .ok ()) :
    ∀ lv ∈ impl.vars.toList, lv.org < m.origins.size := by
  unfold Core.checkImpl at h
  by_cases hmany : 1 < impl.results.size
  · simp [hmany, Core.reject, bind, Except.bind] at h
  · simp only [if_neg hmany] at h
    obtain ⟨_, _, h⟩ := exceptBind_ok_left h
    obtain ⟨_, _, h⟩ := exceptBind_ok_left h
    obtain ⟨_, horigins, _⟩ := exceptBind_ok_left h
    have hbound := coreForAll_ok impl.vars.toList (fun lv =>
      unless lv.org < m.origins.size do
        Core.reject .type s!"{impl.name}: origin of variable {lv.name} is outside the origin table") horigins
    intro lv hlv
    have hcheck := hbound lv hlv
    by_cases hnot : lv.org < m.origins.size
    · exact hnot
    · simp [hnot, Core.reject] at hcheck

theorem checkImpl_localScopes {m : Core.Module} {impl : Core.Impl}
    (h : Core.checkImpl m impl = .ok ()) :
    ∀ lv ∈ impl.vars.toList, lv.scope < (Core.blockScopes none impl.body).length := by
  unfold Core.checkImpl at h
  by_cases hmany : 1 < impl.results.size
  · simp [hmany, Core.reject, bind, Except.bind] at h
  · simp only [if_neg hmany] at h
    obtain ⟨_, _, h⟩ := exceptBind_ok_left h
    obtain ⟨_, _, h⟩ := exceptBind_ok_left h
    obtain ⟨_, _, h⟩ := exceptBind_ok_left h
    by_cases hbody : impl.body.scope = 0
    · simp only [if_pos hbody] at h
      cases horder : Core.scopeOrderError (Core.blockScopes none impl.body) 0 with
      | some message => simp [horder, Core.reject, bind, Except.bind] at h
      | none =>
        simp [horder] at h
        obtain ⟨_, hscopes, _⟩ := exceptBind_ok_left h
        have hbound := coreForAll_ok impl.vars.toList (fun lv =>
          unless lv.scope < (Core.blockScopes none impl.body).length do
            Core.reject .type s!"{impl.name}: scope of variable {lv.name} is outside the body scope table") hscopes
        intro lv hlv
        have hcheck := hbound lv hlv
        by_cases hnot : lv.scope < (Core.blockScopes none impl.body).length
        · exact hnot
        · simp [hnot, Core.reject] at hcheck
    · simp [hbody, Core.reject, bind, Except.bind] at h

theorem lowerImplAt_slotScopes {m : Core.Module} {implId : Nat} {impl : Core.Impl}
    (hcheck : Core.checkImpl m impl = .ok ()) :
    ∀ sl ∈ (lowerImplAt m implId impl).slots,
      sl.scope < (lowerImplAt m implId impl).scopes.size := by
  intro sl hsl
  obtain ⟨i, hslot⟩ := Array.mem_iff_getElem?.mp hsl
  change (impl.vars.mapIdx fun i lv =>
    ({ ty := lv.ty, kind := lv.kind, scope := lv.scope, var := i } : GIR.Slot))[i]? = some sl at hslot
  cases hvar : impl.vars[i]? with
  | none => simp [Array.getElem?_mapIdx, hvar] at hslot
  | some lv =>
    simp [Array.getElem?_mapIdx, hvar] at hslot
    subst sl
    have hmem : lv ∈ impl.vars.toList :=
      Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨i, hvar⟩)
    have hscope := checkImpl_localScopes hcheck lv hmem
    simpa [lowerImplAt, Core.scopeParents] using hscope

/-- Lowering preserves the entry signature and global initializer headers. -/
theorem lower_checkEntryAndGlobals (m : Core.Module) (h : Core.validate m = .ok ()) :
    GIR.checkEntryAndGlobals (lower m) = .ok () := by
  obtain ⟨_, hentry, _, hglobals, _, _, _, _⟩ := core_validate_stages m h
  obtain ⟨ctx, impl, hctx, himpl, hparams, hresults⟩ := checkEntry_shape hentry
  have hfunc : (lower m).funcs[(lower m).entry]? =
      some (lowerImplAt m ctx.impl impl) := by
    rw [lower_func_lookup]
    simp [lower, hctx, himpl]
  have hparamsList : impl.params.toList = [] := by
    have hlen : impl.params.toList.length = 0 := by simpa using hparams
    exact List.eq_nil_of_length_eq_zero hlen
  have hresultsList : impl.results.toList = [] := by
    have hlen : impl.results.toList.length = 0 := by simpa using hresults
    exact List.eq_nil_of_length_eq_zero hlen
  have hglobalOrg : ∀ g ∈ m.globals, g.org < m.origins.size := by
    intro g hg
    obtain ⟨i, hget⟩ := Array.mem_iff_getElem?.mp hg
    exact checkGlobal_origin (hglobals i g hget)
  have hOrigins : (lower m).origins = m.origins := rfl
  let checkLowerGlobal := fun (g : GIR.Global) (_ : PUnit) => do
    unless g.init.params.isEmpty && g.init.results == [g.ty] do
      GIR.violation .v001 s!"the initializer of global {g.name} must take no parameters and return its type"
    unless g.org < m.origins.size do
      GIR.violation .v001 s!"global {g.name}: origin outside the origin table"
    pure (ForInStep.yield PUnit.unit)
  have lowerGlobals_ok : ∀ gs : List Core.Global,
      (∀ g ∈ gs, g.org < m.origins.size) →
      forIn (gs.map (lowerGlobal m)) PUnit.unit checkLowerGlobal = .ok () := by
    intro gs hgs
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.forIn_cons]
      have hg := hgs g (by simp)
      have hp : (lowerGlobal m g).init.params = [] := rfl
      have hr : (lowerGlobal m g).init.results = [g.ty] := rfl
      have ho : (lowerGlobal m g).org = g.org := rfl
      have hty : (lowerGlobal m g).ty = g.ty := rfl
      have hstep : checkLowerGlobal (lowerGlobal m g) PUnit.unit =
          .ok (ForInStep.yield PUnit.unit) := by
        simp only [checkLowerGlobal, hp, hr, ho, hty, List.isEmpty_nil]
        simp [hg, pure, Except.pure]
      rw [hstep]
      apply ih
      intro g' hg'
      exact hgs g' (by simp [hg'])
  unfold GIR.checkEntryAndGlobals
  simp only [bind, Except.bind]
  have hentryShape :
      ((lowerImplAt m ctx.impl impl).params.isEmpty &&
        (lowerImplAt m ctx.impl impl).results.isEmpty) = true := by
    simp [lowerImplAt, hparamsList, hresultsList]
  simp only [hfunc, hentryShape, if_true]
  rw [hOrigins]
  rw [← Array.forIn_toList]
  simp only [lower, Array.toList_map]
  have hloop := lowerGlobals_ok m.globals.toList
    (by
      intro g hg
      apply hglobalOrg
      exact Array.mem_def.mpr hg)
  change (forIn (List.map (lowerGlobal m) m.globals.toList) PUnit.unit checkLowerGlobal >>= fun _ =>
    pure ()) = .ok ()
  rw [hloop]
  rfl

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

theorem lowerGlobal_blocks_nonempty (m : Core.Module) (g : Core.Global) :
    0 < (lowerGlobal m g).init.blocks.size := by
  let le := lowerEnv m #[]
  let run := lowerExpr g.init le startLS
  let v := run.1
  let ls1 := run.2
  have hlower : lowerExpr g.init le startLS = (v, ls1) := rfl
  have hadv1 : startLS.Adv ls1 := advB_lowerExpr g.init le startLS v ls1 hlower
  let endRun := emitTerm (.ret [v] (some g.org)) le ls1
  let ls2 := endRun.2
  have hemit : emitTerm (.ret [v] (some g.org)) le ls1 = ((), ls2) := by rfl
  have hadv2 : ls1.Adv ls2 := adv_emitTerm hemit
  have hsize : startLS.blocks.size ≤ ls2.blocks.size := (hadv1.trans hadv2).ext.1
  have hpos : 0 < ls2.blocks.size := Nat.lt_of_lt_of_le (by simp [startLS]) hsize
  rw [lowerGlobal_blocks]
  simp only [finishBlocks, Array.size_map]
  change 0 < ls2.blocks.size
  exact hpos

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

/-- Finalize the body with a return or close a synthetic divergent frontier. -/
def bodyTail (impl : Impl) (le : LEnv) (v : ValueId) (ls1 : LS) : LS :=
  (finishFunction impl v le ls1).2

theorem lowerImplAt_blocks (m : Core.Module) (implId : ImplId) (impl : Impl)
    (hp : impl.params = #[]) :
    (lowerImplAt m implId impl).blocks = finishBlocks (bodyTail impl (lowerEnv m impl.vars)
      (lowerBlock none [] false impl.body (lowerEnv m impl.vars) startLS).1
      (lowerBlock none [] false impl.body (lowerEnv m impl.vars) startLS).2).blocks := by
  rcases impl with ⟨name, params, results, vars, body, summary⟩
  simp only at hp
  subst hp
  rfl

theorem lowerImpl_blocks (m : Core.Module) (impl : Impl) (hp : impl.params = #[]) :
    (lowerImpl m impl).blocks = finishBlocks (bodyTail impl (lowerEnv m impl.vars)
      (lowerBlock none [] false impl.body (lowerEnv m impl.vars) startLS).1
      (lowerBlock none [] false impl.body (lowerEnv m impl.vars) startLS).2).blocks := by
  unfold lowerImpl
  exact lowerImplAt_blocks m _ impl hp

theorem bodyTail_cases (impl : Impl) (le : LEnv) (v : ValueId) (ls1 : LS)
    (hok : blockOk impl.body = true)
    (hlow : lowerBlock none [] false impl.body le startLS = (v, ls1)) :
    (ls1.cur = none ∧ bodyTail impl le v ls1 = ls1) ∨
    (∃ b, ls1.cur = some b ∧
      emitTerm (.ret (if impl.body.value.isSome then [v] else []) none) le ls1 =
        ((), bodyTail impl le v ls1)) := by
  cases hc : ls1.cur with
  | none =>
    left
    refine ⟨rfl, ?_⟩
    unfold bodyTail
    rw [finishFunction_fragment impl le startLS v ls1 hok hlow]
    simp [bind_run, isLive_none hc, pure_run]
  | some b =>
    right
    refine ⟨b, rfl, ?_⟩
    unfold bodyTail
    rw [finishFunction_fragment impl le startLS v ls1 hok hlow]
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
    have hfn : (lower m).funcs[ctx.impl]? = some (lowerImplAt m ctx.impl impl) := by
      simp [lower, himpl]
    have hmaxd : ¬ ((0 : Nat) ≥ maxCallDepth) := by simp [maxCallDepth]
    rw [hent]
    rw [enterCall_nil ⟨p, m⟩ n' m.entry ctx impl hctx himpl hp]
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
        rcases bodyTail_cases impl le r ls1 hb hlow with ⟨hnone, -⟩ | ⟨b, hcur, hemit⟩
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

/-- The lowering preserves the meaning of the modules whose initializers and entry
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
