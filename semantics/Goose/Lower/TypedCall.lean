import Goose.Lower.FunctionTail
import Goose.Lower.FlowState
import Goose.Lower.SourceDivergence
import Goose.Lower.SourceContexts

namespace Goose.Lower

open Goose.Core Goose.GIR
open Goose.Proofs.Lower (extT_finish bodyTail bodyTail_cases)

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
  have checked := Core.Sound.checkImpl_ok m impl h
  refine ⟨checked.bodyScope, fun parameter member => ?_⟩
  obtain ⟨index, atIndex⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  obtain ⟨hid, localDecl, hvariable, hscope, _⟩ := checked.params index parameter atIndex
  exact ⟨localDecl, by simpa [hid] using hvariable, hscope.trans checked.bodyScope.symm⟩

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

private theorem nonfinalStop_eventual (err : Stop) (hfinal : ¬ IsFinal err)
    (g : Nat → M α) (state : St) : EventualM (M.stop err) g state := by
  refine ⟨fun value after h => ?_, fun stopped after h hf => ?_⟩
  · cases h
  · cases h
    exact False.elim (hfinal hf)

def CalleeBodyAt (n : Nat) (cfg : Cfg) (i : ImplId) (impl : Impl)
    (depth : Nat) (values : List Val) (state : St) : Prop :=
  let env : Env := ⟨impl.vars, state.nextAct, [], depth + 1⟩
  let cx : FnCtx := ⟨⟨cfg.profile, lower cfg.mod⟩, lowerImplAt cfg.mod i impl⟩
  let fr := callFrame impl state.nextAct (depth + 1) values
  let body := lowerBlock none (callPre impl) false impl.body
    (lowerEnv cfg.mod impl.vars impl.results.toList) (callEntry impl)
  let pre := (impl.params.toList.zip values).map fun (p, value) => (p.var, value)
  SimEAt cx (0, 0) fr (execBlock n cfg env pre impl.body)
    (BlockFlowPost cfg env cx (callEntry impl) fr body.2 impl.body false body.1)
    { state with nextAct := state.nextAct + 1 }

theorem typedCall_of_body {m : Core.Module} {c : ContextId} {ctx : Context} {impl : Impl}
    (hctx : m.contexts[c]? = some ctx) (himpl : m.impls[ctx.impl]? = some impl)
    (profile : NumProfile) (n depth : Nat) (values : List Val) (state : St)
    (hbody : impl.params.size = values.length →
      CalleeBodyAt n ⟨profile, m⟩ ctx.impl impl depth values state) :
    EventualM (enterCall (n + 1) ⟨profile, m⟩ depth c values)
      (fun fuel => callFn fuel ⟨profile, lower m⟩ depth
        (((m.contexts[c]?).map (·.impl)).getD 0) values) state := by
  by_cases hd : depth ≥ maxCallDepth
  · simp only [enterCall, hd, ite_true]
    exact nonfinalStop_eventual .timeout (by simp [IsFinal]) _ _
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
      have hs := hbody hp
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
            have hdiv := SourceDivergence.normalBlock_diverges_false n ⟨profile, m⟩ env pre
              impl.body initial finished normal hb
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
      exact nonfinalStop_eventual _ (by simp [IsFinal]) _ _

end Goose.Lower
