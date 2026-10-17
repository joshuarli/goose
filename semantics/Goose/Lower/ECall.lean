import Goose.Lower.EFlow
import Goose.Lower.Call

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Lower

theorem calleeBlockClaim_of_simulation {m : Core.Module} {i : ImplId} {impl : Impl}
    (hcheck : checkImpl m impl = .ok ()) (profile : NumProfile) (n : Nat)
    (hbody : ∀ pre, BlockESimulation n ⟨profile, m⟩ none (callPre impl) pre false impl.body) :
    CalleeBlockClaim n ⟨profile, m⟩ i impl := by
  intro act depth values hp
  let le := lowerEnv m impl.vars impl.results.toList
  let body := lowerBlock none (callPre impl) false impl.body le (callEntry impl)
  let cx : FnCtx := ⟨⟨profile, lower m⟩, lowerImplAt m i impl⟩
  let fr := callFrame impl act depth values
  let env : Env := ⟨impl.vars, act, [], depth⟩
  have hlow : lowerBlock none (callPre impl) false impl.body le (callEntry impl) =
      (body.1, body.2) := (Prod.eta body).symm
  have hextTail : ExtT (bodyTail impl le body.1 body.2) cx.fn.blocks := by
    rw [lowerImplAt_call_blocks]
    exact extT_finish _
  have hextBody : ExtT body.2 cx.fn.blocks := hextTail.of_adv
    (advB_finishFunction impl body.1 le body.2 (finishFunction impl body.1 le body.2).1
      (bodyTail impl le body.1 body.2) rfl)
  have hs := hbody ((impl.params.toList.zip values).map fun (p, value) => (p.var, value))
    env (callPre_scopes hcheck) le (callEntry impl) body.2 body.1 (0, 0) cx fr
    hlow (callEntry_pp impl) hextBody (callFrame_rel m profile i impl act depth values)
    (callFrame_preRel impl act depth values hp) rfl rfl
  rw [prepareReturn_no_scopes env rfl, bind_pure] at hs
  exact hs

private theorem nonfinal_stop_eventual (err : Stop) (hfinal : ¬ IsFinal err)
    (g : Nat → M α) (state : St) : EventualM (M.stop err) g state := by
  refine ⟨fun value after h => ?_, fun stopped after h hf => ?_⟩
  · cases h
  · cases h
    exact False.elim (hfinal hf)

theorem bodyTail_noResults_cases (impl : Impl) (le : LEnv) (v : ValueId) (ls : LS)
    (hresults : impl.results.isEmpty = true) :
    (ls.cur = none ∧ bodyTail impl le v ls = ls) ∨
    (∃ block, ls.cur = some block ∧
      emitTerm (.ret (if impl.body.value.isSome then [v] else []) none) le ls =
        ((), bodyTail impl le v ls)) := by
  cases hcur : ls.cur with
  | none =>
    left
    refine ⟨rfl, ?_⟩
    unfold bodyTail
    rw [finishFunction_noResults impl le ls v hresults]
    simp [bind_run, isLive_none hcur, pure_run]
  | some block =>
    right
    refine ⟨block, rfl, ?_⟩
    unfold bodyTail
    rw [finishFunction_noResults impl le ls v hresults]
    simp [bind_run, isLive_run hcur]

theorem calleeCallClaim_noResults_of_body {m : Core.Module} {c : ContextId} {ctx : Context} {impl : Impl}
    (hctx : m.contexts[c]? = some ctx) (himpl : m.impls[ctx.impl]? = some impl)
    (hresults : impl.results.isEmpty = true) (profile : NumProfile) (n : Nat)
    (hbody : CalleeBlockClaim n ⟨profile, m⟩ ctx.impl impl) :
    CalleeCallClaim (n + 1) ⟨profile, m⟩ c := by
  intro depth values state
  by_cases hd : depth ≥ maxCallDepth
  · simp only [enterCall, hd, ite_true]
    exact nonfinal_stop_eventual .timeout (by simp [IsFinal]) _ _
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
            rcases bodyTail_noResults_cases impl le body.1 body.2 hresults with
              ⟨hnone, _⟩ | ⟨b, hcur, hterm⟩
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
      exact nonfinal_stop_eventual (.fault .arity) (by simp [IsFinal]) _ _

end Goose.Lower
