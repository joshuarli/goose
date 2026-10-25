import Goose.Lower.FuelBoundEndpoints
import Goose.Lower.ContextLowering

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem FuelBoundM.of_eq {sourceFuel targetFuel : Nat} {source target : Nat → M α} {state : St}
    (equal : target targetFuel state = source sourceFuel state) :
    FuelBoundM sourceFuel targetFuel source target state := by
  intro result final done
  exact equal.symm.trans done

theorem FuelBoundM.of_timeout {sourceFuel targetFuel : Nat} {source target : Nat → M α}
    {state after : St} (stopped : target targetFuel state = .stop .timeout after) :
    FuelBoundM sourceFuel targetFuel source target state := by
  intro result final done
  exact (final after (done.symm.trans stopped)).elim

theorem FuelBoundM.map {sourceFuel targetFuel : Nat} {source target : Nat → M α} {state : St}
    (bounded : FuelBoundM sourceFuel targetFuel source target state) (inject : α → β) :
    FuelBoundM sourceFuel targetFuel (fun n => source n >>= fun value => pure (inject value))
      (fun n => target n >>= fun value => pure (inject value)) state := by
  intro result final done
  change (target targetFuel >>= fun value => pure (inject value)) state = result at done
  change (source sourceFuel >>= fun value => pure (inject value)) state = result
  rw [bind_apply] at done
  cases run : target targetFuel state with
  | ok value after =>
    rw [run] at done
    rw [bind_apply,bounded (.ok value after) (NonTimeout.ok _ _) run]
    exact done
  | stop stop after =>
    rw [run] at done
    have nonTimeout : NonTimeout (Res.stop stop after : Res α) := by
      intro failed equal
      cases equal
      exact final after done.symm
    rw [bind_apply,bounded (.stop stop after) nonTimeout run]
    exact done

theorem FuelBoundM.bind_success {sourceFuel targetFuel : Nat} {source₁ target₁ : Nat → M α}
    {source₂ target₂ : α → Nat → M β} {state : St}
    (first : FuelBoundM sourceFuel targetFuel source₁ target₁ state)
    (second : ∀ value after, source₁ sourceFuel state = .ok value after →
      FuelBoundM sourceFuel targetFuel (source₂ value) (target₂ value) after) :
    FuelBoundM sourceFuel targetFuel (fun n => source₁ n >>= fun value => source₂ value n)
      (fun n => target₁ n >>= fun value => target₂ value n) state := by
  intro result final done
  change (target₁ targetFuel >>= fun value => target₂ value targetFuel) state = result at done
  change (source₁ sourceFuel >>= fun value => source₂ value sourceFuel) state = result
  rw [bind_apply] at done
  cases run : target₁ targetFuel state with
  | ok value after =>
    rw [run] at done
    have sourceRun := first (.ok value after) (NonTimeout.ok _ _) run
    rw [bind_apply,sourceRun]
    exact second value after sourceRun result final done
  | stop stop after =>
    rw [run] at done
    have nonTimeout : NonTimeout (Res.stop stop after : Res α) := by
      intro failed equal
      cases equal
      exact final after done.symm
    rw [bind_apply,first (.stop stop after) nonTimeout run]
    exact done

theorem FuelBoundM.source_mono {sourceFuel larger targetFuel : Nat}
    {source target : Nat → M α} {state : St}
    (bounded : FuelBoundM sourceFuel targetFuel source target state)
    (monotone : ∀ n k, n ≤ k → Goose.Proofs.Fuel.MonoM (source n) (source k))
    (enough : sourceFuel ≤ larger) : FuelBoundM larger targetFuel source target state := by
  intro result final done
  have run := bounded result final done
  cases result with
  | ok value after => exact (monotone _ _ enough state).1 value after run
  | stop stop after =>
    exact ((monotone _ _ enough state).2 stop after run).resolve_left
      (by cases stop <;> simp [Goose.Proofs.Fuel.isTimeout] at *; exact (final after rfl).elim)

theorem FuelBoundM.timeout_of_source {sourceFuel targetFuel : Nat}
    {source target : Nat → M α} {state after : St}
    (bounded : FuelBoundM sourceFuel targetFuel source target state)
    (sourceTimeout : source sourceFuel state = .stop .timeout after) :
    ∃ stopped, target targetFuel state = .stop .timeout stopped := by
  cases run : target targetFuel state with
  | ok value stopped =>
    have sourceRun := bounded (.ok value stopped) (NonTimeout.ok _ _) run
    rw [sourceTimeout] at sourceRun
    cases sourceRun
  | stop stop stopped =>
    cases stop with
    | timeout => exact ⟨stopped,rfl⟩
    | fault kind =>
      have sourceRun := bounded (.stop (.fault kind) stopped) (by intro next equal; cases equal) run
      rw [sourceTimeout] at sourceRun
      cases sourceRun
    | abort kind origin =>
      have sourceRun := bounded (.stop (.abort kind origin) stopped) (by intro next equal; cases equal) run
      rw [sourceTimeout] at sourceRun
      cases sourceRun
    | exit code =>
      have sourceRun := bounded (.stop (.exit code) stopped) (by intro next equal; cases equal) run
      rw [sourceTimeout] at sourceRun
      cases sourceRun

theorem FuelBoundM.call_op {sourceFuel targetFuel : Nat} {cx : FnCtx} {fr : GIR.Frame}
    {callee : FnId} {args : List ValueId} {values : List Val} {origin : Option OriginId}
    {source : Nat → M Val} {state : St}
    (arguments : mapList (getVal fr) args = pure values)
    (call : FuelBoundM sourceFuel targetFuel source
      (fun n => callFn n cx.cfg fr.depth callee values) state) :
    FuelBoundM sourceFuel (targetFuel + 1)
      (fun n => source n >>= fun value => pure (RVal.val value))
      (fun n => execOp n cx fr (.call callee args origin)) state := by
  intro result final done
  have step : execOp (targetFuel + 1) cx fr (.call callee args origin) =
      (callFn targetFuel cx.cfg fr.depth callee values >>= fun value => pure (RVal.val value)) := by
    simp only [execOp,arguments,pure_bind]
  change execOp (targetFuel + 1) cx fr (.call callee args origin) state = result at done
  rw [step] at done
  exact call.map RVal.val result final done

theorem FuelBoundM.callFn_of_body {cfg : Cfg} {context : ContextId} {ctx : Context} {impl : Impl}
    {sourceFuel depth fuel : Nat} {values : List Val} {state : St} {entryInsts : List Inst} {entryFrame : Frame}
    (contextAt : cfg.mod.contexts[context]? = some ctx)
    (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (arguments : impl.params.size = values.length) (below : depth < maxCallDepth)
    (entry : enterBlock (lowerContextAt cfg.mod ctx impl)
      ⟨state.nextAct,[],{},depth + 1⟩ 0 (values.map RVal.val) = pure (entryInsts,entryFrame))
    (body : FuelBoundM sourceFuel fuel
      (fun n => Core.execBlock n cfg ⟨impl.vars,state.nextAct,[],depth + 1⟩
        ((impl.params.toList.zip values).map fun (parameter,value) => (parameter.var,value)) impl.body
          >>= expectReturned)
      (fun n => GIR.exec n ⟨⟨cfg.profile,lower cfg.mod⟩,lowerContextAt cfg.mod ctx impl⟩
        entryFrame entryInsts)
      {state with nextAct := state.nextAct + 1}) :
    FuelBoundM (sourceFuel + 1) (fuel + 2) (fun n => Core.enterCall n cfg depth context values)
      (fun n => GIR.callFn n ⟨cfg.profile,lower cfg.mod⟩ depth context values) state := by
  have functionAt := lower_func_at contextAt implAt
  have parameters : (lowerContextAt cfg.mod ctx impl).params.length = values.length := by
    change (impl.params.toList.map fun parameter => tyOfVar impl parameter.var).length = values.length
    simpa using arguments
  have targetStep : GIR.callFn (fuel + 2) ⟨cfg.profile,lower cfg.mod⟩ depth context values state =
      GIR.exec fuel ⟨⟨cfg.profile,lower cfg.mod⟩,lowerContextAt cfg.mod ctx impl⟩
        entryFrame entryInsts {state with nextAct := state.nextAct + 1} := by
    simp only [GIR.callFn, Nat.not_le_of_lt below, ↓reduceIte, lookupFn, functionAt, pure_bind,
      enterFn, parameters, freshAct, bind_apply, pure_apply, entry]
  intro result nonTimeout run
  change GIR.callFn (fuel + 2) ⟨cfg.profile,lower cfg.mod⟩ depth context values state = result at run
  rw [targetStep] at run
  have source := body result nonTimeout run
  change Core.enterCall (sourceFuel + 1) cfg depth context values state = result
  simp only [Core.enterCall, Nat.not_le_of_lt below, ↓reduceIte, lookupContext, lookupImpl,
    contextAt, implAt, pure_bind, arguments, freshAct, bind_apply, pure_apply]
  exact source

end Goose.Lower
