import Goose.Lower.DemandRecursiveNestedCallEntrySuccess
import Goose.Lower.DemandWhileCallModuleSuccess

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_recursive_nested_call_module_success {cfg : Cfg} {fuel : Nat} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ residual, residual + 1 = fuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init)
    {ctx : Context} {impl : Impl}
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : ∀ (state middle : St), NestedCallLoopStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(impl.body.scope, middle.nextScope)], depth := 1 } impl.body.stmts)
    (noValue : impl.body.value = none)
    (run : GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩ St.initial = .ok () after) :
    ∃ sourceFuel, Core.runModule sourceFuel cfg St.initial = .ok () after := by
  have sizes : (lower cfg.mod).globals.size = cfg.mod.globals.size := by simp [lower]
  change (GIR.initGlobals fuel ⟨cfg.profile, lower cfg.mod⟩ (List.range (lower cfg.mod).globals.size) >>= fun _ =>
    GIR.callFn fuel ⟨cfg.profile, lower cfg.mod⟩ 0 (lower cfg.mod).entry [] >>= fun _ => pure ()) St.initial = .ok () after at run
  rw [sizes] at run
  simp only [bind_apply] at run
  cases globals : GIR.initGlobals fuel ⟨cfg.profile, lower cfg.mod⟩ (List.range cfg.mod.globals.size) St.initial with
  | stop reason final => simp only [globals] at run; cases run
  | ok unit state =>
    cases unit
    simp only [globals] at run
    cases call : GIR.callFn fuel ⟨cfg.profile, lower cfg.mod⟩ 0 (lower cfg.mod).entry [] state with
    | stop reason final => simp only [call] at run; cases run
    | ok value final =>
      simp only [call, pure_apply, Res.ok.injEq] at run
      obtain ⟨_, rfl⟩ := run
      obtain ⟨sourceFuel, sourceGlobals⟩ := accepted_source_globals_of_target accepted expressions globals
      obtain ⟨entryCtx, entryImpl, entryContextAt, entryImplAt, noParameters, _, _⟩ := acceptedEntryAfterGlobals accepted sourceFuel sourceGlobals
      have ctxEq : entryCtx = ctx := Option.some.inj (entryContextAt.symm.trans contextAt)
      subst entryCtx
      have implEq : entryImpl = impl := Option.some.inj (entryImplAt.symm.trans implAt)
      subst entryImpl
      obtain ⟨ready⟩ := accepted_generated_target_entry_ready accepted expressions globals contextAt implAt
      have entryExt : ExtT (callEntry impl) (lowerContextAt cfg.mod ctx impl).blocks :=
        ready.extended.of_adv (advB_lowerBlock none [] false impl.body _ _ _ _ rfl)
      have entryEq : (lower cfg.mod).entry = cfg.mod.entry := rfl
      rw [entryEq] at call
      cases fuel with
      | zero => simp [GIR.callFn, timeout, M.stop] at call
      | succ fuel =>
        cases fuel with
        | zero => simp [GIR.callFn, GIR.enterFn, Core.maxCallDepth, lookupFn_lower contextAt implAt, timeout, M.stop] at call
        | succ bodyFuel =>
          have entered : GIR.callFn (bodyFuel + 2) ⟨cfg.profile, lower cfg.mod⟩ 0 (lower cfg.mod).entry [] state =
              GIR.runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
                (callFrame impl state.nextAct 1 []) bodyFuel { state with nextAct := state.nextAct + 1 } := by
            rw [entryEq]
            simp only [GIR.callFn, show ¬ 0 ≥ Core.maxCallDepth by decide, ite_false,
              lookupFn_lower contextAt implAt, pure_bind]
            exact enterFn_call cfg.mod cfg.profile ctx impl 1 bodyFuel [] state (by simpa using noParameters) entryExt
          have bodyRun := entered.symm.trans call
          exact (accepted_generated_recursive_nested_call_entry_success accepted expressions globals contextAt implAt (by omega)
            (fragment state) noValue bodyRun).2



#print axioms accepted_generated_recursive_nested_call_module_success
end Goose.Lower
