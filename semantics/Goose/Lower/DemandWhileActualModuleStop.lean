import Goose.Lower.DemandWhileModuleTerminal

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_module_stop_or_terminal {cfg : Cfg} {fuel : Nat} {stop : Stop} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ residual, residual + 1 = fuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init)
    (fragment : ∀ (state : St) (ctx : Context) (impl : Impl),
      cfg.mod.contexts[cfg.mod.entry]? = some ctx → cfg.mod.impls[ctx.impl]? = some impl →
      ∀ middle : St, WhileMixedStatements cfg
        { vars := impl.vars, act := state.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := 1 } impl.body.stmts)
    (noValue : ∀ (ctx : Context) (impl : Impl), cfg.mod.contexts[cfg.mod.entry]? = some ctx →
      cfg.mod.impls[ctx.impl]? = some impl → impl.body.value = none)
    (nonTimeout : stop ≠ .timeout)
    (run : GIR.runModule fuel ⟨cfg.profile, lower cfg.mod⟩ St.initial = .stop stop after) :
    (∃ sourceFuel, Core.runModule sourceFuel cfg St.initial = .stop stop after) ∨
    ∃ (ctx : Context) (impl : Impl) (state : St) (bodyFuel taken remaining : Nat) (terminal : DemandRuntimePoint),
      cfg.mod.contexts[cfg.mod.entry]? = some ctx ∧ cfg.mod.impls[ctx.impl]? = some impl ∧
      GIR.initGlobals fuel ⟨cfg.profile, lower cfg.mod⟩ (List.range cfg.mod.globals.size) St.initial = .ok () state ∧
      taken + remaining = bodyFuel ∧
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
        ⟨(0, 0), callFrame impl state.nextAct 1 [], { state with nextAct := state.nextAct + 1 }⟩ terminal ∧
      GIR.runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ terminal.point terminal.frame
        remaining terminal.state = .stop stop after ∧
      ((∃ term, instAt (lowerContextAt cfg.mod ctx impl) terminal.point = some (.term term)) ∨
        instAt (lowerContextAt cfg.mod ctx impl) terminal.point = none) := by
  have sizes : (lower cfg.mod).globals.size = cfg.mod.globals.size := by simp [lower]
  change (GIR.initGlobals fuel ⟨cfg.profile, lower cfg.mod⟩ (List.range (lower cfg.mod).globals.size) >>= fun _ =>
    GIR.callFn fuel ⟨cfg.profile, lower cfg.mod⟩ 0 (lower cfg.mod).entry [] >>= fun _ => pure ()) St.initial = .stop stop after at run
  rw [sizes] at run
  simp only [bind_apply] at run
  cases globals : GIR.initGlobals fuel ⟨cfg.profile, lower cfg.mod⟩ (List.range cfg.mod.globals.size) St.initial with
  | stop reason final =>
    simp only [globals, Res.stop.injEq] at run
    obtain ⟨reasonEq, finalEq⟩ := run
    subst reason
    subst final
    obtain ⟨sourceFuel, sourceGlobals⟩ := typedGlobals_reflection accepted expressions (.stop stop after)
      (by intro s same; exact nonTimeout (Res.stop.inj same).1) globals
    left
    refine ⟨sourceFuel, ?_⟩
    change (Core.initGlobals sourceFuel cfg (List.range cfg.mod.globals.size) >>= fun _ =>
      Core.enterCall sourceFuel cfg 0 cfg.mod.entry [] >>= fun _ => pure ()) St.initial = .stop stop after
    simp only [bind_apply, sourceGlobals]
  | ok unit state =>
    cases unit
    simp only [globals] at run
    cases call : GIR.callFn fuel ⟨cfg.profile, lower cfg.mod⟩ 0 (lower cfg.mod).entry [] state with
    | ok value final => simp only [call] at run; cases run
    | stop reason final =>
      simp only [call, Res.stop.injEq] at run
      obtain ⟨reasonEq, finalEq⟩ := run
      subst reason
      subst final
      obtain ⟨sourceFuel, sourceGlobals⟩ := accepted_source_globals_of_target accepted expressions globals
      obtain ⟨ctx, impl, contextAt, implAt, noParameters, _, _⟩ := acceptedEntryAfterGlobals accepted sourceFuel sourceGlobals
      obtain ⟨ready⟩ := accepted_generated_target_entry_ready accepted expressions globals contextAt implAt
      have entryExt : ExtT (callEntry impl) (lowerContextAt cfg.mod ctx impl).blocks :=
        ready.extended.of_adv (advB_lowerBlock none [] false impl.body _ _ _ _ rfl)
      have entryEq : (lower cfg.mod).entry = cfg.mod.entry := rfl
      rw [entryEq] at call
      cases fuel with
      | zero =>
        simp [GIR.callFn, timeout, M.stop] at call
        exact (nonTimeout call.1.symm).elim
      | succ fuel =>
        cases fuel with
        | zero =>
          simp [GIR.callFn, GIR.enterFn, Core.maxCallDepth, lookupFn_lower contextAt implAt, timeout, M.stop] at call
          exact (nonTimeout call.1.symm).elim
        | succ bodyFuel =>
          have entered : GIR.callFn (bodyFuel + 2) ⟨cfg.profile, lower cfg.mod⟩ 0 (lower cfg.mod).entry [] state =
              GIR.runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
                (callFrame impl state.nextAct 1 []) bodyFuel { state with nextAct := state.nextAct + 1 } := by
            rw [entryEq]
            simp only [GIR.callFn, show ¬ 0 ≥ Core.maxCallDepth by decide, ite_false,
              lookupFn_lower contextAt implAt, pure_bind]
            exact enterFn_call cfg.mod cfg.profile ctx impl 1 bodyFuel [] state (by simpa using noParameters) entryExt
          have bodyRun := entered.symm.trans call
          rcases accepted_generated_entry_stop_or_terminal accepted expressions globals contextAt implAt
            (fragment state ctx impl contextAt implAt) (noValue ctx impl contextAt implAt) nonTimeout bodyRun with
              stoppedSource | ⟨taken, remaining, terminal, count, steps, terminalRun, terminalCase⟩
          · exact Or.inl stoppedSource
          · exact Or.inr ⟨ctx, impl, state, bodyFuel, taken, remaining, terminal, contextAt, implAt, rfl,
              count, steps, terminalRun, terminalCase⟩

#print axioms accepted_generated_module_stop_or_terminal
end Goose.Lower
