import Goose.Lower.DemandWhileCompleteModuleStop

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
  exact Or.inl (accepted_generated_module_nonTimeout_stop accepted expressions fragment noValue nonTimeout run)

#print axioms accepted_generated_module_stop_or_terminal
end Goose.Lower
