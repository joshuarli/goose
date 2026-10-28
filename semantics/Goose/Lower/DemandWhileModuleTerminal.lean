import Goose.Lower.DemandWhileModuleStop
import Goose.Lower.DemandWhileEntryReturn

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_entry_stop_or_terminal {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    {globalFuel targetFuel : Nat} {stop : Stop} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ residual, residual + 1 = globalFuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init)
    (initialized : GIR.initGlobals globalFuel ⟨cfg.profile, lower cfg.mod⟩
      (List.range cfg.mod.globals.size) St.initial = .ok () state)
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (fragment : ∀ middle : St, WhileMixedStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := (impl.body.scope, middle.nextScope) :: [], depth := 1 } impl.body.stmts)
    (noValue : impl.body.value = none) (nonTimeout : stop ≠ .timeout)
    (run : GIR.runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
      (callFrame impl state.nextAct 1 []) targetFuel { state with nextAct := state.nextAct + 1 } = .stop stop after) :
    (∃ fuel, Core.runModule fuel cfg St.initial = .stop stop after) ∨
    ∃ taken remaining terminal,
      taken + remaining = targetFuel ∧
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
        ⟨(0, 0), callFrame impl state.nextAct 1 [], { state with nextAct := state.nextAct + 1 }⟩ terminal ∧
      GIR.runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ terminal.point terminal.frame
        remaining terminal.state = .stop stop after ∧
      ((∃ term, instAt (lowerContextAt cfg.mod ctx impl) terminal.point = some (.term term)) ∨
        instAt (lowerContextAt cfg.mod ctx impl) terminal.point = none) := by
  rcases accepted_generated_entry_runAt_stop_to_module accepted expressions initialized contextAt implAt fragment noValue nonTimeout run with
    stoppedSource | ⟨taken, remaining, terminal, count, steps, terminalRun, completed | term | missing⟩
  · exact Or.inl stoppedSource
  · obtain ⟨source, bodyFuel, consumed, rest, boundary, flow, bodyCount, executed, residual, bodyDone, ended⟩ := completed
    have normal := ended.normal
    subst flow
    obtain ⟨sourceFuel, sourceInitialized⟩ := accepted_source_globals_of_target accepted expressions initialized
    obtain ⟨instruction, returns⟩ := accepted_generated_entry_body_return accepted sourceInitialized contextAt implAt noValue source ended
    rcases residual.uncons with ⟨zero, rfl⟩ | ⟨left, nextPoint, restCount, first, tail⟩
    · cases remaining with
      | zero =>
        change timeout terminal.state = .stop stop after at terminalRun
        simp [timeout, M.stop] at terminalRun
        exact (nonTimeout terminalRun.1.symm).elim
      | succ remaining =>
        have equal := (returns remaining).symm.trans terminalRun
        cases equal
    · exact (runtimeStep_excludes_return instruction first).elim
  · exact Or.inr ⟨taken, remaining, terminal, count, steps, terminalRun, Or.inl term⟩
  · exact Or.inr ⟨taken, remaining, terminal, count, steps, terminalRun, Or.inr missing⟩

#print axioms accepted_generated_entry_stop_or_terminal
end Goose.Lower
