import Goose.Lower.DemandWhileActualModuleStop
import Goose.Lower.DemandRuntimeInstruction
import Goose.Lower.Validation.CfgFunctionCompletion

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_module_stop_or_terminator {cfg : Cfg} {fuel : Nat} {stop : Stop} {after : St}
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
      ∃ term, instAt (lowerContextAt cfg.mod ctx impl) terminal.point = some (.term term) := by
  rcases accepted_generated_module_stop_or_terminal accepted expressions fragment noValue nonTimeout run with
    stoppedSource | ⟨ctx, impl, state, bodyFuel, taken, remaining, terminal, contextAt, implAt, globals,
      count, steps, terminalRun, term | missing⟩
  · exact Or.inl stoppedSource
  · exact Or.inr ⟨ctx, impl, state, bodyFuel, taken, remaining, terminal, contextAt, implAt, globals,
      count, steps, terminalRun, term⟩
  · obtain ⟨ready⟩ := accepted_generated_target_entry_ready accepted expressions globals contextAt implAt
    have entryExt : ExtT (callEntry impl) (lowerContextAt cfg.mod ctx impl).blocks :=
      ready.extended.of_adv (advB_lowerBlock none [] false impl.body _ _ _ _ rfl)
    have terminated : TerminatedBlocks (lowerContextAt cfg.mod ctx impl) := by
      intro block member
      exact Validation.lowerContextAt_terminators cfg.mod ctx impl block (Array.mem_toList_iff.mpr member)
    obtain ⟨entryBlock, entryAt, entryParams⟩ := entryExt.params (b := 0)
      (blk := ⟨(List.range impl.params.size).zip (callEntryTypes impl), #[]⟩) rfl
    have initial : ∃ instruction, instAt (lowerContextAt cfg.mod ctx impl) (0, 0) = some instruction :=
      terminated_first_instruction terminated entryAt
    obtain ⟨instruction, found⟩ := steps.has_instruction terminated initial
    rw [missing] at found
    cases found

#print axioms accepted_generated_module_stop_or_terminator
end Goose.Lower
