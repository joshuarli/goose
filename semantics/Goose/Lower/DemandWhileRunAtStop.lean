import Goose.Lower.DemandWhileTargetEntry
import Goose.Lower.DemandRunAtPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_target_entry_runAt_stop {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
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
    ∃ taken remaining terminal,
      taken + remaining = targetFuel ∧
      DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ taken
        ⟨(0, 0), callFrame impl state.nextAct 1 [], { state with nextAct := state.nextAct + 1 }⟩ terminal ∧
      GIR.runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ terminal.point terminal.frame
        remaining terminal.state = .stop stop after ∧
      (∀ next, ¬ DemandInstructionStep ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (remaining - 1) terminal next) ∧
      ((∃ source : BlockSource cfg ⟨impl.vars, state.nextAct, [], 1⟩ [] impl.body { state with nextAct := state.nextAct + 1 },
        StoppedLoopBranchBlockPrefix source ⟨[], []⟩ ⟨[], []⟩
          ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ impl.results.toList (callEntry impl) none
          (callFrame impl state.nextAct 1 []) (0, 0) taken terminal stop after) ∨
       (∃ term, instAt (lowerContextAt cfg.mod ctx impl) terminal.point = some (.term term)) ∨
       instAt (lowerContextAt cfg.mod ctx impl) terminal.point = none) := by
  obtain ⟨taken, remaining, terminal, count, steps, terminalRun, maximal, classified⟩ := runAt_nonTimeout_stopped_prefix
    (initial := ⟨(0, 0), callFrame impl state.nextAct 1 [], { state with nextAct := state.nextAct + 1 }⟩) nonTimeout run
  refine ⟨taken, remaining, terminal, count, steps, terminalRun, maximal, ?_⟩
  rcases classified with stopped | term | missing
  · exact Or.inl (accepted_generated_target_entry_body_stopped accepted expressions initialized contextAt implAt
      fragment noValue steps stopped nonTimeout)
  · exact Or.inr (Or.inl term)
  · exact Or.inr (Or.inr missing)

#print axioms accepted_generated_target_entry_runAt_stop
end Goose.Lower
