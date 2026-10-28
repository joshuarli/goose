import Goose.Lower.DemandWhileRunAtStop
import Goose.Lower.DemandWhileSourceEntryStop

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_entry_runAt_stop_to_module {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
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
      ((∃ source : BlockSource cfg ⟨impl.vars, state.nextAct, [], 1⟩ [] impl.body { state with nextAct := state.nextAct + 1 },
        ∃ (bodyFuel consumed rest : Nat) (boundary : DemandRuntimePoint) (flow : Flow),
          consumed + rest = taken ∧
          DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ consumed
            ⟨(0, 0), callFrame impl state.nextAct 1 [], { state with nextAct := state.nextAct + 1 }⟩ boundary ∧
          DemandRuntimePrefix ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ rest boundary terminal ∧
          execBlock bodyFuel cfg ⟨impl.vars, state.nextAct, [], 1⟩ [] impl.body
            { state with nextAct := state.nextAct + 1 } = .ok flow boundary.state ∧
          GeneratedBranchBlockEnd source ⟨[], []⟩ ⟨[], []⟩
            ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ impl.results.toList
            (callEntry impl) none (callFrame impl state.nextAct 1 []) flow boundary) ∨
       (∃ term, instAt (lowerContextAt cfg.mod ctx impl) terminal.point = some (.term term)) ∨
       instAt (lowerContextAt cfg.mod ctx impl) terminal.point = none) := by
  obtain ⟨taken, remaining, terminal, count, steps, terminalRun, maximal, classified⟩ :=
    accepted_generated_target_entry_runAt_stop accepted expressions initialized contextAt implAt fragment noValue nonTimeout run
  rcases classified with ⟨source, progress⟩ | term | missing
  · cases progress with
    | aborted bodyFuel bodyStop =>
      obtain ⟨sourceFuel, sourceInitialized⟩ := accepted_source_globals_of_target accepted expressions initialized
      exact Or.inl (accepted_entry_body_stop_to_module accepted sourceInitialized contextAt implAt bodyStop nonTimeout)
    | complete bodyCount executed residual evaluated post =>
      exact Or.inr ⟨taken, remaining, terminal, count, steps, terminalRun,
        Or.inl ⟨source, _, _, _, _, _, bodyCount, executed, residual, evaluated, post⟩⟩
  · exact Or.inr ⟨taken, remaining, terminal, count, steps, terminalRun, Or.inr (Or.inl term)⟩
  · exact Or.inr ⟨taken, remaining, terminal, count, steps, terminalRun, Or.inr (Or.inr missing)⟩

#print axioms accepted_generated_entry_runAt_stop_to_module
end Goose.Lower
