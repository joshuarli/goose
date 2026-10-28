import Goose.Lower.DemandWhileMixedTerminal
import Goose.Lower.DemandWhileRunAtStop
import Goose.Lower.DemandWhileEntryReturn
import Goose.Lower.DemandRuntimeInstruction
import Goose.Lower.Validation.CfgFunctionCompletion

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_entry_nonTimeout_stop {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
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
    ∃ fuel, Core.runModule fuel cfg St.initial = .stop stop after := by
  obtain ⟨taken, remaining, terminal, count, steps, terminalRun, maximal, classified⟩ :=
    accepted_generated_target_entry_runAt_stop accepted expressions initialized contextAt implAt fragment noValue nonTimeout run
  rcases classified with ⟨source, progress⟩ | term | missing
  · cases progress with
    | aborted bodyFuel bodyStop =>
      obtain ⟨sourceFuel, sourceInitialized⟩ := accepted_source_globals_of_target accepted expressions initialized
      exact accepted_entry_body_stop_to_module accepted sourceInitialized contextAt implAt bodyStop nonTimeout
    | complete bodyCount executed residual evaluated ended =>
      have normal := ended.normal
      subst normal
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
  · obtain ⟨term, termAt⟩ := term
    obtain ⟨source, decomposition⟩ := accepted_generated_target_entry_body_prefix accepted expressions initialized contextAt implAt fragment noValue steps
    cases decomposition.progress with
    | interior demanded =>
      apply (demanded.excludes_maximal_terminal ?_ termAt maximal).elim
      intro statement state source before built initial start map required runtime cursor term terminal fuel maximal
      exact cursor.excludes_maximal_terminal terminal maximal
    | complete bodyCount executed residual evaluated ended =>
      have normal := ended.normal
      subst normal
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
  · obtain ⟨ready⟩ := accepted_generated_target_entry_ready accepted expressions initialized contextAt implAt
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

#print axioms accepted_generated_entry_nonTimeout_stop
end Goose.Lower
