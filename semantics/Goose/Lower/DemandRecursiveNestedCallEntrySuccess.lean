import Goose.Lower.DemandRecursiveNestedCallEntry
import Goose.Lower.DemandWhileCallEntrySuccess

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_recursive_nested_call_entry_success {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    {globalFuel targetFuel : Nat} {value : Val} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ residual, residual + 1 = globalFuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init)
    (initialized : GIR.initGlobals globalFuel ⟨cfg.profile, lower cfg.mod⟩
      (List.range cfg.mod.globals.size) St.initial = .ok () state)
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (positive : 1 < globalFuel)
    (fragment : ∀ middle : St, NestedCallLoopStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(impl.body.scope, middle.nextScope)], depth := 1 } impl.body.stmts)
    (noValue : impl.body.value = none)
    (run : GIR.runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
      (callFrame impl state.nextAct 1 []) targetFuel { state with nextAct := state.nextAct + 1 } = .ok value after) :
    value = .unit ∧ ∃ fuel, Core.runModule fuel cfg St.initial = .ok () after := by
  obtain ⟨taken, remaining, terminal, count, steps, terminalRun, maximal, classification⟩ := runAt_success_maximal_prefix
    (initial := ⟨(0, 0), callFrame impl state.nextAct 1 [], { state with nextAct := state.nextAct + 1 }⟩) run
  obtain ⟨ready⟩ := accepted_generated_target_entry_ready accepted expressions initialized contextAt implAt
  have entryExt : ExtT (callEntry impl) (lowerContextAt cfg.mod ctx impl).blocks :=
    ready.extended.of_adv (advB_lowerBlock none [] false impl.body _ _ _ _ rfl)
  have terminated : TerminatedBlocks (lowerContextAt cfg.mod ctx impl) := by
    intro block member
    exact Validation.lowerContextAt_terminators cfg.mod ctx impl block (Array.mem_toList_iff.mpr member)
  obtain ⟨entryBlock, entryAt, entryParams⟩ := entryExt.params (b := 0)
    (blk := ⟨(List.range impl.params.size).zip (callEntryTypes impl), #[]⟩) rfl
  have initial : ∃ instruction, instAt (lowerContextAt cfg.mod ctx impl) (0, 0) = some instruction :=
    terminated_first_instruction terminated entryAt
  obtain ⟨instruction, instructionAt⟩ := steps.has_instruction terminated initial
  obtain ⟨term, rfl⟩ := classification instruction instructionAt
  obtain ⟨source, bodyPrefix, bodyStopped⟩ := accepted_generated_recursive_nested_call_entry_body accepted expressions initialized positive contextAt implAt fragment noValue
  have decomposition := bodyPrefix steps
  cases decomposition.progress with
  | interior demanded =>
    exact (demanded.recursiveNestedCall_excludes_maximal_terminal instructionAt maximal).elim
  | complete bodyCount executed residual evaluated ended =>
    have normal := ended.normal
    subst normal
    obtain ⟨sourceFuel, sourceInitialized⟩ := accepted_source_globals_of_target accepted expressions initialized
    obtain ⟨returnAt, returns⟩ := accepted_generated_entry_body_return accepted sourceInitialized contextAt implAt noValue source ended
    rcases residual.uncons with ⟨zero, rfl⟩ | ⟨left, nextPoint, restCount, first, tail⟩
    · cases remaining with
      | zero =>
        change timeout terminal.state = .ok value after at terminalRun
        simp [timeout, M.stop] at terminalRun
      | succ remaining =>
        have equal := (returns remaining).symm.trans terminalRun
        obtain ⟨valueEq, stateEq⟩ := Res.ok.inj equal
        subst value
        subst after
        exact ⟨rfl, accepted_entry_body_success_to_module accepted sourceInitialized contextAt implAt evaluated⟩
    · exact (runtimeStep_excludes_return returnAt first).elim



#print axioms accepted_generated_recursive_nested_call_entry_success
end Goose.Lower
