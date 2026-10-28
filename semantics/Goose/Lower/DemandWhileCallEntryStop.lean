import Goose.Lower.DemandWhileCallEntry
import Goose.Lower.DemandWhileCompleteEntryStop

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_scalar_call_loop_entry_nonTimeout_stop {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    {globalFuel targetFuel : Nat} {stop : Stop} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ residual, residual + 1 = globalFuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init)
    (initialized : GIR.initGlobals globalFuel ⟨cfg.profile, lower cfg.mod⟩
      (List.range cfg.mod.globals.size) St.initial = .ok () state)
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (positive : 1 < globalFuel)
    (condition : Expr) (body : Core.Block) (loopOrigin : OriginId) (conditionForm : ControlPrefixExpression condition)
    (outerStatements : impl.body.stmts = [.while condition body loopOrigin]) (outerNoValue : impl.body.value = none)
    (fragment : ∀ middle : St, ReachableScalarCallStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(body.scope, middle.nextScope), (impl.body.scope, state.nextScope)], depth := 1 } body.stmts)
    (noValue : body.value = none)
    (nonTimeout : stop ≠ .timeout)
    (run : GIR.runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
      (callFrame impl state.nextAct 1 []) targetFuel { state with nextAct := state.nextAct + 1 } = .stop stop after) :
    ∃ fuel, Core.runModule fuel cfg St.initial = .stop stop after := by
  obtain ⟨source, bodyPrefix, bodyStopped⟩ := accepted_generated_scalar_call_loop_entry_body accepted expressions initialized positive contextAt implAt
    condition body loopOrigin conditionForm outerStatements outerNoValue fragment noValue
  obtain ⟨taken, remaining, terminal, count, steps, terminalRun, maximal, classified⟩ := runAt_nonTimeout_stopped_prefix
    (initial := ⟨(0, 0), callFrame impl state.nextAct 1 [], { state with nextAct := state.nextAct + 1 }⟩) nonTimeout run
  rcases classified with actualStopped | term | missing
  · have progress := bodyStopped steps actualStopped nonTimeout
    cases progress with
    | aborted bodyFuel bodyStop =>
      obtain ⟨sourceFuel, sourceInitialized⟩ := accepted_source_globals_of_target accepted expressions initialized
      exact accepted_entry_body_stop_to_module accepted sourceInitialized contextAt implAt bodyStop nonTimeout
    | complete bodyCount executed residual evaluated ended =>
      have normal := ended.normal
      subst normal
      obtain ⟨sourceFuel, sourceInitialized⟩ := accepted_source_globals_of_target accepted expressions initialized
      obtain ⟨instruction, returns⟩ := accepted_generated_entry_body_return accepted sourceInitialized contextAt implAt outerNoValue source ended
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
    have decomposition := bodyPrefix steps
    cases decomposition.progress with
    | interior demanded =>
      exact (demanded.whileCall_excludes_maximal_terminal termAt maximal).elim
    | complete bodyCount executed residual evaluated ended =>
      have normal := ended.normal
      subst normal
      obtain ⟨sourceFuel, sourceInitialized⟩ := accepted_source_globals_of_target accepted expressions initialized
      obtain ⟨instruction, returns⟩ := accepted_generated_entry_body_return accepted sourceInitialized contextAt implAt outerNoValue source ended
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


theorem accepted_generated_call_loop_entry_nonTimeout_stop {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    {globalFuel targetFuel : Nat} {stop : Stop} {after : St}
    (accepted : Core.validate cfg.mod = .ok ())
    (expressions : ∀ residual, residual + 1 = globalFuel → ∀ (id : GlobalId) (global : Core.Global),
      cfg.mod.globals[id]? = some global → TypedExprReflection residual cfg [global.ty] global.init)
    (initialized : GIR.initGlobals globalFuel ⟨cfg.profile, lower cfg.mod⟩
      (List.range cfg.mod.globals.size) St.initial = .ok () state)
    (contextAt : cfg.mod.contexts[cfg.mod.entry]? = some ctx) (implAt : cfg.mod.impls[ctx.impl]? = some impl)
    (positive : 1 < globalFuel)
    (condition : Expr) (body : Core.Block) (loopOrigin : OriginId) (conditionForm : ControlPrefixExpression condition)
    (outerStatements : impl.body.stmts = [.while condition body loopOrigin]) (outerNoValue : impl.body.value = none)
    {callContext : ContextId} {arguments : List Arg} {callOrigin statementOrigin : OriginId}
    (bodyStatements : body.stmts = [.expr (.call callContext arguments callOrigin) statementOrigin]) (noValue : body.value = none)
    {calleeContext : Context} {callee : Impl} (callContextAt : cfg.mod.contexts[callContext]? = some calleeContext)
    (calleeAt : cfg.mod.impls[calleeContext.impl]? = some callee)
    (fragment : ∀ current : St, WhileMixedStatements cfg
      { vars := callee.vars, act := current.nextAct, scopes := (callee.body.scope, current.nextScope) :: [], depth := 2 } callee.body.stmts)
    {expression : Expr} (form : ControlPrefixExpression expression) (hasValue : callee.body.value = some expression)
    (shrink : cfg.mod.profile = .shrink)
    (argumentsForm : ∀ (middle : St) {innerState : St} (argumentSource : StmtSource cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(body.scope, middle.nextScope), (impl.body.scope, state.nextScope)], depth := 1 }
      (.expr (.call callContext arguments callOrigin) statementOrigin) innerState), CallMixedArguments argumentSource.rootsEnv.access arguments)
    (stoppedArgumentsForm : ∀ (middle : St) {innerState : St} (argumentSource : StmtSource cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(body.scope, middle.nextScope), (impl.body.scope, state.nextScope)], depth := 1 }
      (.expr (.call callContext arguments callOrigin) statementOrigin) innerState), CallMixedStoppedArguments argumentSource.rootsEnv.access arguments)
    (nonTimeout : stop ≠ .timeout)
    (run : GIR.runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
      (callFrame impl state.nextAct 1 []) targetFuel { state with nextAct := state.nextAct + 1 } = .stop stop after) :
    ∃ fuel, Core.runModule fuel cfg St.initial = .stop stop after := by
  have mixed : ∀ middle : St, ReachableScalarCallStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(body.scope, middle.nextScope), (impl.body.scope, state.nextScope)], depth := 1 } body.stmts := by
    intro middle
    rw [bodyStatements]
    exact ReachableScalarCallStatements.single callContextAt calleeAt (by change 1 < maxCallDepth; decide)
      fragment form hasValue shrink (argumentsForm middle) (stoppedArgumentsForm middle)
  exact accepted_generated_scalar_call_loop_entry_nonTimeout_stop accepted expressions initialized contextAt implAt positive condition body loopOrigin conditionForm
    outerStatements outerNoValue mixed noValue nonTimeout run

#print axioms accepted_generated_call_loop_entry_nonTimeout_stop
#print axioms accepted_generated_scalar_call_loop_entry_nonTimeout_stop
end Goose.Lower
