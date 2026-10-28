import Goose.Lower.DemandWhileCallEntry
import Goose.Lower.DemandWhileCompleteEntrySuccess

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_scalar_call_loop_entry_success {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    {globalFuel targetFuel : Nat} {value : Val} {after : St}
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
  obtain ⟨source, bodyPrefix, bodyStopped⟩ := accepted_generated_scalar_call_loop_entry_body accepted expressions initialized positive contextAt implAt
    condition body loopOrigin conditionForm outerStatements outerNoValue fragment noValue
  have decomposition := bodyPrefix steps
  cases decomposition.progress with
  | interior demanded =>
    exact (demanded.whileCall_excludes_maximal_terminal instructionAt maximal).elim
  | complete bodyCount executed residual evaluated ended =>
    have normal := ended.normal
    subst normal
    obtain ⟨sourceFuel, sourceInitialized⟩ := accepted_source_globals_of_target accepted expressions initialized
    obtain ⟨returnAt, returns⟩ := accepted_generated_entry_body_return accepted sourceInitialized contextAt implAt outerNoValue source ended
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


theorem accepted_generated_call_loop_entry_success {cfg : Cfg} {state : St} {ctx : Context} {impl : Impl}
    {globalFuel targetFuel : Nat} {value : Val} {after : St}
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
    (run : GIR.runAt ⟨⟨cfg.profile, lower cfg.mod⟩, lowerContextAt cfg.mod ctx impl⟩ (0, 0)
      (callFrame impl state.nextAct 1 []) targetFuel { state with nextAct := state.nextAct + 1 } = .ok value after) :
    value = .unit ∧ ∃ fuel, Core.runModule fuel cfg St.initial = .ok () after := by
  have mixed : ∀ middle : St, ReachableScalarCallStatements cfg
      { vars := impl.vars, act := state.nextAct, scopes := [(body.scope, middle.nextScope), (impl.body.scope, state.nextScope)], depth := 1 } body.stmts := by
    intro middle
    rw [bodyStatements]
    exact ReachableScalarCallStatements.single callContextAt calleeAt (by change 1 < maxCallDepth; decide)
      fragment form hasValue shrink (argumentsForm middle) (stoppedArgumentsForm middle)
  exact accepted_generated_scalar_call_loop_entry_success accepted expressions initialized contextAt implAt positive condition body loopOrigin conditionForm
    outerStatements outerNoValue mixed noValue run

#print axioms accepted_generated_call_loop_entry_success
#print axioms accepted_generated_scalar_call_loop_entry_success
end Goose.Lower
