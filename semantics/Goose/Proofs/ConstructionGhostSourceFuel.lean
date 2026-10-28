import Goose.Proofs.ConstructionGhostSourceMutual

namespace Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual

inductive FuelSupport (config : EvalConfig) : {α : Type} → Nat → SourceOperation α → Prop
  | timeout (operation : SourceOperation α) : FuelSupport config 0 operation
  | legacy (fuel : Nat) {operation : SourceOperation α} (supported : SupportedOperation config operation) :
      FuelSupport config fuel operation
  | expression (fuel : Nat) (environment : RuntimeActivation) (operand : Expr) (origin : Goose.Core.OriginId)
      (child : FuelSupport config fuel (.value environment operand)) :
      FuelSupport config (fuel + 1) (.statement environment (.expr operand origin))
  | sequence (fuel : Nat) (environment : RuntimeActivation) (statement : Stmt) (rest : List Stmt)
      (head : FuelSupport config fuel (.statement environment statement))
      (tail : FuelSupport config fuel (.statements environment rest)) :
      FuelSupport config (fuel + 1) (.statements environment (statement :: rest))
  | activationBody (fuel : Nat) (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt)
      (body : ∀ environment, FuelSupport config fuel (.statements environment statements)) :
      FuelSupport config (fuel + 1) (.activationBody activation (.mk scope statements none))
  | activation (fuel : Nat) (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt)
      (origin : Goose.Core.OriginId)
      (body : FuelSupport config fuel (.activationBody activation (.mk scope statements none))) :
      FuelSupport config (fuel + 1) (.activation activation (.mk scope statements none) origin)
  | callOne (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (origin : Goose.Core.OriginId)
      (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[]) :
      FuelSupport config 1 (.call environment contextId origin)
  | call (fuel : Nat) (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (origin : Goose.Core.OriginId)
      (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
      (body : ∀ act, FuelSupport config (fuel + 1)
        (.activation ⟨context.impl, act, implementation.vars, [], []⟩ implementation.body origin)) :
      FuelSupport config (fuel + 2) (.call environment contextId origin)
  | valueCall (fuel : Nat) (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (origin : Goose.Core.OriginId)
      (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[])
      (callee : FuelSupport config fuel (.call environment contextId origin)) :
      FuelSupport config (fuel + 1) (.value environment (.call contextId [] origin))

theorem fuelHistory_exists (fuel : Nat) (config : EvalConfig) {α : Type} (operation : SourceOperation α)
    (path : List Nat) (before : ExecutionState) (supported : FuelSupport config fuel operation) :
    SourceHistory config fuel path operation before (execute fuel config operation before) := by
  induction fuel generalizing α operation path before with
  | zero =>
      cases operation <;> simpa [execute, evalValue, execStmt, execStmts, execBlock, execActivationBody,
        enterActivation, invokeCall, evalArguments, evalProduce, Goose.Construct.timeout, EvalM.stop] using
        (SourceHistory.timeout path _ before)
  | succ fuel ih =>
      cases supported with
      | legacy fuel supported => exact history_exists (fuel + 1) config _ path before supported
      | expression _ environment operand origin childSupported =>
          have child := ih (.value environment operand) (path ++ [0]) before childSupported
          have actual : execStmt (fuel + 1) config environment (.expr operand origin) before =
              Goose.Proofs.ConstructionGhostSourceTransition.expressionStatementResult
                (evalValue fuel config environment operand before) := by
            simp only [execStmt, bind, Goose.Proofs.ConstructionGhostSourceTransition.expressionStatementResult]
            cases evalValue fuel config environment operand before <;> rfl
          simp only [execute] at child ⊢
          rw [actual]
          exact .expression child
      | sequence _ environment statement rest headSupported tailSupported =>
          have head := ih (.statement environment statement) (path ++ [0]) before headSupported
          have tail : ∀ value middle, execStmt fuel config environment statement before = .ok (.normal value) middle →
              SourceHistory config fuel (path ++ [1]) (.statements environment rest) middle
                (execStmts fuel config environment rest middle) := by
            intro value middle _
            exact ih (.statements environment rest) (path ++ [1]) middle tailSupported
          have actual : execStmts (fuel + 1) config environment (statement :: rest) before =
              Goose.Proofs.ConstructionGhostSourceTransition.sequenceResult fuel config environment rest
                (execStmt fuel config environment statement before) := by
            simp only [execStmts, bind, Goose.Proofs.ConstructionGhostSourceTransition.sequenceResult]
            cases execStmt fuel config environment statement before with
            | ok flow state => cases flow <;> rfl
            | stop | escape | jump => rfl
          simp only [execute] at head ⊢
          rw [actual]
          exact .next head tail
      | activationBody _ activation scope statements bodySupported =>
          let environment := { activation with scopes := (scope, before.nextScope) :: activation.scopes }
          let ready := Goose.Proofs.ConstructionGhostResultScope.resultScopeStart activation scope before
          have child := ih (.statements environment statements) (path ++ [0]) ready (bodySupported environment)
          simp only [execute] at child ⊢
          rw [activationBody_source]
          exact .activationBody child
      | activation _ activation scope statements origin bodySupported =>
          have body : ∀ implementation, config.module.impls[activation.implementation]? = some implementation →
              SourceHistory config fuel (path ++ [0]) (.activationBody activation (.mk scope statements none)) before
                (execActivationBody fuel config activation [] (.mk scope statements none) before) := by
            intro implementation _
            exact ih (.activationBody activation (.mk scope statements none)) (path ++ [0]) before bodySupported
          simp only [execute]
          rw [activationEnter_source]
          exact .activation body
      | callOne environment contextId origin context implementation contextFound implementationFound resultsEmpty =>
          simpa only [execute, emptyCall_one config environment contextId context implementation origin before
            contextFound implementationFound resultsEmpty] using
            (SourceHistory.callOne contextFound implementationFound resultsEmpty :
              SourceHistory config 1 path (.call environment contextId origin) before _)
      | call fuel environment contextId origin context implementation contextFound implementationFound parametersEmpty resultsEmpty body =>
          by_cases depth : before.activations.length < Goose.Core.maxCallDepth
          · let activation : RuntimeActivation := ⟨context.impl, before.nextAct, implementation.vars, [], []⟩
            let activated := { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }
            have child := ih (.activation activation implementation.body origin) (path ++ [0]) activated (body before.nextAct)
            have actual := emptyCall_enter fuel config environment contextId context implementation origin before
              contextFound implementationFound parametersEmpty resultsEmpty depth
            simp only [execute] at child ⊢
            rw [actual]
            have delivered : (enterActivation (fuel + 1) config activation [] implementation.body origin >>= fun carriers =>
                deliverCarriers (fuel + 1) config.layout [] carriers origin) activated =
                callDeliveryResult (fuel + 1) config origin
                  (enterActivation (fuel + 1) config activation [] implementation.body origin activated) := by
              simp only [bind, callDeliveryResult]
              cases enterActivation (fuel + 1) config activation [] implementation.body origin activated <;> rfl
            rw [delivered]
            exact SourceHistory.callEnter contextFound implementationFound parametersEmpty resultsEmpty depth child
          · have full : Goose.Core.maxCallDepth ≤ before.activations.length := Nat.le_of_not_gt depth
            simpa only [execute, emptyCall_depth fuel config environment contextId context implementation origin before
              contextFound implementationFound parametersEmpty resultsEmpty full] using
              (SourceHistory.callDepth contextFound implementationFound parametersEmpty resultsEmpty full :
                SourceHistory config (fuel + 2) path (.call environment contextId origin) before _)
      | valueCall _ environment contextId origin context implementation contextFound implementationFound resultsEmpty callee =>
          have child := ih (.call environment contextId origin) (path ++ [0]) before callee
          simp only [execute] at child ⊢
          rw [valueCall_source fuel config environment contextId context implementation origin before
            contextFound implementationFound resultsEmpty]
          exact .valueCall contextFound implementationFound resultsEmpty child

private def recursiveContext : Context := ⟨0, "recursive", [], [], []⟩
private def recursiveImplementation : Impl := ⟨"recursive", #[], #[], #[],
  .mk 0 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0, .expr (.call 0 [] 0) 0] none, .unknown⟩
private def recursiveConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[recursiveImplementation], #[recursiveContext], 0, #[], #[], #[]⟩⟩

theorem recursiveCall_supported (fuel : Nat) : ∀ environment,
    FuelSupport recursiveConfig fuel (.call environment 0 0) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro environment
    cases fuel with
    | zero => exact .timeout _
    | succ fuel =>
      cases fuel with
      | zero => exact .callOne environment 0 0 recursiveContext recursiveImplementation rfl rfl rfl
      | succ fuel =>
        apply FuelSupport.call fuel environment 0 0 recursiveContext recursiveImplementation rfl rfl rfl rfl
        intro act
        let activation : RuntimeActivation := ⟨0, act, #[], [], []⟩
        change FuelSupport recursiveConfig (fuel + 1)
          (.activation activation (.mk 0 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0, .expr (.call 0 [] 0) 0] none) 0)
        cases fuel with
        | zero => exact .activation 0 activation 0 _ 0 (.timeout _)
        | succ fuel =>
          apply FuelSupport.activation (fuel + 1)
          apply FuelSupport.activationBody fuel
          intro scopedEnvironment
          cases fuel with
          | zero => exact .timeout _
          | succ fuel =>
            apply FuelSupport.sequence fuel
            · exact .legacy fuel (.expression scopedEnvironment 0 (.value scopedEnvironment
                (.fill (.int .i64) 3 0 rfl (.integer .i64 7))))
            · cases fuel with
              | zero => exact .timeout _
              | succ fuel =>
                apply FuelSupport.sequence fuel
                · cases fuel with
                  | zero => exact .timeout _
                  | succ fuel =>
                    apply FuelSupport.expression fuel
                    cases fuel with
                    | zero => exact .timeout _
                    | succ fuel =>
                      apply FuelSupport.valueCall fuel scopedEnvironment 0 0 recursiveContext recursiveImplementation rfl rfl rfl
                      exact ih fuel (by omega) scopedEnvironment
                · exact .legacy fuel (.empty scopedEnvironment)

private def recursiveEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def recursiveState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem recursiveCall_history (fuel : Nat) :
    SourceHistory recursiveConfig fuel [] (.call recursiveEnvironment 0 0) .initial
      (invokeCall fuel recursiveConfig recursiveEnvironment 0 [] [] 0 .initial) :=
  fuelHistory_exists fuel recursiveConfig (.call recursiveEnvironment 0 0) [] .initial
    (recursiveCall_supported fuel recursiveEnvironment)

theorem recursiveCall_terminal : ∃ state,
    invokeCall 15 recursiveConfig recursiveEnvironment 0 [] [] 0 .initial = .stop .timeout state ∧
    1 < state.nextAct ∧
    SourceHistory recursiveConfig 15 [] (.call recursiveEnvironment 0 0) .initial (.stop .timeout state) := by
  refine ⟨recursiveState (invokeCall 15 recursiveConfig recursiveEnvironment 0 [] [] 0 .initial), ?_, ?_, ?_⟩
  · unfold recursiveState recursiveConfig recursiveContext recursiveImplementation recursiveEnvironment
    cbv
  · unfold recursiveState recursiveConfig recursiveContext recursiveImplementation recursiveEnvironment
    cbv
  · have actual : invokeCall 15 recursiveConfig recursiveEnvironment 0 [] [] 0 .initial =
        .stop .timeout (recursiveState (invokeCall 15 recursiveConfig recursiveEnvironment 0 [] [] 0 .initial)) := by
      unfold recursiveState recursiveConfig recursiveContext recursiveImplementation recursiveEnvironment
      cbv
    have history := recursiveCall_history 15
    rw [actual] at history
    exact history

def moduleCallResult : ExecutionStep (List Carrier) → ExecutionStep Unit
  | .ok carriers state => publishCarriers 0 carriers state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem recursiveModule_history (fuel : Nat) :
    ∃ outcome, SourceHistory recursiveConfig fuel [] (.call recursiveEnvironment 0 0) .initial outcome ∧
      runModule fuel recursiveConfig .initial = moduleCallResult outcome := by
  have history := recursiveCall_history fuel
  refine ⟨_, history, ?_⟩
  simp only [runModule, recursiveConfig, recursiveContext, recursiveImplementation, Array.size_empty, List.range_zero,
    initGlobals, getImplementation, Array.getElem?_singleton, channelsFor, Array.toList_empty, List.mapM_nil, bind, pure]
  change (invokeCall fuel recursiveConfig recursiveEnvironment 0 [] [] 0 >>= fun carriers =>
    publishCarriers 0 carriers) .initial = moduleCallResult
      (invokeCall fuel recursiveConfig recursiveEnvironment 0 [] [] 0 .initial)
  simp only [bind, moduleCallResult]
  cases invokeCall fuel recursiveConfig recursiveEnvironment 0 [] [] 0 .initial <;> rfl

theorem recursiveModule_terminal : ∃ state,
    runModule 15 recursiveConfig .initial = .stop .timeout state ∧ 1 < state.nextAct ∧
    SourceHistory recursiveConfig 15 [] (.call recursiveEnvironment 0 0) .initial (.stop .timeout state) := by
  obtain ⟨state, call, allocated, history⟩ := recursiveCall_terminal
  obtain ⟨outcome, moduleHistory, execution⟩ := recursiveModule_history 15
  have actual := moduleHistory.sound
  change invokeCall 15 recursiveConfig recursiveEnvironment 0 [] [] 0 .initial = outcome at actual
  rw [call] at actual
  subst outcome
  exact ⟨state, execution, allocated, history⟩

#print axioms recursiveModule_history
#print axioms recursiveModule_terminal

#print axioms recursiveCall_supported
#print axioms recursiveCall_history
#print axioms recursiveCall_terminal

#print axioms fuelHistory_exists
end Goose.Proofs.ConstructionGhostSourceFuel
