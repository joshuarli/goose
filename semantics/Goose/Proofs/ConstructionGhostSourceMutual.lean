import Goose.Proofs.ConstructionGhostSourceTransition
import Goose.Proofs.ConstructionGhostBlock
import Goose.Proofs.ConstructionGhostResultScopeCore

namespace Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Construct Goose.Proofs.ConstructionGhostSourceTransition
open Goose.Proofs.ConstructionGhostBlock Goose.Proofs.ConstructionGhostResultScope

inductive SourceOperation : Type → Type
  | value (environment : RuntimeActivation) (expression : Expr) : SourceOperation Value
  | statement (environment : RuntimeActivation) (statement : Stmt) : SourceOperation Flow
  | statements (environment : RuntimeActivation) (statements : List Stmt) : SourceOperation Flow
  | block (environment : RuntimeActivation) (block : Block) : SourceOperation Flow
  | activationBody (activation : RuntimeActivation) (block : Block) : SourceOperation (List Carrier)
  | activation (activation : RuntimeActivation) (block : Block) (origin : Goose.Core.OriginId) : SourceOperation (List Carrier)
  | call (environment : RuntimeActivation) (context : Goose.Core.ContextId) (origin : Goose.Core.OriginId) : SourceOperation (List Carrier)
  | producer (environment : RuntimeActivation) (expression : Expr) : SourceOperation (List Carrier)

def execute (fuel : Nat) (config : EvalConfig) : SourceOperation α → EvalM α
  | .value environment expression => evalValue fuel config environment expression
  | .statement environment statement => execStmt fuel config environment statement
  | .statements environment statements => execStmts fuel config environment statements
  | .block environment block => execBlock fuel config environment [] [] block
  | .activationBody activation block => execActivationBody fuel config activation [] block
  | .activation activation block origin => enterActivation fuel config activation [] block origin
  | .call environment context origin => invokeCall fuel config environment context [] [] origin
  | .producer environment expression => evalProduce fuel config environment [] expression

def conditionalResult (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (yes no : Block) : ExecutionStep Value → ExecutionStep Value
  | .ok value state => (do
      let selected ← expectBool value
      let flow ← execBlock fuel config environment [] [] (if selected then yes else no)
      match flow with
      | .normal value => pure value
      | _ => fault .flow) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

def activationBodyResult (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (scope : Nat) (before : ExecutionState) (outcome : ExecutionStep Flow) : ExecutionStep (List Carrier) :=
  match withScope activation scope before.nextScope (fun _ => resultScopeContinuation activation.channels none
      (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
        (fun channels => evalProduce fuel config
          { activation with scopes := (scope, before.nextScope) :: activation.scopes } channels expression)) outcome)
      (resultScopeStart activation scope before) with
  | .ok (.normal _, carriers) state => .ok carriers state
  | .ok _ state => .stop (.fault .flow) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem activationBody_source (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (scope : Nat) (statements : List Stmt) (before : ExecutionState) :
    execActivationBody (fuel + 1) config activation [] (.mk scope statements none) before =
      activationBodyResult fuel config activation scope before
        (execStmts fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
          statements (resultScopeStart activation scope before)) := by
  obtain ⟨outcome, visits, replay, execution⟩ := execResultScope_statementReplay fuel config activation
    activation.channels scope statements
    (fun environment expression => withCompletionChannels activation.channels (expressionOrigin expression)
      (fun channels => evalProduce fuel config environment channels expression)) before
  simp only [execActivationBody, bind]
  rw [execution, replay.sound]
  simp only [activationBodyResult]
  cases result : withScope activation scope before.nextScope (fun _ =>
    resultScopeContinuation activation.channels none
      (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
        (fun channels => evalProduce fuel config
          { activation with scopes := (scope, before.nextScope) :: activation.scopes } channels expression)) outcome)
    (resultScopeStart activation scope before) with
  | ok pair state => cases pair with | mk flow carriers => cases flow <;> simp [result, bind, pure, fault, EvalM.stop]
  | stop | escape | jump => simp [result]

def activationEnterResult (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (block : Block) (origin : Goose.Core.OriginId) (before : ExecutionState) : ExecutionStep (List Carrier) :=
  match config.module.impls[activation.implementation]? with
  | none => fault .unbound before
  | some implementation => finishActivation config.layout activation (implementation.results.toList.map (·.ty)) origin
      (execActivationBody fuel config activation [] block) before

theorem activationEnter_source (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (block : Block) (origin : Goose.Core.OriginId) (before : ExecutionState) :
    enterActivation (fuel + 1) config activation [] block origin before =
      activationEnterResult fuel config activation block origin before := by
  simp only [enterActivation, activationEnterResult]
  cases config.module.impls[activation.implementation]? <;> rfl

theorem emptyCall_enter (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId : Goose.Core.ContextId) (context : Context) (implementation : Impl) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
    (depth : before.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨context.impl, before.nextAct, implementation.vars, [], []⟩
    let activated := { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }
    invokeCall (fuel + 2) config environment contextId [] [] origin before =
      (enterActivation (fuel + 1) config activation [] implementation.body origin >>= fun carriers =>
        deliverCarriers (fuel + 1) config.layout [] carriers origin) activated := by
  simp only [invokeCall, getImplementation, contextFound, implementationFound, resultsEmpty, parametersEmpty,
    Array.size_empty, Array.toList_empty, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.zip_nil_left, List.mapM_nil, evalArguments, freshAct, EvalM.get, EvalM.set, bind, pure,
    List.map_nil, List.zip_nil_left, Nat.not_le.mpr depth]

theorem emptyCall_depth (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (contextId : Goose.Core.ContextId) (context : Context) (implementation : Impl) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
    (depth : Goose.Core.maxCallDepth ≤ before.activations.length) :
    invokeCall (fuel + 2) config environment contextId [] [] origin before = .stop .timeout before := by
  simp only [invokeCall, getImplementation, contextFound, implementationFound, resultsEmpty, parametersEmpty,
    Array.size_empty, Array.toList_empty, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.zip_nil_left, List.mapM_nil, evalArguments, EvalM.get, bind, pure, depth, if_true,
    Goose.Construct.timeout, EvalM.stop]

theorem emptyCall_one (config : EvalConfig) (environment : RuntimeActivation)
    (contextId : Goose.Core.ContextId) (context : Context) (implementation : Impl) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (resultsEmpty : implementation.results = #[]) :
    invokeCall 1 config environment contextId [] [] origin before = .stop .timeout before := by
  simp only [invokeCall, getImplementation, contextFound, implementationFound, resultsEmpty,
    Array.size_empty, Array.toList_empty, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.zip_nil_left, List.mapM_nil, evalArguments, bind, pure, Goose.Construct.timeout, EvalM.stop]

def callDeliveryResult (fuel : Nat) (config : EvalConfig) (origin : Goose.Core.OriginId) :
    ExecutionStep (List Carrier) → ExecutionStep (List Carrier)
  | .ok carriers state => deliverCarriers fuel config.layout [] carriers origin state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

inductive SourceHistory (config : EvalConfig) :
    {α : Type} → Nat → List Nat → SourceOperation α → ExecutionState → ExecutionStep α → Prop
  | timeout (path : List Nat) (operation : SourceOperation α) (before : ExecutionState) :
      SourceHistory config 0 path operation before (.stop .timeout before)
  | integer (fuel : Nat) (path : List Nat) (environment : RuntimeActivation)
      (ty : Goose.Core.IntTy) (value : Int) (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.value environment (.lit ty value)) before (.ok (.int ty value) before)
  | boolean (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (value : Bool) (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.value environment (.bool value)) before (.ok (.bool value) before)
  | negation {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {operand : Expr}
      {before : ExecutionState} {outcome : ExecutionStep Value}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before outcome) :
      SourceHistory config (fuel + 1) path (.value environment (.not operand)) before (negationResult outcome)
  | fill {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {element : Ty} {count : Nat}
      {operand : Expr} {origin : Goose.Core.OriginId} {before : ExecutionState} {outcome : ExecutionStep Value}
      (fixed : (Ty.arr element count).nonfixed = false)
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before outcome) :
      SourceHistory config (fuel + 1) path (.value environment (.fill (.arr element count) operand origin)) before
        (fillResult count outcome)
  | conditional {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {condition : Expr}
      {yes no : Block} {origin : Goose.Core.OriginId} {before : ExecutionState} {outcome : ExecutionStep Value}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment condition) before outcome)
      (branch : ∀ value middle selected ready, outcome = .ok value middle →
        expectBool value middle = .ok selected ready →
        SourceHistory config fuel (path ++ [if selected then 1 else 2])
          (.block environment (if selected then yes else no)) ready
          (execBlock fuel config environment [] [] (if selected then yes else no) ready)) :
      SourceHistory config (fuel + 1) path (.value environment (.ifE condition yes no origin)) before
        (conditionalResult fuel config environment yes no outcome)
  | block {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {scope : Nat}
      {statements : List Stmt} {before : ExecutionState} {outcome : ExecutionStep Flow}
      (body : SourceHistory config fuel (path ++ [0])
        (.statements { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements)
        { before with nextScope := before.nextScope + 1 } outcome) :
      SourceHistory config (fuel + 1) path (.block environment (.mk scope statements none)) before
        (withScope environment scope before.nextScope (fun _ => blockContinuation fuel config
          { environment with scopes := (scope, before.nextScope) :: environment.scopes } [] none outcome)
          { before with nextScope := before.nextScope + 1 })
  | activationBody {fuel : Nat} {path : List Nat} {activation : RuntimeActivation} {scope : Nat}
      {statements : List Stmt} {before : ExecutionState} {outcome : ExecutionStep Flow}
      (body : SourceHistory config fuel (path ++ [0])
        (.statements { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements)
        (resultScopeStart activation scope before) outcome) :
      SourceHistory config (fuel + 1) path (.activationBody activation (.mk scope statements none)) before
        (activationBodyResult fuel config activation scope before outcome)
  | activation {fuel : Nat} {path : List Nat} {activation : RuntimeActivation} {block : Block}
      {origin : Goose.Core.OriginId} {before : ExecutionState}
      (body : ∀ implementation, config.module.impls[activation.implementation]? = some implementation →
        SourceHistory config fuel (path ++ [0]) (.activationBody activation block) before
          (execActivationBody fuel config activation [] block before)) :
      SourceHistory config (fuel + 1) path (.activation activation block origin) before
        (activationEnterResult fuel config activation block origin before)
  | callOne {path : List Nat} {environment : RuntimeActivation} {contextId : Goose.Core.ContextId}
      {origin : Goose.Core.OriginId} {before : ExecutionState} {context : Context} {implementation : Impl}
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[]) :
      SourceHistory config 1 path (.call environment contextId origin) before (.stop .timeout before)
  | callDepth {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {contextId : Goose.Core.ContextId}
      {origin : Goose.Core.OriginId} {before : ExecutionState} {context : Context} {implementation : Impl}
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
      (depth : Goose.Core.maxCallDepth ≤ before.activations.length) :
      SourceHistory config (fuel + 2) path (.call environment contextId origin) before (.stop .timeout before)
  | callEnter {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {contextId : Goose.Core.ContextId}
      {origin : Goose.Core.OriginId} {before : ExecutionState} {context : Context} {implementation : Impl}
      {outcome : ExecutionStep (List Carrier)}
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
      (depth : before.activations.length < Goose.Core.maxCallDepth)
      (child : SourceHistory config (fuel + 1) (path ++ [0])
        (.activation ⟨context.impl, before.nextAct, implementation.vars, [], []⟩ implementation.body origin)
        { before with nextAct := before.nextAct + 1, activations := (⟨context.impl, before.nextAct, implementation.vars, [], []⟩ : RuntimeActivation) :: before.activations } outcome) :
      SourceHistory config (fuel + 2) path (.call environment contextId origin) before
        (callDeliveryResult (fuel + 1) config origin outcome)
  | expression {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {operand : Expr}
      {origin : Goose.Core.OriginId} {before : ExecutionState} {outcome : ExecutionStep Value}
      (child : SourceHistory config fuel (path ++ [0]) (.value environment operand) before outcome) :
      SourceHistory config (fuel + 1) path (.statement environment (.expr operand origin)) before
        (expressionStatementResult outcome)
  | done (fuel : Nat) (path : List Nat) (environment : RuntimeActivation) (before : ExecutionState) :
      SourceHistory config (fuel + 1) path (.statements environment []) before (.ok (.normal .unit) before)
  | next {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {statement : Stmt} {rest : List Stmt}
      {before : ExecutionState} {outcome : ExecutionStep Flow}
      (head : SourceHistory config fuel (path ++ [0]) (.statement environment statement) before outcome)
      (tail : ∀ value middle, outcome = .ok (.normal value) middle →
        SourceHistory config fuel (path ++ [1]) (.statements environment rest) middle
          (execStmts fuel config environment rest middle)) :
      SourceHistory config (fuel + 1) path (.statements environment (statement :: rest)) before
        (sequenceResult fuel config environment rest outcome)
  | discard {fuel : Nat} {path : List Nat} {environment : RuntimeActivation} {expression : Expr}
      {before : ExecutionState} {outcome : ExecutionStep Value} (supported : SupportedValue expression)
      (child : SourceHistory config fuel (path ++ [0]) (.value environment expression) before outcome) :
      SourceHistory config (fuel + 1) path (.producer environment expression) before (discardValue outcome)

theorem SourceHistory.sound (history : SourceHistory config fuel path operation before outcome) :
    execute fuel config operation before = outcome := by
  induction history with
  | timeout path operation before => cases operation <;> simp [execute, evalValue, execStmt, execStmts, execBlock, execActivationBody, enterActivation, invokeCall, evalProduce, Goose.Construct.timeout, EvalM.stop]
  | integer | boolean => simp [execute, evalValue, pure]
  | @negation fuel path environment operand before outcome child ih =>
      simp only [execute] at ih ⊢
      simp only [evalValue, bind, ih, negationResult]
      cases outcome <;> rfl
  | @fill fuel path environment element count operand origin before outcome fixed child ih =>
      simp only [execute] at ih ⊢
      simp only [evalValue, fixed, Bool.false_eq_true, ↓reduceIte, bind, ih, fillResult]
      cases outcome <;> rfl
  | @conditional fuel path environment condition yes no origin before outcome child branch ihChild ihBranch =>
      simp only [execute] at ihChild ⊢
      simp only [evalValue, bind, ihChild, conditionalResult]
      cases outcome with
      | ok value state =>
          simp only
          cases result : expectBool value state with
          | ok selected ready => simp only [result]; cases selected <;> rfl
          | stop | escape | jump => simp only [result]
      | stop | escape | jump => rfl
  | @block fuel path environment scope statements before outcome body ihBody =>
      simp only [execute] at ihBody ⊢
      have bound : bindAll environment.act before.nextScope [] { before with nextScope := before.nextScope + 1 } =
          .ok () { before with nextScope := before.nextScope + 1 } := by simp [bindAll, bind, pure]
      obtain ⟨actual, visits, replay, execution⟩ := execBlock_statementReplay fuel config environment [] [] scope
        statements none before { before with nextScope := before.nextScope + 1 } bound
      rw [execution, ← replay.sound, ihBody]
  | @activationBody fuel path activation scope statements before outcome body ihBody =>
      simp only [execute] at ihBody ⊢
      rw [activationBody_source, ihBody]
  | @activation fuel path activation block origin before body ihBody =>
      simp only [execute]
      exact activationEnter_source fuel config activation block origin before
  | callOne contextFound implementationFound resultsEmpty =>
      exact emptyCall_one _ _ _ _ _ _ _ contextFound implementationFound resultsEmpty
  | callDepth contextFound implementationFound parametersEmpty resultsEmpty depth =>
      exact emptyCall_depth _ _ _ _ _ _ _ _ contextFound implementationFound parametersEmpty resultsEmpty depth
  | @callEnter fuel path environment contextId origin before context implementation outcome contextFound
      implementationFound parametersEmpty resultsEmpty depth child ih =>
      simp only [execute] at ih ⊢
      rw [emptyCall_enter fuel config environment contextId context implementation origin before
        contextFound implementationFound parametersEmpty resultsEmpty depth]
      simp only [bind, ih, callDeliveryResult]
      cases outcome <;> rfl
  | @expression fuel path environment operand origin before outcome child ih =>
      simp only [execute] at ih ⊢
      simp only [execStmt, bind, ih, expressionStatementResult]
      cases outcome <;> rfl
  | done => simp [execute, execStmts, pure]
  | @next fuel path environment statement rest before outcome head tail ihHead ihTail =>
      simp only [execute] at ihHead ⊢
      simp only [execStmts, bind, ihHead, sequenceResult]
      cases outcome with
      | ok flow state => cases flow <;> rfl
      | stop | escape | jump => rfl
  | @discard fuel path environment expression before outcome supported child ih =>
      simp only [execute] at ih ⊢
      rw [emptyProducer_source fuel config environment expression before supported, ih]

theorem ValueHistory.toSource (history : ValueHistory config environment fuel path expression before outcome) :
    SourceHistory config fuel path (.value environment expression) before outcome := by
  induction history with
  | timeout => exact .timeout _ _ _
  | integer => exact .integer _ _ _ _ _ _
  | boolean => exact .boolean _ _ _ _ _
  | negation child ih => exact .negation ih
  | fill fixed child ih => exact .fill fixed ih

theorem StatementHistory.toSource (history : StatementHistory config environment fuel path statement before outcome) :
    SourceHistory config fuel path (.statement environment statement) before outcome := by
  cases history with
  | timeout => exact .timeout _ _ _
  | expression child => exact .expression (ValueHistory.toSource child)

theorem StatementSequenceHistory.toSource
    (history : StatementSequenceHistory config environment fuel path statements before outcome) :
    SourceHistory config fuel path (.statements environment statements) before outcome := by
  induction history with
  | timeout => exact .timeout _ _ _
  | done => exact .done _ _ _ _
  | next head tail ih => exact .next (StatementHistory.toSource head) ih

theorem ProducerHistory.toSource (history : ProducerHistory config environment fuel path expression before outcome) :
    SourceHistory config fuel path (.producer environment expression) before outcome := by
  cases history with
  | timeout => exact .timeout _ _ _
  | discard supported child => exact .discard supported (ValueHistory.toSource child)

theorem value_exists (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (expression : Expr) (before : ExecutionState) (supported : SupportedValue expression) :
    SourceHistory config fuel path (.value environment expression) before (evalValue fuel config environment expression before) :=
  ValueHistory.toSource (valueHistory_exists fuel config environment path expression before supported)

theorem statements_exist (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (statements : List Stmt) (before : ExecutionState)
    (supported : ∀ statement ∈ statements, SupportedStatement statement) :
    SourceHistory config fuel path (.statements environment statements) before
      (execStmts fuel config environment statements before) :=
  StatementSequenceHistory.toSource (statementSequenceHistory_exists fuel config environment path statements before supported)

inductive SupportedOperation (config : EvalConfig) : {α : Type} → SourceOperation α → Prop
  | value (environment : RuntimeActivation) {expression : Expr} (supported : SupportedValue expression) :
      SupportedOperation config (.value environment expression)
  | conditional (environment : RuntimeActivation) {condition : Expr} {yes no : Block} (origin : Goose.Core.OriginId)
      (conditionSupported : SupportedOperation config (.value environment condition))
      (yesSupported : SupportedOperation config (.block environment yes))
      (noSupported : SupportedOperation config (.block environment no)) :
      SupportedOperation config (.value environment (.ifE condition yes no origin))
  | expression (environment : RuntimeActivation) {operand : Expr} (origin : Goose.Core.OriginId)
      (supported : SupportedOperation config (.value environment operand)) :
      SupportedOperation config (.statement environment (.expr operand origin))
  | empty (environment : RuntimeActivation) : SupportedOperation config (.statements environment [])
  | sequence (environment : RuntimeActivation) {statement : Stmt} {rest : List Stmt}
      (head : SupportedOperation config (.statement environment statement))
      (tail : SupportedOperation config (.statements environment rest)) :
      SupportedOperation config (.statements environment (statement :: rest))
  | block (environment : RuntimeActivation) (scope : Nat) (statements : List Stmt)
      (body : ∀ scopedEnvironment, SupportedOperation config (.statements scopedEnvironment statements)) :
      SupportedOperation config (.block environment (.mk scope statements none))
  | activationBody (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt)
      (body : ∀ environment, SupportedOperation config (.statements environment statements)) :
      SupportedOperation config (.activationBody activation (.mk scope statements none))
  | activation (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt)
      (origin : Goose.Core.OriginId)
      (body : ∀ environment, SupportedOperation config (.statements environment statements)) :
      SupportedOperation config (.activation activation (.mk scope statements none) origin)
  | call (environment : RuntimeActivation) (contextId : Goose.Core.ContextId) (origin : Goose.Core.OriginId)
      (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
      (body : ∀ act, SupportedOperation config
        (.activation ⟨context.impl, act, implementation.vars, [], []⟩ implementation.body origin)) :
      SupportedOperation config (.call environment contextId origin)
  | producer (environment : RuntimeActivation) {expression : Expr} (supported : SupportedValue expression) :
      SupportedOperation config (.producer environment expression)

theorem history_exists (fuel : Nat) (config : EvalConfig) {α : Type} (operation : SourceOperation α)
    (path : List Nat) (before : ExecutionState) (supported : SupportedOperation config operation) :
    SourceHistory config fuel path operation before (execute fuel config operation before) := by
  induction fuel generalizing α operation path before with
  | zero =>
      cases operation <;> simpa [execute, evalValue, execStmt, execStmts, execBlock, execActivationBody, enterActivation, invokeCall, evalProduce,
        Goose.Construct.timeout, EvalM.stop] using (SourceHistory.timeout path _ before)
  | succ fuel ih =>
      cases supported with
      | value environment supported =>
          exact value_exists (fuel + 1) config environment path _ before supported
      | @conditional environment condition yes no origin conditionSupported yesSupported noSupported =>
          have child := ih (.value environment condition) (path ++ [0]) before conditionSupported
          have branch : ∀ value middle selected ready,
              evalValue fuel config environment condition before = .ok value middle →
              expectBool value middle = .ok selected ready →
              SourceHistory config fuel (path ++ [if selected then 1 else 2])
                (.block environment (if selected then yes else no)) ready
                (execBlock fuel config environment [] [] (if selected then yes else no) ready) := by
            intro value middle selected ready _ _
            cases selected with
            | false => exact ih (.block environment no) (path ++ [2]) ready noSupported
            | true => exact ih (.block environment yes) (path ++ [1]) ready yesSupported
          have actual : evalValue (fuel + 1) config environment (.ifE condition yes no origin) before =
              conditionalResult fuel config environment yes no (evalValue fuel config environment condition before) := by
            simp only [evalValue, bind, conditionalResult]
            cases result : evalValue fuel config environment condition before with
            | ok value state =>
                simp only
                cases check : expectBool value state with
                | ok selected ready => simp only [check]; cases selected <;> rfl
                | stop | escape | jump => simp only [check]
            | stop | escape | jump => rfl
          simp only [execute]
          rw [actual]
          exact .conditional child branch
      | @expression environment operand origin supported =>
          have child := ih (.value environment operand) (path ++ [0]) before supported
          have actual : execStmt (fuel + 1) config environment (.expr operand origin) before =
              expressionStatementResult (evalValue fuel config environment operand before) := by
            simp only [execStmt, bind, expressionStatementResult]
            cases evalValue fuel config environment operand before <;> rfl
          simp only [execute]
          rw [actual]
          exact .expression child
      | empty environment => simpa [execute, execStmts, pure] using
          (SourceHistory.done fuel path environment before :
            SourceHistory config (fuel + 1) path (.statements environment []) before _)
      | @sequence environment statement rest headSupported tailSupported =>
          have head := ih (.statement environment statement) (path ++ [0]) before headSupported
          have tail : ∀ value middle, execStmt fuel config environment statement before = .ok (.normal value) middle →
              SourceHistory config fuel (path ++ [1]) (.statements environment rest) middle
                (execStmts fuel config environment rest middle) := by
            intro value middle _
            exact ih (.statements environment rest) (path ++ [1]) middle tailSupported
          have actual : execStmts (fuel + 1) config environment (statement :: rest) before =
              sequenceResult fuel config environment rest (execStmt fuel config environment statement before) := by
            simp only [execStmts, bind, sequenceResult]
            cases execStmt fuel config environment statement before with
            | ok flow state => cases flow <;> rfl
            | stop | escape | jump => rfl
          simp only [execute]
          rw [actual]
          exact .next head tail
      | block environment scope statements bodySupported =>
          let scopedEnvironment := { environment with scopes := (scope, before.nextScope) :: environment.scopes }
          let ready := { before with nextScope := before.nextScope + 1 }
          have child := ih (.statements scopedEnvironment statements) (path ++ [0]) ready (bodySupported scopedEnvironment)
          have bound : bindAll environment.act before.nextScope [] ready = .ok () ready := by simp [ready, bindAll, bind, pure]
          obtain ⟨outcome, visits, replay, execution⟩ :=
            execBlock_statementReplay fuel config environment [] [] scope statements none before ready bound
          simp only [execute]
          rw [execution, ← replay.sound]
          exact .block child
      | activationBody activation scope statements bodySupported =>
          let environment := { activation with scopes := (scope, before.nextScope) :: activation.scopes }
          let ready := resultScopeStart activation scope before
          have child := ih (.statements environment statements) (path ++ [0]) ready (bodySupported environment)
          simp only [execute]
          rw [activationBody_source]
          exact .activationBody child
      | activation activation scope statements origin bodySupported =>
          have body : ∀ implementation, config.module.impls[activation.implementation]? = some implementation →
              SourceHistory config fuel (path ++ [0]) (.activationBody activation (.mk scope statements none)) before
                (execActivationBody fuel config activation [] (.mk scope statements none) before) := by
            intro implementation _
            exact ih (.activationBody activation (.mk scope statements none)) (path ++ [0]) before
              (.activationBody activation scope statements bodySupported)
          simp only [execute]
          rw [activationEnter_source]
          exact .activation body
      | call environment contextId origin context implementation contextFound implementationFound parametersEmpty resultsEmpty body =>
          cases fuel with
          | zero =>
              simpa only [execute, emptyCall_one config environment contextId context implementation origin before
                contextFound implementationFound resultsEmpty] using
                (SourceHistory.callOne contextFound implementationFound resultsEmpty :
                  SourceHistory config 1 path (.call environment contextId origin) before _)
          | succ fuel =>
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
      | producer environment supported =>
          exact ProducerHistory.toSource (producerHistory_exists (fuel + 1) config environment path _ before supported)

private def witnessConfig : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def witnessExpression : Expr :=
  .ifE (.bool true) (.mk 1 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none)
    (.mk 2 [] none) 0
private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem witness_nestedFill : ∃ after,
    evalValue 40 witnessConfig witnessEnvironment witnessExpression .initial = .ok .unit after ∧
    SourceHistory witnessConfig 40 [] (.value witnessEnvironment witnessExpression) .initial (.ok .unit after) := by
  have supported : SupportedOperation witnessConfig (.value witnessEnvironment witnessExpression) := by
    unfold witnessExpression
    apply SupportedOperation.conditional
    · exact .value _ (.boolean true)
    · apply SupportedOperation.block
      intro environment
      exact .sequence environment (.expression environment 0 (.value environment
        (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))) (.empty environment)
    · exact .block _ _ _ (fun environment => .empty environment)
  have history := history_exists 40 witnessConfig (.value witnessEnvironment witnessExpression) [] .initial supported
  refine ⟨witnessState (evalValue 40 witnessConfig witnessEnvironment witnessExpression .initial), ?_, ?_⟩
  · unfold witnessConfig witnessEnvironment witnessExpression witnessState
    cbv
  · have actual : evalValue 40 witnessConfig witnessEnvironment witnessExpression .initial =
        .ok .unit (witnessState (evalValue 40 witnessConfig witnessEnvironment witnessExpression .initial)) := by
      unfold witnessConfig witnessEnvironment witnessExpression witnessState
      cbv
    change SourceHistory witnessConfig 40 [] (.value witnessEnvironment witnessExpression) .initial
      (evalValue 40 witnessConfig witnessEnvironment witnessExpression .initial) at history
    rw [actual] at history
    exact history

theorem witness_activationBody : ∃ after,
    execActivationBody 40 witnessConfig witnessEnvironment [] (.mk 0 [.expr witnessExpression 0] none) .initial =
      .ok [] after ∧
    SourceHistory witnessConfig 40 [] (.activationBody witnessEnvironment (.mk 0 [.expr witnessExpression 0] none))
      .initial (.ok [] after) := by
  have bodySupported : ∀ environment, SupportedOperation witnessConfig (.statements environment [.expr witnessExpression 0]) := by
    intro environment
    apply SupportedOperation.sequence
    · apply SupportedOperation.expression
      unfold witnessExpression
      apply SupportedOperation.conditional
      · exact .value _ (.boolean true)
      · apply SupportedOperation.block
        intro inner
        exact .sequence inner (.expression inner 0 (.value inner
          (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))) (.empty inner)
      · exact .block _ _ _ (fun inner => .empty inner)
    · exact .empty environment
  have history := history_exists 40 witnessConfig
    (.activationBody witnessEnvironment (.mk 0 [.expr witnessExpression 0] none)) [] .initial
    (.activationBody witnessEnvironment 0 [.expr witnessExpression 0] bodySupported)
  refine ⟨witnessState (execActivationBody 40 witnessConfig witnessEnvironment []
    (.mk 0 [.expr witnessExpression 0] none) .initial), ?_, ?_⟩
  · unfold witnessConfig witnessEnvironment witnessExpression witnessState
    cbv
  · have actual : execActivationBody 40 witnessConfig witnessEnvironment []
        (.mk 0 [.expr witnessExpression 0] none) .initial =
        .ok [] (witnessState (execActivationBody 40 witnessConfig witnessEnvironment []
          (.mk 0 [.expr witnessExpression 0] none) .initial)) := by
      unfold witnessConfig witnessEnvironment witnessExpression witnessState
      cbv
    change SourceHistory witnessConfig 40 [] (.activationBody witnessEnvironment (.mk 0 [.expr witnessExpression 0] none))
      .initial (execActivationBody 40 witnessConfig witnessEnvironment [] (.mk 0 [.expr witnessExpression 0] none) .initial) at history
    rw [actual] at history
    exact history

private def activationWitnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[⟨"callee", #[], #[], #[],
    .mk 0 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none, .unknown⟩], #[], 0, #[], #[], #[]⟩⟩
private def activationWitnessBlock : Block :=
  .mk 0 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none

theorem witness_activationEntry : ∃ after,
    enterActivation 40 activationWitnessConfig witnessEnvironment [] activationWitnessBlock 0 .initial = .ok [] after ∧
    SourceHistory activationWitnessConfig 40 [] (.activation witnessEnvironment activationWitnessBlock 0)
      .initial (.ok [] after) := by
  have bodySupported : ∀ environment, SupportedOperation activationWitnessConfig
      (.statements environment [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0]) := by
    intro environment
    exact .sequence environment (.expression environment 0 (.value environment
      (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))) (.empty environment)
  have supported : SupportedOperation activationWitnessConfig (.activation witnessEnvironment activationWitnessBlock 0) := by
    unfold activationWitnessBlock
    exact .activation witnessEnvironment 0 _ 0 bodySupported
  have history := history_exists 40 activationWitnessConfig (.activation witnessEnvironment activationWitnessBlock 0)
    [] .initial supported
  refine ⟨witnessState (enterActivation 40 activationWitnessConfig witnessEnvironment [] activationWitnessBlock 0 .initial), ?_, ?_⟩
  · unfold activationWitnessConfig witnessEnvironment activationWitnessBlock witnessState
    cbv
  · have actual : enterActivation 40 activationWitnessConfig witnessEnvironment [] activationWitnessBlock 0 .initial =
        .ok [] (witnessState (enterActivation 40 activationWitnessConfig witnessEnvironment [] activationWitnessBlock 0 .initial)) := by
      unfold activationWitnessConfig witnessEnvironment activationWitnessBlock witnessState
      cbv
    change SourceHistory activationWitnessConfig 40 [] (.activation witnessEnvironment activationWitnessBlock 0)
      .initial (enterActivation 40 activationWitnessConfig witnessEnvironment [] activationWitnessBlock 0 .initial) at history
    rw [actual] at history
    exact history

private def callWitnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[⟨"callee", #[], #[], #[],
    .mk 0 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none, .unknown⟩],
    #[⟨0, "callee", [], [], []⟩], 0, #[], #[], #[]⟩⟩
private def callWitnessContext : Context := ⟨0, "callee", [], [], []⟩
private def callWitnessImplementation : Impl := ⟨"callee", #[], #[], #[],
  .mk 0 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none, .unknown⟩

theorem witness_call : ∃ after,
    invokeCall 40 callWitnessConfig witnessEnvironment 0 [] [] 0 .initial = .ok [] after ∧
    SourceHistory callWitnessConfig 40 [] (.call witnessEnvironment 0 0) .initial (.ok [] after) := by
  have bodySupported : ∀ environment, SupportedOperation callWitnessConfig
      (.statements environment [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0]) := by
    intro environment
    exact .sequence environment (.expression environment 0 (.value environment
      (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))) (.empty environment)
  have supported : SupportedOperation callWitnessConfig (.call witnessEnvironment 0 0) := by
    apply SupportedOperation.call witnessEnvironment 0 0 callWitnessContext callWitnessImplementation
    · rfl
    · rfl
    · rfl
    · rfl
    · intro act
      exact .activation _ 0 _ 0 bodySupported
  have history := history_exists 40 callWitnessConfig (.call witnessEnvironment 0 0) [] .initial supported
  refine ⟨witnessState (invokeCall 40 callWitnessConfig witnessEnvironment 0 [] [] 0 .initial), ?_, ?_⟩
  · unfold callWitnessConfig witnessEnvironment witnessState
    cbv
  · have actual : invokeCall 40 callWitnessConfig witnessEnvironment 0 [] [] 0 .initial =
        .ok [] (witnessState (invokeCall 40 callWitnessConfig witnessEnvironment 0 [] [] 0 .initial)) := by
      unfold callWitnessConfig witnessEnvironment witnessState
      cbv
    change SourceHistory callWitnessConfig 40 [] (.call witnessEnvironment 0 0) .initial
      (invokeCall 40 callWitnessConfig witnessEnvironment 0 [] [] 0 .initial) at history
    rw [actual] at history
    exact history

#print axioms witness_call

#print axioms witness_activationEntry

#print axioms witness_activationBody

#print axioms witness_nestedFill

#print axioms emptyCall_enter
#print axioms emptyCall_depth
#print axioms emptyCall_one
#print axioms activationEnter_source
#print axioms activationBody_source
#print axioms history_exists

#print axioms ValueHistory.toSource
#print axioms StatementSequenceHistory.toSource
#print axioms value_exists
#print axioms statements_exist

#print axioms SourceHistory.sound
end Goose.Proofs.ConstructionGhostSourceMutual
