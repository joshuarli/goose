import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionGhostSourceTransition
open Goose.Construct

inductive SupportedValue : Expr → Prop
  | integer (ty : Goose.Core.IntTy) (value : Int) : SupportedValue (.lit ty value)
  | boolean (value : Bool) : SupportedValue (.bool value)
  | negation {operand : Expr} : SupportedValue operand → SupportedValue (.not operand)

inductive SupportedStatement : Stmt → Prop
  | expression {operand : Expr} (origin : Goose.Core.OriginId) :
      SupportedValue operand → SupportedStatement (.expr operand origin)

def negationResult : ExecutionStep Value → ExecutionStep Value
  | .ok value state => (do pure (Value.bool (!(← expectBool value)))) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

def expressionStatementResult : ExecutionStep Value → ExecutionStep Flow
  | .ok _ state => .ok (.normal .unit) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

inductive ValueHistory (config : EvalConfig) (environment : RuntimeActivation) :
    Nat → List Nat → Expr → ExecutionState → ExecutionStep Value → Prop
  | timeout (path : List Nat) (expression : Expr) (before : ExecutionState) :
      ValueHistory config environment 0 path expression before (.stop .timeout before)
  | integer (fuel : Nat) (path : List Nat) (ty : Goose.Core.IntTy) (value : Int) (before : ExecutionState) :
      ValueHistory config environment (fuel + 1) path (.lit ty value) before (.ok (.int ty value) before)
  | boolean (fuel : Nat) (path : List Nat) (value : Bool) (before : ExecutionState) :
      ValueHistory config environment (fuel + 1) path (.bool value) before (.ok (.bool value) before)
  | negation {fuel : Nat} {path : List Nat} {operand : Expr} {before : ExecutionState} {outcome : ExecutionStep Value}
      (child : ValueHistory config environment fuel (path ++ [0]) operand before outcome) :
      ValueHistory config environment (fuel + 1) path (.not operand) before (negationResult outcome)

inductive StatementHistory (config : EvalConfig) (environment : RuntimeActivation) :
    Nat → List Nat → Stmt → ExecutionState → ExecutionStep Flow → Prop
  | timeout (path : List Nat) (statement : Stmt) (before : ExecutionState) :
      StatementHistory config environment 0 path statement before (.stop .timeout before)
  | expression {fuel : Nat} {path : List Nat} {operand : Expr} {origin : Goose.Core.OriginId}
      {before : ExecutionState} {outcome : ExecutionStep Value}
      (child : ValueHistory config environment fuel (path ++ [0]) operand before outcome) :
      StatementHistory config environment (fuel + 1) path (.expr operand origin) before (expressionStatementResult outcome)

theorem ValueHistory.sound (history : ValueHistory config environment fuel path expression before outcome) :
    evalValue fuel config environment expression before = outcome := by
  induction history with
  | timeout => simp [evalValue, Goose.Construct.timeout, EvalM.stop]
  | integer => simp [evalValue, pure]
  | boolean => simp [evalValue, pure]
  | @negation fuel path operand before outcome child ih =>
      simp only [evalValue, bind, ih, negationResult]
      cases outcome <;> rfl

theorem StatementHistory.sound (history : StatementHistory config environment fuel path statement before outcome) :
    execStmt fuel config environment statement before = outcome := by
  cases history with
  | timeout => simp [execStmt, Goose.Construct.timeout, EvalM.stop]
  | @expression fuel path operand origin before outcome child =>
      have actual := child.sound
      simp only [execStmt, bind, actual, expressionStatementResult]
      cases outcome <;> rfl

theorem valueHistory_exists (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (expression : Expr) (before : ExecutionState) (supported : SupportedValue expression) :
    ValueHistory config environment fuel path expression before (evalValue fuel config environment expression before) := by
  induction fuel generalizing path expression before with
  | zero => simpa [evalValue, Goose.Construct.timeout, EvalM.stop] using (ValueHistory.timeout path expression before : ValueHistory config environment 0 path expression before _)
  | succ fuel ih =>
      cases supported with
      | integer ty value => simpa [evalValue, pure] using (ValueHistory.integer fuel path ty value before : ValueHistory config environment (fuel + 1) path (.lit ty value) before _)
      | boolean value => simpa [evalValue, pure] using (ValueHistory.boolean fuel path value before : ValueHistory config environment (fuel + 1) path (.bool value) before _)
      | @negation operand operandSupported =>
          have child := ih (path ++ [0]) operand before operandSupported
          have actual : evalValue (fuel + 1) config environment (.not operand) before =
              negationResult (evalValue fuel config environment operand before) := by
            simp only [evalValue, bind, negationResult]
            cases evalValue fuel config environment operand before <;> rfl
          rw [actual]
          exact .negation child

theorem statementHistory_exists (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (statement : Stmt) (before : ExecutionState) (supported : SupportedStatement statement) :
    StatementHistory config environment fuel path statement before (execStmt fuel config environment statement before) := by
  cases fuel with
  | zero => simpa [execStmt, Goose.Construct.timeout, EvalM.stop] using (StatementHistory.timeout path statement before : StatementHistory config environment 0 path statement before _)
  | succ fuel =>
      cases supported with
      | @expression operand origin operandSupported =>
          have child := valueHistory_exists fuel config environment (path ++ [0]) operand before operandSupported
          have actual : execStmt (fuel + 1) config environment (.expr operand origin) before =
              expressionStatementResult (evalValue fuel config environment operand before) := by
            simp only [execStmt, bind, expressionStatementResult]
            cases evalValue fuel config environment operand before <;> rfl
          rw [actual]
          exact .expression child


def sequenceResult (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (rest : List Stmt) : ExecutionStep Flow → ExecutionStep Flow
  | .ok (.normal _) state => execStmts fuel config environment rest state
  | .ok flow state => .ok flow state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

inductive StatementSequenceHistory (config : EvalConfig) (environment : RuntimeActivation) :
    Nat → List Nat → List Stmt → ExecutionState → ExecutionStep Flow → Prop
  | timeout (path : List Nat) (statements : List Stmt) (before : ExecutionState) :
      StatementSequenceHistory config environment 0 path statements before (.stop .timeout before)
  | done (fuel : Nat) (path : List Nat) (before : ExecutionState) :
      StatementSequenceHistory config environment (fuel + 1) path [] before (.ok (.normal .unit) before)
  | next {fuel : Nat} {path : List Nat} {statement : Stmt} {rest : List Stmt}
      {before : ExecutionState} {outcome : ExecutionStep Flow}
      (head : StatementHistory config environment fuel (path ++ [0]) statement before outcome)
      (tail : ∀ value middle, outcome = .ok (.normal value) middle →
        StatementSequenceHistory config environment fuel (path ++ [1]) rest middle
          (execStmts fuel config environment rest middle)) :
      StatementSequenceHistory config environment (fuel + 1) path (statement :: rest) before
        (sequenceResult fuel config environment rest outcome)

theorem StatementSequenceHistory.sound
    (history : StatementSequenceHistory config environment fuel path statements before outcome) :
    execStmts fuel config environment statements before = outcome := by
  cases history with
  | timeout => simp [execStmts, Goose.Construct.timeout, EvalM.stop]
  | done => simp [execStmts, pure]
  | @next fuel path statement rest before outcome head tail =>
      have actual := head.sound
      simp only [execStmts, bind, actual, sequenceResult]
      cases outcome with
      | ok flow state => cases flow <;> rfl
      | stop | escape | jump => rfl

theorem statementSequenceHistory_exists (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (statements : List Stmt) (before : ExecutionState)
    (supported : ∀ statement ∈ statements, SupportedStatement statement) :
    StatementSequenceHistory config environment fuel path statements before
      (execStmts fuel config environment statements before) := by
  induction fuel generalizing path statements before with
  | zero => simpa [execStmts, Goose.Construct.timeout, EvalM.stop] using
      (StatementSequenceHistory.timeout path statements before : StatementSequenceHistory config environment 0 path statements before _)
  | succ fuel ih =>
      cases statements with
      | nil => simpa [execStmts, pure] using
          (StatementSequenceHistory.done fuel path before : StatementSequenceHistory config environment (fuel + 1) path [] before _)
      | cons statement rest =>
          have head := statementHistory_exists fuel config environment (path ++ [0]) statement before
            (supported statement (by simp))
          have tail : ∀ value middle, execStmt fuel config environment statement before = .ok (.normal value) middle →
              StatementSequenceHistory config environment fuel (path ++ [1]) rest middle
                (execStmts fuel config environment rest middle) := by
            intro value middle _
            apply ih
            intro next member
            exact supported next (by simp [member])
          have actual : execStmts (fuel + 1) config environment (statement :: rest) before =
              sequenceResult fuel config environment rest (execStmt fuel config environment statement before) := by
            simp only [execStmts, bind, sequenceResult]
            cases execStmt fuel config environment statement before with
            | ok flow state => cases flow <;> rfl
            | stop | escape | jump => rfl
          rw [actual]
          exact .next head tail

private def witnessConfig : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def witnessStatements : List Stmt :=
  [.expr (.not (.bool false)) 0, .expr (.not (.lit .i64 7)) 0, .expr (.bool true) 0]

theorem witness_terminalSequence :
    StatementSequenceHistory witnessConfig witnessEnvironment 20 [] witnessStatements .initial
      (.stop (.fault .shape) .initial) := by
  have supported : ∀ statement ∈ witnessStatements, SupportedStatement statement := by
    intro statement member
    simp only [witnessStatements, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact .expression 0 (.negation (.boolean false))
    · exact .expression 0 (.negation (.integer .i64 7))
    · exact .expression 0 (.boolean true)
  have history := statementSequenceHistory_exists 20 witnessConfig witnessEnvironment [] witnessStatements .initial supported
  have actual : execStmts 20 witnessConfig witnessEnvironment witnessStatements .initial =
      .stop (.fault .shape) .initial := by
    unfold witnessConfig witnessEnvironment witnessStatements
    cbv
  rw [actual] at history
  exact history

#print axioms witness_terminalSequence

#print axioms StatementSequenceHistory.sound
#print axioms statementSequenceHistory_exists

#print axioms ValueHistory.sound
#print axioms StatementHistory.sound
#print axioms valueHistory_exists
#print axioms statementHistory_exists
end Goose.Proofs.ConstructionGhostSourceTransition
