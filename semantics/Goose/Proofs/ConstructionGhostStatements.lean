import Goose.Construct.Eval

namespace Goose.Proofs.ConstructionGhostStatements
open Goose.Construct

structure StatementInvocation where
  activation : Goose.Core.ActId
  ordinal : Nat
  fuel : Nat
  statement : Stmt
  before : ExecutionState
  outcome : ExecutionStep Flow

inductive StatementReplay (config : EvalConfig) (environment : RuntimeActivation) :
    Nat → Nat → List Stmt → ExecutionState → ExecutionStep Flow → List StatementInvocation → Prop
  | timeout (offset : Nat) (statements : List Stmt) (state : ExecutionState) :
      StatementReplay config environment 0 offset statements state (.stop .timeout state) []
  | done (fuel offset : Nat) (state : ExecutionState) :
      StatementReplay config environment (fuel + 1) offset [] state (.ok (.normal .unit) state) []
  | next {fuel offset : Nat} {statement : Stmt} {rest : List Stmt}
      {before middle : ExecutionState} {value : Value} {outcome : ExecutionStep Flow}
      {visits : List StatementInvocation}
      (head : execStmt fuel config environment statement before = .ok (.normal value) middle)
      (tail : StatementReplay config environment fuel (offset + 1) rest middle outcome visits) :
      StatementReplay config environment (fuel + 1) offset (statement :: rest) before outcome
        (⟨environment.act, offset, fuel, statement, before, .ok (.normal value) middle⟩ :: visits)
  | breaking {fuel offset : Nat} {statement : Stmt} {rest : List Stmt}
      {before after : ExecutionState} {value : Option Value}
      (head : execStmt fuel config environment statement before = .ok (.breaking value) after) :
      StatementReplay config environment (fuel + 1) offset (statement :: rest) before
        (.ok (.breaking value) after)
        [⟨environment.act, offset, fuel, statement, before, .ok (.breaking value) after⟩]
  | continuing {fuel offset : Nat} {statement : Stmt} {rest : List Stmt}
      {before after : ExecutionState}
      (head : execStmt fuel config environment statement before = .ok .continuing after) :
      StatementReplay config environment (fuel + 1) offset (statement :: rest) before
        (.ok .continuing after)
        [⟨environment.act, offset, fuel, statement, before, .ok .continuing after⟩]
  | stopped {fuel offset : Nat} {statement : Stmt} {rest : List Stmt}
      {before after : ExecutionState} {reason : Goose.Core.Stop}
      (head : execStmt fuel config environment statement before = .stop reason after) :
      StatementReplay config environment (fuel + 1) offset (statement :: rest) before
        (.stop reason after) [⟨environment.act, offset, fuel, statement, before, .stop reason after⟩]
  | escaped {fuel offset : Nat} {statement : Stmt} {rest : List Stmt}
      {before after : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
      (head : execStmt fuel config environment statement before = .escape address carriers after) :
      StatementReplay config environment (fuel + 1) offset (statement :: rest) before
        (.escape address carriers after)
        [⟨environment.act, offset, fuel, statement, before, .escape address carriers after⟩]
  | jumped {fuel offset : Nat} {statement : Stmt} {rest : List Stmt}
      {before after : ExecutionState} {target : Nat} {kind : JumpKind}
      (head : execStmt fuel config environment statement before = .jump target kind after) :
      StatementReplay config environment (fuel + 1) offset (statement :: rest) before
        (.jump target kind after)
        [⟨environment.act, offset, fuel, statement, before, .jump target kind after⟩]

theorem statementReplay_exists (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (offset : Nat) (statements : List Stmt) (before : ExecutionState) :
    ∃ visits, StatementReplay config environment fuel offset statements before
      (execStmts fuel config environment statements before) visits := by
  induction fuel generalizing offset statements before with
  | zero => simpa [execStmts, Goose.Construct.timeout, EvalM.stop] using
      (show ∃ visits, StatementReplay config environment 0 offset statements before (.stop .timeout before) visits from
        ⟨[], .timeout offset statements before⟩)
  | succ fuel ih =>
    cases statements with
    | nil => simpa [execStmts, pure] using
        (show ∃ visits, StatementReplay config environment (fuel + 1) offset [] before (.ok (.normal .unit) before) visits from
          ⟨[], .done fuel offset before⟩)
    | cons statement rest =>
      cases head : execStmt fuel config environment statement before with
      | ok flow middle =>
        cases flow with
        | normal value =>
          obtain ⟨visits, tail⟩ := ih (offset + 1) rest middle
          simp only [execStmts, bind, head]
          exact ⟨_, .next head tail⟩
        | breaking value =>
          simp only [execStmts, bind, head, pure]
          exact ⟨_, .breaking head⟩
        | continuing =>
          simp only [execStmts, bind, head, pure]
          exact ⟨_, .continuing head⟩
      | stop reason after =>
        simp only [execStmts, bind, head]
        exact ⟨_, .stopped head⟩
      | escape address carriers after =>
        simp only [execStmts, bind, head]
        exact ⟨_, .escaped head⟩
      | jump target kind after =>
        simp only [execStmts, bind, head]
        exact ⟨_, .jumped head⟩

theorem StatementReplay.sound
    (replay : StatementReplay config environment fuel offset statements before outcome visits) :
    execStmts fuel config environment statements before = outcome := by
  induction replay with
  | timeout => simp [execStmts, Goose.Construct.timeout, EvalM.stop]
  | done => simp [execStmts, pure]
  | next head tail ih => simp only [execStmts, bind, head]; exact ih
  | breaking head | continuing head => simp only [execStmts, bind, head, pure]
  | stopped head | escaped head | jumped head => simp only [execStmts, bind, head]

theorem StatementReplay.sourceOrder
    (replay : StatementReplay config environment fuel offset statements before outcome visits) :
    visits.map StatementInvocation.statement = statements.take visits.length := by
  induction replay <;> simp_all

theorem StatementReplay.activation
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (visit : StatementInvocation) (member : visit ∈ visits) : visit.activation = environment.act := by
  induction replay with
  | timeout | done => simp at member
  | next head tail ih =>
    simp only [List.mem_cons] at member
    rcases member with same | later
    · subst visit; rfl
    · exact ih later
  | breaking | continuing | stopped | escaped | jumped =>
    simp only [List.mem_singleton] at member
    subst visit
    rfl

theorem StatementReplay.ordinals
    (replay : StatementReplay config environment fuel offset statements before outcome visits) :
    visits.map StatementInvocation.ordinal = List.range' offset visits.length := by
  induction replay with
  | timeout | done => rfl
  | next head tail ih => simpa [List.range'_succ] using congrArg (offset :: ·) ih
  | breaking | continuing | stopped | escaped | jumped => simp [List.range'_succ]

theorem StatementReplay.once
    (replay : StatementReplay config environment fuel offset statements before outcome visits) :
    (visits.map StatementInvocation.ordinal).Nodup := by
  rw [replay.ordinals]
  exact List.nodup_range'

private def witnessConfig : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 4, #[], [], []⟩
private def witnessStatements : List Stmt :=
  [.print [.text "before"] 0, .abort "stop" 0, .print [.text "after"] 0]
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem statementWitness_sideEffect :
    ∃ state, execStmts 20 witnessConfig witnessEnvironment witnessStatements .initial =
      .stop (.abort .userAbort 0) state ∧
      state.construction.stdout.data.toList = [98, 101, 102, 111, 114, 101, 10] := by
  refine ⟨stepState (execStmts 20 witnessConfig witnessEnvironment witnessStatements .initial), ?_, ?_⟩ <;>
    unfold witnessConfig witnessEnvironment witnessStatements stepState <;> cbv

#print axioms statementWitness_sideEffect
#print axioms StatementReplay.once
#print axioms statementReplay_exists
#print axioms StatementReplay.sound
#print axioms StatementReplay.sourceOrder
#print axioms StatementReplay.activation
end Goose.Proofs.ConstructionGhostStatements
