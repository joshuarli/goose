import Goose.Proofs.ConstructionInvocationReplay
import Goose.Proofs.ConstructionExecutionSourceOrder

namespace Goose.Proofs.ConstructionGhostInvocation
open Goose.Construct Goose.Proofs.ConstructionInvocationReplay

theorem visit_executes {action : α → EvalM β} {offset : Nat} {operands : List α}
    {accumulator : List β} {before : ExecutionState} {outcome : ExecutionStep (List β)}
    {visits : List (Invocation α β)}
    (replay : OperandReplay action offset operands accumulator before outcome visits)
    (visit : Invocation α β) (member : visit ∈ visits) :
    action visit.operand visit.before = visit.outcome := by
  induction replay with
  | done => simp at member
  | next head tail ih =>
    simp only [List.mem_cons] at member
    rcases member with same | later
    · subst visit; exact head
    · exact ih later
  | stopped head | escaped head | jumped head =>
    simp only [List.mem_singleton] at member
    subst visit
    exact head

def trackedInitializer : Expr → Bool
  | .arrLit ty _ _ => !ty.nonfixed
  | .fill (.arr element count) _ _ => !(Ty.arr element count).nonfixed
  | .structLit (.structT _ _) _ => true
  | _ => false

theorem structLiteral_replay (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id : Goose.Core.StructId) (fields : TyList) (operands : List Expr) (before : ExecutionState) :
    ∃ mapped visits,
      OperandReplay (evalValue fuel config environment) 0 operands [] before mapped visits ∧
      evalValue (fuel + 1) config environment (.structLit (.structT id fields) operands) before =
        match mapped with
        | .ok values after => .ok (.record id values.toArray) after
        | .stop reason after => .stop reason after
        | .escape address carriers after => .escape address carriers after
        | .jump target kind after => .jump target kind after := by
  obtain ⟨visits, replay⟩ := mapM_replay (evalValue fuel config environment) operands before
  refine ⟨_, visits, replay, ?_⟩
  simp only [evalValue, bind, pure]
  cases (operands.mapM (evalValue fuel config environment)) before <;> rfl

inductive EvaluationTree (config : EvalConfig) (environment : RuntimeActivation) :
    Nat → List Nat → Expr → ExecutionState → ExecutionStep Value → Prop
  | timeout (path : List Nat) (expression : Expr) (before : ExecutionState) :
      EvaluationTree config environment 0 path expression before
        (evalValue 0 config environment expression before)
  | opaque (fuel : Nat) (path : List Nat) (expression : Expr) (before : ExecutionState)
      (untracked : trackedInitializer expression = false) :
      EvaluationTree config environment (fuel + 1) path expression before
        (evalValue (fuel + 1) config environment expression before)
  | array (fuel : Nat) (path : List Nat) (ty : Ty) (operands : List Expr)
      (origin : Goose.Core.OriginId) (before : ExecutionState)
      (mapped : ExecutionStep (List Value)) (visits : List (Invocation Expr Value))
      (fixed : ty.nonfixed = false)
      (replay : OperandReplay (evalValue fuel config environment) 0 operands [] before mapped visits)
      (children : ∀ visit ∈ visits, EvaluationTree config environment fuel (visit.path path)
        visit.operand visit.before visit.outcome) :
      EvaluationTree config environment (fuel + 1) path (.arrLit ty operands origin) before
        (match mapped with
        | .ok values after => .ok (.fixed values.toArray) after
        | .stop reason after => .stop reason after
        | .escape address carriers after => .escape address carriers after
        | .jump target kind after => .jump target kind after)
  | record (fuel : Nat) (path : List Nat) (id : Goose.Core.StructId) (fields : TyList)
      (operands : List Expr) (before : ExecutionState)
      (mapped : ExecutionStep (List Value)) (visits : List (Invocation Expr Value))
      (replay : OperandReplay (evalValue fuel config environment) 0 operands [] before mapped visits)
      (children : ∀ visit ∈ visits, EvaluationTree config environment fuel (visit.path path)
        visit.operand visit.before visit.outcome) :
      EvaluationTree config environment (fuel + 1) path (.structLit (.structT id fields) operands) before
        (match mapped with
        | .ok values after => .ok (.record id values.toArray) after
        | .stop reason after => .stop reason after
        | .escape address carriers after => .escape address carriers after
        | .jump target kind after => .jump target kind after)
  | fill (fuel : Nat) (path : List Nat) (element : Ty) (count : Nat) (operand : Expr)
      (origin : Goose.Core.OriginId) (before : ExecutionState)
      (fixed : (Ty.arr element count).nonfixed = false)
      (child : EvaluationTree config environment fuel (path ++ [0]) operand before
        (evalValue fuel config environment operand before)) :
      EvaluationTree config environment (fuel + 1) path (.fill (.arr element count) operand origin) before
        (match evalValue fuel config environment operand before with
        | .ok value after => .ok (.fixed (Array.replicate count value)) after
        | .stop reason after => .stop reason after
        | .escape address carriers after => .escape address carriers after
        | .jump target kind after => .jump target kind after)

theorem evaluationTree_exists (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (expression : Expr) (before : ExecutionState) :
    EvaluationTree config environment fuel path expression before
      (evalValue fuel config environment expression before) := by
  induction fuel generalizing path expression before with
  | zero => exact .timeout path expression before
  | succ fuel ih =>
    cases expression with
    | arrLit ty operands origin =>
      cases fixed : ty.nonfixed with
      | false =>
        obtain ⟨mapped, visits, replay, execution⟩ := fixedArray_replay fuel config environment ty operands origin before fixed
        rw [execution]
        cases mapped <;> exact .array fuel path ty operands origin before _ visits fixed replay (fun visit member => by
          rw [← visit_executes replay visit member]
          exact ih _ _ _)
      | true => exact .opaque fuel path _ before (by simp [trackedInitializer, fixed])
    | structLit ty operands =>
      cases ty with
      | structT id fields =>
        obtain ⟨mapped, visits, replay, execution⟩ := structLiteral_replay fuel config environment id fields operands before
        rw [execution]
        cases mapped <;> exact .record fuel path id fields operands before _ visits replay (fun visit member => by
          rw [← visit_executes replay visit member]
          exact ih _ _ _)
      | _ => exact .opaque fuel path _ before (by rfl)
    | fill ty operand origin =>
      cases ty with
      | arr element count =>
        cases fixed : (Ty.arr element count).nonfixed with
        | false =>
          rw [Goose.Proofs.ConstructionExecution.evalValue_fixedFill_result fuel config environment element count operand origin before fixed]
          exact .fill fuel path element count operand origin before fixed (ih _ _ _)
        | true => exact .opaque fuel path _ before (by simp [trackedInitializer, fixed])
      | _ => exact .opaque fuel path _ before (by rfl)
    | _ => exact .opaque fuel path _ before (by rfl)

theorem evaluationTree_sound {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {path : List Nat} {expression : Expr} {before : ExecutionState} {outcome : ExecutionStep Value}
    (tree : EvaluationTree config environment fuel path expression before outcome) :
    evalValue fuel config environment expression before = outcome := by
  cases tree with
  | timeout | «opaque» => rfl
  | array fuel path ty operands origin before mapped visits fixed replay children =>
    simp only [evalValue]
    have notTrue : ¬ ty.nonfixed = true := by simp [fixed]
    rw [ite_eq_right notTrue]
    simp only [bind, pure]
    have actual := replay.execute
    change (operands.mapM (evalValue fuel config environment)) before = mapped at actual
    rw [actual]
    cases mapped <;> rfl
  | record fuel path id fields operands before mapped visits replay children =>
    simp only [evalValue, bind, pure]
    have actual := replay.execute
    change (operands.mapM (evalValue fuel config environment)) before = mapped at actual
    rw [actual]
    cases mapped <;> rfl
  | fill fuel path element count operand origin before fixed child =>
    exact Goose.Proofs.ConstructionExecution.evalValue_fixedFill_result fuel config environment element count operand origin before fixed

#print axioms evaluationTree_sound
#print axioms evaluationTree_exists

private def witnessConfig : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnv : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def witnessSource : Expr :=
  .blockE (.mk 0 [.print [.text "once"] 0] (some (.lit .i64 7))) 0

private def finalState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem source_sideEffect :
    (finalState (evalValue 30 witnessConfig witnessEnv witnessSource .initial)).construction.stdout.data.toList =
      [111, 110, 99, 101, 10] := by
  unfold finalState witnessConfig witnessEnv witnessSource
  cbv

theorem fill_source_sideEffect :
    ∃ state, evalValue 31 witnessConfig witnessEnv
      (.fill (.arr (.int .i64) 2) witnessSource 0) .initial =
        .ok (.fixed #[.int .i64 7, .int .i64 7]) state ∧
      state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  refine ⟨finalState (evalValue 31 witnessConfig witnessEnv
    (.fill (.arr (.int .i64) 2) witnessSource 0) .initial), ?_, ?_⟩ <;>
    unfold finalState witnessConfig witnessEnv witnessSource <;> cbv

theorem record_source_sideEffect :
    ∃ state, evalValue 31 witnessConfig witnessEnv
      (.structLit (.structT 0 (.cons (.int .i64) (.cons (.int .i64) .nil))) [witnessSource, .lit .i64 8]) .initial =
        .ok (.record 0 #[.int .i64 7, .int .i64 8]) state ∧
      state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  refine ⟨finalState (evalValue 31 witnessConfig witnessEnv
    (.structLit (.structT 0 (.cons (.int .i64) (.cons (.int .i64) .nil))) [witnessSource, .lit .i64 8]) .initial), ?_, ?_⟩ <;>
    unfold finalState witnessConfig witnessEnv witnessSource <;> cbv

#print axioms record_source_sideEffect
#print axioms fill_source_sideEffect
#print axioms source_sideEffect
end Goose.Proofs.ConstructionGhostInvocation
