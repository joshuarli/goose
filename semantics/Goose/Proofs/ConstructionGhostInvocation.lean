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

def comparisonContinuation (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (operation : Goose.Core.CmpOp) (second : Expr) (first : ExecutionStep Value) : ExecutionStep Value :=
  match first with
  | .ok value state => (do
      let second ← evalValue fuel config environment second
      let (first, second) ← comparable value second
      pure (Value.bool (Goose.Core.evalCmp operation first second))) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

def notContinuation (source : ExecutionStep Value) : ExecutionStep Value :=
  match source with
  | .ok value state => (do pure (Value.bool (!(← expectBool value)))) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

def shortCircuitContinuation (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (isAnd : Bool) (second : Expr) (first : ExecutionStep Value) : ExecutionStep Value :=
  match first with
  | .ok value state => (do
      let selected ← expectBool value
      if selected == isAnd then
        pure (Value.bool (← expectBool (← evalValue fuel config environment second)))
      else pure (Value.bool selected)) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

def shortCircuitExpr (isAnd : Bool) (first second : Expr) : Expr :=
  if isAnd then .and first second else .or first second

def binaryContinuation (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (operation : Goose.Core.BinOp) (second : Expr) (origin : Goose.Core.OriginId)
    (first : ExecutionStep Value) : ExecutionStep Value :=
  match first with
  | .ok value state => (do
      let (ty, first) ← expectInt value
      let (otherTy, second) ← expectInt (← evalValue fuel config environment second)
      sameIntType ty otherTy
      match Goose.Core.evalBin config.profile operation ty first second with
      | .ok result => pure (Value.int ty result)
      | .error reason => abortAt (Goose.Core.AbortKind.ofNum reason) origin) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

def unaryContinuation (config : EvalConfig) (operation : Goose.Core.UnOp)
    (origin : Goose.Core.OriginId) (source : ExecutionStep Value) : ExecutionStep Value :=
  match source with
  | .ok value state => (do
      let (ty, number) ← expectInt value
      match Goose.Core.evalUn config.profile operation ty number with
      | .ok result => pure (Value.int ty result)
      | .error reason => abortAt (Goose.Core.AbortKind.ofNum reason) origin) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

def conversionContinuation (config : EvalConfig) (kind : Goose.Core.ConvKind) (target : Ty)
    (origin : Goose.Core.OriginId) (source : ExecutionStep Value) : ExecutionStep Value :=
  match source with
  | .ok value state => (do
      let (sourceTy, number) ← expectInt value
      let .int targetTy := target | fault .shape
      match Goose.Core.evalConv config.profile kind sourceTy targetTy number with
      | .ok result => pure (Value.int targetTy result)
      | .error reason => abortAt (Goose.Core.AbortKind.ofNum reason) origin) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

def trackedInitializer : Expr → Bool
  | .arrLit ty _ _ => !ty.nonfixed
  | .fill (.arr element count) _ _ => !(Ty.arr element count).nonfixed
  | .structLit (.structT _ _) _ => true
  | .cmp _ _ _ | .not _ | .and _ _ | .or _ _ | .bin _ _ _ _ | .un _ _ _ | .conv _ _ _ _ => true
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
  | unary (fuel : Nat) (path : List Nat) (operation : Goose.Core.UnOp) (operand : Expr)
      (origin : Goose.Core.OriginId) (before : ExecutionState)
      (child : EvaluationTree config environment fuel (path ++ [0]) operand before
        (evalValue fuel config environment operand before)) :
      EvaluationTree config environment (fuel + 1) path (.un operation operand origin) before
        (unaryContinuation config operation origin (evalValue fuel config environment operand before))
  | conversion (fuel : Nat) (path : List Nat) (kind : Goose.Core.ConvKind) (target : Ty)
      (operand : Expr) (origin : Goose.Core.OriginId) (before : ExecutionState)
      (child : EvaluationTree config environment fuel (path ++ [0]) operand before
        (evalValue fuel config environment operand before)) :
      EvaluationTree config environment (fuel + 1) path (.conv kind target operand origin) before
        (conversionContinuation config kind target origin (evalValue fuel config environment operand before))
  | binary (fuel : Nat) (path : List Nat) (operation : Goose.Core.BinOp)
      (first second : Expr) (origin : Goose.Core.OriginId) (before : ExecutionState)
      (left : EvaluationTree config environment fuel (path ++ [0]) first before
        (evalValue fuel config environment first before))
      (right : ∀ value middle ty number ready,
        evalValue fuel config environment first before = .ok value middle →
        expectInt value middle = .ok (ty, number) ready →
        EvaluationTree config environment fuel (path ++ [1]) second ready
          (evalValue fuel config environment second ready)) :
      EvaluationTree config environment (fuel + 1) path (.bin operation first second origin) before
        (binaryContinuation fuel config environment operation second origin
          (evalValue fuel config environment first before))
  | shortCircuit (fuel : Nat) (path : List Nat) (isAnd : Bool)
      (first second : Expr) (before : ExecutionState)
      (left : EvaluationTree config environment fuel (path ++ [0]) first before
        (evalValue fuel config environment first before))
      (right : ∀ value middle ready, evalValue fuel config environment first before = .ok value middle →
        expectBool value middle = .ok isAnd ready →
        EvaluationTree config environment fuel (path ++ [1]) second ready
          (evalValue fuel config environment second ready)) :
      EvaluationTree config environment (fuel + 1) path (shortCircuitExpr isAnd first second) before
        (shortCircuitContinuation fuel config environment isAnd second
          (evalValue fuel config environment first before))
  | comparison (fuel : Nat) (path : List Nat) (operation : Goose.Core.CmpOp)
      (first second : Expr) (before : ExecutionState)
      (left : EvaluationTree config environment fuel (path ++ [0]) first before
        (evalValue fuel config environment first before))
      (right : ∀ value middle, evalValue fuel config environment first before = .ok value middle →
        EvaluationTree config environment fuel (path ++ [1]) second middle
          (evalValue fuel config environment second middle)) :
      EvaluationTree config environment (fuel + 1) path (.cmp operation first second) before
        (comparisonContinuation fuel config environment operation second
          (evalValue fuel config environment first before))
  | negation (fuel : Nat) (path : List Nat) (operand : Expr) (before : ExecutionState)
      (child : EvaluationTree config environment fuel (path ++ [0]) operand before
        (evalValue fuel config environment operand before)) :
      EvaluationTree config environment (fuel + 1) path (.not operand) before
        (notContinuation (evalValue fuel config environment operand before))
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
    | un operation operand origin =>
      have execution : evalValue (fuel + 1) config environment (.un operation operand origin) before =
          unaryContinuation config operation origin (evalValue fuel config environment operand before) := by
        simp only [evalValue, bind, unaryContinuation]
        cases evalValue fuel config environment operand before <;> rfl
      rw [execution]
      exact .unary fuel path operation operand origin before (ih _ _ _)
    | conv kind target operand origin =>
      have execution : evalValue (fuel + 1) config environment (.conv kind target operand origin) before =
          conversionContinuation config kind target origin (evalValue fuel config environment operand before) := by
        simp only [evalValue, bind, conversionContinuation]
        cases evalValue fuel config environment operand before <;> rfl
      rw [execution]
      exact .conversion fuel path kind target operand origin before (ih _ _ _)
    | bin operation first second origin =>
      have execution : evalValue (fuel + 1) config environment (.bin operation first second origin) before =
          binaryContinuation fuel config environment operation second origin
            (evalValue fuel config environment first before) := by
        simp only [evalValue, bind, binaryContinuation]
        cases evalValue fuel config environment first before <;> rfl
      rw [execution]
      exact .binary fuel path operation first second origin before (ih _ _ _) (fun _ _ _ _ _ _ _ => ih _ _ _)
    | and first second =>
      have execution : evalValue (fuel + 1) config environment (.and first second) before =
          shortCircuitContinuation fuel config environment true second
            (evalValue fuel config environment first before) := by
        simp only [evalValue, bind, shortCircuitContinuation]
        cases evalValue fuel config environment first before <;> simp [bind]
        all_goals split <;> simp_all
        all_goals split <;> simp_all
      rw [execution]
      exact .shortCircuit fuel path true first second before (ih _ _ _) (fun _ _ _ _ _ => ih _ _ _)
    | or first second =>
      have execution : evalValue (fuel + 1) config environment (.or first second) before =
          shortCircuitContinuation fuel config environment false second
            (evalValue fuel config environment first before) := by
        simp only [evalValue, bind, shortCircuitContinuation]
        cases evalValue fuel config environment first before <;> simp [bind]
        all_goals split <;> simp_all
        all_goals split <;> simp_all
      rw [execution]
      exact .shortCircuit fuel path false first second before (ih _ _ _) (fun _ _ _ _ _ => ih _ _ _)
    | cmp operation first second =>
      have execution : evalValue (fuel + 1) config environment (.cmp operation first second) before =
          comparisonContinuation fuel config environment operation second
            (evalValue fuel config environment first before) := by
        simp only [evalValue, bind, comparisonContinuation]
        cases evalValue fuel config environment first before <;> rfl
      rw [execution]
      exact .comparison fuel path operation first second before (ih _ _ _) (fun _ _ _ => ih _ _ _)
    | not operand =>
      have execution : evalValue (fuel + 1) config environment (.not operand) before =
          notContinuation (evalValue fuel config environment operand before) := by
        simp only [evalValue, bind, notContinuation]
        cases evalValue fuel config environment operand before <;> rfl
      rw [execution]
      exact .negation fuel path operand before (ih _ _ _)
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
  | unary fuel path operation operand origin before child =>
    simp only [evalValue, bind, unaryContinuation]
    cases evalValue fuel config environment operand before <;> rfl
  | conversion fuel path kind target operand origin before child =>
    simp only [evalValue, bind, conversionContinuation]
    cases evalValue fuel config environment operand before <;> rfl
  | binary fuel path operation first second origin before left right =>
    simp only [evalValue, bind, binaryContinuation]
    cases evalValue fuel config environment first before <;> rfl
  | shortCircuit fuel path isAnd first second before left right =>
    cases isAnd <;> simp only [shortCircuitExpr, Bool.false_eq_true, ↓reduceIte, evalValue, bind, shortCircuitContinuation]
    all_goals cases evalValue fuel config environment first before <;> simp [bind]
    all_goals split <;> simp_all
    all_goals split <;> simp_all
  | comparison fuel path operation first second before left right =>
    simp only [evalValue, bind, comparisonContinuation]
    cases evalValue fuel config environment first before <;> rfl
  | negation fuel path operand before child =>
    simp only [evalValue, bind, notContinuation]
    cases evalValue fuel config environment operand before <;> rfl
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

theorem comparison_source_sideEffect :
    ∃ state, evalValue 31 witnessConfig witnessEnv
      (.cmp .eq witnessSource (.blockE (.mk 1 [.print [.text "second"] 0]
        (some (.lit .i64 7))) 0)) .initial = .ok (.bool true) state ∧
      state.construction.stdout.data.toList =
        [111, 110, 99, 101, 10, 115, 101, 99, 111, 110, 100, 10] := by
  refine ⟨finalState (evalValue 31 witnessConfig witnessEnv
    (.cmp .eq witnessSource (.blockE (.mk 1 [.print [.text "second"] 0]
      (some (.lit .i64 7))) 0)) .initial), ?_, ?_⟩ <;>
    unfold finalState witnessConfig witnessEnv witnessSource <;> cbv

theorem shortCircuit_skips_source :
    evalValue 31 witnessConfig witnessEnv
      (.and (.bool false) (.blockE (.mk 1 [.print [.text "skipped"] 0]
        (some (.bool true))) 0)) .initial = .ok (.bool false) .initial := by
  unfold witnessConfig witnessEnv
  cbv

theorem binary_source_sideEffect :
    ∃ state, evalValue 31 witnessConfig witnessEnv
      (.bin .add witnessSource (.blockE (.mk 1 [.print [.text "second"] 0]
        (some (.lit .i64 7))) 0) 0) .initial = .ok (.int .i64 14) state ∧
      state.construction.stdout.data.toList =
        [111, 110, 99, 101, 10, 115, 101, 99, 111, 110, 100, 10] := by
  refine ⟨finalState (evalValue 31 witnessConfig witnessEnv
    (.bin .add witnessSource (.blockE (.mk 1 [.print [.text "second"] 0]
      (some (.lit .i64 7))) 0) 0) .initial), ?_, ?_⟩ <;>
    unfold finalState witnessConfig witnessEnv witnessSource <;> cbv

theorem unary_source_sideEffect :
    ∃ state, evalValue 31 witnessConfig witnessEnv (.un .neg witnessSource 0) .initial =
      .ok (.int .i64 (-7)) state ∧
      state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  refine ⟨finalState (evalValue 31 witnessConfig witnessEnv (.un .neg witnessSource 0) .initial), ?_, ?_⟩ <;>
    unfold finalState witnessConfig witnessEnv witnessSource <;> cbv

#print axioms unary_source_sideEffect
#print axioms binary_source_sideEffect
#print axioms shortCircuit_skips_source
#print axioms comparison_source_sideEffect
#print axioms record_source_sideEffect
#print axioms fill_source_sideEffect
#print axioms source_sideEffect
end Goose.Proofs.ConstructionGhostInvocation
