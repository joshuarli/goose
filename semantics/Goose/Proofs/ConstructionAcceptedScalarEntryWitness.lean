import Goose.Proofs.ConstructionAcceptedScalarPosition
import Goose.Proofs.ConstructionAcceptedEntryScope

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private theorem scalar_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem typeExpr_not_singleton (fuel : Nat) (environment : TypingEnv) (expression : Expr)
    (before after : Nat) (types : List Ty)
    (typed : typeExpr fuel environment (.not expression) before = .ok (types, after)) : types = [.bool] := by
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at typed; cases typed
  | succ fuel =>
    simp only [typeExpr, bind, StateT.bind] at typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    cases typed
    rfl

theorem typeExpr_booleanBinary_singleton (fuel : Nat) (environment : TypingEnv) (left right : Expr) (conjunction : Bool)
    (before after : Nat) (types : List Ty)
    (typed : typeExpr fuel environment (if conjunction then .and left right else .or left right) before = .ok (types, after)) :
    types = [.bool] := by
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at typed; cases typed
  | succ fuel =>
    cases conjunction <;> simp only [Bool.false_eq_true, ↓reduceIte, typeExpr, bind, StateT.bind] at typed
    all_goals
      obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
      obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
      obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
      obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
      obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
      obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
      cases typed
      rfl

theorem typeExpr_comparison_singleton (fuel : Nat) (environment : TypingEnv) (left right : Expr)
    (operation : Goose.Core.CmpOp) (before after : Nat) (types : List Ty)
    (typed : typeExpr fuel environment (.cmp operation left right) before = .ok (types, after)) : types = [.bool] := by
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at typed; cases typed
  | succ fuel =>
    simp only [typeExpr, bind, StateT.bind] at typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨leftValue, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨rightValue, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨leftTy, leftCounter⟩ := leftValue
    obtain ⟨rightTy, rightCounter⟩ := rightValue
    cases leftTy <;> cases rightTy <;> try (change Except.error _ = Except.ok _ at typed; cases typed)
    case int.int first second =>
      change (Except.bind _ _) = _ at typed
      obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
      cases typed
      rfl
    case bool.bool =>
      cases operation <;> first
        | change Except.error _ = Except.ok _ at typed; cases typed
        | change Except.ok _ = Except.ok _ at typed; cases typed; rfl

theorem typeExpr_unary_singleton (fuel : Nat) (environment : TypingEnv) (expression : Expr)
    (operation : Goose.Core.UnOp) (origin : Goose.Core.OriginId) (before after : Nat) (types : List Ty)
    (typed : typeExpr fuel environment (.un operation expression origin) before = .ok (types, after)) : ∃ ty, types = [ty] := by
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at typed; cases typed
  | succ fuel =>
    simp only [typeExpr, bind, StateT.bind] at typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨operand, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨operandTy, counter⟩ := operand
    cases operation <;> cases operandTy <;> first
      | change Except.error _ = Except.ok _ at typed; cases typed
      | change Except.ok _ = Except.ok _ at typed; cases typed; exact ⟨_, rfl⟩
      | change (Except.bind _ _) = _ at typed
        obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
        cases typed
        exact ⟨_, rfl⟩

theorem typeExpr_binary_singleton (fuel : Nat) (environment : TypingEnv) (left right : Expr)
    (operation : Goose.Core.BinOp) (origin : Goose.Core.OriginId) (before after : Nat) (types : List Ty)
    (typed : typeExpr fuel environment (.bin operation left right origin) before = .ok (types, after)) : ∃ ty, types = [ty] := by
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at typed; cases typed
  | succ fuel =>
    simp only [typeExpr, bind, StateT.bind] at typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    cases typed
    exact ⟨_, rfl⟩

theorem typeExpr_conversion_singleton (fuel : Nat) (environment : TypingEnv) (expression : Expr)
    (kind : Goose.Core.ConvKind) (target : Ty) (origin : Goose.Core.OriginId) (before after : Nat) (types : List Ty)
    (typed : typeExpr fuel environment (.conv kind target expression origin) before = .ok (types, after)) : types = [target] := by
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at typed; cases typed
  | succ fuel =>
    simp only [typeExpr, bind, StateT.bind] at typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨operand, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨operandTy, counter⟩ := operand
    cases kind with
    | as | asUnchecked => change Except.ok _ = Except.ok _ at typed; cases typed; rfl
    | widen =>
      cases operandTy <;> cases target <;> first
        | change Except.error _ = Except.ok _ at typed; cases typed
        | change (Except.bind _ _) = _ at typed
          obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
          cases typed
          rfl

theorem typeExpr_read_singleton (fuel : Nat) (environment : TypingEnv) (place : Place)
    (before after : Nat) (types : List Ty)
    (typed : typeExpr fuel environment (.read place) before = .ok (types, after)) : ∃ ty, types = [ty] := by
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at typed; cases typed
  | succ fuel =>
    simp only [typeExpr, bind, StateT.bind] at typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    obtain ⟨_, _, typed⟩ := scalar_bind_success _ _ _ typed
    cases typed
    exact ⟨_, rfl⟩

theorem typeExpr_scalar_singleton {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (environment : TypingEnv) (before after : Nat) (types : List Ty)
    (typed : typeExpr fuel environment expression before = .ok (types, after)) : ∃ ty, types = [ty] := by
  cases form with
  | numeric form =>
    cases form with
    | scalar form =>
      cases form with
      | scalar form =>
        cases form with
        | integer type value =>
          cases fuel with
          | zero => change Except.error _ = Except.ok _ at typed; cases typed
          | succ fuel => change Except.ok _ = Except.ok _ at typed; cases typed; exact ⟨_, rfl⟩
        | boolean value =>
          cases fuel with
          | zero => change Except.error _ = Except.ok _ at typed; cases typed
          | succ fuel => change Except.ok _ = Except.ok _ at typed; cases typed; exact ⟨_, rfl⟩
        | globalRead id => exact typeExpr_read_singleton fuel environment (.global id) before after types typed
        | localRead id => exact typeExpr_read_singleton fuel environment (.var id) before after types typed
      | not form => exact ⟨.bool, typeExpr_not_singleton fuel environment _ before after types typed⟩
    | unary operation origin form => exact typeExpr_unary_singleton fuel environment _ operation origin before after types typed
    | conversion kind target origin form => exact ⟨target, typeExpr_conversion_singleton fuel environment _ kind target origin before after types typed⟩
  | binary operation origin left right => exact typeExpr_binary_singleton fuel environment _ _ operation origin before after types typed
  | comparison operation left right => exact ⟨.bool, typeExpr_comparison_singleton fuel environment _ _ operation before after types typed⟩
  | conjunction left right => exact ⟨.bool, typeExpr_booleanBinary_singleton fuel environment _ _ true before after types typed⟩
  | disjunction left right => exact ⟨.bool, typeExpr_booleanBinary_singleton fuel environment _ _ false before after types typed⟩
  | not form => exact ⟨.bool, typeExpr_not_singleton fuel environment _ before after types typed⟩
  | unary operation origin form => exact typeExpr_unary_singleton fuel environment _ operation origin before after types typed
  | conversion kind target origin form => exact ⟨target, typeExpr_conversion_singleton fuel environment _ kind target origin before after types typed⟩

inductive ScalarExpressionStatements : List Stmt → Prop
  | nil : ScalarExpressionStatements []
  | cons (expression : Expr) (origin : Goose.Core.OriginId) (rest : List Stmt)
      (form : AcceptedBinaryExpression expression) (tail : ScalarExpressionStatements rest) :
      ScalarExpressionStatements (.expr expression origin :: rest)

theorem SourcePosition.checkedScalarStatements {config : EvalConfig} (accepted : AcceptedModule config)
    {statements : List Stmt} (form : ScalarExpressionStatements statements) :
    ∀ (frame : ConstructionSourceFrame), SourcePosition accepted frame (.statements statements) →
      (∀ rootsAfter, rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter) →
        GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff) →
      CheckedScalarStatements frame statements := by
  induction form with
  | nil => intro frame position available; exact .nil frame
  | cons expression origin rest form tail ih =>
    intro frame position available
    obtain ⟨finalTyping, finalCounter, finalRoots, typedAll, rootedAll⟩ := position.checked accepted frame _
    obtain ⟨rootMiddle, headRooted, tailRooted⟩ := rpStmts_cons rootedAll
    obtain ⟨roots, expressionRooted⟩ := rpStmt_expression headRooted
    have headAvailable : GlobalEffectsAvailable frame.interpretation frame.initialized rootMiddle.eff := by
      have included := rpStmts_effectTargetsIncluded tailRooted
      intro target member global instantiates
      exact available finalRoots rootedAll target (included member) global instantiates
    cases nesting : frame.typingFuel with
    | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
    | succ headFuel =>
      cases headFuel with
      | zero =>
        rw [nesting] at typedAll
        change Except.error _ = Except.ok _ at typedAll
        cases typedAll
      | succ checkFuel =>
        have headPosition := position.statements_head accepted frame (.expr expression origin) rest (checkFuel + 1) nesting
        obtain ⟨next, statementAfter, headRoots, headTyped, headRooted'⟩ := headPosition.checked accepted _ _
        have sameHead : headRoots = rootMiddle := (Prod.mk.inj (Except.ok.inj (headRooted'.symm.trans headRooted))).2
        subst headRoots
        have expressionTyped : ∃ ty typingAfter,
            typeExpr checkFuel (ordinaryOperandFrame frame checkFuel).typing expression frame.typingCounter = .ok ([ty], typingAfter) := by
          simp only [typeStatement, bind, StateT.bind] at headTyped
          change (Except.bind (typeExpr checkFuel (ordinaryOperandFrame frame checkFuel).typing expression frame.typingCounter) _) = _ at headTyped
          obtain ⟨result, operand, remaining⟩ := scalar_bind_success _ _ _ headTyped
          obtain ⟨resultTypes, typingAfter⟩ := result
          obtain ⟨ty, sameTypes⟩ := typeExpr_scalar_singleton form checkFuel (ordinaryOperandFrame frame checkFuel).typing
            frame.typingCounter typingAfter resultTypes operand
          subst resultTypes
          exact ⟨ty, typingAfter, operand⟩
        obtain ⟨ty, typingAfter, expressionTyped⟩ := expressionTyped
        have checked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression ty roots typingAfter rootMiddle :=
          ⟨expressionTyped, expressionRooted, headAvailable⟩
        let nextFrame := { frame with typingFuel := checkFuel + 1, typing := next, typingCounter := statementAfter, rootCursor := rootMiddle }
        have nextPosition := position.statements_tail accepted frame (.expr expression origin) rest (checkFuel + 1) next statementAfter
          rootMiddle nesting headTyped headRooted
        have tailAvailable : ∀ final, rpStmts nextFrame.source rest nextFrame.rootCursor = .ok ((), final) →
            GlobalEffectsAvailable nextFrame.interpretation nextFrame.initialized final.eff := by
          intro final rooted
          have same : final = finalRoots := (Prod.mk.inj (Except.ok.inj (rooted.symm.trans tailRooted))).2
          subst final
          exact available finalRoots rootedAll
        have remaining := ih nextFrame nextPosition tailAvailable
        exact .cons frame expression origin rest checkFuel ty roots typingAfter rootMiddle next statementAfter rootMiddle nesting
          form checked headTyped headRooted remaining

theorem SourcePosition.scalarStatements_complete {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (statements : List Stmt) (form : ScalarExpressionStatements statements)
    (position : SourcePosition accepted frame (.statements statements))
    (available : ∀ rootsAfter, rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter) →
      GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff)
    (fuel : Nat) (state : ExecutionState) (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) :
    let outcome := execStmts fuel config frame.interpretation.environment statements state
    Goose.Proofs.Exit.stepState outcome = state ∧
      (∀ flow after, outcome = .ok flow after → ∃ finalFrame,
        flow = .normal .unit ∧ after = state ∧ finalFrame.interpretation = frame.interpretation ∧
        finalFrame.initialized = frame.initialized ∧ AcceptedFrame config accepted finalFrame state types ∧
        SourcePosition accepted finalFrame (.statements [])) ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types :=
  execStmts_checkedScalar_complete (position.checkedScalarStatements accepted form frame available) fuel config accepted state
    ambient types live regions pending world source position

theorem acceptedEntry_scalarStatements_complete (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation config.module.entry)
    (parametersEmpty : frame.source.impl.params = #[]) (scopes : frame.interpretation.environment.scopes = [])
    (initialized : frame.initialized = config.module.globals.size) (cursor : frame.rootCursor = ⟨0, {}, []⟩)
    (form : ScalarExpressionStatements frame.source.impl.body.stmts)
    (available : ∀ rootsAfter,
      let next := entryStatementsFrame config frame state.nextScope
      rpStmts next.source frame.source.impl.body.stmts next.rootCursor = .ok ((), rootsAfter) →
        GlobalEffectsAvailable next.interpretation next.initialized rootsAfter.eff) (fuel : Nat) :
    let next := entryStatementsFrame config frame state.nextScope
    let after := { state with nextScope := state.nextScope + 1 }
    freshScope state = .ok state.nextScope after ∧
      Goose.Proofs.Exit.stepState (execStmts fuel config next.interpretation.environment frame.source.impl.body.stmts after) = after ∧
      AcceptedWorld config next.initialized
        (Goose.Proofs.Exit.stepState (execStmts fuel config next.interpretation.environment frame.source.impl.body.stmts after))
        ambient types live regions pending ∧
      AcceptedFrame config accepted next
        (Goose.Proofs.Exit.stepState (execStmts fuel config next.interpretation.environment frame.source.impl.body.stmts after)) types := by
  obtain ⟨fresh, nextWorld, nextSource, position⟩ := acceptedEntryStatementsFrame config accepted frame state ambient types live regions pending
    world source phase parametersEmpty scopes initialized cursor
  have result := position.scalarStatements_complete accepted _ frame.source.impl.body.stmts form available fuel _ ambient types live regions pending
    nextWorld nextSource
  exact ⟨fresh, result.1, result.2.2.1, result.2.2.2⟩

#print axioms SourcePosition.scalarStatements_complete
#print axioms acceptedEntry_scalarStatements_complete
#print axioms SourcePosition.checkedScalarStatements
#print axioms typeExpr_scalar_singleton
#print axioms typeExpr_read_singleton
#print axioms typeExpr_unary_singleton
#print axioms typeExpr_binary_singleton
#print axioms typeExpr_conversion_singleton
#print axioms typeExpr_comparison_singleton
#print axioms typeExpr_booleanBinary_singleton
#print axioms typeExpr_not_singleton
end Goose.Proofs.ConstructionAcceptedExecution
