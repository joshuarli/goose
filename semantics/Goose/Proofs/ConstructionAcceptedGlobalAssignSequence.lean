import Goose.Proofs.ConstructionAcceptedGlobalAssignChecker
import Goose.Proofs.ConstructionAcceptedGlobalExpressionSequence
import Goose.Proofs.ConstructionAcceptedMixedExecution

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

inductive GlobalScalarStatements : List Stmt → Prop
  | nil : GlobalScalarStatements []
  | expression (expression : Expr) (origin : Nat) (rest : List Stmt)
      (form : AcceptedBinaryExpression expression) (tail : GlobalScalarStatements rest) :
      GlobalScalarStatements (.expr expression origin :: rest)
  | assign (id : Nat) (expression : Expr) (origin : Nat) (rest : List Stmt)
      (form : AcceptedBinaryExpression expression) (tail : GlobalScalarStatements rest) :
      GlobalScalarStatements (.assign (.global id) expression origin :: rest)

private theorem globalAssignSequence_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem globalScalarStatements_checker_advance {statements : List Stmt} (form : GlobalScalarStatements statements) :
    ∀ (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
      (state : ExecutionState) (types : RootTypes) (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState),
      AcceptedFrame config accepted frame state types → frame.typing.globalLimit ≤ frame.initialized →
      (∀ parameter global, ¬ frame.interpretation.parameters parameter (.global global)) →
      GlobalEffectTargetsBounded frame.rootCursor.eff frame.initialized →
      typeStatements frame.typingFuel frame.typing statements frame.typingCounter = .ok (next, typingAfter) →
      rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter) →
      next = frame.typing ∧ typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar ∧
      GlobalEffectTargetsBounded rootsAfter.eff frame.initialized := by
  induction form with
  | nil =>
    intro config accepted frame state types next typingAfter rootsAfter source limit noParameters bounded typed rooted
    cases nesting : frame.typingFuel with
    | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      rw [nesting] at typed
      change Except.ok (frame.typing, frame.typingCounter) = Except.ok (next, typingAfter) at typed
      change Except.ok ((), frame.rootCursor) = Except.ok ((), rootsAfter) at rooted
      cases typed
      cases rooted
      exact ⟨rfl, rfl, rfl, bounded⟩
  | expression expression origin rest expressionForm tail ih =>
    intro config accepted frame state types next typingAfter rootsAfter source limit noParameters bounded typed rooted
    obtain ⟨rootMiddle, headRooted, tailRooted⟩ := rpStmts_cons rooted
    obtain ⟨operandRoots, operandRooted⟩ := rpStmt_expression headRooted
    cases nesting : frame.typingFuel with
    | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
    | succ headFuel =>
      cases headFuel with
      | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ checkFuel =>
        rw [nesting] at typed
        simp only [typeStatements, bind, StateT.bind] at typed
        obtain ⟨result, headTyped, tailTyped⟩ := globalAssignSequence_bind_success _ _ _ typed
        obtain ⟨headEnvironment, headCounter⟩ := result
        obtain ⟨sameEnv, operandTypes, operandTyped⟩ := typeStatement_expression_parts checkFuel frame.typing headEnvironment
          expression origin frame.typingCounter headCounter headTyped
        obtain ⟨ty, sameTypes⟩ := typeExpr_scalar_singleton expressionForm checkFuel
          (ordinaryOperandFrame frame checkFuel).typing frame.typingCounter headCounter operandTypes operandTyped
        subst operandTypes
        have middleBound := recursiveScalar_effects_bounded expressionForm checkFuel (ordinaryOperandFrame frame checkFuel).typing
          frame.source frame.initialized frame.typingCounter headCounter frame.rootCursor rootMiddle [ty] operandRoots limit bounded operandTyped operandRooted
        have available : GlobalEffectsAvailable frame.interpretation frame.initialized rootMiddle.eff := by
          intro target member global instantiates
          cases target with
          | global other =>
            change global = other at instantiates
            subst global
            exact middleBound other member
          | param parameter => exact (noParameters parameter global instantiates.1).elim
        have checked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression ty operandRoots headCounter rootMiddle :=
          ⟨operandTyped, operandRooted, available⟩
        have ⟨sameTyping, sameCounter, middleSource⟩ := checkedScalarExpression_statementAdvance config accepted frame state types source
          expression origin expressionForm checkFuel ty operandRoots headCounter rootMiddle checked headEnvironment headCounter rootMiddle headTyped headRooted
        let middleFrame := { frame with
          typingFuel := checkFuel + 1
          typing := headEnvironment
          typingCounter := headCounter
          rootCursor := rootMiddle }
        have result := ih config accepted middleFrame state types next typingAfter rootsAfter middleSource
          (by simpa [middleFrame, sameTyping] using limit) noParameters middleBound tailTyped tailRooted
        have sameRoot : rootMiddle.nextVar = frame.rootCursor.nextVar := by
          have cursor := checked_binary_recursive_cursor expressionForm (ordinaryOperandFrame frame checkFuel) ty operandRoots headCounter rootMiddle checked
          simpa [ordinaryOperandFrame] using cursor.2
        simpa [middleFrame, sameTyping, sameCounter, sameRoot] using result
  | assign id expression origin rest expressionForm tail ih =>
    intro config accepted frame state types next typingAfter rootsAfter source limit noParameters bounded typed rooted
    obtain ⟨rootMiddle, headRooted, tailRooted⟩ := rpStmts_cons rooted
    cases nesting : frame.typingFuel with
    | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
    | succ headFuel =>
      cases headFuel with
      | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ checkFuel =>
        rw [nesting] at typed
        simp only [typeStatements, bind, StateT.bind] at typed
        obtain ⟨result, headTyped, tailTyped⟩ := globalAssignSequence_bind_success _ _ _ typed
        obtain ⟨headEnvironment, headCounter⟩ := result
        have ⟨sameEnv, sameCounter, sameRoot, middleBound⟩ := checkedGlobalAssign_prefix_advance checkFuel config accepted
          frame state types id expression origin expressionForm source limit noParameters bounded headEnvironment headCounter rootMiddle headTyped headRooted
        let middleFrame := { frame with
          typingFuel := checkFuel + 1
          rootCursor := rootMiddle }
        have middleSource : AcceptedFrame config accepted middleFrame state types :=
          (source.withRootCursor rootMiddle sameRoot).withTypingFuel (checkFuel + 1)
        have tailTyped' : typeStatements middleFrame.typingFuel middleFrame.typing rest middleFrame.typingCounter = .ok (next, typingAfter) := by
          simpa [middleFrame, sameEnv, sameCounter] using tailTyped
        have result := ih config accepted middleFrame state types next typingAfter rootsAfter middleSource limit noParameters middleBound tailTyped' tailRooted
        simpa [middleFrame, sameRoot] using result

#print axioms globalScalarStatements_checker_advance
theorem execStmts_globalScalar_prefix {statements : List Stmt} (form : GlobalScalarStatements statements) :
    ∀ (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
      (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient)
      (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
      (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState),
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.typing.globalLimit ≤ frame.initialized →
      (∀ parameter global, ¬ frame.interpretation.parameters parameter (.global global)) →
      GlobalEffectTargetsBounded frame.rootCursor.eff frame.initialized →
      typeStatements frame.typingFuel frame.typing statements frame.typingCounter = .ok (next, typingAfter) →
      rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter) →
      (∀ id expression origin, .assign (.global id) expression origin ∈ statements →
        ∀ descriptor, config.module.globals[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) →
      ∃ finalFrame,
        let outcome := execStmts fuel config frame.interpretation.environment statements before
        let after := Goose.Proofs.Exit.stepState outcome
        finalFrame.initialized = frame.initialized ∧ finalFrame.interpretation = frame.interpretation ∧ finalFrame.source = frame.source ∧
        AcceptedWorld config frame.initialized after ambient types live regions pending ∧
        AcceptedFrame config accepted finalFrame after types ∧
        (match outcome with
        | .ok flow _ => flow = .normal .unit ∧ finalFrame.typing = next ∧ finalFrame.typingCounter = typingAfter ∧ finalFrame.rootCursor = rootsAfter
        | .stop .. => True
        | _ => False) := by
  induction form with
  | nil =>
    intro fuel config accepted frame before ambient types live regions pending next typingAfter rootsAfter world source limit noParameters bounded typed rooted scalar
    cases nesting : frame.typingFuel with
    | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
    | succ checkFuel =>
      rw [nesting] at typed
      change Except.ok (frame.typing, frame.typingCounter) = Except.ok (next, typingAfter) at typed
      change Except.ok ((), frame.rootCursor) = Except.ok ((), rootsAfter) at rooted
      cases typed
      cases rooted
      cases fuel <;> simp only [execStmts, timeout, EvalM.stop, pure, Goose.Proofs.Exit.stepState]
      all_goals exact ⟨frame, rfl, rfl, rfl, world, source, by simp⟩
  | expression expression origin rest expressionForm tail ih =>
    intro fuel config accepted frame before ambient types live regions pending next typingAfter rootsAfter world source limit noParameters bounded typed rooted scalar
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, rfl, rfl, rfl, world, source, trivial⟩
    | succ fuel =>
      obtain ⟨rootMiddle, headRooted, tailRooted⟩ := rpStmts_cons rooted
      obtain ⟨operandRoots, operandRooted⟩ := rpStmt_expression headRooted
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
        | succ checkFuel =>
          rw [nesting] at typed
          simp only [typeStatements, bind, StateT.bind] at typed
          obtain ⟨result, headTyped, tailTyped⟩ := globalAssignSequence_bind_success _ _ _ typed
          obtain ⟨headEnvironment, headCounter⟩ := result
          obtain ⟨sameEnv, operandTypes, operandTyped⟩ := typeStatement_expression_parts checkFuel frame.typing headEnvironment
            expression origin frame.typingCounter headCounter headTyped
          obtain ⟨ty, sameTypes⟩ := typeExpr_scalar_singleton expressionForm checkFuel
            (ordinaryOperandFrame frame checkFuel).typing frame.typingCounter headCounter operandTypes operandTyped
          subst operandTypes
          have middleBound := recursiveScalar_effects_bounded expressionForm checkFuel (ordinaryOperandFrame frame checkFuel).typing
            frame.source frame.initialized frame.typingCounter headCounter frame.rootCursor rootMiddle [ty] operandRoots limit bounded operandTyped operandRooted
          have available : GlobalEffectsAvailable frame.interpretation frame.initialized rootMiddle.eff := by
            intro target member global instantiates
            cases target with
            | global other =>
              change global = other at instantiates
              subst global
              exact middleBound other member
            | param parameter => exact (noParameters parameter global instantiates.1).elim
          have checked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression ty operandRoots headCounter rootMiddle :=
            ⟨operandTyped, operandRooted, available⟩
          have ⟨sameTyping, sameCounter, middleSource⟩ := checkedScalarExpression_statementAdvance config accepted frame before types source
            expression origin expressionForm checkFuel ty operandRoots headCounter rootMiddle checked headEnvironment headCounter rootMiddle headTyped headRooted
          have head := execStmt_checkedScalarExpression_complete expression origin expressionForm fuel checkFuel config accepted frame before
            ambient types live regions pending world source ty operandRoots headCounter rootMiddle checked
          cases headExecution : execStmt fuel config frame.interpretation.environment (.expr expression origin) before with
          | stop reason after =>
            simp only [headExecution, Goose.Proofs.Exit.stepState] at head
            have same := head.1
            subst after
            simp only [execStmts, bind, headExecution, Goose.Proofs.Exit.stepState]
            exact ⟨frame, rfl, rfl, rfl, world, source, trivial⟩
          | escape address carriers after =>
            exact ((execStmt_scalar_controlFree expression origin expressionForm fuel config frame.interpretation.environment).1
              before address carriers after headExecution).elim
          | jump target kind after =>
            exact ((execStmt_scalar_controlFree expression origin expressionForm fuel config frame.interpretation.environment).2
              before target kind after headExecution).elim
          | ok flow middle =>
            obtain ⟨sameFlow, sameState⟩ := head.2.1 flow middle headExecution
            subst flow middle
            let middleFrame := { frame with
              typingFuel := checkFuel + 1
              typing := headEnvironment
              typingCounter := headCounter
              rootCursor := rootMiddle }
            have tailTyped' : typeStatements middleFrame.typingFuel middleFrame.typing rest middleFrame.typingCounter = .ok (next, typingAfter) := tailTyped
            have remainingScalar : ∀ id expression origin, .assign (.global id) expression origin ∈ rest →
                ∀ descriptor, config.module.globals[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
              intro other expr otherOrigin member descriptor found
              exact scalar other expr otherOrigin (List.mem_cons_of_mem _ member) descriptor found
            obtain ⟨finalFrame, initEq, interpretationEq, sourceEq, finalWorld, finalSource, finalFlow⟩ :=
              ih fuel config accepted middleFrame before ambient types live regions pending next typingAfter rootsAfter
                world middleSource (by simpa [middleFrame, sameTyping] using limit) noParameters middleBound tailTyped' tailRooted remainingScalar
            change (match execStmts fuel config frame.interpretation.environment rest before with
              | .ok flow _ => _ | .stop .. => _ | _ => False) at finalFlow
            simp only [execStmts, bind, headExecution, Goose.Proofs.Exit.stepState]
            exact ⟨finalFrame, initEq, interpretationEq, sourceEq, finalWorld, finalSource, finalFlow⟩
  | assign id expression origin rest expressionForm tail ih =>
    intro fuel config accepted frame before ambient types live regions pending next typingAfter rootsAfter world source limit noParameters bounded typed rooted scalar
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, rfl, rfl, rfl, world, source, trivial⟩
    | succ fuel =>
      obtain ⟨rootMiddle, headRooted, tailRooted⟩ := rpStmts_cons rooted
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
        | succ checkFuel =>
          rw [nesting] at typed
          simp only [typeStatements, bind, StateT.bind] at typed
          obtain ⟨result, headTyped, tailTyped⟩ := globalAssignSequence_bind_success _ _ _ typed
          obtain ⟨headEnvironment, headCounter⟩ := result
          have ⟨sameEnv, sameCounter, sameRoot, middleBound⟩ := checkedGlobalAssign_prefix_advance checkFuel config accepted
            frame before types id expression origin expressionForm source limit noParameters bounded headEnvironment headCounter rootMiddle headTyped headRooted
          have headScalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
              (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
            intro descriptor found
            exact scalar id expression origin (by simp) descriptor found
          have head := execStmt_checkedGlobalAssign_prefix fuel checkFuel config accepted frame before ambient types live regions pending
            id expression origin expressionForm world source limit noParameters headEnvironment headCounter rootMiddle headTyped headRooted headScalar
          cases headExecution : execStmt fuel config frame.interpretation.environment (.assign (.global id) expression origin) before with
          | stop reason after =>
            simp only [headExecution, Goose.Proofs.Exit.stepState] at head
            simp only [execStmts, bind, headExecution, Goose.Proofs.Exit.stepState]
            exact ⟨frame, rfl, rfl, rfl, head.1, head.2.1, trivial⟩
          | escape address carriers after | jump target kind after =>
            simp only [headExecution] at head
            exact head.2.2.elim
          | ok flow middle =>
            simp only [headExecution, Goose.Proofs.Exit.stepState] at head
            have flowEq := head.2.2
            subst flow
            let middleFrame := { frame with
              typingFuel := checkFuel + 1
              rootCursor := rootMiddle }
            have middleSource : AcceptedFrame config accepted middleFrame middle types :=
              (head.2.1.withRootCursor rootMiddle sameRoot).withTypingFuel (checkFuel + 1)
            have tailTyped' : typeStatements middleFrame.typingFuel middleFrame.typing rest middleFrame.typingCounter = .ok (next, typingAfter) := by
              simpa [middleFrame, sameEnv, sameCounter] using tailTyped
            have remainingScalar : ∀ id expression origin, .assign (.global id) expression origin ∈ rest →
                ∀ descriptor, config.module.globals[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
              intro other expr otherOrigin member descriptor found
              exact scalar other expr otherOrigin (List.mem_cons_of_mem _ member) descriptor found
            obtain ⟨finalFrame, initEq, interpretationEq, sourceEq, finalWorld, finalSource, finalFlow⟩ :=
              ih fuel config accepted middleFrame middle ambient types live regions pending next typingAfter rootsAfter
                head.1 middleSource limit noParameters middleBound tailTyped' tailRooted remainingScalar
            change (match execStmts fuel config frame.interpretation.environment rest middle with
              | .ok flow _ => _ | .stop .. => _ | _ => False) at finalFlow
            simp only [execStmts, bind, headExecution, Goose.Proofs.Exit.stepState]
            exact ⟨finalFrame, initEq, interpretationEq, sourceEq, finalWorld, finalSource, finalFlow⟩

#print axioms execStmts_globalScalar_prefix
end Goose.Proofs.ConstructionAcceptedExecution
