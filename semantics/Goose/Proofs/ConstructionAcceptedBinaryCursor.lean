import Goose.Proofs.ConstructionAcceptedBinaryTyping

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

private theorem cursor_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem scalar_checked_cursor {expression : Expr} (form : AcceptedScalarExpression expression)
    (frame : ConstructionSourceFrame) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar := by
  cases form with
  | integer type value =>
    have typing := checked.typing
    cases fuel : frame.typingFuel with
    | zero => rw [fuel] at typing; change Except.error _ = Except.ok _ at typing; cases typing
    | succ fuel =>
      rw [fuel] at typing
      change Except.ok ([Ty.int type], frame.typingCounter) = Except.ok ([ty], typingAfter) at typing
      cases typing
      have provenance := checked.provenance
      change Except.ok ([], frame.rootCursor) = Except.ok (roots, rootsAfter) at provenance
      cases provenance
      exact ⟨rfl, rfl⟩
  | boolean value =>
    have typing := checked.typing
    cases fuel : frame.typingFuel with
    | zero => rw [fuel] at typing; change Except.error _ = Except.ok _ at typing; cases typing
    | succ fuel =>
      rw [fuel] at typing
      change Except.ok ([Ty.bool], frame.typingCounter) = Except.ok ([ty], typingAfter) at typing
      cases typing
      have provenance := checked.provenance
      change Except.ok ([], frame.rootCursor) = Except.ok (roots, rootsAfter) at provenance
      cases provenance
      exact ⟨rfl, rfl⟩
  | globalRead id =>
    have typing := checked.typing
    cases depth : frame.typingFuel with
    | zero => rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
    | succ remaining =>
      cases remaining with
      | zero => rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
      | succ remaining =>
        rw [depth] at typing
        simp only [typeExpr, typePlace, bind, StateT.bind] at typing
        split at typing
        · change Except.error _ = Except.ok _ at typing; cases typing
        · cases found : frame.typing.module.globals[id]? with
          | none => simp only [found] at typing; change Except.error _ = Except.ok _ at typing; cases typing
          | some descriptor =>
            simp only [found] at typing
            have sameCounter : typingAfter = frame.typingCounter := by
              simp only [pure, StateT.pure, Except.bind] at typing
              obtain ⟨result, required, returned⟩ := cursor_bind_success _ _ _ typing
              cases returned
              cases valid : (descriptor.ty.storable && !descriptor.ty.nonfixed) with
              | false =>
                simp only [valid] at required
                change Except.error _ = Except.ok _ at required
                cases required
              | true =>
                simp only [valid] at required
                change Except.ok ((), frame.typingCounter) = Except.ok result at required
                cases required
                rfl
            have provenance := checked.provenance
            simp [rpExpr, rpPlace, readRoots, addReads, addRoots, modify, bind, pure] at provenance
            cases provenance
            exact ⟨sameCounter, rfl⟩

theorem not_checked_cursor {expression : Expr} (form : AcceptedNotExpression expression)
    (frame : ConstructionSourceFrame) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar := by
  induction form generalizing frame ty roots typingAfter rootsAfter with
  | scalar form => exact scalar_checked_cursor form frame ty roots typingAfter rootsAfter checked
  | @not expression form ih =>
    cases depth : frame.typingFuel with
    | zero => have typing := checked.typing; rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
    | succ fuel =>
      obtain ⟨_, _, operandRoots, operandChecked⟩ := checkedValue_not_operand frame fuel expression ty roots typingAfter rootsAfter depth checked
      exact ih (ordinaryOperandFrame frame fuel) .bool operandRoots typingAfter rootsAfter operandChecked

theorem rpExpr_un_nextVar (environment : PEnv) (operation : Goose.Core.UnOp) (expression : Expr)
    (origin : Goose.Core.OriginId) (before after : RState) (roots : List RootRef)
    (checked : rpExpr environment (.un operation expression origin) before = .ok (roots, after)) :
    ∃ operandRoots operandAfter, rpExpr environment expression before = .ok (operandRoots, operandAfter) ∧
      after.nextVar = operandAfter.nextVar := by
  change (Except.bind (rpExpr environment expression before) _) = .ok (roots, after) at checked
  cases operand : rpExpr environment expression before with
  | error failure => simp only [operand, Except.bind] at checked; cases checked
  | ok value =>
    obtain ⟨operandRoots, operandAfter⟩ := value
    simp only [operand, Except.bind] at checked
    cases operation with
    | bitnot =>
      change Except.ok ([], operandAfter) = Except.ok (roots, after) at checked
      cases checked
      exact ⟨operandRoots, _, rfl, rfl⟩
    | neg =>
      change Except.ok ([], { operandAfter with eff := { operandAfter.eff with aborts := true } }) = Except.ok (roots, after) at checked
      cases checked
      exact ⟨operandRoots, operandAfter, rfl, rfl⟩

theorem rpExpr_conv_nextVar (environment : PEnv) (kind : Goose.Core.ConvKind) (target : Ty) (expression : Expr)
    (origin : Goose.Core.OriginId) (before after : RState) (roots : List RootRef)
    (checked : rpExpr environment (.conv kind target expression origin) before = .ok (roots, after)) :
    ∃ operandRoots operandAfter, rpExpr environment expression before = .ok (operandRoots, operandAfter) ∧
      after.nextVar = operandAfter.nextVar := by
  change (Except.bind (rpExpr environment expression before) _) = .ok (roots, after) at checked
  cases operand : rpExpr environment expression before with
  | error failure => simp only [operand, Except.bind] at checked; cases checked
  | ok value =>
    obtain ⟨operandRoots, operandAfter⟩ := value
    simp only [operand, Except.bind] at checked
    cases kind with
    | widen | asUnchecked =>
      change Except.ok ([], operandAfter) = Except.ok (roots, after) at checked
      cases checked
      exact ⟨operandRoots, _, rfl, rfl⟩
    | as =>
      change Except.ok ([], { operandAfter with eff := { operandAfter.eff with aborts := true } }) = Except.ok (roots, after) at checked
      cases checked
      exact ⟨operandRoots, operandAfter, rfl, rfl⟩

theorem numeric_checked_cursor {expression : Expr} (form : AcceptedNumericExpression expression)
    (frame : ConstructionSourceFrame) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar := by
  induction form generalizing frame ty roots typingAfter rootsAfter with
  | scalar form => exact not_checked_cursor form frame ty roots typingAfter rootsAfter checked
  | @unary expression operation origin form ih =>
    cases depth : frame.typingFuel with
    | zero => have typing := checked.typing; rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
    | succ fuel =>
      obtain ⟨integer, operandRoots, operandAfter, _, _, operandChecked⟩ :=
        checkedValue_un_operand frame fuel operation expression origin ty roots typingAfter rootsAfter depth checked
      obtain ⟨otherRoots, otherAfter, rooted, nextVar⟩ := rpExpr_un_nextVar frame.source operation expression origin
        frame.rootCursor rootsAfter roots checked.provenance
      have same := operandChecked.provenance.symm.trans rooted
      cases same
      have result := ih (ordinaryOperandFrame frame fuel) (.int integer) operandRoots typingAfter operandAfter operandChecked
      exact ⟨result.1, nextVar.trans result.2⟩
  | @conversion expression kind target origin form ih =>
    cases depth : frame.typingFuel with
    | zero => have typing := checked.typing; rw [depth] at typing; change Except.error _ = Except.ok _ at typing; cases typing
    | succ fuel =>
      obtain ⟨integer, _, operandRoots, operandAfter, _, _, _, operandChecked⟩ :=
        checkedValue_conv_operand frame fuel kind target expression origin ty roots typingAfter rootsAfter depth checked
      obtain ⟨otherRoots, otherAfter, rooted, nextVar⟩ := rpExpr_conv_nextVar frame.source kind target expression origin
        frame.rootCursor rootsAfter roots checked.provenance
      have same := operandChecked.provenance.symm.trans rooted
      cases same
      have result := ih (ordinaryOperandFrame frame fuel) (.int integer) operandRoots typingAfter operandAfter operandChecked
      exact ⟨result.1, nextVar.trans result.2⟩

theorem numericOperand_rightFrame_accepted {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (fuel : Nat) (state : ExecutionState) (types : RootTypes)
    (valid : AcceptedFrame config accepted frame state types) {expression : Expr}
    (form : AcceptedNumericExpression expression) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue (ordinaryOperandFrame frame fuel) expression ty roots typingAfter rootsAfter) :
    AcceptedFrame config accepted
      { ordinaryOperandFrame frame fuel with typingCounter := typingAfter, rootCursor := rootsAfter } state types := by
  obtain ⟨counter, cursor⟩ := numeric_checked_cursor form (ordinaryOperandFrame frame fuel) ty roots typingAfter rootsAfter checked
  have initial := ordinaryOperandFrame_accepted accepted frame fuel state types valid
  refine ⟨⟨initial.compatible.module, initial.compatible.rootModule, initial.compatible.variables,
    initial.compatible.sourceVariables, initial.compatible.scopes, initial.compatible.globalCount,
    initial.compatible.globals, initial.compatible.initialized, ?_, ?_, ?_, initial.compatible.initializing,
    initial.compatible.currentScope, initial.compatible.origin⟩,
    initial.frontier, initial.scopeFrontier, ?_, initial.aliases, initial.locals, initial.localTypes, ?_, ?_,
    initial.futureGlobals, initial.direct, initial.contents⟩
  · simpa only [counter, cursor] using initial.compatible.declarations
  · simpa only [counter] using initial.compatible.typingBound
  · simpa only [cursor] using initial.compatible.visible
  · simpa only [cursor] using initial.initializingBefore
  · simpa only [cursor] using initial.uninitializedLocals
  · simpa only [cursor] using initial.uninitializedTypes

#print axioms numericOperand_rightFrame_accepted
#print axioms numeric_checked_cursor
#print axioms not_checked_cursor
#print axioms scalar_checked_cursor
end Goose.Proofs.ConstructionAcceptedExecution
