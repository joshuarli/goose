import Goose.Proofs.ConstructionAcceptedUnknownLeftOperator
import Goose.Proofs.ConstructionAcceptedBinaryComplete
import Lean.Elab.Tactic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def retentionHelperName (name : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Roots") 0) "Goose") "Construct") name

elab "unfold_retention_named" : tactic => do
  let named := Lean.mkIdent (retentionHelperName "noteNamed")
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $named at *))

theorem initializer_retains_read (config : EvalConfig) (names : Array (List RootRef)) (id : Nat) (localRead : Bool) :
    InitializerRetainsUnknown config names (.read (if localRead then .var id else .global id)) := by
  intro before after roots prior checked
  cases localRead <;> simp only [Bool.false_eq_true, ite_false, ite_true] at checked
  all_goals
    simp only [rpExpr, rpPlace] at checked
    unfold_retention_named
    simp [initializerSource, initImpl, readRoots, addReads, addRoots, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at checked
    obtain ⟨_, rfl⟩ := checked
    exact prior

#print axioms initializer_retains_read

theorem initializer_retains_not (config : EvalConfig) (names : Array (List RootRef)) (expression : Expr)
    (childRetains : InitializerRetainsUnknown config names expression) : InitializerRetainsUnknown config names (.not expression) := by
  intro before after roots prior checked
  exact initializer_unknown_not config names expression before after roots
    (fun childRoots middle child => childRetains before middle childRoots prior child) checked

theorem initializer_retains_unary (config : EvalConfig) (names : Array (List RootRef)) (operation : Goose.Core.UnOp)
    (expression : Expr) (origin : Nat) (childRetains : InitializerRetainsUnknown config names expression) :
    InitializerRetainsUnknown config names (.un operation expression origin) := by
  intro before after roots prior checked
  change (do let _ ← rpExpr (initializerSource config names) expression
             match operation with | .neg => noteAborts | .bitnot => pure ()
             pure []) before = .ok (roots, after) at checked
  simp only [bind, StateT.bind, Except.bind] at checked
  cases child : rpExpr (initializerSource config names) expression before with
  | error failure => simp [child] at checked
  | ok pair =>
    obtain ⟨childRoots, middle⟩ := pair
    have retained := childRetains before middle childRoots prior child
    cases operation <;>
      simp [child, noteAborts, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure] at checked <;>
      obtain ⟨_, rfl⟩ := checked <;> simpa using retained

theorem initializer_retains_conversion (config : EvalConfig) (names : Array (List RootRef)) (kind : Goose.Core.ConvKind)
    (ty : Ty) (expression : Expr) (origin : Nat) (childRetains : InitializerRetainsUnknown config names expression) :
    InitializerRetainsUnknown config names (.conv kind ty expression origin) := by
  intro before after roots prior checked
  change (do let _ ← rpExpr (initializerSource config names) expression
             match kind with | .as => noteAborts | _ => pure ()
             pure []) before = .ok (roots, after) at checked
  simp only [bind, StateT.bind, Except.bind] at checked
  cases child : rpExpr (initializerSource config names) expression before with
  | error failure => simp [child] at checked
  | ok pair =>
    obtain ⟨childRoots, middle⟩ := pair
    have retained := childRetains before middle childRoots prior child
    cases kind <;>
      simp [child, noteAborts, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure] at checked <;>
      obtain ⟨_, rfl⟩ := checked <;> simpa using retained

theorem initializer_retains_sequence (config : EvalConfig) (names : Array (List RootRef)) (left right : Expr)
    (leftRetains : InitializerRetainsUnknown config names left) (rightRetains : InitializerRetainsUnknown config names right)
    (before after : RState) (roots : List RootRef) (prior : before.eff.unknown = true)
    (checked : (do let _ ← rpExpr (initializerSource config names) left
                   let _ ← rpExpr (initializerSource config names) right
                   pure []) before = .ok (roots, after)) : after.eff.unknown = true := by
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at checked
  cases first : rpExpr (initializerSource config names) left before with
  | error failure => simp [first] at checked
  | ok pair =>
    obtain ⟨leftRoots, middle⟩ := pair
    have retained := leftRetains before middle leftRoots prior first
    simp only [first] at checked
    cases second : rpExpr (initializerSource config names) right middle with
    | error failure => simp [second] at checked
    | ok pair =>
      obtain ⟨rightRoots, final⟩ := pair
      simp [second] at checked
      obtain ⟨_, rfl⟩ := checked
      exact rightRetains middle final rightRoots retained second

theorem initializer_retains_cmp (config : EvalConfig) (names : Array (List RootRef)) (operation : Goose.Core.CmpOp)
    (left right : Expr) (leftRetains : InitializerRetainsUnknown config names left) (rightRetains : InitializerRetainsUnknown config names right) :
    InitializerRetainsUnknown config names (.cmp operation left right) := by
  intro before after roots prior checked
  exact initializer_retains_sequence config names left right leftRetains rightRetains before after roots prior checked

theorem initializer_retains_and (config : EvalConfig) (names : Array (List RootRef))
    (left right : Expr) (leftRetains : InitializerRetainsUnknown config names left) (rightRetains : InitializerRetainsUnknown config names right) :
    InitializerRetainsUnknown config names (.and left right) := by
  intro before after roots prior checked
  exact initializer_retains_sequence config names left right leftRetains rightRetains before after roots prior checked

theorem initializer_retains_or (config : EvalConfig) (names : Array (List RootRef))
    (left right : Expr) (leftRetains : InitializerRetainsUnknown config names left) (rightRetains : InitializerRetainsUnknown config names right) :
    InitializerRetainsUnknown config names (.or left right) := by
  intro before after roots prior checked
  exact initializer_retains_sequence config names left right leftRetains rightRetains before after roots prior checked

theorem initializer_retains_binary (config : EvalConfig) (names : Array (List RootRef)) (operation : Goose.Core.BinOp)
    (left right : Expr) (origin : Nat) (leftRetains : InitializerRetainsUnknown config names left)
    (rightRetains : InitializerRetainsUnknown config names right) : InitializerRetainsUnknown config names (.bin operation left right origin) := by
  intro before after roots prior checked
  change (do let _ ← rpExpr (initializerSource config names) left
             let _ ← rpExpr (initializerSource config names) right
             if binOpMayAbort operation then noteAborts
             pure []) before = .ok (roots, after) at checked
  simp only [bind, StateT.bind, Except.bind] at checked
  cases first : rpExpr (initializerSource config names) left before with
  | error failure => simp [first] at checked
  | ok pair =>
    obtain ⟨leftRoots, middle⟩ := pair
    have retained := leftRetains before middle leftRoots prior first
    simp only [first] at checked
    cases second : rpExpr (initializerSource config names) right middle with
    | error failure => simp [second] at checked
    | ok pair =>
      obtain ⟨rightRoots, final⟩ := pair
      have retained := rightRetains middle final rightRoots retained second
      cases aborts : binOpMayAbort operation <;>
        simp [second, aborts, noteAborts, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          pure, StateT.pure, Except.pure] at checked <;>
        obtain ⟨_, rfl⟩ := checked <;> simpa using retained

theorem initializer_retains_scalar {expression : Expr} (form : AcceptedScalarExpression expression)
    (config : EvalConfig) (names : Array (List RootRef)) : InitializerRetainsUnknown config names expression := by
  cases form with
  | integer ty value => exact initializer_literal_retainsUnknown config names (.integer ty value)
  | boolean value => exact initializer_literal_retainsUnknown config names (.boolean value)
  | globalRead id => simpa using initializer_retains_read config names id false
  | localRead id => simpa using initializer_retains_read config names id true

theorem initializer_retains_notExpression {expression : Expr} (form : AcceptedNotExpression expression)
    (config : EvalConfig) (names : Array (List RootRef)) : InitializerRetainsUnknown config names expression := by
  induction form with
  | scalar form => exact initializer_retains_scalar form config names
  | not form ih => exact initializer_retains_not config names _ ih

theorem initializer_retains_numeric {expression : Expr} (form : AcceptedNumericExpression expression)
    (config : EvalConfig) (names : Array (List RootRef)) : InitializerRetainsUnknown config names expression := by
  induction form with
  | scalar form => exact initializer_retains_notExpression form config names
  | unary operation origin form ih => exact initializer_retains_unary config names operation _ origin ih
  | conversion kind ty origin form ih => exact initializer_retains_conversion config names kind ty _ origin ih

theorem initializer_retains_binaryExpression {expression : Expr} (form : AcceptedBinaryExpression expression)
    (config : EvalConfig) (names : Array (List RootRef)) : InitializerRetainsUnknown config names expression := by
  induction form with
  | numeric form => exact initializer_retains_numeric form config names
  | binary operation origin left right leftIH rightIH => exact initializer_retains_binary config names operation _ _ origin leftIH rightIH
  | comparison operation left right leftIH rightIH => exact initializer_retains_cmp config names operation _ _ leftIH rightIH
  | conjunction left right leftIH rightIH => exact initializer_retains_and config names _ _ leftIH rightIH
  | disjunction left right leftIH rightIH => exact initializer_retains_or config names _ _ leftIH rightIH
  | not form ih => exact initializer_retains_not config names _ ih
  | unary operation origin form ih => exact initializer_retains_unary config names operation _ origin ih
  | conversion kind ty origin form ih => exact initializer_retains_conversion config names kind ty _ origin ih

theorem validated_scalar_initializer_binaryLeftScalar_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (target origin : Nat) (context : Context) (callee : Impl)
    (operation : Goose.Core.BinOp) (left right : Expr) (location : Nat)
    (present : config.module.globals[id]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (expression : descriptor.init = .bin operation left right location)
    (leftForm : OperatorWrappedZeroCall target origin left) (rightForm : AcceptedBinaryExpression right)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) : ∃ summary, callee.summary = .known summary := by
  obtain ⟨names, roots, after, rooted, clear⟩ := validated_scalar_initializer_noUnknown config accepted id descriptor present scalar
  rw [expression] at rooted
  cases summary : callee.summary with
  | known value => exact ⟨value, rfl⟩
  | unknown =>
    have leftUnknown := initializer_unknown_operatorWrappedZeroCall config names target origin context callee
      contextAt calleeAt parameters summary leftForm
    have retained := initializer_retains_binaryExpression rightForm config names
    have raised := initializer_unknown_binaryLeft config names operation left right location leftUnknown retained ⟨0, {}, []⟩ after roots rooted
    simp [clear] at raised

#print axioms validated_scalar_initializer_binaryLeftScalar_known
#print axioms initializer_retains_binaryExpression
#print axioms initializer_retains_numeric
#print axioms initializer_retains_notExpression
#print axioms initializer_retains_scalar
#print axioms initializer_retains_binary
#print axioms initializer_retains_cmp
#print axioms initializer_retains_and
#print axioms initializer_retains_or
#print axioms initializer_retains_not
#print axioms initializer_retains_unary
#print axioms initializer_retains_conversion
end Goose.Proofs.ConstructionAcceptedExecution
