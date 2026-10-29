import Goose.Proofs.ConstructionAcceptedUnknownCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

def InitializerRaisesUnknown (config : EvalConfig) (names : Array (List RootRef)) (expression : Expr) : Prop :=
  ∀ before after roots, rpExpr (initializerSource config names) expression before = .ok (roots, after) → after.eff.unknown = true

theorem initializer_unknown_rightSequence (config : EvalConfig) (names : Array (List RootRef)) (left right : Expr)
    (rightUnknown : InitializerRaisesUnknown config names right) (before after : RState) (roots : List RootRef)
    (checked : (do let _ ← rpExpr (initializerSource config names) left
                   let _ ← rpExpr (initializerSource config names) right
                   pure []) before = .ok (roots, after)) : after.eff.unknown = true := by
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at checked
  cases first : rpExpr (initializerSource config names) left before with
  | error failure => simp [first] at checked
  | ok pair =>
    obtain ⟨leftRoots, middle⟩ := pair
    simp only [first, Except.bind] at checked
    cases second : rpExpr (initializerSource config names) right middle with
    | error failure => simp [second] at checked
    | ok pair =>
      obtain ⟨rightRoots, final⟩ := pair
      simp [second] at checked
      obtain ⟨_, rfl⟩ := checked
      exact rightUnknown middle final rightRoots second

theorem initializer_unknown_cmpRight (config : EvalConfig) (names : Array (List RootRef)) (operation : Goose.Core.CmpOp)
    (left right : Expr) (rightUnknown : InitializerRaisesUnknown config names right) :
    InitializerRaisesUnknown config names (.cmp operation left right) := by
  intro before after roots checked
  exact initializer_unknown_rightSequence config names left right rightUnknown before after roots checked

theorem initializer_unknown_andRight (config : EvalConfig) (names : Array (List RootRef))
    (left right : Expr) (rightUnknown : InitializerRaisesUnknown config names right) :
    InitializerRaisesUnknown config names (.and left right) := by
  intro before after roots checked
  exact initializer_unknown_rightSequence config names left right rightUnknown before after roots checked

theorem initializer_unknown_orRight (config : EvalConfig) (names : Array (List RootRef))
    (left right : Expr) (rightUnknown : InitializerRaisesUnknown config names right) :
    InitializerRaisesUnknown config names (.or left right) := by
  intro before after roots checked
  exact initializer_unknown_rightSequence config names left right rightUnknown before after roots checked

theorem initializer_unknown_unary (config : EvalConfig) (names : Array (List RootRef)) (operation : Goose.Core.UnOp)
    (expression : Expr) (origin : Nat) (childUnknown : InitializerRaisesUnknown config names expression) :
    InitializerRaisesUnknown config names (.un operation expression origin) := by
  intro before after roots checked
  change (do let _ ← rpExpr (initializerSource config names) expression
             match operation with | .neg => noteAborts | .bitnot => pure ()
             pure []) before = .ok (roots, after) at checked
  simp only [bind, StateT.bind, Except.bind] at checked
  cases child : rpExpr (initializerSource config names) expression before with
  | error failure => simp [child] at checked
  | ok pair =>
    obtain ⟨childRoots, middle⟩ := pair
    have raised := childUnknown before middle childRoots child
    cases operation <;>
      simp [child, noteAborts, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure] at checked <;>
      obtain ⟨_, rfl⟩ := checked <;> simpa using raised

theorem initializer_unknown_conversion (config : EvalConfig) (names : Array (List RootRef)) (kind : Goose.Core.ConvKind)
    (ty : Ty) (expression : Expr) (origin : Nat) (childUnknown : InitializerRaisesUnknown config names expression) :
    InitializerRaisesUnknown config names (.conv kind ty expression origin) := by
  intro before after roots checked
  change (do let _ ← rpExpr (initializerSource config names) expression
             match kind with | .as => noteAborts | _ => pure ()
             pure []) before = .ok (roots, after) at checked
  simp only [bind, StateT.bind, Except.bind] at checked
  cases child : rpExpr (initializerSource config names) expression before with
  | error failure => simp [child] at checked
  | ok pair =>
    obtain ⟨childRoots, middle⟩ := pair
    have raised := childUnknown before middle childRoots child
    cases kind <;>
      simp [child, noteAborts, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure] at checked <;>
      obtain ⟨_, rfl⟩ := checked <;> simpa using raised

theorem initializer_unknown_binaryRight (config : EvalConfig) (names : Array (List RootRef)) (operation : Goose.Core.BinOp)
    (left right : Expr) (origin : Nat) (rightUnknown : InitializerRaisesUnknown config names right) :
    InitializerRaisesUnknown config names (.bin operation left right origin) := by
  intro before after roots checked
  change (do let _ ← rpExpr (initializerSource config names) left
             let _ ← rpExpr (initializerSource config names) right
             if binOpMayAbort operation then noteAborts
             pure []) before = .ok (roots, after) at checked
  simp only [bind, StateT.bind, Except.bind] at checked
  cases first : rpExpr (initializerSource config names) left before with
  | error failure => simp [first] at checked
  | ok pair =>
    obtain ⟨leftRoots, middle⟩ := pair
    simp only [first, Except.bind] at checked
    cases second : rpExpr (initializerSource config names) right middle with
    | error failure => simp [second] at checked
    | ok pair =>
      obtain ⟨rightRoots, final⟩ := pair
      have raised := rightUnknown middle final rightRoots second
      cases aborts : binOpMayAbort operation <;>
        simp [second, aborts, noteAborts, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          pure, StateT.pure, Except.pure] at checked <;>
        obtain ⟨_, rfl⟩ := checked <;> simpa using raised

inductive OperatorWrappedCall (target origin : Nat) (arguments : List Arg) : Expr → Prop
  | call : OperatorWrappedCall target origin arguments (.call target arguments origin)
  | not {expression : Expr} : OperatorWrappedCall target origin arguments expression → OperatorWrappedCall target origin arguments (.not expression)
  | unary (operation : Goose.Core.UnOp) (location : Nat) {expression : Expr} :
      OperatorWrappedCall target origin arguments expression → OperatorWrappedCall target origin arguments (.un operation expression location)
  | conversion (kind : Goose.Core.ConvKind) (ty : Ty) (location : Nat) {expression : Expr} :
      OperatorWrappedCall target origin arguments expression → OperatorWrappedCall target origin arguments (.conv kind ty expression location)
  | binaryRight (operation : Goose.Core.BinOp) (left : Expr) (location : Nat) {right : Expr} :
      OperatorWrappedCall target origin arguments right → OperatorWrappedCall target origin arguments (.bin operation left right location)
  | compareRight (operation : Goose.Core.CmpOp) (left : Expr) {right : Expr} :
      OperatorWrappedCall target origin arguments right → OperatorWrappedCall target origin arguments (.cmp operation left right)
  | andRight (left : Expr) {right : Expr} : OperatorWrappedCall target origin arguments right → OperatorWrappedCall target origin arguments (.and left right)
  | orRight (left : Expr) {right : Expr} : OperatorWrappedCall target origin arguments right → OperatorWrappedCall target origin arguments (.or left right)

theorem initializer_unknown_operatorWrappedCall (config : EvalConfig) (names : Array (List RootRef)) (target origin : Nat)
    (arguments : List Arg) (context : Context) (callee : Impl) (contextAt : config.module.contexts[target]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee) (unknown : callee.summary = .unknown) :
    ∀ {expression}, OperatorWrappedCall target origin arguments expression → InitializerRaisesUnknown config names expression := by
  intro expression form
  induction form with
  | call =>
    intro before after roots checked
    exact initializer_unknown_anyArgumentCallExpr config names target origin context callee arguments before after roots contextAt calleeAt unknown checked
  | not inner ih =>
    intro before after roots checked
    exact initializer_unknown_not config names _ before after roots (fun childRoots middle child => ih before middle childRoots child) checked
  | unary operation location inner ih => exact initializer_unknown_unary config names operation _ location ih
  | conversion kind ty location inner ih => exact initializer_unknown_conversion config names kind ty _ location ih
  | binaryRight operation left location inner ih => exact initializer_unknown_binaryRight config names operation left _ location ih
  | compareRight operation left inner ih => exact initializer_unknown_cmpRight config names operation left _ ih
  | andRight left inner ih => exact initializer_unknown_andRight config names left _ ih
  | orRight left inner ih => exact initializer_unknown_orRight config names left _ ih

theorem validated_scalar_initializer_operatorWrappedCall_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (target origin : Nat) (arguments : List Arg) (context : Context) (callee : Impl)
    (present : config.module.globals[id]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (form : OperatorWrappedCall target origin arguments descriptor.init)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee) :
    ∃ summary, callee.summary = .known summary := by
  obtain ⟨names, roots, after, rooted, clear⟩ := validated_scalar_initializer_noUnknown config accepted id descriptor present scalar
  cases summary : callee.summary with
  | known value => exact ⟨value, rfl⟩
  | unknown =>
    have raised := initializer_unknown_operatorWrappedCall config names target origin arguments context callee contextAt calleeAt summary
      form ⟨0, {}, []⟩ after roots rooted
    simp [clear] at raised


inductive OperatorWrappedZeroCall (target origin : Nat) : Expr → Prop
  | call : OperatorWrappedZeroCall target origin (.call target [] origin)
  | not {expression : Expr} : OperatorWrappedZeroCall target origin expression → OperatorWrappedZeroCall target origin (.not expression)
  | unary (operation : Goose.Core.UnOp) (location : Nat) {expression : Expr} :
      OperatorWrappedZeroCall target origin expression → OperatorWrappedZeroCall target origin (.un operation expression location)
  | conversion (kind : Goose.Core.ConvKind) (ty : Ty) (location : Nat) {expression : Expr} :
      OperatorWrappedZeroCall target origin expression → OperatorWrappedZeroCall target origin (.conv kind ty expression location)
  | binaryRight (operation : Goose.Core.BinOp) (left : Expr) (location : Nat) {right : Expr} :
      OperatorWrappedZeroCall target origin right → OperatorWrappedZeroCall target origin (.bin operation left right location)
  | compareRight (operation : Goose.Core.CmpOp) (left : Expr) {right : Expr} :
      OperatorWrappedZeroCall target origin right → OperatorWrappedZeroCall target origin (.cmp operation left right)
  | andRight (left : Expr) {right : Expr} : OperatorWrappedZeroCall target origin right → OperatorWrappedZeroCall target origin (.and left right)
  | orRight (left : Expr) {right : Expr} : OperatorWrappedZeroCall target origin right → OperatorWrappedZeroCall target origin (.or left right)

theorem OperatorWrappedZeroCall.toWrappedCall {target origin : Nat} {expression : Expr}
    (form : OperatorWrappedZeroCall target origin expression) : OperatorWrappedCall target origin [] expression := by
  induction form with
  | call => exact .call
  | not inner ih => exact .not ih
  | unary operation location inner ih => exact .unary operation location ih
  | conversion kind ty location inner ih => exact .conversion kind ty location ih
  | binaryRight operation left location inner ih => exact .binaryRight operation left location ih
  | compareRight operation left inner ih => exact .compareRight operation left ih
  | andRight left inner ih => exact .andRight left ih
  | orRight left inner ih => exact .orRight left ih

theorem initializer_unknown_operatorWrappedZeroCall (config : EvalConfig) (names : Array (List RootRef)) (target origin : Nat)
    (context : Context) (callee : Impl) (contextAt : config.module.contexts[target]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee) (parameters : callee.params = #[]) (unknown : callee.summary = .unknown) :
    ∀ {expression}, OperatorWrappedZeroCall target origin expression → InitializerRaisesUnknown config names expression := by
  intro expression form
  exact initializer_unknown_operatorWrappedCall config names target origin [] context callee contextAt calleeAt unknown form.toWrappedCall

theorem validated_scalar_initializer_operatorWrappedZeroCall_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (target origin : Nat) (context : Context) (callee : Impl)
    (present : config.module.globals[id]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (form : OperatorWrappedZeroCall target origin descriptor.init)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) : ∃ summary, callee.summary = .known summary := by
  exact validated_scalar_initializer_operatorWrappedCall_known config accepted id descriptor target origin [] context callee present scalar
    form.toWrappedCall contextAt calleeAt

#print axioms OperatorWrappedZeroCall.toWrappedCall
#print axioms initializer_unknown_operatorWrappedCall
#print axioms validated_scalar_initializer_operatorWrappedCall_known
#print axioms initializer_unknown_operatorWrappedZeroCall
#print axioms validated_scalar_initializer_operatorWrappedZeroCall_known
#print axioms initializer_unknown_conversion
#print axioms initializer_unknown_binaryRight
#print axioms initializer_unknown_unary
#print axioms initializer_unknown_cmpRight
#print axioms initializer_unknown_andRight
#print axioms initializer_unknown_orRight
end Goose.Proofs.ConstructionAcceptedExecution
