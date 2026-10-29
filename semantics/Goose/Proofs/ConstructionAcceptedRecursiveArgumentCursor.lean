import Goose.Proofs.ConstructionAcceptedNestedParameterCursor
import Goose.Proofs.ConstructionAcceptedUnaryCallComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

inductive RecursiveArgumentExpression (config : EvalConfig) (integer : Goose.Core.IntTy) (implementation : Impl) : Expr → Prop
  | literal (value : Int) : RecursiveArgumentExpression config integer implementation (.lit integer value)
  | localRead (id : Nat) (descriptor : LocalVar) : implementation.vars[id]? = some descriptor → descriptor.ty = .int integer →
      RecursiveArgumentExpression config integer implementation (.read (.var id))
  | binary {left right : Expr} (operation : Goose.Core.BinOp) (origin : Nat) :
      RecursiveArgumentExpression config integer implementation left → RecursiveArgumentExpression config integer implementation right →
      RecursiveArgumentExpression config integer implementation (.bin operation left right origin)
  | zeroCall (target origin : Nat) (context : Context) (callee : Impl) :
      config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some callee →
      callee.params = #[] → callee.results = #[⟨.int integer, .register, none⟩] →
      RegisterCallGraphWithCallLocals config (.int integer) →
      RecursiveArgumentExpression config integer implementation (.call target [] origin)
  | call {argument : Expr} (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param)
      (descriptor : LocalVar) (summary : Summary) :
      config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some callee →
      callee.params = #[parameter] → parameter.mode = .byValue → callee.vars[parameter.var]? = some descriptor →
      descriptor.ty = .int integer → callee.results = #[⟨.int integer, .register, none⟩] → callee.summary = .known summary →
      RecursiveArgumentExpression config integer implementation argument →
      RecursiveArgumentExpression config integer implementation (.call target [.byVal argument] origin)

theorem RecursiveArgumentExpression.toSource {config : EvalConfig} {integer : Goose.Core.IntTy} {implementation : Impl} {expression : Expr}
    (form : RecursiveArgumentExpression config integer implementation expression) :
    NestedParameterExpression config integer implementation expression := by
  induction form with
  | literal value => exact .literal value
  | localRead id descriptor declared descriptorType => exact .localRead id descriptor declared (Or.inl ⟨integer, descriptorType⟩)
  | binary operation origin left right leftIH rightIH => exact .binary operation origin leftIH rightIH
  | zeroCall target origin context callee contextAt calleeAt parameters results graph =>
    exact .zeroCall target origin context callee contextAt calleeAt parameters results
  | call target origin context callee parameter descriptor summary contextAt calleeAt parameters mode declared descriptorType results known argument ih =>
    exact .call target origin context callee parameter summary contextAt calleeAt parameters results known ih

theorem checkedRecursiveArgument_cursor {config : EvalConfig} {integer : Goose.Core.IntTy} {implementation : Impl} {expression : Expr}
    (form : RecursiveArgumentExpression config integer implementation expression) (frame : ConstructionSourceFrame)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (typingModule : frame.typing.module = config.module) (rootModule : frame.source.mod = config.module)
    (requests : frame.typing.resultRequests = [] ∨ frame.typing.resultRequests = [.register])
    (checked : CheckedValue frame expression (.int integer) roots typingAfter rootsAfter) :
    typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar := by
  exact ⟨nestedParameterExpression_typingCursor form.toSource frame.typingFuel frame.typing frame.typingCounter typingAfter (.int integer)
      typingModule requests checked.typing,
    nestedParameterExpression_rootCursor form.toSource frame roots rootsAfter rootModule checked.provenance⟩

#print axioms checkedRecursiveArgument_cursor
#print axioms RecursiveArgumentExpression.toSource
end Goose.Proofs.ConstructionAcceptedExecution
