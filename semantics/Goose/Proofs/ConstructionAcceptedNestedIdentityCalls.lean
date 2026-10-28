import Goose.Proofs.ConstructionAcceptedEarlierScalarComplete
import Goose.Proofs.ConstructionAcceptedIdentityUnaryCall
import Goose.Proofs.ConstructionAcceptedUnaryArgumentSource
import Goose.Proofs.ConstructionAcceptedInvocationValue

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

inductive NestedIdentityExpression (config : EvalConfig) (integer : Goose.Core.IntTy) : Expr → Prop
  | scalar {expression : Expr} : AcceptedBinaryExpression expression → NestedIdentityExpression config integer expression
  | call {argument : Expr} (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar) :
      config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some callee →
      callee.params = #[parameter] → parameter.mode = .byValue → callee.vars[parameter.var]? = some descriptor →
      descriptor.ty = .int integer → callee.results = #[⟨.int integer, .register, none⟩] →
      callee.body = ⟨callee.body.scope, [], some (.read (.var 0))⟩ → NestedIdentityExpression config integer argument →
      NestedIdentityExpression config integer (.call target [.byVal argument] origin)

theorem evalValue_nestedIdentity {config : EvalConfig} {integer : Goose.Core.IntTy} {expression : Expr}
    (form : NestedIdentityExpression config integer expression) (fuel : Nat) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression (.int integer) roots typingAfter rootsAfter) :
    EarlierScalarOutcome config accepted frame before ambient types regions pending (.int integer)
      (evalValue fuel config frame.interpretation.environment expression before) := by
  induction form generalizing fuel frame before ambient types live roots typingAfter rootsAfter with
  | scalar form =>
    exact evalValue_checkedBinary_earlier config integer form fuel accepted frame before ambient types live regions pending
      world source roots typingAfter rootsAfter checked
  | @call argument target origin context callee parameter descriptor contextAt calleeAt parameters mode declared descriptorType results body argumentForm ih =>
    apply evalValue_registerArguments_earlier_fromInvocation fuel config accepted frame before ambient types live regions pending
      target [.byVal argument] context callee (.int integer) origin world source contextAt calleeAt results
    intro callFuel fuelEq
    cases depth : frame.typingFuel with
    | zero =>
      have typed := checked.typing
      rw [depth] at typed
      change Except.error _ = Except.ok _ at typed
      cases typed
    | succ remaining =>
      cases remaining with
      | zero =>
        have typed := checked.typing
        rw [depth] at typed
        simp only [typeExpr, source.compatible.module, contextAt, calleeAt, parameters, typeArguments, bind, StateT.bind, Except.bind] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ checkFuel =>
        apply invokeCall_identity_fromArguments frame before ambient types live regions pending target origin context callee parameter descriptor
          argument integer callFuel world source contextAt calleeAt parameters declared descriptorType results body
        intro argumentFuel
        apply evalArguments_singleByValue_fromChecker frame before ambient types live regions pending target origin context callee parameter descriptor
          argument integer checkFuel argumentFuel world source contextAt calleeAt parameters mode declared descriptorType depth
          (.int integer) roots typingAfter rootsAfter checked
        intro argumentRoots argumentTypingAfter argumentRootsAfter operandSource operandChecked inner
        exact ih inner (ordinaryOperandFrame frame checkFuel) before ambient types live world operandSource argumentRoots
          argumentTypingAfter argumentRootsAfter operandChecked

#print axioms evalValue_nestedIdentity
end Goose.Proofs.ConstructionAcceptedExecution
