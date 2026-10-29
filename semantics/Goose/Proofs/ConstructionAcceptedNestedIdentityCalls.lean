import Goose.Proofs.ConstructionAcceptedEarlierScalarComplete
import Goose.Proofs.ConstructionAcceptedSingleArgumentValue
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
    apply evalValue_singleArgument_fromOperand fuel frame before ambient types live regions pending target origin context callee parameter descriptor
      argument integer world source contextAt calleeAt parameters mode declared descriptorType results roots typingAfter rootsAfter checked
    · intro bodyFuel argumentState argumentTypes argumentLive argumentAmbient value represented argumentWorld argumentSource
      have parameterAt : callee.params[0]? = some parameter := by simp [parameters]
      have parameterId := validated_parameter_variable config.module context.impl callee 0 parameter accepted.accepted calleeAt parameterAt
      have declared0 : callee.vars[0]? = some descriptor := by simpa [parameterId] using declared
      have pointers : PointerTypedValue argumentTypes (.int integer) value := by
        cases represented with
        | integer _ number => exact .integer integer number
        | stored _ _ nonfixed _ => cases nonfixed
      exact identityParameterBody_partial bodyFuel config accepted frame argumentState argumentAmbient argumentTypes argumentLive regions pending
        target context callee parameter descriptor value (.int integer) contextAt calleeAt parameters declared0 body
        (Or.inl ⟨integer, descriptorType⟩) descriptorType represented pointers argumentWorld argumentSource
    · intro checkFuel argumentRoots argumentTypingAfter argumentRootsAfter depth operandSource operandChecked inner
      exact ih inner (ordinaryOperandFrame frame checkFuel) before ambient types live world operandSource argumentRoots
        argumentTypingAfter argumentRootsAfter operandChecked

#print axioms evalValue_nestedIdentity
end Goose.Proofs.ConstructionAcceptedExecution
