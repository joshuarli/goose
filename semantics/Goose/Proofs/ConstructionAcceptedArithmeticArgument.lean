import Goose.Proofs.ConstructionAcceptedRecursiveRegisterArithmetic
import Goose.Proofs.ConstructionAcceptedUnaryCallArgument
import Goose.Proofs.ConstructionAcceptedUnaryArgumentSource

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalArguments_registerArithmetic {expression : Expr} (config : EvalConfig) (integer : Goose.Core.IntTy)
    (form : RegisterArithmeticExpression config integer expression) (fuel : Nat) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (parameterVars : Array LocalVar) (parameter : Param) (graph : RegisterCallGraphWithCallLocals config (.int integer))
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression (.int integer) roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalArguments fuel config frame.interpretation.environment parameterVars [parameter] [.byVal expression] before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok values _ => nextAmbient = ambient ∧ ∃ value, values = [value] ∧ ValueRepresentation (.int integer) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  exact evalArguments_singleByValue_earlier config (.int integer) fuel accepted frame before ambient types live regions pending
    parameterVars parameter world source (fun inner =>
      evalValue_registerArithmetic config integer form inner accepted frame before ambient types live regions pending graph
        world source roots typingAfter rootsAfter checked)

theorem evalArguments_registerArithmetic_fromChecker {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target callOrigin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (expression : Expr) (integer : Goose.Core.IntTy) (checkFuel fuel : Nat)
    (form : RegisterArithmeticExpression config integer expression) (graph : RegisterCallGraphWithCallLocals config (.int integer))
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (mode : parameter.mode = .byValue)
    (declared : callee.vars[parameter.var]? = some descriptor) (descriptorType : descriptor.ty = .int integer)
    (nesting : frame.typingFuel = checkFuel + 2)
    (resultTy : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.call target [.byVal expression] callOrigin) resultTy roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalArguments fuel config frame.interpretation.environment callee.vars [parameter] [.byVal expression] before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok values _ => nextAmbient = ambient ∧ ∃ value, values = [value] ∧ ValueRepresentation (.int integer) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  apply evalArguments_singleByValue_fromChecker frame before ambient types live regions pending target callOrigin context callee parameter
    descriptor expression integer checkFuel fuel world source contextAt calleeAt parameters mode declared descriptorType nesting
    resultTy roots typingAfter rootsAfter checked
  intro argumentRoots argumentTypingAfter argumentRootsAfter operandSource operandChecked inner
  exact evalValue_registerArithmetic config integer form inner accepted (ordinaryOperandFrame frame checkFuel) before ambient types live
    regions pending graph world operandSource argumentRoots argumentTypingAfter argumentRootsAfter operandChecked

#print axioms evalArguments_registerArithmetic_fromChecker
#print axioms evalArguments_registerArithmetic
end Goose.Proofs.ConstructionAcceptedExecution
