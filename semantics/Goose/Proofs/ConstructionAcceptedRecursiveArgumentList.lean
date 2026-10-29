import Goose.Proofs.ConstructionAcceptedRecursiveArgumentEvaluation
import Goose.Proofs.ConstructionAcceptedUnaryArgumentSource

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalArguments_recursiveArgument_fromChecker {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (expression : Expr) (integer : Goose.Core.IntTy) (checkFuel argumentFuel bound : Nat)
    (form : RecursiveArgumentExpression config integer frame.source.impl expression)
    (calls : RecursiveArgumentCallSafety config accepted integer bound) (fuelBound : argumentFuel ≤ bound)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (mode : parameter.mode = .byValue)
    (declared : callee.vars[parameter.var]? = some descriptor) (descriptorType : descriptor.ty = .int integer)
    (nesting : frame.typingFuel = checkFuel + 2)
    (resultTy : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.call target [.byVal expression] origin) resultTy roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalArguments argumentFuel config frame.interpretation.environment callee.vars [parameter] [.byVal expression] before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok values _ => nextAmbient = ambient ∧ ∃ value, values = [value] ∧ ValueRepresentation (.int integer) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  apply evalArguments_singleByValue_fromChecker_lowerFuel frame before ambient types live regions pending target origin context callee parameter
    descriptor expression integer checkFuel argumentFuel world source contextAt calleeAt parameters mode declared descriptorType nesting
    resultTy roots typingAfter rootsAfter checked
  intro argumentRoots argumentTypingAfter argumentRootsAfter operandSource operandChecked inner innerBound
  exact evalValue_recursiveArgument_fromCalls form inner bound accepted calls (by omega) (ordinaryOperandFrame frame checkFuel) before ambient
    types live regions pending rfl world operandSource argumentRoots argumentTypingAfter argumentRootsAfter operandChecked

#print axioms evalArguments_recursiveArgument_fromChecker
end Goose.Proofs.ConstructionAcceptedExecution
