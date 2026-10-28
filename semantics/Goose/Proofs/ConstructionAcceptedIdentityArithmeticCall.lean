import Goose.Proofs.ConstructionAcceptedIdentityUnaryCall
import Goose.Proofs.ConstructionAcceptedArithmeticArgument

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem invokeCall_identityArithmetic_allFuel {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (expression : Expr) (integer : Goose.Core.IntTy) (checkFuel fuel : Nat)
    (form : RegisterArithmeticExpression config integer expression) (graph : RegisterCallGraphWithCallLocals config (.int integer))
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (mode : parameter.mode = .byValue)
    (declared : callee.vars[parameter.var]? = some descriptor) (descriptorType : descriptor.ty = .int integer)
    (results : callee.results = #[⟨.int integer, .register, none⟩])
    (body : callee.body = ⟨callee.body.scope, [], some (.read (.var 0))⟩)
    (nesting : frame.typingFuel = checkFuel + 2)
    (resultTy : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.call target [.byVal expression] origin) resultTy roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config frame.interpretation.environment target [.byVal expression] [.register (.int integer)] origin before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation (.int integer) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  apply invokeCall_identity_fromArguments frame before ambient types live regions pending target origin context callee parameter descriptor
    expression integer fuel world source contextAt calleeAt parameters declared descriptorType results body
  intro argumentFuel
  exact evalArguments_registerArithmetic_fromChecker frame before ambient types live regions pending target origin context callee parameter
    descriptor expression integer checkFuel argumentFuel form graph world source contextAt calleeAt parameters mode declared descriptorType nesting
    resultTy roots typingAfter rootsAfter checked


theorem evalValue_identityArithmetic_allFuel {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (expression : Expr) (integer : Goose.Core.IntTy) (checkFuel fuel : Nat)
    (form : RegisterArithmeticExpression config integer expression) (graph : RegisterCallGraphWithCallLocals config (.int integer))
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (mode : parameter.mode = .byValue)
    (declared : callee.vars[parameter.var]? = some descriptor) (descriptorType : descriptor.ty = .int integer)
    (results : callee.results = #[⟨.int integer, .register, none⟩])
    (body : callee.body = ⟨callee.body.scope, [], some (.read (.var 0))⟩)
    (nesting : frame.typingFuel = checkFuel + 2)
    (resultTy : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.call target [.byVal expression] origin) resultTy roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalValue fuel config frame.interpretation.environment (.call target [.byVal expression] origin) before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation (.int integer) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  cases fuel with
  | zero =>
    simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source.futureGlobals, trivial⟩
  | succ fuel =>
    obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩ :=
      invokeCall_identityArithmetic_allFuel frame before ambient types live regions pending target origin context callee parameter descriptor
        expression integer checkFuel fuel form graph world source contextAt calleeAt parameters mode declared descriptorType results body nesting
        resultTy roots typingAfter rootsAfter checked
    exact evalValue_registerCall_withArguments_fromInvoke fuel config frame.initialized frame.interpretation.environment before ambient types regions pending
      target context callee [.byVal expression] (.int integer) origin contextAt calleeAt results
      ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩


#print axioms invokeCall_identityArithmetic_allFuel
#print axioms evalValue_identityArithmetic_allFuel
end Goose.Proofs.ConstructionAcceptedExecution
