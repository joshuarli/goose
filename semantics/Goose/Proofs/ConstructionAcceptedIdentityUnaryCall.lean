import Goose.Proofs.ConstructionAcceptedParameterIdentityWorld
import Goose.Proofs.ConstructionAcceptedSingleArgumentCompose
import Goose.Proofs.ConstructionAcceptedUnaryArgumentSource
import Goose.Proofs.ConstructionAcceptedRecursiveLocalCallEvaluation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem invokeCall_singleArgument_fromArguments {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param)
    (expression : Expr) (integer : Goose.Core.IntTy) (fuel : Nat)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (results : callee.results = #[⟨.int integer, .register, none⟩])
    (bodySafe : ∀ bodyFuel argumentState argumentTypes argumentLive argumentAmbient value,
      ValueRepresentation (.int integer) value →
      AcceptedWorld config frame.initialized argumentState argumentAmbient argumentTypes argumentLive regions pending →
      AcceptedFrame config accepted frame argumentState argumentTypes →
      let activation : RuntimeActivation := ⟨context.impl, argumentState.nextAct, callee.vars, [], [.register (.int integer)]⟩
      let pushed := { argumentState with nextAct := argumentState.nextAct + 1, activations := activation :: argumentState.activations }
      ∃ nextTypes nextLive nextAmbient,
        let outcome := execActivationBody bodyFuel config activation [(parameter.var, value)] callee.body pushed
        RootTypesExtend argumentTypes nextTypes ∧ pushed.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        pushed.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations argumentState.nextAct pushed (Goose.Proofs.Exit.stepState outcome) argumentTypes nextTypes ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = .callChannels activation [] :: argumentAmbient ∧
             ∃ result, carriers = [.register result] ∧ ValueRepresentation (.int integer) result
         | .stop .. => True | .escape .. | .jump .. => False))
    (argumentsSafe : ∀ argumentFuel, ∃ nextTypes nextLive nextAmbient,
      let outcome := evalArguments argumentFuel config frame.interpretation.environment callee.vars [parameter] [.byVal expression] before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok values _ => nextAmbient = ambient ∧ ∃ value, values = [value] ∧ ValueRepresentation (.int integer) value
       | .stop .. => True | .escape .. | .jump .. => False)) :
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
  cases fuel with
  | zero =>
    simp only [invokeCall, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source,
      source.futureGlobals, EarlierCallerObservations.refl _ _ _, trivial⟩
  | succ fuel =>
    obtain ⟨middleTypes, middleLive, middleAmbient, extension, acts, scopes, middleWorld, middleSource, clear, observed, result⟩ :=
      argumentsSafe fuel
    cases evaluated : evalArguments fuel config frame.interpretation.environment callee.vars [parameter] [.byVal expression] before with
    | stop reason after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at acts scopes middleWorld middleSource clear observed result
      rw [invokeCall_singleArgument_register_stopped fuel config _ target context callee parameter (.byVal expression) (.int integer) origin
        before after reason contextAt calleeAt parameters results evaluated]
      exact ⟨middleTypes, middleLive, middleAmbient, extension, acts, scopes, middleWorld, middleSource, clear, observed, trivial⟩
    | escape target carriers after | jump target kind after => simp [evaluated] at result
    | ok values after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at acts scopes middleWorld middleSource clear observed result
      obtain ⟨rfl, value, rfl, representation⟩ := result
      cases fuel with
      | zero => simp [evalArguments, timeout, EvalM.stop] at evaluated
      | succ fuel =>
        have bodyOutcome := bodySafe fuel after middleTypes middleLive middleAmbient value representation middleWorld middleSource
        obtain ⟨finalTypes, finalLive, finalAmbient, extension2, acts2, scopes2, finalWorld, finalClear, observed2, finalResult⟩ :=
          invokeCall_singleArgument_register_compose fuel config frame.initialized frame.interpretation.environment before after middleAmbient middleTypes
            middleLive regions pending after.nextAct target context callee parameter (.byVal expression) value (.int integer) origin
            middleWorld clear contextAt calleeAt parameters results evaluated bodyOutcome
        have finalObserved := observed.trans acts observed2
        have finalActs := Nat.le_trans acts acts2
        have finalScopes := Nat.le_trans scopes scopes2
        exact ⟨finalTypes, finalLive, finalAmbient, (fun root ty found => extension2 root ty (extension root ty found)),
          finalActs, finalScopes, finalWorld, source.afterEarlierObservations finalActs finalScopes finalObserved, finalClear,
          finalObserved, finalResult⟩



theorem invokeCall_identity_fromArguments {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (expression : Expr) (integer : Goose.Core.IntTy) (fuel : Nat)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (declared : callee.vars[parameter.var]? = some descriptor)
    (descriptorType : descriptor.ty = .int integer) (results : callee.results = #[⟨.int integer, .register, none⟩])
    (body : callee.body = ⟨callee.body.scope, [], some (.read (.var 0))⟩)
    (argumentsSafe : ∀ argumentFuel, ∃ nextTypes nextLive nextAmbient,
      let outcome := evalArguments argumentFuel config frame.interpretation.environment callee.vars [parameter] [.byVal expression] before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok values _ => nextAmbient = ambient ∧ ∃ value, values = [value] ∧ ValueRepresentation (.int integer) value
       | .stop .. => True | .escape .. | .jump .. => False)) :
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
  apply invokeCall_singleArgument_fromArguments frame before ambient types live regions pending target origin context callee parameter
    expression integer fuel world source contextAt calleeAt parameters results
  · intro bodyFuel argumentState argumentTypes argumentLive argumentAmbient value represented argumentWorld argumentSource
    have parameterAt : callee.params[0]? = some parameter := by simp [parameters]
    have parameterId := validated_parameter_variable config.module context.impl callee 0 parameter accepted.accepted calleeAt parameterAt
    have declared0 : callee.vars[0]? = some descriptor := by simpa [parameterId] using declared
    have pointers : PointerTypedValue argumentTypes (.int integer) value := by
      cases represented with
      | integer _ number => exact .integer integer number
      | stored _ _ nonfixed _ => cases nonfixed
    exact identityParameterBody_partial bodyFuel config accepted frame argumentState argumentAmbient argumentTypes argumentLive regions pending target context
      callee parameter descriptor value (.int integer) contextAt calleeAt parameters declared0 body (Or.inl ⟨integer, descriptorType⟩)
      descriptorType represented pointers argumentWorld argumentSource
  · exact argumentsSafe

theorem invokeCall_identityUnary_allFuel {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (expression : Expr) (integer : Goose.Core.IntTy) (checkFuel fuel : Nat)
    (form : UnaryRegisterExpression config integer expression) (graph : RegisterCallGraphWithCallLocals config (.int integer))
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
  exact evalArguments_unaryRegisterExpression_fromChecker frame before ambient types live regions pending target origin context callee parameter
    descriptor expression integer checkFuel argumentFuel form graph world source contextAt calleeAt parameters mode declared descriptorType nesting
    resultTy roots typingAfter rootsAfter checked

theorem evalValue_identityUnary_allFuel {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (expression : Expr) (integer : Goose.Core.IntTy) (checkFuel fuel : Nat)
    (form : UnaryRegisterExpression config integer expression) (graph : RegisterCallGraphWithCallLocals config (.int integer))
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
      invokeCall_identityUnary_allFuel frame before ambient types live regions pending target origin context callee parameter descriptor
        expression integer checkFuel fuel form graph world source contextAt calleeAt parameters mode declared descriptorType results body nesting
        resultTy roots typingAfter rootsAfter checked
    exact evalValue_registerCall_withArguments_fromInvoke fuel config frame.initialized frame.interpretation.environment before ambient types regions pending
      target context callee [.byVal expression] (.int integer) origin contextAt calleeAt results
      ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, result⟩

#print axioms evalValue_identityUnary_allFuel
#print axioms invokeCall_singleArgument_fromArguments
#print axioms invokeCall_identity_fromArguments
#print axioms invokeCall_identityUnary_allFuel
end Goose.Proofs.ConstructionAcceptedExecution
