import Goose.Proofs.ConstructionAcceptedEarlierBinaryCompose
import Goose.Proofs.ConstructionAcceptedIdentityUnaryCall
import Goose.Proofs.ConstructionAcceptedUnaryArgumentSource
import Goose.Proofs.ConstructionAcceptedInvocationValue

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalValue_singleArgument_fromLowerFuel {config : EvalConfig} {accepted : AcceptedModule config}
    (fuel : Nat) (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (expression : Expr) (integer : Goose.Core.IntTy)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (mode : parameter.mode = .byValue)
    (declared : callee.vars[parameter.var]? = some descriptor) (descriptorType : descriptor.ty = .int integer)
    (results : callee.results = #[⟨.int integer, .register, none⟩])
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.call target [.byVal expression] origin) (.int integer) roots typingAfter rootsAfter)
    (bodySafe : ∀ bodyFuel, bodyFuel + 3 ≤ fuel → ∀ argumentState argumentTypes argumentLive argumentAmbient value,
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
    (operandSafe : ∀ checkFuel argumentRoots argumentTypingAfter argumentRootsAfter,
      frame.typingFuel = checkFuel + 2 →
      AcceptedFrame config accepted (ordinaryOperandFrame frame checkFuel) before types →
      CheckedValue (ordinaryOperandFrame frame checkFuel) expression (.int integer) argumentRoots argumentTypingAfter argumentRootsAfter →
      ∀ inner, inner + 3 ≤ fuel → EarlierScalarOutcome config accepted (ordinaryOperandFrame frame checkFuel) before ambient types regions pending (.int integer)
        (evalValue inner config (ordinaryOperandFrame frame checkFuel).interpretation.environment expression before)) :
    EarlierScalarOutcome config accepted frame before ambient types regions pending (.int integer)
      (evalValue fuel config frame.interpretation.environment (.call target [.byVal expression] origin) before) := by
  apply evalValue_registerArguments_earlier_fromInvocation fuel config accepted frame before ambient types live regions pending
    target [.byVal expression] context callee (.int integer) origin world source contextAt calleeAt results
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
      simp only [typeExpr, source.compatible.module, contextAt, calleeAt, typeArguments, bind, StateT.bind, Except.bind] at typed
      change Except.error _ = Except.ok _ at typed
      cases typed
    | succ checkFuel =>
      apply invokeCall_singleArgument_fromLowerFuel frame before ambient types live regions pending target origin context callee parameter
        expression integer callFuel world source contextAt calleeAt parameters results
      · intro bodyFuel bound
        exact bodySafe bodyFuel (by omega)
      · intro argumentFuel argumentBound
        apply evalArguments_singleByValue_fromChecker_lowerFuel frame before ambient types live regions pending target origin context callee parameter descriptor
          expression integer checkFuel argumentFuel world source contextAt calleeAt parameters mode declared descriptorType depth
          (.int integer) roots typingAfter rootsAfter checked
        intro argumentRoots argumentTypingAfter argumentRootsAfter operandSource operandChecked inner innerBound
        exact operandSafe checkFuel argumentRoots argumentTypingAfter argumentRootsAfter depth operandSource operandChecked inner (by omega)


theorem evalValue_singleArgument_fromOperand {config : EvalConfig} {accepted : AcceptedModule config}
    (fuel : Nat) (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (expression : Expr) (integer : Goose.Core.IntTy)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (mode : parameter.mode = .byValue)
    (declared : callee.vars[parameter.var]? = some descriptor) (descriptorType : descriptor.ty = .int integer)
    (results : callee.results = #[⟨.int integer, .register, none⟩])
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.call target [.byVal expression] origin) (.int integer) roots typingAfter rootsAfter)
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
    (operandSafe : ∀ checkFuel argumentRoots argumentTypingAfter argumentRootsAfter,
      frame.typingFuel = checkFuel + 2 →
      AcceptedFrame config accepted (ordinaryOperandFrame frame checkFuel) before types →
      CheckedValue (ordinaryOperandFrame frame checkFuel) expression (.int integer) argumentRoots argumentTypingAfter argumentRootsAfter →
      ∀ inner, EarlierScalarOutcome config accepted (ordinaryOperandFrame frame checkFuel) before ambient types regions pending (.int integer)
        (evalValue inner config (ordinaryOperandFrame frame checkFuel).interpretation.environment expression before)) :
    EarlierScalarOutcome config accepted frame before ambient types regions pending (.int integer)
      (evalValue fuel config frame.interpretation.environment (.call target [.byVal expression] origin) before) := by
  apply evalValue_singleArgument_fromLowerFuel fuel frame before ambient types live regions pending target origin context callee parameter descriptor
    expression integer world source contextAt calleeAt parameters mode declared descriptorType results roots typingAfter rootsAfter checked
  · intro bodyFuel bound
    exact bodySafe bodyFuel
  · intro checkFuel argumentRoots argumentTypingAfter argumentRootsAfter depth operandSource operandChecked inner bound
    exact operandSafe checkFuel argumentRoots argumentTypingAfter argumentRootsAfter depth operandSource operandChecked inner

#print axioms evalValue_singleArgument_fromLowerFuel
#print axioms evalValue_singleArgument_fromOperand
end Goose.Proofs.ConstructionAcceptedExecution
