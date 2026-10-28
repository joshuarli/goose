import Goose.Proofs.ConstructionAcceptedArgumentPrefixPosition
import Goose.Proofs.ConstructionAcceptedUnaryCallArgument

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem checkedValue_singleByValue_argument {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (before : ExecutionState) (types : RootTypes)
    (target callOrigin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (expression : Expr) (integer : Goose.Core.IntTy) (checkFuel : Nat)
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (mode : parameter.mode = .byValue)
    (declared : callee.vars[parameter.var]? = some descriptor) (descriptorType : descriptor.ty = .int integer)
    (nesting : frame.typingFuel = checkFuel + 2)
    (position : SourcePosition accepted frame (.expression (.call target [.byVal expression] callOrigin)))
    (resultTy : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.call target [.byVal expression] callOrigin) resultTy roots typingAfter rootsAfter) :
    ∃ argumentRoots argumentTypingAfter argumentRootsAfter,
      AcceptedFrame config accepted (ordinaryOperandFrame frame checkFuel) before types ∧
      CheckedValue (ordinaryOperandFrame frame checkFuel) expression (.int integer) argumentRoots argumentTypingAfter argumentRootsAfter := by
  have argumentsPosition := position.call_arguments accepted frame target callOrigin (checkFuel + 1) context callee [.byVal expression]
    source.compatible contextAt calleeAt (by omega)
  have argumentsPosition' : SourcePosition accepted { frame with typingFuel := checkFuel + 1 }
      (.arguments callee [parameter] [.byVal expression]) := by simpa [parameters] using argumentsPosition
  obtain ⟨argumentTypingAfter, argumentRoots, argumentRootsAfter, argumentPosition, tailPosition, typed, rooted⟩ :=
    argumentsPosition'.arguments_byValue accepted { frame with typingFuel := checkFuel + 1 } callee parameter descriptor [] expression []
      checkFuel rfl mode declared (Or.inl ⟨integer, descriptorType⟩)
  have rooted' : rpExpr frame.source expression frame.rootCursor = .ok (argumentRoots, argumentRootsAfter) := by simpa using rooted
  obtain ⟨selected, selectedCallee, allRoots, argumentsAfter, selectedAt, selectedCalleeAt, argumentsRooted, contents⟩ :=
    rpExpr_call_argumentChecks checked.provenance
  have sourceContext : frame.source.mod.contexts[target]? = some context := by simpa [source.compatible.rootModule] using contextAt
  have sourceCallee : frame.source.mod.impls[context.impl]? = some callee := by simpa [source.compatible.rootModule] using calleeAt
  have selectedSame : selected = context := Option.some.inj (selectedAt.symm.trans sourceContext)
  subst selected
  have calleeSame : selectedCallee = callee := Option.some.inj (selectedCalleeAt.symm.trans sourceCallee)
  subst selectedCallee
  have argumentEffects := rpArgs_byVal_operandEffects rooted' argumentsRooted
  have callEffects := rpExpr_call_argumentEffects sourceContext sourceCallee parameters argumentsRooted checked.provenance
  have available : GlobalEffectsAvailable frame.interpretation frame.initialized argumentRootsAfter.eff := by
    intro effect member global interpreted
    exact checked.available effect (callEffects (argumentEffects member)) global interpreted
  refine ⟨argumentRoots, argumentTypingAfter, argumentRootsAfter, ordinaryOperandFrame_accepted accepted frame checkFuel before types source, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [ordinaryOperandFrame, descriptorType] using typed
  · simpa [ordinaryOperandFrame, StateT.run] using rooted'
  · simpa [ordinaryOperandFrame] using available


theorem evalArguments_unaryRegisterExpression_fromCall {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target callOrigin : Nat) (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (expression : Expr) (integer : Goose.Core.IntTy) (checkFuel fuel : Nat)
    (form : UnaryRegisterExpression config integer expression) (graph : RegisterCallGraphWithCallLocals config (.int integer))
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (mode : parameter.mode = .byValue)
    (declared : callee.vars[parameter.var]? = some descriptor) (descriptorType : descriptor.ty = .int integer)
    (nesting : frame.typingFuel = checkFuel + 2)
    (position : SourcePosition accepted frame (.expression (.call target [.byVal expression] callOrigin)))
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
  obtain ⟨argumentRoots, argumentTypingAfter, argumentRootsAfter, operandSource, operandChecked⟩ :=
    checkedValue_singleByValue_argument frame before types target callOrigin context callee parameter descriptor expression integer checkFuel
      source contextAt calleeAt parameters mode declared descriptorType nesting position resultTy roots typingAfter rootsAfter checked
  have operandWorld : AcceptedWorld config (ordinaryOperandFrame frame checkFuel).initialized before ambient types live regions pending := world
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalOperandSource, clear, observed, result⟩ :=
    evalArguments_unaryRegisterExpression config integer form fuel accepted (ordinaryOperandFrame frame checkFuel) before ambient types live
      regions pending callee.vars parameter graph operandWorld operandSource argumentRoots argumentTypingAfter argumentRootsAfter operandChecked
  have finalSource := source.afterEarlierObservations acts scopes observed
  exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, finalSource, clear, observed, result⟩

#print axioms evalArguments_unaryRegisterExpression_fromCall
#print axioms checkedValue_singleByValue_argument
end Goose.Proofs.ConstructionAcceptedExecution
