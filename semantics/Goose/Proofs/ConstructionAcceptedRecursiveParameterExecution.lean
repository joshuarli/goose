import Goose.Proofs.ConstructionAcceptedRecursiveParameterPrefixExecution
import Goose.Proofs.ConstructionAcceptedRecursiveParameterGraph
import Goose.Proofs.ConstructionAcceptedRecursiveArgumentList
import Goose.Proofs.ConstructionAcceptedParameterizedRecursiveGraph

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem invokeCall_recursiveParameterGraph_allFuel (fuel : Nat) (config : EvalConfig) (integer : Goose.Core.IntTy)
    (accepted : AcceptedModule config) (graph : RecursiveParameterGraph config integer)
    :
    ∀ (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (implementation : Impl) (parameter : Param) (argument : Expr)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (mode : parameter.mode = .byValue)
    (results : implementation.results = #[⟨.int integer, .register, none⟩])
    (form : RecursiveArgumentExpression config integer caller.source.impl argument) (checkFuel : Nat) (nesting : caller.typingFuel = checkFuel + 2)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [.byVal argument] origin) (.int integer) roots typingAfter rootsAfter),
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config caller.interpretation.environment target [.byVal argument] [.register (.int integer)] origin state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted caller (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations state.nextAct state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation (.int integer) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  apply invokeCall_recursiveParameterPrefixGraph_allFuel fuel config integer accepted
  intro target context implementation parameter contextAt implementationAt parameters mode results
  rcases graph target context implementation parameter contextAt implementationAt parameters mode results with identity | scalarTail | tail
  · exact Or.inl identity
  · exact Or.inr (Or.inl scalarTail)
  · obtain ⟨descriptor, summary, tailTarget, tailOrigin, tailContext, tailCallee, tailParameter, tailDescriptor, tailSummary, argument,
      declared, descriptorTy, known, body, tailContextAt, tailCalleeAt, tailParameters, tailMode, tailDeclared, tailDescriptorTy,
      tailResults, tailKnown, form⟩ := tail
    exact Or.inr (Or.inr ⟨descriptor, summary, tailTarget, tailOrigin, tailContext, tailCallee, tailParameter, tailDescriptor,
      tailSummary, argument, [], declared, descriptorTy, known, body, tailContextAt, tailCalleeAt, tailParameters, tailMode,
      tailDeclared, tailDescriptorTy, tailResults, tailKnown, form, .nil, by simp⟩)

#print axioms invokeCall_recursiveParameterGraph_allFuel
end Goose.Proofs.ConstructionAcceptedExecution
