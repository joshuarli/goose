import Goose.Proofs.ConstructionAcceptedInvocationValue
import Goose.Proofs.ConstructionAcceptedEarlierRecursiveCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalValue_recursive_register_earlier (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (ty : Ty) (origin : Nat)
    (graph : RegisterCallGraphWithLocals config ty)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := evalValue fuel config caller.interpretation.environment (.call target [] origin) state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted caller (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations state.nextAct state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok value _ => nextAmbient = ambient ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  apply evalValue_register_earlier_fromInvocation fuel config accepted caller state ambient types live regions pending
    target context implementation ty origin world source contextAt implementationAt results
  intro callFuel _
  exact invokeCall_recursive_register_earlier_frame callFuel config accepted ty scalarTy graph caller state ambient types live regions pending
    target context implementation origin world source contextAt implementationAt parameters results roots typingAfter rootsAfter checked

#print axioms evalValue_recursive_register_earlier
end Goose.Proofs.ConstructionAcceptedExecution
