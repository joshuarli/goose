import Goose.Proofs.ConstructionAcceptedEarlierCallLocalGraph

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem invokeCall_recursive_register_earlier (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (ty : Ty) (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool) (graph : RegisterCallGraphWithLocals config ty) :
    ∀ (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (origin : Nat)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter),
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config caller.interpretation.environment target [] [.register ty] origin state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations state.nextAct state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  apply invokeCall_recursive_register_callLocal_earlier fuel config accepted ty scalar
  intro target context implementation contextAt implementationAt parameters results
  exact Or.inl (graph target context implementation contextAt implementationAt parameters results)

theorem invokeCall_recursive_register_earlier_frame (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (ty : Ty) (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool) (graph : RegisterCallGraphWithLocals config ty) :
    ∀ (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (origin : Nat)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter),
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config caller.interpretation.environment target [] [.register ty] origin state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted caller (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations state.nextAct state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  intro caller state ambient types live regions pending target context implementation origin world source contextAt implementationAt
    parameters results roots typingAfter rootsAfter checked
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld, clear, observations, result⟩ :=
    invokeCall_recursive_register_earlier fuel config accepted ty scalar graph caller state ambient types live regions pending target context
      implementation origin world source contextAt implementationAt parameters results roots typingAfter rootsAfter checked
  exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, finalWorld,
    source.afterEarlierObservations acts scopes observations, clear, observations, result⟩

#print axioms invokeCall_recursive_register_earlier_frame
#print axioms invokeCall_recursive_register_earlier
end Goose.Proofs.ConstructionAcceptedExecution
