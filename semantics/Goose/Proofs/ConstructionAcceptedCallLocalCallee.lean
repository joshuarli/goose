import Goose.Proofs.ConstructionAcceptedPrefixedCallLocalCallee

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_callLocal_scalarTail (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (frontier scope id target callOrigin statementOrigin : Nat) (rest : List Stmt) (expression : Expr) (ty : Ty)
    (calleeContext : Context) (callee : Impl)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation context)
    (parameters : frame.source.impl.params = #[]) (scopes : frame.interpretation.environment.scopes = [])
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) (bodyFrame : implementationBodyFrame config frame = frame)
    (body : frame.source.impl.body = ⟨scope, .letS id (.call target [] callOrigin) statementOrigin :: rest, some expression⟩)
    (frontierBound : frontier ≤ frame.interpretation.environment.act) (frontierClock : frontier ≤ state.nextAct)
    (channels : frame.interpretation.environment.channels = [.register ty])
    (position : SourcePosition accepted frame (.block ⟨scope, .letS id (.call target [] callOrigin) statementOrigin :: rest, some expression⟩))
    (tailForm : AcceptedBinaryExpression expression) (restForm : ScalarLocalStatements rest)
    (localScalar : ∀ descriptor, frame.source.impl.vars[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (restScalar : ∀ id expression origin, .letS id expression origin ∈ rest → ∀ descriptor,
      frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (bodyType : ∃ declared, typeBlock frame.typingFuel frame.typing
      ⟨scope, .letS id (.call target [] callOrigin) statementOrigin :: rest, some expression⟩ frame.typingCounter = .ok ([ty], declared))
    (available : ∀ result after, rpBlockValue frame.source []
      ⟨scope, .letS id (.call target [] callOrigin) statementOrigin :: rest, some expression⟩ frame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable frame.interpretation frame.initialized after.eff)
    (contextAt : config.module.contexts[target]? = some calleeContext)
    (calleeAt : config.module.impls[calleeContext.impl]? = some callee)
    (calleeParameters : callee.params = #[]) (calleeResults : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (inner : ∀ callFuel, callFuel < fuel → ∀ (caller : ConstructionSourceFrame) (before : ExecutionState)
        (currentTypes : RootTypes) (currentLive : Goose.Core.RootInst → Prop)
        (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState),
      AcceptedWorld config caller.initialized before ambient currentTypes currentLive regions pending →
      AcceptedFrame config accepted caller before currentTypes →
      CheckedValue caller (.call target [] callOrigin) ty roots typingAfter rootsAfter →
      ∃ nextTypes nextLive nextAmbient,
        let outcome := invokeCall callFuel config caller.interpretation.environment target [] [.register ty] callOrigin before
        RootTypesExtend currentTypes nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted caller (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
        FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) currentTypes nextTypes ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := execActivationBody fuel config frame.interpretation.environment []
        ⟨scope, .letS id (.call target [] callOrigin) statementOrigin :: rest, some expression⟩ state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations frontier state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  exact execActivationBody_callLocal_withPrefix fuel config accepted frame context state ambient types live regions pending
    frontier scope id target callOrigin statementOrigin [] rest expression ty calleeContext callee world source phase parameters scopes
    cursor bodyFrame body frontierBound frontierClock channels position tailForm .nil restForm
    (by intro id expression origin member; cases member) localScalar restScalar bodyType available contextAt calleeAt calleeParameters
    calleeResults scalar inner

#print axioms execActivationBody_callLocal_scalarTail
end Goose.Proofs.ConstructionAcceptedExecution
