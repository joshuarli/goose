import Goose.Proofs.ConstructionAcceptedCalleeBodySequence
import Goose.Proofs.ConstructionAcceptedCallLocalStatements

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_callLocals (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (frontier scope : Nat) (statements : List Stmt) (expression : Expr) (ty : Ty)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation context)
    (parameters : frame.source.impl.params = #[]) (scopes : frame.interpretation.environment.scopes = [])
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) (bodyFrame : implementationBodyFrame config frame = frame)
    (body : frame.source.impl.body = ⟨scope, statements, some expression⟩)
    (frontierBound : frontier ≤ frame.interpretation.environment.act) (frontierClock : frontier ≤ state.nextAct)
    (channels : frame.interpretation.environment.channels = [.register ty])
    (position : SourcePosition accepted frame (.block ⟨scope, statements, some expression⟩))
    (form : CallLocalStatements config ty statements) (tailForm : AcceptedBinaryExpression expression)
    (scalarLocals : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
      frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (bodyType : ∃ declared, typeBlock frame.typingFuel frame.typing ⟨scope, statements, some expression⟩ frame.typingCounter = .ok ([ty], declared))
    (available : ∀ result after, rpBlockValue frame.source [] ⟨scope, statements, some expression⟩ frame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable frame.interpretation frame.initialized after.eff)
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (inner : ∀ callFuel, callFuel < fuel → ∀ (caller : ConstructionSourceFrame) (before : ExecutionState)
        (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
        (target : Nat) (calleeContext : Context) (callee : Impl) (origin : Nat)
        (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState),
      AcceptedWorld config caller.initialized before ambient types live regions pending →
      AcceptedFrame config accepted caller before types →
      config.module.contexts[target]? = some calleeContext → config.module.impls[calleeContext.impl]? = some callee →
      callee.params = #[] → callee.results = #[⟨ty, .register, none⟩] →
      CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter →
      ∃ nextTypes nextLive nextAmbient,
        let outcome := invokeCall callFuel config caller.interpretation.environment target [] [.register ty] origin before
        RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted caller (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
        FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations before.nextAct before (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := execActivationBody fuel config frame.interpretation.environment [] ⟨scope, statements, some expression⟩ state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations frontier state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  obtain ⟨nextTypes, nextLive, nextAmbient, _, extend, acts, scopeClocks, finalWorld, clear, observed, result⟩ :=
    execActivationBody_checkedSequence_earlier fuel config accepted frame context state ambient types live regions pending
      frontier scope statements expression ty world source phase parameters scopes cursor bodyFrame body frontierBound channels position
      tailForm bodyType available (fun _ => True) trivial (by
        intro n nBound child before seqWorld seqSource seqPhase seqPosition seqAvailable
        have bodyScope : frame.source.impl.body.scope = scope := by simp [body, Block.scope]
        have childSource : child.source = { frame.source with scopes := scope :: frame.source.scopes } := by
          simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame, bodyScope]
        have childInterpretation : child.interpretation = frame.interpretation.enterScope scope state.nextScope := by
          simp [child, entryStatementsFrame, bodyScope]
        have childScopes : child.interpretation.environment.scopes = (scope, state.nextScope) :: [] := by
          simp [childInterpretation, RootInterpretation.enterScope, scopes]
        have childFrontier : frontier ≤ child.interpretation.environment.act := by
          simpa [childInterpretation, RootInterpretation.enterScope] using frontierBound
        have beforeClock : frontier ≤ before.nextAct := by simpa [before, ownershipResultScopeState] using frontierClock
        have childScalar : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
            child.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
          intro id expression origin member descriptor declared
          apply scalarLocals id expression origin member descriptor
          simpa [childSource] using declared
        obtain ⟨next, nextTypes, nextLive, nextAmbient, initialized, extend, acts, scopeClocks,
          finalWorld, finalSource, observed, result⟩ :=
          execStmts_callLocals config ty form accepted context frontier fuel scope state.nextScope [] regions pending scalar inner
            n (by omega) child before ambient types live childFrontier beforeClock seqWorld seqSource seqPhase childScopes
            seqPosition seqAvailable childScalar
        exact ⟨next, nextTypes, nextLive, nextAmbient, initialized, trivial, extend, acts, scopeClocks, finalWorld, finalSource, observed, result⟩)
  exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopeClocks, finalWorld, clear, observed, result⟩

#print axioms execActivationBody_callLocals
end Goose.Proofs.ConstructionAcceptedExecution
