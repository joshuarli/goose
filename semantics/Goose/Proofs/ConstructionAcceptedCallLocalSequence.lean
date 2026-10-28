import Goose.Proofs.ConstructionAcceptedCallLocalSuffix

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem execStmts_callLocal_scalarTail (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (id statementOrigin target callOrigin : Nat) (rest : List Stmt) (context : Context) (callee : Impl) (ty : Ty) (scope scopeInst : Nat)
    (outerScopes : List (Nat × Nat))
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (results : callee.results = #[⟨ty, .register, none⟩])
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (localScalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (contextId : Nat) (phase : frame.phase = .implementation contextId)
    (tailForm : ScalarLocalStatements rest)
    (tailScalar : ∀ localId expression origin, .letS localId expression origin ∈ rest → ∀ descriptor,
      frame.source.impl.vars[localId]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (nesting : frame.typingFuel = (checkFuel + 1) + 2)
    (position : SourcePosition accepted frame (.statements (.letS id (.call target [] callOrigin) statementOrigin :: rest)))
    (available : ∀ rootsAfter, rpStmts frame.source (.letS id (.call target [] callOrigin) statementOrigin :: rest) frame.rootCursor =
      .ok ((), rootsAfter) → GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff)
    (scopes : frame.interpretation.environment.scopes = (scope, scopeInst) :: outerScopes)
    (frontier : Nat) (frontierClock : frontier ≤ state.nextAct)
    (frontierAct : frontier ≤ frame.interpretation.environment.act)
    (invoked : ∀ evalFuel callFuel, fuel = evalFuel + 1 → evalFuel = callFuel + 1 →
      ∃ nextTypes nextLive nextAmbient,
        let outcome := invokeCall callFuel config frame.interpretation.environment target [] [.register ty] callOrigin state
        RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted (letInitializerFrame frame id (checkFuel + 1)) (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
        FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations state.nextAct state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
        (match outcome with
         | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ (next : ConstructionSourceFrame) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (nextAmbient : OwnershipAmbient),
      let outcome := execStmts (fuel + 1) config frame.interpretation.environment
        (.letS id (.call target [] callOrigin) statementOrigin :: rest) state
      let after := Goose.Proofs.Exit.stepState outcome
      next.initialized = frame.initialized ∧ RootTypesExtend types nextTypes ∧ state.nextAct ≤ after.nextAct ∧
      state.nextScope ≤ after.nextScope ∧ AcceptedWorld config next.initialized after nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted next after nextTypes ∧ EarlierCallerObservations frontier state after types nextTypes ∧
      (match outcome with
       | .ok flow _ => nextAmbient = ambient ∧ flow = .normal .unit ∧ SourcePosition accepted next (.statements []) ∧
           ScalarLocalReplay frame next (.letS id (.call target [] callOrigin) statementOrigin :: rest)
       | .stop .. => True | .escape .. | .jump .. => False) := by
  apply execStmts_callLocal_fromSuffix fuel checkFuel config accepted frame state ambient types live regions pending
    id statementOrigin target callOrigin rest context callee ty scope scopeInst outerScopes world source contextAt calleeAt parameters results
    scalarTy localScalar nesting position available scopes frontier frontierClock frontierAct invoked
  intro rootsAfter middle nextTypes nextLive nextFrame middleWorld middleSource middlePosition remainingAvailable
  have remainingScalar : ∀ id expression origin, .letS id expression origin ∈ rest →
      ∀ descriptor, nextFrame.source.impl.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
    intro id expression origin member descriptor found
    apply tailScalar id expression origin member descriptor
    simpa [nextFrame, advanceLocalFrame] using found
  obtain ⟨finalFrame, finalTypes, finalLive, initializedEq, finalExtended, finalActs, finalScopes,
    finalWorld, finalSource, finalObserved, finalFlow⟩ :=
    execStmts_scalarLocal_prefix_observed tailForm frontier fuel config accepted nextFrame contextId middle ambient nextTypes nextLive regions pending
      (by simpa [nextFrame, advanceLocalFrame] using frontierAct) middleWorld middleSource
      (by simpa [nextFrame, advanceLocalFrame] using phase) middlePosition remainingAvailable remainingScalar
  refine ⟨finalFrame, finalTypes, finalLive, ambient, initializedEq, finalExtended, Nat.le_of_eq finalActs.symm,
    Nat.le_of_eq finalScopes.symm, finalWorld, finalSource, finalObserved, ?_⟩
  cases run : execStmts fuel config nextFrame.interpretation.environment rest middle with
  | ok flow after => simp only [run] at finalFlow ⊢; exact ⟨trivial, finalFlow⟩
  | stop reason after => simp only [run] at finalFlow ⊢
  | escape address carriers after | jump target kind after => simp only [run] at finalFlow

#print axioms execStmts_callLocal_scalarTail
end Goose.Proofs.ConstructionAcceptedExecution
