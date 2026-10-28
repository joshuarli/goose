import Goose.Proofs.ConstructionAcceptedCalleeBodySequence
import Goose.Proofs.ConstructionAcceptedCallLocalSequence

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
  obtain ⟨nextTypes, nextLive, nextAmbient, _, extend, acts, scopeClocks, finalWorld, clear, observed, result⟩ :=
    execActivationBody_checkedSequence_earlier fuel config accepted frame context state ambient types live regions pending
      frontier scope (.letS id (.call target [] callOrigin) statementOrigin :: rest) expression ty world source phase parameters scopes
      cursor bodyFrame body frontierBound channels position tailForm bodyType available (fun _ => True) trivial (by
        intro n nBound child before seqWorld seqSource seqPhase seqPosition seqAvailable
        have depth : frame.typingFuel = 4096 := by
          have fixed := congrArg (fun f : ConstructionSourceFrame => f.typingFuel) bodyFrame
          simpa [implementationBodyFrame] using fixed.symm
        have bodyScope : frame.source.impl.body.scope = scope := by simp [body, Block.scope]
        have childFuel : child.typingFuel = 4095 := by
          have fixed := congrArg (fun f : ConstructionSourceFrame => f.typingFuel) bodyFrame
          simp only [implementationBodyFrame] at fixed
          simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame, ← fixed, depth]
        have childSource : child.source = { frame.source with scopes := scope :: frame.source.scopes } := by
          simp [child, entryStatementsFrame, blockStatementsFrame, bodyFrame, bodyScope]
        have childInterpretation : child.interpretation = frame.interpretation.enterScope scope state.nextScope := by
          simp [child, entryStatementsFrame, bodyScope]
        have childScopes : child.interpretation.environment.scopes = (scope, state.nextScope) :: [] := by
          simp [childInterpretation, RootInterpretation.enterScope, scopes]
        have childFrontier : frontier ≤ child.interpretation.environment.act := by
          simpa [childInterpretation, RootInterpretation.enterScope] using frontierBound
        have beforeClock : frontier ≤ before.nextAct := by simpa [before, ownershipResultScopeState] using frontierClock
        have localTyped : ∀ descriptor, child.typing.variables[id]? = some descriptor →
            (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
          intro descriptor declared
          apply localScalar descriptor
          rw [← seqSource.compatible.sourceVariables, childSource] at declared
          exact declared
        have restTyped : ∀ id expression origin, .letS id expression origin ∈ rest → ∀ descriptor,
            child.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
          intro id expression origin member descriptor declared
          apply restScalar id expression origin member descriptor
          simpa [childSource] using declared
        cases n with
        | zero =>
          simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
          exact ⟨child, types, live, ambient, rfl, trivial, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _,
            seqWorld, seqSource, EarlierCallerObservations.refl frontier before types, trivial⟩
        | succ n =>
          have headPosition := seqPosition.statements_head accepted child (.letS id (.call target [] callOrigin) statementOrigin) rest 4094
            (by omega)
          obtain ⟨_, _, allRoots, _, rootedAll⟩ := seqPosition.checked accepted child _
          obtain ⟨middleRoots, headRooted, tailRooted⟩ := rpStmts_cons rootedAll
          have headAvailable : ∀ after, rpStmt child.source (.letS id (.call target [] callOrigin) statementOrigin) child.rootCursor =
              .ok ((), after) → GlobalEffectsAvailable child.interpretation child.initialized after.eff := by
            intro after rooted
            have same : after = middleRoots := (Prod.mk.inj (Except.ok.inj (rooted.symm.trans headRooted))).2
            subst after
            have included := rpStmts_effectTargetsIncluded tailRooted
            intro target member global rooted
            exact seqAvailable allRoots rootedAll target (included member) global rooted
          have headSource := seqSource.withTypingFuel 4094
          obtain ⟨descriptor, roots, typingAfter, rootsAfter, declared, typingOrder, rootOrder, sameTy, initialSource, checked⟩ :=
            checked_recursiveRegisterCall_initializer { child with typingFuel := 4094 } before types id statementOrigin target callOrigin 4092
              calleeContext callee ty headSource contextAt calleeAt calleeResults scalar localTyped rfl headPosition headAvailable
          have outcome := execStmts_callLocal_scalarTail n 4092 config accepted child before ambient types live regions pending
            id statementOrigin target callOrigin rest calleeContext callee ty scope state.nextScope [] seqWorld seqSource contextAt calleeAt
            calleeParameters calleeResults scalar localTyped context seqPhase restForm restTyped (by omega) seqPosition seqAvailable childScopes
            frontier beforeClock childFrontier (by
              intro evalFuel callFuel first second
              have lower : callFuel < fuel := by omega
              exact inner callFuel lower (letInitializerFrame { child with typingFuel := 4094 } id 4093)
                before types live roots typingAfter rootsAfter seqWorld initialSource checked)
          obtain ⟨next, nextTypes, nextLive, nextAmbient, initialized, extend, acts, scopeClocks, world, source, observed, result⟩ := outcome
          exact ⟨next, nextTypes, nextLive, nextAmbient, initialized, trivial, extend, acts, scopeClocks, world, source, observed, result⟩)
  exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopeClocks, finalWorld, clear, observed, result⟩

#print axioms execActivationBody_callLocal_scalarTail
end Goose.Proofs.ConstructionAcceptedExecution
