import Goose.Proofs.ConstructionAcceptedCalleeBodySequence
import Goose.Proofs.ConstructionAcceptedCallLocalSequence
import Goose.Proofs.ConstructionAcceptedScalarPrefixCompose

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_callLocal_withPrefix (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (frontier scope id target callOrigin statementOrigin : Nat) (leading rest : List Stmt) (expression : Expr) (ty : Ty)
    (calleeContext : Context) (callee : Impl)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation context)
    (parameters : frame.source.impl.params = #[]) (scopes : frame.interpretation.environment.scopes = [])
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) (bodyFrame : implementationBodyFrame config frame = frame)
    (body : frame.source.impl.body = ⟨scope, leading ++ .letS id (.call target [] callOrigin) statementOrigin :: rest, some expression⟩)
    (frontierBound : frontier ≤ frame.interpretation.environment.act) (frontierClock : frontier ≤ state.nextAct)
    (channels : frame.interpretation.environment.channels = [.register ty])
    (position : SourcePosition accepted frame (.block ⟨scope, leading ++ .letS id (.call target [] callOrigin) statementOrigin :: rest, some expression⟩))
    (tailForm : AcceptedBinaryExpression expression) (leadingForm : ScalarLocalStatements leading) (restForm : ScalarLocalStatements rest)
    (leadingScalar : ∀ id expression origin, .letS id expression origin ∈ leading → ∀ descriptor,
      frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (localScalar : ∀ descriptor, frame.source.impl.vars[id]? = some descriptor →
      (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (restScalar : ∀ id expression origin, .letS id expression origin ∈ rest → ∀ descriptor,
      frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (bodyType : ∃ declared, typeBlock frame.typingFuel frame.typing
      ⟨scope, leading ++ .letS id (.call target [] callOrigin) statementOrigin :: rest, some expression⟩ frame.typingCounter = .ok ([ty], declared))
    (available : ∀ result after, rpBlockValue frame.source []
      ⟨scope, leading ++ .letS id (.call target [] callOrigin) statementOrigin :: rest, some expression⟩ frame.rootCursor =
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
        ⟨scope, leading ++ .letS id (.call target [] callOrigin) statementOrigin :: rest, some expression⟩ state
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
      frontier scope (leading ++ .letS id (.call target [] callOrigin) statementOrigin :: rest) expression ty world source phase parameters scopes
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
        let invariant : ConstructionSourceFrame → Prop := fun current =>
          current.source.impl = child.source.impl ∧ current.interpretation.environment = child.interpretation.environment ∧
            current.initialized = child.initialized
        have advance : ∀ current id fuel roots, invariant current →
            invariant { advanceLocalFrame { current with typingFuel := fuel } id with rootCursor := roots } := by
          intro current id fuel roots valid
          simpa [invariant, advanceLocalFrame] using valid
        have initialInvariant : invariant child := ⟨rfl, rfl, rfl⟩
        have childLeading : ∀ id expression origin, .letS id expression origin ∈ leading → ∀ descriptor,
            child.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
          intro id expression origin member descriptor declared
          apply leadingScalar id expression origin member descriptor
          simpa [childSource] using declared
        obtain ⟨next, nextTypes, nextLive, nextAmbient, initialized, extend, acts, scopeClocks, finalWorld, finalSource, observed, result⟩ :=
          execStmts_scalarPrefix_fromSuffix leadingForm (.letS id (.call target [] callOrigin) statementOrigin :: rest)
            config accepted context frontier n regions pending (fun current => current = ambient) invariant advance (by
              intro tailFuel tailBound tailFrame tailBefore tailAmbient tailTypes tailLive sameAmbient valid tailFrontier tailClock
                tailWorld tailSource tailPhase tailPosition tailAvailable
              subst tailAmbient
              have tailScopes : tailFrame.interpretation.environment.scopes = (scope, state.nextScope) :: [] := by
                rw [valid.2.1]
                exact childScopes
              have localTyped : ∀ descriptor, tailFrame.typing.variables[id]? = some descriptor →
                  (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
                intro descriptor declared
                apply localScalar descriptor
                rw [← tailSource.compatible.sourceVariables, valid.1, childSource] at declared
                exact declared
              have restTyped : ∀ id expression origin, .letS id expression origin ∈ rest → ∀ descriptor,
                  tailFrame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
                intro id expression origin member descriptor declared
                apply restScalar id expression origin member descriptor
                rw [valid.1, childSource] at declared
                exact declared
              cases tailFuel with
              | zero =>
                simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
                exact ⟨tailFrame, tailTypes, tailLive, ambient, rfl, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _,
                  tailWorld, tailSource, EarlierCallerObservations.refl frontier tailBefore tailTypes, trivial⟩
              | succ tailFuel =>
                have depth := tailPosition.zeroArgumentCallLocal_nesting tailFrame tailBefore tailTypes id target callOrigin statementOrigin rest
                  calleeContext callee ty tailSource contextAt calleeAt calleeParameters calleeResults scalar
                let checkFuel := tailFrame.typingFuel - 3
                have nesting : tailFrame.typingFuel = (checkFuel + 1) + 2 := by simp [checkFuel]; omega
                have headPosition := tailPosition.statements_head accepted tailFrame (.letS id (.call target [] callOrigin) statementOrigin) rest
                  (checkFuel + 2) (by omega)
                obtain ⟨_, _, allRoots, _, rootedAll⟩ := tailPosition.checked accepted tailFrame _
                obtain ⟨middleRoots, headRooted, tailRooted⟩ := rpStmts_cons rootedAll
                have headAvailable : ∀ after, rpStmt tailFrame.source (.letS id (.call target [] callOrigin) statementOrigin) tailFrame.rootCursor =
                    .ok ((), after) → GlobalEffectsAvailable tailFrame.interpretation tailFrame.initialized after.eff := by
                  intro after rooted
                  have same : after = middleRoots := (Prod.mk.inj (Except.ok.inj (rooted.symm.trans headRooted))).2
                  subst after
                  have included := rpStmts_effectTargetsIncluded tailRooted
                  intro target member global rooted
                  exact tailAvailable allRoots rootedAll target (included member) global rooted
                have headSource := tailSource.withTypingFuel (checkFuel + 2)
                obtain ⟨descriptor, roots, typingAfter, rootsAfter, declared, typingOrder, rootOrder, sameTy, initialSource, checked⟩ :=
                  checked_recursiveRegisterCall_initializer { tailFrame with typingFuel := checkFuel + 2 } tailBefore tailTypes id statementOrigin target callOrigin checkFuel
                    calleeContext callee ty headSource contextAt calleeAt calleeResults scalar localTyped rfl headPosition headAvailable
                exact execStmts_callLocal_scalarTail tailFuel checkFuel config accepted tailFrame tailBefore ambient tailTypes tailLive regions pending
                  id statementOrigin target callOrigin rest calleeContext callee ty scope state.nextScope [] tailWorld tailSource contextAt calleeAt
                  calleeParameters calleeResults scalar localTyped context tailPhase restForm restTyped nesting tailPosition tailAvailable tailScopes
                  frontier tailClock tailFrontier (by
                    intro evalFuel callFuel first second
                    have lower : callFuel < fuel := by omega
                    exact inner callFuel lower (letInitializerFrame { tailFrame with typingFuel := checkFuel + 2 } id (checkFuel + 1))
                      tailBefore tailTypes tailLive roots typingAfter rootsAfter tailWorld initialSource checked))
            n (Nat.le_refl n) child before ambient types live rfl initialInvariant childFrontier beforeClock seqWorld seqSource seqPhase
            seqPosition seqAvailable childLeading
        exact ⟨next, nextTypes, nextLive, nextAmbient, initialized, trivial, extend, acts, scopeClocks, finalWorld, finalSource, observed, result⟩)
  exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopeClocks, finalWorld, clear, observed, result⟩

#print axioms execActivationBody_callLocal_withPrefix
end Goose.Proofs.ConstructionAcceptedExecution
