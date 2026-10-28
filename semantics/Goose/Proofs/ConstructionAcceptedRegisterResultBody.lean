import Goose.Proofs.ConstructionMixedLocalTailPosition
import Goose.Proofs.ConstructionMixedLocalProtectedTypes
import Goose.Proofs.ConstructionAcceptedRegisterScopeExit
import Goose.Proofs.ConstructionAcceptedRegisterResultTyping
import Goose.Proofs.ConstructionAcceptedScalarResultProduce
import Goose.Proofs.ConstructionAcceptedScopeObservation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem mixedLocal_registerResultBody_observedWorld (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (pre : List (Nat × Value))
    (before boundState : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (context : Context) (helper : Impl) (ty : Ty) (expression : Expr)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (helperEq : frame.source.impl = helper) (phase : frame.phase = .implementation contextId)
    (environment : frame.interpretation.environment = activation) (channels : activation.channels = [.register ty])
    (results : helper.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (tail : helper.body.value = some expression) (shape : AcceptedBinaryExpression expression)
    (initialized : frame.initialized = config.module.globals.size)
    (bound : bindAll activation.act before.nextScope pre
      (ownershipResultScopeState activation helper.body.scope before) = .ok () boundState)
    (world : AcceptedWorld config config.module.globals.size boundState (.callChannels activation [] :: ambient) types live regions pending)
    (source : AcceptedFrame config accepted (entryStatementsFrame config frame before.nextScope) boundState types)
    (position : SourcePosition accepted (entryStatementsFrame config frame before.nextScope) (.statements helper.body.stmts))
    (form : MixedLocalStatements helper.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ helper.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, helper.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
    match execActivationBody (fuel + 1) config activation pre helper.body before with
    | .stop _ after => ∃ nextTypes nextLive nextRegions, RootTypesExtend types nextTypes ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local activation.act scope id) → nextTypes root = types root) ∧
        AcceptedWorld config config.module.globals.size after (.callChannels activation [] :: ambient) nextTypes nextLive nextRegions pending
    | .ok carriers after => ∃ value nextTypes nextLive nextRegions, carriers = [.register value] ∧
        ValueRepresentation ty value ∧ RootTypesExtend types nextTypes ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local activation.act scope id) → nextTypes root = types root) ∧
        AcceptedWorld config config.module.globals.size after (.callChannels activation [] :: ambient) nextTypes nextLive nextRegions pending ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local activation.act scope id) →
          after.objects.lookup root = boundState.objects.lookup root ∧
          after.objectOrdinals.lookup root = boundState.objectOrdinals.lookup root)
    | _ => False := by
  let entryFrame := entryStatementsFrame config frame before.nextScope
  have fullInitialized : entryFrame.initialized = config.module.globals.size := by
    simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using initialized
  have frameWorld : AcceptedWorld config entryFrame.initialized boundState (.callChannels activation [] :: ambient) types live regions pending :=
    fullInitialized.symm ▸ world
  have limit : entryFrame.typing.globalLimit ≤ config.module.globals.size := by
    simp [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]
  have initialBound : GlobalEffectTargetsBounded entryFrame.rootCursor.eff config.module.globals.size := by
    simp [GlobalEffectTargetsBounded, Eff.accessTargets, entryFrame, entryStatementsFrame,
      blockStatementsFrame, implementationBodyFrame]
  have entryPhase : entryFrame.phase = .implementation contextId := by
    simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using phase
  have owners' : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (entryFrame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)) := by
    intro declaration member
    simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, helperEq] using owners declaration member
  have scalarOwners' : ∀ id expression origin, .letS id expression origin ∈ helper.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, entryFrame.source.impl.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
    intro id expression origin member expressionForm descriptor declared
    apply scalarOwners id expression origin member expressionForm descriptor
    simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, helperEq] using declared
  have unnamed : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (entryFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none := by
    intro declaration member
    simp [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, helperEq, results]
  obtain ⟨next, nextTypes, nextLive, nextRegions, nextInitialized, extended, finalWorld, finalSource, finalFlow,
      sourceEq, interpretationEq, phaseEq, limitEq, finalBounded, finalProtected, finalObserved, finalReplay⟩ :=
    execStmts_mixedLocal_observed_world form fuel config accepted entryFrame contextId boundState
      (.callChannels activation [] :: ambient) types live regions pending frameWorld source entryPhase position
      fullInitialized limit initialBound owners' scalarOwners' unnamed
  change (match execStmts fuel config entryFrame.interpretation.environment helper.body.stmts boundState with
    | .ok result _ => result = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) at finalFlow
  change AcceptedWorld config next.initialized
    (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment helper.body.stmts boundState))
    (.callChannels activation [] :: ambient) nextTypes nextLive nextRegions pending at finalWorld
  change AcceptedFrame config accepted next
    (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment helper.body.stmts boundState)) nextTypes at finalSource
  change (match execStmts fuel config entryFrame.interpretation.environment helper.body.stmts boundState with
    | .ok _ _ => typeStatements entryFrame.typingFuel entryFrame.typing helper.body.stmts entryFrame.typingCounter =
        .ok (next.typing, next.typingCounter) ∧ rpStmts entryFrame.source helper.body.stmts entryFrame.rootCursor =
          .ok ((), next.rootCursor)
    | _ => True) at finalReplay
  have nextFull : next.initialized = config.module.globals.size := nextInitialized.trans fullInitialized
  have unaffected : ∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local activation.act scope id) → nextTypes root = types root := by
    simpa [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environment] using finalProtected
  cases outcome : execStmts fuel config entryFrame.interpretation.environment helper.body.stmts boundState with
  | escape address carriers after | jump target kind after => simp only [outcome] at finalFlow
  | stop reason after =>
    simp only [outcome, Goose.Proofs.Exit.stepState] at finalWorld
    have stopped : execStmts fuel config
        { activation with scopes := (helper.body.scope, before.nextScope) :: activation.scopes }
        helper.body.stmts boundState = .stop reason after := by
      simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environment, helperEq] using outcome
    have actual := execActivationBody_bound_stopped fuel config activation pre helper.body before boundState after reason bound stopped
    rw [actual]
    exact ⟨nextTypes, nextLive, nextRegions, extended, unaffected, nextFull ▸ finalWorld⟩
  | ok flow middle =>
    simp only [outcome] at finalFlow
    subst flow
    cases fuel with
    | zero => simp [execStmts, timeout, EvalM.stop] at outcome
    | succ fuel =>
      simp only [outcome, Goose.Proofs.Exit.stepState] at finalWorld finalSource finalObserved finalReplay
      let blockFrame := implementationBodyFrame config entryFrame
      have blockPosition : SourcePosition accepted blockFrame (.block blockFrame.source.impl.body) :=
        .implementationBody entryFrame contextId entryPhase source.compatible
      have helperBody : helper.body = ⟨helper.body.scope, helper.body.stmts, some expression⟩ := by
        cases body : helper.body with
        | mk scope statements value => simp only [body, Block.value] at tail; subst value; rfl
      have blockBody : blockFrame.source.impl.body = ⟨helper.body.scope, helper.body.stmts, some expression⟩ := by
        simpa only [blockFrame, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, helperEq] using helperBody
      rw [blockBody] at blockPosition
      obtain ⟨declared, bodyTyped⟩ := validated_scalarRegister_body_typing config.module context.impl helper
        accepted.accepted helperAt ty results scalar (by simp [tail])
      have blockTyped : typeBlock blockFrame.typingFuel blockFrame.typing ⟨helper.body.scope, helper.body.stmts, some expression⟩
          blockFrame.typingCounter = .ok ([ty], declared) := by
        simpa only [blockFrame, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, helperEq, ← helperBody] using bodyTyped
      obtain ⟨blockNext, blockCounter, rootMiddle, bodyTypes, bodyCounter, tailRoots, tailRootsAfter,
        checkedBlock, typedStatements, rootedStatements, tailTyped, tailRooted⟩ :=
        blockPosition.blockTail_checks accepted blockFrame helper.body.scope 4095 helper.body.stmts expression rfl
      have sameTypes : bodyTypes = [ty] := (Prod.mk.inj (Except.ok.inj (checkedBlock.symm.trans blockTyped))).1
      subst bodyTypes
      have sameTyping : (blockNext, blockCounter) = (next.typing, next.typingCounter) := by
        apply Except.ok.inj
        exact typedStatements.symm.trans (by simpa only [blockFrame, entryFrame, entryStatementsFrame,
          blockStatementsFrame, implementationBodyFrame, helperEq] using finalReplay.1)
      have sameRoot : rootMiddle = next.rootCursor := (Prod.mk.inj (Except.ok.inj (rootedStatements.symm.trans
        (by simpa only [blockFrame, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, helperEq] using finalReplay.2)))).2
      obtain ⟨sameEnv, sameCounter⟩ := Prod.mk.inj sameTyping
      subst blockNext blockCounter rootMiddle
      let tailFrame := { next with typingFuel := 4095 }
      have tailTyped' : typeExpr tailFrame.typingFuel tailFrame.typing expression tailFrame.typingCounter = .ok ([ty], bodyCounter) := by
        simpa [tailFrame] using tailTyped
      have tailRooted' : rpExpr tailFrame.source expression tailFrame.rootCursor = .ok (tailRoots, tailRootsAfter) := by
        simpa only [tailFrame, sourceEq, blockFrame, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, helperEq] using tailRooted
      have tailBounded := recursiveScalar_effects_bounded shape 4095 tailFrame.typing tailFrame.source config.module.globals.size
        tailFrame.typingCounter bodyCounter tailFrame.rootCursor tailRootsAfter [ty] tailRoots
        (by simpa [tailFrame, limitEq] using limit) finalBounded tailTyped' tailRooted'
      have tailAvailable : GlobalEffectsAvailable tailFrame.interpretation tailFrame.initialized tailRootsAfter.eff := by
        rw [show tailFrame.initialized = config.module.globals.size from nextFull, ← finalSource.compatible.globalCount]
        exact (globalEffectsAvailable_iff_bounded tailFrame.interpretation tailRootsAfter.eff).2
          (by simpa only [tailFrame, finalSource.compatible.globalCount] using tailBounded)
      have tailChecked : CheckedValue tailFrame expression ty tailRoots bodyCounter tailRootsAfter := ⟨tailTyped', tailRooted', tailAvailable⟩
      have tailWorld : AcceptedWorld config tailFrame.initialized middle (.callChannels activation [] :: ambient) nextTypes nextLive nextRegions pending := finalWorld
      have tailSource : AcceptedFrame config accepted tailFrame middle nextTypes := finalSource.withTypingFuel 4095
      have produced := evalProduce_checkedScalar_register_world shape fuel config accepted tailFrame middle
        (.callChannels activation [] :: ambient) nextTypes nextLive nextRegions pending tailWorld tailSource
        ty tailRoots bodyCounter tailRootsAfter tailChecked
      have scopeEnvironment : tailFrame.interpretation.environment =
          { activation with scopes := (helper.body.scope, before.nextScope) :: activation.scopes } := by
        simp [tailFrame, interpretationEq, entryFrame, entryStatementsFrame, blockStatementsFrame,
          RootInterpretation.enterScope, environment, helperEq]
      have normal : execStmts (fuel + 1) config
          { activation with scopes := (helper.body.scope, before.nextScope) :: activation.scopes }
          helper.body.stmts boundState = .ok (.normal .unit) middle := by
        simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environment, helperEq] using outcome
      have actual := execActivationBody_bound_registerTail (fuel + 1) config activation pre helper.body.scope helper.body.stmts
        expression ty before boundState middle channels bound normal
      rw [← helperBody] at actual
      rw [scopeEnvironment] at produced
      cases completed : withCompletionChannels [.register ty] (expressionOrigin expression)
          (fun channels => evalProduce (fuel + 1) config
            { activation with scopes := (helper.body.scope, before.nextScope) :: activation.scopes } channels expression) middle with
      | escape target carriers after | jump target kind after => simp [completed] at produced
      | stop reason after =>
        simp only [completed, Goose.Proofs.Exit.stepState] at produced
        have same := produced.1
        subst after
        simp only [completed] at actual
        rw [actual]
        exact ⟨nextTypes, nextLive, nextRegions, extended, unaffected, nextFull ▸ finalWorld⟩
      | ok carriers after =>
        simp only [completed, Goose.Proofs.Exit.stepState] at produced
        have same := produced.1
        subst after
        obtain ⟨value, sameCarriers, valid⟩ := produced.2.2.2
        subst carriers
        simp only [completed] at actual
        rw [actual]
        have released := finalWorld.releaseScope config next.initialized middle (.callChannels activation [] :: ambient)
          nextTypes nextLive nextRegions pending activation helper.body.scope before.nextScope
        refine ⟨value, nextTypes, _, nextRegions, rfl, valid.represented, extended, unaffected, nextFull ▸ released, ?_⟩
        intro root outside
        have scopeObserved := releaseScopeState_outsideActivation activation helper.body.scope before.nextScope middle root outside
        have bodyObserved := finalObserved root (by simpa [entryFrame, entryStatementsFrame, blockStatementsFrame,
          RootInterpretation.enterScope, environment] using outside)
        exact ⟨scopeObserved.1.trans bodyObserved.1, scopeObserved.2.trans bodyObserved.2⟩

theorem mixedLocal_registerResultBody_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (pre : List (Nat × Value))
    (before boundState : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (context : Context) (helper : Impl) (ty : Ty) (expression : Expr)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (helperEq : frame.source.impl = helper) (phase : frame.phase = .implementation contextId)
    (environment : frame.interpretation.environment = activation) (channels : activation.channels = [.register ty])
    (results : helper.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (tail : helper.body.value = some expression) (shape : AcceptedBinaryExpression expression)
    (initialized : frame.initialized = config.module.globals.size)
    (bound : bindAll activation.act before.nextScope pre
      (ownershipResultScopeState activation helper.body.scope before) = .ok () boundState)
    (world : AcceptedWorld config config.module.globals.size boundState (.callChannels activation [] :: ambient) types live regions pending)
    (source : AcceptedFrame config accepted (entryStatementsFrame config frame before.nextScope) boundState types)
    (position : SourcePosition accepted (entryStatementsFrame config frame before.nextScope) (.statements helper.body.stmts))
    (form : MixedLocalStatements helper.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ helper.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, helper.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
    match execActivationBody (fuel + 1) config activation pre helper.body before with
    | .stop _ after => ∃ nextTypes nextLive nextRegions, RootTypesExtend types nextTypes ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local activation.act scope id) → nextTypes root = types root) ∧
        AcceptedWorld config config.module.globals.size after (.callChannels activation [] :: ambient) nextTypes nextLive nextRegions pending
    | .ok carriers after => ∃ value nextTypes nextLive nextRegions, carriers = [.register value] ∧
        ValueRepresentation ty value ∧ RootTypesExtend types nextTypes ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local activation.act scope id) → nextTypes root = types root) ∧
        AcceptedWorld config config.module.globals.size after (.callChannels activation [] :: ambient) nextTypes nextLive nextRegions pending
    | _ => False := by
  have result := mixedLocal_registerResultBody_observedWorld fuel config accepted frame activation pre before boundState ambient types
    live regions pending contextId context helper ty expression helperAt helperEq phase environment channels results scalar tail shape
    initialized bound world source position form owners scalarOwners
  cases outcome : execActivationBody (fuel + 1) config activation pre helper.body before with
  | stop reason after => simpa only [outcome] using result
  | escape target carriers after => simpa only [outcome] using result
  | jump target kind after => simpa only [outcome] using result
  | ok carriers after =>
    simp only [outcome] at result ⊢
    obtain ⟨value, nextTypes, nextLive, nextRegions, eq, represented, extended, protectedTypes, finalWorld, observations⟩ := result
    exact ⟨value, nextTypes, nextLive, nextRegions, eq, represented, extended, protectedTypes, finalWorld⟩

#print axioms mixedLocal_registerResultBody_world
#print axioms mixedLocal_registerResultBody_observedWorld
end Goose.Proofs.ConstructionAcceptedExecution
