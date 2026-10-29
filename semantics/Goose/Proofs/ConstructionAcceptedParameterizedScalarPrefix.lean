import Goose.Proofs.ConstructionAcceptedParameterizedStatementCall
import Goose.Proofs.ConstructionAcceptedScalarLocalPrefix

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem execActivationBody_boundScalarPrefix_withClock_earlier (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (activation : RuntimeActivation) (scope : Nat)
    (pre : List (Nat × Value)) (statements : List Stmt) (target origin : Nat) (arguments : List Arg)
    (before boundState : ExecutionState) (ambient : OwnershipAmbient) (types boundTypes : RootTypes)
    (boundLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (ty : Ty) (frontier : Nat)
    (channels : activation.channels = [.register ty]) (frontierBound : frontier ≤ activation.act)
    (environment : frame.interpretation.environment = { activation with scopes := (scope, before.nextScope) :: activation.scopes })
    (bound : bindAll activation.act before.nextScope pre (ownershipResultScopeState activation scope before) = .ok () boundState)
    (extended : RootTypesExtend types boundTypes) (acts : before.nextAct ≤ boundState.nextAct) (scopes : before.nextScope ≤ boundState.nextScope)
    (observed : EarlierCallerObservations frontier before boundState types boundTypes)
    (world : AcceptedWorld config frame.initialized boundState ambient boundTypes boundLive regions pending)
    (source : AcceptedFrame config accepted frame boundState boundTypes) (phase : frame.phase = .implementation context)
    (position : SourcePosition accepted frame (.statements statements)) (form : ScalarLocalStatements statements)
    (available : ∀ rootsAfter, rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter) →
      GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff)
    (scalar : ∀ id expression location, .letS id expression location ∈ statements → ∀ descriptor,
      frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (inner : ∀ (final : ConstructionSourceFrame) (middle : ExecutionState) (middleTypes : RootTypes)
        (middleLive : Goose.Core.RootInst → Prop),
      final.initialized = frame.initialized → middle.nextAct = boundState.nextAct →
      AcceptedWorld config final.initialized middle ambient middleTypes middleLive regions pending →
      AcceptedFrame config accepted final middle middleTypes → ScalarLocalReplay frame final statements →
      ∃ finalTypes finalLive finalAmbient,
        let outcome := invokeCall fuel config frame.interpretation.environment target arguments [.register ty] origin middle
        RootTypesExtend middleTypes finalTypes ∧ middle.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        middle.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) finalAmbient finalTypes finalLive regions pending ∧
        FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations frontier middle (Goose.Proofs.Exit.stepState outcome) middleTypes finalTypes ∧
        (match outcome with
         | .ok carriers _ => finalAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ finalTypes finalLive finalAmbient,
      let outcome := execActivationBody (fuel + 2) config activation pre ⟨scope, statements, some (.call target arguments origin)⟩ before
      RootTypesExtend types finalTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) finalAmbient finalTypes finalLive regions pending ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations frontier before (Goose.Proofs.Exit.stepState outcome) types finalTypes ∧
      (match outcome with
       | .ok carriers _ => finalAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  have frameFrontier : frontier ≤ frame.interpretation.environment.act := by simpa [environment] using frontierBound
  obtain ⟨final, middleTypes, middleLive, initialized, extension, nextAct, nextScope, middleWorld, middleSource, middleObserved, flow⟩ :=
    execStmts_scalarLocal_prefix_observed form frontier (fuel + 1) config accepted frame context boundState ambient boundTypes boundLive
      regions pending frameFrontier world source phase position available scalar
  cases execution : execStmts (fuel + 1) config frame.interpretation.environment statements boundState with
  | stop reason after =>
    simp only [execution, Goose.Proofs.Exit.stepState] at nextAct nextScope middleWorld middleSource middleObserved flow
    have stopped := execActivationBody_boundStatements_stopped fuel config activation scope pre statements (.call target arguments origin)
      before boundState after reason bound (by simpa [environment] using execution)
    rw [stopped]
    exact ⟨middleTypes, middleLive, ambient, (fun root ty found => extension root ty (extended root ty found)),
      nextAct ▸ acts, nextScope ▸ scopes, initialized ▸ middleWorld, initialized ▸ middleSource.futureGlobals,
      observed.trans (Nat.le_refl _) middleObserved, trivial⟩
  | escape address carriers after | jump destination kind after => simp [execution] at flow
  | ok result middle =>
    simp only [execution, Goose.Proofs.Exit.stepState] at nextAct nextScope middleWorld middleSource middleObserved flow
    obtain ⟨normal, _, replay⟩ := flow
    subst result
    have safe := inner final middle middleTypes middleLive initialized nextAct middleWorld middleSource replay
    apply execActivationBody_boundStatementsCall_earlier fuel config frame.initialized activation scope pre statements target origin arguments
      before boundState middle ambient types middleTypes regions pending ty frontier channels frontierBound bound
      (by simpa [environment] using execution) (fun root ty found => extension root ty (extended root ty found))
      (nextAct ▸ acts) (nextScope ▸ scopes) (observed.trans (Nat.le_refl _) middleObserved)
    rw [environment] at safe
    exact safe


theorem execActivationBody_boundScalarPrefix_earlier (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (activation : RuntimeActivation) (scope : Nat)
    (pre : List (Nat × Value)) (statements : List Stmt) (target origin : Nat) (arguments : List Arg)
    (before boundState : ExecutionState) (ambient : OwnershipAmbient) (types boundTypes : RootTypes)
    (boundLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (ty : Ty) (frontier : Nat)
    (channels : activation.channels = [.register ty]) (frontierBound : frontier ≤ activation.act)
    (environment : frame.interpretation.environment = { activation with scopes := (scope, before.nextScope) :: activation.scopes })
    (bound : bindAll activation.act before.nextScope pre (ownershipResultScopeState activation scope before) = .ok () boundState)
    (extended : RootTypesExtend types boundTypes) (acts : before.nextAct ≤ boundState.nextAct) (scopes : before.nextScope ≤ boundState.nextScope)
    (observed : EarlierCallerObservations frontier before boundState types boundTypes)
    (world : AcceptedWorld config frame.initialized boundState ambient boundTypes boundLive regions pending)
    (source : AcceptedFrame config accepted frame boundState boundTypes) (phase : frame.phase = .implementation context)
    (position : SourcePosition accepted frame (.statements statements)) (form : ScalarLocalStatements statements)
    (available : ∀ rootsAfter, rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter) →
      GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff)
    (scalar : ∀ id expression location, .letS id expression location ∈ statements → ∀ descriptor,
      frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (inner : ∀ (final : ConstructionSourceFrame) (middle : ExecutionState) (middleTypes : RootTypes)
        (middleLive : Goose.Core.RootInst → Prop),
      final.initialized = frame.initialized →
      AcceptedWorld config final.initialized middle ambient middleTypes middleLive regions pending →
      AcceptedFrame config accepted final middle middleTypes → ScalarLocalReplay frame final statements →
      ∃ finalTypes finalLive finalAmbient,
        let outcome := invokeCall fuel config frame.interpretation.environment target arguments [.register ty] origin middle
        RootTypesExtend middleTypes finalTypes ∧ middle.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
        middle.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
        AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) finalAmbient finalTypes finalLive regions pending ∧
        FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
        EarlierCallerObservations frontier middle (Goose.Proofs.Exit.stepState outcome) middleTypes finalTypes ∧
        (match outcome with
         | .ok carriers _ => finalAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
         | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ finalTypes finalLive finalAmbient,
      let outcome := execActivationBody (fuel + 2) config activation pre ⟨scope, statements, some (.call target arguments origin)⟩ before
      RootTypesExtend types finalTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) finalAmbient finalTypes finalLive regions pending ∧
      FutureGlobalsClear config frame.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations frontier before (Goose.Proofs.Exit.stepState outcome) types finalTypes ∧
      (match outcome with
       | .ok carriers _ => finalAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  apply execActivationBody_boundScalarPrefix_withClock_earlier fuel config accepted frame context activation scope pre statements target origin arguments
    before boundState ambient types boundTypes boundLive regions pending ty frontier channels frontierBound environment bound extended acts scopes
    observed world source phase position form available scalar
  intro final middle middleTypes middleLive initialized _ finalWorld finalSource replay
  exact inner final middle middleTypes middleLive initialized finalWorld finalSource replay

#print axioms execActivationBody_boundScalarPrefix_withClock_earlier
#print axioms execActivationBody_boundScalarPrefix_earlier
end Goose.Proofs.ConstructionAcceptedExecution
