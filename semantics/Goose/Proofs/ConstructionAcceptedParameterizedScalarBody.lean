import Goose.Proofs.ConstructionAcceptedParameterizedScalarTailEffects
import Goose.Proofs.ConstructionAcceptedParameterIdentityWorld
import Goose.Proofs.ConstructionAcceptedScalarControl

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem scalarParameterBody_parameterSummary_partial (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (implementation : Impl) (parameter : Param) (descriptor : LocalVar)
    (argument expression : Expr) (value : Value) (ty : Ty) (summary : Summary)
    (contextAt : config.module.contexts[contextId]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (declared : implementation.vars[0]? = some descriptor)
    (body : implementation.body = ⟨implementation.body.scope, [], some expression⟩) (form : AcceptedBinaryExpression expression)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (sameTy : descriptor.ty = ty) (represented : ValueRepresentation ty value) (pointers : PointerTypedValue types ty value)
    (known : implementation.summary = .known summary)
    (results : implementation.results = #[⟨ty, .register, none⟩])
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types) (outerTy : Ty) (outerRoots : List RootRef)
    (outerTypingAfter : Nat) (outerRootsAfter : RState)
    (checked : CheckedValue caller (.call contextId [.byVal argument] origin) outerTy outerRoots outerTypingAfter outerRootsAfter) :
    let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
    let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    ∃ nextTypes nextLive nextAmbient,
      let outcome := execActivationBody fuel config activation [(parameter.var, value)] implementation.body pushed
      RootTypesExtend types nextTypes ∧ pushed.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      pushed.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations state.nextAct pushed (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = .callChannels activation [] :: ambient ∧
           ∃ result, carriers = [.register result] ∧ ValueRepresentation ty result
       | .stop .. => True | .escape .. | .jump .. => False) := by
  have scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool := by simpa [sameTy] using scalar
  obtain ⟨frame, actual, after, tailRoots, tailTypingAfter, tailRootsAfter, sameImpl, initialized, environment, act, scopes, channels,
    activationImpl, activationVars, bound, extended, afterWorld, afterSource, tailChecked⟩ :=
    acceptedSingleByValueBoundScalarTail_parameterSummary config accepted caller state ambient types live regions pending contextId origin context implementation
      parameter descriptor argument value ty summary expression contextAt implementationAt parameters declared scalar
      (by simpa [sameTy] using represented) (by simpa [sameTy] using pointers) known form results body scalarTy world source
      outerTy outerRoots outerTypingAfter outerRootsAfter checked
  have actualEq : actual = (⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩ : RuntimeActivation) := by
    cases actual
    simp only [RuntimeActivation.mk.injEq] at *
    exact ⟨activationImpl, act, activationVars, scopes, channels⟩
  rw [actualEq] at bound extended afterWorld afterSource
  let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
  let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let root := Goose.Core.RootInst.local state.nextAct state.nextScope 0
  let nextTypes := registerRootType types root ty
  let nextLive := fun other => other = root ∨ live other
  let child := entryStatementsFrame config frame state.nextScope
  have parameterId := validated_parameter_variable config.module context.impl implementation 0 parameter
    accepted.accepted implementationAt (by simp [parameters])
  have bound' : bindAll activation.act pushed.nextScope [(parameter.var, value)]
      (ownershipResultScopeState activation implementation.body.scope pushed) = .ok () after := by simpa [activation, pushed] using bound
  have counters := bindAll_single_counters activation implementation.body.scope parameter.var value state after (by simpa [activation] using bound)
  have observed : EarlierCallerObservations state.nextAct pushed after types nextTypes := by
    simpa [activation, pushed, nextTypes, root, parameterId] using
      bindAll_single_earlier activation implementation.body.scope parameter.var value state after types ty state.nextAct
        (by simp [activation]) (by simpa [activation] using bound)
  have clear : FutureGlobalsClear config caller.initialized after := by
    simpa only [FutureGlobalsClear, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, initialized] using afterSource.futureGlobals
  have pushedWorld : AcceptedWorld config caller.initialized pushed (.callChannels activation [] :: ambient) types live regions pending :=
    acceptedWorld_pushRegisterActivation config caller.initialized state ambient types live regions pending activation world rfl ty rfl
  have pushedClear : FutureGlobalsClear config caller.initialized pushed := by simpa [pushed, FutureGlobalsClear] using source.futureGlobals
  have boundWorld : AcceptedWorld config caller.initialized after (.callChannels activation [] :: ambient) nextTypes nextLive regions pending := by
    simpa [activation, nextTypes, nextLive, root, sameTy] using afterWorld
  have extension : RootTypesExtend types nextTypes := by simpa [activation, nextTypes, root, sameTy] using extended
  have childSource : AcceptedFrame config accepted child after nextTypes := by simpa [child, nextTypes, root, sameTy] using afterSource
  have childWorld : AcceptedWorld config child.initialized after (.callChannels activation [] :: ambient) nextTypes nextLive regions pending := by
    simpa [child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, initialized] using boundWorld
  have childChecked : CheckedValue child expression ty tailRoots tailTypingAfter tailRootsAfter := by simpa [child] using tailChecked
  have childEnvironment : child.interpretation.environment =
      { activation with scopes := (implementation.body.scope, pushed.nextScope) :: activation.scopes } := by
    simp [child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, environment, actualEq,
      RootInterpretation.enterScope, activation, scopes, sameImpl, pushed]
  have step1 : execActivationBody 1 config activation [(parameter.var, value)]
      ⟨implementation.body.scope, [], some expression⟩ pushed = .stop .timeout after := by
    have step := bound'
    simp [ownershipResultScopeState] at step
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
      beq_iff_eq, step, execStmts, timeout, EvalM.stop]
  change ∃ nextTypes nextLive nextAmbient, let outcome := execActivationBody fuel config activation [(parameter.var, value)] implementation.body pushed; _
  cases fuel with
  | zero =>
    simp only [execActivationBody, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨types, live, .callChannels activation [] :: ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _,
      pushedWorld, pushedClear, EarlierCallerObservations.refl _ _ _, trivial⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      rw [body, step1]
      exact ⟨nextTypes, nextLive, .callChannels activation [] :: ambient, extension,
        by simpa [pushed, Goose.Proofs.Exit.stepState] using Nat.le_of_eq counters.1.symm,
        by simp [pushed, Goose.Proofs.Exit.stepState, counters.2], boundWorld, clear, observed, trivial⟩
    | succ fuel =>
      have complete := evalValue_checked_binary_recursive form fuel config accepted child after (.callChannels activation [] :: ambient)
        nextTypes nextLive regions pending childWorld childSource ty tailRoots tailTypingAfter tailRootsAfter childChecked
      have control := evalValue_scalar_controlFree form fuel config child.interpretation.environment
      have execution := execActivationBody_register_scalar_tail_withBindings form fuel config activation implementation.body.scope
        [(parameter.var, value)] [] pushed after after ty rfl bound' (by simp [execStmts, pure])
      cases evaluated : evalValue fuel config child.interpretation.environment expression after with
      | stop reason final =>
        simp only [evaluated, Goose.Proofs.Exit.stepState] at complete
        have same := complete.1
        subst final
        rw [childEnvironment] at evaluated
        rw [body, execution, evaluated]
        exact ⟨nextTypes, nextLive, .callChannels activation [] :: ambient, extension,
          by simpa [pushed, Goose.Proofs.Exit.stepState] using Nat.le_of_eq counters.1.symm,
          by simp [pushed, Goose.Proofs.Exit.stepState, counters.2], boundWorld, clear, observed, trivial⟩
      | escape target carriers final => exact False.elim (control.1 after target carriers final evaluated)
      | jump target kind final => exact False.elim (control.2 after target kind final evaluated)
      | ok result final =>
        have valueAccepted := complete.2.1 result final evaluated
        simp only [evaluated, Goose.Proofs.Exit.stepState] at complete
        have same := complete.1
        subst final
        rw [childEnvironment] at evaluated
        rw [body, execution, evaluated]
        exact ⟨nextTypes, _, .callChannels activation [] :: ambient, extension,
          by simp [pushed, Goose.Proofs.Exit.stepState, releaseScopeState, counters.1],
          by simp [pushed, Goose.Proofs.Exit.stepState, releaseScopeState, counters.2],
          boundWorld.releaseScope config caller.initialized after (.callChannels activation [] :: ambient) nextTypes nextLive regions pending
            activation implementation.body.scope state.nextScope,
          clear.releaseScope activation implementation.body.scope state.nextScope,
          observed.trans (Nat.le_refl _) (EarlierCallerObservations.releaseScope state.nextAct activation implementation.body.scope
            state.nextScope after nextTypes (by simp [activation])), rfl, result, rfl, valueAccepted.represented⟩


theorem scalarParameterBody_partial (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (implementation : Impl) (parameter : Param) (descriptor : LocalVar)
    (argument expression : Expr) (value : Value) (ty : Ty) (summary : Summary)
    (contextAt : config.module.contexts[contextId]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (declared : implementation.vars[0]? = some descriptor)
    (body : implementation.body = ⟨implementation.body.scope, [], some expression⟩) (form : AcceptedBinaryExpression expression)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (sameTy : descriptor.ty = ty) (represented : ValueRepresentation ty value) (pointers : PointerTypedValue types ty value)
    (known : implementation.summary = .known summary)
    (noParameters : ∀ id, .param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks)
    (results : implementation.results = #[⟨ty, .register, none⟩])
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types) (outerTy : Ty) (outerRoots : List RootRef)
    (outerTypingAfter : Nat) (outerRootsAfter : RState)
    (checked : CheckedValue caller (.call contextId [.byVal argument] origin) outerTy outerRoots outerTypingAfter outerRootsAfter) :
    let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
    let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    ∃ nextTypes nextLive nextAmbient,
      let outcome := execActivationBody fuel config activation [(parameter.var, value)] implementation.body pushed
      RootTypesExtend types nextTypes ∧ pushed.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      pushed.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations state.nextAct pushed (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = .callChannels activation [] :: ambient ∧
           ∃ result, carriers = [.register result] ∧ ValueRepresentation ty result
       | .stop .. => True | .escape .. | .jump .. => False) := by
  exact scalarParameterBody_parameterSummary_partial fuel config accepted caller state ambient types live regions pending
    contextId origin context implementation parameter descriptor argument expression value ty summary contextAt implementationAt
    parameters declared body form scalar sameTy represented pointers known results world source outerTy outerRoots outerTypingAfter
    outerRootsAfter checked

#print axioms scalarParameterBody_parameterSummary_partial
#print axioms scalarParameterBody_partial
end Goose.Proofs.ConstructionAcceptedExecution
