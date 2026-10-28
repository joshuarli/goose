import Goose.Proofs.ConstructionAcceptedParameterIdentity
import Goose.Proofs.ConstructionAcceptedEarlierCallerObservations
import Goose.Proofs.ConstructionAcceptedPartialRegisterParameterCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem bindAll_single_earlier (activation : RuntimeActivation) (scope : Nat) (parameter : Nat) (value : Value)
    (before after : ExecutionState) (types : RootTypes) (ty : Ty) (frontier : Nat)
    (frontierBefore : frontier ≤ activation.act)
    (bound : bindAll activation.act before.nextScope [(parameter, value)]
      (ownershipResultScopeState activation scope { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }) = .ok () after) :
    EarlierCallerObservations frontier
      { before with nextAct := before.nextAct + 1, activations := activation :: before.activations } after
      types (registerRootType types (.local activation.act before.nextScope parameter) ty) := by
  intro root earlier
  have outside : ∀ scope id, root ≠ .local activation.act scope id := by
    intro otherScope id same
    subst root
    exact (Nat.not_lt_of_ge frontierBefore) earlier
  have unchanged := bindAll_single_outside activation scope parameter value before after bound root outside
  exact ⟨unchanged.1, unchanged.2, by simp [registerRootType, outside before.nextScope parameter]⟩

theorem execActivationBody_identityParameter_lowFuel (config : EvalConfig) (activation : RuntimeActivation)
    (scope : Nat) (parameter : Nat) (value : Value) (ty : Ty) (before after : ExecutionState)
    (channels : activation.channels = [.register ty])
    (bound : bindAll activation.act before.nextScope [(parameter, value)]
      (ownershipResultScopeState activation scope { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }) = .ok () after) :
    let pushed := { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }
    let body := Block.mk scope [] (some (.read (.var 0)))
    execActivationBody 0 config activation [(parameter, value)] body pushed = .stop .timeout pushed ∧
    execActivationBody 1 config activation [(parameter, value)] body pushed = .stop .timeout after ∧
    execActivationBody 2 config activation [(parameter, value)] body pushed = .stop .timeout after ∧
    execActivationBody 3 config activation [(parameter, value)] body pushed = .stop .timeout after := by
  simp [ownershipResultScopeState, channels] at bound
  simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
    channels, beq_iff_eq, bound, execStmts, evalProduce, withCompletionChannels, completionChannelSetup,
    evalValue, evalPlace, selectCompletionChannel, timeout, EvalM.stop]

theorem identityParameterBody_partial (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (context : Context) (implementation : Impl) (parameter : Param) (descriptor : LocalVar)
    (value : Value) (ty : Ty)
    (contextAt : config.module.contexts[contextId]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (declared : implementation.vars[0]? = some descriptor)
    (body : implementation.body = ⟨implementation.body.scope, [], some (.read (.var 0))⟩)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (sameTy : descriptor.ty = ty) (represented : ValueRepresentation ty value)
    (pointers : PointerTypedValue types ty value)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types) :
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
  obtain ⟨frame, actual, after, sameImpl, initialized, phase, environment, act, scopes, channels, freshActStep,
    freshScopeStep, bound, extended, afterWorld, afterSource, position⟩ :=
    acceptedRegisterParameterCallBody_partial config accepted caller state ambient types live regions pending contextId context
      implementation parameter descriptor value ty contextAt implementationAt parameters declared scalar
      (by simpa [sameTy] using represented) (by simpa [sameTy] using pointers) world source
  have variables : actual.vars = implementation.vars := by
    have compatibility := afterSource.compatible
    simpa [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, RootInterpretation.enterScope,
      environment, sameImpl] using compatibility.variables.trans compatibility.sourceVariables.symm
  have identifier : actual.implementation = context.impl := by
    have origin := afterSource.compatible.origin
    simp only [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, RootInterpretation.enterScope,
      phase, SourceOrigin] at origin
    obtain ⟨original, calls, found, impl, same, rest⟩ := origin
    have eqContext : original = context := Option.some.inj (found.symm.trans contextAt)
    simpa [environment, eqContext] using same
  have actualEq : actual = (⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩ : RuntimeActivation) := by
    cases actual
    simp only [RuntimeActivation.mk.injEq] at *
    exact ⟨identifier, act, variables, scopes, channels⟩
  rw [actualEq] at bound extended afterWorld
  let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
  let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let root := Goose.Core.RootInst.local state.nextAct state.nextScope 0
  let nextTypes := registerRootType types root ty
  let nextLive := fun other => other = root ∨ live other
  have parameterId := validated_parameter_variable config.module context.impl implementation 0 parameter
    accepted.accepted implementationAt (by simp [parameters])
  have counters := bindAll_single_counters activation implementation.body.scope parameter.var value state after (by simpa [activation] using bound)
  have observed : EarlierCallerObservations state.nextAct pushed after types nextTypes := by
    simpa [activation, pushed, nextTypes, root, parameterId] using
      bindAll_single_earlier activation implementation.body.scope parameter.var value state after types ty state.nextAct
        (by simp [activation]) (by simpa [activation] using bound)
  have clear : FutureGlobalsClear config caller.initialized after := by
    simpa only [FutureGlobalsClear, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, initialized] using afterSource.futureGlobals
  have pushedWorld : AcceptedWorld config caller.initialized pushed (.callChannels activation [] :: ambient) types live regions pending :=
    acceptedWorld_pushRegisterActivation config caller.initialized state ambient types live regions pending activation world rfl ty rfl
  have pushedClear : FutureGlobalsClear config caller.initialized pushed := by
    simpa [pushed, FutureGlobalsClear] using source.futureGlobals
  have boundWorld : AcceptedWorld config caller.initialized after (.callChannels activation [] :: ambient) nextTypes nextLive regions pending := by
    simpa [activation, nextTypes, nextLive, root, sameTy] using afterWorld
  have extension : RootTypesExtend types nextTypes := by simpa [activation, nextTypes, root, sameTy] using extended
  have low := execActivationBody_identityParameter_lowFuel config activation implementation.body.scope parameter.var value ty state after rfl
    (by simpa [activation] using bound)
  have normal (n : Nat) := execActivationBody_identityParameter n config context.impl implementation parameter descriptor activation state after value ty
    accepted.accepted implementationAt (by simp [parameters]) declared rfl rfl (by simpa [activation] using bound)
  change ∃ nextTypes nextLive nextAmbient, let outcome := execActivationBody fuel config activation [(parameter.var, value)] implementation.body pushed; _
  cases fuel with
  | zero =>
    rw [body, low.1]
    exact ⟨types, live, .callChannels activation [] :: ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _,
      pushedWorld, pushedClear, EarlierCallerObservations.refl _ _ _, trivial⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      rw [body, low.2.1]
      exact ⟨nextTypes, nextLive, .callChannels activation [] :: ambient, extension, by simpa [pushed, Goose.Proofs.Exit.stepState] using Nat.le_of_eq counters.1.symm,
        by simp [pushed, Goose.Proofs.Exit.stepState, counters.2], boundWorld, clear, observed, trivial⟩
    | succ fuel =>
      cases fuel with
      | zero =>
        rw [body, low.2.2.1]
        exact ⟨nextTypes, nextLive, .callChannels activation [] :: ambient, extension, by simpa [pushed, Goose.Proofs.Exit.stepState] using Nat.le_of_eq counters.1.symm,
          by simp [pushed, Goose.Proofs.Exit.stepState, counters.2], boundWorld, clear, observed, trivial⟩
      | succ fuel =>
        cases fuel with
        | zero =>
          rw [body, low.2.2.2]
          exact ⟨nextTypes, nextLive, .callChannels activation [] :: ambient, extension, by simpa [pushed, Goose.Proofs.Exit.stepState] using Nat.le_of_eq counters.1.symm,
            by simp [pushed, Goose.Proofs.Exit.stepState, counters.2], boundWorld, clear, observed, trivial⟩
        | succ n =>
          rw [body, normal n]
          exact ⟨nextTypes, _, .callChannels activation [] :: ambient, extension,
            by simp [pushed, Goose.Proofs.Exit.stepState, releaseScopeState, counters.1], by simp [pushed, Goose.Proofs.Exit.stepState, releaseScopeState, counters.2],
            boundWorld.releaseScope config caller.initialized after (.callChannels activation [] :: ambient) nextTypes nextLive regions pending
              activation implementation.body.scope state.nextScope,
            clear.releaseScope activation implementation.body.scope state.nextScope,
            observed.trans (Nat.le_refl _) (EarlierCallerObservations.releaseScope state.nextAct activation implementation.body.scope
              state.nextScope after nextTypes (by simp [activation])), rfl, value, rfl, represented⟩

#print axioms identityParameterBody_partial
#print axioms bindAll_single_earlier
#print axioms execActivationBody_identityParameter_lowFuel
end Goose.Proofs.ConstructionAcceptedExecution
