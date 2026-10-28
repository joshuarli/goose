import Goose.Proofs.ConstructionAcceptedObservedParameterListInvoke
import Goose.Proofs.ConstructionAcceptedScalarGlobalsRegisterBody
import Goose.Proofs.ConstructionAcceptedCallerScalarGlobals

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem scalarGlobalsParameterList_call_worldWithCallerFrame (specifications : List (Expr × Ty)) (fuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (callee : Impl) (resultTy : Ty) (resultExpression : Expr)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameterTypes : List Ty) (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (specificationTypes : specifications.map Prod.snd = parameterTypes)
    (results : callee.results = #[⟨resultTy, .register, none⟩]) (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (tail : callee.body.value = some resultExpression) (resultForm : AcceptedBinaryExpression resultExpression)
    (statements : ScalarGlobalAssignments callee.body.stmts)
    (globalScalar : ∀ id expression origin, .assign (.global id) expression origin ∈ callee.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types) (initialized : caller.initialized = config.module.globals.size)
    (safe : ∀ specification ∈ specifications, ∀ runtimeFuel current,
      AcceptedWorld config caller.initialized current ambient types live regions pending →
      AcceptedFrame config accepted caller current types →
      FirstArgumentOutcome config accepted caller ambient types live regions pending specification.2 []
        (evalValue runtimeFuel config caller.interpretation.environment specification.1 current)) :
    match invokeCall fuel config caller.interpretation.environment contextId
      (specifications.map fun specification => .byVal specification.1) [.register resultTy] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions, RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => ∃ value nextTypes nextLive nextRegions, carriers = [.register value] ∧
        ValueRepresentation resultTy value ∧ RootTypesExtend types nextTypes ∧
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending ∧
        AcceptedFrame config accepted caller after nextTypes
    | _ => False := by
  cases fuel with
  | zero =>
    simp only [invokeCall, timeout, EvalM.stop]
    exact ⟨ambient, types, live, regions, (fun _ _ found => found), initialized ▸ world⟩
  | succ fuel =>
    have arguments := evalArguments_statefulScalarList_body_protected specifications fuel config accepted caller state ambient types live regions pending
      contextId context callee resultTy contextAt calleeAt parameterTypes descriptors specificationTypes world source initialized safe
    cases evaluated : evalArguments fuel config caller.interpretation.environment callee.vars callee.params.toList
        (specifications.map fun specification => .byVal specification.1) state with
    | escape address carriers after | jump target kind after => simp [evaluated] at arguments
    | stop reason after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at arguments
      simp [invokeCall, getImplementation, contextAt, calleeAt, results, evaluated, bind, pure]
      exact ⟨ambient, types, (fun _ _ found => found), live, regions, initialized ▸ arguments.1⟩
    | ok values argumentState =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at arguments
      obtain ⟨argumentWorld, argumentSource, helperFrame, activation, boundState, boundTypes, boundLive,
        helperEq, helperInitialized, phase, environment, act, scopes, channels, freshActStep, freshScopeStep,
        bound, boundExtended, boundProtected, boundWorld, boundSource, bodyPosition⟩ := arguments
      by_cases tooDeep : argumentState.activations.length ≥ Goose.Core.maxCallDepth
      · simp [invokeCall, getImplementation, contextAt, calleeAt, results, evaluated, bind, pure, tooDeep, EvalM.get, timeout, EvalM.stop]
        exact ⟨ambient, types, (fun _ _ found => found), live, regions, initialized ▸ argumentWorld⟩
      · cases fuel with
        | zero => simp [evalArguments, timeout, EvalM.stop] at evaluated
        | succ fuel =>
          cases fuel with
          | zero =>
            let activation0 : RuntimeActivation := ⟨context.impl, argumentState.nextAct, callee.vars, [], [.register resultTy]⟩
            have currentWorld : AcceptedWorld config config.module.globals.size argumentState ambient types live regions pending := initialized ▸ argumentWorld
            have pushedWorld := acceptedWorld_pushRegisterActivation config config.module.globals.size argumentState ambient types live regions pending
              activation0 currentWorld rfl resultTy rfl
            simp [invokeCall, getImplementation, contextAt, calleeAt, results, evaluated, bind, pure, tooDeep,
              EvalM.get, EvalM.set, freshAct, enterActivation, execActivationBody, finishActivation, timeout, EvalM.stop]
            exact ⟨.callChannels activation0 [] :: ambient, types, (fun _ _ found => found), live, regions, pushedWorld⟩
          | succ fuel =>
            let pushed := { argumentState with nextAct := argumentState.nextAct + 1, activations := activation :: argumentState.activations }
            let pre := (callee.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
            have bodyResult := scalarGlobals_registerResultBody_observedWorld fuel config accepted helperFrame activation pre pushed boundState ambient
              boundTypes boundLive regions pending contextId context callee resultTy resultExpression
              calleeAt helperEq phase environment channels results resultScalar tail resultForm statements globalScalar helperInitialized
              (by simpa [pushed, pre] using bound) (by simpa [pushed] using boundWorld) (by simpa [pushed] using boundSource)
              (by simpa [pushed] using bodyPosition)
            have implementationId : activation.implementation = context.impl := by
              have originFact := boundSource.compatible.origin
              unfold SourceOrigin at originFact
              simp only [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, phase] at originFact
              obtain ⟨selected, calls, selectedAt, implementationAt, implementationId, rest⟩ := originFact
              have sameContext : selected = context := Option.some.inj (selectedAt.symm.trans contextAt)
              subst selected
              simpa [environment, RootInterpretation.enterScope] using implementationId
            have vars : activation.vars = callee.vars := by
              have fact := boundSource.compatible.variables.trans boundSource.compatible.sourceVariables.symm
              simpa [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame,
                RootInterpretation.enterScope, environment, helperEq] using fact
            have activationEq : activation = ⟨context.impl, argumentState.nextAct, callee.vars, [], [.register resultTy]⟩ := by
              cases activation with
              | mk implementation actualAct actualVars actualScopes actualChannels =>
                simp only at implementationId act vars scopes channels
                cases implementationId; cases act; cases vars; cases scopes; cases channels; rfl
            have evaluated' : evalArguments (fuel + 2) config caller.interpretation.environment callee.vars callee.params.toList
                (specifications.map fun specification => .byVal specification.1) state = .ok values argumentState := by
              simpa [Nat.add_assoc] using evaluated
            have invokeStep : invokeCall (fuel + 3) config caller.interpretation.environment contextId
                (specifications.map fun specification => .byVal specification.1) [.register resultTy] origin state =
                (finishActivation config.layout activation [resultTy] origin
                  (execActivationBody (fuel + 1) config activation pre helperFrame.source.impl.body) >>= fun carriers =>
                    deliverCarriers (fuel + 2) config.layout [.register resultTy] carriers origin) pushed := by
              simp [invokeCall, getImplementation, contextAt, calleeAt, results, evaluated', enterActivation,
                freshAct, EvalM.get, EvalM.set, bind, pure, tooDeep, activationEq, pushed, pre, helperEq]
            rw [invokeStep]
            rw [← helperEq] at bodyResult
            cases body : execActivationBody (fuel + 1) config activation pre helperFrame.source.impl.body pushed with
            | escape address carriers after | jump target kind after => simp [body] at bodyResult
            | stop reason after =>
              simp only [body] at bodyResult
              obtain ⟨nextLive, nextRegions, finalWorld⟩ := bodyResult
              simp only [bind, finishActivation, body]
              exact ⟨.callChannels activation [] :: ambient, boundTypes, nextLive, nextRegions, boundExtended, finalWorld⟩
            | ok carriers after =>
              simp only [body] at bodyResult
              obtain ⟨returned, nextLive, nextRegions, equal, represented, finalWorld, bodyObservation⟩ := bodyResult
              subst carriers
              have outer := (initialized ▸ argumentWorld).freshActivationOutside config config.module.globals.size argumentState ambient types live regions pending
              have outer' : OwnershipAmbient.withoutActivation activation.act ambient = ambient := by simpa [act] using outer
              have finished := finalWorld.finishEmptyCall config config.module.globals.size after activation ambient boundTypes nextLive nextRegions pending outer'
              have bindingObserved := bindAll_list_observations activation.act argumentState.nextScope pre
                (ownershipResultScopeState activation callee.body.scope pushed) boundState (by simpa [pushed, pre] using bound)
              have protectedTypes : ∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local argumentState.nextAct scope id) → boundTypes root = types root := by
                intro root outside
                exact boundProtected root (by simpa [act] using outside argumentState.nextScope)
              have counters : argumentState.nextAct ≤ after.nextAct ∧ argumentState.nextScope ≤ after.nextScope := by
                simp only [pushed, ownershipResultScopeState] at bindingObserved
                have bodyActs := bodyObservation.1
                have bodyScopes := bodyObservation.2.1
                omega
              have objectObservations : ∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local argumentState.nextAct scope id) →
                  after.objects.lookup root = argumentState.objects.lookup root ∨
                  ∃ id value, root = .global id ∧ after.objects.lookup root = some value ∧
                    ((∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean) := by
                intro root outside
                rcases bodyObservation.2.2.1 root (by simpa [act] using outside) with unchanged | scalar
                · have boundOutside := bindingObserved.2.2 root (by simpa [act] using outside argumentState.nextScope)
                  exact Or.inl (unchanged.trans (by simpa [pushed, ownershipResultScopeState] using boundOutside.1))
                · exact Or.inr scalar
              have ordinalObservations : ∀ root, (∃ act scope id, root = Goose.Core.RootInst.local act scope id) →
                  (∀ scope id, root ≠ Goose.Core.RootInst.local argumentState.nextAct scope id) →
                  after.objectOrdinals.lookup root = argumentState.objectOrdinals.lookup root := by
                intro root localRoot outside
                obtain ⟨otherAct, scope, id, rfl⟩ := localRoot
                have different : otherAct ≠ activation.act := by
                  intro same
                  apply outside scope id
                  simp [same, act]
                have bodyOrdinal := bodyObservation.2.2.2 otherAct scope id different
                have boundOutside := bindingObserved.2.2 (.local otherAct scope id) (by simpa [act] using outside argumentState.nextScope)
                exact bodyOrdinal.trans (by simpa [pushed, ownershipResultScopeState] using boundOutside.2)
              have callerAfter := argumentSource.afterFreshActivationWithScalarGlobalsLocalOrdinals initialized counters.1 counters.2
                objectObservations ordinalObservations protectedTypes
              have callerFinished := callerAfter.withActivations (after.activations.filter (fun current => current.act != activation.act))
              simp [bind, finishActivation, body, finishChannels, landCarriersInto, deliverCarriers, pure, channels]
              exact ⟨returned, rfl, represented, boundTypes, boundExtended, ⟨nextLive, nextRegions, finished⟩, callerFinished⟩


#print axioms scalarGlobalsParameterList_call_worldWithCallerFrame
end Goose.Proofs.ConstructionAcceptedExecution
