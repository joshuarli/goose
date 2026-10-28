import Goose.Proofs.ConstructionAcceptedStatefulParameterListInvoke
import Goose.Proofs.ConstructionAcceptedProtectedParameterListBody
import Goose.Proofs.ConstructionAcceptedParameterListObservation
import Goose.Proofs.ConstructionAcceptedUnusedScope

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem statefulScalarParameterList_call_worldWithCallerFrame (specifications : List (Expr × Ty)) (fuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (callee : Impl) (resultTy : Ty) (resultExpression : Expr)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameterTypes : List Ty) (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (specificationTypes : specifications.map Prod.snd = parameterTypes)
    (results : callee.results = #[⟨resultTy, .register, none⟩]) (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (bodyForm : MixedLocalStatements callee.body.stmts) (tail : callee.body.value = some resultExpression)
    (resultForm : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ callee.body.stmts →
      (callee.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value statementOrigin, .letS id value statementOrigin ∈ callee.body.stmts →
      AcceptedBinaryExpression value → ∀ descriptor, callee.vars[id]? = some descriptor →
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
            have bodyResult := mixedLocal_registerResultBody_observedWorld fuel config accepted helperFrame activation pre pushed boundState ambient
              boundTypes boundLive regions pending contextId context callee resultTy resultExpression calleeAt helperEq phase environment channels
              results resultScalar tail resultForm helperInitialized (by simpa [pushed, pre] using bound) (by simpa [pushed] using boundWorld)
              (by simpa [pushed] using boundSource) (by simpa [pushed] using bodyPosition) bodyForm owners scalarOwners
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
              obtain ⟨nextTypes, nextLive, nextRegions, bodyExtended, bodyProtected, finalWorld⟩ := bodyResult
              simp only [bind, finishActivation, body]
              exact ⟨.callChannels activation [] :: ambient, nextTypes, nextLive, nextRegions,
                (fun root ty found => bodyExtended root ty (boundExtended root ty found)), finalWorld⟩
            | ok carriers after =>
              simp only [body] at bodyResult
              obtain ⟨returned, nextTypes, nextLive, nextRegions, equal, represented, bodyExtended, bodyProtected, finalWorld, bodyCounters, bodyObserved⟩ := bodyResult
              subst carriers
              have outer := (initialized ▸ argumentWorld).freshActivationOutside config config.module.globals.size argumentState ambient types live regions pending
              have outer' : OwnershipAmbient.withoutActivation activation.act ambient = ambient := by simpa [act] using outer
              have finished := finalWorld.finishEmptyCall config config.module.globals.size after activation ambient nextTypes nextLive nextRegions pending outer'
              have bindingObserved := bindAll_list_observations activation.act argumentState.nextScope pre
                (ownershipResultScopeState activation callee.body.scope pushed) boundState (by simpa [pushed, pre] using bound)
              have protectedTypes : ∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local argumentState.nextAct scope id) → nextTypes root = types root := by
                intro root outside
                have bodyOutside := bodyProtected root (by simpa [act] using outside)
                have boundOutside := boundProtected root (by simpa [act] using outside argumentState.nextScope)
                exact bodyOutside.trans boundOutside
              have counters : argumentState.nextAct ≤ after.nextAct ∧ argumentState.nextScope ≤ after.nextScope := by
                simp only [pushed, ownershipResultScopeState] at bindingObserved
                omega
              have observations : ∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local argumentState.nextAct scope id) →
                  after.objects.lookup root = argumentState.objects.lookup root ∧ after.objectOrdinals.lookup root = argumentState.objectOrdinals.lookup root := by
                intro root outside
                have bodyOutside := bodyObserved root (by simpa [act] using outside)
                have bindOutside := bindingObserved.2.2 root (by simpa [act] using outside argumentState.nextScope)
                exact ⟨bodyOutside.1.trans (by simpa [pushed, ownershipResultScopeState] using bindOutside.1),
                  bodyOutside.2.trans (by simpa [pushed, ownershipResultScopeState] using bindOutside.2)⟩
              have callerAfter := argumentSource.afterFreshActivation counters.1 counters.2
                (fun root outside => (observations root outside).1) (fun root outside => (observations root outside).2) protectedTypes
              have callerFinished := callerAfter.withActivations (after.activations.filter (fun current => current.act != activation.act))
              simp [bind, finishActivation, body, finishChannels, landCarriersInto, deliverCarriers, pure, channels]
              exact ⟨returned, rfl, represented, nextTypes,
                (fun root ty found => bodyExtended root ty (boundExtended root ty found)), ⟨nextLive, nextRegions, finished⟩, callerFinished⟩


#print axioms statefulScalarParameterList_call_worldWithCallerFrame
end Goose.Proofs.ConstructionAcceptedExecution
