import Goose.Proofs.ConstructionAcceptedEmptyParameterListBody
import Goose.Proofs.ConstructionAcceptedMixedAssignBoundBody
import Goose.Proofs.ConstructionAcceptedFreshActivation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem emptyMixedAssignParameterList_call_world (specifications : List (Expr × Ty)) (fuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (callee : Impl)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameterTypes : List Ty) (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (specificationTypes : specifications.map Prod.snd = parameterTypes)
    (results : callee.results = #[])
    (bodyForm : MixedAssignStatements callee.body.stmts) (tail : callee.body.value = none)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ callee.body.stmts →
      (callee.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value statementOrigin, .letS id value statementOrigin ∈ callee.body.stmts →
      AcceptedBinaryExpression value → ∀ descriptor, callee.vars[id]? = some descriptor →
        (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (localTargets : ∀ id expression statementOrigin, .assign (.var id) expression statementOrigin ∈ callee.body.stmts →
      ∀ descriptor, callee.vars[id]? = some descriptor → (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (globalTargets : ∀ id expression statementOrigin, .assign (.global id) expression statementOrigin ∈ callee.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor → (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types) (initialized : caller.initialized = config.module.globals.size)
    (safe : ∀ specification ∈ specifications, ∀ runtimeFuel current,
      AcceptedWorld config caller.initialized current ambient types live regions pending →
      AcceptedFrame config accepted caller current types →
      FirstArgumentOutcome config accepted caller ambient types live regions pending specification.2 []
        (evalValue runtimeFuel config caller.interpretation.environment specification.1 current)) :
    match invokeCall fuel config caller.interpretation.environment contextId
      (specifications.map fun specification => .byVal specification.1) [] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => carriers = [] ∧ ∃ nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending
    | _ => False := by
  cases fuel with
  | zero =>
    simp only [invokeCall, timeout, EvalM.stop]
    exact ⟨ambient, types, live, regions, initialized ▸ world⟩
  | succ fuel =>
    have arguments := evalArguments_emptyParameterList_body specifications fuel config accepted caller state ambient types live regions pending
      contextId context callee contextAt calleeAt parameterTypes descriptors specificationTypes world source initialized safe
    cases evaluated : evalArguments fuel config caller.interpretation.environment callee.vars callee.params.toList
        (specifications.map fun specification => .byVal specification.1) state with
    | escape address carriers after | jump target kind after => simp [evaluated] at arguments
    | stop reason after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at arguments
      simp [invokeCall, getImplementation, contextAt, calleeAt, results, evaluated, bind, pure]
      exact ⟨ambient, types, live, regions, initialized ▸ arguments.1⟩
    | ok values argumentState =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at arguments
      obtain ⟨argumentWorld, argumentSource, helperFrame, activation, boundState, boundTypes, boundLive,
        helperEq, helperInitialized, phase, environment, act, scopes, channels, freshActStep, freshScopeStep,
        bound, boundExtended, boundProtected, boundWorld, boundSource, bodyPosition⟩ := arguments
      by_cases tooDeep : argumentState.activations.length ≥ Goose.Core.maxCallDepth
      · simp [invokeCall, getImplementation, contextAt, calleeAt, results, evaluated, bind, pure, tooDeep, EvalM.get, timeout, EvalM.stop]
        exact ⟨ambient, types, live, regions, initialized ▸ argumentWorld⟩
      · cases fuel with
        | zero => simp [evalArguments, timeout, EvalM.stop] at evaluated
        | succ fuel =>
          cases fuel with
          | zero =>
            let activation0 : RuntimeActivation := ⟨context.impl, argumentState.nextAct, callee.vars, [], []⟩
            have currentWorld : AcceptedWorld config config.module.globals.size argumentState ambient types live regions pending := initialized ▸ argumentWorld
            have pushedWorld := acceptedWorld_pushEmptyActivation config config.module.globals.size argumentState ambient types live regions pending
              activation0 currentWorld rfl rfl
            simp [invokeCall, getImplementation, contextAt, calleeAt, results, evaluated, bind, pure, tooDeep,
              EvalM.get, EvalM.set, freshAct, enterActivation, execActivationBody, finishActivation, timeout, EvalM.stop]
            exact ⟨.callChannels activation0 [] :: ambient, types, live, regions, pushedWorld⟩
          | succ fuel =>
            let pushed := { argumentState with nextAct := argumentState.nextAct + 1, activations := activation :: argumentState.activations }
            let pre := (callee.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
            have bodyResult := mixedAssign_boundBody_world fuel config accepted helperFrame activation pre pushed boundState ambient
              boundTypes boundLive regions pending contextId environment channels (by simpa [helperEq] using results)
              (by simpa [helperEq] using tail) phase helperInitialized (by simpa [pushed, pre, helperEq] using bound) (by simpa [pushed] using boundWorld)
              (by simpa [pushed] using boundSource) (by simpa [pushed, helperEq] using bodyPosition)
              (by simpa [helperEq] using bodyForm) (by simpa [helperEq] using owners) (by simpa [helperEq] using scalarOwners)
              (by simpa [helperEq] using localTargets) (by simpa [helperEq] using globalTargets)
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
            have activationEq : activation = ⟨context.impl, argumentState.nextAct, callee.vars, [], []⟩ := by
              cases activation with
              | mk implementation actualAct actualVars actualScopes actualChannels =>
                simp only at implementationId act vars scopes channels
                cases implementationId; cases act; cases vars; cases scopes; cases channels; rfl
            have evaluated' : evalArguments (fuel + 2) config caller.interpretation.environment callee.vars callee.params.toList
                (specifications.map fun specification => .byVal specification.1) state = .ok values argumentState := by
              simpa [Nat.add_assoc] using evaluated
            have invokeStep : invokeCall (fuel + 3) config caller.interpretation.environment contextId
                (specifications.map fun specification => .byVal specification.1) [] origin state =
                (finishActivation config.layout activation [] origin
                  (execActivationBody (fuel + 1) config activation pre helperFrame.source.impl.body) >>= fun carriers =>
                    deliverCarriers (fuel + 2) config.layout [] carriers origin) pushed := by
              simp [invokeCall, getImplementation, contextAt, calleeAt, results, evaluated', enterActivation,
                freshAct, EvalM.get, EvalM.set, bind, pure, tooDeep, activationEq, pushed, pre, helperEq]
            rw [invokeStep]
            cases body : execActivationBody (fuel + 1) config activation pre helperFrame.source.impl.body pushed with
            | escape address carriers after | jump target kind after => simp [body] at bodyResult
            | stop reason after =>
              simp only [body] at bodyResult
              obtain ⟨nextTypes, nextLive, nextRegions, finalWorld⟩ := bodyResult
              simp only [bind, finishActivation, body]
              exact ⟨.callChannels activation [] :: ambient, nextTypes, nextLive, nextRegions, finalWorld⟩
            | ok carriers after =>
              simp only [body] at bodyResult
              obtain ⟨equal, nextTypes, nextLive, nextRegions, finalWorld⟩ := bodyResult
              subst carriers
              have outer := (initialized ▸ argumentWorld).freshActivationOutside config config.module.globals.size argumentState ambient types live regions pending
              have outer' : OwnershipAmbient.withoutActivation activation.act ambient = ambient := by simpa [act] using outer
              have finished := finalWorld.finishEmptyCall config config.module.globals.size after activation ambient nextTypes nextLive nextRegions pending outer'
              simp [bind, finishActivation, body, finishChannels, landCarriersInto, deliverCarriers, pure, channels]
              exact ⟨nextTypes, nextLive, nextRegions, finished⟩


#print axioms emptyMixedAssignParameterList_call_world
end Goose.Proofs.ConstructionAcceptedExecution
