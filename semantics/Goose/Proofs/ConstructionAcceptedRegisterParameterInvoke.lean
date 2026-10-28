import Goose.Proofs.ConstructionAcceptedRegisterParameterArgument
import Goose.Proofs.ConstructionAcceptedRegisterResultBody
import Goose.Proofs.ConstructionAcceptedNestedActivation
import Goose.Proofs.ConstructionAcceptedParameterObservation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem mixedLocalRegisterParameter_call_observedWorld {expression : Expr} (shape : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar)
    (resultTy : Ty) (resultExpression : Expr)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[parameter]) (results : helper.results = #[⟨resultTy, .register, none⟩])
    (resultScalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (declared : helper.vars[0]? = some descriptor)
    (scalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (callerInitialized : caller.initialized = config.module.globals.size)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (callerSource : AcceptedFrame config accepted caller state types)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller expression descriptor.ty roots typingAfter rootsAfter)
    (form : MixedLocalStatements helper.body.stmts) (tail : helper.body.value = some resultExpression)
    (resultShape : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value origin, .letS id value origin ∈ helper.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, helper.vars[id]? = some localDesc →
        (∃ ty, localDesc.ty = .int ty) ∨ localDesc.ty = .bool)
    (depth : state.activations.length < Goose.Core.maxCallDepth)
    (outer : OwnershipAmbient.withoutActivation state.nextAct ambient = ambient) :
    match invokeCall fuel config caller.interpretation.environment contextId [.byVal expression] [.register resultTy] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions, RootTypesExtend types nextTypes ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local state.nextAct scope id) → nextTypes root = types root) ∧
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => ∃ value nextTypes nextLive nextRegions, carriers = [.register value] ∧
        ValueRepresentation resultTy value ∧ RootTypesExtend types nextTypes ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local state.nextAct scope id) → nextTypes root = types root) ∧
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local state.nextAct scope id) →
          after.objects.lookup root = state.objects.lookup root ∧ after.objectOrdinals.lookup root = state.objectOrdinals.lookup root)
    | _ => False := by
  cases fuel with
  | zero =>
    simp only [invokeCall, timeout, EvalM.stop]
    exact ⟨ambient, types, live, regions, (fun _ _ found => found), (fun _ _ => rfl), callerInitialized ▸ world⟩
  | succ fuel =>
    have arguments := evalArguments_registerParameter_body shape fuel config accepted caller state ambient types live
      regions pending contextId context helper parameter descriptor resultTy contextAt helperAt parameters declared scalar
      callerInitialized world callerSource roots typingAfter rootsAfter checked
    cases evaluated : evalArguments fuel config caller.interpretation.environment helper.vars helper.params.toList [.byVal expression] state with
    | escape address carriers after | jump target kind after => simp [evaluated] at arguments
    | stop reason after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at arguments
      have same := arguments.1
      subst after
      simp [invokeCall, getImplementation, contextAt, helperAt, results, evaluated, bind, pure]
      exact ⟨ambient, types, (fun _ _ found => found), (fun _ _ => rfl), live, regions, callerInitialized ▸ world⟩
    | ok values after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at arguments
      have same := arguments.1
      subst after
      obtain ⟨value, valuesEq, frame, activation, boundState, helperEq, initialized, phase, environment, act, scopes,
        channels, fresh, freshScope, bound, boundExtended, boundWorld, boundSource, position⟩ := arguments.2
      subst values
      cases fuel with
      | zero => simp [evalArguments, timeout, EvalM.stop] at evaluated
      | succ fuel =>
        cases fuel with
        | zero =>
          cases expressionStep : evalValue 0 config caller.interpretation.environment expression state <;>
            simp [parameters, evalArguments, expressionStep, bind, timeout, EvalM.stop] at evaluated
        | succ fuel =>
          let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
          have bodyResult := mixedLocal_registerResultBody_observedWorld fuel config accepted frame activation [(parameter.var, value)] pushed
            boundState ambient (registerRootType types (.local activation.act state.nextScope 0) descriptor.ty)
            (fun other => other = .local activation.act state.nextScope 0 ∨ live other) regions pending contextId context helper resultTy resultExpression
            helperAt helperEq phase environment channels results resultScalar tail resultShape initialized (by simpa [pushed] using bound)
            (by simpa [pushed] using boundWorld) (by simpa [pushed] using boundSource)
            (by simpa [pushed] using position) form owners scalarOwners
          have implementationId : activation.implementation = context.impl := by
            have origin := boundSource.compatible.origin
            unfold SourceOrigin at origin
            simp only [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, phase] at origin
            obtain ⟨selected, calls, selectedAt, implementationAt, implementationId, rest⟩ := origin
            have sameContext : selected = context := Option.some.inj (selectedAt.symm.trans contextAt)
            subst selected
            simpa [environment, RootInterpretation.enterScope] using implementationId
          have vars : activation.vars = helper.vars := by
            have fact := boundSource.compatible.variables.trans boundSource.compatible.sourceVariables.symm
            simpa [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame,
              RootInterpretation.enterScope, environment, helperEq] using fact
          have activationEq : activation = ⟨context.impl, state.nextAct, helper.vars, [], [.register resultTy]⟩ := by
            cases activation with
            | mk implementation actualAct actualVars actualScopes actualChannels =>
              simp only at implementationId act vars scopes channels
              cases implementationId; cases act; cases vars; cases scopes; cases channels; rfl
          have evaluated' : evalArguments (fuel + 2) config caller.interpretation.environment helper.vars [parameter]
              [.byVal expression] state = .ok [value] state := by
            simpa [parameters, Nat.add_assoc] using evaluated
          have invokeStep : invokeCall (fuel + 3) config caller.interpretation.environment contextId [.byVal expression] [.register resultTy] origin state =
              (finishActivation config.layout activation [resultTy] origin
                (execActivationBody (fuel + 1) config activation [(parameter.var, value)] frame.source.impl.body) >>= fun carriers =>
                  deliverCarriers (fuel + 2) config.layout [.register resultTy] carriers origin) pushed := by
            simp [invokeCall, getImplementation, contextAt, helperAt, results, evaluated', parameters, enterActivation,
              freshAct, EvalM.get, EvalM.set, bind, pure, Nat.not_le.mpr depth, activationEq, pushed, helperEq]
          rw [invokeStep]
          rw [← helperEq] at bodyResult
          cases body : execActivationBody (fuel + 1) config activation [(parameter.var, value)] frame.source.impl.body pushed with
          | escape address carriers after | jump target kind after => simp [body] at bodyResult
          | stop reason after =>
            simp only [body] at bodyResult
            obtain ⟨nextTypes, nextLive, nextRegions, bodyExtended, bodyProtected, finalWorld⟩ := bodyResult
            simp only [bind, finishActivation, body]
            refine ⟨.callChannels activation [] :: ambient, nextTypes, nextLive, nextRegions,
              (fun root ty found => bodyExtended root ty (boundExtended root ty found)), ?_, finalWorld⟩
            intro root outside
            have unchanged := bodyProtected root (by simpa [act] using outside)
            have different := outside state.nextScope 0
            simpa [registerRootType, act, different] using unchanged
          | ok carriers after =>
            simp only [body] at bodyResult
            obtain ⟨returned, nextTypes, nextLive, nextRegions, equal, represented, bodyExtended, bodyProtected, finalWorld, bodyObserved⟩ := bodyResult
            subst carriers
            have outer' : OwnershipAmbient.withoutActivation activation.act ambient = ambient := by simpa [act] using outer
            have finished := finalWorld.finishEmptyCall config config.module.globals.size after activation ambient nextTypes nextLive nextRegions pending outer'
            simp [bind, finishActivation, body, finishChannels, landCarriersInto, deliverCarriers, pure, channels]
            refine ⟨returned, rfl, represented, nextTypes,
              (fun root ty found => bodyExtended root ty (boundExtended root ty found)), ?_, ⟨nextLive, nextRegions, finished⟩, ?_⟩
            · intro root outside
              have unchanged := bodyProtected root (by simpa [act] using outside)
              have different := outside state.nextScope 0
              simpa [registerRootType, act, different] using unchanged
            · intro root outside
              have bodyOutside := bodyObserved root (by simpa [act] using outside)
              have bindOutside := bindAll_single_outside activation helper.body.scope parameter.var value state boundState
                (by simpa [pushed] using bound) root (by simpa [act] using outside)
              exact ⟨bodyOutside.1.trans bindOutside.1, bodyOutside.2.trans bindOutside.2⟩

theorem mixedLocalRegisterParameter_call_world {expression : Expr} (shape : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar)
    (resultTy : Ty) (resultExpression : Expr)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[parameter]) (results : helper.results = #[⟨resultTy, .register, none⟩])
    (resultScalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (declared : helper.vars[0]? = some descriptor)
    (scalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (callerInitialized : caller.initialized = config.module.globals.size)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (callerSource : AcceptedFrame config accepted caller state types)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller expression descriptor.ty roots typingAfter rootsAfter)
    (form : MixedLocalStatements helper.body.stmts) (tail : helper.body.value = some resultExpression)
    (resultShape : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value origin, .letS id value origin ∈ helper.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, helper.vars[id]? = some localDesc →
        (∃ ty, localDesc.ty = .int ty) ∨ localDesc.ty = .bool)
    (depth : state.activations.length < Goose.Core.maxCallDepth)
    (outer : OwnershipAmbient.withoutActivation state.nextAct ambient = ambient) :
    match invokeCall fuel config caller.interpretation.environment contextId [.byVal expression] [.register resultTy] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions, RootTypesExtend types nextTypes ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local state.nextAct scope id) → nextTypes root = types root) ∧
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => ∃ value nextTypes nextLive nextRegions, carriers = [.register value] ∧
        ValueRepresentation resultTy value ∧ RootTypesExtend types nextTypes ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local state.nextAct scope id) → nextTypes root = types root) ∧
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending
    | _ => False := by
  have result := mixedLocalRegisterParameter_call_observedWorld shape fuel config accepted caller state ambient types live regions pending
    contextId origin context helper parameter descriptor resultTy resultExpression contextAt helperAt parameters results resultScalar declared
    scalar callerInitialized world callerSource roots typingAfter rootsAfter checked form tail resultShape owners scalarOwners depth outer
  cases outcome : invokeCall fuel config caller.interpretation.environment contextId [.byVal expression] [.register resultTy] origin state with
  | stop reason after => simpa only [outcome] using result
  | escape target carriers after => simpa only [outcome] using result
  | jump target kind after => simpa only [outcome] using result
  | ok carriers after =>
    simp only [outcome] at result ⊢
    obtain ⟨value, nextTypes, nextLive, nextRegions, eq, represented, extended, protectedTypes, finalWorld, observations⟩ := result
    exact ⟨value, nextTypes, nextLive, nextRegions, eq, represented, extended, protectedTypes, finalWorld⟩

#print axioms mixedLocalRegisterParameter_call_world
#print axioms mixedLocalRegisterParameter_call_observedWorld
end Goose.Proofs.ConstructionAcceptedExecution
