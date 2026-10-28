import Goose.Proofs.ConstructionAcceptedScalarParameterArgumentInitialized
import Goose.Proofs.ConstructionAcceptedParameterBody
import Goose.Proofs.ConstructionAcceptedNestedActivation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem mixedLocalScalarParameter_call_world {expression : Expr} (shape : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin : Nat) (context : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[parameter]) (results : helper.results = #[])
    (declared : helper.vars[0]? = some descriptor)
    (scalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (callerInitialized : caller.initialized = config.module.globals.size)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (callerSource : AcceptedFrame config accepted caller state types)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller expression descriptor.ty roots typingAfter rootsAfter)
    (form : MixedLocalStatements helper.body.stmts) (tail : helper.body.value = none)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value origin, .letS id value origin ∈ helper.body.stmts →
      AcceptedBinaryExpression value → ∀ localDesc, helper.vars[id]? = some localDesc →
        (∃ ty, localDesc.ty = .int ty) ∨ localDesc.ty = .bool)
    (depth : state.activations.length < Goose.Core.maxCallDepth)
    (outer : OwnershipAmbient.withoutActivation state.nextAct ambient = ambient) :
    match invokeCall fuel config caller.interpretation.environment contextId [.byVal expression] [] origin state with
    | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after nextAmbient nextTypes nextLive nextRegions pending
    | .ok carriers after => carriers = [] ∧ ∃ nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after ambient nextTypes nextLive nextRegions pending
    | _ => False := by
  cases fuel with
  | zero =>
    simp only [invokeCall, timeout, EvalM.stop]
    exact ⟨ambient, types, live, regions, callerInitialized ▸ world⟩
  | succ fuel =>
    have arguments := evalArguments_scalarParameter_body_initialized shape fuel config accepted caller state ambient types live
      regions pending contextId context helper parameter descriptor contextAt helperAt parameters results declared scalar
      callerInitialized world callerSource roots typingAfter rootsAfter checked
    cases evaluated : evalArguments fuel config caller.interpretation.environment helper.vars helper.params.toList [.byVal expression] state with
    | escape address carriers after | jump target kind after => simp [evaluated] at arguments
    | stop reason after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at arguments
      have same := arguments.1
      subst after
      simp [invokeCall, getImplementation, contextAt, helperAt, results, evaluated, bind, pure]
      exact ⟨ambient, types, live, regions, callerInitialized ▸ world⟩
    | ok values after =>
      simp only [evaluated, Goose.Proofs.Exit.stepState] at arguments
      have same := arguments.1
      subst after
      obtain ⟨value, valuesEq, frame, activation, boundState, helperEq, initialized, phase, environment, act, scopes,
        channels, fresh, freshScope, bound, boundWorld, boundSource, position⟩ := arguments.2
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
          have frameForm : MixedLocalStatements frame.source.impl.body.stmts := by simpa [helperEq] using form
          have frameTail : frame.source.impl.body.value = none := by simpa [helperEq] using tail
          have frameResults : frame.source.impl.results = #[] := by simpa [helperEq] using results
          have frameOwners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ frame.source.impl.body.stmts →
              (frame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)) := by
            intro declaration member
            exact (by simpa [helperEq] using owners declaration (by simpa [helperEq] using member))
          have frameScalar : ∀ id expression origin, .letS id expression origin ∈ frame.source.impl.body.stmts →
              AcceptedBinaryExpression expression → ∀ descriptor, frame.source.impl.vars[id]? = some descriptor →
                (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
            intro id expression origin member shape descriptor declared
            apply scalarOwners id expression origin (by simpa [helperEq] using member) shape descriptor
            simpa [helperEq] using declared
          have bodyResult := mixedLocal_boundBody_world fuel config accepted frame activation [(parameter.var, value)] pushed
            boundState ambient (registerRootType types (.local activation.act state.nextScope 0) descriptor.ty)
            (fun other => other = .local activation.act state.nextScope 0 ∨ live other) regions pending contextId
            environment channels frameResults frameTail phase initialized (by simpa [helperEq, pushed] using bound)
            (by simpa [pushed] using boundWorld) (by simpa [pushed] using boundSource)
            (by simpa [helperEq, pushed] using position) frameForm frameOwners frameScalar
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
          have activationEq : activation = ⟨context.impl, state.nextAct, helper.vars, [], []⟩ := by
            cases activation with
            | mk implementation actualAct actualVars actualScopes actualChannels =>
              simp only at implementationId act vars scopes channels
              cases implementationId; cases act; cases vars; cases scopes; cases channels; rfl
          have evaluated' : evalArguments (fuel + 2) config caller.interpretation.environment helper.vars [parameter]
              [.byVal expression] state = .ok [value] state := by
            simpa [parameters, Nat.add_assoc] using evaluated
          have invokeStep : invokeCall (fuel + 3) config caller.interpretation.environment contextId [.byVal expression] [] origin state =
              (finishActivation config.layout activation [] origin
                (execActivationBody (fuel + 1) config activation [(parameter.var, value)] frame.source.impl.body) >>= fun carriers =>
                  deliverCarriers (fuel + 2) config.layout [] carriers origin) pushed := by
            simp [invokeCall, getImplementation, contextAt, helperAt, results, evaluated', parameters, enterActivation,
              freshAct, EvalM.get, EvalM.set, bind, pure, Nat.not_le.mpr depth, activationEq, pushed, helperEq]
          rw [invokeStep]
          cases body : execActivationBody (fuel + 1) config activation [(parameter.var, value)] frame.source.impl.body pushed with
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
            have outer' : OwnershipAmbient.withoutActivation activation.act ambient = ambient := by simpa [act] using outer
            have finished := finalWorld.finishEmptyCall config config.module.globals.size after activation ambient nextTypes nextLive nextRegions pending outer'
            simp [bind, finishActivation, body, finishChannels, landCarriersInto, deliverCarriers, pure, channels]
            exact ⟨nextTypes, nextLive, nextRegions, finished⟩

#print axioms mixedLocalScalarParameter_call_world
end Goose.Proofs.ConstructionAcceptedExecution
