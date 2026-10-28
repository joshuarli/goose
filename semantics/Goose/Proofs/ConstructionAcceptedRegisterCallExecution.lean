import Goose.Proofs.ConstructionAcceptedCalleeBodyComplete
import Goose.Proofs.ConstructionAcceptedCallCheckedEffects
import Goose.Proofs.ConstructionAcceptedCalleeFrame
import Goose.Proofs.ConstructionAcceptedRegisterResultTyping

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem invokeCall_zeroArgument_register_transition (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (target : Nat) (context : Context) (implementation : Impl) (ty : Ty) (origin : Nat) (state : ExecutionState)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨ty, .register, none⟩]) :
    let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
    let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    invokeCall (fuel + 2) config environment target [] [.register ty] origin state =
      if state.activations.length ≥ Goose.Core.maxCallDepth then .stop .timeout state
      else (do let carriers ← enterActivation (fuel + 1) config activation [] implementation.body origin
               deliverCarriers (fuel + 1) config.layout [.register ty] carriers origin) pushed := by
  by_cases depth : state.activations.length ≥ Goose.Core.maxCallDepth
  · simp [invokeCall, getImplementation, contextAt, implementationAt, parameters, results,
      evalArguments, depth, timeout, EvalM.stop, EvalM.get, EvalM.set, bind, pure]
  · simp [invokeCall, getImplementation, contextAt, implementationAt, parameters, results,
      evalArguments, depth, freshAct, EvalM.get, EvalM.set, bind, pure]

theorem invokeCall_scalarLocal_prefix (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (ty : Ty) (origin : Nat) (scope : Nat)
    (statements : List Stmt) (expression : Expr) (summary : Summary)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (body : implementation.body = ⟨scope, statements, some expression⟩)
    (known : implementation.summary = .known summary)
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (form : ScalarLocalStatements statements) (tailForm : AcceptedBinaryExpression expression)
    (scalarLocals : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
      implementation.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config caller.interpretation.environment target [] [.register ty] origin state
      RootTypesExtend types nextTypes ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True
       | .escape .. | .jump .. => False) := by
  have clear : FutureGlobalsClear config caller.initialized state := source.futureGlobals
  cases fuel with
  | zero =>
    simp only [invokeCall, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨types, live, ambient, (fun _ _ found => found), world, clear, trivial⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      simp only [invokeCall, getImplementation, contextAt, implementationAt, parameters, results, evalArguments,
        timeout, EvalM.stop, bind, pure, Goose.Proofs.Exit.stepState]
      exact ⟨types, live, ambient, (fun _ _ found => found), world, clear, trivial⟩
    | succ fuel =>
      have transition := invokeCall_zeroArgument_register_transition fuel config caller.interpretation.environment target context
        implementation ty origin state contextAt implementationAt parameters results
      by_cases depth : state.activations.length ≥ Goose.Core.maxCallDepth
      · simp only [depth, ↓reduceIte] at transition
        rw [transition]
        exact ⟨types, live, ambient, (fun _ _ found => found), world, clear, trivial⟩
      · simp only [depth, ↓reduceIte] at transition
        let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
        let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
        obtain ⟨frame, phase, impl, initialized, interpretation, frameBody, cursor, frameSource, position, frameWorld,
          bodyTypes, declared, typed⟩ := acceptedZeroArgumentRegisterCallee config accepted caller state ambient types live regions pending
            target context implementation ty source world contextAt implementationAt parameters
        have scopeEmpty : frame.interpretation.environment.scopes = [] := by rw [interpretation]; rfl
        have channelEq : frame.interpretation.environment.channels = [.register ty] := by rw [interpretation]; rfl
        have bodyEq : frame.source.impl.body = ⟨scope, statements, some expression⟩ := by simpa [impl] using body
        have bodyPosition : SourcePosition accepted frame (.block ⟨scope, statements, some expression⟩) := by
          simpa [bodyEq] using position
        have effectAvailable := checked.zeroArgument_calleeFrame_effects accepted caller frame target context implementation activation origin
          ty roots typingAfter rootsAfter source.compatible frameSource.compatible contextAt implementationAt parameters summary known
          phase impl interpretation initialized frameBody
        have localScalar : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
            frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
          intro id expression origin member descriptor present
          apply scalarLocals id expression origin member descriptor
          simpa [impl] using present
        have tailPresent : implementation.body.value.isSome = true := by simp [body, Block.value]
        obtain ⟨bodyDeclared, validatedType⟩ := validated_scalarRegister_body_typing config.module context.impl implementation
          accepted.accepted implementationAt ty results scalarTy tailPresent
        have actualType : ∃ declared, typeBlock frame.typingFuel frame.typing ⟨scope, statements, some expression⟩ frame.typingCounter =
            .ok ([ty], declared) := by
          refine ⟨bodyDeclared, ?_⟩
          conv => lhs; rw [← frameBody]
          simpa [implementationBodyFrame, impl, body, parameters] using validatedType
        have actualParameters : frame.source.impl.params = #[] := by simpa [impl] using parameters
        obtain ⟨nextTypes, nextLive, extend, bodyWorld, bodyClear, bodyResult⟩ :=
          execActivationBody_scalarLocal_prefix fuel config accepted frame target pushed (.callChannels activation [] :: ambient)
            types live regions pending scope statements expression ty frameWorld frameSource phase actualParameters scopeEmpty cursor frameBody
            bodyEq channelEq bodyPosition form tailForm localScalar actualType (by simpa [bodyEq] using effectAvailable)
        have sameEnvironment : frame.interpretation.environment = activation := by rw [interpretation]; rfl
        have calleeAt : config.module.impls[activation.implementation]? = some implementation := by
          simpa [activation] using implementationAt
        cases execution : execActivationBody fuel config activation [] ⟨scope, statements, some expression⟩ pushed with
        | stop reason after =>
          simp only [sameEnvironment, execution, Goose.Proofs.Exit.stepState] at bodyWorld bodyClear bodyResult
          have entered : enterActivation (fuel + 1) config activation [] implementation.body origin pushed = .stop reason after := by
            simp [enterActivation, calleeAt, body, finishActivation, execution]
          have callRun : invokeCall (fuel + 2) config caller.interpretation.environment target [] [.register ty] origin state =
              .stop reason after := by
            rw [transition]
            change (do let carriers ← enterActivation (fuel + 1) config activation [] implementation.body origin
                       deliverCarriers (fuel + 1) config.layout [.register ty] carriers origin) pushed = .stop reason after
            simp only [bind, entered]
          rw [callRun]
          exact ⟨nextTypes, nextLive, .callChannels activation [] :: ambient, extend, initialized ▸ bodyWorld,
            initialized ▸ bodyClear, trivial⟩
        | escape address carriers after | jump destination kind after =>
          simp [sameEnvironment, execution] at bodyResult
        | ok carriers after =>
          simp only [sameEnvironment, execution, Goose.Proofs.Exit.stepState] at bodyWorld bodyClear bodyResult
          obtain ⟨value, rfl, represented⟩ := bodyResult
          have finished := finishActivation_register_normal config frame.initialized activation ambient nextTypes nextLive regions pending
            ty origin (execActivationBody fuel config activation [] ⟨scope, statements, some expression⟩) pushed after value
            rfl execution bodyWorld bodyClear
          obtain ⟨finishedRun, finishedWorld, finishedClear⟩ := finished
          have entered : enterActivation (fuel + 1) config activation [] implementation.body origin pushed =
              .ok [.register value] { after with activations := after.activations.filter (fun current => current.act != activation.act) } := by
            simpa [enterActivation, calleeAt, results, body] using finishedRun
          have callRun : invokeCall (fuel + 2) config caller.interpretation.environment target [] [.register ty] origin state =
              .ok [.register value] { after with activations := after.activations.filter (fun current => current.act != activation.act) } := by
            rw [transition]
            change (do let carriers ← enterActivation (fuel + 1) config activation [] implementation.body origin
                       deliverCarriers (fuel + 1) config.layout [.register ty] carriers origin) pushed = _
            simpa only [bind, entered] using deliverCarriers_register (fuel + 1) config ty value origin
              { after with activations := after.activations.filter (fun current => current.act != activation.act) }
          rw [callRun]
          exact ⟨nextTypes, nextLive, ambient, extend, initialized ▸ finishedWorld, initialized ▸ finishedClear, value, rfl, represented⟩

#print axioms invokeCall_scalarLocal_prefix
#print axioms invokeCall_zeroArgument_register_transition
end Goose.Proofs.ConstructionAcceptedExecution
