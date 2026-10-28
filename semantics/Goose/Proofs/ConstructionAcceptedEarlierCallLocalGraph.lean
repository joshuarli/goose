import Goose.Proofs.ConstructionAcceptedEarlierScalarCall
import Goose.Proofs.ConstructionAcceptedRecursiveRegisterCall
import Goose.Proofs.ConstructionAcceptedCallLocalCallee

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

def RegisterCallGraphWithCallLocals (config : EvalConfig) (ty : Ty) : Prop :=
  ∀ (target : Nat) (context : Context) (implementation : Impl), config.module.contexts[target]? = some context →
    config.module.impls[context.impl]? = some implementation → implementation.params = #[] →
    implementation.results = #[⟨ty, .register, none⟩] →
    RegisterCalleeFormWithLocals config ty implementation ∨
      ∃ summary scope id innerTarget callOrigin statementOrigin rest expression innerContext innerCallee,
        implementation.summary = .known summary ∧
        implementation.body = ⟨scope, .letS id (.call innerTarget [] callOrigin) statementOrigin :: rest, some expression⟩ ∧
        ScalarLocalStatements rest ∧ AcceptedBinaryExpression expression ∧
        (∀ descriptor, implementation.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) ∧
        (∀ id expression origin, .letS id expression origin ∈ rest → ∀ descriptor,
          implementation.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) ∧
        config.module.contexts[innerTarget]? = some innerContext ∧ config.module.impls[innerContext.impl]? = some innerCallee ∧
        innerCallee.params = #[] ∧ innerCallee.results = #[⟨ty, .register, none⟩]

theorem invokeCall_recursive_register_callLocal_earlier (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (ty : Ty) (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool) (graph : RegisterCallGraphWithCallLocals config ty) :
    ∀ (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target : Nat) (context : Context) (implementation : Impl) (origin : Nat)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (results : implementation.results = #[⟨ty, .register, none⟩])
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter),
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config caller.interpretation.environment target [] [.register ty] origin state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations state.nextAct state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro caller state ambient types live regions pending target context implementation origin world source contextAt implementationAt parameters results roots typingAfter rootsAfter checked
    rcases graph target context implementation contextAt implementationAt parameters results with existing | callLocal
    ·
      obtain ⟨summary, known, form | form⟩ := existing
      · obtain ⟨scope, statements, expression, body, statementsForm, tailForm, locals⟩ := form
        exact invokeCall_scalarLocal_prefix_earlier fuel config accepted caller state ambient types live regions pending target context implementation ty origin
          scope statements expression summary world source contextAt implementationAt parameters results body known scalar statementsForm tailForm locals
          roots typingAfter rootsAfter checked
      · obtain ⟨scope, statements, innerTarget, innerOrigin, innerContext, innerCallee, body, statementsForm, locals, innerContextAt, innerCalleeAt, innerParameters, innerResults⟩ := form
        cases fuel with
        | zero =>
          simp only [invokeCall, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
          exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source.futureGlobals, EarlierCallerObservations.refl state.nextAct state types, trivial⟩
        | succ fuel =>
          cases fuel with
          | zero =>
            simp only [invokeCall, getImplementation, contextAt, implementationAt, parameters, results, evalArguments,
              timeout, EvalM.stop, bind, pure, Goose.Proofs.Exit.stepState]
            exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source.futureGlobals, EarlierCallerObservations.refl state.nextAct state types, trivial⟩
          | succ fuel =>
            let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
            let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
            obtain ⟨frame, phase, impl, initialized, interpretation, frameBody, cursor, frameSource, position, frameWorld,
              bodyTypes, declared, typed⟩ := acceptedZeroArgumentRegisterCallee config accepted caller state ambient types live regions pending
                target context implementation ty source world contextAt implementationAt parameters
            have scopes : frame.interpretation.environment.scopes = [] := by rw [interpretation]; rfl
            have channels : frame.interpretation.environment.channels = [.register ty] := by rw [interpretation]; rfl
            have bodyEq : frame.source.impl.body = ⟨scope, statements, some (.call innerTarget [] innerOrigin)⟩ := by simpa [impl] using body
            have bodyPosition : SourcePosition accepted frame (.block ⟨scope, statements, some (.call innerTarget [] innerOrigin)⟩) := by simpa [bodyEq] using position
            have actualParameters : frame.source.impl.params = #[] := by simpa [impl] using parameters
            have requests : frame.typing.resultRequests = [.register] := by
              have equal := congrArg (fun f : ConstructionSourceFrame => f.typing.resultRequests) frameBody
              simpa [implementationBodyFrame, impl, results] using equal.symm
            have typingModule : frame.typing.module = config.module := by
              have equal := congrArg (fun f : ConstructionSourceFrame => f.typing.module) frameBody
              simpa [implementationBodyFrame] using equal.symm
            have checkedEffects := checked.zeroArgument_calleeFrame_effects accepted caller frame target context implementation activation origin
              ty roots typingAfter rootsAfter source.compatible frameSource.compatible contextAt implementationAt parameters summary known
              phase impl interpretation initialized frameBody
            have frameEnv : frame.interpretation.environment = activation := by rw [interpretation]; rfl
            have bodySafe : ∃ nextTypes nextLive nextAmbient,
                let outcome := execActivationBody fuel config activation [] implementation.body pushed
                RootTypesExtend types nextTypes ∧ pushed.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
                pushed.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
                AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
                FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
                EarlierCallerObservations state.nextAct pushed (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
                (match outcome with
                 | .ok carriers _ => nextAmbient = .callChannels activation [] :: ambient ∧
                    ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
                 | .stop .. => True | .escape .. | .jump .. => False) := by
              cases fuel with
              | zero =>
                simp only [execActivationBody, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
                exact ⟨types, live, .callChannels activation [] :: ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, initialized ▸ frameWorld, initialized ▸ frameSource.futureGlobals, EarlierCallerObservations.refl state.nextAct pushed types, trivial⟩
              | succ fuel =>
                cases fuel with
                | zero =>
                  obtain ⟨scopeWorld, scopeSource, _⟩ := acceptedCalleeBodyScope config accepted frame target pushed
                    (.callChannels activation [] :: ambient) types live regions pending frameWorld frameSource phase actualParameters scopes cursor
                  rw [bodyEq] at scopeWorld scopeSource
                  simp only [Block.scope] at scopeWorld scopeSource
                  rw [body]
                  simp only [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll,
                    List.forIn_nil, execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
                  exact ⟨types, live, .callChannels activation [] :: ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_succ _,
                    (by simpa [entryStatementsFrame, blockStatementsFrame, frameBody, bodyEq, Block.scope, frameEnv, ownershipResultScopeState, initialized] using scopeWorld),
                    (by simpa [entryStatementsFrame, blockStatementsFrame, frameBody, bodyEq, Block.scope, frameEnv, ownershipResultScopeState, initialized, FutureGlobalsClear] using scopeSource.futureGlobals),
                    EarlierCallerObservations.enterScope state.nextAct activation scope pushed types, trivial⟩
                | succ fuel =>
                  have localScalar : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
                      frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
                    intro id expression origin member descriptor present
                    apply locals id expression origin member descriptor
                    simpa [impl] using present
                  have safe := execActivationBody_scalarLocal_registerCall_earlier fuel config accepted frame target pushed
                    (.callChannels activation [] :: ambient) types live regions pending state.nextAct scope statements innerTarget innerOrigin innerContext innerCallee ty
                    frameWorld frameSource phase actualParameters scopes cursor frameBody bodyEq (by rw [interpretation]; exact Nat.le_refl _)
                    channels bodyPosition statementsForm localScalar
                    (by simpa [typingModule] using innerContextAt) (by simpa [typingModule] using innerCalleeAt) innerResults scalar requests
                    (by simpa [bodyEq] using checkedEffects)
                    (by
                      intro nextFrame after currentTypes currentLive roots typingAfter rootsAfter environment currentWorld currentSource checked
                      have bound : state.nextAct ≤ after.nextAct := by
                        have previous := currentSource.frontier.1
                        have act : nextFrame.interpretation.environment.act = state.nextAct := by rw [environment, interpretation]; rfl
                        rw [act] at previous
                        exact Nat.le_of_lt previous
                      obtain ⟨nt, nl, na, ext, ac, sc, w, cl, obs, res⟩ :=
                        ih fuel (by omega) nextFrame after (.callChannels activation [] :: ambient) currentTypes currentLive regions pending
                          innerTarget innerContext innerCallee innerOrigin currentWorld currentSource innerContextAt innerCalleeAt innerParameters innerResults
                          roots typingAfter rootsAfter checked
                      exact ⟨nt, nl, na, ext, ac, sc, w, cl, obs.restrict bound, res⟩)
                  have fuelEq : fuel + 2 = fuel + 1 + 1 := by omega
                  obtain ⟨nt, nl, na, ext, ac, sc, w, cl, obs, res⟩ := safe
                  refine ⟨nt, nl, na, ext, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · simpa only [frameEnv, body, initialized, fuelEq] using ac
                  · simpa only [frameEnv, body, initialized, fuelEq] using sc
                  · simpa only [frameEnv, body, initialized, fuelEq] using w
                  · simpa only [frameEnv, body, initialized, fuelEq] using cl
                  · simpa only [frameEnv, body, fuelEq] using obs
                  · simp only [frameEnv, body, initialized, fuelEq] at res
                    cases execution : execActivationBody (fuel + 1 + 1) config activation []
                      ⟨scope, statements, some (.call innerTarget [] innerOrigin)⟩ pushed <;>
                      simpa [body, execution] using res
  
            exact invokeCall_register_compose_earlier fuel config caller.initialized caller.interpretation.environment state ambient types live regions pending
              state.nextAct target context implementation ty origin world source.futureGlobals contextAt implementationAt parameters results bodySafe
    · obtain ⟨summary, scope, id, innerTarget, callOrigin, statementOrigin, rest, expression, innerContext, innerCallee,
        known, body, restForm, tailForm, scalarLocal, scalarRest, innerContextAt, innerCalleeAt, innerParameters, innerResults⟩ := callLocal
      cases fuel with
      | zero =>
        simp only [invokeCall, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
        exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source.futureGlobals,
          EarlierCallerObservations.refl state.nextAct state types, trivial⟩
      | succ fuel =>
        cases fuel with
        | zero =>
          simp only [invokeCall, getImplementation, contextAt, implementationAt, parameters, results, evalArguments,
            timeout, EvalM.stop, bind, pure, Goose.Proofs.Exit.stepState]
          exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source.futureGlobals,
            EarlierCallerObservations.refl state.nextAct state types, trivial⟩
        | succ fuel =>
          let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
          let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
          obtain ⟨frame, phase, impl, initialized, interpretation, frameBody, cursor, frameSource, position, frameWorld,
            bodyTypes, declared, typed⟩ := acceptedZeroArgumentRegisterCallee config accepted caller state ambient types live regions pending
              target context implementation ty source world contextAt implementationAt parameters
          have scopeEmpty : frame.interpretation.environment.scopes = [] := by rw [interpretation]; rfl
          have channelEq : frame.interpretation.environment.channels = [.register ty] := by rw [interpretation]; rfl
          have bodyEq : frame.source.impl.body = ⟨scope, .letS id (.call innerTarget [] callOrigin) statementOrigin :: rest, some expression⟩ := by simpa [impl] using body
          have bodyPosition : SourcePosition accepted frame (.block ⟨scope, .letS id (.call innerTarget [] callOrigin) statementOrigin :: rest, some expression⟩) := by simpa [bodyEq] using position
          have effectAvailable := checked.zeroArgument_calleeFrame_effects accepted caller frame target context implementation activation origin
            ty roots typingAfter rootsAfter source.compatible frameSource.compatible contextAt implementationAt parameters summary known
            phase impl interpretation initialized frameBody
          have localScalar : ∀ descriptor, frame.source.impl.vars[id]? = some descriptor →
              (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
            intro descriptor present
            apply scalarLocal descriptor
            simpa [impl] using present
          have restScalar : ∀ id expression origin, .letS id expression origin ∈ rest → ∀ descriptor,
              frame.source.impl.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool := by
            intro id expression origin member descriptor present
            apply scalarRest id expression origin member descriptor
            simpa [impl] using present
          have tailPresent : implementation.body.value.isSome = true := by simp [body, Block.value]
          obtain ⟨bodyDeclared, validatedType⟩ := validated_scalarRegister_body_typing config.module context.impl implementation
            accepted.accepted implementationAt ty results scalar tailPresent
          have actualType : ∃ declared, typeBlock frame.typingFuel frame.typing
              ⟨scope, .letS id (.call innerTarget [] callOrigin) statementOrigin :: rest, some expression⟩ frame.typingCounter = .ok ([ty], declared) := by
            refine ⟨bodyDeclared, ?_⟩
            conv => lhs; rw [← frameBody]
            simpa [implementationBodyFrame, impl, body, parameters] using validatedType
          have actualParameters : frame.source.impl.params = #[] := by simpa [impl] using parameters
          have sameEnvironment : frame.interpretation.environment = activation := by rw [interpretation]; rfl
          obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopeClocks, bodyWorld, bodyClear, observed, bodyResult⟩ :=
            execActivationBody_callLocal_scalarTail fuel config accepted frame target pushed (.callChannels activation [] :: ambient)
              types live regions pending state.nextAct scope id innerTarget callOrigin statementOrigin rest expression ty innerContext innerCallee
              frameWorld frameSource phase actualParameters scopeEmpty cursor frameBody bodyEq (by rw [interpretation]; exact Nat.le_refl _)
              (by simp [pushed]) channelEq bodyPosition tailForm restForm localScalar restScalar actualType (by simpa [bodyEq] using effectAvailable)
              innerContextAt innerCalleeAt innerParameters innerResults scalar (by
                intro callFuel lower nextFrame before currentTypes currentLive roots typingAfter rootsAfter currentWorld currentSource checked
                obtain ⟨nt, nl, na, ext, ac, sc, w, cl, obs, res⟩ := ih callFuel (by omega) nextFrame before
                  (.callChannels activation [] :: ambient) currentTypes currentLive regions pending innerTarget innerContext innerCallee callOrigin
                  currentWorld currentSource innerContextAt innerCalleeAt innerParameters innerResults roots typingAfter rootsAfter checked
                exact ⟨nt, nl, na, ext, ac, sc, w, currentSource.afterEarlierObservations ac sc obs, cl, obs, res⟩)
          have bodySafe : ∃ nextTypes nextLive nextAmbient,
              let outcome := execActivationBody fuel config activation [] implementation.body pushed
              RootTypesExtend types nextTypes ∧ pushed.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
              pushed.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
              AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
              FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
              EarlierCallerObservations state.nextAct pushed (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
              (match outcome with
               | .ok carriers _ => nextAmbient = .callChannels activation [] :: ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
               | .stop .. => True | .escape .. | .jump .. => False) := by
            refine ⟨nextTypes, nextLive, nextAmbient, extend, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simpa only [sameEnvironment, body] using acts
            · simpa only [sameEnvironment, body] using scopeClocks
            · simpa only [sameEnvironment, body, initialized] using bodyWorld
            · simpa only [sameEnvironment, body, initialized] using bodyClear
            · simpa only [sameEnvironment, body] using observed
            · cases execution : execActivationBody fuel config activation [] implementation.body pushed with
              | ok carriers after =>
                have execution' : execActivationBody fuel config activation [] ⟨scope, .letS id (.call innerTarget [] callOrigin) statementOrigin :: rest, some expression⟩ pushed = .ok carriers after := by simpa [body] using execution
                simp only [sameEnvironment, execution'] at bodyResult
                simpa [execution] using bodyResult
              | stop reason after => simp [execution]
              | escape address carriers after | jump destination kind after =>
                rw [body] at execution
                simp [sameEnvironment, execution] at bodyResult
          exact invokeCall_register_compose_earlier fuel config caller.initialized caller.interpretation.environment state ambient types live regions pending
            state.nextAct target context implementation ty origin world source.futureGlobals contextAt implementationAt parameters results bodySafe

#print axioms invokeCall_recursive_register_callLocal_earlier
end Goose.Proofs.ConstructionAcceptedExecution
