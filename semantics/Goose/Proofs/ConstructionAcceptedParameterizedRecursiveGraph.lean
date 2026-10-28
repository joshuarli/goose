import Goose.Proofs.ConstructionAcceptedParameterizedGraph
import Goose.Proofs.ConstructionAcceptedParameterIdentityWorld
import Goose.Proofs.ConstructionAcceptedParameterizedTailCompose
import Goose.Proofs.ConstructionAcceptedSingleArgumentCompose
import Goose.Proofs.ConstructionAcceptedUnaryArgumentSource
import Goose.Proofs.ConstructionAcceptedIdentityUnaryCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem invokeCall_parameterizedGeneralGraph_allFuel (fuel : Nat) (config : EvalConfig) (integer : Goose.Core.IntTy)
    (accepted : AcceptedModule config) (graph : ParameterizedRegisterGraph config integer)
    (argumentGraph : RegisterCallGraphWithCallLocals config (.int integer)) :
    ∀ (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (implementation : Impl) (parameter : Param) (argument : Expr)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (mode : parameter.mode = .byValue)
    (results : implementation.results = #[⟨.int integer, .register, none⟩])
    (form : UnaryRegisterExpression config integer argument) (checkFuel : Nat) (nesting : caller.typingFuel = checkFuel + 2)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [.byVal argument] origin) (.int integer) roots typingAfter rootsAfter),
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config caller.interpretation.environment target [.byVal argument] [.register (.int integer)] origin state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted caller (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations state.nextAct state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation (.int integer) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro caller state ambient types live regions pending target origin context implementation parameter argument world source
      contextAt implementationAt parameters mode results form checkFuel nesting roots typingAfter rootsAfter checked
    rcases graph target context implementation parameter contextAt implementationAt parameters mode results with identity | tail
    · obtain ⟨descriptor, declared, descriptorTy, body⟩ := identity
      have parameterId := validated_parameter_variable config.module context.impl implementation 0 parameter accepted.accepted implementationAt (by simp [parameters])
      have parameterDeclared : implementation.vars[parameter.var]? = some descriptor := by simpa [parameterId] using declared
      exact invokeCall_identityUnary_allFuel caller state ambient types live regions pending target origin context implementation parameter descriptor
        argument integer checkFuel fuel form argumentGraph world source contextAt implementationAt parameters mode parameterDeclared descriptorTy results body nesting
        (.int integer) roots typingAfter rootsAfter checked
    ·
      obtain ⟨descriptor, summary, tailTarget, tailOrigin, tailContext, tailCallee, tailParameter, tailDescriptor, tailArgument,
        declared, descriptorTy, known, noParameters, body, tailContextAt, tailCalleeAt, tailParameters, tailMode,
        tailDeclared, tailDescriptorTy, tailResults, tailForm⟩ := tail
      have parameterId := validated_parameter_variable config.module context.impl implementation 0 parameter accepted.accepted implementationAt (by simp [parameters])
      have parameterDeclared : implementation.vars[parameter.var]? = some descriptor := by simpa [parameterId] using declared
      cases fuel with
      | zero =>
        simp only [invokeCall, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
        exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source, source.futureGlobals,
          EarlierCallerObservations.refl _ _ _, trivial⟩
      | succ fuel =>
        obtain ⟨argumentTypes, argumentLive, argumentAmbient, extend, acts, scopes, argumentWorld, argumentSource, clear, observed, result⟩ :=
          evalArguments_unaryRegisterExpression_fromChecker caller state ambient types live regions pending target origin context implementation parameter
            descriptor argument integer checkFuel fuel form argumentGraph world source contextAt implementationAt parameters mode parameterDeclared descriptorTy nesting
            (.int integer) roots typingAfter rootsAfter checked
        cases evaluated : evalArguments fuel config caller.interpretation.environment implementation.vars [parameter] [.byVal argument] state with
        | stop reason after =>
          simp only [evaluated, Goose.Proofs.Exit.stepState] at acts scopes argumentWorld argumentSource clear observed result
          rw [invokeCall_singleArgument_register_stopped fuel config _ target context implementation parameter (.byVal argument) (.int integer) origin
            state after reason contextAt implementationAt parameters results evaluated]
          exact ⟨argumentTypes, argumentLive, argumentAmbient, extend, acts, scopes, argumentWorld, argumentSource, clear, observed, trivial⟩
        | escape target carriers after | jump target kind after => simp [evaluated] at result
        | ok values after =>
          simp only [evaluated, Goose.Proofs.Exit.stepState] at acts scopes argumentWorld argumentSource clear observed result
          obtain ⟨rfl, value, rfl, representation⟩ := result
          cases fuel with
          | zero => simp [evalArguments, timeout, EvalM.stop] at evaluated
          | succ bodyFuel =>
            have pointers : PointerTypedValue argumentTypes (.int integer) value := by
              cases representation with
              | integer _ number => exact .integer integer number
              | stored _ _ nonfixed _ => cases nonfixed
            have bodySafe :
                let activation : RuntimeActivation := ⟨context.impl, after.nextAct, implementation.vars, [], [.register (.int integer)]⟩
                let pushed := { after with nextAct := after.nextAct + 1, activations := activation :: after.activations }
                ∃ nextTypes nextLive nextAmbient,
                  let outcome := execActivationBody bodyFuel config activation [(parameter.var, value)] implementation.body pushed
                  RootTypesExtend argumentTypes nextTypes ∧ pushed.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
                  pushed.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
                  AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
                  FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
                  EarlierCallerObservations after.nextAct pushed (Goose.Proofs.Exit.stepState outcome) argumentTypes nextTypes ∧
                  (match outcome with
                   | .ok carriers _ => nextAmbient = .callChannels activation [] :: argumentAmbient ∧
                      ∃ value, carriers = [.register value] ∧ ValueRepresentation (.int integer) value
                   | .stop .. => True | .escape .. | .jump .. => False) := by
              obtain ⟨calleeFrame, actual, boundState, tailRoots, tailTypingAfter, tailRootsAfter, sameImpl, initialized, environment,
                act, emptyScopes, channels, activationImpl, activationVars, bound, boundExtended, boundWorld, boundSource, tailChecked⟩ :=
                acceptedSingleByValueBoundCallTail config accepted caller after argumentAmbient argumentTypes argumentLive regions pending
                  target origin context implementation parameter descriptor argument value (.int integer) summary contextAt implementationAt
                  parameters declared (Or.inl ⟨integer, descriptorTy⟩) (by simpa [descriptorTy] using representation)
                  (by simpa [descriptorTy] using pointers) known noParameters results tailTarget tailOrigin tailContext tailCallee [.byVal tailArgument]
                  body tailContextAt tailCalleeAt tailResults (Or.inl ⟨integer, rfl⟩) argumentWorld argumentSource
                  (.int integer) roots typingAfter rootsAfter checked
              have actualEq : actual = (⟨context.impl, after.nextAct, implementation.vars, [], [.register (.int integer)]⟩ : RuntimeActivation) := by
                cases actual
                simp only [RuntimeActivation.mk.injEq] at *
                exact ⟨activationImpl, act, activationVars, emptyScopes, channels⟩
              rw [actualEq] at bound boundExtended boundWorld boundSource
              let activation : RuntimeActivation := ⟨context.impl, after.nextAct, implementation.vars, [], [.register (.int integer)]⟩
              let pushed := { after with nextAct := after.nextAct + 1, activations := activation :: after.activations }
              let root := Goose.Core.RootInst.local after.nextAct after.nextScope 0
              let boundTypes := registerRootType argumentTypes root (.int integer)
              let boundLive := fun other => other = root ∨ argumentLive other
              have bound' : bindAll activation.act pushed.nextScope [(parameter.var, value)]
                  (ownershipResultScopeState activation implementation.body.scope pushed) = .ok () boundState := by
                simpa [activation, pushed] using bound
              have boundWorld' : AcceptedWorld config caller.initialized boundState (.callChannels activation [] :: argumentAmbient)
                  boundTypes boundLive regions pending := by
                simpa [activation, root, boundTypes, boundLive, descriptorTy] using boundWorld
              have extension : RootTypesExtend argumentTypes boundTypes := by simpa [activation, root, boundTypes, descriptorTy] using boundExtended
              have counters := bindAll_single_counters activation implementation.body.scope parameter.var value after boundState
                (by simpa [activation, pushed] using bound)
              have boundObserved : EarlierCallerObservations after.nextAct pushed boundState argumentTypes boundTypes := by
                simpa [activation, pushed, root, boundTypes, parameterId] using
                  bindAll_single_earlier activation implementation.body.scope parameter.var value after boundState argumentTypes (.int integer) after.nextAct
                    (by simp [activation]) (by simpa [activation, pushed] using bound)
              have boundClear : FutureGlobalsClear config caller.initialized boundState := by
                simpa only [FutureGlobalsClear, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, initialized] using boundSource.futureGlobals
              have pushedWorld : AcceptedWorld config caller.initialized pushed (.callChannels activation [] :: argumentAmbient)
                  argumentTypes argumentLive regions pending :=
                acceptedWorld_pushRegisterActivation config caller.initialized after argumentAmbient argumentTypes argumentLive regions pending activation argumentWorld rfl _ rfl
              have pushedClear : FutureGlobalsClear config caller.initialized pushed := by simpa [pushed, FutureGlobalsClear] using argumentSource.futureGlobals
              have low := execActivationBody_boundCall_lowFuel config activation implementation.body.scope [(parameter.var, value)] tailTarget tailOrigin
                [.byVal tailArgument] (.int integer) pushed boundState rfl bound'
              change ∃ nextTypes nextLive nextAmbient, let outcome := execActivationBody bodyFuel config activation [(parameter.var, value)] implementation.body pushed; _
              cases bodyFuel with
              | zero =>
                rw [body, low.1]
                exact ⟨argumentTypes, argumentLive, .callChannels activation [] :: argumentAmbient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _,
                  pushedWorld, pushedClear, EarlierCallerObservations.refl _ _ _, trivial⟩
              | succ bodyFuel =>
                cases bodyFuel with
                | zero =>
                  rw [body, low.2.1]
                  exact ⟨boundTypes, boundLive, .callChannels activation [] :: argumentAmbient, extension,
                    by simpa [pushed, Goose.Proofs.Exit.stepState] using Nat.le_of_eq counters.1.symm,
                    by simp [pushed, Goose.Proofs.Exit.stepState, counters.2], boundWorld', boundClear, boundObserved, trivial⟩
                | succ innerFuel =>
                  let child := entryStatementsFrame config calleeFrame after.nextScope
                  have childWorld : AcceptedWorld config child.initialized boundState (.callChannels activation [] :: argumentAmbient)
                      boundTypes boundLive regions pending := by simpa [child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, initialized] using boundWorld'
                  have childSource : AcceptedFrame config accepted child boundState boundTypes := by simpa [child, boundTypes, root, descriptorTy] using boundSource
                  have childChecked : CheckedValue child (.call tailTarget [.byVal tailArgument] tailOrigin) (.int integer) tailRoots tailTypingAfter tailRootsAfter := by
                    simpa [child] using tailChecked
                  have childFuel : child.typingFuel = 4093 + 2 := by simp [child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]
                  obtain ⟨finalTypes, finalLive, finalAmbient, extension2, nextActs, nextScopes, finalWorld, finalSource, finalClear, nextObserved, result2⟩ :=
                    ih innerFuel (by omega) child boundState (.callChannels activation [] :: argumentAmbient) boundTypes boundLive regions pending
                      tailTarget tailOrigin tailContext tailCallee tailParameter tailArgument childWorld childSource tailContextAt tailCalleeAt
                      tailParameters tailMode tailResults tailForm 4093 childFuel tailRoots tailTypingAfter tailRootsAfter childChecked
                  have frontier : after.nextAct ≤ boundState.nextAct := by omega
                  have innerObserved := nextObserved.restrict frontier
                  have inner : ∃ innerTypes innerLive innerAmbient,
                      let outcome := invokeCall innerFuel config child.interpretation.environment tailTarget [.byVal tailArgument]
                        [.register (.int integer)] tailOrigin boundState
                      RootTypesExtend boundTypes innerTypes ∧ boundState.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
                      boundState.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
                      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) innerAmbient innerTypes innerLive regions pending ∧
                      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
                      EarlierCallerObservations after.nextAct boundState (Goose.Proofs.Exit.stepState outcome) boundTypes innerTypes ∧
                      (match outcome with
                       | .ok carriers _ => innerAmbient = .callChannels activation [] :: argumentAmbient ∧
                           ∃ value, carriers = [.register value] ∧ ValueRepresentation (.int integer) value
                       | .stop .. => True | .escape .. | .jump .. => False) := by
                    exact ⟨finalTypes, finalLive, finalAmbient, extension2, nextActs, nextScopes,
                      (by simpa [child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, initialized] using finalWorld),
                      (by simpa [child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, initialized] using finalClear), innerObserved, result2⟩
                  rw [body]
                  apply execActivationBody_boundCall_earlier innerFuel config caller.initialized activation implementation.body.scope
                    [(parameter.var, value)] tailTarget tailOrigin [.byVal tailArgument] pushed boundState
                    (.callChannels activation [] :: argumentAmbient) argumentTypes boundTypes regions pending (.int integer) after.nextAct rfl
                    (by simp [activation]) bound' extension
                    (by simpa [pushed] using Nat.le_of_eq counters.1.symm) (by simp [pushed, counters.2]) boundObserved
                  have childEnvironment : child.interpretation.environment =
                      { activation with scopes := (implementation.body.scope, pushed.nextScope) :: activation.scopes } := by
                    simp [child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, environment, actualEq,
                      RootInterpretation.enterScope, activation, emptyScopes, sameImpl, pushed]
                  rw [childEnvironment] at inner
                  exact inner
            obtain ⟨finalTypes, finalLive, finalAmbient, extension2, acts2, scopes2, finalWorld, finalClear, observed2, finalResult⟩ :=
              invokeCall_singleArgument_register_compose bodyFuel config caller.initialized caller.interpretation.environment state after argumentAmbient argumentTypes
                argumentLive regions pending after.nextAct target context implementation parameter (.byVal argument) value (.int integer) origin
                argumentWorld clear contextAt implementationAt parameters results evaluated bodySafe
            have finalObserved := observed.trans acts observed2
            have finalActs := Nat.le_trans acts acts2
            have finalScopes := Nat.le_trans scopes scopes2
            exact ⟨finalTypes, finalLive, finalAmbient, (fun root ty found => extension2 root ty (extend root ty found)),
              finalActs, finalScopes, finalWorld, source.afterEarlierObservations finalActs finalScopes finalObserved, finalClear, finalObserved, finalResult⟩


theorem invokeCall_parameterizedGraph_allFuel (fuel : Nat) (config : EvalConfig) (integer : Goose.Core.IntTy)
    (accepted : AcceptedModule config) (graph : ParameterizedRegisterTailGraph config integer)
    (argumentGraph : RegisterCallGraphWithCallLocals config (.int integer)) :
    ∀ (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (implementation : Impl) (parameter : Param) (argument : Expr)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (mode : parameter.mode = .byValue)
    (results : implementation.results = #[⟨.int integer, .register, none⟩])
    (form : UnaryRegisterExpression config integer argument) (checkFuel : Nat) (nesting : caller.typingFuel = checkFuel + 2)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [.byVal argument] origin) (.int integer) roots typingAfter rootsAfter),
    ∃ nextTypes nextLive nextAmbient,
      let outcome := invokeCall fuel config caller.interpretation.environment target [.byVal argument] [.register (.int integer)] origin state
      RootTypesExtend types nextTypes ∧ state.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      state.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      AcceptedFrame config accepted caller (Goose.Proofs.Exit.stepState outcome) nextTypes ∧
      FutureGlobalsClear config caller.initialized (Goose.Proofs.Exit.stepState outcome) ∧
      EarlierCallerObservations state.nextAct state (Goose.Proofs.Exit.stepState outcome) types nextTypes ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation (.int integer) value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  exact invokeCall_parameterizedGeneralGraph_allFuel fuel config integer accepted graph.toGraph argumentGraph

#print axioms invokeCall_parameterizedGeneralGraph_allFuel
#print axioms invokeCall_parameterizedGraph_allFuel
end Goose.Proofs.ConstructionAcceptedExecution
