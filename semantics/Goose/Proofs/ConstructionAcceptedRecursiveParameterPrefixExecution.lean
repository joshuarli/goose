import Goose.Proofs.ConstructionAcceptedRecursiveParameterGraph
import Goose.Proofs.ConstructionAcceptedParameterizedPrefixSource
import Goose.Proofs.ConstructionAcceptedParameterizedCheckedPrefix
import Goose.Proofs.ConstructionAcceptedRecursiveArgumentList
import Goose.Proofs.ConstructionAcceptedParameterizedRecursiveGraph

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

def RecursiveParameterPrefixTailCallee (config : EvalConfig) (integer : Goose.Core.IntTy) (implementation : Impl) : Prop :=
  ∃ descriptor summary target origin context callee parameter tailDescriptor tailSummary argument statements,
    implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧ implementation.summary = .known summary ∧
    implementation.body = ⟨implementation.body.scope, statements, some (.call target [.byVal argument] origin)⟩ ∧
    config.module.contexts[target]? = some context ∧ config.module.impls[context.impl]? = some callee ∧
    callee.params = #[parameter] ∧ parameter.mode = .byValue ∧ callee.vars[parameter.var]? = some tailDescriptor ∧
    tailDescriptor.ty = .int integer ∧ callee.results = #[⟨.int integer, .register, none⟩] ∧
    callee.summary = .known tailSummary ∧ RecursiveArgumentExpression config integer implementation argument ∧ ScalarLocalStatements statements ∧
    (∀ id expression location, .letS id expression location ∈ statements → ∀ descriptor,
      implementation.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)

def RecursiveParameterPrefixGraph (config : EvalConfig) (integer : Goose.Core.IntTy) : Prop :=
  ∀ (target : Nat) (context : Context) (implementation : Impl) (parameter : Param),
    config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some implementation →
    implementation.params = #[parameter] → parameter.mode = .byValue →
    implementation.results = #[⟨.int integer, .register, none⟩] →
    (∃ descriptor, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.body = ⟨implementation.body.scope, [], some (.read (.var 0))⟩) ∨
    (∃ descriptor summary expression, implementation.vars[0]? = some descriptor ∧ descriptor.ty = .int integer ∧
      implementation.summary = .known summary ∧
      implementation.body = ⟨implementation.body.scope, [], some expression⟩ ∧ AcceptedBinaryExpression expression) ∨
      RecursiveParameterPrefixTailCallee config integer implementation


theorem invokeCall_recursiveParameterPrefixGraph_allFuel (fuel : Nat) (config : EvalConfig) (integer : Goose.Core.IntTy)
    (accepted : AcceptedModule config) (graph : RecursiveParameterPrefixGraph config integer)
    :
    ∀ (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (implementation : Impl) (parameter : Param) (argument : Expr)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (mode : parameter.mode = .byValue)
    (results : implementation.results = #[⟨.int integer, .register, none⟩])
    (form : RecursiveArgumentExpression config integer caller.source.impl argument) (checkFuel : Nat) (nesting : caller.typingFuel = checkFuel + 2)
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
    have calls : RecursiveArgumentCallSafety config accepted integer fuel := by
      intro callFuel smaller callerImpl frame before ambient types live regions pending target origin context callee parameter descriptor summary argument
        implementationEq argumentForm contextAt calleeAt parameters mode declared descriptorType results known world source roots typingAfter rootsAfter checked
      have argumentForm' : RecursiveArgumentExpression config integer frame.source.impl argument := by simpa [implementationEq] using argumentForm
      cases depth : frame.typingFuel with
      | zero =>
        have typed := checked.typing
        rw [depth] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ remaining =>
        cases remaining with
        | zero =>
          have typed := checked.typing
          rw [depth] at typed
          simp only [typeExpr, source.compatible.module, contextAt, calleeAt, typeArguments, bind, StateT.bind, Except.bind] at typed
          change Except.error _ = Except.ok _ at typed
          cases typed
        | succ checkFuel =>
          exact ih callFuel smaller frame before ambient types live regions pending target origin context callee parameter argument world source
            contextAt calleeAt parameters mode results argumentForm' checkFuel depth roots typingAfter rootsAfter checked
    rcases graph target context implementation parameter contextAt implementationAt parameters mode results with identity | scalarTail | tail
    · obtain ⟨descriptor, declared, descriptorTy, body⟩ := identity
      have parameterId := validated_parameter_variable config.module context.impl implementation 0 parameter accepted.accepted implementationAt (by simp [parameters])
      have parameterDeclared : implementation.vars[parameter.var]? = some descriptor := by simpa [parameterId] using declared
      apply invokeCall_singleArgument_fromLowerFuel caller state ambient types live regions pending target origin context implementation parameter
        argument integer fuel world source contextAt implementationAt parameters results
      · intro bodyFuel bodyBound argumentState argumentTypes argumentLive argumentAmbient value represented argumentWorld argumentSource
        have pointers : PointerTypedValue argumentTypes (.int integer) value := by
          cases represented with
          | integer _ number => exact .integer integer number
          | stored _ _ nonfixed _ => cases nonfixed
        exact identityParameterBody_partial bodyFuel config accepted caller argumentState argumentAmbient argumentTypes argumentLive regions pending target context
          implementation parameter descriptor value (.int integer) contextAt implementationAt parameters declared body (Or.inl ⟨integer, descriptorTy⟩)
          descriptorTy represented pointers argumentWorld argumentSource
      · intro argumentFuel argumentBound
        exact evalArguments_recursiveArgument_fromChecker caller state ambient types live regions pending target origin context implementation parameter
          descriptor argument integer checkFuel argumentFuel fuel form calls (by omega) world source contextAt implementationAt parameters mode parameterDeclared
          descriptorTy nesting (.int integer) roots typingAfter rootsAfter checked
    · obtain ⟨descriptor, summary, tailExpression, declared, descriptorTy, known, body, tailForm⟩ := scalarTail
      have parameterId := validated_parameter_variable config.module context.impl implementation 0 parameter accepted.accepted implementationAt (by simp [parameters])
      have parameterDeclared : implementation.vars[parameter.var]? = some descriptor := by simpa [parameterId] using declared
      apply invokeCall_singleArgument_fromLowerFuel caller state ambient types live regions pending target origin context implementation parameter
        argument integer fuel world source contextAt implementationAt parameters results
      · intro bodyFuel bodyBound argumentState argumentTypes argumentLive argumentAmbient value represented argumentWorld argumentSource
        have pointers : PointerTypedValue argumentTypes (.int integer) value := by
          cases represented with
          | integer _ number => exact .integer integer number
          | stored _ _ nonfixed _ => cases nonfixed
        exact scalarParameterBody_parameterSummary_partial bodyFuel config accepted caller argumentState argumentAmbient argumentTypes argumentLive regions pending
          target origin context implementation parameter descriptor argument tailExpression value (.int integer) summary contextAt implementationAt
          parameters declared body tailForm (Or.inl ⟨integer, descriptorTy⟩) descriptorTy represented pointers known results
          argumentWorld argumentSource (.int integer) roots typingAfter rootsAfter checked
      · intro argumentFuel argumentBound
        exact evalArguments_recursiveArgument_fromChecker caller state ambient types live regions pending target origin context implementation parameter
          descriptor argument integer checkFuel argumentFuel fuel form calls (by omega) world source contextAt implementationAt parameters mode parameterDeclared
          descriptorTy nesting (.int integer) roots typingAfter rootsAfter checked
    ·
      obtain ⟨descriptor, summary, tailTarget, tailOrigin, tailContext, tailCallee, tailParameter, tailDescriptor, tailSummary, tailArgument, statements,
        declared, descriptorTy, known, body, tailContextAt, tailCalleeAt, tailParameters, tailMode,
        tailDeclared, tailDescriptorTy, tailResults, tailKnown, tailForm, statementsForm, scalarStatements⟩ := tail
      have parameterId := validated_parameter_variable config.module context.impl implementation 0 parameter accepted.accepted implementationAt (by simp [parameters])
      have parameterDeclared : implementation.vars[parameter.var]? = some descriptor := by simpa [parameterId] using declared
      cases fuel with
      | zero =>
        simp only [invokeCall, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
        exact ⟨types, live, ambient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _, world, source, source.futureGlobals,
          EarlierCallerObservations.refl _ _ _, trivial⟩
      | succ fuel =>
        obtain ⟨argumentTypes, argumentLive, argumentAmbient, extend, acts, scopes, argumentWorld, argumentSource, clear, observed, result⟩ :=
          evalArguments_recursiveArgument_fromChecker caller state ambient types live regions pending target origin context implementation parameter
            descriptor argument integer checkFuel fuel (fuel + 1) form calls (by omega) world source contextAt implementationAt parameters mode parameterDeclared descriptorTy nesting
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
              obtain ⟨calleeFrame, actual, boundState, sameImpl, initialized, phase, environment,
                act, emptyScopes, channels, activationImpl, activationVars, bound, boundExtended, boundWorld, boundSource,
                statementsPosition, blockPosition, bodyEffects⟩ :=
                acceptedSingleByValueScalarPrefixSource config accepted caller after argumentAmbient argumentTypes argumentLive regions pending
                  target origin context implementation parameter descriptor argument value (.int integer) summary contextAt implementationAt
                  parameters declared (Or.inl ⟨integer, descriptorTy⟩) (by simpa [descriptorTy] using representation)
                  (by simpa [descriptorTy] using pointers) known tailTarget tailOrigin statements tailArgument integer tailContext tailCallee
                  tailParameter tailSummary body statementsForm tailForm tailContextAt tailCalleeAt tailParameters tailKnown scalarStatements
                  argumentWorld argumentSource (.int integer) roots typingAfter rootsAfter checked
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
              have low := execActivationBody_boundStatements_lowFuel config activation implementation.body.scope [(parameter.var, value)] statements
                (some (.call tailTarget [.byVal tailArgument] tailOrigin)) (.int integer) pushed boundState rfl bound'
              change ∃ nextTypes nextLive nextAmbient, let outcome := execActivationBody bodyFuel config activation [(parameter.var, value)] implementation.body pushed; _
              cases bodyFuel with
              | zero =>
                rw [body, low.1]
                exact ⟨argumentTypes, argumentLive, .callChannels activation [] :: argumentAmbient, (fun _ _ found => found), Nat.le_refl _, Nat.le_refl _,
                  pushedWorld, pushedClear, EarlierCallerObservations.refl _ _ _, trivial⟩
              | succ bodyFuel =>
                cases bodyFuel with
                | zero =>
                  rw [body, low.2]
                  exact ⟨boundTypes, boundLive, .callChannels activation [] :: argumentAmbient, extension,
                    by simpa [pushed, Goose.Proofs.Exit.stepState] using Nat.le_of_eq counters.1.symm,
                    by simp [pushed, Goose.Proofs.Exit.stepState, counters.2], boundWorld', boundClear, boundObserved, trivial⟩
                | succ innerFuel =>
                  let child := entryStatementsFrame config calleeFrame after.nextScope
                  have childWorld : AcceptedWorld config child.initialized boundState (.callChannels activation [] :: argumentAmbient)
                      boundTypes boundLive regions pending := by simpa [child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, initialized] using boundWorld'
                  have childSource : AcceptedFrame config accepted child boundState boundTypes := by simpa [child, boundTypes, root, descriptorTy] using boundSource
                  let blockFrame := implementationBodyFrame config calleeFrame
                  have childEnvironment : child.interpretation.environment =
                      { activation with scopes := (implementation.body.scope, pushed.nextScope) :: activation.scopes } := by
                    simp [child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, environment, actualEq,
                      RootInterpretation.enterScope, activation, emptyScopes, sameImpl, pushed]
                  have childPhase : child.phase = .implementation target := by
                    simpa [child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using phase
                  have childScalar : ∀ id expression location, .letS id expression location ∈ statements → ∀ varDescriptor,
                      child.source.impl.vars[id]? = some varDescriptor → (∃ intTy, varDescriptor.ty = .int intTy) ∨ varDescriptor.ty = .bool := by
                    intro id expression location member varDescriptor found
                    apply scalarStatements id expression location member varDescriptor
                    simpa [child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, sameImpl] using found
                  have requests : blockFrame.typing.resultRequests = [.register] := by
                    simp [blockFrame, implementationBodyFrame, sameImpl, results]
                  rw [body]
                  have childInit : child.initialized = caller.initialized := by
                    simp [child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, initialized]
                  rw [← childInit]
                  apply execActivationBody_boundCheckedScalarPrefix_withReplay_earlier innerFuel 4094 config accepted blockFrame child target
                    activation implementation.body.scope after.nextScope [(parameter.var, value)] statements tailTarget tailOrigin [.byVal tailArgument]
                    tailContext tailCallee pushed boundState (.callChannels activation [] :: argumentAmbient) argumentTypes boundTypes boundLive
                    regions pending (.int integer) after.nextAct rfl (by simp [activation]) childEnvironment bound' extension
                    (by simpa [pushed] using Nat.le_of_eq counters.1.symm) (by simp [pushed, counters.2]) boundObserved childWorld childSource childPhase
                    (by simpa [child] using statementsPosition) statementsForm childScalar (by simpa [blockFrame] using blockPosition)
                    (by simp [blockFrame, implementationBodyFrame])
                    (by simp [child, blockFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, sameImpl])
                    (by simp [child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, sameImpl])
                    (by simp [child, blockFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, sameImpl])
                    (by simp [child, blockFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, sameImpl])
                    (by simp [child, blockFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, sameImpl])
                    (by simp [child, blockFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, sameImpl])
                    (by simp [child, blockFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, sameImpl])
                    (by simpa [blockFrame, implementationBodyFrame] using tailContextAt)
                    (by simpa [blockFrame, implementationBodyFrame] using tailCalleeAt) tailResults (Or.inl ⟨integer, rfl⟩) requests
                    (by intro result afterRoots rooted; apply bodyEffects result afterRoots; rw [body]; exact rooted)
                  intro final middle middleTypes middleLive tailRoots tailTypingAfter tailRootsAfter sameInit clock replay finalWorld finalSource tailChecked
                  have finalForm : RecursiveArgumentExpression config integer final.source.impl tailArgument := by
                    have sameSource := replay.2.2.1
                    simpa [sameSource, child, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, sameImpl] using tailForm
                  have finalFuel : ({ final with typingFuel := 4094 + 1 } : ConstructionSourceFrame).typingFuel = 4093 + 2 := by rfl
                  have tailSource := finalSource.withTypingFuel (4094 + 1)
                  obtain ⟨finalTypes, finalLive, finalAmbient, extension2, nextActs, nextScopes, nextWorld, _, finalClear, nextObserved, result2⟩ :=
                    ih innerFuel (by omega) { final with typingFuel := 4094 + 1 } middle (.callChannels activation [] :: argumentAmbient)
                      middleTypes middleLive regions pending tailTarget tailOrigin tailContext tailCallee tailParameter tailArgument finalWorld tailSource
                      tailContextAt tailCalleeAt tailParameters tailMode tailResults finalForm 4093 finalFuel tailRoots tailTypingAfter tailRootsAfter tailChecked
                  have frontier : after.nextAct ≤ middle.nextAct := by rw [clock, counters.1]; simp [pushed]
                  have childFinalEnv : final.interpretation.environment = child.interpretation.environment :=
                    congrArg RootInterpretation.environment replay.2.2.2
                  simp only at nextActs nextScopes nextWorld finalClear nextObserved result2
                  rw [childFinalEnv] at nextActs nextScopes nextWorld finalClear nextObserved result2
                  refine ⟨finalTypes, finalLive, finalAmbient, extension2, nextActs, nextScopes, ?_, ?_, nextObserved.restrict frontier, ?_⟩
                  · simpa [sameInit] using nextWorld
                  · simpa [sameInit] using finalClear
                  · cases outcome : invokeCall innerFuel config child.interpretation.environment tailTarget [.byVal tailArgument]
                      [.register (.int integer)] tailOrigin middle <;> simp [outcome] at result2 ⊢ <;> exact result2

            obtain ⟨finalTypes, finalLive, finalAmbient, extension2, acts2, scopes2, finalWorld, finalClear, observed2, finalResult⟩ :=
              invokeCall_singleArgument_register_compose bodyFuel config caller.initialized caller.interpretation.environment state after argumentAmbient argumentTypes
                argumentLive regions pending after.nextAct target context implementation parameter (.byVal argument) value (.int integer) origin
                argumentWorld clear contextAt implementationAt parameters results evaluated bodySafe
            have finalObserved := observed.trans acts observed2
            have finalActs := Nat.le_trans acts acts2
            have finalScopes := Nat.le_trans scopes scopes2
            exact ⟨finalTypes, finalLive, finalAmbient, (fun root ty found => extension2 root ty (extend root ty found)),
              finalActs, finalScopes, finalWorld, source.afterEarlierObservations finalActs finalScopes finalObserved, finalClear, finalObserved, finalResult⟩








#print axioms invokeCall_recursiveParameterPrefixGraph_allFuel
end Goose.Proofs.ConstructionAcceptedExecution
