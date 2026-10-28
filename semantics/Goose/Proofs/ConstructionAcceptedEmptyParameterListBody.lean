import Goose.Proofs.ConstructionAcceptedStatefulParameterListBody
import Goose.Proofs.ConstructionAcceptedEmptyParameterListCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalArguments_emptyParameterList_body (specifications : List (Expr × Ty)) (fuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (caller : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat) (context : Context) (callee : Impl)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameterTypes : List Ty)
    (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (specificationTypes : specifications.map Prod.snd = parameterTypes)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types) (initialized : caller.initialized = config.module.globals.size)
    (safe : ∀ specification ∈ specifications, ∀ runtimeFuel current,
      AcceptedWorld config caller.initialized current ambient types live regions pending →
      AcceptedFrame config accepted caller current types →
      FirstArgumentOutcome config accepted caller ambient types live regions pending specification.2 []
        (evalValue runtimeFuel config caller.interpretation.environment specification.1 current)) :
    let arguments := specifications.map fun specification => .byVal specification.1
    let step := evalArguments fuel config caller.interpretation.environment callee.vars callee.params.toList arguments state
    AcceptedWorld config caller.initialized (Goose.Proofs.Exit.stepState step) ambient types live regions pending ∧
    AcceptedFrame config accepted caller (Goose.Proofs.Exit.stepState step) types ∧
    match step with
    | .ok values argumentState => ∃ helperFrame activation after finalTypes finalLive,
        let activated := { argumentState with nextAct := argumentState.nextAct + 1, activations := activation :: argumentState.activations }
        let scopeState := ownershipResultScopeState activation callee.body.scope activated
        helperFrame.source.impl = callee ∧ helperFrame.initialized = config.module.globals.size ∧
        helperFrame.phase = .implementation contextId ∧ helperFrame.interpretation.environment = activation ∧
        activation.act = argumentState.nextAct ∧ activation.scopes = [] ∧ activation.channels = [] ∧
        freshAct argumentState = .ok activation.act { argumentState with nextAct := argumentState.nextAct + 1 } ∧
        freshScope activated = .ok activated.nextScope { activated with nextScope := activated.nextScope + 1 } ∧
        bindAll activation.act argumentState.nextScope ((callee.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)) scopeState = .ok () after ∧
        RootTypesExtend types finalTypes ∧
        (∀ root, (∀ id, root ≠ .local activation.act argumentState.nextScope id) → finalTypes root = types root) ∧
        AcceptedWorld config config.module.globals.size after
          (.callChannels activation [] :: ambient) finalTypes finalLive regions pending ∧
        AcceptedFrame config accepted (entryStatementsFrame config helperFrame argumentState.nextScope) after finalTypes ∧
        SourcePosition accepted (entryStatementsFrame config helperFrame argumentState.nextScope) (.statements callee.body.stmts)
    | .stop .. => True
    | _ => False := by
  have descriptorLengths := descriptors.lengths
  have lengths : callee.params.toList.length = specifications.length := by
    rw [descriptorLengths, ← specificationTypes]
    simp
  have outcome := evalArguments_statefulScalarList_world specifications fuel config accepted caller state ambient types live regions pending
    callee.vars callee.params.toList lengths world source safe
  cases executed : evalArguments fuel config caller.interpretation.environment callee.vars callee.params.toList
      (specifications.map fun specification => .byVal specification.1) state with
  | escape address carriers after | jump target kind after => simp [executed] at outcome
  | stop reason after => simpa [executed] using outcome
  | ok values argumentState =>
    simp only [executed, Goose.Proofs.Exit.stepState] at outcome ⊢
    obtain ⟨argumentWorld, argumentSource, valid⟩ := outcome
    have represented : ScalarTypesRepresented parameterTypes values := by
      rw [← specificationTypes]
      exact valid.types
    have parameterValues := descriptors.bindValues represented
    have helperWorld : AcceptedWorld config config.module.globals.size argumentState ambient types live regions pending := initialized ▸ argumentWorld
    obtain ⟨helperFrame, activation, after, finalTypes, finalLive, sameImpl, helperInitialized, phase, environment, act, scopes,
      channels, freshActStep, freshScopeStep, bound, extended, protectedTypes, finalWorld, finalSource, position⟩ :=
      acceptedEmptyParameterListCallBody_protected config accepted argumentState ambient types live regions pending contextId context callee
        values contextAt calleeAt parameterValues helperWorld
    exact ⟨argumentWorld, argumentSource, helperFrame, activation, after, finalTypes, finalLive, sameImpl, helperInitialized,
      phase, environment, act, scopes, channels, freshActStep, freshScopeStep, bound, extended, protectedTypes, finalWorld, finalSource, position⟩



#print axioms evalArguments_emptyParameterList_body
end Goose.Proofs.ConstructionAcceptedExecution
