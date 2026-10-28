import Goose.Proofs.ConstructionAcceptedParameterizedScalarTail
import Goose.Proofs.ConstructionAcceptedParameterizedBodyFrameEffects
import Goose.Proofs.ConstructionAcceptedScalarParameterEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem acceptedSingleByValueBoundScalarTail_parameterSummary (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (implementation : Impl) (parameter : Param) (descriptor : LocalVar)
    (argument : Expr) (value : Value) (ty : Ty) (summary : Summary) (expression : Expr)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (declared : implementation.vars[0]? = some descriptor)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (represented : ValueRepresentation descriptor.ty value) (pointers : PointerTypedValue types descriptor.ty value)
    (known : implementation.summary = .known summary)
    (form : AcceptedBinaryExpression expression)
    (results : implementation.results = #[⟨ty, .register, none⟩])
    (body : implementation.body = ⟨implementation.body.scope, [], some expression⟩)
    (scalarTy : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (outerTy : Ty) (outerRoots : List RootRef) (outerTypingAfter : Nat) (outerRootsAfter : RState)
    (checked : CheckedValue caller (.call target [.byVal argument] origin) outerTy outerRoots outerTypingAfter outerRootsAfter) :
    ∃ frame activation after roots typingAfter rootsAfter,
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let scopeState := ownershipResultScopeState activation implementation.body.scope activated
      let root := Goose.Core.RootInst.local activation.act state.nextScope 0
      frame.source.impl = implementation ∧ frame.initialized = caller.initialized ∧ frame.interpretation.environment = activation ∧
      activation.act = state.nextAct ∧ activation.scopes = [] ∧ activation.channels = [.register ty] ∧
      activation.implementation = context.impl ∧ activation.vars = implementation.vars ∧
      bindAll activation.act state.nextScope [(parameter.var, value)] scopeState = .ok () after ∧
      RootTypesExtend types (registerRootType types root descriptor.ty) ∧
      AcceptedWorld config caller.initialized after (.callChannels activation [] :: ambient)
        (registerRootType types root descriptor.ty) (fun other => other = root ∨ live other) regions pending ∧
      AcceptedFrame config accepted (entryStatementsFrame config frame state.nextScope) after (registerRootType types root descriptor.ty) ∧
      CheckedValue (entryStatementsFrame config frame state.nextScope) expression ty roots typingAfter rootsAfter := by
  obtain ⟨frame, activation, after, sameImpl, initialized, phase, environment, act, scopes, channels, freshActStep,
    freshScopeStep, bound, extended, afterWorld, afterSource, activationImpl, activationVars, compatible, bodyPosition, position⟩ :=
    acceptedRegisterParameterCallBody_partial_withSource config accepted caller state ambient types live regions pending target context
      implementation parameter descriptor value ty contextAt implementationAt parameters declared scalar represented pointers world source
  let normalized := implementationBodyFrame config frame
  have normalizedIdem : implementationBodyFrame config normalized = normalized := by simp [normalized, implementationBodyFrame]
  have normalizedImpl : normalized.source.impl = implementation := by simpa [normalized, implementationBodyFrame] using sameImpl
  have tailPosition : SourcePosition accepted normalized (.block ⟨implementation.body.scope, [], some expression⟩) := by
    rw [body] at bodyPosition
    exact bodyPosition
  have available := checked.singleByValue_normalizedBody_effects_noParameterBody accepted caller frame target context implementation parameter argument
    activation origin outerTy outerRoots outerTypingAfter outerRootsAfter source.compatible compatible contextAt implementationAt parameters
    summary known (by
      intro bodyContext actualEscapes bodyValue bodyState closed targets rooted id
      rw [body] at rooted
      have clear : NoParameterAccess ({} : Eff) := by simp [NoParameterAccess, Eff.accessTargets]
      exact scalarTail_noParameter _ implementation.body.scope expression form _ bodyState bodyValue clear rooted id)
    phase sameImpl initialized
  obtain ⟨roots, typingAfter, rootsAfter, tailChecked⟩ :=
    tailPosition.emptyBlock_scalarRegister_checked accepted normalized state implementation.body.scope expression context implementation ty
      normalizedIdem normalizedImpl body implementationAt results scalarTy (by rw [body] at available; exact available)
  have actualChecked : CheckedValue (entryStatementsFrame config frame state.nextScope) expression ty roots typingAfter rootsAfter := by
    simpa [entryStatementsFrame, blockStatementsFrame, normalized, implementationBodyFrame] using tailChecked
  exact ⟨frame, activation, after, roots, typingAfter, rootsAfter, sameImpl, initialized, environment, act, scopes, channels,
    activationImpl, activationVars, bound, extended, afterWorld, afterSource, actualChecked⟩

#print axioms acceptedSingleByValueBoundScalarTail_parameterSummary
end Goose.Proofs.ConstructionAcceptedExecution
