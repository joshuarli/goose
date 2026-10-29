import Goose.Proofs.ConstructionAcceptedPartialRegisterParameterCall
import Goose.Proofs.ConstructionAcceptedScalarLocalRecursiveEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem acceptedSingleByValueScalarPrefixSource (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (target origin : Nat) (context : Context) (implementation : Impl) (parameter : Param) (descriptor : LocalVar)
    (expression : Expr) (value : Value) (ty : Ty) (summary : Summary)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (declared : implementation.vars[0]? = some descriptor)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (represented : ValueRepresentation descriptor.ty value) (pointers : PointerTypedValue types descriptor.ty value)
    (known : implementation.summary = .known summary)
    (tailTarget tailOrigin : Nat) (statements : List Stmt) (argument : Expr) (integer : Goose.Core.IntTy)
    (tailContext : Context) (tailCallee : Impl) (tailParameter : Param) (tailSummary : Summary)
    (body : implementation.body = ⟨implementation.body.scope, statements, some (.call tailTarget [.byVal argument] tailOrigin)⟩)
    (statementsForm : ScalarLocalStatements statements) (argumentForm : RecursiveArgumentExpression config integer implementation argument)
    (tailContextAt : config.module.contexts[tailTarget]? = some tailContext)
    (tailCalleeAt : config.module.impls[tailContext.impl]? = some tailCallee)
    (tailParameters : tailCallee.params = #[tailParameter]) (tailKnown : tailCallee.summary = .known tailSummary)
    (scalarStatements : ∀ id initializer location, .letS id initializer location ∈ statements → ∀ varDescriptor,
      implementation.vars[id]? = some varDescriptor → (∃ intTy, varDescriptor.ty = .int intTy) ∨ varDescriptor.ty = .bool)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted caller state types)
    (outerTy : Ty) (outerRoots : List RootRef) (outerTypingAfter : Nat) (outerRootsAfter : RState)
    (checked : CheckedValue caller (.call target [.byVal expression] origin) outerTy outerRoots outerTypingAfter outerRootsAfter) :
    ∃ frame activation after,
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let scopeState := ownershipResultScopeState activation implementation.body.scope activated
      let root := Goose.Core.RootInst.local activation.act state.nextScope 0
      frame.source.impl = implementation ∧ frame.initialized = caller.initialized ∧ frame.phase = .implementation target ∧
      frame.interpretation.environment = activation ∧ activation.act = state.nextAct ∧ activation.scopes = [] ∧
      activation.channels = [.register ty] ∧ activation.implementation = context.impl ∧ activation.vars = implementation.vars ∧
      bindAll activation.act state.nextScope [(parameter.var, value)] scopeState = .ok () after ∧
      RootTypesExtend types (registerRootType types root descriptor.ty) ∧
      AcceptedWorld config caller.initialized after (.callChannels activation [] :: ambient)
        (registerRootType types root descriptor.ty) (fun other => other = root ∨ live other) regions pending ∧
      AcceptedFrame config accepted (entryStatementsFrame config frame state.nextScope) after (registerRootType types root descriptor.ty) ∧
      SourcePosition accepted (entryStatementsFrame config frame state.nextScope) (.statements statements) ∧
      SourcePosition accepted (implementationBodyFrame config frame) (.block ⟨implementation.body.scope, statements, some (.call tailTarget [.byVal argument] tailOrigin)⟩) ∧
      (∀ result afterRoots, rpBlockValue (implementationBodyFrame config frame).source [] implementation.body
        (implementationBodyFrame config frame).rootCursor = .ok (result, afterRoots) →
        GlobalEffectsAvailable frame.interpretation frame.initialized afterRoots.eff) := by
  obtain ⟨frame, activation, after, sameImpl, initialized, phase, environment, act, scopes, channels, _, _, bound, extended,
    afterWorld, afterSource, activationImpl, activationVars, compatible, bodyPosition, position⟩ :=
    acceptedRegisterParameterCallBody_partial_withSource config accepted caller state ambient types live regions pending target context
      implementation parameter descriptor value ty contextAt implementationAt parameters declared scalar represented pointers world source
  have effects := checked.singleByValue_scalarLocalRecursiveBody_effects accepted caller frame target context implementation parameter expression
    activation origin outerTy outerRoots outerTypingAfter outerRootsAfter source.compatible compatible contextAt implementationAt parameters
    summary known tailTarget tailOrigin statements argument integer tailContext tailCallee tailParameter tailSummary body statementsForm argumentForm
    tailContextAt tailCalleeAt tailParameters tailKnown scalarStatements phase sameImpl initialized
  have position' : SourcePosition accepted (entryStatementsFrame config frame state.nextScope) (.statements statements) := by
    rw [body] at position
    exact position
  have bodyPosition' : SourcePosition accepted (implementationBodyFrame config frame)
      (.block ⟨implementation.body.scope, statements, some (.call tailTarget [.byVal argument] tailOrigin)⟩) := by
    rw [body] at bodyPosition
    exact bodyPosition
  exact ⟨frame, activation, after, sameImpl, initialized, phase, environment, act, scopes, channels, activationImpl, activationVars,
    bound, extended, afterWorld, afterSource, position', bodyPosition', effects⟩

theorem entryStatementsFrame_bodyAlignment (config : EvalConfig) (frame : ConstructionSourceFrame) (stamp : Nat) :
    let blockFrame := implementationBodyFrame config frame
    let child := entryStatementsFrame config frame stamp
    let scope := frame.source.impl.body.scope
    blockFrame.typingFuel = (4094 + 1) + 1 ∧
    child.typing = { blockFrame.typing with scope := scope } ∧ child.typingFuel = 4094 + 1 ∧
    child.typingCounter = blockFrame.typingCounter ∧
    child.source = { blockFrame.source with scopes := scope :: blockFrame.source.scopes } ∧
    child.rootCursor = blockFrame.rootCursor ∧
    child.interpretation = blockFrame.interpretation.enterScope scope stamp ∧ child.initialized = blockFrame.initialized := by
  simp [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]

#print axioms entryStatementsFrame_bodyAlignment
#print axioms acceptedSingleByValueScalarPrefixSource
end Goose.Proofs.ConstructionAcceptedExecution
