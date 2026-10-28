import Goose.Proofs.ConstructionAcceptedRegisterResultTyping
import Goose.Proofs.ConstructionAcceptedParameterizedBoundTail
import Goose.Proofs.ConstructionAcceptedBlockTailChecks

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem SourcePosition.emptyBlock_scalarRegister_checked {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (scope : Nat) (expression : Expr)
    (context : Context) (implementation : Impl) (ty : Ty)
    (bodyFrame : implementationBodyFrame config frame = frame)
    (implementationEq : frame.source.impl = implementation)
    (body : implementation.body = ⟨scope, [], some expression⟩)
    (position : SourcePosition accepted frame (.block ⟨scope, [], some expression⟩))
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (results : implementation.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (available : ∀ result after, rpBlockValue frame.source [] ⟨scope, [], some expression⟩ frame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable frame.interpretation frame.initialized after.eff) :
    ∃ roots typingAfter rootsAfter,
      CheckedValue (entryStatementsFrame config frame state.nextScope) expression ty roots typingAfter rootsAfter := by
  have nesting : frame.typingFuel = 4095 + 1 := by
    have fixed := congrArg (fun f : ConstructionSourceFrame => f.typingFuel) bodyFrame
    simpa [implementationBodyFrame] using fixed.symm
  have tail : implementation.body.value.isSome = true := by rw [body]; rfl
  obtain ⟨declared, validated⟩ := validated_scalarRegister_body_typing config.module context.impl implementation accepted.accepted
    implementationAt ty results scalar tail
  have typedBody : typeBlock frame.typingFuel frame.typing ⟨scope, [], some expression⟩ frame.typingCounter = .ok ([ty], declared) := by
    have fixed := bodyFrame
    conv => lhs; rw [← fixed]
    simpa [implementationBodyFrame, implementationEq, body] using validated
  obtain ⟨next, typingMiddle, rootMiddle, types, typingAfter, roots, rootsAfter,
    blockTyped, statementsTyped, statementsRooted, tailTyped, tailRooted⟩ :=
    position.blockTail_checks accepted frame scope 4095 [] expression nesting
  have same : (types, typingAfter) = ([ty], declared) := Except.ok.inj (blockTyped.symm.trans typedBody)
  cases same
  simp only [typeStatements, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at statementsTyped
  obtain ⟨rfl, rfl⟩ := statementsTyped
  simp only [rpStmts, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at statementsRooted
  cases statementsRooted.2
  obtain ⟨middle, otherRoots, final, sameStatements, sameTail, _, finalAvailable⟩ :=
    position.blockTail_effects accepted frame scope [] expression available
  have sameMiddle : middle = frame.rootCursor := by
    simp only [rpStmts, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at sameStatements
    exact sameStatements.2.symm
  subst middle
  have sameFinal : rootsAfter = final := (Prod.mk.inj (Except.ok.inj (tailRooted.symm.trans sameTail))).2
  subst final
  refine ⟨roots, declared, rootsAfter, ?_, ?_, ?_⟩
  · simpa [entryStatementsFrame, blockStatementsFrame, bodyFrame, implementationEq, body, Block.scope] using tailTyped
  · simpa [entryStatementsFrame, blockStatementsFrame, bodyFrame, implementationEq, body, Block.scope, StateT.run] using tailRooted
  · simpa [entryStatementsFrame, blockStatementsFrame, bodyFrame, implementationEq, body, Block.scope, RootInterpretation.enterScope,
      GlobalEffectsAvailable] using finalAvailable

theorem acceptedSingleByValueBoundScalarTail (config : EvalConfig) (accepted : AcceptedModule config)
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
    (noParameters : ∀ id, .param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks)
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
  have available := checked.singleByValue_normalizedBody_effects accepted caller frame target context implementation parameter argument
    activation origin outerTy outerRoots outerTypingAfter outerRootsAfter source.compatible compatible contextAt implementationAt parameters
    summary known noParameters phase sameImpl initialized
  obtain ⟨roots, typingAfter, rootsAfter, tailChecked⟩ :=
    tailPosition.emptyBlock_scalarRegister_checked accepted normalized state implementation.body.scope expression context implementation ty
      normalizedIdem normalizedImpl body implementationAt results scalarTy (by rw [body] at available; exact available)
  have actualChecked : CheckedValue (entryStatementsFrame config frame state.nextScope) expression ty roots typingAfter rootsAfter := by
    simpa [entryStatementsFrame, blockStatementsFrame, normalized, implementationBodyFrame] using tailChecked
  exact ⟨frame, activation, after, roots, typingAfter, rootsAfter, sameImpl, initialized, environment, act, scopes, channels,
    activationImpl, activationVars, bound, extended, afterWorld, afterSource, actualChecked⟩

#print axioms acceptedSingleByValueBoundScalarTail
#print axioms SourcePosition.emptyBlock_scalarRegister_checked
end Goose.Proofs.ConstructionAcceptedExecution
