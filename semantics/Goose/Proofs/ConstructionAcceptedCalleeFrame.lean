import Goose.Proofs.ConstructionRootCorrespondenceAcceptedCallee
import Goose.Proofs.ConstructionAcceptedRegisterCallWorld
import Goose.Proofs.ConstructionAcceptedEntryCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedZeroArgumentCalleeFrame (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) (target : Nat)
    (original : Context) (implementation : Impl) (channels : List Channel)
    (callerSource : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (parameters : implementation.params = #[]) :
    ∃ frame : ConstructionSourceFrame,
      frame.phase = .implementation target ∧ frame.source.impl = implementation ∧
      frame.initialized = caller.initialized ∧ frame.typing.visible = [] ∧
      frame.interpretation = CallInterpretation caller.interpretation
        ⟨original.impl, state.nextAct, implementation.vars, [], channels⟩ [] ∧
      implementationBodyFrame config frame = frame ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      AcceptedFrame config accepted frame { state with nextAct := state.nextAct + 1 } types ∧
      SourcePosition accepted frame (.block frame.source.impl.body) ∧
      ∃ bodyTypes declared, typeBlock frame.typingFuel frame.typing frame.source.impl.body frame.typingCounter =
        .ok (bodyTypes, declared) := by
  obtain ⟨frame, phase, impl, aliases, interpretation, initialized, bodyFrame, compatible, allocated, frontier⟩ :=
    acceptedCalleeSourceFrame config accepted caller state target original implementation [] channels callerSource.compatible
      callerSource.frontier contextAt implementationAt
  have visible : frame.typing.visible = [] := by
    have equal := congrArg (fun f : ConstructionSourceFrame => f.typing.visible) bodyFrame
    simpa [implementationBodyFrame, impl, parameters] using equal.symm
  have initializing : frame.source.initializing = [] := by
    have equal := congrArg (fun f : ConstructionSourceFrame => f.source.initializing) bodyFrame
    simpa [implementationBodyFrame] using equal.symm
  have scopes : frame.interpretation.environment.scopes = [] := by
    rw [interpretation]
    rfl
  have coverage : AliasClosure caller.source.aliases (accepted.aliases[target]!) [] caller.interpretation.globalCount := by
    constructor <;> intros <;> simp_all
  have aliasComplete : AliasComplete frame.interpretation frame.source.aliases := by
    rw [interpretation, aliases]
    exact call_aliasComplete caller.interpretation _ [] caller.source.aliases _ callerSource.aliases coverage callerSource.frontier
  have framed : AcceptedFrame config accepted frame { state with nextAct := state.nextAct + 1 } types := {
    compatible := compatible
    frontier := frontier
    scopeFrontier := by intro entry member; rw [scopes] at member; cases member
    initializingBefore := by intro id member; rw [initializing] at member; cases member
    aliases := aliasComplete
    locals := by intro id member; rw [visible] at member; cases member
    localTypes := by intro id member; rw [visible] at member; cases member
    uninitializedLocals := by
      intro id _ root resolved
      have actual := rootOf_instantiates frame.interpretation id _ root resolved
      cases actual with
      | «local» id descriptor scope declared active => rw [scopes] at active; cases active
    uninitializedTypes := by
      intro id _ root resolved
      have actual := rootOf_instantiates frame.interpretation id _ root resolved
      cases actual with
      | «local» id descriptor scope declared active => rw [scopes] at active; cases active
    futureGlobals := by
      intro id future bound
      rw [initialized] at future
      exact callerSource.futureGlobals id future bound
    direct := by intro id member; rw [visible] at member; cases member
    contents := by intro fuel id member; rw [visible] at member; cases member }
  obtain ⟨bodyTypes, declared, typed⟩ := validated_implementation_typing config.module original.impl implementation accepted.accepted implementationAt
  have cursor : frame.rootCursor = ⟨0, {}, []⟩ := by
    have equal := congrArg (fun f : ConstructionSourceFrame => f.rootCursor) bodyFrame
    simpa [implementationBodyFrame, impl, parameters] using equal.symm
  have position : SourcePosition accepted frame (.block frame.source.impl.body) := by
    have original := SourcePosition.implementationBody frame target phase compatible
    simpa [bodyFrame] using original
  refine ⟨frame, phase, impl, initialized, visible, interpretation, bodyFrame, cursor, framed, position, bodyTypes, declared, ?_⟩
  have same := bodyFrame
  conv => lhs; rw [← same]
  simpa [implementationBodyFrame, impl, parameters] using typed

theorem acceptedZeroArgumentRegisterCallee (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion)
    (pending : List PendingCarrierFrame) (target : Nat) (original : Context) (implementation : Impl) (ty : Ty)
    (callerSource : AcceptedFrame config accepted caller state types)
    (world : AcceptedWorld config caller.initialized state ambient types live regions pending)
    (contextAt : config.module.contexts[target]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (parameters : implementation.params = #[]) :
    ∃ frame : ConstructionSourceFrame,
      let activation : RuntimeActivation := ⟨original.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
      let after := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      frame.phase = .implementation target ∧ frame.source.impl = implementation ∧ frame.initialized = caller.initialized ∧
      frame.interpretation = CallInterpretation caller.interpretation activation [] ∧
      implementationBodyFrame config frame = frame ∧ frame.rootCursor = ⟨0, {}, []⟩ ∧
      AcceptedFrame config accepted frame after types ∧
      SourcePosition accepted frame (.block frame.source.impl.body) ∧
      AcceptedWorld config frame.initialized after (.callChannels activation [] :: ambient) types live regions pending ∧
      ∃ bodyTypes declared, typeBlock frame.typingFuel frame.typing frame.source.impl.body frame.typingCounter =
        .ok (bodyTypes, declared) := by
  obtain ⟨frame, phase, impl, initialized, visible, interpretation, bodyFrame, cursor, source, position, bodyTypes, declared, typed⟩ :=
    acceptedZeroArgumentCalleeFrame config accepted caller state types target original implementation [.register ty]
      callerSource contextAt implementationAt parameters
  let activation : RuntimeActivation := ⟨original.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
  have pushed := acceptedWorld_pushRegisterActivation config caller.initialized state ambient types live regions pending
    activation world rfl ty rfl
  have transferred := source.emptyVisible_activations visible (activation :: state.activations)
  exact ⟨frame, phase, impl, initialized, interpretation, bodyFrame, cursor, transferred, position, initialized ▸ pushed, bodyTypes, declared, typed⟩

#print axioms acceptedZeroArgumentRegisterCallee
#print axioms acceptedZeroArgumentCalleeFrame
end Goose.Proofs.ConstructionAcceptedExecution
