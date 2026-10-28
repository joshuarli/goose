import Goose.Proofs.ConstructionAcceptedEntryStartup
import Goose.Proofs.ConstructionAcceptedEntryActivation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem AcceptedFrame.emptyVisible_activations {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {state : ExecutionState} {types : RootTypes}
    (source : AcceptedFrame config accepted frame state types) (visible : frame.typing.visible = [])
    (activations : List RuntimeActivation) :
    AcceptedFrame config accepted frame { state with activations := activations } types := by
  refine ⟨source.compatible, source.frontier, source.scopeFrontier, source.initializingBefore, source.aliases,
    ?_, ?_, ?_, ?_, source.futureGlobals, ?_, ?_⟩
  · intro id member
    rw [visible] at member
    cases member
  · intro id member
    rw [visible] at member
    cases member
  · intro id uninitialized root resolved
    exact source.uninitializedLocals id uninitialized root
      (rootOf_transfer frame.interpretation id _ state root resolved)
  · intro id uninitialized root resolved
    exact source.uninitializedTypes id uninitialized root
      (rootOf_transfer frame.interpretation id _ state root resolved)
  · intro id member
    rw [visible] at member
    cases member
  · intro fuel id member
    rw [visible] at member
    cases member

theorem acceptedEntryPushedStatements (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config config.module.globals.size state ambient types live regions pending) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let scopeState := { activated with nextScope := activated.nextScope + 1 }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := entryStatementsFrame config frame activated.nextScope
      frame.interpretation.environment = activation ∧ activation.act = state.nextAct ∧ activation.channels = [] ∧
      freshAct state = .ok activation.act { state with nextAct := state.nextAct + 1 } ∧
      freshScope activated = .ok activated.nextScope scopeState ∧
      AcceptedWorld config next.initialized after (.callChannels activation [] :: ambient) types live regions pending ∧
      AcceptedFrame config accepted next after types ∧
      SourcePosition accepted next (.statements frame.source.impl.body.stmts) ∧
      frame.phase = .implementation config.module.entry ∧ frame.source.impl.results = #[] := by
  obtain ⟨original, implementation, originalAt, implementationAt, parametersEmpty, resultsEmpty⟩ :=
    validated_entry config.module accepted.accepted
  let activation : RuntimeActivation := ⟨original.impl, state.nextAct, implementation.vars, [], []⟩
  let pushed := { state with activations := activation :: state.activations }
  have pushedWorld := acceptedWorld_pushEmptyActivation config config.module.globals.size state ambient types live regions pending
    activation world rfl rfl
  obtain ⟨frame, frameWorld, frameSource, phase, visible, fuel, counter, cursor, initialized, frameParameters, frameResults,
    sourceScopes, scopes, channels, allocated, bodyTypes, declared, typed⟩ :=
    acceptedEntryWorldFrame config accepted pushed (.callChannels activation [] :: ambient) types live regions pending pushedWorld
  have originFact := frameSource.compatible.origin
  unfold SourceOrigin at originFact
  rw [phase] at originFact
  obtain ⟨entry, calls, entryFound, implFound, environmentImpl, restOrigin⟩ := originFact
  have sameEntry : entry = original := Option.some.inj (entryFound.symm.trans originalAt)
  subst entry
  have sameImpl : frame.source.impl = implementation := Option.some.inj (implFound.symm.trans implementationAt)
  have identifier : frame.interpretation.environment.act = state.nextAct := by
    have exactAct : freshAct pushed = .ok state.nextAct { pushed with nextAct := pushed.nextAct + 1 } := rfl
    exact (ExecutionStep.ok.inj (allocated.symm.trans exactAct)).1
  have variables : frame.interpretation.environment.vars = implementation.vars := by
    rw [frameSource.compatible.variables, ← frameSource.compatible.sourceVariables, sameImpl]
  have environment : frame.interpretation.environment = activation := by
    cases runtime : frame.interpretation.environment with
    | mk impl act vars scopes' channels' =>
      simp only [runtime] at environmentImpl identifier variables scopes channels
      simp only [activation]
      cases environmentImpl
      cases identifier
      cases variables
      cases scopes
      cases channels
      rfl
  obtain ⟨fresh, scopeWorld, scopeSource, position⟩ := acceptedEntryStatementsFrame config accepted frame
    { pushed with nextAct := pushed.nextAct + 1 } (.callChannels activation [] :: ambient) types live regions pending
    frameWorld frameSource phase frameParameters scopes initialized cursor
  have scopeVisible : (entryStatementsFrame config frame state.nextScope).typing.visible = [] := by
    simp only [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, frameParameters,
      Array.size_empty, List.range_zero]
  have actualSource := scopeSource.emptyVisible_activations scopeVisible
    (({ pushed with nextAct := pushed.nextAct + 1 }).activations.map (fun (current : RuntimeActivation) =>
      if current.act == activation.act then { current with scopes := (frame.source.impl.body.scope, state.nextScope) :: activation.scopes }
      else current))
  have actualWorld := acceptedWorld_resultScope config frame.initialized
    { pushed with nextAct := pushed.nextAct + 1 } (.callChannels activation [] :: ambient) types live regions pending
    activation frame.source.impl.body.scope frameWorld
  refine ⟨frame, activation, environment, rfl, rfl, ?_, fresh, actualWorld, actualSource, position, phase, frameResults⟩
  rfl

#print axioms AcceptedFrame.emptyVisible_activations
#print axioms acceptedEntryPushedStatements

end Goose.Proofs.ConstructionAcceptedExecution
