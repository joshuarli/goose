import Goose.Proofs.ConstructionAcceptedBytePrefix
import Goose.Proofs.ConstructionRootCorrespondenceAcceptedEntryState
import Goose.Proofs.ConstructionAcceptedScopeTypes

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

def entryStatementsFrame (config : EvalConfig) (frame : ConstructionSourceFrame) (scopeInst : Nat) : ConstructionSourceFrame :=
  { blockStatementsFrame (implementationBodyFrame config frame) frame.source.impl.body.scope 4095 with
    interpretation := frame.interpretation.enterScope frame.source.impl.body.scope scopeInst }

theorem acceptedCalleeStatementsFrame (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation context)
    (parametersEmpty : frame.source.impl.params = #[])
    (scopes : frame.interpretation.environment.scopes = [])
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) :
    let next := entryStatementsFrame config frame state.nextScope
    let after := { state with nextScope := state.nextScope + 1 }
    freshScope state = .ok state.nextScope after ∧
    AcceptedWorld config next.initialized after ambient types live regions pending ∧
    AcceptedFrame config accepted next after types ∧
    SourcePosition accepted next (.statements frame.source.impl.body.stmts) := by
  let scope := frame.source.impl.body.scope
  let after := { state with nextScope := state.nextScope + 1 }
  let interpretation := frame.interpretation.enterScope scope state.nextScope
  let next := entryStatementsFrame config frame state.nextScope
  have scopeWorld := (freshScope_acceptedWorld config frame.initialized state ambient types live world).2
  have frontier : RootFrontier interpretation after.nextAct := by
    exact rootFrontier_enterScope frame.interpretation scope state.nextScope state.nextAct source.frontier
  have aliases : AliasComplete interpretation frame.source.aliases :=
    aliasComplete_enterScope frame.interpretation frame.source.aliases scope state.nextScope state.nextAct source.frontier source.aliases
  have emptyTypes : ∀ id root, rootOf interpretation.environment id after = .ok root after → types root = none := by
    intro id root resolved
    apply source.enterScope_uninitializedTypes world scope id ?_ root resolved
    left
    simp only [cursor]
    exact Nat.zero_le _
  have compatible : SourceFrameCompatible accepted next := by
    refine ⟨rfl, source.compatible.rootModule, ?_, rfl, ?_, source.compatible.globalCount, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, RootInterpretation.enterScope]
        using source.compatible.variables.trans source.compatible.sourceVariables.symm
    · simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, RootInterpretation.enterScope,
        scopes, List.map_cons, List.map_nil]
    · exact Nat.le_refl _
    · simpa only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using source.compatible.initialized
    · simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty, Array.size_empty]
      exact Nat.le_refl _
    · simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty, Array.size_empty]
      exact Nat.zero_le _
    · intro id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty,
        Array.size_empty, List.range_zero, List.not_mem_nil] at member
    · intro id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, List.not_mem_nil] at member
    · intro current rest same
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, List.cons.injEq] at same
      change frame.source.impl.body.scope = current
      exact same.1
    · have origin := source.compatible.origin
      unfold SourceOrigin at origin ⊢
      rw [phase] at origin
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, RootInterpretation.enterScope, phase,
        ]
      obtain ⟨original, calls, found, implementation, environment, typing, remaining⟩ := origin
      exact ⟨original, calls, found, implementation, environment, True.intro, remaining⟩
  have framed : AcceptedFrame config accepted next after types := by
    refine ⟨compatible, frontier, ?_, ?_, aliases, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro entry member
      simp only [next, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, scopes, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst entry
      exact Nat.lt_succ_self _
    · intro id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, List.not_mem_nil] at member
    · intro id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty,
        Array.size_empty, List.range_zero, List.not_mem_nil] at member
    · intro id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty,
        Array.size_empty, List.range_zero, List.not_mem_nil] at member
    · intro id _ root resolved
      have absent := emptyTypes id root resolved
      constructor
      · cases present : state.objects.lookup root with
        | none => rfl
        | some value =>
          obtain ⟨ty, typed⟩ := world.objectsRegistered root value present
          rw [absent] at typed
          cases typed
      · cases present : state.objectOrdinals.lookup root with
        | none => rfl
        | some value =>
          obtain ⟨ty, typed⟩ := world.ordinalsRegistered root value present
          rw [absent] at typed
          cases typed
    · intro id _ root resolved
      exact emptyTypes id root resolved
    · intro id future bound
      change frame.initialized ≤ id at future
      exact source.futureGlobals id future bound
    · intro id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty,
        Array.size_empty, List.range_zero, List.not_mem_nil] at member
    · intro fuel id member
      simp only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, parametersEmpty,
        Array.size_empty, List.range_zero, List.not_mem_nil] at member
  have bodyPosition : SourcePosition accepted (implementationBodyFrame config frame) (.block frame.source.impl.body) :=
    .implementationBody frame context phase source.compatible
  have statementsPosition : SourcePosition accepted
      (blockStatementsFrame (implementationBodyFrame config frame) scope 4095) (.statements frame.source.impl.body.stmts) := by
    cases body : frame.source.impl.body with
    | mk scope' statements value =>
      rw [body] at bodyPosition
      simpa only [scope, body, Block.scope, Block.stmts, implementationBodyFrame] using
        bodyPosition.block_statements accepted (implementationBodyFrame config frame) scope' 4095 statements value rfl
  have position : SourcePosition accepted next (.statements frame.source.impl.body.stmts) := by
    exact .instantiate statementsPosition interpretation frame.initialized
  exact ⟨rfl, scopeWorld, framed, position⟩


theorem acceptedEntryStatementsFrame (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation config.module.entry)
    (parametersEmpty : frame.source.impl.params = #[])
    (scopes : frame.interpretation.environment.scopes = []) (_initialized : frame.initialized = config.module.globals.size)
    (cursor : frame.rootCursor = ⟨0, {}, []⟩) :
    let next := entryStatementsFrame config frame state.nextScope
    let after := { state with nextScope := state.nextScope + 1 }
    freshScope state = .ok state.nextScope after ∧
    AcceptedWorld config next.initialized after ambient types live regions pending ∧
    AcceptedFrame config accepted next after types ∧
    SourcePosition accepted next (.statements frame.source.impl.body.stmts) :=
  acceptedCalleeStatementsFrame config accepted frame config.module.entry state ambient types live regions pending
    world source phase parametersEmpty scopes cursor

theorem acceptedEntryFreshStatements (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config config.module.globals.size state ambient types live regions pending) :
    ∃ frame : ConstructionSourceFrame,
      let activated := { state with nextAct := state.nextAct + 1 }
      let after := { activated with nextScope := activated.nextScope + 1 }
      let next := entryStatementsFrame config frame activated.nextScope
      freshAct state = .ok frame.interpretation.environment.act activated ∧
      freshScope activated = .ok activated.nextScope after ∧
      AcceptedWorld config next.initialized after ambient types live regions pending ∧
      AcceptedFrame config accepted next after types ∧
      SourcePosition accepted next (.statements frame.source.impl.body.stmts) ∧
      frame.phase = .implementation config.module.entry ∧ frame.source.impl.results = #[] := by
  have activatedWorld := (freshAct_acceptedWorld config config.module.globals.size state ambient types live world).2
  obtain ⟨frame, frameWorld, frameSource, phase, visible, fuel, counter, cursor, initialized, parametersEmpty, resultsEmpty,
    sourceScopes, scopes, channels, allocated, bodyTypes, declared, typed⟩ :=
      acceptedEntryWorldFrame config accepted state ambient types live regions pending activatedWorld
  obtain ⟨fresh, scopeWorld, scopeSource, position⟩ := acceptedEntryStatementsFrame config accepted frame
    { state with nextAct := state.nextAct + 1 } ambient types live regions pending frameWorld frameSource phase parametersEmpty
    scopes initialized cursor
  exact ⟨frame, allocated, fresh, scopeWorld, scopeSource, position, phase, resultsEmpty⟩

#print axioms acceptedCalleeStatementsFrame
#print axioms acceptedEntryStatementsFrame
#print axioms acceptedEntryFreshStatements

end Goose.Proofs.ConstructionAcceptedExecution
