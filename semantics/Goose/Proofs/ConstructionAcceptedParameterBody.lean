import Goose.Proofs.ConstructionAcceptedMixedLocalExecution
import Goose.Proofs.ConstructionAcceptedParameterScopeExit

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem mixedLocal_boundBody_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (pre : List (Nat × Value))
    (before boundState : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId : Nat)
    (environment : frame.interpretation.environment = activation) (channels : activation.channels = [])
    (results : frame.source.impl.results = #[])
    (tail : frame.source.impl.body.value = none) (phase : frame.phase = .implementation contextId)
    (initialized : frame.initialized = config.module.globals.size)
    (bound : bindAll activation.act before.nextScope pre
      (ownershipResultScopeState activation frame.source.impl.body.scope before) = .ok () boundState)
    (world : AcceptedWorld config config.module.globals.size boundState (.callChannels activation [] :: ambient) types live regions pending)
    (source : AcceptedFrame config accepted (entryStatementsFrame config frame before.nextScope) boundState types)
    (position : SourcePosition accepted (entryStatementsFrame config frame before.nextScope) (.statements frame.source.impl.body.stmts))
    (form : MixedLocalStatements frame.source.impl.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ frame.source.impl.body.stmts →
      (frame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ frame.source.impl.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, frame.source.impl.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
    match execActivationBody (fuel + 1) config activation pre frame.source.impl.body before with
    | .stop _ after => ∃ nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after (.callChannels activation [] :: ambient) nextTypes nextLive nextRegions pending
    | .ok carriers after => carriers = [] ∧ ∃ nextTypes nextLive nextRegions,
        AcceptedWorld config config.module.globals.size after (.callChannels activation [] :: ambient) nextTypes nextLive nextRegions pending
    | _ => False := by
  let entryFrame := entryStatementsFrame config frame before.nextScope
  have fullInitialized : entryFrame.initialized = config.module.globals.size := by
    simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using initialized
  have frameWorld : AcceptedWorld config entryFrame.initialized boundState (.callChannels activation [] :: ambient) types live regions pending :=
    fullInitialized.symm ▸ world
  have limit : entryFrame.typing.globalLimit ≤ config.module.globals.size := by
    simp [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]
  have initialBound : GlobalEffectTargetsBounded entryFrame.rootCursor.eff config.module.globals.size := by
    simp [GlobalEffectTargetsBounded, Eff.accessTargets, entryFrame, entryStatementsFrame,
      blockStatementsFrame, implementationBodyFrame]
  have owners' : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ frame.source.impl.body.stmts →
      (entryFrame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)) := by
    intro declaration member
    simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using owners declaration member
  have scalarOwners' : ∀ id expression origin, .letS id expression origin ∈ frame.source.impl.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, entryFrame.source.impl.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
    intro id expression origin member shape descriptor declared
    apply scalarOwners id expression origin member shape descriptor
    simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using declared
  have unnamed : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ frame.source.impl.body.stmts →
      (entryFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none := by
    intro declaration member
    simp only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, results,
      Array.toList_empty, List.zipIdx_nil, List.find?_nil]
  obtain ⟨next, nextTypes, nextLive, nextRegions, nextInitialized, extended, finalWorld, finalSource, finalFlow⟩ :=
    execStmts_mixedLocal_accepted_world form fuel config accepted entryFrame contextId boundState
      (.callChannels activation [] :: ambient) types live regions pending frameWorld source
      (by simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using phase)
      position fullInitialized limit initialBound owners' scalarOwners' unnamed
  change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts boundState with
    | .ok result _ => result = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) at finalFlow
  change AcceptedWorld config next.initialized
    (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts boundState))
    (.callChannels activation [] :: ambient) nextTypes nextLive nextRegions pending at finalWorld
  have nextInitialized' : next.initialized = config.module.globals.size := by
    simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, initialized] using nextInitialized
  cases outcome : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts boundState with
  | escape address carriers after | jump target kind after => simp only [outcome] at finalFlow
  | stop reason after =>
    simp only [outcome, Goose.Proofs.Exit.stepState] at finalWorld
    have stopped : execStmts fuel config
        { activation with scopes := (frame.source.impl.body.scope, before.nextScope) :: activation.scopes }
        frame.source.impl.body.stmts boundState = .stop reason after := by
      simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environment] using outcome
    have actual := execActivationBody_bound_stopped fuel config activation pre frame.source.impl.body before boundState after reason bound stopped
    rw [actual]
    exact ⟨nextTypes, nextLive, nextRegions, nextInitialized' ▸ finalWorld⟩
  | ok flow after =>
    simp only [outcome] at finalFlow
    subst flow
    simp only [outcome, Goose.Proofs.Exit.stepState] at finalWorld
    have normal : execStmts fuel config
        { activation with scopes := (frame.source.impl.body.scope, before.nextScope) :: activation.scopes }
        frame.source.impl.body.stmts boundState = .ok (.normal .unit) after := by
      simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environment] using outcome
    have actual := execActivationBody_bound_normal fuel config activation pre frame.source.impl.body before boundState after channels tail bound normal
    have released := finalWorld.releaseScope config next.initialized after (.callChannels activation [] :: ambient)
      nextTypes nextLive nextRegions pending activation frame.source.impl.body.scope before.nextScope
    rw [actual]
    exact ⟨rfl, nextTypes, _, nextRegions, nextInitialized' ▸ released⟩

#print axioms mixedLocal_boundBody_world
end Goose.Proofs.ConstructionAcceptedExecution
