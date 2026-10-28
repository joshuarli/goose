import Goose.Proofs.ConstructionAcceptedEntryUnitTyping
import Goose.Proofs.ConstructionByteTailEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedByteEntry_scalarTail_afterNormal (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (frameState : ExecutionState) (frameTypes : RootTypes)
    (activation : RuntimeActivation) (activationBefore before after : ExecutionState)
    (scope : Nat) (declarations : List ByteOwnerDeclaration) (expression : Expr)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (frameSource : AcceptedFrame config accepted frame frameState frameTypes)
    (phase : frame.phase = .implementation config.module.entry)
    (initialized : frame.initialized = config.module.globals.size)
    (body : frame.source.impl.body = ⟨scope, declarations.map ByteOwnerDeclaration.statement, some expression⟩)
    (form : AcceptedBinaryExpression expression) (channels : activation.channels = [])
    (scopeState : before = ownershipResultScopeState activation scope activationBefore)
    (environment : frame.interpretation.environment =
      { activation with scopes := (scope, activationBefore.nextScope) :: activation.scopes })
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted
      (blockStatementsFrame (implementationBodyFrame config frame) scope 4095) before types)
    (owners : ∀ declaration ∈ declarations,
      (frame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : ∀ declaration ∈ declarations,
      (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none)
    (enoughFuel : declarations.length + 2 ≤ fuel + 1) (enoughCheck : declarations.length ≤ 4094)
    (normal : execStmts (fuel + 1) config frame.interpretation.environment
      (declarations.map ByteOwnerDeclaration.statement) before = .ok (.normal .unit) after) :
    ∃ (next : ConstructionSourceFrame) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop)
      (nextRegions : List ReceivingRegion),
      let outcome := execActivationBody (fuel + 2) config activation [] frame.source.impl.body activationBefore
      match outcome with
      | .stop _ final => AcceptedWorld config next.initialized final ambient nextTypes nextLive nextRegions pending
      | .ok _ final | .escape _ _ final | .jump _ _ final =>
        AcceptedWorld config next.initialized final ambient nextTypes
          (fun root => nextLive root ∧ (Goose.Proofs.Exit.runtimeScopeRoots activation scope activationBefore.nextScope).contains root = false)
          nextRegions pending := by
  have scopeEq : frame.source.impl.body.scope = scope := congrArg Block.scope body
  let blockFrame := implementationBodyFrame config frame
  have blockPosition : SourcePosition accepted blockFrame (.block ⟨scope, declarations.map ByteOwnerDeclaration.statement, some expression⟩) := by
    have position : SourcePosition accepted blockFrame (.block frame.source.impl.body) :=
      .implementationBody frame config.module.entry phase frameSource.compatible
    simpa only [body] using position
  obtain ⟨finalCounter, unitTyped⟩ := acceptedEntry_bodyUnit config accepted frame phase frameSource.compatible
  have unitTyped' : typeBlock blockFrame.typingFuel blockFrame.typing
      ⟨scope, declarations.map ByteOwnerDeclaration.statement, some expression⟩ blockFrame.typingCounter =
      .ok ([.unit], finalCounter) := by simpa only [body] using unitTyped
  have count : frame.interpretation.globalCount = config.module.globals.size := frameSource.compatible.globalCount
  have limit : blockFrame.typing.globalLimit ≤ blockFrame.interpretation.globalCount := by
    simp only [blockFrame, implementationBodyFrame, count, Nat.le_refl]
  have bounded : GlobalEffectTargetsBounded blockFrame.rootCursor.eff blockFrame.interpretation.globalCount := by
    simp [GlobalEffectTargetsBounded, Eff.accessTargets, blockFrame, implementationBodyFrame]
  have initialized' : blockFrame.initialized = blockFrame.interpretation.globalCount := by
    simpa only [blockFrame, implementationBodyFrame, count] using initialized
  have available := byteBody_scalarTail_available_afterNormal (fuel + 1) 4094 config accepted blockFrame scope declarations expression
    config.module.entry before after ambient types live regions pending blockPosition rfl world source phase owners unnamed
    enoughFuel enoughCheck limit bounded initialized' form normal
  have completed := byteBody_scalarTail_afterNormal fuel 4094 config accepted blockFrame scope declarations expression
    config.module.entry before after activationBefore activation ambient types live regions pending blockPosition rfl world source phase
    owners unnamed enoughFuel enoughCheck finalCounter unitTyped' available form channels scopeState environment normal
  obtain ⟨next, nextTypes, nextLive, nextRegions, completed⟩ := completed
  refine ⟨next, nextTypes, nextLive, nextRegions, ?_⟩
  rw [body]
  exact completed

#print axioms acceptedByteEntry_scalarTail_afterNormal
end Goose.Proofs.ConstructionAcceptedExecution
