import Goose.Proofs.ConstructionAcceptedBlockTailChecks
import Goose.Proofs.ConstructionByteReplay

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem SourcePosition.blockTail_checkedUnit_afterReplay {config : EvalConfig} (accepted : AcceptedModule config)
    (frame next : ConstructionSourceFrame) (scope fuel : Nat) (statements : List Stmt) (expression : Expr)
    (position : SourcePosition accepted frame (.block ⟨scope, statements, some expression⟩))
    (nesting : frame.typingFuel = fuel + 1) (finalCounter : Nat)
    (bodyUnit : typeBlock frame.typingFuel frame.typing ⟨scope, statements, some expression⟩ frame.typingCounter =
      .ok ([.unit], finalCounter))
    (available : ∀ rootMiddle roots rootsAfter,
      rpStmts { frame.source with scopes := scope :: frame.source.scopes } statements frame.rootCursor = .ok ((), rootMiddle) →
      rpExpr { frame.source with scopes := scope :: frame.source.scopes } expression rootMiddle = .ok (roots, rootsAfter) →
      GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff)
    (typing : typeStatements fuel { frame.typing with scope := scope } statements frame.typingCounter = .ok (next.typing, next.typingCounter))
    (rooting : rpStmts { frame.source with scopes := scope :: frame.source.scopes } statements frame.rootCursor = .ok ((), next.rootCursor))
    (source : next.source = { frame.source with scopes := scope :: frame.source.scopes })
    (interpretation : next.interpretation = frame.interpretation) (initialized : next.initialized = frame.initialized)
    (phase : next.phase = frame.phase) :
    ∃ roots rootsAfter, CheckedValue { next with typingFuel := fuel } expression .unit roots finalCounter rootsAfter := by
  obtain ⟨typingEnv, typingMiddle, rootMiddle, roots, rootsAfter, typed, rooted, checked⟩ :=
    position.blockTail_checkedUnit accepted frame scope fuel statements expression nesting finalCounter bodyUnit available
  have sameTyping : (typingEnv, typingMiddle) = (next.typing, next.typingCounter) := Except.ok.inj (typed.symm.trans typing)
  have sameRoot : rootMiddle = next.rootCursor := (Prod.mk.inj (Except.ok.inj (rooted.symm.trans rooting))).2
  obtain ⟨sameEnv, sameCounter⟩ := Prod.mk.inj sameTyping
  subst typingEnv typingMiddle rootMiddle
  refine ⟨roots, rootsAfter, ?_⟩
  cases frame
  cases next
  simp_all only [CheckedValue, ConstructionSourceFrame.mk.injEq]

theorem byteBody_checkedTail_afterNormal (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (blockFrame : ConstructionSourceFrame) (scope : Nat) (declarations : List ByteOwnerDeclaration) (expression : Expr)
    (context : Nat) (before after : ExecutionState) (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (blockPosition : SourcePosition accepted blockFrame (.block ⟨scope, declarations.map ByteOwnerDeclaration.statement, some expression⟩))
    (nesting : blockFrame.typingFuel = checkFuel + 2)
    (world : AcceptedWorld config (blockStatementsFrame blockFrame scope (checkFuel + 1)).initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted (blockStatementsFrame blockFrame scope (checkFuel + 1)) before types)
    (phase : blockFrame.phase = .implementation context)
    (owners : ∀ declaration ∈ declarations,
      ((blockStatementsFrame blockFrame scope (checkFuel + 1)).typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (unnamed : ∀ declaration ∈ declarations,
      ((blockStatementsFrame blockFrame scope (checkFuel + 1)).source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none)
    (enoughFuel : declarations.length + 2 ≤ fuel) (enoughCheck : declarations.length ≤ checkFuel)
    (finalCounter : Nat)
    (bodyUnit : typeBlock blockFrame.typingFuel blockFrame.typing ⟨scope, declarations.map ByteOwnerDeclaration.statement, some expression⟩ blockFrame.typingCounter =
      .ok ([.unit], finalCounter))
    (available : ∀ rootMiddle roots rootsAfter,
      rpStmts { blockFrame.source with scopes := scope :: blockFrame.source.scopes } (declarations.map ByteOwnerDeclaration.statement) blockFrame.rootCursor = .ok ((), rootMiddle) →
      rpExpr { blockFrame.source with scopes := scope :: blockFrame.source.scopes } expression rootMiddle = .ok (roots, rootsAfter) →
      GlobalEffectsAvailable blockFrame.interpretation blockFrame.initialized rootsAfter.eff)
    (normal : execStmts fuel config (blockStatementsFrame blockFrame scope (checkFuel + 1)).interpretation.environment
      (declarations.map ByteOwnerDeclaration.statement) before = .ok (.normal .unit) after) :
    ∃ (next : ConstructionSourceFrame) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop)
      (nextRegions : List ReceivingRegion) (roots : List RootRef) (rootsAfter : RState),
      AcceptedWorld config next.initialized after ambient nextTypes nextLive nextRegions pending ∧
      AcceptedFrame config accepted { next with typingFuel := checkFuel + 1 } after nextTypes ∧
      CheckedValue { next with typingFuel := checkFuel + 1 } expression .unit roots finalCounter rootsAfter ∧
      next.interpretation = blockFrame.interpretation ∧ next.initialized = blockFrame.initialized := by
  let entry := blockStatementsFrame blockFrame scope (checkFuel + 1)
  have position := blockPosition.block_statements accepted blockFrame scope (checkFuel + 1)
    (declarations.map ByteOwnerDeclaration.statement) (some expression) (by omega)
  obtain ⟨remainingFuel, next, middle, nextTypes, nextLive, nextRegions, fuelEq, interpretationEq, initializedEq,
    sourceEq, phaseEq, limitEq, effectEq, typed, rooted, tail, extended, nextWorld, nextSource, nextPosition⟩ :=
    execStmts_byteOwners_normalTail_replay declarations fuel checkFuel config accepted entry context [] before after .unit
      ambient types live regions pending enoughFuel enoughCheck rfl world source phase (by simpa only [List.append_nil, entry] using position) owners unnamed (by simpa using normal)
  have remaining : 0 < remainingFuel := by omega
  cases remainingFuel with
  | zero => omega
  | succ remainingFuel =>
    have same : middle = after := by
      simpa only [entry, List.map_nil, List.nil_append, execStmts, pure, ExecutionStep.ok.injEq, true_and] using tail
    subst middle
    have typed' : typeStatements (checkFuel + 1) { blockFrame.typing with scope := scope }
        (declarations.map ByteOwnerDeclaration.statement) blockFrame.typingCounter = .ok (next.typing, next.typingCounter) := by
      simpa only [entry, blockStatementsFrame] using typed
    have rooted' : rpStmts { blockFrame.source with scopes := scope :: blockFrame.source.scopes }
        (declarations.map ByteOwnerDeclaration.statement) blockFrame.rootCursor = .ok ((), next.rootCursor) := by
      simpa only [entry, blockStatementsFrame] using rooted
    obtain ⟨roots, rootsAfter, checked⟩ := blockPosition.blockTail_checkedUnit_afterReplay accepted blockFrame next scope
      (checkFuel + 1) (declarations.map ByteOwnerDeclaration.statement) expression (by omega) finalCounter bodyUnit available
      typed' rooted' (by simpa only [entry, blockStatementsFrame] using sourceEq)
      (by simpa only [entry, blockStatementsFrame] using interpretationEq)
      (by simpa only [entry, blockStatementsFrame] using initializedEq)
      (by simpa only [entry, blockStatementsFrame] using phaseEq)
    exact ⟨next, nextTypes, nextLive, nextRegions, roots, rootsAfter, nextWorld,
      nextSource.withTypingFuel (checkFuel + 1), checked, interpretationEq, initializedEq⟩

#print axioms byteBody_checkedTail_afterNormal
#print axioms SourcePosition.blockTail_checkedUnit_afterReplay
end Goose.Proofs.ConstructionAcceptedExecution
