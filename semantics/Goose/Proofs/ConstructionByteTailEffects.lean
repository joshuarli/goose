import Goose.Proofs.ConstructionByteTailReplay
import Goose.Proofs.ConstructionAcceptedScalarEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem SourcePosition.scalarTail_available_afterReplay {config : EvalConfig} (accepted : AcceptedModule config)
    (frame next : ConstructionSourceFrame) (scope fuel : Nat) (statements : List Stmt) (expression : Expr)
    (position : SourcePosition accepted frame (.block ⟨scope, statements, some expression⟩))
    (nesting : frame.typingFuel = fuel + 1) (form : AcceptedBinaryExpression expression)
    (typing : typeStatements fuel { frame.typing with scope := scope } statements frame.typingCounter = .ok (next.typing, next.typingCounter))
    (rooting : rpStmts { frame.source with scopes := scope :: frame.source.scopes } statements frame.rootCursor = .ok ((), next.rootCursor))
    (limit : next.typing.globalLimit ≤ frame.interpretation.globalCount)
    (bounded : GlobalEffectTargetsBounded next.rootCursor.eff frame.interpretation.globalCount)
    (initialized : frame.initialized = frame.interpretation.globalCount) :
    ∀ rootMiddle roots rootsAfter,
      rpStmts { frame.source with scopes := scope :: frame.source.scopes } statements frame.rootCursor = .ok ((), rootMiddle) →
      rpExpr { frame.source with scopes := scope :: frame.source.scopes } expression rootMiddle = .ok (roots, rootsAfter) →
      GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff := by
  obtain ⟨typedEnv, typedCounter, typedRoot, types, typingAfter, actualRoots, actualAfter,
    blockTyped, typedStatements, rootedStatements, typedTail, rootedTail⟩ :=
    position.blockTail_checks accepted frame scope fuel statements expression nesting
  have sameTyping : (typedEnv, typedCounter) = (next.typing, next.typingCounter) := Except.ok.inj (typedStatements.symm.trans typing)
  have sameRoot : typedRoot = next.rootCursor := (Prod.mk.inj (Except.ok.inj (rootedStatements.symm.trans rooting))).2
  obtain ⟨sameEnv, sameCounter⟩ := Prod.mk.inj sameTyping
  subst typedEnv typedCounter typedRoot
  intro rootMiddle roots rootsAfter statementsRooted expressionRooted
  have sameMiddle : rootMiddle = next.rootCursor := (Prod.mk.inj (Except.ok.inj (statementsRooted.symm.trans rooting))).2
  subst rootMiddle
  have targets := recursiveScalar_effects_bounded form fuel next.typing
    { frame.source with scopes := scope :: frame.source.scopes } frame.interpretation.globalCount
    next.typingCounter typingAfter next.rootCursor rootsAfter types roots limit bounded typedTail expressionRooted
  rw [initialized]
  exact (globalEffectsAvailable_iff_bounded frame.interpretation rootsAfter.eff).2 targets

theorem byteBody_scalarTail_available_afterNormal (fuel checkFuel : Nat) (config : EvalConfig)
    (accepted : AcceptedModule config) (blockFrame : ConstructionSourceFrame) (scope : Nat)
    (declarations : List ByteOwnerDeclaration) (expression : Expr) (context : Nat) (before after : ExecutionState)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
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
    (limit : blockFrame.typing.globalLimit ≤ blockFrame.interpretation.globalCount)
    (bounded : GlobalEffectTargetsBounded blockFrame.rootCursor.eff blockFrame.interpretation.globalCount)
    (initialized : blockFrame.initialized = blockFrame.interpretation.globalCount)
    (form : AcceptedBinaryExpression expression)
    (normal : execStmts fuel config (blockStatementsFrame blockFrame scope (checkFuel + 1)).interpretation.environment
      (declarations.map ByteOwnerDeclaration.statement) before = .ok (.normal .unit) after) :
    ∀ rootMiddle roots rootsAfter,
      rpStmts { blockFrame.source with scopes := scope :: blockFrame.source.scopes } (declarations.map ByteOwnerDeclaration.statement) blockFrame.rootCursor = .ok ((), rootMiddle) →
      rpExpr { blockFrame.source with scopes := scope :: blockFrame.source.scopes } expression rootMiddle = .ok (roots, rootsAfter) →
      GlobalEffectsAvailable blockFrame.interpretation blockFrame.initialized rootsAfter.eff := by
  let entry := blockStatementsFrame blockFrame scope (checkFuel + 1)
  have position := blockPosition.block_statements accepted blockFrame scope (checkFuel + 1)
    (declarations.map ByteOwnerDeclaration.statement) (some expression) (by omega)
  obtain ⟨remainingFuel, next, middle, nextTypes, nextLive, nextRegions, fuelEq, interpretationEq, initializedEq,
    sourceEq, phaseEq, limitEq, effectEq, typed, rooted, tail, extended, nextWorld, nextSource, nextPosition⟩ :=
    execStmts_byteOwners_normalTail_replay declarations fuel checkFuel config accepted entry context [] before after .unit
      ambient types live regions pending enoughFuel enoughCheck rfl world source phase
      (by simpa only [List.append_nil, entry] using position) owners unnamed (by simpa using normal)
  have typed' : typeStatements (checkFuel + 1) { blockFrame.typing with scope := scope }
      (declarations.map ByteOwnerDeclaration.statement) blockFrame.typingCounter = .ok (next.typing, next.typingCounter) := by
    simpa only [entry, blockStatementsFrame] using typed
  have rooted' : rpStmts { blockFrame.source with scopes := scope :: blockFrame.source.scopes }
      (declarations.map ByteOwnerDeclaration.statement) blockFrame.rootCursor = .ok ((), next.rootCursor) := by
    simpa only [entry, blockStatementsFrame] using rooted
  apply blockPosition.scalarTail_available_afterReplay accepted blockFrame next scope (checkFuel + 1)
    (declarations.map ByteOwnerDeclaration.statement) expression (by omega) form typed' rooted'
  · simpa only [limitEq, entry, blockStatementsFrame] using limit
  · simpa only [effectEq, entry, blockStatementsFrame] using bounded
  · exact initialized

#print axioms byteBody_scalarTail_available_afterNormal
#print axioms SourcePosition.scalarTail_available_afterReplay
end Goose.Proofs.ConstructionAcceptedExecution
