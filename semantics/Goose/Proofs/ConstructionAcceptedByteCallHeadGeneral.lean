import Goose.Proofs.ConstructionAcceptedByteCallCursor
import Goose.Proofs.ConstructionAcceptedFreshByteCallStatementGeneral
import Goose.Proofs.ConstructionAcceptedByteCallEntry

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

theorem acceptedEntry_byteCall_head_pending (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (before : ExecutionState)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (entryScope scopeInst localId contextId helperScope : Nat) (rest : List Stmt)
    (bytes : List UInt8) (statementOrigin origin : Nat) (context : Context) (helper : Impl)
    (world : AcceptedWorld config frame.initialized before [.callChannels activation []] types live regions pending)
    (coverage : EvaluationHistoryCoverage before [.callChannels activation []] pending)
    (source : AcceptedFrame config accepted frame before types)
    (phase : frame.phase = .implementation config.module.entry)
    (scopes : frame.interpretation.environment.scopes = (entryScope, scopeInst) :: activation.scopes)
    (position : SourcePosition accepted frame (.statements (.letS localId (.call contextId [] origin) statementOrigin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 2)
    (owner : (frame.source.impl.vars[localId]?).map (·.ty) = some (.varr (.int .u8)))
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨helperScope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ item ∈ helper.vars.toList, item.scope ≠ helperScope)
    (fits : bytes.length < 2 ^ 32) :
    match execStmt fuel config frame.interpretation.environment (.letS localId (.call contextId [] origin) statementOrigin) before with
    | .stop _ after => ∃ nextAmbient nextRegions,
        AcceptedWorld config frame.initialized after nextAmbient types live nextRegions pending
    | .ok flow after => ∃ root nextRegions rootsAfter,
        let nextFrame := { advanceLocalFrame { frame with typingFuel := checkFuel + 1 } localId with rootCursor := rootsAfter }
        flow = .normal .unit ∧ RootTypesExtend types (registerRootType types root (.varr (.int .u8))) ∧
        AcceptedWorld config frame.initialized after [.callChannels activation []] (registerRootType types root (.varr (.int .u8)))
          (fun other => other = root ∨ live other) nextRegions pending ∧
        AcceptedFrame config accepted nextFrame after (registerRootType types root (.varr (.int .u8))) ∧
        SourcePosition accepted nextFrame (.statements rest) ∧ EvaluationHistoryCoverage after [.callChannels activation []] pending
    | _ => False := by
  let headFrame := { frame with typingFuel := checkFuel + 1 }
  have head := position.statements_head accepted frame (.letS localId (.call contextId [] origin) statementOrigin) rest (checkFuel + 1) nesting
  obtain ⟨headTyping, headCounter, headRoots, headTyped, headRooted⟩ := head.checked accepted _ _
  obtain ⟨descriptor, declared, localScope, typingOrder⟩ := typeStatement_let_descriptor checkFuel frame.typing headTyping localId
    (.call contextId [] origin) statementOrigin frame.typingCounter headCounter headTyped
  have descriptorType : descriptor.ty = .varr (.int .u8) := by
    have same : frame.source.impl.vars[localId]? = some descriptor := by simpa only [source.compatible.sourceVariables] using declared
    simpa only [same, Option.map_some, Option.some.injEq] using owner
  have sourceScopes : frame.source.scopes = entryScope :: activation.scopes.map Prod.fst := by
    rw [source.compatible.scopes, scopes]
    rfl
  have localScope' := localScope.trans (source.compatible.currentScope entryScope (activation.scopes.map Prod.fst) sourceScopes)
  have runtimeDeclared : frame.interpretation.environment.vars[localId]? = some descriptor := by
    rw [source.compatible.variables]
    exact declared
  have rootOrder := (rpStmt_letS_initializer headRooted).1
  let root := RootInst.local frame.interpretation.environment.act scopeInst localId
  have resolved : rootOf frame.interpretation.environment localId before = .ok root before := by
    simp only [rootOf, runtimeDeclared, scopes, List.find?_cons, localScope', beq_self_eq_true, pure, root]
  have originFact := source.compatible.origin
  simp only [SourceOrigin, phase] at originFact
  obtain ⟨original, calls, contextFound, implementationFound, implementationId, restOrigin⟩ := originFact
  have implementation : config.module.impls[frame.interpretation.environment.implementation]? = some frame.source.impl := by
    rw [implementationId]
    exact implementationFound
  obtain ⟨entry, entryImpl, entryFound, entryImplFound, entryParameters, entryResults⟩ := validated_entry config.module accepted.accepted
  have sameEntry : original = entry := Option.some.inj (contextFound.symm.trans entryFound)
  subst entry
  have sameImpl : frame.source.impl = entryImpl := Option.some.inj (implementationFound.symm.trans entryImplFound)
  have entryEmpty : frame.source.impl.results = #[] := by simpa only [sameImpl] using entryResults
  have unnamed : (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some localId)) = none := by
    simp [entryEmpty]
  have depth : before.activations.length < Goose.Core.maxCallDepth := by
    have lengths := congrArg List.length world.ownership.runtime.activations
    simp [OwnershipAmbient.activations, OwnershipAmbientFrame.activationChannels] at lengths
    simp [Goose.Core.maxCallDepth, lengths]
  obtain ⟨rootsAfter, rooted, nextVar, tail⟩ := position.zeroArgumentByteCallLocal_tail frame before types localId contextId origin
    statementOrigin checkFuel rest context helper source nesting contextAt helperAt parameters results owner
  have outcome := acceptedByteCall_let_pending_history_allFuel fuel config accepted headFrame contextId helperScope localId root bytes statementOrigin origin
    context helper frame.source.impl before [.callChannels activation []] types live regions pending world (source.withTypingFuel (checkFuel + 1))
    descriptor rootOrder typingOrder declared descriptorType resolved True.intro implementation unnamed contextAt helperAt parameters results body absent coverage fits depth
  cases step : execStmt fuel config frame.interpretation.environment (.letS localId (.call contextId [] origin) statementOrigin) before with
  | stop reason after => simpa only [headFrame, step] using outcome
  | ok flow after =>
    simp only [headFrame, step] at outcome ⊢
    obtain ⟨nextRegions, normal, extended, finalWorld, finalFrame, nextCoverage⟩ := outcome
    have transported := finalFrame.with_rootCursor rootsAfter (by simpa [advanceLocalFrame, headFrame] using nextVar)
    exact ⟨root, nextRegions, rootsAfter, normal, extended, finalWorld, transported, tail, nextCoverage⟩
  | escape target carriers after | jump target kind after => simp only [headFrame, step] at outcome

#print axioms acceptedEntry_byteCall_head_pending
end Goose.Proofs.ConstructionAcceptedExecution
