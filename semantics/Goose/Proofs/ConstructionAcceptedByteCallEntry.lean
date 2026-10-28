import Goose.Proofs.ConstructionAcceptedByteCallStatement
import Goose.Proofs.ConstructionAcceptedCheckedModuleFromGlobals
import Goose.Proofs.ConstructionAcceptedEntryUnitTyping

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

theorem acceptedEntry_byteCall_statement (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (before : ExecutionState)
    (types : RootTypes) (live : RootInst → Prop) (entryScope scopeInst localId contextId helperScope : Nat)
    (bytes : List UInt8) (statementOrigin origin : Nat) (context : Context) (helper : Impl)
    (world : AcceptedWorld config frame.initialized before [.callChannels activation []] types live [] [])
    (source : AcceptedFrame config accepted frame before types)
    (phase : frame.phase = .implementation config.module.entry)
    (scopes : frame.interpretation.environment.scopes = (entryScope, scopeInst) :: activation.scopes)
    (channels : activation.channels = [])
    (position : SourcePosition accepted frame (.statements [.letS localId (.call contextId [] origin) statementOrigin]))
    (owner : (frame.source.impl.vars[localId]?).map (·.ty) = some (.varr (.int .u8)))
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨helperScope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ item ∈ helper.vars.toList, item.scope ≠ helperScope)
    (fits : bytes.length < 2 ^ 32) :
    StatementWorldOutcome config accepted frame.initialized [.callChannels activation []] []
      (execStmts fuel config frame.interpretation.environment [.letS localId (.call contextId [] origin) statementOrigin] before) := by
  obtain ⟨next, counter, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  cases frameFuel : frame.typingFuel with
  | zero =>
    simp only [frameFuel, typeStatements] at typed
    change Except.error _ = Except.ok _ at typed
    cases typed
  | succ headFuel =>
    have head := position.statements_head accepted frame (.letS localId (.call contextId [] origin) statementOrigin) [] headFuel frameFuel
    obtain ⟨headTyping, headCounter, headRoots, headTyped, headRooted⟩ := head.checked accepted _ _
    cases headFuel with
    | zero =>
      simp only [typeStatement] at headTyped
      change Except.error _ = Except.ok _ at headTyped
      cases headTyped
    | succ checkFuel =>
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
      obtain ⟨original, calls, contextFound, implementationFound, implementationId, rest⟩ := originFact
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
      have history : ReservationReferencesBounded before.construction [.callChannels activation []] := by
        intro frame member
        simp only [List.mem_singleton] at member
        subst frame
        simp [OwnershipAmbientFrame.tickets, channels]
      have noRetained : completedCarrierIds (OwnershipAmbient.retained [.callChannels activation []]) = [] := by
        simp [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers, completedCarrierIds]
      have noTickets : ∀ frame ∈ [OwnershipAmbientFrame.callChannels activation []], frame.tickets = [] := by
        intro frame member
        simp only [List.mem_singleton] at member
        subst frame
        rfl
      have depth : before.activations.length < Goose.Core.maxCallDepth := by
        have lengths := congrArg List.length world.ownership.runtime.activations
        simp [OwnershipAmbient.activations, OwnershipAmbientFrame.activationChannels] at lengths
        simp [Goose.Core.maxCallDepth, lengths]
      have outcome (statementFuel : Nat) : StatementWorldOutcome config accepted frame.initialized [.callChannels activation []] []
          (execStmt statementFuel config frame.interpretation.environment (.letS localId (.call contextId [] origin) statementOrigin) before) := by
        have statement := acceptedByteCall_let_allFuel statementFuel config accepted frame contextId helperScope localId root bytes statementOrigin origin
          context helper frame.source.impl before [.callChannels activation []] types live world source descriptor rootOrder typingOrder declared descriptorType
          resolved True.intro implementation unnamed contextAt helperAt parameters results body absent history noRetained noTickets fits depth
        cases step : execStmt statementFuel config frame.interpretation.environment (.letS localId (.call contextId [] origin) statementOrigin) before with
        | stop reason after =>
          simp only [step] at statement
          simp only [StatementWorldOutcome]
          obtain ⟨nextAmbient, nextRegions, finalWorld⟩ := statement
          exact ⟨nextAmbient, types, live, nextRegions, finalWorld⟩
        | ok flow after =>
          simp only [step] at statement
          simp only [StatementWorldOutcome]
          obtain ⟨normal, extended, finalWorld, finalFrame⟩ := statement
          exact ⟨normal, advanceLocalFrame frame localId, _, _, [], rfl, finalWorld, finalFrame⟩
        | escape target carriers after | jump target kind after => simp only [step] at statement
      cases fuel with
      | zero =>
        simp [execStmts, Goose.Construct.timeout, EvalM.stop, StatementWorldOutcome]
        exact ⟨[.callChannels activation []], types, live, [], world⟩
      | succ fuel =>
        have single := execStmts_terminal_world fuel config accepted frame frame.interpretation.environment
          (.letS localId (.call contextId [] origin) statementOrigin) before [.callChannels activation []] [] (outcome fuel)
        simpa using single

#print axioms acceptedEntry_byteCall_statement
end Goose.Proofs.ConstructionAcceptedExecution
