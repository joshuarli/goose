import Goose.Proofs.ConstructionAcceptedByteCallHeadGeneral

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

inductive EntryByteCallStatements (config : EvalConfig) : List Stmt → Prop
  | nil : EntryByteCallStatements config []
  | call (localId contextId helperScope : Nat) (statementOrigin origin : OriginId) (bytes : List UInt8)
      (context : Context) (helper : Impl) (rest : List Stmt)
      (contextAt : config.module.contexts[contextId]? = some context)
      (helperAt : config.module.impls[context.impl]? = some helper)
      (parameters : helper.params = #[])
      (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
      (body : helper.body = ⟨helperScope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
      (absent : ∀ item ∈ helper.vars.toList, item.scope ≠ helperScope)
      (fits : bytes.length < 2 ^ 32) (tail : EntryByteCallStatements config rest) :
      EntryByteCallStatements config (.letS localId (.call contextId [] origin) statementOrigin :: rest)

theorem execStmts_entryByteCalls_world {config : EvalConfig} {statements : List Stmt}
    (form : EntryByteCallStatements config statements) :
    ∀ (fuel : Nat) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
      (activation : RuntimeActivation) (before : ExecutionState) (types : RootTypes) (live : RootInst → Prop)
      (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (entryScope scopeInst : Nat),
      AcceptedWorld config frame.initialized before [.callChannels activation []] types live regions pending →
      EvaluationHistoryCoverage before [.callChannels activation []] pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation config.module.entry →
      frame.interpretation.environment.scopes = (entryScope, scopeInst) :: activation.scopes →
      SourcePosition accepted frame (.statements statements) →
      (∀ localId contextId origin statementOrigin,
        .letS localId (.call contextId [] origin) statementOrigin ∈ statements →
        (frame.source.impl.vars[localId]?).map (·.ty) = some (.varr (.int .u8))) →
      let outcome := execStmts fuel config frame.interpretation.environment statements before
      match outcome with
      | .stop _ after => ∃ nextAmbient nextTypes nextLive nextRegions,
          AcceptedWorld config frame.initialized after nextAmbient nextTypes nextLive nextRegions pending
      | .ok flow after => ∃ nextFrame nextTypes nextLive nextRegions,
          flow = .normal .unit ∧ nextFrame.initialized = frame.initialized ∧ RootTypesExtend types nextTypes ∧
          AcceptedWorld config frame.initialized after [.callChannels activation []] nextTypes nextLive nextRegions pending ∧
          AcceptedFrame config accepted nextFrame after nextTypes ∧
          SourcePosition accepted nextFrame (.statements []) ∧
          EvaluationHistoryCoverage after [.callChannels activation []] pending
      | _ => False := by
  induction form with
  | nil =>
    intro fuel accepted frame activation before types live regions pending entryScope scopeInst world coverage source phase scopes position owners
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop]
      exact ⟨[.callChannels activation []], types, live, regions, world⟩
    | succ fuel =>
      simp only [execStmts, pure]
      exact ⟨frame, types, live, regions, trivial, rfl, (fun _ _ found => found), world, source, position, coverage⟩
  | call localId contextId helperScope statementOrigin origin bytes context helper rest contextAt helperAt parameters results body absent fits tail ih =>
    intro fuel accepted frame activation before types live regions pending entryScope scopeInst world coverage source phase scopes position owners
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop]
      exact ⟨[.callChannels activation []], types, live, regions, world⟩
    | succ fuel =>
      obtain ⟨_, _, _, typedAll, _⟩ := position.checked accepted frame _
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
        | succ checkFuel =>
          have owner := owners localId contextId origin statementOrigin (by simp)
          have headOutcome := acceptedEntry_byteCall_head_pending fuel checkFuel config accepted frame activation before types live regions pending
            entryScope scopeInst localId contextId helperScope rest bytes statementOrigin origin context helper world coverage source phase scopes
            position nesting owner contextAt helperAt parameters results body absent fits
          cases head : execStmt fuel config frame.interpretation.environment (.letS localId (.call contextId [] origin) statementOrigin) before with
          | stop reason after =>
            simp only [head] at headOutcome
            simp only [execStmts, bind, head]
            obtain ⟨nextAmbient, nextRegions, finalWorld⟩ := headOutcome
            exact ⟨nextAmbient, types, live, nextRegions, finalWorld⟩
          | escape target carriers after | jump target kind after => simp only [head] at headOutcome
          | ok flow middle =>
            simp only [head] at headOutcome
            obtain ⟨root, middleRegions, rootsAfter, normal, extended, middleWorld, middleSource, middlePosition, middleCoverage⟩ := headOutcome
            subst flow
            let nextFrame := { advanceLocalFrame { frame with typingFuel := checkFuel + 1 } localId with rootCursor := rootsAfter }
            let nextTypes := registerRootType types root (.varr (.int .u8))
            let nextLive := fun other => other = root ∨ live other
            have remainingOwners : ∀ id target callOrigin declOrigin,
                .letS id (.call target [] callOrigin) declOrigin ∈ rest →
                (nextFrame.source.impl.vars[id]?).map (·.ty) = some (.varr (.int .u8)) := by
              intro id target callOrigin declOrigin member
              exact owners id target callOrigin declOrigin (List.mem_cons_of_mem _ member)
            have nextPhase : nextFrame.phase = .implementation config.module.entry := by simpa [nextFrame, advanceLocalFrame] using phase
            have nextScopes : nextFrame.interpretation.environment.scopes = (entryScope, scopeInst) :: activation.scopes := by
              simpa [nextFrame, advanceLocalFrame] using scopes
            have result := ih fuel accepted nextFrame activation middle nextTypes nextLive middleRegions pending entryScope scopeInst
              middleWorld middleCoverage middleSource nextPhase nextScopes middlePosition remainingOwners
            cases tailStep : execStmts fuel config nextFrame.interpretation.environment rest middle with
            | stop reason after =>
              have tailOriginal : execStmts fuel config frame.interpretation.environment rest middle = .stop reason after := tailStep
              simp only [tailStep] at result
              simp only [execStmts, bind, head, tailOriginal]
              obtain ⟨nextAmbient, nextTypes, nextLive, nextRegions, finalWorld⟩ := result
              exact ⟨nextAmbient, nextTypes, nextLive, nextRegions, finalWorld⟩
            | ok tailFlow after =>
              have tailOriginal : execStmts fuel config frame.interpretation.environment rest middle = .ok tailFlow after := tailStep
              simp only [tailStep] at result
              obtain ⟨finalFrame, finalTypes, finalLive, finalRegions, normal, initializedEq, finalExtended, finalWorld, finalSource, finalPosition, finalCoverage⟩ := result
              simp only [execStmts, bind, head, tailOriginal]
              refine ⟨finalFrame, finalTypes, finalLive, finalRegions, normal, initializedEq, ?_, finalWorld, finalSource, finalPosition, finalCoverage⟩
              intro oldRoot ty found
              exact finalExtended oldRoot ty (extended oldRoot ty found)
            | escape target carriers after | jump target kind after => simp only [tailStep] at result

#print axioms execStmts_entryByteCalls_world
end Goose.Proofs.ConstructionAcceptedExecution
