import Goose.Proofs.ConstructionAcceptedMixedTerminal
import Goose.Proofs.ConstructionAcceptedRegisterGlobalAssignments
import Goose.Proofs.ConstructionEntryCallIdentity

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem execStmts_entryMixed_registerGlobalAssignmentsPrint_world {statements : List Stmt} (prefixForm : MixedLocalStatements statements)
    {expression : Expr} (shape : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (entry : RuntimeActivation) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId origin localId statementOrigin printOrigin : Nat) (assignments : List GlobalIntegerAssignment) (context : Context) (helper : Impl) (parameter : Param) (descriptor : LocalVar)
    (resultTy : Ty) (resultExpression : Expr) (scope scopeInst : Nat) (outerScopes : List (Nat × Nat))
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[parameter]) (results : helper.results = #[⟨resultTy, .register, none⟩])
    (mode : parameter.mode = .byValue) (resultScalar : (∃ intTy, resultTy = .int intTy) ∨ resultTy = .bool)
    (declared : helper.vars[0]? = some descriptor) (scalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (initialized : frame.initialized = config.module.globals.size)
    (world : AcceptedWorld config frame.initialized state [.callChannels entry []] types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation config.module.entry)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (limit : frame.typing.globalLimit ≤ config.module.globals.size)
    (position : SourcePosition accepted frame (.statements (statements ++ (.letS localId (.call contextId [.byVal expression] origin) statementOrigin :: (globalIntegerAssignments assignments ++ [.print [.expr (.read (.var localId))] printOrigin])))))
    (scopes : frame.interpretation.environment.scopes = (scope, scopeInst) :: outerScopes)
    (localScalar : ∀ localDescriptor, frame.source.impl.vars[localId]? = some localDescriptor →
      (∃ intTy, localDescriptor.ty = .int intTy) ∨ localDescriptor.ty = .bool)
    (prefixOwners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
      (frame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (prefixScalar : ∀ id value origin, .letS id value origin ∈ statements → AcceptedBinaryExpression value →
      ∀ localDesc, frame.source.impl.vars[id]? = some localDesc → (∃ ty, localDesc.ty = .int ty) ∨ localDesc.ty = .bool)
    (prefixUnnamed : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
      (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none)
    (targets : ∀ assignment ∈ assignments, ∃ globalDescriptor,
      config.module.globals[assignment.id]? = some globalDescriptor ∧ globalDescriptor.ty = .int assignment.intTy)
    (form : MixedLocalStatements helper.body.stmts) (tail : helper.body.value = some resultExpression)
    (resultShape : AcceptedBinaryExpression resultExpression)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id value origin, .letS id value origin ∈ helper.body.stmts → AcceptedBinaryExpression value →
      ∀ localDesc, helper.vars[id]? = some localDesc → (∃ ty, localDesc.ty = .int ty) ∨ localDesc.ty = .bool) :
    StatementWorldOutcome config accepted frame.initialized [.callChannels entry []] pending
      (execStmts fuel config frame.interpretation.environment
        (statements ++ (.letS localId (.call contextId [.byVal expression] origin) statementOrigin :: (globalIntegerAssignments assignments ++ [.print [.expr (.read (.var localId))] printOrigin]))) state) := by
  let guard : ConstructionSourceFrame → Prop := fun next =>
    next.source.impl = frame.source.impl ∧ next.interpretation.environment.scopes = (scope, scopeInst) :: outerScopes
  have stable : ∀ first next, first.source = next.source → first.interpretation = next.interpretation →
      first.phase = next.phase → guard first → guard next := by
    intro first next sourceEq interpretationEq phaseEq guarded
    exact ⟨by rw [← sourceEq]; exact guarded.1, by rw [← interpretationEq]; exact guarded.2⟩
  have terminalWorld : ∀ (terminalFuel : Nat) (next : ConstructionSourceFrame) (before : ExecutionState) (nextTypes : RootTypes)
      (nextLive : Goose.Core.RootInst → Prop) (nextRegions : List ReceivingRegion),
      AcceptedWorld config next.initialized before [.callChannels entry []] nextTypes nextLive nextRegions pending →
      AcceptedFrame config accepted next before nextTypes → next.phase = .implementation config.module.entry → guard next →
      SourcePosition accepted next (.statements (.letS localId (.call contextId [.byVal expression] origin) statementOrigin :: (globalIntegerAssignments assignments ++ [.print [.expr (.read (.var localId))] printOrigin]))) →
      next.initialized = config.module.globals.size → next.typing.globalLimit ≤ config.module.globals.size →
      GlobalEffectTargetsBounded next.rootCursor.eff config.module.globals.size →
      StatementWorldOutcome config accepted next.initialized [.callChannels entry []] pending
        (execStmts terminalFuel config next.interpretation.environment
          (.letS localId (.call contextId [.byVal expression] origin) statementOrigin :: (globalIntegerAssignments assignments ++ [.print [.expr (.read (.var localId))] printOrigin])) before) := by
    intro terminalFuel next before nextTypes nextLive nextRegions nextWorld nextSource nextPhase guarded nextPosition nextInitialized nextLimit nextBounded
    have nextScalar : ∀ localDescriptor, next.typing.variables[localId]? = some localDescriptor →
        (∃ intTy, localDescriptor.ty = .int intTy) ∨ localDescriptor.ty = .bool := by
      intro localDescriptor present
      apply localScalar localDescriptor
      rw [← guarded.1]
      simpa only [nextSource.compatible.sourceVariables] using present
    obtain ⟨depth, outer⟩ := acceptedEntry_callIdentity config next.initialized before entry nextTypes nextLive nextRegions pending nextWorld
    exact execStmts_registerLet_globalAssignments_print_world shape terminalFuel config accepted next before [.callChannels entry []]
      nextTypes nextLive nextRegions pending contextId origin localId statementOrigin printOrigin assignments context helper parameter descriptor resultTy resultExpression
      scope scopeInst outerScopes contextAt helperAt parameters results mode resultScalar declared scalar nextInitialized nextWorld nextSource
      nextBounded nextPosition nextScalar guarded.2 form tail resultShape owners scalarOwners targets depth outer
  exact execStmts_mixedSuffix_world prefixForm config accepted config.module.entry [.callChannels entry []] pending
    (.letS localId (.call contextId [.byVal expression] origin) statementOrigin :: (globalIntegerAssignments assignments ++ [.print [.expr (.read (.var localId))] printOrigin])) guard stable terminalWorld
    fuel frame state types live regions world source phase ⟨rfl, scopes⟩ position initialized limit bounded
    prefixOwners prefixScalar prefixUnnamed

#print axioms execStmts_entryMixed_registerGlobalAssignmentsPrint_world
end Goose.Proofs.ConstructionAcceptedExecution
