import Goose.Proofs.ConstructionAcceptedArgumentListSequence
import Goose.Proofs.ConstructionAcceptedNestedScalarGlobalsTerminal

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem checkedSequence_nestedScalarGlobals (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl) (statements : List Stmt) (localId statementOrigin : Nat)
    (contextId callOrigin : Nat) (context : Context) (callee : Impl) (expressions : List Expr) (parameterTypes : List Ty)
    (resultTy : Ty) (resultExpression : Expr)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = statements ++ [.letS localId (.call contextId
      (expressions.map Arg.byVal) callOrigin) statementOrigin])
    (prefixForm : MixedLocalStatements statements)
    (prefixOwners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (prefixScalar : ∀ id expression origin, .letS id expression origin ∈ statements → AcceptedBinaryExpression expression →
      ∀ descriptor, implementation.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (localScalar : ∀ descriptor, implementation.vars[localId]? = some descriptor →
      (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (blockConditions : ∀ expression ∈ expressions, ∀ scope id origin blockOrigin value intTy literal,
      expression = .blockE ⟨scope, [.assign (.global id) value origin], some (.lit intTy literal)⟩ blockOrigin →
      scope ≠ implementation.body.scope ∧
      (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ scope) ∧
      (∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool))
    (nestedConditions : ∀ expression ∈ expressions, ∀ outerScope innerScope id origin innerOrigin outerOrigin value intTy literal,
      expression = .blockE ⟨outerScope, [], some (.blockE
        ⟨innerScope, [.assign (.global id) value origin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin →
      outerScope ≠ implementation.body.scope ∧ innerScope ≠ implementation.body.scope ∧ innerScope ≠ outerScope ∧
      (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ outerScope) ∧
      (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ innerScope) ∧
      (∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool))
    (contextAt : config.module.contexts[contextId]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (results : callee.results = #[⟨resultTy, .register, none⟩]) (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (forms : NestedEffectfulArguments expressions)
    (tail : callee.body.value = some resultExpression) (resultForm : AcceptedBinaryExpression resultExpression)
    (helperStatements : ScalarGlobalAssignments callee.body.stmts)
    (globalScalar : ∀ id expression origin, .assign (.global id) expression origin ∈ callee.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool) :
    ∀ (sequenceFuel : Nat) (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (before : ExecutionState)
      (types : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (scopeInst : Nat),
      AcceptedWorld config frame.initialized before [.callChannels activation []] types nextLive regions [] →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation config.module.entry →
      frame.source.impl = implementation →
      frame.interpretation.environment.scopes = (implementation.body.scope, scopeInst) :: activation.scopes →
      activation.scopes = [] →
      SourcePosition accepted frame (.statements implementation.body.stmts) →
      frame.initialized = config.module.globals.size → frame.typing.globalLimit ≤ config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      StatementWorldOutcome config accepted frame.initialized [.callChannels activation []] []
        (execStmts sequenceFuel config frame.interpretation.environment implementation.body.stmts before) := by
  intro sequenceFuel frame activation before types live regions scopeInst world source phase sourceImpl scopes activationEmpty position initialized limit bounded
  have fullPosition : SourcePosition accepted frame (.statements (statements ++ [.letS localId (.call contextId
      (expressions.map Arg.byVal) callOrigin) statementOrigin])) := by
    simpa [body] using position
  obtain ⟨entry, entryImpl, entryAt, implAt, entryParams, entryResults⟩ := validated_entry config.module accepted.accepted
  have entryEq : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have implEq : entryImpl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  subst entryImpl
  have unnamed : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
      (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none := by
    intro declaration member
    simp [sourceImpl, entryResults]
  let terminal : List Stmt := [.letS localId (.call contextId
    (expressions.map Arg.byVal) callOrigin) statementOrigin]
  let guard : ConstructionSourceFrame → Prop := fun current => current.source.impl = implementation ∧
    current.interpretation.environment.scopes = [(implementation.body.scope, scopeInst)]
  have initialGuard : guard frame := ⟨sourceImpl, by simpa [activationEmpty] using scopes⟩
  have guardStable : ∀ firstFrame nextFrame, firstFrame.source = nextFrame.source → firstFrame.interpretation = nextFrame.interpretation →
      firstFrame.phase = nextFrame.phase → guard firstFrame → guard nextFrame := by
    intro firstFrame nextFrame sameSource sameInterpretation samePhase valid
    simpa [guard, ← sameSource, ← sameInterpretation] using valid
  have terminalWorld : ∀ (fuel : Nat) (current : ConstructionSourceFrame) (state : ExecutionState) (currentTypes : RootTypes)
      (currentLive : Goose.Core.RootInst → Prop) (currentRegions : List ReceivingRegion),
      AcceptedWorld config current.initialized state [.callChannels activation []] currentTypes currentLive currentRegions [] →
      AcceptedFrame config accepted current state currentTypes → current.phase = .implementation config.module.entry → guard current →
      SourcePosition accepted current (.statements terminal) → current.initialized = config.module.globals.size →
      current.typing.globalLimit ≤ config.module.globals.size → GlobalEffectTargetsBounded current.rootCursor.eff config.module.globals.size →
      StatementWorldOutcome config accepted current.initialized [.callChannels activation []] []
        (execStmts fuel config current.interpretation.environment terminal state) := by
    intro fuel current state currentTypes currentLive currentRegions currentWorld currentSource currentPhase guarded terminalPosition currentInitialized currentLimit currentBounded
    cases fuel with
    | zero => simp only [execStmts, timeout, EvalM.stop, StatementWorldOutcome]; exact ⟨[.callChannels activation []], currentTypes, currentLive, currentRegions, currentWorld⟩
    | succ fuel =>
      obtain ⟨_, _, _, typed, _⟩ := terminalPosition.checked accepted current _
      cases currentFuel : current.typingFuel with
      | zero => rw [currentFuel] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ headFuel =>
        have head := terminalPosition.statements_head accepted current _ [] headFuel currentFuel
        have currentScopes : current.interpretation.environment.scopes = [(implementation.body.scope, scopeInst)] := guarded.2
        have currentScope : current.typing.scope = implementation.body.scope := by
          have sourceScopes : current.source.scopes = [implementation.body.scope] := by rw [currentSource.compatible.scopes, currentScopes]; rfl
          exact currentSource.compatible.currentScope implementation.body.scope [] sourceScopes
        have vars : current.interpretation.environment.vars = implementation.vars := by
          rw [currentSource.compatible.variables, ← currentSource.compatible.sourceVariables, guarded.1]
        have currentBlocks : ∀ expression ∈ expressions, NestedArgumentSafe config current expression := by
          intro expression member
          constructor
          · intro scope id origin blockOrigin value intTy literal equal
            obtain ⟨different, absent, globalScalar⟩ := blockConditions expression member scope id origin blockOrigin value intTy literal equal
            refine ⟨?_, ?_, globalScalar⟩
            · simp [currentScopes, different.symm]
            · simpa [vars] using absent
          · intro outerScope innerScope id origin innerOrigin outerOrigin value intTy literal equal
            obtain ⟨outerDifferent, innerDifferent, different, outerAbsent, innerAbsent, globalScalar⟩ :=
              nestedConditions expression member outerScope innerScope id origin innerOrigin outerOrigin value intTy literal equal
            refine ⟨?_, ?_, different, ?_, ?_, globalScalar⟩
            · simp [currentScopes, outerDifferent.symm]
            · simp [currentScopes, innerDifferent.symm]
            · simpa [vars] using outerAbsent
            · simpa [vars] using innerAbsent
        have currentScalar : ∀ descriptor, current.typing.variables[localId]? = some descriptor →
            (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
          intro descriptor declared
          apply localScalar descriptor
          simpa [← currentSource.compatible.sourceVariables, guarded.1] using declared
        let headFrame := { current with typingFuel := headFuel }
        have headSource := currentSource.withTypingFuel headFuel
        have statementWorld := nestedArgumentList_scalarGlobalsTerminal_world fuel headFrame state [.callChannels activation []] currentTypes currentLive currentRegions []
          contextId callOrigin context callee expressions parameterTypes resultTy resultExpression forms currentWorld headSource contextAt calleeAt
          descriptors results resultScalar tail resultForm helperStatements globalScalar currentInitialized currentBounded currentBlocks
          localId scopeInst statementOrigin [] (by simpa [headFrame, currentScope] using currentScopes) (by simpa [terminal, headFrame] using head) currentScalar
        simpa [terminal, headFrame] using execStmts_terminal_world fuel config accepted headFrame current.interpretation.environment _ state [.callChannels activation []] [] statementWorld
  simpa [body, terminal] using execStmts_mixedSuffix_world prefixForm config accepted config.module.entry [.callChannels activation []] [] terminal guard
    guardStable terminalWorld sequenceFuel frame before types live regions world source phase initialGuard fullPosition initialized limit bounded
    (by simpa [sourceImpl] using prefixOwners) (by simpa [sourceImpl] using prefixScalar) unnamed

theorem acceptedModule_nestedScalarGlobals_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl) (statements : List Stmt) (localId statementOrigin : Nat)
    (contextId callOrigin : Nat) (context : Context) (callee : Impl) (expressions : List Expr) (parameterTypes : List Ty)
    (resultTy : Ty) (resultExpression : Expr)
    (globals : ∀ globalId, globalId < config.module.globals.size →
      ∃ descriptor, config.module.globals[globalId]? = some descriptor ∧ RecursiveGlobalInitializer descriptor)
    (entryTail : implementation.body.value = none)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = statements ++ [.letS localId (.call contextId
      (expressions.map Arg.byVal) callOrigin) statementOrigin])
    (prefixForm : MixedLocalStatements statements)
    (prefixOwners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (prefixScalar : ∀ id expression origin, .letS id expression origin ∈ statements → AcceptedBinaryExpression expression →
      ∀ descriptor, implementation.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (localScalar : ∀ descriptor, implementation.vars[localId]? = some descriptor →
      (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (blockConditions : ∀ expression ∈ expressions, ∀ scope id origin blockOrigin value intTy literal,
      expression = .blockE ⟨scope, [.assign (.global id) value origin], some (.lit intTy literal)⟩ blockOrigin →
      scope ≠ implementation.body.scope ∧
      (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ scope) ∧
      (∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool))
    (nestedConditions : ∀ expression ∈ expressions, ∀ outerScope innerScope id origin innerOrigin outerOrigin value intTy literal,
      expression = .blockE ⟨outerScope, [], some (.blockE
        ⟨innerScope, [.assign (.global id) value origin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin →
      outerScope ≠ implementation.body.scope ∧ innerScope ≠ implementation.body.scope ∧ innerScope ≠ outerScope ∧
      (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ outerScope) ∧
      (∀ descriptor ∈ implementation.vars.toList, descriptor.scope ≠ innerScope) ∧
      (∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool))
    (contextAt : config.module.contexts[contextId]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (descriptors : ScalarParameterDescriptors callee 0 callee.params.toList parameterTypes)
    (results : callee.results = #[⟨resultTy, .register, none⟩]) (resultScalar : (∃ t, resultTy = .int t) ∨ resultTy = .bool)
    (forms : NestedEffectfulArguments expressions)
    (tail : callee.body.value = some resultExpression) (resultForm : AcceptedBinaryExpression resultExpression)
    (helperStatements : ScalarGlobalAssignments callee.body.stmts)
    (globalScalar : ∀ id expression origin, .assign (.global id) expression origin ∈ callee.body.stmts →
      ∀ descriptor, config.module.globals[id]? = some descriptor →
        (∃ t, descriptor.ty = .int t) ∨ descriptor.ty = .bool) :
    ∃ initialized ambient types live regions,
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState (runModule fuel config .initial)) ambient types live regions [] ∧
      (match runModule fuel config .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  apply acceptedModule_checkedRecursiveSequence_allFuelWithScopes fuel config accepted original implementation globals entryTail originalAt implementationAt
  exact checkedSequence_nestedScalarGlobals config accepted original implementation statements localId statementOrigin contextId callOrigin
    context callee expressions parameterTypes resultTy resultExpression
    originalAt implementationAt body prefixForm prefixOwners prefixScalar localScalar blockConditions nestedConditions contextAt calleeAt
    descriptors results resultScalar forms tail resultForm helperStatements globalScalar



#print axioms acceptedModule_nestedScalarGlobals_allFuel
#print axioms checkedSequence_nestedScalarGlobals
end Goose.Proofs.ConstructionAcceptedExecution
