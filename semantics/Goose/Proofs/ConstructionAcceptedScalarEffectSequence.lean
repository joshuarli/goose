import Goose.Proofs.ConstructionAcceptedScalarEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private theorem effectSequence_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem ScalarExpressionStatements.effects_bounded {statements : List Stmt} (form : ScalarExpressionStatements statements) :
    ∀ (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (count : Nat),
      SourcePosition accepted frame (.statements statements) → frame.typing.globalLimit ≤ count →
      GlobalEffectTargetsBounded frame.rootCursor.eff count →
      ∀ final, rpStmts frame.source statements frame.rootCursor = .ok ((), final) →
        GlobalEffectTargetsBounded final.eff count := by
  induction form with
  | nil =>
    intro config accepted frame count position limit bounded final rooted
    change Except.ok ((), frame.rootCursor) = Except.ok ((), final) at rooted
    cases rooted
    exact bounded
  | cons expression origin rest expressionForm tail ih =>
    intro config accepted frame count position limit bounded final rooted
    obtain ⟨_, _, _, typedAll, _⟩ := position.checked accepted frame _
    obtain ⟨middle, headRooted, tailRooted⟩ := rpStmts_cons rooted
    obtain ⟨operandRoots, operandRooted⟩ := rpStmt_expression headRooted
    cases nesting : frame.typingFuel with
    | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
    | succ headFuel =>
      cases headFuel with
      | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
      | succ checkFuel =>
        have headPosition := position.statements_head accepted frame (.expr expression origin) rest (checkFuel + 1) nesting
        obtain ⟨next, nextCounter, nextRoots, headTyped, headRooted'⟩ := headPosition.checked accepted _ _
        have sameRoots : nextRoots = middle := (Prod.mk.inj (Except.ok.inj (headRooted'.symm.trans headRooted))).2
        subst nextRoots
        have headTyped' := headTyped
        simp only [typeStatement, bind, StateT.bind] at headTyped'
        change (Except.bind (typeExpr checkFuel (ordinaryOperandFrame frame checkFuel).typing expression frame.typingCounter) _) = _ at headTyped'
        obtain ⟨result, operandTyped, remaining⟩ := effectSequence_bind_success _ _ _ headTyped'
        obtain ⟨operandTypes, counter⟩ := result
        obtain ⟨result, required, returned⟩ := effectSequence_bind_success _ _ _ remaining
        cases returned
        cases fixed : operandTypes.all (fun ty => !ty.nonfixed) with
        | false =>
          simp only [fixed] at required
          change Except.error _ = Except.ok _ at required
          cases required
        | true =>
          simp only [fixed] at required
          change Except.ok ((), counter) = Except.ok result at required
          cases required
          have middleBounded := recursiveScalar_effects_bounded expressionForm checkFuel (ordinaryOperandFrame frame checkFuel).typing
            frame.source count frame.typingCounter counter frame.rootCursor middle operandTypes operandRoots limit bounded operandTyped operandRooted
          have nextPosition := position.statements_tail accepted frame (.expr expression origin) rest (checkFuel + 1) frame.typing counter
            middle nesting headTyped headRooted
          exact ih config accepted _ count nextPosition limit middleBounded final tailRooted

theorem ScalarExpressionStatements.entryEffects_available (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (source : AcceptedFrame config accepted frame state types) (scopeInst : Nat)
    (initialized : frame.initialized = config.module.globals.size)
    (form : ScalarExpressionStatements frame.source.impl.body.stmts)
    (position : SourcePosition accepted (entryStatementsFrame config frame scopeInst) (.statements frame.source.impl.body.stmts)) :
    ∀ final, rpStmts (entryStatementsFrame config frame scopeInst).source frame.source.impl.body.stmts
      (entryStatementsFrame config frame scopeInst).rootCursor = .ok ((), final) →
      GlobalEffectsAvailable (entryStatementsFrame config frame scopeInst).interpretation
        (entryStatementsFrame config frame scopeInst).initialized final.eff := by
  intro final rooted
  let next := entryStatementsFrame config frame scopeInst
  have limit : next.typing.globalLimit ≤ config.module.globals.size := by simp [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]
  have initial : GlobalEffectTargetsBounded next.rootCursor.eff config.module.globals.size := by
    simp [GlobalEffectTargetsBounded, Eff.accessTargets, next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]
  have bounded := form.effects_bounded config accepted next config.module.globals.size position limit initial final rooted
  have count : next.interpretation.globalCount = config.module.globals.size := by
    simpa only [next, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, RootInterpretation.enterScope] using
      source.compatible.globalCount
  have initialized' : next.initialized = next.interpretation.globalCount := by
    change frame.initialized = next.interpretation.globalCount
    rw [initialized, count]
  rw [initialized']
  apply (globalEffectsAvailable_iff_bounded next.interpretation final.eff).2
  simpa only [count] using bounded

theorem acceptedEntry_scalarStatements_unconditional (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState)
    (ambient : Goose.Proofs.ConstructionExecutionOwnership.OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (phase : frame.phase = .implementation config.module.entry)
    (parametersEmpty : frame.source.impl.params = #[]) (scopes : frame.interpretation.environment.scopes = [])
    (initialized : frame.initialized = config.module.globals.size) (cursor : frame.rootCursor = ⟨0, {}, []⟩)
    (form : ScalarExpressionStatements frame.source.impl.body.stmts) (fuel : Nat) :
    let next := entryStatementsFrame config frame state.nextScope
    let after := { state with nextScope := state.nextScope + 1 }
    freshScope state = .ok state.nextScope after ∧
      Goose.Proofs.Exit.stepState (execStmts fuel config next.interpretation.environment frame.source.impl.body.stmts after) = after ∧
      AcceptedWorld config next.initialized
        (Goose.Proofs.Exit.stepState (execStmts fuel config next.interpretation.environment frame.source.impl.body.stmts after))
        ambient types live regions pending ∧
      AcceptedFrame config accepted next
        (Goose.Proofs.Exit.stepState (execStmts fuel config next.interpretation.environment frame.source.impl.body.stmts after)) types := by
  obtain ⟨_, _, _, position⟩ := acceptedEntryStatementsFrame config accepted frame state ambient types live regions pending
    world source phase parametersEmpty scopes initialized cursor
  have available := form.entryEffects_available config accepted frame state types source state.nextScope initialized position
  exact acceptedEntry_scalarStatements_complete config accepted frame state ambient types live regions pending world source phase
    parametersEmpty scopes initialized cursor form available fuel

#print axioms acceptedEntry_scalarStatements_unconditional
#print axioms ScalarExpressionStatements.entryEffects_available
#print axioms ScalarExpressionStatements.effects_bounded
end Goose.Proofs.ConstructionAcceptedExecution
