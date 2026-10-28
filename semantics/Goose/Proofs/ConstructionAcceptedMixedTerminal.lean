import Goose.Proofs.ConstructionAcceptedTerminalSequence
import Goose.Proofs.ConstructionAcceptedMixedLocalExecution

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

private theorem mixedTerminal_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem execStmts_mixedTerminal_world {statements : List Stmt} (form : MixedLocalStatements statements)
    (config : EvalConfig) (accepted : AcceptedModule config) (context : Nat) (ambient : OwnershipAmbient)
    (pending : List PendingCarrierFrame) (terminal : Stmt) (guard : ConstructionSourceFrame → Prop)
    (guardStable : ∀ first next, first.source = next.source → first.interpretation = next.interpretation →
      first.phase = next.phase → guard first → guard next)
    (terminalWorld : ∀ (fuel : Nat) (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
      (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion),
      AcceptedWorld config frame.initialized state ambient types live regions pending →
      AcceptedFrame config accepted frame state types → frame.phase = .implementation context → guard frame →
      SourcePosition accepted frame (.statement terminal) → frame.initialized = config.module.globals.size →
      frame.typing.globalLimit ≤ config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      StatementWorldOutcome config accepted frame.initialized ambient pending
        (execStmt fuel config frame.interpretation.environment terminal state)) :
    ∀ (fuel : Nat) (frame : ConstructionSourceFrame) (before : ExecutionState) (types : RootTypes)
      (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion),
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation context → guard frame →
      SourcePosition accepted frame (.statements (statements ++ [terminal])) →
      frame.initialized = config.module.globals.size → frame.typing.globalLimit ≤ config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      (∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
        (frame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8))) →
      (∀ id expression origin, .letS id expression origin ∈ statements → AcceptedBinaryExpression expression →
        ∀ descriptor, frame.source.impl.vars[id]? = some descriptor →
          (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) →
      (∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
        (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none) →
      StatementWorldOutcome config accepted frame.initialized ambient pending
        (execStmts fuel config frame.interpretation.environment (statements ++ [terminal]) before) := by
  induction form with
  | nil =>
    intro fuel frame before types live regions world source phase guarded position initialized limit bounded owners scalarOwners unnamed
    cases fuel with
    | zero =>
      simp only [List.nil_append, execStmts, timeout, EvalM.stop, StatementWorldOutcome]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      obtain ⟨_, _, _, typed, _⟩ := position.checked accepted frame _
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ checkFuel =>
        have head := position.statements_head accepted frame terminal [] checkFuel nesting
        have checked := terminalWorld fuel { frame with typingFuel := checkFuel } before types live regions world
          (source.withTypingFuel checkFuel) phase (guardStable frame _ rfl rfl rfl guarded) head initialized limit bounded
        simpa only [List.nil_append] using execStmts_terminal_world fuel config accepted frame
          frame.interpretation.environment terminal before ambient pending checked
  | byte declaration rest tail ih =>
    intro fuel frame before types live regions world source phase guarded position initialized limit bounded owners scalarOwners unnamed
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, StatementWorldOutcome]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      obtain ⟨_, _, _, typedAll, _⟩ := position.checked accepted frame _
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
        | succ checkFuel =>
          have byteOwner : (frame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8)) := by
            rw [← source.compatible.sourceVariables]; exact owners declaration (by simp)
          have headUnnamed := unnamed declaration (by simp)
          have headPosition : SourcePosition accepted frame (.statements
              (.letS declaration.id (.bytes (.varr (.int .u8)) declaration.bytes declaration.bytesOrigin) declaration.origin :: (rest ++ [terminal]))) := by
            simpa only [List.cons_append, ByteOwnerDeclaration.statement] using position
          have headOutcome := execStmt_acceptedByteOwner_outcome fuel (checkFuel + 1) config accepted frame context declaration.id
            declaration.bytes declaration.origin declaration.bytesOrigin (rest ++ [terminal]) before ambient types live regions pending
            world source phase headPosition nesting byteOwner headUnnamed
          cases head : execStmt fuel config frame.interpretation.environment declaration.statement before with
          | stop reason after =>
            have head' := head
            simp only [ByteOwnerDeclaration.statement] at head'
            simp only [head'] at headOutcome
            obtain ⟨nextRegions, finalWorld, finalSource⟩ := headOutcome
            simp only [List.cons_append, execStmts, bind, head, StatementWorldOutcome]
            exact ⟨ambient, types, live, nextRegions, finalWorld⟩
          | escape address carriers after | jump target kind after =>
            have head' := head
            simp only [ByteOwnerDeclaration.statement] at head'
            simp only [head'] at headOutcome
          | ok flow middle =>
            have head' := head
            simp only [ByteOwnerDeclaration.statement] at head'
            simp only [head'] at headOutcome
            obtain ⟨normal, scopeInst, stored, published, extended, middleWorld, middleSource, middlePosition⟩ := headOutcome
            subst flow
            let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst declaration.id
            let nextTypes := registerRootType types root (.varr (.int .u8))
            let nextFrame := advanceLocalFrame { frame with typingFuel := checkFuel + 1 } declaration.id
            let nextLive := fun other => other = root ∨ live other
            let nextRegions := regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent published stored.storage))
            have remainingOwners : ∀ item : ByteOwnerDeclaration, item.statement ∈ rest →
                (nextFrame.source.impl.vars[item.id]?).map (·.ty) = some (.varr (.int .u8)) := by
              intro item member; exact owners item (List.mem_cons_of_mem declaration.statement member)
            have remainingUnnamed : ∀ item : ByteOwnerDeclaration, item.statement ∈ rest →
                (nextFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some item.id)) = none := by
              intro item member; exact unnamed item (List.mem_cons_of_mem declaration.statement member)
            have result := ih fuel nextFrame middle nextTypes nextLive nextRegions middleWorld middleSource
              (by simpa [nextFrame, advanceLocalFrame] using phase)
              (guardStable frame nextFrame rfl rfl rfl guarded) middlePosition initialized limit bounded remainingOwners
              (by intro id expression origin member shape descriptor found; exact scalarOwners id expression origin (List.mem_cons_of_mem _ member) shape descriptor found)
              remainingUnnamed
            simpa only [List.cons_append, execStmts, bind, head, nextFrame, advanceLocalFrame] using result
  | scalar expression origin rest expressionForm tail ih =>
    intro fuel frame before types live regions world source phase guarded position initialized limit bounded owners scalarOwners unnamed
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, StatementWorldOutcome]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      obtain ⟨finalTyping, finalCounter, finalRoots, typedAll, rootedAll⟩ := position.checked accepted frame _
      obtain ⟨rootMiddle, headRooted, tailRooted⟩ := rpStmts_cons rootedAll
      obtain ⟨roots, expressionRooted⟩ := rpStmt_expression headRooted
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
        | succ checkFuel =>
          have headPosition := position.statements_head accepted frame (.expr expression origin) (rest ++ [terminal]) (checkFuel + 1) nesting
          obtain ⟨next, statementAfter, headRoots, headTyped, headRooted'⟩ := headPosition.checked accepted _ _
          have sameHead : headRoots = rootMiddle := (Prod.mk.inj (Except.ok.inj (headRooted'.symm.trans headRooted))).2
          subst headRoots
          have headTyped' := headTyped
          simp only [typeStatement, bind, StateT.bind] at headTyped'
          change (Except.bind (typeExpr checkFuel (ordinaryOperandFrame frame checkFuel).typing expression frame.typingCounter) _) = _ at headTyped'
          obtain ⟨result, expressionTyped, remaining⟩ := mixedTerminal_bind_success _ _ _ headTyped'
          obtain ⟨resultTypes, typingAfter⟩ := result
          obtain ⟨ty, sameTypes⟩ := typeExpr_scalar_singleton expressionForm checkFuel (ordinaryOperandFrame frame checkFuel).typing
            frame.typingCounter typingAfter resultTypes expressionTyped
          subst resultTypes
          have middleBounded := recursiveScalar_effects_bounded expressionForm checkFuel (ordinaryOperandFrame frame checkFuel).typing
            frame.source config.module.globals.size frame.typingCounter typingAfter frame.rootCursor rootMiddle [ty] roots limit bounded expressionTyped expressionRooted
          have headAvailable : GlobalEffectsAvailable frame.interpretation frame.initialized rootMiddle.eff := by
            rw [initialized, ← source.compatible.globalCount]
            exact (globalEffectsAvailable_iff_bounded frame.interpretation rootMiddle.eff).2
              (by simpa only [source.compatible.globalCount] using middleBounded)
          have checked : CheckedValue (ordinaryOperandFrame frame checkFuel) expression ty roots typingAfter rootMiddle :=
            ⟨expressionTyped, expressionRooted, headAvailable⟩
          obtain ⟨sameTyping, sameCounter, nextSource⟩ := checkedScalarExpression_statementAdvance config accepted frame before types source
            expression origin expressionForm checkFuel ty roots typingAfter rootMiddle checked next statementAfter rootMiddle headTyped headRooted
          subst next statementAfter
          let nextFrame := { frame with typingFuel := checkFuel + 1, rootCursor := rootMiddle }
          have nextPosition := position.statements_tail accepted frame (.expr expression origin) (rest ++ [terminal]) (checkFuel + 1) frame.typing frame.typingCounter
            rootMiddle nesting headTyped headRooted
          have headOutcome := execStmt_checkedScalarExpression_complete expression origin expressionForm fuel checkFuel config accepted frame before
            ambient types live regions pending world source ty roots typingAfter rootMiddle checked
          have control := execStmt_scalar_controlFree expression origin expressionForm fuel config frame.interpretation.environment
          cases head : execStmt fuel config frame.interpretation.environment (.expr expression origin) before with
          | stop reason after =>
            simp only [head, Goose.Proofs.Exit.stepState] at headOutcome
            have same := headOutcome.1
            subst after
            simp only [List.cons_append, execStmts, bind, head, StatementWorldOutcome]
            exact ⟨ambient, types, live, regions, world⟩
          | escape address carriers after => exact (control.1 before address carriers after head).elim
          | jump target kind after => exact (control.2 before target kind after head).elim
          | ok flow middle =>
            obtain ⟨normal, same⟩ := headOutcome.2.1 flow middle head
            subst flow middle
            have remainingOwners : ∀ item : ByteOwnerDeclaration, item.statement ∈ rest →
                (nextFrame.source.impl.vars[item.id]?).map (·.ty) = some (.varr (.int .u8)) := by
              intro item member; exact owners item (List.mem_cons_of_mem _ member)
            have remainingUnnamed : ∀ item : ByteOwnerDeclaration, item.statement ∈ rest →
                (nextFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some item.id)) = none := by
              intro item member; exact unnamed item (List.mem_cons_of_mem _ member)
            have result := ih fuel nextFrame before types live regions world nextSource phase
              (guardStable frame nextFrame rfl rfl rfl guarded) nextPosition initialized limit middleBounded remainingOwners
              (by intro id expression origin member shape descriptor found; exact scalarOwners id expression origin (List.mem_cons_of_mem _ member) shape descriptor found)
              remainingUnnamed
            simpa only [List.cons_append, execStmts, bind, head, nextFrame] using result
  | scalarLocal id expression origin rest expressionForm tail ih =>
    intro fuel frame before types live regions world source phase guarded position initialized limit bounded owners scalarOwners unnamed
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, StatementWorldOutcome]
      exact ⟨ambient, types, live, regions, world⟩
    | succ fuel =>
      obtain ⟨_, _, _, typedAll, _⟩ := position.checked accepted frame _
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
        | succ checkFuel =>
          have localScalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
              (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
            intro descriptor declared
            apply scalarOwners id expression origin (by simp) expressionForm descriptor
            rw [source.compatible.sourceVariables]; exact declared
          have headOutcome := execStmt_acceptedScalarLocal_outcome fuel checkFuel config accepted frame context id expression origin (rest ++ [terminal])
            before ambient types live regions pending expressionForm world source phase position nesting initialized bounded localScalar
          cases head : execStmt fuel config frame.interpretation.environment (.letS id expression origin) before with
          | stop reason after =>
            simp only [head] at headOutcome
            obtain ⟨finalWorld, finalSource⟩ := headOutcome
            simp only [List.cons_append, execStmts, bind, head, StatementWorldOutcome]
            exact ⟨ambient, types, live, regions, finalWorld⟩
          | escape address carriers after | jump target kind after => simp only [head] at headOutcome
          | ok flow middle =>
            simp only [head] at headOutcome
            obtain ⟨normal, scopeInst, descriptor, rootsAfter, extended, middleWorld, middleSource, middlePosition, middleBounded⟩ := headOutcome
            subst flow
            let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
            let nextTypes := registerRootType types root descriptor.ty
            let nextFrame := { advanceLocalFrame { frame with typingFuel := checkFuel + 1 } id with rootCursor := rootsAfter }
            let nextLive := fun other => other = root ∨ live other
            have remainingOwners : ∀ item : ByteOwnerDeclaration, item.statement ∈ rest →
                (nextFrame.source.impl.vars[item.id]?).map (·.ty) = some (.varr (.int .u8)) := by
              intro item member; exact owners item (List.mem_cons_of_mem _ member)
            have remainingScalar : ∀ id expression origin, .letS id expression origin ∈ rest → AcceptedBinaryExpression expression →
                ∀ descriptor, nextFrame.source.impl.vars[id]? = some descriptor →
                  (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
              intro id expression origin member shape descriptor found
              exact scalarOwners id expression origin (List.mem_cons_of_mem _ member) shape descriptor found
            have remainingUnnamed : ∀ item : ByteOwnerDeclaration, item.statement ∈ rest →
                (nextFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some item.id)) = none := by
              intro item member; exact unnamed item (List.mem_cons_of_mem _ member)
            have result := ih fuel nextFrame middle nextTypes nextLive regions middleWorld middleSource
              (by simpa [nextFrame, advanceLocalFrame] using phase)
              (guardStable frame nextFrame rfl rfl rfl guarded) middlePosition initialized limit middleBounded
                remainingOwners remainingScalar remainingUnnamed
            simpa only [List.cons_append, execStmts, bind, head, nextFrame, advanceLocalFrame] using result

#print axioms execStmts_mixedTerminal_world
end Goose.Proofs.ConstructionAcceptedExecution
