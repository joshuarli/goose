import Goose.Proofs.ConstructionAcceptedMixedLocalExecution
import Goose.Proofs.ConstructionScalarLocalReplayOutcome
import Goose.Proofs.ConstructionByteReplay
import Goose.Proofs.ConstructionAcceptedByteObservation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

private theorem mixedLocalProtected_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem execStmts_mixedLocal_observed_world {statements : List Stmt} (form : MixedLocalStatements statements) :
    ∀ (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
      (frame : ConstructionSourceFrame) (context : Nat) (before : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
      (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation context →
      SourcePosition accepted frame (.statements statements) →
      frame.initialized = config.module.globals.size → frame.typing.globalLimit ≤ config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      (∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
        (frame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8))) →
      (∀ id expression origin, .letS id expression origin ∈ statements → AcceptedBinaryExpression expression →
        ∀ descriptor, frame.source.impl.vars[id]? = some descriptor →
          (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) →
      (∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
        (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none) →
      ∃ (next : ConstructionSourceFrame) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop)
        (nextRegions : List ReceivingRegion),
        let outcome := execStmts fuel config frame.interpretation.environment statements before
        let after := Goose.Proofs.Exit.stepState outcome
        next.initialized = frame.initialized ∧ RootTypesExtend types nextTypes ∧
        AcceptedWorld config next.initialized after ambient nextTypes nextLive nextRegions pending ∧
        AcceptedFrame config accepted next after nextTypes ∧
        (match outcome with | .ok flow _ => flow = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) ∧
        next.source = frame.source ∧ next.interpretation = frame.interpretation ∧ next.phase = frame.phase ∧
        next.typing.globalLimit = frame.typing.globalLimit ∧ GlobalEffectTargetsBounded next.rootCursor.eff config.module.globals.size ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local frame.interpretation.environment.act scope id) → nextTypes root = types root) ∧
        (match outcome with
        | .ok _ _ => after.nextAct = before.nextAct ∧ after.nextScope = before.nextScope
        | _ => True) ∧
        (match outcome with
        | .ok _ _ => ∀ other, (∀ scope id, other ≠ Goose.Core.RootInst.local frame.interpretation.environment.act scope id) →
            after.objects.lookup other = before.objects.lookup other ∧ after.objectOrdinals.lookup other = before.objectOrdinals.lookup other
        | _ => True) ∧
        (match outcome with
        | .ok _ _ => typeStatements frame.typingFuel frame.typing statements frame.typingCounter = .ok (next.typing, next.typingCounter) ∧
            rpStmts frame.source statements frame.rootCursor = .ok ((), next.rootCursor)
        | _ => True) := by
  induction form with
  | nil =>
    intro fuel config accepted frame context before ambient types live regions pending world source phase position initialized limit bounded owners scalarOwners unnamed
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial, rfl, rfl, rfl, rfl, bounded, (fun _ _ => rfl), trivial, trivial, trivial⟩
    | succ fuel =>
      obtain ⟨next, counter, roots, typed, rooted⟩ := position.checked accepted frame _
      cases check : frame.typingFuel with
      | zero => rw [check] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ checkFuel =>
        have replay : typeStatements frame.typingFuel frame.typing [] frame.typingCounter = .ok (frame.typing, frame.typingCounter) := by
          simp [check, typeStatements, pure, StateT.pure, Except.pure]
        simp only [execStmts, pure, Goose.Proofs.Exit.stepState]
        exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial, rfl, rfl, rfl, rfl, bounded, (fun _ _ => rfl), ⟨trivial, trivial⟩, (fun _ _ => ⟨trivial, trivial⟩), ⟨(by simpa only [check] using replay), rfl⟩⟩
  | byte declaration rest tail ih =>
    intro fuel config accepted frame context before ambient types live regions pending world source phase position initialized limit bounded owners scalarOwners unnamed
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial, rfl, rfl, rfl, rfl, bounded, (fun _ _ => rfl), trivial, trivial, trivial⟩
    | succ fuel =>
      obtain ⟨_, _, _, typedAll, _⟩ := position.checked accepted frame _
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
        | succ checkFuel =>
          have byteOwner : (frame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8)) := by
            rw [← source.compatible.sourceVariables]
            exact owners declaration (by simp)
          have headUnnamed := unnamed declaration (by simp)
          have headPosition : SourcePosition accepted frame (.statements
              (.letS declaration.id (.bytes (.varr (.int .u8)) declaration.bytes declaration.bytesOrigin) declaration.origin :: rest)) := by
            simpa only [ByteOwnerDeclaration.statement] using position
          have headOutcome := execStmt_acceptedByteOwner_outcome fuel (checkFuel + 1) config accepted frame context declaration.id
            declaration.bytes declaration.origin declaration.bytesOrigin rest before ambient types live regions pending
            world source phase headPosition nesting byteOwner headUnnamed
          cases head : execStmt fuel config frame.interpretation.environment declaration.statement before with
          | stop reason after =>
            have head' := head
            simp only [ByteOwnerDeclaration.statement] at head'
            simp only [head'] at headOutcome
            obtain ⟨nextRegions, finalWorld, finalSource⟩ := headOutcome
            simp only [execStmts, bind, head, Goose.Proofs.Exit.stepState]
            exact ⟨frame, types, live, nextRegions, rfl, (fun _ _ found => found), finalWorld, finalSource, trivial, rfl, rfl, rfl, rfl, bounded, (fun _ _ => rfl), trivial, trivial, trivial⟩
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
            have headReplay : typeStatement (checkFuel + 1) frame.typing declaration.statement frame.typingCounter =
                .ok (nextFrame.typing, nextFrame.typingCounter) ∧
                rpStmt frame.source declaration.statement frame.rootCursor = .ok ((), nextFrame.rootCursor) := by
              cases fuel with
              | zero => simp [execStmt, ByteOwnerDeclaration.statement, timeout, EvalM.stop] at head
              | succ fuel =>
                cases fuel with
                | zero =>
                  have hp := headPosition.statements_head accepted frame declaration.statement rest (checkFuel + 1) nesting
                  obtain ⟨typingNext, typingAfter, rootsAfter, typed, rooted⟩ := hp.checked accepted _ _
                  have impossible := execStmt_acceptedByteOwner_one_ne_ok config accepted
                    { frame with typingFuel := checkFuel + 1 } context declaration.id declaration.bytes declaration.origin
                    declaration.bytesOrigin before middle (.normal .unit) types typingNext typingAfter
                    (source.withTypingFuel (checkFuel + 1)) phase
                    (by simpa [ByteOwnerDeclaration.statement] using typed) byteOwner headUnnamed
                  exact (impossible (by simpa [ByteOwnerDeclaration.statement] using head)).elim
                | succ fuel =>
                  exact execStmt_byteOwner_replay fuel (checkFuel + 1) config accepted frame context declaration rest
                    before middle ambient types live regions pending world source phase headPosition nesting byteOwner headUnnamed head
            have remainingOwners : ∀ item : ByteOwnerDeclaration, item.statement ∈ rest →
                (nextFrame.source.impl.vars[item.id]?).map (·.ty) = some (.varr (.int .u8)) := by
              intro item member; exact owners item (List.mem_cons_of_mem declaration.statement member)
            have remainingUnnamed : ∀ item : ByteOwnerDeclaration, item.statement ∈ rest →
                (nextFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some item.id)) = none := by
              intro item member; exact unnamed item (List.mem_cons_of_mem declaration.statement member)
            obtain ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, finalExtended, finalWorld, finalSource, finalFlow, finalSourceEq, finalInterpretationEq, finalPhaseEq, finalLimitEq, finalBounded, finalProtected, finalCounters, finalObserved, finalReplay⟩ :=
              ih fuel config accepted nextFrame context middle ambient nextTypes nextLive nextRegions pending middleWorld middleSource
                (by simpa [nextFrame, advanceLocalFrame] using phase) middlePosition initialized limit bounded remainingOwners (by intro id expression origin member shape descriptor found; exact scalarOwners id expression origin (List.mem_cons_of_mem _ member) shape descriptor found) remainingUnnamed
            simp only [execStmts, bind, head]
            refine ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, ?_, finalWorld, finalSource, finalFlow, finalSourceEq, finalInterpretationEq, finalPhaseEq, finalLimitEq, finalBounded, ?_, ?_, ?_, ?_⟩
            · intro oldRoot ty found
              exact finalExtended oldRoot ty (extended oldRoot ty found)
            · intro other outside
              have different : other ≠ root := outside scopeInst _
              have unchanged := finalProtected other (by simpa [nextFrame, advanceLocalFrame] using outside)
              simpa [nextTypes, registerRootType, different] using unchanged
            · simp only [nextFrame, advanceLocalFrame] at finalCounters
              cases tailExecution : execStmts fuel config frame.interpretation.environment rest middle with
              | ok result after =>
                simp only [tailExecution, Goose.Proofs.Exit.stepState] at finalCounters ⊢
                cases fuel with
                | zero => simp [execStmt, ByteOwnerDeclaration.statement, timeout, EvalM.stop] at head
                | succ fuel =>
                  cases fuel with
                  | zero =>
                    have hp := headPosition.statements_head accepted frame declaration.statement rest (checkFuel + 1) nesting
                    obtain ⟨typingNext, typingAfter, rootsAfter, typed, rooted⟩ := hp.checked accepted _ _
                    have impossible := execStmt_acceptedByteOwner_one_ne_ok config accepted
                      { frame with typingFuel := checkFuel + 1 } context declaration.id declaration.bytes declaration.origin
                      declaration.bytesOrigin before middle (.normal .unit) types typingNext typingAfter
                      (source.withTypingFuel (checkFuel + 1)) phase
                      (by simpa [ByteOwnerDeclaration.statement] using typed) byteOwner headUnnamed
                    exact (impossible (by simpa [ByteOwnerDeclaration.statement] using head)).elim
                  | succ fuel =>
                    obtain ⟨scopeInst, stored, published, ⟨frame⟩, bound⟩ :=
                      execStmt_byteOwner_observation fuel config accepted { frame with typingFuel := checkFuel + 1 }
                        context declaration.id declaration.bytes declaration.origin declaration.bytesOrigin before middle ambient types live
                        regions pending nextFrame.rootCursor nextFrame.typing nextFrame.typingCounter world
                        (source.withTypingFuel (checkFuel + 1)) phase headReplay.2 headReplay.1 byteOwner headUnnamed
                        (by simpa [ByteOwnerDeclaration.statement] using head)
                    have first := freshDestination_bindRoot_counters before published middle _ stored frame bound
                    exact ⟨finalCounters.1.trans first.1, finalCounters.2.trans first.2⟩
              | stop reason after | escape _ _ after | jump _ _ after => simp only [tailExecution]
            · simp only [nextFrame, advanceLocalFrame] at finalObserved
              cases tailExecution : execStmts fuel config frame.interpretation.environment rest middle with
              | ok result after =>
                simp only [tailExecution] at finalObserved ⊢
                intro other outside
                have tailObserved := finalObserved other (by simpa [nextFrame, advanceLocalFrame] using outside)
                cases fuel with
                | zero => simp [execStmt, ByteOwnerDeclaration.statement, timeout, EvalM.stop] at head
                | succ fuel =>
                  cases fuel with
                  | zero =>
                    have hp := headPosition.statements_head accepted frame declaration.statement rest (checkFuel + 1) nesting
                    obtain ⟨typingNext, typingAfter, rootsAfter, typed, rooted⟩ := hp.checked accepted _ _
                    have impossible := execStmt_acceptedByteOwner_one_ne_ok config accepted
                      { frame with typingFuel := checkFuel + 1 } context declaration.id declaration.bytes declaration.origin
                      declaration.bytesOrigin before middle (.normal .unit) types typingNext typingAfter
                      (source.withTypingFuel (checkFuel + 1)) phase
                      (by simpa [ByteOwnerDeclaration.statement] using typed) byteOwner headUnnamed
                    exact (impossible (by simpa [ByteOwnerDeclaration.statement] using head)).elim
                  | succ fuel =>
                    have first := execStmt_byteOwner_outside fuel config accepted { frame with typingFuel := checkFuel + 1 }
                      context declaration.id declaration.bytes declaration.origin declaration.bytesOrigin before middle ambient types live
                      regions pending nextFrame.rootCursor nextFrame.typing nextFrame.typingCounter world
                      (source.withTypingFuel (checkFuel + 1)) phase headReplay.2 headReplay.1 byteOwner headUnnamed
                      (by simpa [ByteOwnerDeclaration.statement] using head) other outside
                    exact ⟨tailObserved.1.trans first.1, tailObserved.2.trans first.2⟩
              | stop reason after | escape _ _ after | jump _ _ after => simp only [tailExecution]
            · simp only [nextFrame, advanceLocalFrame] at finalReplay
              cases tailExecution : execStmts fuel config frame.interpretation.environment rest middle with
              | ok value after =>
                simp only [tailExecution] at finalReplay ⊢
                have replay := statementReplay_cons (checkFuel + 1) frame nextFrame finalFrame declaration.statement rest
                  headReplay.1 headReplay.2 rfl finalReplay.1 finalReplay.2
                simpa only [nesting] using replay
              | stop reason after | escape _ _ after | jump _ _ after => simp only [tailExecution] at finalReplay ⊢
  | scalar expression origin rest expressionForm tail ih =>
    intro fuel config accepted frame context before ambient types live regions pending world source phase position initialized limit bounded owners scalarOwners unnamed
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial, rfl, rfl, rfl, rfl, bounded, (fun _ _ => rfl), trivial, trivial, trivial⟩
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
          have headPosition := position.statements_head accepted frame (.expr expression origin) rest (checkFuel + 1) nesting
          obtain ⟨next, statementAfter, headRoots, headTyped, headRooted'⟩ := headPosition.checked accepted _ _
          have sameHead : headRoots = rootMiddle := (Prod.mk.inj (Except.ok.inj (headRooted'.symm.trans headRooted))).2
          subst headRoots
          have headTyped' := headTyped
          simp only [typeStatement, bind, StateT.bind] at headTyped'
          change (Except.bind (typeExpr checkFuel (ordinaryOperandFrame frame checkFuel).typing expression frame.typingCounter) _) = _ at headTyped'
          obtain ⟨result, expressionTyped, remaining⟩ := mixedLocalProtected_bind_success _ _ _ headTyped'
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
          have nextPosition := position.statements_tail accepted frame (.expr expression origin) rest (checkFuel + 1) frame.typing frame.typingCounter
            rootMiddle nesting headTyped headRooted
          have headOutcome := execStmt_checkedScalarExpression_complete expression origin expressionForm fuel checkFuel config accepted frame before
            ambient types live regions pending world source ty roots typingAfter rootMiddle checked
          have control := execStmt_scalar_controlFree expression origin expressionForm fuel config frame.interpretation.environment
          cases head : execStmt fuel config frame.interpretation.environment (.expr expression origin) before with
          | stop reason after =>
            simp only [head, Goose.Proofs.Exit.stepState] at headOutcome
            have same := headOutcome.1
            subst after
            simp only [execStmts, bind, head, Goose.Proofs.Exit.stepState]
            exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial, rfl, rfl, rfl, rfl, bounded, (fun _ _ => rfl), trivial, trivial, trivial⟩
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
            obtain ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, finalExtended, finalWorld, finalSource, finalFlow, finalSourceEq, finalInterpretationEq, finalPhaseEq, finalLimitEq, finalBounded, finalProtected, finalCounters, finalObserved, finalReplay⟩ :=
              ih fuel config accepted nextFrame context before ambient types live regions pending world nextSource phase nextPosition
                initialized limit middleBounded remainingOwners (by intro id expression origin member shape descriptor found; exact scalarOwners id expression origin (List.mem_cons_of_mem _ member) shape descriptor found) remainingUnnamed
            simp only [execStmts, bind, head]
            refine ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, finalExtended, finalWorld, finalSource, finalFlow,
              finalSourceEq, finalInterpretationEq, finalPhaseEq, finalLimitEq, finalBounded, ?_, ?_, ?_, ?_⟩
            · intro other outside
              exact finalProtected other (by simpa [nextFrame] using outside)
            · simp only [nextFrame] at finalCounters
              cases tailExecution : execStmts fuel config frame.interpretation.environment rest before with
              | ok result after => simpa only [tailExecution, Goose.Proofs.Exit.stepState] using finalCounters
              | stop reason after | escape _ _ after | jump _ _ after => simp only [tailExecution]
            · simp only [nextFrame] at finalObserved
              cases tailExecution : execStmts fuel config frame.interpretation.environment rest before with
              | ok result after =>
                simp only [tailExecution] at finalObserved ⊢
                exact fun other outside => finalObserved other (by simpa [nextFrame] using outside)
              | stop reason after | escape _ _ after | jump _ _ after => simp only [tailExecution]
            · simp only [nextFrame] at finalReplay
              cases tailExecution : execStmts fuel config frame.interpretation.environment rest before with
              | ok value after =>
                simp only [tailExecution] at finalReplay ⊢
                have replay := statementReplay_cons (checkFuel + 1) frame nextFrame finalFrame (.expr expression origin) rest
                  headTyped headRooted rfl finalReplay.1 finalReplay.2
                simpa only [nesting] using replay
              | stop reason after | escape _ _ after | jump _ _ after => simp only [tailExecution] at finalReplay ⊢

  | scalarLocal id expression origin rest expressionForm tail ih =>
    intro fuel config accepted frame context before ambient types live regions pending world source phase position initialized limit bounded owners scalarOwners unnamed
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial, rfl, rfl, rfl, rfl, bounded, (fun _ _ => rfl), trivial, trivial, trivial⟩
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
          have headOutcome := execStmt_acceptedScalarLocal_observedOutcome fuel checkFuel config accepted frame context id expression origin rest
            before ambient types live regions pending expressionForm world source phase position nesting initialized bounded localScalar
          cases head : execStmt fuel config frame.interpretation.environment (.letS id expression origin) before with
          | stop reason after =>
            simp only [head] at headOutcome
            obtain ⟨finalWorld, finalSource⟩ := headOutcome
            simp only [execStmts, bind, head, Goose.Proofs.Exit.stepState]
            exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), finalWorld, finalSource, trivial, rfl, rfl, rfl, rfl, bounded, (fun _ _ => rfl), trivial, trivial, trivial⟩
          | escape address carriers after | jump target kind after => simp only [head] at headOutcome
          | ok flow middle =>
            simp only [head] at headOutcome
            obtain ⟨normal, scopeInst, descriptor, rootsAfter, headReplayTyped, headReplayRooted, extended, middleWorld, middleSource, middlePosition, middleBounded, headCounters, headObserved⟩ := headOutcome
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
            obtain ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, finalExtended, finalWorld, finalSource, finalFlow, finalSourceEq, finalInterpretationEq, finalPhaseEq, finalLimitEq, finalBounded, finalProtected, finalCounters, finalObserved, finalReplay⟩ :=
              ih fuel config accepted nextFrame context middle ambient nextTypes nextLive regions pending middleWorld middleSource
                (by simpa [nextFrame, advanceLocalFrame] using phase) middlePosition initialized limit middleBounded
                  remainingOwners remainingScalar remainingUnnamed
            simp only [execStmts, bind, head]
            refine ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, ?_, finalWorld, finalSource, finalFlow, finalSourceEq, finalInterpretationEq, finalPhaseEq, finalLimitEq, finalBounded, ?_, ?_, ?_, ?_⟩
            · intro oldRoot ty found
              exact finalExtended oldRoot ty (extended oldRoot ty found)
            · intro other outside
              have different : other ≠ root := outside scopeInst _
              have unchanged := finalProtected other (by simpa [nextFrame, advanceLocalFrame] using outside)
              simpa [nextTypes, registerRootType, different] using unchanged
            · simp only [nextFrame, advanceLocalFrame] at finalCounters
              cases tailExecution : execStmts fuel config frame.interpretation.environment rest middle with
              | ok result after =>
                simp only [tailExecution, Goose.Proofs.Exit.stepState] at finalCounters ⊢
                exact ⟨finalCounters.1.trans headCounters.1, finalCounters.2.trans headCounters.2⟩
              | stop reason after | escape _ _ after | jump _ _ after => simp only [tailExecution]
            · simp only [nextFrame, advanceLocalFrame] at finalObserved
              cases tailExecution : execStmts fuel config frame.interpretation.environment rest middle with
              | ok result after =>
                simp only [tailExecution] at finalObserved ⊢
                intro other outside
                have tailObserved := finalObserved other (by simpa [nextFrame, advanceLocalFrame] using outside)
                have first := headObserved other outside
                exact ⟨tailObserved.1.trans first.1, tailObserved.2.trans first.2⟩
              | stop reason after | escape _ _ after | jump _ _ after => simp only [tailExecution]
            · simp only [nextFrame, advanceLocalFrame] at finalReplay
              cases tailExecution : execStmts fuel config frame.interpretation.environment rest middle with
              | ok value after =>
                simp only [tailExecution] at finalReplay ⊢
                have replay := statementReplay_cons (checkFuel + 1) frame nextFrame finalFrame (.letS id expression origin) rest
                  headReplayTyped headReplayRooted rfl finalReplay.1 finalReplay.2
                simpa only [nesting] using replay
              | stop reason after | escape _ _ after | jump _ _ after => simp only [tailExecution] at finalReplay ⊢


theorem execStmts_mixedLocal_protectedTypes_world {statements : List Stmt} (form : MixedLocalStatements statements) :
    ∀ (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
      (frame : ConstructionSourceFrame) (context : Nat) (before : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
      (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation context →
      SourcePosition accepted frame (.statements statements) →
      frame.initialized = config.module.globals.size → frame.typing.globalLimit ≤ config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      (∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
        (frame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8))) →
      (∀ id expression origin, .letS id expression origin ∈ statements → AcceptedBinaryExpression expression →
        ∀ descriptor, frame.source.impl.vars[id]? = some descriptor →
          (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) →
      (∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
        (frame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none) →
      ∃ (next : ConstructionSourceFrame) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop)
        (nextRegions : List ReceivingRegion),
        let outcome := execStmts fuel config frame.interpretation.environment statements before
        let after := Goose.Proofs.Exit.stepState outcome
        next.initialized = frame.initialized ∧ RootTypesExtend types nextTypes ∧
        AcceptedWorld config next.initialized after ambient nextTypes nextLive nextRegions pending ∧
        AcceptedFrame config accepted next after nextTypes ∧
        (match outcome with | .ok flow _ => flow = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) ∧
        next.source = frame.source ∧ next.interpretation = frame.interpretation ∧ next.phase = frame.phase ∧
        next.typing.globalLimit = frame.typing.globalLimit ∧ GlobalEffectTargetsBounded next.rootCursor.eff config.module.globals.size ∧
        (∀ root, (∀ scope id, root ≠ Goose.Core.RootInst.local frame.interpretation.environment.act scope id) → nextTypes root = types root) ∧
        (match outcome with
        | .ok _ _ => typeStatements frame.typingFuel frame.typing statements frame.typingCounter = .ok (next.typing, next.typingCounter) ∧
            rpStmts frame.source statements frame.rootCursor = .ok ((), next.rootCursor)
        | _ => True) := by
  intro fuel config accepted frame context before ambient types live regions pending world source phase position initialized limit bounded owners scalarOwners unnamed
  obtain ⟨next, nextTypes, nextLive, nextRegions, initializedEq, extended, finalWorld, finalSource, flow,
    sourceEq, interpretationEq, phaseEq, limitEq, finalBounded, protectedTypes, counters, observations, replay⟩ :=
    execStmts_mixedLocal_observed_world form fuel config accepted frame context before ambient types live regions pending
      world source phase position initialized limit bounded owners scalarOwners unnamed
  exact ⟨next, nextTypes, nextLive, nextRegions, initializedEq, extended, finalWorld, finalSource, flow,
    sourceEq, interpretationEq, phaseEq, limitEq, finalBounded, protectedTypes, replay⟩

#print axioms execStmts_mixedLocal_protectedTypes_world
#print axioms execStmts_mixedLocal_observed_world
end Goose.Proofs.ConstructionAcceptedExecution
