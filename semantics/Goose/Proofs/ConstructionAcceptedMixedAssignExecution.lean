import Goose.Proofs.ConstructionAcceptedScalarAssignCursor

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

inductive MixedAssignStatements : List Stmt → Prop
  | nil : MixedAssignStatements []
  | scalar (expression : Expr) (origin : Goose.Core.OriginId) (rest : List Stmt)
      (form : AcceptedBinaryExpression expression) (tail : MixedAssignStatements rest) :
      MixedAssignStatements (.expr expression origin :: rest)
  | byte (declaration : ByteOwnerDeclaration) (rest : List Stmt) (tail : MixedAssignStatements rest) :
      MixedAssignStatements (declaration.statement :: rest)
  | scalarLocal (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (rest : List Stmt)
      (form : AcceptedBinaryExpression expression) (tail : MixedAssignStatements rest) :
      MixedAssignStatements (.letS id expression origin :: rest)
  | assign (place : Place) (expression : Expr) (origin : Goose.Core.OriginId) (rest : List Stmt)
      (form : AcceptedBinaryExpression expression)
      (direct : (∃ id, place = .var id) ∨ ∃ id, place = .global id) (tail : MixedAssignStatements rest) :
      MixedAssignStatements (.assign place expression origin :: rest)

private theorem mixedAssign_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem execStmts_mixedAssign_accepted_world {statements : List Stmt} (form : MixedAssignStatements statements) :
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
      (∀ id expression origin, .assign (.var id) expression origin ∈ statements →
        ∀ descriptor, frame.source.impl.vars[id]? = some descriptor →
          (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) →
      (∀ id expression origin, .assign (.global id) expression origin ∈ statements →
        ∀ descriptor, config.module.globals[id]? = some descriptor →
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
        (match outcome with | .ok flow _ => flow = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) := by
  induction form with
  | nil =>
    intro fuel config accepted frame context before ambient types live regions pending world source phase position initialized limit bounded owners scalarOwners localTargets globalTargets unnamed
    cases fuel <;> simp only [execStmts, timeout, EvalM.stop, pure, Goose.Proofs.Exit.stepState]
    all_goals exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial⟩
  | byte declaration rest tail ih =>
    intro fuel config accepted frame context before ambient types live regions pending world source phase position initialized limit bounded owners scalarOwners localTargets globalTargets unnamed
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial⟩
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
            exact ⟨frame, types, live, nextRegions, rfl, (fun _ _ found => found), finalWorld, finalSource, trivial⟩
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
            obtain ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, finalExtended, finalWorld, finalSource, finalFlow⟩ :=
              ih fuel config accepted nextFrame context middle ambient nextTypes nextLive nextRegions pending middleWorld middleSource
                (by simpa [nextFrame, advanceLocalFrame] using phase) middlePosition initialized limit bounded remainingOwners (by intro id expression origin member shape descriptor found; exact scalarOwners id expression origin (List.mem_cons_of_mem _ member) shape descriptor found) (by intro id expression origin member descriptor found; exact localTargets id expression origin (List.mem_cons_of_mem _ member) descriptor found) (by intro id expression origin member descriptor found; exact globalTargets id expression origin (List.mem_cons_of_mem _ member) descriptor found) remainingUnnamed
            simp only [execStmts, bind, head]
            refine ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, ?_, finalWorld, finalSource, finalFlow⟩
            intro oldRoot ty found
            exact finalExtended oldRoot ty (extended oldRoot ty found)
  | scalar expression origin rest expressionForm tail ih =>
    intro fuel config accepted frame context before ambient types live regions pending world source phase position initialized limit bounded owners scalarOwners localTargets globalTargets unnamed
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial⟩
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
          obtain ⟨result, expressionTyped, remaining⟩ := mixedAssign_bind_success _ _ _ headTyped'
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
            exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial⟩
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
            obtain ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, finalExtended, finalWorld, finalSource, finalFlow⟩ :=
              ih fuel config accepted nextFrame context before ambient types live regions pending world nextSource phase nextPosition
                initialized limit middleBounded remainingOwners (by intro id expression origin member shape descriptor found; exact scalarOwners id expression origin (List.mem_cons_of_mem _ member) shape descriptor found) (by intro id expression origin member descriptor found; exact localTargets id expression origin (List.mem_cons_of_mem _ member) descriptor found) (by intro id expression origin member descriptor found; exact globalTargets id expression origin (List.mem_cons_of_mem _ member) descriptor found) remainingUnnamed
            simp only [execStmts, bind, head]
            exact ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, finalExtended, finalWorld, finalSource, finalFlow⟩

  | scalarLocal id expression origin rest expressionForm tail ih =>
    intro fuel config accepted frame context before ambient types live regions pending world source phase position initialized limit bounded owners scalarOwners localTargets globalTargets unnamed
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial⟩
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
          have headOutcome := execStmt_acceptedScalarLocal_outcome fuel checkFuel config accepted frame context id expression origin rest
            before ambient types live regions pending expressionForm world source phase position nesting initialized bounded localScalar
          cases head : execStmt fuel config frame.interpretation.environment (.letS id expression origin) before with
          | stop reason after =>
            simp only [head] at headOutcome
            obtain ⟨finalWorld, finalSource⟩ := headOutcome
            simp only [execStmts, bind, head, Goose.Proofs.Exit.stepState]
            exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), finalWorld, finalSource, trivial⟩
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
            obtain ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, finalExtended, finalWorld, finalSource, finalFlow⟩ :=
              ih fuel config accepted nextFrame context middle ambient nextTypes nextLive regions pending middleWorld middleSource
                (by simpa [nextFrame, advanceLocalFrame] using phase) middlePosition initialized limit middleBounded
                  remainingOwners remainingScalar (by intro id expression origin member descriptor found; exact localTargets id expression origin (List.mem_cons_of_mem _ member) descriptor found) (by intro id expression origin member descriptor found; exact globalTargets id expression origin (List.mem_cons_of_mem _ member) descriptor found) remainingUnnamed
            simp only [execStmts, bind, head]
            refine ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, ?_, finalWorld, finalSource, finalFlow⟩
            intro oldRoot ty found
            exact finalExtended oldRoot ty (extended oldRoot ty found)

  | assign place expression origin rest expressionForm direct tail ih =>
    intro fuel config accepted frame context before ambient types live regions pending world source phase position initialized limit bounded owners scalarOwners localTargets globalTargets unnamed
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, regions, rfl, (fun _ _ found => found), world, source, trivial⟩
    | succ fuel =>
      obtain ⟨_, _, _, typedAll, _⟩ := position.checked accepted frame _
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
        | succ checkFuel =>
          obtain ⟨rootsAfter, sameRoot, nextBounded, nextPosition⟩ := position.scalarAssign_tail accepted frame before types
            place expression origin rest checkFuel expressionForm source initialized bounded nesting direct
          have headPosition := position.statements_head accepted frame (.assign place expression origin) rest (checkFuel + 1) nesting
          let headFrame := { frame with typingFuel := checkFuel + 1 }
          have headSource : AcceptedFrame config accepted headFrame before types := source.withTypingFuel (checkFuel + 1)
          have headResult : ∃ nextLive,
              let outcome := execStmt fuel config frame.interpretation.environment (.assign place expression origin) before
              AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types nextLive regions pending ∧
              AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types ∧
              (match outcome with | .ok flow _ => flow = .normal .unit | .stop .. => True | .escape .. | .jump .. => False) := by
            rcases direct with ⟨id, same⟩ | ⟨id, same⟩
            · subst place
              have scalar : ∀ descriptor, headFrame.typing.variables[id]? = some descriptor →
                  (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
                intro descriptor declared
                apply localTargets id expression origin (by simp) descriptor
                rw [source.compatible.sourceVariables]; exact declared
              obtain ⟨nextLive, nextWorld, nextSource, flow⟩ := execStmt_sourceScalarAssignLocal fuel checkFuel config accepted headFrame before
                ambient types live regions pending id expression origin expressionForm world headSource initialized headPosition rfl scalar
              exact ⟨nextLive, nextWorld, by simpa [headFrame] using nextSource.withTypingFuel frame.typingFuel, flow⟩
            · subst place
              have scalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
                  (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
                intro descriptor declared; exact globalTargets id expression origin (by simp) descriptor declared
              obtain ⟨nextWorld, nextSource, flow⟩ := execStmt_sourceScalarAssignGlobal fuel checkFuel config accepted headFrame before
                ambient types live regions pending id expression origin expressionForm world headSource initialized headPosition rfl scalar
              exact ⟨live, nextWorld, by simpa [headFrame] using nextSource.withTypingFuel frame.typingFuel, flow⟩
          obtain ⟨nextLive, nextWorld, nextSource, headFlow⟩ := headResult
          cases head : execStmt fuel config frame.interpretation.environment (.assign place expression origin) before with
          | stop reason after =>
            simp only [head, Goose.Proofs.Exit.stepState] at nextWorld nextSource headFlow
            simp only [execStmts, bind, head, Goose.Proofs.Exit.stepState]
            exact ⟨frame, types, nextLive, regions, rfl, (fun _ _ found => found), nextWorld, nextSource, trivial⟩
          | escape address carriers after | jump target kind after => simp only [head] at headFlow
          | ok flow middle =>
            simp only [head, Goose.Proofs.Exit.stepState] at nextWorld nextSource headFlow
            subst flow
            let nextFrame := { frame with typingFuel := checkFuel + 1, rootCursor := rootsAfter }
            have afterSource : AcceptedFrame config accepted nextFrame middle types := by
              exact (nextSource.withTypingFuel (checkFuel + 1)).withRootCursor rootsAfter sameRoot
            have remainingOwners : ∀ item : ByteOwnerDeclaration, item.statement ∈ rest →
                (nextFrame.source.impl.vars[item.id]?).map (·.ty) = some (.varr (.int .u8)) := by
              intro item member; exact owners item (List.mem_cons_of_mem _ member)
            have remainingScalar : ∀ id expression origin, .letS id expression origin ∈ rest → AcceptedBinaryExpression expression →
                ∀ descriptor, nextFrame.source.impl.vars[id]? = some descriptor →
                  (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
              intro id expression origin member shape descriptor found
              exact scalarOwners id expression origin (List.mem_cons_of_mem _ member) shape descriptor found
            have remainingLocal : ∀ id expression origin, .assign (.var id) expression origin ∈ rest →
                ∀ descriptor, nextFrame.source.impl.vars[id]? = some descriptor →
                  (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
              intro id expression origin member descriptor found
              exact localTargets id expression origin (List.mem_cons_of_mem _ member) descriptor found
            have remainingGlobal : ∀ id expression origin, .assign (.global id) expression origin ∈ rest →
                ∀ descriptor, config.module.globals[id]? = some descriptor →
                  (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
              intro id expression origin member descriptor found
              exact globalTargets id expression origin (List.mem_cons_of_mem _ member) descriptor found
            have remainingUnnamed : ∀ item : ByteOwnerDeclaration, item.statement ∈ rest →
                (nextFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some item.id)) = none := by
              intro item member; exact unnamed item (List.mem_cons_of_mem _ member)
            obtain ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, finalExtended, finalWorld, finalSource, finalFlow⟩ :=
              ih fuel config accepted nextFrame context middle ambient types nextLive regions pending nextWorld afterSource
                phase nextPosition initialized limit nextBounded remainingOwners remainingScalar remainingLocal remainingGlobal remainingUnnamed
            simp only [execStmts, bind, head]
            exact ⟨finalFrame, finalTypes, finalLive, finalRegions, initializedEq, finalExtended, finalWorld, finalSource, finalFlow⟩

#print axioms execStmts_mixedAssign_accepted_world
end Goose.Proofs.ConstructionAcceptedExecution
