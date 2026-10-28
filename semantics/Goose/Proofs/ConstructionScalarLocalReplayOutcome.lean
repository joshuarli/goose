import Goose.Proofs.ConstructionAcceptedScalarLocalAdvance

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem execStmt_acceptedScalarLocal_replayOutcome (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id : Nat) (expression : Expr) (origin : Goose.Core.OriginId)
    (rest : List Stmt) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (_phase : frame.phase = .implementation context)
    (position : SourcePosition accepted frame (.statements (.letS id expression origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 2)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (scalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
    match execStmt fuel config frame.interpretation.environment (.letS id expression origin) before with
    | .stop _ after => AcceptedWorld config frame.initialized after ambient types live regions pending ∧
        AcceptedFrame config accepted frame after types
    | .ok flow after => flow = .normal .unit ∧ ∃ (scopeInst : Nat) (descriptor : LocalVar) (rootsAfter : RState),
        let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
        let next := { advanceLocalFrame { frame with typingFuel := checkFuel + 1 } id with rootCursor := rootsAfter }
        typeStatement (checkFuel + 1) frame.typing (.letS id expression origin) frame.typingCounter =
          .ok (next.typing, next.typingCounter) ∧
        rpStmt frame.source (.letS id expression origin) frame.rootCursor = .ok ((), next.rootCursor) ∧
        RootTypesExtend types (registerRootType types root descriptor.ty) ∧
        AcceptedWorld config frame.initialized after ambient (registerRootType types root descriptor.ty)
          (fun other => other = root ∨ live other) regions pending ∧
        AcceptedFrame config accepted next after (registerRootType types root descriptor.ty) ∧
        SourcePosition accepted next (.statements rest) ∧
        GlobalEffectTargetsBounded rootsAfter.eff config.module.globals.size
    | .escape .. | .jump .. => False := by
  have headPosition := position.statements_head accepted frame (.letS id expression origin) rest (checkFuel + 1) nesting
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := headPosition.checked accepted _ _
  obtain ⟨descriptor, roots, expressionTypingAfter, expressionRootsAfter, declared, checked, initializer⟩ :=
    checkedValue_typedScalarLocal_initializer checkFuel config accepted frame before types id expression origin form next typingAfter rootsAfter
      source initialized bounded typed rooted scalar
  obtain ⟨descriptor', ty, expressionTypingAfter', declared', typingOrder, expressionTyped, passing, counter⟩ :=
    typeStatement_scalarLocal_initializer checkFuel frame.typing next id expression origin frame.typingCounter typingAfter form typed
  have sameDescriptor : descriptor' = descriptor := Option.some.inj (declared'.symm.trans declared)
  subst descriptor'
  have sameType := scalar_passesTo_equal ty descriptor.ty (scalar descriptor declared) passing
  subst ty
  have sameTypingAfter : expressionTypingAfter' = expressionTypingAfter :=
    (Prod.mk.inj (Except.ok.inj (expressionTyped.symm.trans checked.typing))).2
  subst expressionTypingAfter'
  have rootOrder := (rpStmt_letS_initializer rooted).1
  have nextTyping := typeStatement_let_environment checkFuel frame.typing next id expression origin frame.typingCounter typingAfter typed
  have cursor := checked_binary_recursive_cursor form (letInitializerFrame frame id checkFuel) descriptor.ty roots
    expressionTypingAfter expressionRootsAfter checked
  have nextCounter : typingAfter = frame.typingCounter + 1 := by simpa [letInitializerFrame] using sameTypingAfter.trans cursor.1
  have sourceDeclared : frame.source.impl.vars[id]? = some descriptor := by rw [source.compatible.sourceVariables]; exact declared
  have rootAfter : rootsAfter = expressionRootsAfter := rpStmt_scalarLocal_cursor frame.source id expression origin
    frame.rootCursor rootsAfter expressionRootsAfter descriptor roots sourceDeclared (scalar descriptor declared) checked.provenance rooted
  have nextCursor : rootsAfter.nextVar = frame.rootCursor.nextVar + 1 := by
    rw [rootAfter]; simpa [letInitializerFrame] using cursor.2
  have effects : GlobalEffectTargetsBounded rootsAfter.eff config.module.globals.size := by
    rw [rootAfter]
    exact recursiveScalar_effects_bounded form checkFuel (letInitializerFrame frame id checkFuel).typing
      (letInitializerFrame frame id checkFuel).source config.module.globals.size (frame.typingCounter + 1) expressionTypingAfter
      (letInitializerFrame frame id checkFuel).rootCursor expressionRootsAfter [descriptor.ty] roots source.compatible.globals
      bounded checked.typing checked.provenance
  have nextPosition := position.statements_tail accepted frame (.letS id expression origin) rest (checkFuel + 1) next typingAfter
    rootsAfter nesting typed rooted
  have fixed : descriptor.ty.nonfixed = false := by
    rcases scalar descriptor declared with ⟨ty, same⟩ | same <;> simp [same, Ty.nonfixed]
  have runtimeDeclared : frame.interpretation.environment.vars[id]? = some descriptor := by
    rw [source.compatible.variables]; exact declared
  cases scopes : frame.interpretation.environment.scopes with
  | nil =>
    cases fuel with
    | zero => simp [execStmt, timeout, EvalM.stop, world, source]
    | succ fuel => simp [execStmt, runtimeDeclared, rootOf, scopes, fault, EvalM.stop, bind, world, source]
  | cons scopeEntry outer =>
    obtain ⟨scope, scopeInst⟩ := scopeEntry
    obtain ⟨otherDescriptor, root, otherDeclared, runtimeOther, typedOrder, rootedOrder, resolved, absent, fresh, freshType⟩ :=
      scalarLocal_sourceRoot checkFuel config accepted frame before types id expression origin rest source position nesting scope scopeInst outer scopes
    have descriptorSame : otherDescriptor = descriptor := Option.some.inj (otherDeclared.symm.trans declared)
    subst otherDescriptor
    obtain ⟨scopeDescriptor, scopeDeclared, localScope, order⟩ :=
      typeStatement_let_descriptor checkFuel frame.typing next id expression origin frame.typingCounter typingAfter typed
    have sameScopeDescriptor : scopeDescriptor = descriptor := Option.some.inj (scopeDeclared.symm.trans declared)
    subst scopeDescriptor
    have sourceScopes : frame.source.scopes = scope :: outer.map Prod.fst := by
      rw [source.compatible.scopes, scopes]; rfl
    have localScope' := localScope.trans (source.compatible.currentScope scope (outer.map Prod.fst) sourceScopes)
    have resolved' : rootOf frame.interpretation.environment id before =
        .ok (.local frame.interpretation.environment.act scopeInst id) before := by
      simp [rootOf, runtimeDeclared, scopes, localScope', pure]
    have localRoot : root = .local frame.interpretation.environment.act scopeInst id :=
      (ExecutionStep.ok.inj (resolved.symm.trans resolved')).1
    subst root
    cases fuel with
    | zero => simp [execStmt, timeout, EvalM.stop, world, source]
    | succ fuel =>
      have evaluated := evalValue_checked_binary_recursive form fuel config accepted (letInitializerFrame frame id checkFuel) before
        ambient types live regions pending world initializer descriptor.ty roots expressionTypingAfter expressionRootsAfter checked
      change Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment expression before) = before ∧ _ at evaluated
      have action := execStmt_scalarLocal_afterRoot fuel config frame.interpretation.environment id descriptor expression origin before
        (.local frame.interpretation.environment.act scopeInst id) runtimeDeclared fixed resolved
      rw [action]
      cases execution : evalValue fuel config frame.interpretation.environment expression before with
      | stop reason after =>
        simp only [execution, Goose.Proofs.Exit.stepState] at evaluated
        have same : after = before := evaluated.1
        subst after
        simp [bind, execution, world, source]
      | escape address carriers after =>
        exact ((evalValue_scalar_controlFree form fuel config frame.interpretation.environment).1 before address carriers after execution).elim
      | jump target kind after =>
        exact ((evalValue_scalar_controlFree form fuel config frame.interpretation.environment).2 before target kind after execution).elim
      | ok value after =>
        simp only [execution, Goose.Proofs.Exit.stepState] at evaluated
        have same : after = before := evaluated.1
        subst after
        have valid := evaluated.2.1 value before execution
        have scalarValue : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean := by
          rcases scalar descriptor declared with ⟨intTy, same⟩ | same
          · rw [same] at valid
            cases valid.represented with
            | integer intTy number => exact Or.inl ⟨intTy, number, rfl⟩
            | stored ty stored nonfixed logical => simp [Ty.nonfixed] at nonfixed
          · rw [same] at valid
            cases valid.represented with
            | boolean boolean => exact Or.inr ⟨boolean, rfl⟩
            | stored ty stored nonfixed logical => simp [Ty.nonfixed] at nonfixed
        have conform : LayoutConforms config.layout descriptor.ty := by
          rcases scalar descriptor declared with ⟨intTy, same⟩ | same <;> simp [same, LayoutConforms]
        have compatible : RootTypeCompatible types (.local frame.interpretation.environment.act scopeInst id) descriptor.ty := by
          intro prior present; rw [freshType] at present; cases present
        have uninitialized : frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing := Or.inl (by rw [rootOrder]; exact Nat.le_refl _)
        obtain ⟨_, frontier, synthetic⟩ := source.uninitializedLocal_fresh id _ uninitialized resolved
        obtain ⟨after, bound, extended, afterWorld⟩ := bindRoot_freshScalar_world config frame.initialized before ambient types live
          (.local frame.interpretation.environment.act scopeInst id) descriptor.ty value regions pending world scalarValue fresh
          compatible conform valid.represented valid.pointers frontier synthetic
        have afterSource := source.bindFreshScalar_advance world id descriptor _ value scalarValue rootOrder typingOrder declared valid.represented resolved bound
        let nextFrame := { advanceLocalFrame { frame with typingFuel := checkFuel + 1 } id with rootCursor := rootsAfter }
        have nextSource : AcceptedFrame config accepted nextFrame after (registerRootType types (.local frame.interpretation.environment.act scopeInst id) descriptor.ty) := by
          apply AcceptedFrame.withRootCursor (afterSource.withTypingFuel (checkFuel + 1))
          simpa [advanceLocalFrame] using nextCursor
        have tailPosition : SourcePosition accepted nextFrame (.statements rest) := by
          simpa [nextFrame, advanceLocalFrame, nextTyping, nextCounter] using nextPosition
        simp only [bind, execution, bound, pure]
        have replayTyped : typeStatement (checkFuel + 1) frame.typing (.letS id expression origin) frame.typingCounter =
            .ok (nextFrame.typing, nextFrame.typingCounter) := by
          simpa [nextFrame, advanceLocalFrame, nextTyping, nextCounter] using typed
        have replayRooted : rpStmt frame.source (.letS id expression origin) frame.rootCursor =
            .ok ((), nextFrame.rootCursor) := by simpa [nextFrame] using rooted
        exact ⟨trivial, scopeInst, descriptor, rootsAfter, replayTyped, replayRooted, extended, afterWorld, nextSource, tailPosition, effects⟩

#print axioms execStmt_acceptedScalarLocal_replayOutcome
end Goose.Proofs.ConstructionAcceptedExecution
