import Goose.Proofs.ConstructionAcceptedScalarLocalOutcome
import Goose.Proofs.ConstructionAcceptedBlockTailChecks

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem checkedValue_scalarLocal_prefix (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (id : Nat) (expression : Expr) (origin : Goose.Core.OriginId) (form : AcceptedBinaryExpression expression)
    (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState)
    (source : AcceptedFrame config accepted frame state types)
    (typed : typeStatement (fuel + 1) frame.typing (.letS id expression origin) frame.typingCounter = .ok (next, typingAfter))
    (rooted : rpStmt frame.source (.letS id expression origin) frame.rootCursor = .ok ((), rootsAfter))
    (available : GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff)
    (scalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
    ∃ descriptor roots expressionTypingAfter expressionRootsAfter,
      frame.typing.variables[id]? = some descriptor ∧
      CheckedValue (letInitializerFrame frame id fuel) expression descriptor.ty roots expressionTypingAfter expressionRootsAfter ∧
      AcceptedFrame config accepted (letInitializerFrame frame id fuel) state types := by
  obtain ⟨descriptor, ty, expressionTypingAfter, declared, typingOrder, expressionTyped, passing, _⟩ :=
    typeStatement_scalarLocal_initializer fuel frame.typing next id expression origin frame.typingCounter typingAfter form typed
  obtain ⟨rootOrder, roots, middle, expressionRooted, _⟩ := rpStmt_letS_initializer rooted
  have initializer := source.letInitializer id fuel descriptor rootOrder typingOrder declared
  have sourceDeclared : frame.source.impl.vars[id]? = some descriptor := by
    rw [source.compatible.sourceVariables]; exact declared
  have same := rpStmt_scalarLocal_cursor frame.source id expression origin frame.rootCursor rootsAfter middle descriptor roots
    sourceDeclared (scalar descriptor declared) expressionRooted rooted
  have equal := scalar_passesTo_equal ty descriptor.ty (scalar descriptor declared) passing
  subst ty
  refine ⟨descriptor, roots, expressionTypingAfter, middle, declared, ⟨expressionTyped, expressionRooted, ?_⟩, initializer⟩
  change GlobalEffectsAvailable frame.interpretation frame.initialized middle.eff
  rw [← same]
  exact available

theorem execStmt_acceptedScalarLocal_prefix (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context id : Nat) (expression : Expr) (origin : Goose.Core.OriginId)
    (rest : List Stmt) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types) (_phase : frame.phase = .implementation context)
    (position : SourcePosition accepted frame (.statements (.letS id expression origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 2)
    (available : ∀ rootsAfter, rpStmt frame.source (.letS id expression origin) frame.rootCursor = .ok ((), rootsAfter) →
      GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff)
    (scalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
      (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
    match execStmt fuel config frame.interpretation.environment (.letS id expression origin) before with
    | .stop _ after => AcceptedWorld config frame.initialized after ambient types live regions pending ∧
        AcceptedFrame config accepted frame after types
    | .ok flow after => flow = .normal .unit ∧ ∃ (scopeInst : Nat) (descriptor : LocalVar) (rootsAfter : RState),
        let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
        let next := { advanceLocalFrame { frame with typingFuel := checkFuel + 1 } id with rootCursor := rootsAfter }
        RootTypesExtend types (registerRootType types root descriptor.ty) ∧
        AcceptedWorld config frame.initialized after ambient (registerRootType types root descriptor.ty)
          (fun other => other = root ∨ live other) regions pending ∧
        AcceptedFrame config accepted next after (registerRootType types root descriptor.ty) ∧
        SourcePosition accepted next (.statements rest) ∧
        typeStatement (checkFuel + 1) frame.typing (.letS id expression origin) frame.typingCounter =
          .ok (next.typing, next.typingCounter) ∧
        rpStmt frame.source (.letS id expression origin) frame.rootCursor = .ok ((), rootsAfter) ∧
        GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff
    | .escape .. | .jump .. => False := by
  have headPosition := position.statements_head accepted frame (.letS id expression origin) rest (checkFuel + 1) nesting
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := headPosition.checked accepted _ _
  obtain ⟨descriptor, roots, expressionTypingAfter, expressionRootsAfter, declared, checked, initializer⟩ :=
    checkedValue_scalarLocal_prefix checkFuel config accepted frame before types id expression origin form next typingAfter rootsAfter
      source typed rooted (available rootsAfter rooted) scalar
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
  have effects := available rootsAfter rooted
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
        have headTyped : typeStatement (checkFuel + 1) frame.typing (.letS id expression origin) frame.typingCounter =
            .ok (nextFrame.typing, nextFrame.typingCounter) := by
          simpa [nextFrame, advanceLocalFrame, nextTyping, nextCounter] using typed
        exact ⟨trivial, scopeInst, descriptor, rootsAfter, extended, afterWorld, nextSource, tailPosition, headTyped, rooted, effects⟩


def ScalarLocalReplay (frame next : ConstructionSourceFrame) (statements : List Stmt) : Prop :=
  typeStatements frame.typingFuel frame.typing statements frame.typingCounter = .ok (next.typing, next.typingCounter) ∧
  rpStmts frame.source statements frame.rootCursor = .ok ((), next.rootCursor) ∧ next.source = frame.source ∧
  next.interpretation = frame.interpretation

inductive ScalarLocalStatements : List Stmt → Prop
  | nil : ScalarLocalStatements []
  | cons (id : Nat) (expression : Expr) (origin : Nat) (rest : List Stmt)
      (form : AcceptedBinaryExpression expression) (tail : ScalarLocalStatements rest) :
      ScalarLocalStatements (.letS id expression origin :: rest)

theorem execStmts_scalarLocal_prefix {statements : List Stmt} (form : ScalarLocalStatements statements) :
    ∀ (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
      (frame : ConstructionSourceFrame) (context : Nat) (before : ExecutionState)
      (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
      (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation context →
      SourcePosition accepted frame (.statements statements) →
      (∀ rootsAfter, rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter) →
        GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff) →
      (∀ id expression origin, .letS id expression origin ∈ statements →
        ∀ descriptor, frame.source.impl.vars[id]? = some descriptor →
          (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) →
      ∃ (next : ConstructionSourceFrame) (nextTypes : RootTypes) (nextLive : Goose.Core.RootInst → Prop),
        let outcome := execStmts fuel config frame.interpretation.environment statements before
        let after := Goose.Proofs.Exit.stepState outcome
        next.initialized = frame.initialized ∧ RootTypesExtend types nextTypes ∧
        AcceptedWorld config next.initialized after ambient nextTypes nextLive regions pending ∧
        AcceptedFrame config accepted next after nextTypes ∧
        (match outcome with | .ok flow _ => flow = .normal .unit ∧ SourcePosition accepted next (.statements []) ∧ ScalarLocalReplay frame next statements | .stop _ _ => True | .escape .. | .jump .. => False) := by
  induction form with
  | nil =>
    intro fuel config accepted frame context before ambient types live regions pending world source phase position available scalar
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, rfl, (fun _ _ found => found), world, source, trivial⟩
    | succ fuel =>
      simp only [execStmts, pure, Goose.Proofs.Exit.stepState]
      obtain ⟨_, _, _, typed, _⟩ := position.checked accepted frame _
      cases depth : frame.typingFuel with
      | zero => rw [depth] at typed; change Except.error _ = Except.ok _ at typed; cases typed
      | succ n =>
        have replay : ScalarLocalReplay frame frame [] := by simp [ScalarLocalReplay, depth, typeStatements, rpStmts, pure, StateT.pure, Except.pure]
        exact ⟨frame, types, live, rfl, (fun _ _ found => found), world, source, trivial, position, replay⟩
  | cons id expression origin rest expressionForm tail ih =>
    intro fuel config accepted frame context before ambient types live regions pending world source phase position available scalar
    cases fuel with
    | zero =>
      simp only [execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
      exact ⟨frame, types, live, rfl, (fun _ _ found => found), world, source, trivial⟩
    | succ fuel =>
      obtain ⟨_, _, allRoots, typedAll, rootedAll⟩ := position.checked accepted frame _
      obtain ⟨middleRoots, headRooted, tailRooted⟩ := rpStmts_cons rootedAll
      have headAvailable : ∀ after, rpStmt frame.source (.letS id expression origin) frame.rootCursor = .ok ((), after) →
          GlobalEffectsAvailable frame.interpretation frame.initialized after.eff := by
        intro after rooted
        have equal : after = middleRoots := (Prod.mk.inj (Except.ok.inj (rooted.symm.trans headRooted))).2
        subst after
        have included := rpStmts_effectTargetsIncluded tailRooted
        intro target member global rooted
        exact available allRoots rootedAll target (included member) global rooted
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
        | succ checkFuel =>
          have localScalar : ∀ descriptor, frame.typing.variables[id]? = some descriptor →
              (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
            intro descriptor declared
            apply scalar id expression origin (by simp) descriptor
            rw [source.compatible.sourceVariables]; exact declared
          have headOutcome := execStmt_acceptedScalarLocal_prefix fuel checkFuel config accepted frame context id expression origin rest
            before ambient types live regions pending expressionForm world source phase position nesting headAvailable localScalar
          cases head : execStmt fuel config frame.interpretation.environment (.letS id expression origin) before with
          | stop reason after =>
            simp only [head] at headOutcome
            obtain ⟨finalWorld, finalSource⟩ := headOutcome
            simp only [execStmts, bind, head, Goose.Proofs.Exit.stepState]
            exact ⟨frame, types, live, rfl, (fun _ _ found => found), finalWorld, finalSource, trivial⟩
          | escape address carriers after | jump target kind after => simp only [head] at headOutcome
          | ok flow middle =>
            simp only [head] at headOutcome
            obtain ⟨normal, scopeInst, descriptor, rootsAfter, extended, middleWorld, middleSource, middlePosition, middleTyped, middleRooted, middleAvailable⟩ := headOutcome
            subst flow
            have sameRoots : rootsAfter = middleRoots :=
              (Prod.mk.inj (Except.ok.inj (middleRooted.symm.trans headRooted))).2
            let root := Goose.Core.RootInst.local frame.interpretation.environment.act scopeInst id
            let nextTypes := registerRootType types root descriptor.ty
            let nextFrame := { advanceLocalFrame { frame with typingFuel := checkFuel + 1 } id with rootCursor := rootsAfter }
            let nextLive := fun other => other = root ∨ live other
            have remainingAvailable : ∀ final, rpStmts nextFrame.source rest nextFrame.rootCursor = .ok ((), final) →
                GlobalEffectsAvailable nextFrame.interpretation nextFrame.initialized final.eff := by
              intro final checked
              have equal : final = allRoots := by
                have checked' : rpStmts frame.source rest middleRoots = .ok ((), final) := by
                  simpa [nextFrame, advanceLocalFrame, sameRoots] using checked
                exact (Prod.mk.inj (Except.ok.inj (checked'.symm.trans tailRooted))).2
              subst final
              simpa [nextFrame, advanceLocalFrame] using available allRoots rootedAll
            have remainingScalar : ∀ id expression origin, .letS id expression origin ∈ rest →
                ∀ descriptor, nextFrame.source.impl.vars[id]? = some descriptor →
                  (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool := by
              intro id expression origin member descriptor found
              exact scalar id expression origin (List.mem_cons_of_mem _ member) descriptor found
            obtain ⟨finalFrame, finalTypes, finalLive, initializedEq, finalExtended, finalWorld, finalSource, finalFlow⟩ :=
              ih fuel config accepted nextFrame context middle ambient nextTypes nextLive regions pending middleWorld middleSource
                (by simpa [nextFrame, advanceLocalFrame] using phase) middlePosition remainingAvailable remainingScalar
            simp only [execStmts, bind, head] at finalFlow finalWorld finalSource ⊢
            cases tailRun : execStmts fuel config nextFrame.interpretation.environment rest middle with
            | stop reason after =>
              have tailRun' : execStmts fuel config frame.interpretation.environment rest middle = .stop reason after := by
                simpa [nextFrame, advanceLocalFrame] using tailRun
              simp only [tailRun, tailRun'] at finalFlow finalWorld finalSource ⊢
              exact ⟨finalFrame, finalTypes, finalLive, initializedEq,
                (fun oldRoot ty found => finalExtended oldRoot ty (extended oldRoot ty found)), finalWorld, finalSource, trivial⟩
            | escape address carriers after | jump target kind after => simp [tailRun] at finalFlow
            | ok result after =>
              have tailRun' : execStmts fuel config frame.interpretation.environment rest middle = .ok result after := by
                simpa [nextFrame, advanceLocalFrame] using tailRun
              simp only [tailRun, tailRun'] at finalFlow finalWorld finalSource ⊢
              obtain ⟨normal, finalPosition, replay⟩ := finalFlow
              refine ⟨finalFrame, finalTypes, finalLive, initializedEq,
                (fun oldRoot ty found => finalExtended oldRoot ty (extended oldRoot ty found)), finalWorld, finalSource,
                normal, finalPosition, ?_⟩
              obtain ⟨typedRest, rootedRest, sourceSame, interpretationSame⟩ := replay
              refine ⟨?_, ?_, ?_, ?_⟩
              · rw [nesting]
                simp only [typeStatements, bind, StateT.bind, middleTyped, Except.bind]
                simpa [nextFrame, advanceLocalFrame] using typedRest
              · simp only [rpStmts, bind, StateT.bind, middleRooted, Except.bind]
                simpa [nextFrame, advanceLocalFrame] using rootedRest
              · simpa [nextFrame, advanceLocalFrame] using sourceSame
              · simpa [nextFrame, advanceLocalFrame] using interpretationSame

theorem ScalarLocalReplay.blockTail_checked {config : EvalConfig} (accepted : AcceptedModule config)
    (blockFrame child final : ConstructionSourceFrame) (scope fuel : Nat) (statements : List Stmt) (expression : Expr)
    (position : SourcePosition accepted blockFrame (.block ⟨scope, statements, some expression⟩))
    (nesting : blockFrame.typingFuel = fuel + 1)
    (childTyping : child.typing = { blockFrame.typing with scope := scope })
    (childFuel : child.typingFuel = fuel) (childCounter : child.typingCounter = blockFrame.typingCounter)
    (childSource : child.source = { blockFrame.source with scopes := scope :: blockFrame.source.scopes })
    (childCursor : child.rootCursor = blockFrame.rootCursor)
    (replay : ScalarLocalReplay child final statements) (form : AcceptedBinaryExpression expression)
    (available : ∀ roots rootsAfter,
      rpExpr final.source expression final.rootCursor = .ok (roots, rootsAfter) →
      GlobalEffectsAvailable final.interpretation final.initialized rootsAfter.eff) :
    ∃ ty roots typingAfter rootsAfter,
      CheckedValue { final with typingFuel := fuel } expression ty roots typingAfter rootsAfter := by
  obtain ⟨next, typingMiddle, rootMiddle, types, typingAfter, roots, rootsAfter,
    _, typedStatements, rootedStatements, typedTail, rootedTail⟩ :=
    position.blockTail_checks accepted blockFrame scope fuel statements expression nesting
  obtain ⟨typedReplay, rootedReplay, sourceSame, interpretationSame⟩ := replay
  rw [childTyping, childFuel, childCounter] at typedReplay
  have sameTyping : (final.typing, final.typingCounter) = (next, typingMiddle) :=
    Except.ok.inj (typedReplay.symm.trans typedStatements)
  obtain ⟨sameEnvironment, sameCounter⟩ := Prod.mk.inj sameTyping
  rw [childSource, childCursor] at rootedReplay
  have sameRoots : final.rootCursor = rootMiddle :=
    (Prod.mk.inj (Except.ok.inj (rootedReplay.symm.trans rootedStatements))).2
  have finalRooted : rpExpr final.source expression final.rootCursor = .ok (roots, rootsAfter) := by
    rw [sourceSame, childSource, sameRoots]
    exact rootedTail
  obtain ⟨ty, singleton⟩ := typeExpr_scalar_singleton form fuel next typingMiddle typingAfter types typedTail
  subst types
  refine ⟨ty, roots, typingAfter, rootsAfter, ?_, finalRooted, available roots rootsAfter finalRooted⟩
  simpa [sameEnvironment, sameCounter] using typedTail

#print axioms ScalarLocalReplay.blockTail_checked
#print axioms execStmts_scalarLocal_prefix
#print axioms execStmt_acceptedScalarLocal_prefix
#print axioms checkedValue_scalarLocal_prefix
end Goose.Proofs.ConstructionAcceptedExecution
