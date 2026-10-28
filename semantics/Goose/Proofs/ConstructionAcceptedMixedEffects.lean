import Goose.Proofs.ConstructionAcceptedScalarModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

theorem rpStmt_byteOwner_effectTargets (env : PEnv) (id : Nat) (bytes : List UInt8)
    (origin bytesOrigin : Goose.Core.OriginId) (before after : RState) (descriptor : LocalVar)
    (declared : env.impl.vars[id]? = some descriptor) (ty : descriptor.ty = .varr (.int .u8))
    (checked : rpStmt env (.letS id (.bytes (.varr (.int .u8)) bytes bytesOrigin) origin) before = .ok ((), after)) :
    Eff.accessTargets after.eff = Eff.accessTargets before.eff := by
  have order := (rpStmt_letS_initializer checked).1
  subst id
  simp only [rpStmt, bind, StateT.bind] at checked
  have getState (state : RState) : (get : P RState) state = .ok (state, state) := rfl
  have modifyState (f : RState → RState) (state : RState) : (modify f : P Unit) state = .ok ((), f state) := rfl
  simp only [getState, Except.bind, ↓reduceIte] at checked
  simp only [StateT.bind, modifyState, rpExpr, pure, declared, ty, Ty.isRefLike] at checked
  simp only [StateT.pure, Bool.false_eq_true, ↓reduceIte] at checked
  simp only [bind, Except.bind, pure] at checked
  dsimp only [Except.pure] at checked
  simp only [noteReceivingCapacity_byte_result] at checked
  by_cases large : bytes.length > 2 ^ 32 - 1
  · simp only [large, ↓reduceIte, noteAborts, modifyState] at checked
    cases checked
    rfl
  · simp only [large, ↓reduceIte, pure, StateT.pure, Except.pure] at checked
    cases checked
    rfl

inductive MixedScalarByteStatements : List Stmt → Prop
  | nil : MixedScalarByteStatements []
  | scalar (expression : Expr) (origin : Goose.Core.OriginId) (rest : List Stmt)
      (form : AcceptedBinaryExpression expression) (tail : MixedScalarByteStatements rest) :
      MixedScalarByteStatements (.expr expression origin :: rest)
  | byte (declaration : ByteOwnerDeclaration) (rest : List Stmt) (tail : MixedScalarByteStatements rest) :
      MixedScalarByteStatements (declaration.statement :: rest)

private theorem mixedEffects_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem MixedScalarByteStatements.effects_bounded {statements : List Stmt} (form : MixedScalarByteStatements statements) :
    ∀ (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (count : Nat),
      SourcePosition accepted frame (.statements statements) → frame.typing.globalLimit ≤ count →
      GlobalEffectTargetsBounded frame.rootCursor.eff count →
      (∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
        (frame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8))) →
      ∀ final, rpStmts frame.source statements frame.rootCursor = .ok ((), final) →
        GlobalEffectTargetsBounded final.eff count := by
  induction form with
  | nil =>
    intro config accepted frame count position limit bounded owners final rooted
    change Except.ok ((), frame.rootCursor) = Except.ok ((), final) at rooted
    cases rooted
    exact bounded
  | scalar expression origin rest expressionForm tail ih =>
    intro config accepted frame count position limit bounded owners final rooted
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
        obtain ⟨result, operandTyped, remaining⟩ := mixedEffects_bind_success _ _ _ headTyped'
        obtain ⟨operandTypes, counter⟩ := result
        obtain ⟨result, required, returned⟩ := mixedEffects_bind_success _ _ _ remaining
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
          apply ih config accepted _ count nextPosition limit middleBounded
          · intro declaration member
            exact owners declaration (List.mem_cons_of_mem _ member)
          · exact tailRooted
  | byte declaration rest tail ih =>
    intro config accepted frame count position limit bounded owners final rooted
    obtain ⟨_, _, _, typedAll, _⟩ := position.checked accepted frame _
    obtain ⟨middle, headRooted, tailRooted⟩ := rpStmts_cons rooted
    have owner := owners declaration (by simp)
    cases declared : frame.source.impl.vars[declaration.id]? with
    | none => simp [declared] at owner
    | some descriptor =>
      have ty : descriptor.ty = .varr (.int .u8) := by simpa [declared] using owner
      have sameEffects := rpStmt_byteOwner_effectTargets frame.source declaration.id declaration.bytes declaration.origin
        declaration.bytesOrigin frame.rootCursor middle descriptor declared ty (by simpa [ByteOwnerDeclaration.statement] using headRooted)
      have middleBounded : GlobalEffectTargetsBounded middle.eff count := by
        unfold GlobalEffectTargetsBounded at bounded ⊢
        rw [sameEffects]
        exact bounded
      cases nesting : frame.typingFuel with
      | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
      | succ headFuel =>
        cases headFuel with
        | zero => rw [nesting] at typedAll; change Except.error _ = Except.ok _ at typedAll; cases typedAll
        | succ checkFuel =>
          have headPosition := position.statements_head accepted frame declaration.statement rest (checkFuel + 1) nesting
          obtain ⟨next, nextCounter, nextRoots, headTyped, headRooted'⟩ := headPosition.checked accepted _ _
          have sameRoots : nextRoots = middle := (Prod.mk.inj (Except.ok.inj (headRooted'.symm.trans headRooted))).2
          subst nextRoots
          have nextTyping := typeStatement_let_environment checkFuel frame.typing next declaration.id
            (.bytes (.varr (.int .u8)) declaration.bytes declaration.bytesOrigin) declaration.origin
            frame.typingCounter nextCounter (by simpa [ByteOwnerDeclaration.statement] using headTyped)
          subst next
          have nextPosition := position.statements_tail accepted frame declaration.statement rest (checkFuel + 1) _ nextCounter
            middle nesting headTyped headRooted
          apply ih config accepted _ count nextPosition limit middleBounded
          · intro item member
            exact owners item (List.mem_cons_of_mem _ member)
          · exact tailRooted

theorem MixedScalarByteStatements.effects_available {statements : List Stmt} (form : MixedScalarByteStatements statements)
    (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (types : RootTypes)
    (source : AcceptedFrame config accepted frame state types)
    (position : SourcePosition accepted frame (.statements statements))
    (initialized : frame.initialized = config.module.globals.size)
    (limit : frame.typing.globalLimit ≤ config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ statements →
      (frame.source.impl.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8))) :
    ∀ final, rpStmts frame.source statements frame.rootCursor = .ok ((), final) →
      GlobalEffectsAvailable frame.interpretation frame.initialized final.eff := by
  intro final rooted
  have effects := form.effects_bounded config accepted frame config.module.globals.size position limit bounded owners final rooted
  rw [initialized, ← source.compatible.globalCount]
  exact (globalEffectsAvailable_iff_bounded frame.interpretation final.eff).2 (by simpa only [source.compatible.globalCount] using effects)

#print axioms MixedScalarByteStatements.effects_available
#print axioms MixedScalarByteStatements.effects_bounded
#print axioms rpStmt_byteOwner_effectTargets
end Goose.Proofs.ConstructionAcceptedExecution
