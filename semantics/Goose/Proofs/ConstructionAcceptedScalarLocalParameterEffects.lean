import Goose.Proofs.ConstructionAcceptedScalarLocalPrefix
import Goose.Proofs.ConstructionAcceptedScalarParameterEffects
import Goose.Proofs.ConstructionAcceptedRecursiveArgumentCallEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem rpStmt_letS_descriptor {env : PEnv} {id : Nat} {expression : Expr} {origin : Nat} {before after : RState}
    (checked : rpStmt env (.letS id expression origin) before = .ok ((), after)) :
    ∃ descriptor, env.impl.vars[id]? = some descriptor := by
  obtain ⟨order, roots, middle, operand, calls⟩ := rpStmt_letS_initializer checked
  cases declared : env.impl.vars[id]? with
  | some descriptor => exact ⟨descriptor, rfl⟩
  | none =>
    subst id
    simp only [rpStmt, bind, StateT.bind] at checked
    have getState (state : RState) : (get : P RState) state = .ok (state, state) := rfl
    have modifyState (f : RState → RState) (state : RState) : (modify f : P Unit) state = .ok ((), f state) := rfl
    simp only [getState, Except.bind, ↓reduceIte] at checked
    simp only [StateT.bind, modifyState, declared] at checked
    change (rpExpr { env with initializing := before.nextVar :: env.initializing } expression
      { before with nextVar := before.nextVar + 1 }).bind (fun _ => Except.error _) = Except.ok ((), after) at checked
    simp only [operand, Except.bind] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked

theorem scalarLocalStatements_noParameter {statements : List Stmt} (form : ScalarLocalStatements statements) :
    ∀ (source : PEnv) (before after : RState),
      (∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
        source.impl.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) →
      NoParameterAccess before.eff → rpStmts source statements before = .ok ((), after) → NoParameterAccess after.eff := by
  induction form with
  | nil =>
    intro source before after scalar clear rooted
    change Except.ok ((), before) = Except.ok ((), after) at rooted
    cases rooted
    exact clear
  | cons id expression origin rest expressionForm tailForm ih =>
    intro source before after scalar clear rooted
    obtain ⟨middle, head, tail⟩ := rpStmts_cons rooted
    obtain ⟨descriptor, declared⟩ := rpStmt_letS_descriptor head
    have descriptorScalar := scalar id expression origin (by simp) descriptor declared
    obtain ⟨order, roots, operandAfter, operand, calls⟩ := rpStmt_letS_initializer head
    have operandClear := recursiveScalar_noParameter expressionForm { source with initializing := id :: source.initializing }
      { before with nextVar := before.nextVar + 1 } operandAfter roots clear operand
    have same := rpStmt_scalarLocal_cursor source id expression origin before middle operandAfter descriptor roots declared descriptorScalar operand head
    subst middle
    apply ih source operandAfter after ?_ operandClear tail
    intro nextId nextExpression nextOrigin member nextDescriptor nextDeclared
    exact scalar nextId nextExpression nextOrigin (by simp [member]) nextDescriptor nextDeclared

theorem scalarLocalRecursiveTail_noParameter (config : EvalConfig) (integer : Goose.Core.IntTy) (implementation : Impl)
    (source : PEnv) (scope target origin : Nat) (statements : List Stmt) (argument : Expr)
    (context : Context) (callee : Impl) (parameter : Param) (summary : Summary)
    (before after : RState) (result : List RootRef × (Nat × Nat))
    (statementsForm : ScalarLocalStatements statements) (argumentForm : RecursiveArgumentExpression config integer implementation argument)
    (moduleEq : source.mod = config.module) (implementationEq : source.impl = implementation)
    (contextAt : source.mod.contexts[target]? = some context) (calleeAt : source.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (known : callee.summary = .known summary)
    (scalar : ∀ id expression origin, .letS id expression origin ∈ statements → ∀ descriptor,
      implementation.vars[id]? = some descriptor → (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (clear : NoParameterAccess before.eff)
    (rooted : rpBlockValue source [] ⟨scope, statements, some (.call target [.byVal argument] origin)⟩ before = .ok (result, after)) :
    NoParameterAccess after.eff := by
  obtain ⟨_, middle, roots, statementsRooted, tailRooted, resultEq⟩ := rpBlockValue_body rooted
  have statementsClear := scalarLocalStatements_noParameter statementsForm { source with scopes := scope :: source.scopes }
    { before with nextVar := before.nextVar + [].length } middle (by
      intro id expression origin member descriptor declared
      exact scalar id expression origin member descriptor (by simpa [implementationEq] using declared)) clear statementsRooted
  exact recursiveArgumentCall_noParameter (env := { source with scopes := scope :: source.scopes }) summary argumentForm moduleEq implementationEq
    contextAt calleeAt parameters known statementsClear (by simpa using tailRooted)

#print axioms scalarLocalRecursiveTail_noParameter
#print axioms scalarLocalStatements_noParameter
#print axioms rpStmt_letS_descriptor
end Goose.Proofs.ConstructionAcceptedExecution
