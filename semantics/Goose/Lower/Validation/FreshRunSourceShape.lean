import Goose.Lower.Validation.FreshRunFuture
import Goose.Lower.Validation.ExpressionTypingAggregateOps
import Goose.Lower.Validation.SourceStatementTypingBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

mutual
inductive OwnerFreshExpr : Expr → Prop
  | literal (ty : Ty) (values : List Expr) (owner : isLiteralRunType ty = true) :
      OwnerFreshExpr (.arrLit ty values)
  | conditional (condition : Expr) {yes no : Core.Block}
      (yesFresh : OwnerFreshBlock yes) (noFresh : OwnerFreshBlock no) :
      OwnerFreshExpr (.ifE condition yes no)
  | block {body : Core.Block} (fresh : OwnerFreshBlock body) : OwnerFreshExpr (.blockE body)
inductive OwnerFreshBlock : Core.Block → Prop
  | result (scope : Nat) (statements : List Stmt) {expr : Expr} (fresh : OwnerFreshExpr expr) :
      OwnerFreshBlock (.mk scope statements (some expr))
end

mutual
theorem ownerFreshExpr_of_source (expr : Expr) {env : TEnv} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env expr start = .ok (ty, finish)) (fresh : expr.freshOwner = true)
    (owner : isLiteralRunType ty = true) : OwnerFreshExpr expr := by
  cases expr <;> try simp only [Core.Expr.freshOwner, Bool.false_eq_true] at fresh
  case arrLit arrayTy values =>
    have same := (tyExpr_arrayLiteral_children source).1
    subst ty
    exact .literal arrayTy values owner
  case blockE body =>
    exact .block (ownerFreshBlock_of_source body source fresh owner)
  case ifE condition yes no =>
    have freshBranches : yes.freshOwner = true ∧ no.freshOwner = true := by
      simpa only [Core.Expr.freshOwner, Bool.and_eq_true] using fresh
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨yesTy, _, yesSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨noTy, noFinish, noSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    by_cases equal : (yesTy == noTy) = true
    · simp only [equal, ite_true] at source
      have resultType := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      change ty = yesTy at resultType
      have same := eq_of_beq equal
      subst noTy
      subst ty
      exact .conditional condition
        (ownerFreshBlock_of_source yes yesSource freshBranches.1 owner)
        (ownerFreshBlock_of_source no noSource freshBranches.2 owner)
    · simp only [equal] at source
      change ((Core.rej .type "the branches of `if` have different types" : Core.T Unit) >>=
        fun _ => pure yesTy) noFinish = .ok (ty, finish) at source
      obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
      exact (rej_ok _ _ _ _).mp rejected |>.elim

theorem ownerFreshBlock_of_source (body : Core.Block) {env : TEnv} {ty : Ty} {start finish : Nat}
    (source : Core.tyBlock env [] body start = .ok (ty, finish)) (fresh : body.freshOwner = true)
    (owner : isLiteralRunType ty = true) : OwnerFreshBlock body := by
  cases body with
  | mk scope statements value =>
    cases value with
    | none => simp [Core.Block.freshOwner] at fresh
    | some expr =>
      obtain ⟨_, declared, output, statementStart, valueStart, _, _, child⟩ := tyBlock_checked_children source
      exact .result scope statements (ownerFreshExpr_of_source expr child fresh owner)
end

end Goose.Lower.Validation
