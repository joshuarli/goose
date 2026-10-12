import Goose.Share.Equal

/-!
Soundness of `Goose.Share.Equal`: when a boolean comparison says two terms are
equal, they are. Each theorem recurses on its first argument and splits the
second, so a mismatch of constructors is refuted by the comparison itself.
-/

namespace Goose.Share

open Goose.Core

mutual
theorem eqPlace_sound : ∀ (a b : Place), eqPlace a b = true → a = b
  | .var x, c, h => by
    cases c with
    | var y => simp_all [eqPlace]
    | _ => simp [eqPlace] at h
  | .global g, c, h => by
    cases c with
    | global g' => simp_all [eqPlace]
    | _ => simp [eqPlace] at h
  | .deref e, c, h => by
    cases c with
    | deref f => have := eqExpr_sound _ _ (by simpa [eqPlace] using h); simp_all
    | _ => simp [eqPlace] at h
  | .elem v i o, c, h => by
    cases c with
    | elem w j p =>
      simp only [eqPlace, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3⟩ := h
      have := eqView_sound _ _ h1; have := eqExpr_sound _ _ h2; simp_all
    | _ => simp [eqPlace] at h

theorem eqView_sound : ∀ (a b : View), eqView a b = true → a = b
  | .of p, c, h => by
    cases c with
    | of q => have := eqPlace_sound _ _ (by simpa [eqView] using h); simp_all
    | _ => simp [eqView] at h
  | .val e, c, h => by
    cases c with
    | val f => have := eqExpr_sound _ _ (by simpa [eqView] using h); simp_all
    | _ => simp [eqView] at h

theorem eqBound_sound : ∀ (a b : Bound), eqBound a b = true → a = b
  | .expr e, c, h => by
    cases c with
    | expr f => have := eqExpr_sound _ _ (by simpa [eqBound] using h); simp_all
    | _ => simp [eqBound] at h
  | .fromEnd e, c, h => by
    cases c with
    | fromEnd f => have := eqExpr_sound _ _ (by simpa [eqBound] using h); simp_all
    | _ => simp [eqBound] at h
  | .omitted, c, h => by
    cases c with
    | omitted => rfl
    | _ => simp [eqBound] at h

theorem eqExpr_sound : ∀ (a b : Expr), eqExpr a b = true → a = b
  | .lit t n, c, h => by
    cases c with
    | lit u m => simp_all [eqExpr]
    | _ => simp [eqExpr] at h
  | .bool x, c, h => by
    cases c with
    | bool y => simp_all [eqExpr]
    | _ => simp [eqExpr] at h
  | .read p, c, h => by
    cases c with
    | read q => have := eqPlace_sound _ _ (by simpa [eqExpr] using h); simp_all
    | _ => simp [eqExpr] at h
  | .ref m p, c, h => by
    cases c with
    | ref n q =>
      simp only [eqExpr, Bool.and_eq_true, beq_iff_eq] at h
      have := eqPlace_sound _ _ h.2; simp_all
    | _ => simp [eqExpr] at h
  | .slice m v lo hi o, c, h => by
    cases c with
    | slice n w lo' hi' p =>
      simp only [eqExpr, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have := eqView_sound _ _ h2; have := eqBound_sound _ _ h3
      have := eqBound_sound _ _ h4; simp_all
    | _ => simp [eqExpr] at h
  | .len v, c, h => by
    cases c with
    | len w => have := eqView_sound _ _ (by simpa [eqExpr] using h); simp_all
    | _ => simp [eqExpr] at h
  | .un op e o, c, h => by
    cases c with
    | un op' f p =>
      simp only [eqExpr, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3⟩ := h
      have := eqExpr_sound _ _ h2; simp_all
    | _ => simp [eqExpr] at h
  | .bin op a b o, c, h => by
    cases c with
    | bin op' a' b' p =>
      simp only [eqExpr, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      have := eqExpr_sound _ _ h2; have := eqExpr_sound _ _ h3; simp_all
    | _ => simp [eqExpr] at h
  | .cmp op a b, c, h => by
    cases c with
    | cmp op' a' b' =>
      simp only [eqExpr, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3⟩ := h
      have := eqExpr_sound _ _ h2; have := eqExpr_sound _ _ h3; simp_all
    | _ => simp [eqExpr] at h
  | .and a b, c, h => by
    cases c with
    | and a' b' =>
      simp only [eqExpr, Bool.and_eq_true] at h
      have := eqExpr_sound _ _ h.1; have := eqExpr_sound _ _ h.2; simp_all
    | _ => simp [eqExpr] at h
  | .or a b, c, h => by
    cases c with
    | or a' b' =>
      simp only [eqExpr, Bool.and_eq_true] at h
      have := eqExpr_sound _ _ h.1; have := eqExpr_sound _ _ h.2; simp_all
    | _ => simp [eqExpr] at h
  | .not e, c, h => by
    cases c with
    | not f => have := eqExpr_sound _ _ (by simpa [eqExpr] using h); simp_all
    | _ => simp [eqExpr] at h
  | .conv k t e o, c, h => by
    cases c with
    | conv k' t' f p =>
      simp only [eqExpr, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      have := eqExpr_sound _ _ h3; simp_all
    | _ => simp [eqExpr] at h
  | .call n args o, c, h => by
    cases c with
    | call n' args' p =>
      simp only [eqExpr, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3⟩ := h
      have := eqArgs_sound _ _ h2; simp_all
    | _ => simp [eqExpr] at h
  | .push p e, c, h => by
    cases c with
    | push q f =>
      simp only [eqExpr, Bool.and_eq_true] at h
      have := eqPlace_sound _ _ h.1; have := eqExpr_sound _ _ h.2; simp_all
    | _ => simp [eqExpr] at h
  | .ifE x t f, c, h => by
    cases c with
    | ifE x' t' f' =>
      simp only [eqExpr, Bool.and_eq_true, and_assoc] at h
      obtain ⟨h1, h2, h3⟩ := h
      have := eqExpr_sound _ _ h1; have := eqBlock_sound _ _ h2
      have := eqBlock_sound _ _ h3; simp_all
    | _ => simp [eqExpr] at h
  | .blockE b, c, h => by
    cases c with
    | blockE b' => have := eqBlock_sound _ _ (by simpa [eqExpr] using h); simp_all
    | _ => simp [eqExpr] at h
  | .arrLit t es, c, h => by
    cases c with
    | arrLit u fs =>
      simp only [eqExpr, Bool.and_eq_true, beq_iff_eq] at h
      have := eqExprs_sound _ _ h.2; simp_all
    | _ => simp [eqExpr] at h
  | .fill t e, c, h => by
    cases c with
    | fill u f =>
      simp only [eqExpr, Bool.and_eq_true, beq_iff_eq] at h
      have := eqExpr_sound _ _ h.2; simp_all
    | _ => simp [eqExpr] at h

theorem eqExprs_sound : ∀ (a b : List Expr), eqExprs a b = true → a = b
  | [], c, h => by
    cases c with
    | nil => rfl
    | cons _ _ => simp [eqExprs] at h
  | e :: es, c, h => by
    cases c with
    | nil => simp [eqExprs] at h
    | cons f fs =>
      simp only [eqExprs, Bool.and_eq_true] at h
      have := eqExpr_sound _ _ h.1; have := eqExprs_sound _ _ h.2; simp_all

theorem eqArg_sound : ∀ (a b : Arg), eqArg a b = true → a = b
  | .byVal e, c, h => by
    cases c with
    | byVal f => have := eqExpr_sound _ _ (by simpa [eqArg] using h); simp_all
    | _ => simp [eqArg] at h
  | .byRef m p, c, h => by
    cases c with
    | byRef n q =>
      simp only [eqArg, Bool.and_eq_true, beq_iff_eq] at h
      have := eqPlace_sound _ _ h.2; simp_all
    | _ => simp [eqArg] at h

theorem eqArgs_sound : ∀ (a b : List Arg), eqArgs a b = true → a = b
  | [], c, h => by
    cases c with
    | nil => rfl
    | cons _ _ => simp [eqArgs] at h
  | e :: es, c, h => by
    cases c with
    | nil => simp [eqArgs] at h
    | cons f fs =>
      simp only [eqArgs, Bool.and_eq_true] at h
      have := eqArg_sound _ _ h.1; have := eqArgs_sound _ _ h.2; simp_all

theorem eqOptExpr_sound : ∀ (a b : Option Expr), eqOptExpr a b = true → a = b
  | none, c, h => by
    cases c with
    | none => rfl
    | some _ => simp [eqOptExpr] at h
  | some e, c, h => by
    cases c with
    | none => simp [eqOptExpr] at h
    | some f => have := eqExpr_sound _ _ (by simpa [eqOptExpr] using h); simp_all

theorem eqBlock_sound : ∀ (a b : Block), eqBlock a b = true → a = b
  | .mk s ss v, c, h => by
    cases c with
    | mk t ts w =>
      simp only [eqBlock, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3⟩ := h
      have := eqStmts_sound _ _ h2; have := eqOptExpr_sound _ _ h3; simp_all

theorem eqOptBlock_sound : ∀ (a b : Option Block), eqOptBlock a b = true → a = b
  | none, c, h => by
    cases c with
    | none => rfl
    | some _ => simp [eqOptBlock] at h
  | some e, c, h => by
    cases c with
    | none => simp [eqOptBlock] at h
    | some f => have := eqBlock_sound _ _ (by simpa [eqOptBlock] using h); simp_all

theorem eqPrintArg_sound : ∀ (a b : PrintArg), eqPrintArg a b = true → a = b
  | .text s, c, h => by
    cases c with
    | text t => simp_all [eqPrintArg]
    | _ => simp [eqPrintArg] at h
  | .expr e, c, h => by
    cases c with
    | expr f => have := eqExpr_sound _ _ (by simpa [eqPrintArg] using h); simp_all
    | _ => simp [eqPrintArg] at h

theorem eqPrintArgs_sound : ∀ (a b : List PrintArg), eqPrintArgs a b = true → a = b
  | [], c, h => by
    cases c with
    | nil => rfl
    | cons _ _ => simp [eqPrintArgs] at h
  | e :: es, c, h => by
    cases c with
    | nil => simp [eqPrintArgs] at h
    | cons f fs =>
      simp only [eqPrintArgs, Bool.and_eq_true] at h
      have := eqPrintArg_sound _ _ h.1; have := eqPrintArgs_sound _ _ h.2; simp_all

theorem eqStmt_sound : ∀ (a b : Stmt), eqStmt a b = true → a = b
  | .letS x e o, c, h => by
    cases c with
    | letS y f p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3⟩ := h
      have := eqExpr_sound _ _ h2; simp_all
    | _ => simp [eqStmt] at h
  | .assign q e o, c, h => by
    cases c with
    | assign q' f p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3⟩ := h
      have := eqPlace_sound _ _ h1; have := eqExpr_sound _ _ h2; simp_all
    | _ => simp [eqStmt] at h
  | .assignOp op q e o, c, h => by
    cases c with
    | assignOp op' q' f p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h0, h1, h2, h3⟩ := h
      have := eqPlace_sound _ _ h1; have := eqExpr_sound _ _ h2; simp_all
    | _ => simp [eqStmt] at h
  | .rebind x e o, c, h => by
    cases c with
    | rebind y f p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3⟩ := h
      have := eqExpr_sound _ _ h2; simp_all
    | _ => simp [eqStmt] at h
  | .expr e o, c, h => by
    cases c with
    | expr f p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq] at h
      have := eqExpr_sound _ _ h.1; simp_all
    | _ => simp [eqStmt] at h
  | .append q v o, c, h => by
    cases c with
    | append q' w p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3⟩ := h
      have := eqPlace_sound _ _ h1; have := eqView_sound _ _ h2; simp_all
    | _ => simp [eqStmt] at h
  | .ifS x t f o, c, h => by
    cases c with
    | ifS x' t' f' p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      have := eqExpr_sound _ _ h1; have := eqBlock_sound _ _ h2
      have := eqOptBlock_sound _ _ h3; simp_all
    | _ => simp [eqStmt] at h
  | .while x b o, c, h => by
    cases c with
    | «while» x' b' p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3⟩ := h
      have := eqExpr_sound _ _ h1; have := eqBlock_sound _ _ h2; simp_all
    | _ => simp [eqStmt] at h
  | .forRange x lo hi b o, c, h => by
    cases c with
    | forRange y lo' hi' b' p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have := eqExpr_sound _ _ h2; have := eqExpr_sound _ _ h3
      have := eqBlock_sound _ _ h4; simp_all
    | _ => simp [eqStmt] at h
  | .forEach x i v byRef b o, c, h => by
    cases c with
    | forEach y j w byRef' b' p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      have := eqView_sound _ _ h3; have := eqBlock_sound _ _ h5; simp_all
    | _ => simp [eqStmt] at h
  | .ret e o, c, h => by
    cases c with
    | ret f p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq] at h
      have := eqOptExpr_sound _ _ h.1; simp_all
    | _ => simp [eqStmt] at h
  | .brk o, c, h => by
    cases c with
    | brk p => simp_all [eqStmt]
    | _ => simp [eqStmt] at h
  | .cont o, c, h => by
    cases c with
    | cont p => simp_all [eqStmt]
    | _ => simp [eqStmt] at h
  | .print as o, c, h => by
    cases c with
    | print bs p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq] at h
      have := eqPrintArgs_sound _ _ h.1; simp_all
    | _ => simp [eqStmt] at h
  | .assertS e o, c, h => by
    cases c with
    | assertS f p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq] at h
      have := eqExpr_sound _ _ h.1; simp_all
    | _ => simp [eqStmt] at h
  | .abort s o, c, h => by
    cases c with
    | abort t p => simp_all [eqStmt]
    | _ => simp [eqStmt] at h
  | .exit e o, c, h => by
    cases c with
    | exit f p =>
      simp only [eqStmt, Bool.and_eq_true, beq_iff_eq] at h
      have := eqExpr_sound _ _ h.1; simp_all
    | _ => simp [eqStmt] at h

theorem eqStmts_sound : ∀ (a b : List Stmt), eqStmts a b = true → a = b
  | [], c, h => by
    cases c with
    | nil => rfl
    | cons _ _ => simp [eqStmts] at h
  | e :: es, c, h => by
    cases c with
    | nil => simp [eqStmts] at h
    | cons f fs =>
      simp only [eqStmts, Bool.and_eq_true] at h
      have := eqStmt_sound _ _ h.1; have := eqStmts_sound _ _ h.2; simp_all
end

end Goose.Share
