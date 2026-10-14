import Goose.Core.Sound.Stops

namespace Goose.Lower.SourceDivergence

open Goose.Core Goose.Core.Sound

private theorem only_bind {Q : α → Prop} {R : β → Prop} {x : M α} {f : α → M β}
    (hx : Only Q x) (hf : ∀ a, Q a → Only R (f a)) : Only R (x >>= f) := by
  intro s b s' hb
  change M.bind' x f s = .ok b s' at hb
  unfold M.bind' at hb
  cases hxs : x s with
  | ok a s1 => rw [hxs] at hb; exact hf a (hx s a s1 hxs) s1 b s' hb
  | stop e s1 => rw [hxs] at hb; cases hb

private theorem only_mono {Q R : α → Prop} {x : M α}
    (hx : Only Q x) (hf : ∀ a, Q a → R a) : Only R x :=
  fun s a s' h => hf a (hx s a s' h)

private def FlowFacts (divergent breaks : Bool) : Flow → Prop
  | .normal _ => divergent = false
  | .brk => breaks = true
  | _ => True

private def NoBreak : Flow → Prop
  | .brk => False
  | _ => True

private def WhileFacts (c : Expr) (body : Block) : Flow → Prop
  | .normal _ => c = .bool true → body.hasBreak = true
  | .brk => False
  | _ => True

private structure FactsAt (cfg : Cfg) (n : Nat) : Prop where
  block : ∀ env pre b, Only (FlowFacts (b.diverges cfg.mod.noReturn) b.hasBreak)
    (execBlock n cfg env pre b)
  stmts : ∀ env ss, Only (FlowFacts (stmtsDiverge cfg.mod.noReturn ss) (stmtsHaveBreak ss))
    (execStmts n cfg env ss)
  stmt : ∀ env st, Only (FlowFacts (st.diverges cfg.mod.noReturn) st.hasBreak)
    (execStmt n cfg env st)
  while_ : ∀ env c b, Only (WhileFacts c b) (execWhile n cfg env c b)
  range : ∀ env x t i hi b, Only NoBreak (execRange n cfg env x t i hi b)
  each : ∀ env x idx byRef b vw i, Only NoBreak (execEach n cfg env x idx byRef b vw i)

private theorem factsAt (cfg : Cfg) : ∀ n, FactsAt cfg n
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intros <;> simp only [execBlock, execStmts, execStmt, execWhile, execRange, execEach] <;>
      exact Only.of_never never_timeout
  | n + 1 => by
    have ih := factsAt cfg n
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro env pre b
      obtain ⟨sc, ss, value⟩ := b
      simp only [execBlock]
      refine Only.bind (fun si => Only.bind (fun _ => ?_))
      refine only_bind (ih.stmts _ ss) ?_
      intro flow hflow
      cases flow <;> cases value <;> simp only [FlowFacts] at hflow ⊢ <;>
        repeat' (first
          | rw [pure_bind_M]
          | exact Only.pure hflow
          | exact Only.pure trivial
          | refine Only.bind (fun _ => ?_)
          | simpa [Block.diverges, Block.hasBreak] using hflow)
    · intro env ss
      cases ss with
      | nil => simp only [execStmts]; exact Only.pure rfl
      | cons st rest =>
        simp only [execStmts]
        refine only_bind (ih.stmt env st) ?_
        intro flow hflow
        cases flow with
        | normal v =>
          refine only_mono (ih.stmts env rest) ?_
          intro fl hfl
          cases fl <;> simp_all [FlowFacts, stmtsDiverge, stmtsHaveBreak]
        | brk => exact Only.pure (by simp_all [FlowFacts, stmtsHaveBreak])
        | ret v => exact Only.pure trivial
        | cont => exact Only.pure trivial
    · intro env st
      cases st
      case expr e o =>
        cases hd : (Stmt.expr e o).diverges cfg.mod.noReturn with
        | false =>
          exact only_mono (plain_only (n + 1) cfg env _ (by rfl)) (fun fl hfl =>
            by cases fl <;> simp_all [IsNormal, FlowFacts])
        | true =>
          rw [execStmt]
          exact Only.of_never (Never.bind_left (never_call_expr cfg cfg.mod.noReturn
            (noReturn_sound cfg.mod cfg.profile) n env e o (by
              cases e <;> simp_all [Stmt.diverges])))
      case ifS c t f o =>
        rw [execStmt]
        refine Only.bind (fun _ => Only.bind (fun branch => ?_))
        cases branch <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · cases f with
          | none => exact Only.pure rfl
          | some fb =>
            refine only_bind (ih.block env [] fb) ?_
            intro fl hfl
            cases fl <;> exact Only.pure (by simp_all [FlowFacts, Stmt.diverges, Stmt.hasBreak])
        · refine only_bind (ih.block env [] t) ?_
          intro fl hfl
          cases fl <;> exact Only.pure (by cases f <;> simp_all [FlowFacts, Stmt.diverges, Stmt.hasBreak])
      case «while» c b o =>
        rw [execStmt]
        refine only_mono (ih.while_ env c b) ?_
        intro fl hfl
        cases fl <;> simp only [WhileFacts] at hfl
        · change (Stmt.while c b o).diverges cfg.mod.noReturn = false
          cases c <;> try rfl
          rename_i bit
          cases bit
          · rfl
          · simp only [Stmt.diverges, hfl rfl, Bool.not_true]
        · trivial
        · trivial
      case forRange x lo hi b o =>
        rw [execStmt]
        refine Only.bind (fun _ => Only.bind (fun _ => Only.bind (fun _ =>
          Only.bind (fun _ => Only.bind (fun _ => ?_)))))
        refine only_mono (ih.range env x _ _ _ b) ?_
        intro fl hfl
        cases fl <;> simp_all [NoBreak, FlowFacts, Stmt.diverges]
        all_goals trivial
      case forEach x idx vw byRef b o =>
        rw [execStmt]
        refine Only.bind (fun view => only_mono (ih.each env x idx byRef b view 0) ?_)
        intro fl hfl
        cases fl <;> simp_all [NoBreak, FlowFacts, Stmt.diverges]
        all_goals trivial
      case ret e o =>
        rw [execStmt.eq_def]
        cases e <;> repeat' (first | exact Only.pure trivial | refine Only.bind (fun _ => ?_))
      case brk o => rw [execStmt]; exact Only.pure rfl
      case cont o => rw [execStmt]; exact Only.pure trivial
      case abort msg o => rw [execStmt]; exact Only.of_never (never_abort _ _)
      case exit e o =>
        rw [execStmt]
        exact Only.of_never (Never.bind_right (fun _ => Never.bind_right (fun _ => never_stop _)))
      all_goals exact only_mono (plain_only (n + 1) cfg env _ (by rfl)) (fun fl hfl =>
        by cases fl <;> simp_all [IsNormal, FlowFacts, Stmt.diverges])
    · intro env c b
      by_cases hc : c = .bool true
      · subst c
        cases n with
        | zero => simp only [execWhile, evalExpr]; exact Only.of_never (Never.bind_left never_timeout)
        | succ k =>
          rw [execWhile]
          simp only [evalExpr, expectBool, pure_bind_M, ite_true]
          refine only_bind (ih.block env [] b) ?_
          intro fl hfl
          cases fl <;> simp only [FlowFacts] at hfl
          · exact ih.while_ env (.bool true) b
          · exact Only.pure (fun _ => hfl)
          · exact ih.while_ env (.bool true) b
          · exact Only.pure trivial
      · simp only [execWhile]
        refine Only.bind (fun _ => Only.bind (fun branch => ?_))
        cases branch <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        · exact Only.pure (by simp [WhileFacts, hc])
        · refine Only.bind (fun fl => ?_)
          cases fl
          · exact ih.while_ env c b
          · exact Only.pure (by simp [WhileFacts, hc])
          · exact ih.while_ env c b
          · exact Only.pure trivial
    · intro env x t i hi b
      simp only [execRange]
      split
      · refine Only.bind (fun fl => ?_)
        cases fl <;> first | exact ih.range env x t (i + 1) hi b | exact Only.pure trivial
      · exact Only.pure trivial
    · intro env x idx byRef b vw i
      rw [execEach.eq_def]
      dsimp only
      split <;> refine Only.bind (fun len => ?_)
      all_goals split
      all_goals first
        | exact Only.pure trivial
        | (split <;> refine Only.bind (fun ev => Only.bind (fun fl => ?_))
           all_goals cases fl <;> first
             | exact ih.each env x idx byRef b vw (i + 1)
             | exact Only.pure trivial)

theorem normalBlock_diverges_false (n : Nat) (cfg : Cfg) (env : Env)
    (pre : List (VarId × Val)) (body : Block) (state final : St) (value : Val)
    (h : execBlock n cfg env pre body state = .ok (.normal value) final) :
    body.diverges cfg.mod.noReturn = false :=
  (factsAt cfg n).block env pre body state (.normal value) final h

end Goose.Lower.SourceDivergence
