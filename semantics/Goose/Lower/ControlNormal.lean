import Goose.Lower.Control
import Goose.Lower.Normal

namespace Goose.Lower

open Goose.Core Goose.GIR

private theorem flow_bind_ok {c : M α} {f : α → M β} {s s' : St} {b : β}
    (h : (c >>= f) s = .ok b s') :
    ∃ a middle, c s = .ok a middle ∧ f a middle = .ok b s' := by
  rw [bind_apply] at h
  cases hc : c s with
  | stop err middle => rw [hc] at h; cases h
  | ok a middle => exact ⟨a, middle, rfl, by simpa [hc] using h⟩

private theorem unitFlow_normal_source (flow : Flow) (s s' : St) (value : Val)
    (h : (pure (unitFlow flow) : M Flow) s = .ok (.normal value) s') :
    ∃ v, flow = .normal v := by
  cases flow with
  | normal v => exact ⟨v, rfl⟩
  | _ => simp [unitFlow, pure_apply] at h

private theorem valueFlow_normal_source (n : Nat) (cfg : Cfg) (value : Option Expr)
    (env : Env) (flow : Flow) (s s' : St) (v : Val)
    (h : valueFlow n cfg value env flow s = .ok (.normal v) s') :
    ∃ w, flow = .normal w := by
  cases flow with
  | normal w => exact ⟨w, rfl⟩
  | _ => cases value <;> simp [valueFlow, pure_apply] at h

private structure NormalDivergenceClaims (n : Nat) : Prop where
  stmt : ∀ cfg env stmt, flowStmtOk stmt = true → stmt.diverges cfg.mod.noReturn = true →
    ∀ s s' value, execStmt n cfg env stmt s = .ok (.normal value) s' → False
  stmts : ∀ cfg env stmts, flowStmtsOk stmts = true →
    stmtsDiverge cfg.mod.noReturn stmts = true →
    ∀ s s' value, execStmts n cfg env stmts s = .ok (.normal value) s' → False
  block : ∀ cfg env pre block, flowBlockOk block = true → block.diverges cfg.mod.noReturn = true →
    ∀ s s' value, execBlock n cfg env pre block s = .ok (.normal value) s' → False

private theorem normalDivergenceClaims (n : Nat) : NormalDivergenceClaims n := by
  induction n with
  | zero =>
    constructor <;> intros <;> simp_all [execStmt, execStmts, execBlock, timeout, M.stop]
  | succ n ih =>
    constructor
    · intro cfg env stmt hok hd s s' value h
      cases stmt with
      | abort message org => simp [execStmt, abortAt, M.stop] at h
      | exit e org =>
        simp only [execStmt] at h
        obtain ⟨_, _, _, hrest⟩ := flow_bind_ok h
        obtain ⟨_, _, _, hrest⟩ := flow_bind_ok hrest
        simp [M.stop] at hrest
      | ret e org =>
        cases e with
        | none => simp [execStmt, pure_apply] at h
        | some e =>
          simp only [execStmt] at h
          obtain ⟨_, _, _, hrest⟩ := flow_bind_ok h
          simp [pure_apply] at hrest
      | ifS c t f org =>
        cases f with
        | none => simp [Stmt.diverges] at hd
        | some f =>
          have hd' : t.diverges cfg.mod.noReturn = true ∧ f.diverges cfg.mod.noReturn = true := by
            simpa [Stmt.diverges] using hd
          have hok' : exprOk c = true ∧ flowBlockOk t = true ∧ flowBlockOk f = true := by
            simpa [flowStmtOk, Bool.and_eq_true, and_assoc] using hok
          simp only [execStmt] at h
          obtain ⟨_, _, _, hrest⟩ := flow_bind_ok h
          obtain ⟨branch, middle, _, hrest⟩ := flow_bind_ok hrest
          cases branch
          · simp only [Bool.false_eq_true, ↓reduceIte] at hrest
            obtain ⟨flow, after, hbranch, htail⟩ := flow_bind_ok hrest
            obtain ⟨v, rfl⟩ := unitFlow_normal_source flow after s' value (by cases flow <;> exact htail)
            exact ih.block cfg env [] f hok'.2.2 hd'.2 middle after v hbranch
          · simp only [↓reduceIte] at hrest
            obtain ⟨flow, after, hbranch, htail⟩ := flow_bind_ok hrest
            obtain ⟨v, rfl⟩ := unitFlow_normal_source flow after s' value (by cases flow <;> exact htail)
            exact ih.block cfg env [] t hok'.2.1 hd'.1 middle after v hbranch
      | «while» c body org =>
        have hb : flowBlockOk body = true := by
          have hok' : exprOk c = true ∧ flowBlockOk body = true := by simpa [flowStmtOk] using hok
          exact hok'.2
        cases c with
        | bool b =>
          cases b with
          | false => simp [Stmt.diverges] at hd
          | true =>
            rw [execStmt] at h
            exact execWhile_true_never_normal n cfg env body hb s s' value h
        | _ => simp [Stmt.diverges] at hd
      | expr e org => cases e <;> simp_all [Stmt.diverges, flowStmtOk, stmtReturnOk, stmtOk, exprOk]
      | _ => simp_all [Stmt.diverges, flowStmtOk, stmtReturnOk, stmtOk]
    · intro cfg env stmts hok hd s s' value h
      cases stmts with
      | nil => simp [stmtsDiverge] at hd
      | cons stmt rest =>
        have hok' : flowStmtOk stmt = true ∧ flowStmtsOk rest = true := by
          simpa [flowStmtsOk] using hok
        have hd' : stmt.diverges cfg.mod.noReturn = true ∨
            stmtsDiverge cfg.mod.noReturn rest = true := by
          simpa [stmtsDiverge] using hd
        simp only [execStmts] at h
        obtain ⟨flow, middle, hstmt, hrest⟩ := flow_bind_ok h
        cases flow with
        | normal v =>
          rcases hd' with hd' | hd'
          · exact ih.stmt cfg env stmt hok'.1 hd' s middle v hstmt
          · exact ih.stmts cfg env rest hok'.2 hd' middle s' value hrest
        | _ => simp [pure_apply] at hrest
    · intro cfg env pre block hok hd s s' value h
      cases block with
      | mk scope stmts expression =>
        rw [flowBlockOk.eq_def] at hok
        have hstmts : flowStmtsOk stmts = true := ((Bool.and_eq_true _ _).mp hok).1
        rw [Core.Block.diverges.eq_def] at hd
        rw [execBlock_pre] at h
        unfold prefixCoreBlock at h
        obtain ⟨si, middle, _, hrest⟩ := flow_bind_ok h
        obtain ⟨_, bound, _, hrest⟩ := flow_bind_ok hrest
        obtain ⟨flow, after, hsource, hrest⟩ := flow_bind_ok hrest
        obtain ⟨result, cleaned, hvalue, hrest⟩ := flow_bind_ok hrest
        obtain ⟨_, final, _, hrest⟩ := flow_bind_ok hrest
        simp only [pure_apply] at hrest
        obtain ⟨rfl, rfl⟩ := Res.ok.inj hrest
        obtain ⟨v, rfl⟩ := valueFlow_normal_source n cfg expression
          { env with scopes := (scope, si) :: env.scopes } flow after cleaned value hvalue
        exact ih.stmts cfg { env with scopes := (scope, si) :: env.scopes }
          stmts hstmts hd bound after v hsource

theorem execBlock_normal_not_divergent (n : Nat) (cfg : Cfg) (env : Env)
    (pre : List (VarId × Val)) (block : Core.Block) (hok : flowBlockOk block = true)
    (s s' : St) (value : Val)
    (h : execBlock n cfg env pre block s = .ok (.normal value) s') :
    block.diverges cfg.mod.noReturn = false := by
  cases hd : block.diverges cfg.mod.noReturn with
  | false => rfl
  | true => exact False.elim ((normalDivergenceClaims n).block cfg env pre block hok hd s s' value h)

end Goose.Lower
