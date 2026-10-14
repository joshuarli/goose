import Goose.Lower.Claims

namespace Goose.Lower

open Goose.Core Goose.GIR

private def initialBuilder (env : Env) : LS :=
  { blocks := #[⟨[], #[]⟩], vals := #[], cur := some 0,
    stack := env.scopes.map Prod.fst }

private def fragmentFunction (env : Env) (ls : LS) : Func :=
  { name := "", params := [], results := [],
    slots := env.vars.mapIdx fun i lv => ⟨lv.ty, lv.kind, lv.scope, i⟩,
    scopes := #[], blocks := finishBlocks ls.blocks, summary := .unknown, org := none }

private theorem fragment_ext (env : Env) (ls : LS) :
    ExtT ls (fragmentFunction env ls).blocks := by
  refine ⟨by simp [fragmentFunction, finishBlocks], fun i blk hi => ?_⟩
  refine ⟨⟨blk.params, blk.insts.toList⟩, ?_, rfl, [], by simp⟩
  simp [fragmentFunction, finishBlocks, Array.getElem?_map, hi]

private def fragmentContext (cfg : Cfg) (env : Env) (ls : LS) : FnCtx :=
  ⟨⟨cfg.profile, lower cfg.mod⟩, fragmentFunction env ls⟩

private theorem fragment_rel (cfg : Cfg) (env : Env) (ls : LS) :
    Rel cfg env (fragmentContext cfg env ls)
      ⟨env.act, env.scopes, {}, env.depth⟩ (initialBuilder env) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem execBlock_fragment_normal (n : Nat) (cfg : Cfg) (env : Env) (b : Core.Block)
    (hb : blockOk b = true) (s s' : St) (flow : Flow)
    (h : execBlock n cfg env [] b s = .ok flow s') :
    ∃ v, flow = .normal v := by
  let le := lowerEnv cfg.mod env.vars
  let result := lowerBlock none [] false b le (initialBuilder env)
  have hlow : lowerBlock none [] false b le (initialBuilder env) = (result.1, result.2) := rfl
  have hsim := (claims n).block none false b hb le (initialBuilder env) result.1 result.2
    (0, 0) cfg env (fragmentContext cfg env result.2) ⟨env.act, env.scopes, {}, env.depth⟩
    hlow rfl (fragment_ext env result.2) (fragment_rel cfg env result.2)
  obtain ⟨_, _, _, ⟨v, hv, _, _⟩, _⟩ := (hsim s).1 flow s' h
  exact ⟨v, hv⟩

theorem execStmt_fragment_normal (n : Nat) (cfg : Cfg) (env : Env) (stmt : Stmt)
    (hs : stmtOk stmt = true) (s s' : St) (flow : Flow)
    (h : execStmt n cfg env stmt s = .ok flow s') : flow = .normal .unit := by
  let le := lowerEnv cfg.mod env.vars
  let result := lowerStmt none stmt le (initialBuilder env)
  have hlow : lowerStmt none stmt le (initialBuilder env) = (result.1, result.2) := rfl
  have hsim := (claims n).stmt none stmt hs le (initialBuilder env) result.1 result.2
    (0, 0) cfg env (fragmentContext cfg env result.2) ⟨env.act, env.scopes, {}, env.depth⟩
    hlow rfl (fragment_ext env result.2) (fragment_rel cfg env result.2)
  obtain ⟨_, _, _, ⟨hf, _⟩, _⟩ := (hsim s).1 flow s' h
  exact hf

private theorem bind_ok {c : M α} {f : α → M β} {s s' : St} {b : β}
    (h : (c >>= f) s = .ok b s') :
    ∃ a mid, c s = .ok a mid ∧ f a mid = .ok b s' := by
  rw [bind_apply] at h
  cases hc : c s with
  | stop e mid => rw [hc] at h; cases h
  | ok a mid => exact ⟨a, mid, rfl, by simpa [hc] using h⟩

theorem execWhile_true_never_ok (n : Nat) (cfg : Cfg) (env : Env) (body : Core.Block)
    (hb : blockOk body = true) (s s' : St) (flow : Flow)
    (h : execWhile n cfg env (.bool true) body s = .ok flow s') : False := by
  induction n generalizing s s' flow with
  | zero => simp [execWhile, timeout, M.stop] at h
  | succ n ih =>
    cases n with
    | zero => simp [execWhile, evalExpr, timeout, M.stop, bind_apply] at h
    | succ k =>
      rw [execWhile, evalExpr] at h
      simp only [pure_bind, expectBool, ↓reduceIte] at h
      obtain ⟨flow1, mid, hbody, hrest⟩ := bind_ok h
      obtain ⟨v, rfl⟩ := execBlock_fragment_normal (k + 1) cfg env body hb s mid flow1 hbody
      change execWhile (k + 1) cfg env (.bool true) body mid = .ok flow s' at hrest
      exact ih mid s' flow hrest

private structure DivergenceClaims (n : Nat) : Prop where
  stmt : ∀ cfg env stmt, stmtOk stmt = true → stmt.diverges cfg.mod.noReturn = true →
    ∀ s s' flow, execStmt n cfg env stmt s = .ok flow s' → False
  stmts : ∀ cfg env ss, stmtsOk ss = true → stmtsDiverge cfg.mod.noReturn ss = true →
    ∀ s s' flow, execStmts n cfg env ss s = .ok flow s' → False
  block : ∀ cfg env b, blockOk b = true → b.diverges cfg.mod.noReturn = true →
    ∀ s s' flow, execBlock n cfg env [] b s = .ok flow s' → False

private theorem divergenceClaims (n : Nat) : DivergenceClaims n := by
  induction n with
  | zero =>
    constructor <;> intros <;> simp_all [execStmt, execStmts, execBlock, timeout, M.stop]
  | succ n ih =>
    constructor
    · intro cfg env stmt hok hd s s' flow h
      cases stmt with
      | abort msg org => simp [execStmt, abortAt, M.stop] at h
      | exit e org =>
        simp only [execStmt] at h
        obtain ⟨_, _, _, hrest⟩ := bind_ok h
        obtain ⟨_, _, _, hrest⟩ := bind_ok hrest
        simp [M.stop] at hrest
      | ifS c t f org =>
        cases f with
        | none => simp [Stmt.diverges] at hd
        | some f =>
          have hd' : t.diverges cfg.mod.noReturn = true ∧ f.diverges cfg.mod.noReturn = true := by
            simpa [Stmt.diverges] using hd
          have hok' : exprOk c = true ∧ blockOk t = true ∧ blockOk f = true := by
            simpa [stmtOk, Bool.and_eq_true, and_assoc] using hok
          simp only [execStmt] at h
          obtain ⟨_, _, _, hrest⟩ := bind_ok h
          obtain ⟨branch, mid, _, hrest⟩ := bind_ok hrest
          cases branch
          · simp only [Bool.false_eq_true, ↓reduceIte] at hrest
            obtain ⟨flow1, after, hbranch, _⟩ := bind_ok hrest
            exact ih.block cfg env f hok'.2.2 hd'.2 mid after flow1 hbranch
          · simp only [↓reduceIte] at hrest
            obtain ⟨flow1, after, hbranch, _⟩ := bind_ok hrest
            exact ih.block cfg env t hok'.2.1 hd'.1 mid after flow1 hbranch
      | «while» c body org =>
        rw [stmtOk.eq_def] at hok
        have hb : blockOk body = true := (Bool.and_eq_true _ _).mp hok |>.2
        cases c with
        | bool b =>
          cases b with
          | false => simp [Stmt.diverges] at hd
          | true =>
            rw [execStmt] at h
            exact execWhile_true_never_ok n cfg env body hb s s' flow h
        | _ => simp [Stmt.diverges] at hd
      | expr e org => cases e <;> simp_all [Stmt.diverges, stmtOk, exprOk]
      | ret e org => simp [stmtOk] at hok
      | _ => simp_all [Stmt.diverges, stmtOk]
    · intro cfg env ss hok hd s s' flow h
      cases ss with
      | nil => simp [stmtsDiverge] at hd
      | cons stmt rest =>
        have hok' : stmtOk stmt = true ∧ stmtsOk rest = true := by
          simpa [stmtsOk] using hok
        have hd' : stmt.diverges cfg.mod.noReturn = true ∨
            stmtsDiverge cfg.mod.noReturn rest = true := by
          simpa [stmtsDiverge] using hd
        simp only [execStmts] at h
        obtain ⟨flow1, mid, hstmt, hrest⟩ := bind_ok h
        rcases hd' with hd' | hd'
        · exact ih.stmt cfg env stmt hok'.1 hd' s mid flow1 hstmt
        · have hf := execStmt_fragment_normal n cfg env stmt hok'.1 s mid flow1 hstmt
          subst hf
          exact ih.stmts cfg env rest hok'.2 hd' mid s' flow hrest
    · intro cfg env b hok hd s s' flow h
      cases b with
      | mk sc ss value =>
        rw [blockOk.eq_def] at hok
        rw [Core.Block.diverges.eq_def] at hd
        have hs : stmtsOk ss = true := (Bool.and_eq_true _ _).mp hok |>.1
        rw [execBlock_nil] at h
        unfold coreBlock at h
        obtain ⟨si, mid, _, hrest⟩ := bind_ok h
        obtain ⟨flow1, after, hstmts, _⟩ := bind_ok hrest
        exact ih.stmts cfg { env with scopes := (sc, si) :: env.scopes } ss hs hd
          mid after flow1 hstmts

theorem execBlock_success_not_divergent (n : Nat) (cfg : Cfg) (env : Env) (b : Core.Block)
    (hb : blockOk b = true) (s s' : St) (flow : Flow)
    (h : execBlock n cfg env [] b s = .ok flow s') : b.diverges cfg.mod.noReturn = false := by
  cases hd : b.diverges cfg.mod.noReturn with
  | false => rfl
  | true => exact False.elim ((divergenceClaims n).block cfg env b hb hd s s' flow h)

end Goose.Lower
