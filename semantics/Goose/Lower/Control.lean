import Goose.Lower.IfFlow

namespace Goose.Lower

open Goose.Core Goose.GIR

mutual
def flowStmtOk : Stmt → Bool
  | .ifS c t none _ => exprOk c && flowBlockOk t
  | .ifS c t (some block) _ => exprOk c && flowBlockOk t && flowBlockOk block
  | stmt => stmtReturnOk stmt

def flowStmtsOk : List Stmt → Bool
  | [] => true
  | stmt :: rest => flowStmtOk stmt && flowStmtsOk rest

def flowBlockOk : Core.Block → Bool
  | .mk _ stmts value => flowStmtsOk stmts &&
      (match value with | none => true | some expr => exprOk expr)
end

def FlowStmtClaim (n : Nat) (lc : Option LoopCtx) (stmt : Stmt) : Prop :=
  flowStmtOk stmt = true → ∀ (le : LEnv) (ls ls' : LS) (u : Unit) (pt : Pt)
    (cfg : Cfg) (env : Env) (cx : FnCtx) (fr : GIR.Frame),
    lowerStmt lc stmt le ls = (u, ls') → ls.pp = some pt → ExtT ls' cx.fn.blocks →
    Rel cfg env cx fr ls →
    SimG cx pt fr (execStmt n cfg env stmt >>= prepareReturn env)
      (StmtFlowPost cfg env cx ls fr ls')

def FlowStmtsClaim (n : Nat) (lc : Option LoopCtx) (stmts : List Stmt) : Prop :=
  flowStmtsOk stmts = true → StatementsFlowSimulation n lc stmts

def FlowBlockClaim (n : Nat) (lc : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val))
    (want : Bool) (blk : Core.Block) : Prop :=
  flowBlockOk blk = true → ∀ (cfg : Cfg) (env : Env),
    (∀ p ∈ pre, ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = blk.scope) →
    ∀ (le : LEnv) (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerBlock lc pre want blk le ls = (r, ls') → ls.pp = some pt →
    ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls → PreRel fr pre pre' →
    SimG cx pt fr (execBlock n cfg env pre' blk >>= prepareReturn env)
      (BlockFlowPost cfg env cx ls fr ls' blk want r)

structure FlowClaims (n : Nat) : Prop where
  stmt : ∀ lc stmt, FlowStmtClaim n lc stmt
  stmts : ∀ lc stmts, FlowStmtsClaim n lc stmts
  block : ∀ lc pre pre' want blk, FlowBlockClaim n lc pre pre' want blk

theorem flowStmtsClaim_succ (n : Nat) (lc : Option LoopCtx)
    (ihs : ∀ stmt, FlowStmtClaim n lc stmt) (ihss : ∀ stmts, FlowStmtsClaim n lc stmts)
    (stmts : List Stmt) : FlowStmtsClaim (n + 1) lc stmts := by
  cases stmts with
  | nil =>
    intro hok le ls ls' u pt cfg env cx fr hlow hpp hext hrel
    simp only [lowerStmts, pure_run] at hlow
    obtain ⟨_, rfl⟩ := Prod.mk.inj hlow
    simp only [execStmts, pure_bind, prepareReturn]
    exact SimG.ret (Or.inl ⟨rfl, Post.init hrel hpp⟩)
  | cons stmt rest =>
    intro hok le ls ls' u pt cfg env cx fr hlow hpp hext hrel
    simp only [flowStmtsOk, Bool.and_eq_true] at hok
    obtain ⟨hokStmt, hokRest⟩ := hok
    obtain ⟨blk, hc, _, _⟩ := LS.pp_some hpp
    simp only [lowerStmts, bind_eq] at hlow
    obtain ⟨live, ls0, hlive, hlow⟩ := hlow
    rw [isLive_run hc] at hlive
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlive
    simp only [ite_true, bind_eq] at hlow
    obtain ⟨u1, ls1, hstmt, hrest⟩ := hlow
    have hext1 := hext.of_adv (advB_lowerStmts lc rest _ _ _ _ hrest)
    rw [prepareReturn_execStmts]
    refine SimG.bind (ihs stmt hokStmt le ls ls1 u1 pt cfg env cx fr hstmt hpp hext1 hrel)
      fun flow pt1 fr1 hpost => ?_
    rcases hpost with ⟨rfl, hnormal⟩ | ⟨value, org, rfl, hreturned⟩
    · exact (ihss rest hokRest le ls1 ls' u pt1 cfg env cx fr1 hrest hnormal.pp hext
        hnormal.rel).mono fun flow' pt' fr' hpost' => by
        rcases hpost' with ⟨hflow, hpost'⟩ | hreturned'
        · exact Or.inl ⟨hflow, (hnormal.comp hpost').sub (by simp)⟩
        · exact Or.inr hreturned'
    · exact SimG.ret (Or.inr ⟨value, org, rfl, hreturned⟩)

theorem flowBlockClaim_succ (n : Nat) (lc : Option LoopCtx)
    (ihss : ∀ stmts, FlowStmtsClaim n lc stmts)
    (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val))
    (want : Bool) (blk : Core.Block) : FlowBlockClaim (n + 1) lc pre pre' want blk := by
  obtain ⟨sc, stmts, value⟩ := blk
  intro hok cfg env hpre le ls ls' r pt cx fr hlow hpp hext hrel hprer
  simp only [flowBlockOk, Bool.and_eq_true] at hok
  exact blockFlow_sim n lc pre pre' want sc stmts value
    (ihss stmts hok.1) hok.2 cfg env hpre le ls ls' r pt cx fr hlow hpp hext hrel hprer

theorem flowStmtClaim_succ (n : Nat) (lc : Option LoopCtx)
    (ihb : ∀ pre pre' want blk, FlowBlockClaim n lc pre pre' want blk)
    (stmt : Stmt) : FlowStmtClaim (n + 1) lc stmt := by
  intro hok le ls ls' u pt cfg env cx fr hlow hpp hext hrel
  cases stmt with
  | ifS c t f org =>
    cases f with
    | none =>
      simp only [flowStmtOk, Bool.and_eq_true] at hok
      have hthen : BlockFlowSimulation n lc t := by
        intro le ls r ls' pt cfg env cx fr hlow hpp hext hrel
        exact ihb [] [] false t hok.2 cfg env (by simp)
          le ls ls' r pt cx fr hlow hpp hext hrel trivial
      exact stmt_if_none_flow_sim n lc c t org hok.1 hthen
        le ls u ls' pt cfg env cx fr hlow hpp hext hrel
    | some fb =>
      simp only [flowStmtOk, Bool.and_eq_true] at hok
      have hthen : BlockFlowSimulation n lc t := by
        intro le ls r ls' pt cfg env cx fr hlow hpp hext hrel
        exact ihb [] [] false t hok.1.2 cfg env (by simp)
          le ls ls' r pt cx fr hlow hpp hext hrel trivial
      have helse : BlockFlowSimulation n lc fb := by
        intro le ls r ls' pt cfg env cx fr hlow hpp hext hrel
        exact ihb [] [] false fb hok.2 cfg env (by simp)
          le ls ls' r pt cx fr hlow hpp hext hrel trivial
      exact stmt_if_some_flow_sim n lc c t fb org hok.1.1 hthen helse
        le ls u ls' pt cfg env cx fr hlow hpp hext hrel
  | _ =>
    simp only [flowStmtOk] at hok
    apply stmtReturnClaim (n + 1) lc _ _ le ls ls' u pt cfg env cx fr hlow hpp hext hrel
    exact hok

theorem flowClaims (n : Nat) : FlowClaims n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro lc stmt hok le ls ls' u pt cfg env cx fr hlow hpp hext hrel
      simp only [execStmt]
      exact SimG.of_timeout_bind
    · intro lc stmts hok le ls ls' u pt cfg env cx fr hlow hpp hext hrel
      simp only [execStmts]
      exact SimG.of_timeout_bind
    · intro lc pre pre' want blk hok cfg env hpre le ls ls' r pt cx fr hlow hpp hext hrel hprer
      simp only [execBlock]
      exact SimG.of_timeout_bind
  | succ n ih =>
    exact ⟨fun lc => flowStmtClaim_succ n lc (ih.block lc),
      fun lc => flowStmtsClaim_succ n lc (ih.stmt lc) (ih.stmts lc),
      fun lc pre pre' => flowBlockClaim_succ n lc (ih.stmts lc) pre pre'⟩

end Goose.Lower
