import Goose.Lower.Arguments
import Goose.Lower.Flow

namespace Goose.Lower

open Goose.Core Goose.GIR

def StatementESimulation (n : Nat) (cfg : Cfg) (lc : Option LoopCtx) (stmt : Stmt) : Prop :=
  ∀ (le : LEnv) (ls ls' : LS) (u : Unit) (pt : Pt)
    (env : Env) (cx : FnCtx) (fr : GIR.Frame),
    lowerStmt lc stmt le ls = (u, ls') → ls.pp = some pt → ExtT ls' cx.fn.blocks →
    Rel cfg env cx fr ls → le.mod = cfg.mod → cx.cfg.mod = lower cfg.mod →
    SimE cx pt fr (execStmt n cfg env stmt >>= prepareReturn env)
      (StmtFlowPost cfg env cx ls fr ls')

def StatementsESimulation (n : Nat) (cfg : Cfg) (lc : Option LoopCtx) (stmts : List Stmt) : Prop :=
  ∀ (le : LEnv) (ls ls' : LS) (u : Unit) (pt : Pt)
    (env : Env) (cx : FnCtx) (fr : GIR.Frame),
    lowerStmts lc stmts le ls = (u, ls') → ls.pp = some pt → ExtT ls' cx.fn.blocks →
    Rel cfg env cx fr ls → le.mod = cfg.mod → cx.cfg.mod = lower cfg.mod →
    SimE cx pt fr (execStmts n cfg env stmts >>= prepareReturn env)
      (StmtFlowPost cfg env cx ls fr ls')

theorem statementESimulation_zero (cfg : Cfg) (lc : Option LoopCtx) (stmt : Stmt) :
    StatementESimulation 0 cfg lc stmt := by
  intro le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir
  simp only [execStmt]
  exact SimE.of_simG SimG.of_timeout_bind

theorem statementESimulation_fragment (n : Nat) (cfg : Cfg) (lc : Option LoopCtx)
    (stmt : Stmt) (hok : stmtReturnOk stmt = true) : StatementESimulation n cfg lc stmt := by
  intro le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir
  exact SimE.of_simG (stmtReturnClaim n lc stmt hok le ls ls' u pt cfg env cx fr
    hlow hpp hext hrel)

theorem stmt_exprE_sim (n : Nat) (cfg : Cfg) (lc : Option LoopCtx) (expr : Expr)
    (org : OriginId) (hexpr : ExprEClaim n cfg expr) :
    StatementESimulation (n + 1) cfg lc (.expr expr org) := by
  intro le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨id, middle, hvalue, htail⟩ := hlow
  rw [pure_run] at htail
  have hmiddle := (Prod.mk.inj htail).2
  subst middle
  simp only [execStmt, bind_assoc]
  refine SimE.bind (hexpr le ls id ls' pt env cx fr hvalue hpp hext hrel hmod hgir)
    fun value pt' fr' hpost => ?_
  exact SimE.ret (Or.inl ⟨rfl, hpost.sub (by simp)⟩)

theorem statementsESimulation_zero (cfg : Cfg) (lc : Option LoopCtx) (stmts : List Stmt) :
    StatementsESimulation 0 cfg lc stmts := by
  intro le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir
  simp only [execStmts]
  exact SimE.of_simG SimG.of_timeout_bind

theorem statementsE_nil (n : Nat) (cfg : Cfg) (lc : Option LoopCtx) :
    StatementsESimulation (n + 1) cfg lc [] := by
  intro le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir
  simp only [lowerStmts, pure_run] at hlow
  obtain ⟨_, rfl⟩ := Prod.mk.inj hlow
  simp only [execStmts, pure_bind, prepareReturn]
  exact SimE.ret (Or.inl ⟨rfl, Post.init hrel hpp⟩)

theorem statementsE_cons (n : Nat) (cfg : Cfg) (lc : Option LoopCtx)
    (stmt : Stmt) (rest : List Stmt)
    (hstmt : StatementESimulation n cfg lc stmt) (hrest : StatementsESimulation n cfg lc rest) :
    StatementsESimulation (n + 1) cfg lc (stmt :: rest) := by
  intro le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir
  obtain ⟨blk, hc, _, _⟩ := LS.pp_some hpp
  simp only [lowerStmts, bind_eq] at hlow
  obtain ⟨live, ls0, hlive, hlow⟩ := hlow
  rw [isLive_run hc] at hlive
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlive
  simp only [ite_true, bind_eq] at hlow
  obtain ⟨u1, ls1, hs, hr⟩ := hlow
  have hext1 := hext.of_adv (advB_lowerStmts lc rest _ _ _ _ hr)
  rw [prepareReturn_execStmts]
  refine SimE.bind (hstmt le ls ls1 u1 pt env cx fr hs hpp hext1 hrel hmod hgir)
    fun flow pt1 fr1 hpost => ?_
  rcases hpost with ⟨rfl, hnormal⟩ | ⟨value, org, rfl, hreturned⟩
  · exact (hrest le ls1 ls' u pt1 env cx fr1 hr hnormal.pp hext hnormal.rel hmod hgir).mono
      fun flow' pt' fr' hpost' => by
      rcases hpost' with ⟨hflow, hpost'⟩ | hreturned'
      · exact Or.inl ⟨hflow, (hnormal.comp hpost').sub (by simp)⟩
      · exact Or.inr hreturned'
  · exact SimE.ret (Or.inr ⟨value, org, rfl, hreturned⟩)

def BlockESimulation (n : Nat) (cfg : Cfg) (lc : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val))
    (want : Bool) (block : Core.Block) : Prop :=
  ∀ (env : Env), (∀ p ∈ pre, ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = block.scope) →
    ∀ (le : LEnv) (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerBlock lc pre want block le ls = (r, ls') → ls.pp = some pt →
    ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls → PreRel fr pre pre' →
    le.mod = cfg.mod → cx.cfg.mod = lower cfg.mod →
    SimE cx pt fr (execBlock n cfg env pre' block >>= prepareReturn env)
      (BlockFlowPost cfg env cx ls fr ls' block want r)

theorem blockESimulation_zero (cfg : Cfg) (lc : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val))
    (want : Bool) (block : Core.Block) : BlockESimulation 0 cfg lc pre pre' want block := by
  intro env hpre le ls ls' r pt cx fr hlow hpp hext hrel hprer hmod hgir
  simp only [execBlock]
  exact SimE.of_simG SimG.of_timeout_bind

theorem preparedBlockE_core {n : Nat} {cfg : Cfg} {lc : Option LoopCtx} {sc : ScopeId}
    {stmts : List Stmt} {value : Option Expr} {pre : List (SlotId × ValueId × OriginId)}
    {pre' : List (VarId × Val)} {env : Env}
    (hstmts : StatementsESimulation n cfg lc stmts)
    {U : Val → Prop} {X : B ValueId} {cells : ValueId → Val → List (ValueId × RVal)}
    {le : LEnv} {ls ls1 ls_p ls_s ls_x ls_l ls' : LS} {u0 u : Unit} {rx r : ValueId}
    {pt : Pt} {cx : FnCtx} {fr : GIR.Frame}
    (hpre : ∀ p ∈ pre, ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = sc)
    (h1 : emitEffect (.enter sc) le ls = ((), ls1))
    (h2 : initSlots pre le { ls1 with stack := sc :: ls1.stack } = (u0, ls_p))
    (h3 : lowerStmts lc stmts le ls_p = (u, ls_s))
    (h4 : X le ls_s = (rx, ls_x)) (h5 : emitEffect (.leave sc) le ls_x = ((), ls_l))
    (hls' : ls' = { ls_l with stack := ls_l.stack.drop 1 }) (hr : r = rx)
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hprer : PreRel fr pre pre') (hmod : le.mod = cfg.mod)
    (hgir : cx.cfg.mod = lower cfg.mod) (hadvX : AdvB X)
    (hX : ∀ (env' : Env) (pt_x : Pt) (fr_x : GIR.Frame), ls_s.pp = some pt_x →
      ExtT ls_x cx.fn.blocks → Rel cfg env' cx fr_x ls_s →
      SimE cx pt_x fr_x (valueFlow n cfg value env' (.normal .unit))
        (fun flow pt' fr' => ∃ v, flow = .normal v ∧ U v ∧
          Post cfg env' cx ls_s fr_x ls_x fr' pt' (cells rx v))) :
    SimE cx pt fr (preparedCoreBlock n cfg env sc stmts value pre')
      (fun flow pt' fr' => (∃ v, flow = .normal v ∧ U v ∧
        Post cfg env cx ls fr ls' fr' pt' (cells r v)) ∨ ReturnedAt cx flow pt' fr') := by
  subst hr
  have hext_l : ExtT ls_l cx.fn.blocks := by rw [hls'] at hext; exact hext
  have hext_x := hext_l.of_adv (adv_emitEffect h5)
  have hext_s := hext_x.of_adv (hadvX _ _ _ _ h4)
  have hext_p := hext_s.of_adv (advB_lowerStmts lc stmts _ _ _ _ h3)
  have hext_i := hext_p.of_adv (advB_initSlots pre _ _ _ _ h2)
  have hext_1 : ExtT ls1 cx.fn.blocks := hext_i
  unfold preparedCoreBlock
  refine SimE.bind (SimE.of_simG (block_enter hpp h1 hext_1 hrel))
    fun si pt1 fr1 ⟨hpp1, hv1, hfr1, hrel1⟩ => ?_
  have hsc : ({ env with scopes := (sc, si) :: env.scopes } : Env).scopes.head? =
      some (sc, si) := rfl
  refine SimE.bind (SimE.of_simG (initSlots_sim hsc pre pre' hpre h2 hpp1 hext_p hrel1
    (PreRel.ext hfr1 hprer))) fun _ pt1' fr1' ⟨hpp1', hfr1', hst1', hvl1'⟩ => ?_
  subst fr1'
  have hrel1' : Rel cfg { env with scopes := (sc, si) :: env.scopes } cx fr1 ls_p :=
    hrel1.stack_eq hst1'
  refine SimE.bind (hstmts le _ ls_s u pt1' _ cx fr1
    h3 hpp1' hext_s hrel1' hmod hgir) fun flow pt2 fr2 hpost => ?_
  rcases hpost with ⟨rfl, P2⟩ | ⟨returned, org, rfl, hsite⟩
  · refine SimE.bind (hX _ pt2 fr2 P2.pp hext_x P2.rel)
      fun flow' pt3 fr3 ⟨v, hflow', hU, P3⟩ => ?_
    subst flow'
    refine SimE.bind (SimE.of_simG (block_leave P3.pp h5 hext_l P3.rel))
      fun _ pt4 fr4 ⟨hpp4, hv4, hfr4, hrel4⟩ => ?_
    refine SimE.ret (Or.inl ⟨v, rfl, hU, ?_⟩)
    have P23 := P2.comp P3
    refine Post.rescope (P23.sub (cells' := cells r v) (by simp))
      (hv0 := ?_) (hfr0 := hfr1) ?_ ?_ hfr4 ?_
    · rw [hvl1']; exact hv1
    · rw [hls']; exact hpp4
    · rw [hls']; exact hv4
    · rw [hls']; exact hrel4
  · exact SimE.ret (Or.inr ⟨returned, org, rfl, hsite⟩)

theorem blockEFlow_sim (n : Nat) (cfg : Cfg) (lc : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val))
    (want : Bool) (sc : ScopeId) (stmts : List Stmt) (value : Option Expr)
    (hstmts : StatementsESimulation n cfg lc stmts)
    (hvalue : match value with | none => True | some expr => ExprEClaim n cfg expr)
    (env : Env)
    (hpre : ∀ p ∈ pre, ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = sc)
    (le : LEnv) (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame)
    (hlow : lowerBlock lc pre want (.mk sc stmts value) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hprer : PreRel fr pre pre') (hmod : le.mod = cfg.mod)
    (hgir : cx.cfg.mod = lower cfg.mod) :
    SimE cx pt fr (execBlock (n + 1) cfg env pre' (.mk sc stmts value) >>= prepareReturn env)
      (BlockFlowPost cfg env cx ls fr ls' (.mk sc stmts value) want r) := by
  obtain ⟨ls1, ls_p, ls_s, ls_x, ls_l, u0, u, rx, h1, h2, h3, h4, h5, hls', hr⟩ :=
    prefixBlock_unfold hlow
  rw [prepareReturn_execBlock]
  cases value with
  | some expr =>
    simp only [lowerBlockValue] at h4
    refine (preparedBlockE_core hstmts hpre h1 h2 h3 h4 h5 hls' hr hpp hext hrel hprer hmod hgir
      (advB_lowerExpr expr) (U := fun _ => True) (cells := fun rx v => [(rx, .val v)]) ?_).mono ?_
    · intro env' pt_x fr_x hpp_x hext_x hrel_x
      simp only [valueFlow]
      refine SimE.bind (hvalue le ls_s rx ls_x pt_x env' cx fr_x
        h4 hpp_x hext_x hrel_x hmod hgir) fun v pt' fr' P => ?_
      exact SimE.ret ⟨v, rfl, trivial, P⟩
    · intro flow pt' fr' hpost
      rcases hpost with ⟨v, hflow, _, P⟩ | hreturned
      · exact Or.inl ⟨v, hflow, (fun h => by cases h), by simpa [blockCells, Core.Block.value] using P⟩
      · exact Or.inr hreturned
  | none =>
    cases want
    · have h4' : (pure 0 : B ValueId) le ls_s = (rx, ls_x) := by
        simpa [lowerBlockValue] using h4
      refine (preparedBlockE_core hstmts hpre h1 h2 h3 h4' h5 hls' hr hpp hext hrel hprer hmod hgir
        (AdvB.pure _) (U := fun v => v = .unit) (cells := fun _ _ => []) ?_).mono ?_
      · intro env' pt_x fr_x hpp_x hext_x hrel_x
        have hx : ls_x = ls_s := by rw [pure_run] at h4'; exact (Prod.mk.inj h4').2.symm
        subst hx
        exact SimE.ret ⟨.unit, rfl, rfl, Post.init hrel_x hpp_x⟩
      · intro flow pt' fr' hpost
        rcases hpost with ⟨v, hflow, hunit, P⟩ | hreturned
        · exact Or.inl ⟨v, hflow, fun _ => hunit, by simpa [blockCells, Core.Block.value] using P⟩
        · exact Or.inr hreturned
    · have h4' : emitDef .constUnit le ls_s = (rx, ls_x) := by
        simpa [lowerBlockValue] using h4
      refine (preparedBlockE_core hstmts hpre h1 h2 h3 h4' h5 hls' hr hpp hext hrel hprer hmod hgir
        (advB_emitDef _) (U := fun v => v = .unit) (cells := fun rx v => [(rx, .val v)]) ?_).mono ?_
      · intro env' pt_x fr_x hpp_x hext_x hrel_x
        have P := Post.init hrel_x hpp_x
        show SimE cx pt_x fr_x ((pure () : M Unit) >>= fun _ => pure (Flow.normal Val.unit)) _
        refine SimE.bind (SimE.of_simG (leaf_def P h4' hext_x (by simp) (fun _ => RVal.val Val.unit)
          (c := (pure () : M Unit)) (by simp [execPure]))) fun _ pt' fr' P' => ?_
        exact SimE.ret ⟨.unit, rfl, rfl, P'⟩
      · intro flow pt' fr' hpost
        rcases hpost with ⟨v, hflow, hunit, P⟩ | hreturned
        · exact Or.inl ⟨v, hflow, fun _ => hunit, by simpa [blockCells, Core.Block.value] using P⟩
        · exact Or.inr hreturned

theorem blockESimulation_succ (n : Nat) (cfg : Cfg) (lc : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val))
    (want : Bool) (scope : ScopeId) (stmts : List Stmt) (value : Option Expr)
    (hstmts : StatementsESimulation n cfg lc stmts)
    (hvalue : match value with | none => True | some expr => ExprEClaim n cfg expr) :
    BlockESimulation (n + 1) cfg lc pre pre' want (.mk scope stmts value) :=
  blockEFlow_sim n cfg lc pre pre' want scope stmts value hstmts hvalue

end Goose.Lower
