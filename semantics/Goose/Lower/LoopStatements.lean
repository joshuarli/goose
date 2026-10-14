import Goose.Lower.LoopPrepare

namespace Goose.Lower

open Goose.Core Goose.GIR

def StatementLoopPost (cfg : Cfg) (env : Env) (cx : FnCtx) (ls : LS) (fr : GIR.Frame)
    (ls' : LS) (loop : Option LoopCtx) (flow : Flow) (pt' : Pt) (fr' : GIR.Frame) : Prop :=
  (flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) ∨
  ReturnedAt cx flow pt' fr' ∨
  (∃ context, loop = some context ∧
    ((flow = .brk ∧ ExitedAt context fr ls.vals.size
      (env.scopes.drop (env.scopes.length - context.depth)) pt' fr') ∨
    (flow = .cont ∧ ContinuedAt context fr ls.vals.size
      (env.scopes.drop (env.scopes.length - context.depth)) pt' fr')))

def LoopCounterAt (loop : Option LoopCtx) (ls : LS) (fr : GIR.Frame) : Prop :=
  match loop with
  | none => True
  | some context => match context.cont with
    | .jump _ => True
    | .next _ _ counter => counter < ls.vals.size ∧
        ∃ runtimeTy current, fr.vals[counter]? = some (.val (.int runtimeTy current))

def StatementLoopSimulation (n : Nat) (cfg : Cfg) (loop : Option LoopCtx) (stmt : Stmt) : Prop :=
  ∀ (le : LEnv) (ls ls' : LS) (u : Unit) (pt : Pt)
    (env : Env) (cx : FnCtx) (fr : GIR.Frame),
    lowerStmt loop stmt le ls = (u, ls') → ls.pp = some pt → ExtT ls' cx.fn.blocks →
    Rel cfg env cx fr ls → le.mod = cfg.mod → cx.cfg.mod = lower cfg.mod →
    LoopDepthFits env loop →
    (match loop with | none => True | some context => LoopTargets cx.fn context) →
    LoopCounterAt loop ls fr →
    SimE cx pt fr (execStmt n cfg env stmt >>= prepareLoopFlow env loop)
      (StatementLoopPost cfg env cx ls fr ls' loop)

theorem StatementESimulation.toLoop {n : Nat} {cfg : Cfg} {loop : Option LoopCtx} {stmt : Stmt}
    (hstmt : StatementESimulation n cfg loop stmt) : StatementLoopSimulation n cfg loop stmt := by
  intro le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir hdepth htargets hcounter
  have hsource :
      ((execStmt n cfg env stmt >>= prepareReturn env) >>= fun flow =>
        match loop with
        | none => pure flow
        | some context => prepareLoopExit env context.depth flow) =
      (execStmt n cfg env stmt >>= prepareLoopFlow env loop) := by
    rw [bind_assoc]
    rfl
  rw [← hsource]
  refine SimE.bind (hstmt le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir)
    fun flow pt' fr' hpost => ?_
  rcases hpost with ⟨rfl, P⟩ | ⟨value, org, rfl, hsite⟩
  · cases loop <;> exact SimE.ret (Or.inl ⟨rfl, P⟩)
  · cases loop <;> exact SimE.ret (Or.inr (Or.inl ⟨value, org, rfl, hsite⟩))

theorem statementLoopSimulation_zero (cfg : Cfg) (loop : Option LoopCtx) (stmt : Stmt) :
    StatementLoopSimulation 0 cfg loop stmt := by
  intro le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir hdepth htargets hcounter
  simp only [execStmt]
  exact SimE.of_simG SimG.of_timeout_bind

theorem StatementLoopPost.prefix {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls middle ls' : LS} {fr frMiddle fr' : GIR.Frame} {loop : Option LoopCtx}
    {ptMiddle pt' : Pt} {flow : Flow}
    (hrel : Rel cfg env cx fr ls) (P : Post cfg env cx ls fr middle frMiddle ptMiddle [])
    (hcounter : LoopCounterAt loop ls fr)
    (h : StatementLoopPost cfg env cx middle frMiddle ls' loop flow pt' fr') :
    StatementLoopPost cfg env cx ls fr ls' loop flow pt' fr' := by
  have hact : frMiddle.act = fr.act := P.rel.act.trans hrel.act.symm
  have hdepth : frMiddle.depth = fr.depth := P.rel.depth.trans hrel.depth.symm
  rcases h with ⟨hflow, Q⟩ | hreturned | ⟨context, hloop, htransfer⟩
  · exact Or.inl ⟨hflow, (P.comp Q).sub (by simp)⟩
  · exact Or.inr (Or.inl hreturned)
  · refine Or.inr (Or.inr ⟨context, hloop, ?_⟩)
    rcases htransfer with ⟨hflow, hpoint, hframe⟩ | ⟨hflow, hcontinue⟩
    · exact Or.inl ⟨hflow, hpoint,
        ⟨P.same.trans (hframe.values.mono P.mono) (Nat.le_refl _),
          hframe.activation.trans hact, hframe.scopesEqual, hframe.depth.trans hdepth⟩⟩
    · refine Or.inr ⟨hflow, ?_⟩
      cases hkind : context.cont with
      | jump header =>
        rw [ContinuedAt, hkind] at hcontinue ⊢
        obtain ⟨hpoint, hframe⟩ := hcontinue
        exact ⟨hpoint, ⟨P.same.trans (hframe.values.mono P.mono) (Nat.le_refl _),
          hframe.activation.trans hact, hframe.scopesEqual, hframe.depth.trans hdepth⟩⟩
      | next header hint counter =>
        rw [ContinuedAt, hkind] at hcontinue ⊢
        obtain ⟨runtimeTy, current, hcell, hnext⟩ := hcontinue
        have hbound : counter < ls.vals.size := by
          rw [hloop] at hcounter
          simp only [LoopCounterAt, hkind] at hcounter
          exact hcounter.1
        refine ⟨runtimeTy, current, ?_, hnext.prefix P.same (Nat.le_of_lt hbound) hact hdepth⟩
        rw [← P.same counter hbound] 
        exact hcell

theorem LoopCounterAt.afterPost {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls ls' : LS} {fr fr' : GIR.Frame} {loop : Option LoopCtx} {pt' : Pt}
    (h : LoopCounterAt loop ls fr) (P : Post cfg env cx ls fr ls' fr' pt' []) :
    LoopCounterAt loop ls' fr' := by
  cases loop with
  | none => trivial
  | some context =>
    cases hkind : context.cont with
    | jump header => simp [LoopCounterAt, hkind]
    | next header hint counter =>
      simp only [LoopCounterAt, hkind] at h ⊢
      obtain ⟨hbound, runtimeTy, current, hcell⟩ := h
      exact ⟨Nat.lt_of_lt_of_le hbound P.mono, runtimeTy, current,
        (P.same counter hbound).trans hcell⟩

def StatementsLoopSimulation (n : Nat) (cfg : Cfg) (loop : Option LoopCtx) (stmts : List Stmt) : Prop :=
  ∀ (le : LEnv) (ls ls' : LS) (u : Unit) (pt : Pt)
    (env : Env) (cx : FnCtx) (fr : GIR.Frame),
    lowerStmts loop stmts le ls = (u, ls') → ls.pp = some pt → ExtT ls' cx.fn.blocks →
    Rel cfg env cx fr ls → le.mod = cfg.mod → cx.cfg.mod = lower cfg.mod →
    LoopDepthFits env loop →
    (match loop with | none => True | some context => LoopTargets cx.fn context) →
    LoopCounterAt loop ls fr →
    SimE cx pt fr (execStmts n cfg env stmts >>= prepareLoopFlow env loop)
      (StatementLoopPost cfg env cx ls fr ls' loop)

theorem statementsLoopSimulation_zero (cfg : Cfg) (loop : Option LoopCtx) (stmts : List Stmt) :
    StatementsLoopSimulation 0 cfg loop stmts := by
  intro le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir hdepth htargets hcounter
  simp only [execStmts]
  exact SimE.of_simG SimG.of_timeout_bind

theorem statementsLoop_nil (n : Nat) (cfg : Cfg) (loop : Option LoopCtx) :
    StatementsLoopSimulation (n + 1) cfg loop [] := by
  intro le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir hdepth htargets hcounter
  simp only [lowerStmts, pure_run] at hlow
  obtain ⟨_, rfl⟩ := Prod.mk.inj hlow
  simp only [execStmts, pure_bind, prepareLoopFlow, prepareReturn]
  cases loop <;> exact SimE.ret (Or.inl ⟨rfl, Post.init hrel hpp⟩)

theorem statementsLoop_cons (n : Nat) (cfg : Cfg) (loop : Option LoopCtx)
    (stmt : Stmt) (rest : List Stmt)
    (hstmt : StatementLoopSimulation n cfg loop stmt)
    (hrest : StatementsLoopSimulation n cfg loop rest) :
    StatementsLoopSimulation (n + 1) cfg loop (stmt :: rest) := by
  intro le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir hdepth htargets hcounter
  obtain ⟨blk, hc, _, _⟩ := LS.pp_some hpp
  simp only [lowerStmts, bind_eq] at hlow
  obtain ⟨live, ls0, hlive, hlow⟩ := hlow
  rw [isLive_run hc] at hlive
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlive
  simp only [ite_true, bind_eq] at hlow
  obtain ⟨u1, ls1, hs, hr⟩ := hlow
  have hext1 := hext.of_adv (advB_lowerStmts loop rest _ _ _ _ hr)
  rw [prepareLoopFlow_execStmts]
  refine SimE.bind (hstmt le ls ls1 u1 pt env cx fr hs hpp hext1 hrel hmod hgir
    hdepth htargets hcounter) fun flow pt1 fr1 hpost => ?_
  rcases hpost with ⟨rfl, P⟩ | ⟨value, org, rfl, hsite⟩ | ⟨context, hloop, htransfer⟩
  · exact (hrest le ls1 ls' u pt1 env cx fr1 hr P.pp hext P.rel hmod hgir hdepth
      htargets (hcounter.afterPost P)).mono fun flow' pt' fr' hpost' =>
        hpost'.prefix hrel P hcounter
  · exact SimE.ret (Or.inr (Or.inl ⟨value, org, rfl, hsite⟩))
  · rcases htransfer with ⟨rfl, hexited⟩ | ⟨rfl, hcontinued⟩
    · exact SimE.ret (Or.inr (Or.inr ⟨context, hloop, Or.inl ⟨rfl, hexited⟩⟩))
    · exact SimE.ret (Or.inr (Or.inr ⟨context, hloop, Or.inr ⟨rfl, hcontinued⟩⟩))

theorem prepareLoopFlow_execStmt_break (n : Nat) (cfg : Cfg) (env : Env) (loop : LoopCtx)
    (org : OriginId) :
    (execStmt n cfg env (.brk org) >>= prepareLoopFlow env (some loop)) =
      (execStmt n cfg env (.brk org) >>= prepareLoopExit env loop.depth) := by
  cases n with
  | zero => simp only [execStmt]; rfl
  | succ n => simp only [execStmt, pure_bind, prepareLoopFlow, prepareReturn]

theorem prepareLoopFlow_execStmt_continue (n : Nat) (cfg : Cfg) (env : Env) (loop : LoopCtx)
    (org : OriginId) :
    (execStmt n cfg env (.cont org) >>= prepareLoopFlow env (some loop)) =
      (execStmt n cfg env (.cont org) >>= prepareLoopExit env loop.depth) := by
  cases n with
  | zero => simp only [execStmt]; rfl
  | succ n => simp only [execStmt, pure_bind, prepareLoopFlow, prepareReturn]

theorem stmt_breakLoop_sim (n : Nat) (cfg : Cfg) (loop : LoopCtx) (org : OriginId)
    (le : LEnv) (ls ls' : LS) (u : Unit) (pt : Pt) (env : Env) (cx : FnCtx) (fr : GIR.Frame)
    (hlow : lowerStmt (some loop) (.brk org) le ls = (u, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (htarget : ∃ block, cx.fn.blocks[loop.breakTo]? = some block ∧ block.params = []) :
    SimE cx pt fr (execStmt n cfg env (.brk org) >>= prepareLoopFlow env (some loop))
      (StatementLoopPost cfg env cx ls fr ls' (some loop)) := by
  rw [prepareLoopFlow_execStmt_break]
  exact (SimE.of_simG (stmt_brk_prepared_sim n loop org le ls ls' u pt cfg env cx fr
    hlow hpp hext hrel htarget)).mono fun flow pt' fr' ⟨hflow, hpost⟩ =>
      Or.inr (Or.inr ⟨loop, rfl, Or.inl ⟨hflow, hpost.exitedAt _⟩⟩)

theorem stmt_continueJumpLoop_sim (n : Nat) (cfg : Cfg) (loop : LoopCtx)
    (header : BlockId) (org : OriginId) (hkind : loop.cont = .jump header)
    (le : LEnv) (ls ls' : LS) (u : Unit) (pt : Pt) (env : Env) (cx : FnCtx) (fr : GIR.Frame)
    (hlow : lowerStmt (some loop) (.cont org) le ls = (u, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (htarget : ∃ block, cx.fn.blocks[header]? = some block ∧ block.params = []) :
    SimE cx pt fr (execStmt n cfg env (.cont org) >>= prepareLoopFlow env (some loop))
      (StatementLoopPost cfg env cx ls fr ls' (some loop)) := by
  rw [prepareLoopFlow_execStmt_continue]
  exact (SimE.of_simG (stmt_cont_jump_prepared_sim n loop header org hkind le ls ls' u pt
    cfg env cx fr hlow hpp hext hrel htarget)).mono fun flow pt' fr' ⟨hflow, hpost⟩ =>
      Or.inr (Or.inr ⟨loop, rfl, Or.inr ⟨hflow, hpost.continuedAt hkind _⟩⟩)

theorem stmt_continueNextLoop_sim (n : Nat) (cfg : Cfg) (loop : LoopCtx)
    (header : BlockId) (hint runtimeTy : IntTy) (counter : ValueId) (current : Int) (org : OriginId)
    (hkind : loop.cont = .next header hint counter)
    (le : LEnv) (ls ls' : LS) (u : Unit) (pt : Pt) (env : Env) (cx : FnCtx) (fr : GIR.Frame)
    (hcounter : fr.vals[counter]? = some (.val (.int runtimeTy current)))
    (hbound : counter < ls.vals.size)
    (hlow : lowerStmt (some loop) (.cont org) le ls = (u, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (htarget : ∃ block, cx.fn.blocks[header]? = some block ∧
      block.params = [(counter, .data (.int hint))]) :
    SimE cx pt fr (execStmt n cfg env (.cont org) >>= prepareLoopFlow env (some loop))
      (StatementLoopPost cfg env cx ls fr ls' (some loop)) := by
  rw [prepareLoopFlow_execStmt_continue]
  exact (SimE.of_simG (stmt_cont_next_prepared_sim n loop header hint runtimeTy counter current org
    hkind le ls ls' u pt cfg env cx fr hcounter hbound hlow hpp hext hrel htarget)).mono
    fun flow pt' fr' ⟨hflow, hpost⟩ =>
      Or.inr (Or.inr ⟨loop, rfl, Or.inr ⟨hflow, hpost.continuedAt hkind hcounter⟩⟩)

theorem statementLoopSimulation_break (n : Nat) (cfg : Cfg) (loop : LoopCtx) (org : OriginId) :
    StatementLoopSimulation n cfg (some loop) (.brk org) := by
  intro le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir hdepth htargets hcounter
  exact stmt_breakLoop_sim n cfg loop org le ls ls' u pt env cx fr
    hlow hpp hext hrel htargets.breakBlock

theorem statementLoopSimulation_continue (n : Nat) (cfg : Cfg) (loop : LoopCtx) (org : OriginId) :
    StatementLoopSimulation n cfg (some loop) (.cont org) := by
  intro le ls ls' u pt env cx fr hlow hpp hext hrel hmod hgir hdepth htargets hcounter
  cases hkind : loop.cont with
  | jump header =>
    exact stmt_continueJumpLoop_sim n cfg loop header org hkind le ls ls' u pt env cx fr
      hlow hpp hext hrel (by simpa only [hkind] using htargets.continueBlock)
  | next header hint counter =>
    simp only [LoopCounterAt, hkind] at hcounter
    obtain ⟨hbound, runtimeTy, current, hcell⟩ := hcounter
    exact stmt_continueNextLoop_sim n cfg loop header hint runtimeTy counter current org hkind
      le ls ls' u pt env cx fr hcell hbound hlow hpp hext hrel
      (by simpa only [hkind] using htargets.continueBlock)

end Goose.Lower
