import Goose.Lower.Return

namespace Goose.Lower

open Goose.Core Goose.GIR

def stmtReturnOk : Stmt → Bool
  | .ret none _ => true
  | .ret (some e) _ => exprOk e
  | stmt => stmtOk stmt

def stmtsReturnOk : List Stmt → Bool
  | [] => true
  | stmt :: rest => stmtReturnOk stmt && stmtsReturnOk rest

def ReturnedAt (cx : FnCtx) (flow : Flow) (pt : Pt) (fr : GIR.Frame) : Prop :=
  ∃ value org, flow = .ret value ∧ ReturnSite cx pt fr value org

def StmtFlowPost (cfg : Cfg) (env : Env) (cx : FnCtx) (ls : LS) (fr : GIR.Frame)
    (ls' : LS) (flow : Flow) (pt' : Pt) (fr' : GIR.Frame) : Prop :=
  (flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) ∨ ReturnedAt cx flow pt' fr'

def StmtReturnClaim (n : Nat) (lc : Option LoopCtx) (stmt : Stmt) : Prop :=
  stmtReturnOk stmt = true → ∀ (le : LEnv) (ls ls' : LS) (u : Unit) (pt : Pt)
    (cfg : Cfg) (env : Env) (cx : FnCtx) (fr : GIR.Frame),
    lowerStmt lc stmt le ls = (u, ls') → ls.pp = some pt → ExtT ls' cx.fn.blocks →
    Rel cfg env cx fr ls →
    SimG cx pt fr (execStmt n cfg env stmt >>= prepareReturn env)
      (StmtFlowPost cfg env cx ls fr ls')

theorem stmtReturnClaim (n : Nat) (lc : Option LoopCtx) (stmt : Stmt) :
    StmtReturnClaim n lc stmt := by
  intro hok le ls ls' u pt cfg env cx fr hlow hpp hext hrel
  cases stmt with
  | ret expr org =>
    exact (stmt_ret_prepared_sim n lc expr org (by cases expr <;> exact hok) le ls ls' u pt cfg env cx fr
      hlow hpp hext hrel).mono fun flow pt' fr' ⟨value, hflow, hsite⟩ =>
        Or.inr ⟨value, org, hflow, hsite⟩
  | _ =>
    refine SimG.bind ((claims n).stmt lc _ hok le ls u ls' pt cfg env cx fr
      hlow hpp hext hrel) fun flow pt' fr' ⟨hflow, hpost⟩ => ?_
    subst flow
    exact SimG.ret (Or.inl ⟨rfl, hpost⟩)

def returnStmtsTail (n : Nat) (cfg : Cfg) (env : Env) (rest : List Stmt) : Flow → M Flow
  | .normal _ => execStmts n cfg env rest >>= prepareReturn env
  | flow => pure flow

theorem prepareReturn_execStmts (n : Nat) (cfg : Cfg) (env : Env)
    (stmt : Stmt) (rest : List Stmt) :
    (execStmts (n + 1) cfg env (stmt :: rest) >>= prepareReturn env) =
      ((execStmt n cfg env stmt >>= prepareReturn env) >>= returnStmtsTail n cfg env rest) := by
  simp only [execStmts, bind_assoc]
  congr 1
  funext flow
  cases flow <;> simp [prepareReturn, returnStmtsTail, bind_assoc, pure_bind]

def StmtsReturnClaim (n : Nat) (lc : Option LoopCtx) (stmts : List Stmt) : Prop :=
  stmtsReturnOk stmts = true → ∀ (le : LEnv) (ls ls' : LS) (u : Unit) (pt : Pt)
    (cfg : Cfg) (env : Env) (cx : FnCtx) (fr : GIR.Frame),
    lowerStmts lc stmts le ls = (u, ls') → ls.pp = some pt → ExtT ls' cx.fn.blocks →
    Rel cfg env cx fr ls →
    SimG cx pt fr (execStmts n cfg env stmts >>= prepareReturn env)
      (StmtFlowPost cfg env cx ls fr ls')

theorem stmtsReturnClaim (n : Nat) (lc : Option LoopCtx) (stmts : List Stmt) :
    StmtsReturnClaim n lc stmts := by
  induction n generalizing stmts with
  | zero =>
    intro hok le ls ls' u pt cfg env cx fr hlow hpp hext hrel
    simp only [execStmts]
    exact SimG.of_timeout_bind
  | succ n ih =>
    cases stmts with
    | nil =>
      intro hok le ls ls' u pt cfg env cx fr hlow hpp hext hrel
      simp only [lowerStmts, pure_run] at hlow
      obtain ⟨_, rfl⟩ := Prod.mk.inj hlow
      simp only [execStmts, pure_bind, prepareReturn]
      exact SimG.ret (Or.inl ⟨rfl, Post.init hrel hpp⟩)
    | cons stmt rest =>
      intro hok le ls ls' u pt cfg env cx fr hlow hpp hext hrel
      simp only [stmtsReturnOk, Bool.and_eq_true] at hok
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
      refine SimG.bind (stmtReturnClaim n lc stmt hokStmt le ls ls1 u1 pt cfg env cx fr
        hstmt hpp hext1 hrel) fun flow pt1 fr1 hpost => ?_
      rcases hpost with ⟨rfl, hnormal⟩ | ⟨value, org, rfl, hreturned⟩
      · exact (ih rest hokRest le ls1 ls' u pt1 cfg env cx fr1 hrest hnormal.pp hext
          hnormal.rel).mono fun flow' pt' fr' hpost' => by
          rcases hpost' with ⟨hflow, hpost'⟩ | hreturned'
          · exact Or.inl ⟨hflow, (hnormal.comp hpost').sub (by simp)⟩
          · exact Or.inr hreturned'
      · exact SimG.ret (Or.inr ⟨value, org, rfl, hreturned⟩)

def blockReturnOk : Core.Block → Bool
  | .mk _ stmts value => stmtsReturnOk stmts &&
      (match value with | none => true | some expr => exprOk expr)

def BlockFlowPost (cfg : Cfg) (env : Env) (cx : FnCtx) (ls : LS) (fr : GIR.Frame)
    (ls' : LS) (blk : Core.Block) (want : Bool) (r : ValueId)
    (flow : Flow) (pt' : Pt) (fr' : GIR.Frame) : Prop :=
  (∃ value, flow = .normal value ∧ (blk.value = none → value = .unit) ∧
    Post cfg env cx ls fr ls' fr' pt' (blockCells blk want r value)) ∨
    ReturnedAt cx flow pt' fr'

theorem preparedBlock_core {n : Nat} {lc : Option LoopCtx} {sc : ScopeId}
    {stmts : List Stmt} {value : Option Expr} {pre : List (SlotId × ValueId × OriginId)}
    {pre' : List (VarId × Val)} {env : Env} (hokS : stmtsReturnOk stmts = true)
    {U : Val → Prop} {X : B ValueId} {cells : ValueId → Val → List (ValueId × RVal)}
    {le : LEnv} {ls ls1 ls_p ls_s ls_x ls_l ls' : LS} {u0 u : Unit} {rx r : ValueId}
    {pt : Pt} {cfg : Cfg} {cx : FnCtx} {fr : GIR.Frame}
    (hpre : ∀ p ∈ pre, ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = sc)
    (h1 : emitEffect (.enter sc) le ls = ((), ls1))
    (h2 : initSlots pre le { ls1 with stack := sc :: ls1.stack } = (u0, ls_p))
    (h3 : lowerStmts lc stmts le ls_p = (u, ls_s))
    (h4 : X le ls_s = (rx, ls_x)) (h5 : emitEffect (.leave sc) le ls_x = ((), ls_l))
    (hls' : ls' = { ls_l with stack := ls_l.stack.drop 1 }) (hr : r = rx)
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hprer : PreRel fr pre pre') (hadvX : AdvB X)
    (hX : ∀ (env' : Env) (pt_x : Pt) (fr_x : GIR.Frame), ls_s.pp = some pt_x →
      ExtT ls_x cx.fn.blocks → Rel cfg env' cx fr_x ls_s →
      SimG cx pt_x fr_x (valueFlow n cfg value env' (.normal .unit))
        (fun flow pt' fr' => ∃ v, flow = .normal v ∧ U v ∧
          Post cfg env' cx ls_s fr_x ls_x fr' pt' (cells rx v))) :
    SimG cx pt fr (preparedCoreBlock n cfg env sc stmts value pre')
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
  refine SimG.bind (block_enter hpp h1 hext_1 hrel)
    fun si pt1 fr1 ⟨hpp1, hv1, hfr1, hrel1⟩ => ?_
  have hsc : ({ env with scopes := (sc, si) :: env.scopes } : Env).scopes.head? =
      some (sc, si) := rfl
  refine SimG.bind (initSlots_sim hsc pre pre' hpre h2 hpp1 hext_p hrel1
    (PreRel.ext hfr1 hprer)) fun _ pt1' fr1' ⟨hpp1', hfr1', hst1', hvl1'⟩ => ?_
  subst fr1'
  have hrel1' : Rel cfg { env with scopes := (sc, si) :: env.scopes } cx fr1 ls_p :=
    hrel1.stack_eq hst1'
  refine SimG.bind (stmtsReturnClaim n lc stmts hokS le _ ls_s u pt1' cfg _ cx fr1
    h3 hpp1' hext_s hrel1') fun flow pt2 fr2 hpost => ?_
  rcases hpost with ⟨rfl, P2⟩ | ⟨returned, org, rfl, hsite⟩
  · refine SimG.bind (hX _ pt2 fr2 P2.pp hext_x P2.rel)
      fun flow' pt3 fr3 ⟨v, hflow', hU, P3⟩ => ?_
    subst flow'
    refine SimG.bind (block_leave P3.pp h5 hext_l P3.rel)
      fun _ pt4 fr4 ⟨hpp4, hv4, hfr4, hrel4⟩ => ?_
    refine SimG.ret (Or.inl ⟨v, rfl, hU, ?_⟩)
    have P23 := P2.comp P3
    refine Post.rescope (P23.sub (cells' := cells r v) (by simp))
      (hv0 := ?_) (hfr0 := hfr1) ?_ ?_ hfr4 ?_
    · rw [hvl1']; exact hv1
    · rw [hls']; exact hpp4
    · rw [hls']; exact hv4
    · rw [hls']; exact hrel4
  · exact SimG.ret (Or.inr ⟨returned, org, rfl, hsite⟩)

def BlockReturnClaim (n : Nat) (lc : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val))
    (want : Bool) (blk : Core.Block) : Prop :=
  blockReturnOk blk = true → ∀ (cfg : Cfg) (env : Env),
    (∀ p ∈ pre, ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = blk.scope) →
    ∀ (le : LEnv) (ls ls' : LS) (r : ValueId) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerBlock lc pre want blk le ls = (r, ls') → ls.pp = some pt →
    ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls → PreRel fr pre pre' →
    SimG cx pt fr (execBlock n cfg env pre' blk >>= prepareReturn env)
      (BlockFlowPost cfg env cx ls fr ls' blk want r)

theorem blockReturnClaim (n : Nat) (lc : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val))
    (want : Bool) (blk : Core.Block) : BlockReturnClaim n lc pre pre' want blk := by
  cases n with
  | zero =>
    intro hok cfg env hpre le ls ls' r pt cx fr hlow hpp hext hrel hprer
    simp only [execBlock]
    exact SimG.of_timeout_bind
  | succ n =>
    obtain ⟨sc, stmts, value⟩ := blk
    intro hok cfg env hpre le ls ls' r pt cx fr hlow hpp hext hrel hprer
    simp only [blockReturnOk, Bool.and_eq_true] at hok
    obtain ⟨hokS, hokV⟩ := hok
    obtain ⟨ls1, ls_p, ls_s, ls_x, ls_l, u0, u, rx, h1, h2, h3, h4, h5, hls', hr⟩ :=
      prefixBlock_unfold hlow
    rw [prepareReturn_execBlock]
    cases value with
    | some expr =>
      simp only [lowerBlockValue] at h4
      refine (preparedBlock_core hokS hpre h1 h2 h3 h4 h5 hls' hr hpp hext hrel hprer
        (advB_lowerExpr expr) (U := fun _ => True) (cells := fun rx v => [(rx, .val v)]) ?_).mono ?_
      · intro env' pt_x fr_x hpp_x hext_x hrel_x
        simp only [valueFlow]
        refine SimG.bind ((claims n).expr expr hokV le ls_s rx ls_x pt_x cfg env' cx fr_x
          h4 hpp_x hext_x hrel_x) fun v pt' fr' P => ?_
        exact SimG.ret ⟨v, rfl, trivial, P⟩
      · intro flow pt' fr' hpost
        rcases hpost with ⟨v, hflow, _, P⟩ | hreturned
        · exact Or.inl ⟨v, hflow, (fun h => by cases h), by simpa [blockCells, Core.Block.value] using P⟩
        · exact Or.inr hreturned
    | none =>
      cases want
      · have h4' : (pure 0 : B ValueId) le ls_s = (rx, ls_x) := by
          simpa [lowerBlockValue] using h4
        refine (preparedBlock_core hokS hpre h1 h2 h3 h4' h5 hls' hr hpp hext hrel hprer
          (AdvB.pure _) (U := fun v => v = .unit) (cells := fun _ _ => []) ?_).mono ?_
        · intro env' pt_x fr_x hpp_x hext_x hrel_x
          have hx : ls_x = ls_s := by rw [pure_run] at h4'; exact (Prod.mk.inj h4').2.symm
          subst hx
          exact SimG.ret ⟨.unit, rfl, rfl, Post.init hrel_x hpp_x⟩
        · intro flow pt' fr' hpost
          rcases hpost with ⟨v, hflow, hunit, P⟩ | hreturned
          · exact Or.inl ⟨v, hflow, fun _ => hunit, by simpa [blockCells, Core.Block.value] using P⟩
          · exact Or.inr hreturned
      · have h4' : emitDef .constUnit le ls_s = (rx, ls_x) := by
          simpa [lowerBlockValue] using h4
        refine (preparedBlock_core hokS hpre h1 h2 h3 h4' h5 hls' hr hpp hext hrel hprer
          (advB_emitDef _) (U := fun v => v = .unit) (cells := fun rx v => [(rx, .val v)]) ?_).mono ?_
        · intro env' pt_x fr_x hpp_x hext_x hrel_x
          have P := Post.init hrel_x hpp_x
          show SimG cx pt_x fr_x ((pure () : M Unit) >>= fun _ => pure (Flow.normal Val.unit)) _
          refine SimG.bind (leaf_def P h4' hext_x (by simp) (fun _ => RVal.val Val.unit)
            (c := (pure () : M Unit)) (by simp [execPure])) fun _ pt' fr' P' => ?_
          exact SimG.ret ⟨.unit, rfl, rfl, P'⟩
        · intro flow pt' fr' hpost
          rcases hpost with ⟨v, hflow, hunit, P⟩ | hreturned
          · exact Or.inl ⟨v, hflow, fun _ => hunit, by simpa [blockCells, Core.Block.value] using P⟩
          · exact Or.inr hreturned

end Goose.Lower
