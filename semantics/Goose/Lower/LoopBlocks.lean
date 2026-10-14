import Goose.Lower.LoopPrepare

namespace Goose.Lower

open Goose.Core Goose.GIR

def BlockLoopPost (cfg : Cfg) (env : Env) (cx : FnCtx) (ls : LS) (fr : GIR.Frame)
    (ls' : LS) (loop : Option LoopCtx) (block : Core.Block) (want : Bool) (result : ValueId)
    (flow : Flow) (pt' : Pt) (fr' : GIR.Frame) : Prop :=
  (∃ value, flow = .normal value ∧ (block.value = none → value = .unit) ∧
    Post cfg env cx ls fr ls' fr' pt' (blockCells block want result value)) ∨
  ReturnedAt cx flow pt' fr' ∨
  (∃ context, loop = some context ∧
    ((flow = .brk ∧ ExitedAt context fr ls.vals.size
      (env.scopes.drop (env.scopes.length - context.depth)) pt' fr') ∨
    (flow = .cont ∧ ContinuedAt context fr ls.vals.size
      (env.scopes.drop (env.scopes.length - context.depth)) pt' fr')))

theorem loopScopeSuffix_entered (env : Env) (scope : ScopeId) (scopeInstance : ScopeInst)
    (depth : Nat) (hdepth : depth ≤ env.scopes.length) :
    (((scope, scopeInstance) :: env.scopes).drop
      (((scope, scopeInstance) :: env.scopes).length - depth)) =
    env.scopes.drop (env.scopes.length - depth) := by
  have hlength : ((scope, scopeInstance) :: env.scopes).length - depth =
      (env.scopes.length - depth) + 1 := by simp only [List.length_cons]; omega
  rw [hlength, List.drop_succ_cons]

theorem StatementLoopPost.rescope {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls inner out : LS} {before entered after : GIR.Frame} {loop : Option LoopCtx}
    {scope : ScopeId} {scopeInstance : ScopeInst} {flow : Flow} {pt : Pt}
    (hdepth : LoopDepthFits env loop) (hrel : Rel cfg env cx before ls)
    (hentered : Rel cfg { env with scopes := (scope, scopeInstance) :: env.scopes } cx entered inner)
    (hvalues : entered.vals = before.vals) (hsize : inner.vals.size = ls.vals.size)
    (h : StatementLoopPost cfg { env with scopes := (scope, scopeInstance) :: env.scopes }
      cx inner entered out loop flow pt after)
    (habnormal : ∀ value, flow ≠ .normal value) :
    ReturnedAt cx flow pt after ∨
      (∃ context, loop = some context ∧
        ((flow = .brk ∧ ExitedAt context before ls.vals.size
          (env.scopes.drop (env.scopes.length - context.depth)) pt after) ∨
        (flow = .cont ∧ ContinuedAt context before ls.vals.size
          (env.scopes.drop (env.scopes.length - context.depth)) pt after))) := by
  have hact : entered.act = before.act := hentered.act.trans hrel.act.symm
  have hframeDepth : entered.depth = before.depth := hentered.depth.trans hrel.depth.symm
  have hprefix : Same ls.vals.size before entered := fun id _ => by rw [hvalues]
  rcases h with ⟨hflow, P⟩ | hret | ⟨context, hloop, htransfer⟩
  · exact (habnormal .unit hflow).elim
  · exact Or.inl hret
  · have hfit : context.depth ≤ env.scopes.length := by
      rw [hloop] at hdepth
      exact hdepth
    have hsuffix := loopScopeSuffix_entered env scope scopeInstance context.depth hfit
    change ((scope, scopeInstance) :: env.scopes).drop
      (((scope, scopeInstance) :: env.scopes).length - context.depth) = _ at hsuffix
    refine Or.inr ⟨context, hloop, ?_⟩
    rcases htransfer with ⟨hflow, hpoint, hframe⟩ | ⟨hflow, hcontinue⟩
    · rw [hsuffix, hsize] at hframe
      exact Or.inl ⟨hflow, hpoint, hframe.prefix hprefix hact hframeDepth⟩
    · refine Or.inr ⟨hflow, ?_⟩
      cases hkind : context.cont with
      | jump header =>
        rw [ContinuedAt, hkind] at hcontinue ⊢
        obtain ⟨hpoint, hframe⟩ := hcontinue
        rw [hsuffix, hsize] at hframe
        exact ⟨hpoint, hframe.prefix hprefix hact hframeDepth⟩
      | next header hint counter =>
        rw [ContinuedAt, hkind] at hcontinue ⊢
        obtain ⟨runtimeTy, current, hcell, hnext⟩ := hcontinue
        rw [hsuffix] at hnext
        refine ⟨runtimeTy, current, ?_, ?_⟩
        · rw [← hvalues]
          exact hcell
        · exact ⟨hnext.point, fun id hid => by rw [← hvalues]; exact hnext.values id hid,
            hnext.counterValue, hnext.activation.trans hact, hnext.scopesEqual,
            hnext.depth.trans hframeDepth⟩

theorem preparedLoopBlock_core_at {n : Nat} {cfg : Cfg} {loop : Option LoopCtx}
    {scope : ScopeId} {stmts : List Stmt} {value : Option Expr} {want : Bool}
    {pre : List (SlotId × ValueId × OriginId)} {pre' : List (VarId × Val)}
    {env : Env} {state : St} {le : LEnv}
    {ls ls1 ls_p ls_s ls_x ls_l ls' : LS} {u0 u : Unit} {rx r : ValueId}
    {pt : Pt} {cx : FnCtx} {fr : GIR.Frame}
    (hpre : ∀ p ∈ pre, ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = scope)
    (h1 : emitEffect (.enter scope) le ls = ((), ls1))
    (h2 : initSlots pre le { ls1 with stack := scope :: ls1.stack } = (u0, ls_p))
    (h3 : lowerStmts loop stmts le ls_p = (u, ls_s))
    (h4 : lowerBlockValue want value le ls_s = (rx, ls_x))
    (h5 : emitEffect (.leave scope) le ls_x = ((), ls_l))
    (hls' : ls' = { ls_l with stack := ls_l.stack.drop 1 }) (hr : r = rx)
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks)
    (hrel : Rel cfg env cx fr ls) (hprer : PreRel fr pre pre')
    (hdepth : LoopDepthFits env loop)
    (hS : ∀ (si : ScopeInst) (entered initialized : St),
      freshScope state = .ok si entered → bindAll env.act si pre' entered = .ok () initialized →
      ∀ (pt_s : Pt) (fr_s : GIR.Frame), ls_p.pp = some pt_s →
      ExtT ls_s cx.fn.blocks →
      Rel cfg { env with scopes := (scope, si) :: env.scopes } cx fr_s ls_p →
      SimEAt cx pt_s fr_s
        (execStmts n cfg { env with scopes := (scope, si) :: env.scopes } stmts >>=
          prepareLoopFlow { env with scopes := (scope, si) :: env.scopes } loop)
        (StatementLoopPost cfg { env with scopes := (scope, si) :: env.scopes }
          cx ls_p fr_s ls_s loop) initialized)
    (hX : ∀ (si : ScopeInst) (entered initialized after : St),
      freshScope state = .ok si entered → bindAll env.act si pre' entered = .ok () initialized →
      (execStmts n cfg { env with scopes := (scope, si) :: env.scopes } stmts >>=
        prepareLoopFlow { env with scopes := (scope, si) :: env.scopes } loop)
        initialized = .ok (.normal .unit) after →
      ∀ (pt_x : Pt) (fr_x : GIR.Frame), ls_s.pp = some pt_x →
      ExtT ls_x cx.fn.blocks →
      Rel cfg { env with scopes := (scope, si) :: env.scopes } cx fr_x ls_s →
      SimEAt cx pt_x fr_x
        (valueFlow n cfg value { env with scopes := (scope, si) :: env.scopes } (.normal .unit))
        (fun flow pt' fr' => ∃ v, flow = .normal v ∧ (value = none → v = .unit) ∧
          Post cfg { env with scopes := (scope, si) :: env.scopes } cx ls_s fr_x ls_x fr' pt'
            (blockCells (.mk scope stmts value) want rx v)) after) :
    SimEAt cx pt fr (preparedCoreLoopBlock n cfg env loop scope stmts value pre')
      (BlockLoopPost cfg env cx ls fr ls' loop (.mk scope stmts value) want r) state := by
  subst hr
  have hext_l : ExtT ls_l cx.fn.blocks := by rw [hls'] at hext; exact hext
  have hext_x := hext_l.of_adv (adv_emitEffect h5)
  have hext_s := hext_x.of_adv (advB_lowerBlockValue want value _ _ _ _ h4)
  have hext_p := hext_s.of_adv (advB_lowerStmts loop stmts _ _ _ _ h3)
  have hext_i := hext_p.of_adv (advB_initSlots pre _ _ _ _ h2)
  have hext_1 : ExtT ls1 cx.fn.blocks := hext_i
  unfold preparedCoreLoopBlock
  refine SimEAt.bind (SimEAt.of_simG (block_enter hpp h1 hext_1 hrel) state)
    fun si entered pt1 fr1 hfresh ⟨hpp1, hv1, hfr1, hrel1⟩ => ?_
  have hsc : ({ env with scopes := (scope, si) :: env.scopes } : Env).scopes.head? =
      some (scope, si) := rfl
  refine SimEAt.bind (SimEAt.of_simG (initSlots_sim hsc pre pre' hpre h2 hpp1 hext_p hrel1
    (PreRel.ext hfr1 hprer)) entered)
    fun _ initialized pt1' fr1' hbind ⟨hpp1', hfr1', hst1', hvl1'⟩ => ?_
  subst fr1'
  have hrel1' : Rel cfg { env with scopes := (scope, si) :: env.scopes } cx fr1 ls_p :=
    hrel1.stack_eq hst1'
  refine SimEAt.bind (hS si entered initialized hfresh hbind pt1' fr1 hpp1' hext_s hrel1')
    fun flow after pt2 fr2 hactual hpost => ?_
  rcases hpost with ⟨rfl, P2⟩ | hreturned | ⟨context, hloop, htransfer⟩
  · refine SimEAt.bind (hX si entered initialized after hfresh hbind hactual pt2 fr2
      P2.pp hext_x P2.rel) fun flow' afterValue pt3 fr3 hvalue ⟨v, hflow', hunit, P3⟩ => ?_
    subst flow'
    refine SimEAt.bind (SimEAt.of_simG (block_leave P3.pp h5 hext_l P3.rel) afterValue)
      fun _ _ pt4 fr4 _ ⟨hpp4, hv4, hfr4, hrel4⟩ => ?_
    refine SimEAt.ret (Or.inl ⟨v, rfl, hunit, ?_⟩)
    have P23 := P2.comp P3
    refine Post.rescope (P23.sub (cells' := blockCells (.mk scope stmts value) want r v)
      (by simp)) (hv0 := ?_) (hfr0 := hfr1) ?_ ?_ hfr4 ?_
    · rw [hvl1']; exact hv1
    · rw [hls']; exact hpp4
    · rw [hls']; exact hv4
    · rw [hls']; exact hrel4
  · obtain ⟨returned, org, rfl, hsite⟩ := hreturned
    exact SimEAt.ret (Or.inr (Or.inl ⟨returned, org, rfl, hsite⟩))
  · have hrescope := StatementLoopPost.rescope (out := ls_s) (after := fr2)
      (flow := flow) (pt := pt2) hdepth hrel hrel1' hfr1
      (by rw [hvl1']; exact hv1)
    rcases htransfer with ⟨rfl, hexit⟩ | ⟨rfl, hcontinue⟩
    · have houter := hrescope (Or.inr (Or.inr ⟨context, hloop, Or.inl ⟨rfl, hexit⟩⟩))
        (by intro v h; cases h)
      rw [hloop]
      rw [hloop] at houter
      exact SimEAt.ret (Or.inr houter)
    · have houter := hrescope (Or.inr (Or.inr ⟨context, hloop, Or.inr ⟨rfl, hcontinue⟩⟩))
        (by intro v h; cases h)
      rw [hloop]
      rw [hloop] at houter
      exact SimEAt.ret (Or.inr houter)

end Goose.Lower
