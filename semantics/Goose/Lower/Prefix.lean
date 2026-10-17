import Goose.Lower.Claims

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem prefixBlock_core {n : Nat} {lc : Option LoopCtx} (ihs : ∀ ss, StmtsClaim n lc ss) {sc : ScopeId}
    {stmts : List Stmt} {pre : List (SlotId × ValueId × OriginId)} {pre' : List (VarId × Val)}
    {env : Env} (hokS : stmtsOk stmts = true) {U : Val → Prop}
    {X : B ValueId} {vf : Env → Flow → M Flow} {cells : ValueId → Val → List (ValueId × RVal)}
    {le : LEnv} {ls ls1 ls_p ls_s ls_x ls_l ls' : LS} {u0 u : Unit} {rx r : ValueId} {pt : Pt} {cfg : Cfg}
    {cx : FnCtx} {fr : Frame}
    (hpre : ∀ p ∈ pre, ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = sc)
    (h1 : emitEffect (.enter sc) le ls = ((), ls1))
    (h2 : initSlots pre le { ls1 with stack := sc :: ls1.stack } = (u0, ls_p))
    (h3 : lowerStmts lc stmts le ls_p = (u, ls_s))
    (h4 : X le ls_s = (rx, ls_x)) (h5 : emitEffect (.leave sc) le ls_x = ((), ls_l))
    (hls' : ls' = { ls_l with stack := ls_l.stack.drop 1 }) (hr : r = rx)
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hprer : PreRel fr pre pre') (hadvX : AdvB X)
    (hX : ∀ (env' : Env) (pt_x : Pt) (fr_x : Frame), ls_s.pp = some pt_x →
      ExtT ls_x cx.fn.blocks → Rel cfg env' cx fr_x ls_s →
      SimG cx pt_x fr_x (vf env' (.normal .unit)) (fun flow pt' fr' => ∃ v, flow = .normal v ∧ U v ∧
        Post cfg env' cx ls_s fr_x ls_x fr' pt' (cells rx v))) :
    SimG cx pt fr (prefixCoreBlock n cfg env sc stmts pre' vf) (fun flow pt' fr' => ∃ v, flow = .normal v ∧ U v ∧
      Post cfg env cx ls fr ls' fr' pt' (cells r v)) := by
  subst hr
  have hext_l : ExtT ls_l cx.fn.blocks := by rw [hls'] at hext; exact hext
  have hext_x : ExtT ls_x cx.fn.blocks := hext_l.of_adv (adv_emitEffect h5)
  have hext_s : ExtT ls_s cx.fn.blocks := hext_x.of_adv (hadvX _ _ _ _ h4)
  have hext_p : ExtT ls_p cx.fn.blocks := hext_s.of_adv (advB_lowerStmts lc stmts _ _ _ _ h3)
  have hext_i : ExtT { ls1 with stack := sc :: ls1.stack } cx.fn.blocks :=
    hext_p.of_adv (advB_initSlots pre _ _ _ _ h2)
  have hext_1 : ExtT ls1 cx.fn.blocks := hext_i
  unfold prefixCoreBlock
  refine SimG.bind (block_enter hpp h1 hext_1 hrel) fun si pt1 fr1 ⟨hpp1, hv1, hfr1, hrel1⟩ => ?_
  have hsc : ({ env with scopes := (sc, si) :: env.scopes } : Env).scopes.head? = some (sc, si) := rfl
  refine SimG.bind (initSlots_sim hsc pre pre' hpre h2 hpp1 hext_p hrel1
    (PreRel.ext hfr1 hprer)) fun _ pt1' fr1' ⟨hpp1', hfr1', hst1', hvl1'⟩ => ?_
  subst fr1'
  have hrel1' : Rel cfg { env with scopes := (sc, si) :: env.scopes } cx fr1 ls_p := hrel1.stack_eq hst1'
  refine SimG.bind (ihs stmts hokS le _ u ls_s pt1' cfg _ cx fr1 h3 hpp1' hext_s hrel1')
    fun flow pt2 fr2 ⟨hfl, P2⟩ => ?_
  subst hfl
  refine SimG.bind (hX _ pt2 fr2 P2.pp hext_x P2.rel) fun flow' pt3 fr3 ⟨v, hfl', hU, P3⟩ => ?_
  subst hfl'
  refine SimG.bind (block_leave P3.pp h5 hext_l P3.rel) fun _ pt4 fr4 ⟨hpp4, hv4, hfr4, hrel4⟩ => ?_
  refine SimG.ret ⟨v, rfl, hU, ?_⟩
  have P23 := P2.comp P3
  refine Post.rescope (P23.sub (cells' := cells r v) (by simp)) (hv0 := ?_) (hfr0 := hfr1) ?_ ?_ hfr4 ?_
  · rw [hvl1']; exact hv1
  · rw [hls']; exact hpp4
  · rw [hls']; exact hv4
  · rw [hls']; exact hrel4

def prefixBlockCells (blk : Core.Block) (want : Bool) (r : ValueId) (v : Val) : List (ValueId × RVal) :=
  if blk.value.isSome || want then [(r, .val v)] else []

def BlockPreClaim (n : Nat) (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (pre' : List (VarId × Val)) (want : Bool) (blk : Core.Block) : Prop :=
  ∀ (cfg : Cfg) (env : Env), blockOk blk = true →
    (∀ p ∈ pre, ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = blk.scope) →
    ∀ (le : LEnv) (ls : LS) (r : ValueId) (ls' : LS) (pt : Pt) (cx : FnCtx)
    (fr : Frame), lowerBlock lc pre want blk le ls = (r, ls') → ls.pp = some pt →
    ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls → PreRel fr pre pre' →
    SimG cx pt fr (execBlock n cfg env pre' blk) (fun flow pt' fr' => ∃ v, flow = .normal v ∧
      (blk.value = none → v = .unit) ∧ Post cfg env cx ls fr ls' fr' pt' (prefixBlockCells blk want r v))

theorem blockPreClaim_succ (n : Nat) (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (pre' : List (VarId × Val)) (ihs : ∀ ss, StmtsClaim n lc ss) (ihe : ∀ e, ExprClaim n e)
    (want : Bool) (blk : Core.Block) : BlockPreClaim (n + 1) lc pre pre' want blk := by
  obtain ⟨sc, stmts, value⟩ := blk
  intro cfg env hok hpre le ls r ls' pt cx fr hlow hpp hext hrel hprer
  obtain ⟨ls1, ls_p, ls_s, ls_x, ls_l, u0, u, rx, h1, h2, h3, h4, h5, hls', hr⟩ := prefixBlock_unfold hlow
  rw [execBlock_pre]
  cases value with
  | some e =>
    simp only [lowerBlockValue] at h4
    refine (prefixBlock_core ihs (by okpf) hpre h1 h2 h3 h4 h5 hls' hr hpp hext hrel hprer (advB_lowerExpr e)
      (U := fun _ => True) (cells := fun rx v => [(rx, .val v)]) (vf := valueFlow n cfg (some e)) ?_).mono ?_
    · intro env' pt_x fr_x hpp_x hext_x hrel_x
      simp only [valueFlow]
      refine SimG.bind (ihe e (by okpf) le ls_s rx ls_x pt_x cfg env' cx fr_x h4 hpp_x hext_x hrel_x)
        fun v pt' fr' P => ?_
      exact SimG.ret ⟨v, rfl, trivial, P⟩
    · rintro flow pt' fr' ⟨v, hf, -, P⟩
      exact ⟨v, hf, (fun h => by cases h), by
        simp only [prefixBlockCells, Core.Block.value, Option.isSome_some, Bool.true_or, ↓reduceIte]; exact P⟩
  | none =>
    cases want
    · have h4' : (pure 0 : B ValueId) le ls_s = (rx, ls_x) := by
        simpa [lowerBlockValue] using h4
      refine (prefixBlock_core ihs (by okpf) hpre h1 h2 h3 h4' h5 hls' hr hpp hext hrel hprer (AdvB.pure _)
        (U := fun v => v = .unit) (cells := fun _ _ => []) (vf := valueFlow n cfg none) ?_).mono ?_
      · intro env' pt_x fr_x hpp_x hext_x hrel_x
        have hx : ls_x = ls_s := by rw [pure_run] at h4'; exact (Prod.mk.inj h4').2.symm
        subst hx
        exact SimG.ret ⟨.unit, rfl, rfl, Post.init hrel_x hpp_x⟩
      · rintro flow pt' fr' ⟨v, hf, hU, P⟩
        exact ⟨v, hf, (fun _ => hU), by simp only [prefixBlockCells, Core.Block.value, Option.isSome_none,
          Bool.false_or, Bool.false_eq_true, ↓reduceIte]; exact P⟩
    · have h4' : emitDef .constUnit le ls_s = (rx, ls_x) := by
        simpa [lowerBlockValue] using h4
      refine (prefixBlock_core ihs (by okpf) hpre h1 h2 h3 h4' h5 hls' hr hpp hext hrel hprer (advB_emitDef _)
        (U := fun v => v = .unit) (cells := fun rx v => [(rx, .val v)]) (vf := valueFlow n cfg none) ?_).mono ?_
      · intro env' pt_x fr_x hpp_x hext_x hrel_x
        have hP := Post.init hrel_x hpp_x
        show SimG cx pt_x fr_x ((pure () : M Unit) >>= fun _ => pure (Flow.normal Val.unit)) _
        refine SimG.bind (leaf_def hP h4' hext_x (by simp) (fun _ => RVal.val Val.unit)
          (c := (pure () : M Unit)) (by simp [execPure])) fun _ pt' fr' P => ?_
        exact SimG.ret ⟨.unit, rfl, rfl, P⟩
      · rintro flow pt' fr' ⟨v, hf, hU, P⟩
        exact ⟨v, hf, (fun _ => hU), by simp only [prefixBlockCells, Core.Block.value, Option.isSome_none,
          Bool.false_or, Bool.or_true, ↓reduceIte]; exact P⟩

theorem blockPreClaim (n : Nat) (lc : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val))
    (want : Bool) (blk : Core.Block) : BlockPreClaim n lc pre pre' want blk := by
  cases n with
  | zero =>
    intro cfg env hok hpre le ls r ls' pt cx fr hlow hpp hext hrel hprer
    simp only [execBlock]
    exact SimG.of_timeout
  | succ n => exact blockPreClaim_succ n lc pre pre' ((claims n).stmts lc) (claims n).expr want blk

end Goose.Lower
