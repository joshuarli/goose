import Goose.Lower.Prefix
import Goose.Lower.Validate

namespace Goose.Lower

open Goose.Core Goose.GIR

private theorem emitTerm_closed (t : Term) (le : LEnv) (ls : LS) :
    (emitTerm t le ls).2.cur = none := by
  cases hc : ls.cur with
  | none => rw [emitTerm_none t le hc]; exact hc
  | some b => rw [emitTerm_run t le hc]

private theorem lowerStmts_closed (lc : Option LoopCtx) (ss : List Stmt) (le : LEnv) (ls : LS)
    (hc : ls.cur = none) : lowerStmts lc ss le ls = ((), ls) := by
  cases ss <;> simp [lowerStmts, bind_run, isLive_none hc, pure_run]

private def DeadB (x : B α) : Prop :=
  ∀ le ls, ls.cur = none → ∃ a, x le ls = (a, ls)

private theorem DeadB.pure (a : α) : DeadB (pure a) := by
  intro le ls _
  exact ⟨a, pure_run a le ls⟩

private theorem DeadB.bind {x : B α} {f : α → B β} (hx : DeadB x)
    (hf : ∀ a, DeadB (f a)) : DeadB (x >>= f) := by
  intro le ls hc
  obtain ⟨a, ha⟩ := hx le ls hc
  obtain ⟨b, hb⟩ := hf a le ls hc
  exact ⟨b, by rw [bind_run, ha]; exact hb⟩

private theorem dead_emitDef (op : Op) : DeadB (emitDef op) := by
  intro le ls hc
  exact ⟨0, emitDef_none op le hc⟩

private theorem dead_emitEffect (e : Effect) : DeadB (emitEffect e) := by
  intro le ls hc
  exact ⟨(), emitEffect_none e le hc⟩

private theorem dead_emitTerm (t : Term) : DeadB (emitTerm t) := by
  intro le ls hc
  exact ⟨(), emitTerm_none t le hc⟩

private theorem dead_whenLive (d : α) (f : BlockId → B α) : DeadB (whenLive d f) := by
  intro le ls hc
  exact ⟨d, whenLive_none d f le hc⟩

private theorem dead_read : DeadB (read : B LEnv) := by
  intro le ls _
  exact ⟨le, rfl⟩

private theorem dead_valTy (v : ValueId) : DeadB (valTy v) := by
  intro le ls _
  exact ⟨(valTy v le ls).1, Prod.ext rfl (valTy_run v le ls)⟩

private theorem dead_intTyOf (v : ValueId) : DeadB (intTyOf v) := by
  intro le ls _
  exact ⟨(intTyOf v le ls).1, Prod.ext rfl (intTyOf_state v le ls)⟩

private theorem dead_freezeTo (mu : Mutability) (v : ValueId) : DeadB (freezeTo mu v) := by
  unfold freezeTo
  apply DeadB.bind (dead_valTy v)
  intro t
  cases mu <;> cases t with
    | view mu el => exact DeadB.pure _
    | data ty =>
      cases ty with
      | ref mode target => cases mode <;> first | exact dead_emitDef _ | exact DeadB.pure _
      | _ => exact DeadB.pure _

private theorem dead_initSlots : ∀ pre, DeadB (initSlots pre)
  | [] => by simp only [initSlots]; exact DeadB.pure _
  | _ :: rest => by
    simp only [initSlots]
    exact DeadB.bind (dead_emitEffect _) fun _ => dead_initSlots rest

private theorem dead_inScope (sc : ScopeId) {action : B α} (h : DeadB action) : DeadB (inScope sc action) := by
  intro le ls hc
  obtain ⟨a, ha⟩ := h le { ls with stack := sc :: ls.stack } hc
  refine ⟨a, ?_⟩
  simp only [inScope, bind_run, pushScope_run, ha, popScope_run, pure_run]
  rfl

mutual
 private theorem dead_lowerExpr : ∀ e, DeadB (lowerExpr e)
  | .lit .. | .bool _ => by simp only [lowerExpr]; exact dead_emitDef _
  | .read p => by
    simp only [lowerExpr]
    exact DeadB.bind (dead_lowerPlace p) fun _ => dead_emitDef _
  | .ref mu p => by
    simp only [lowerExpr]
    exact DeadB.bind (dead_lowerPlace p) fun r => dead_freezeTo mu r
  | .slice _ v lo hi _ => by
    simp only [lowerExpr]
    exact DeadB.bind (dead_lowerView v) fun _ => DeadB.bind (dead_lowerBound lo) fun _ =>
      DeadB.bind (dead_lowerBound hi) fun _ => dead_emitDef _
  | .len v => by simp only [lowerExpr]; exact DeadB.bind (dead_lowerView v) fun _ => dead_emitDef _
  | .un _ e _ => by
    simp only [lowerExpr]
    exact DeadB.bind (dead_lowerExpr e) fun v => DeadB.bind (dead_intTyOf v) fun _ => dead_emitDef _
  | .bin _ a b _ => by
    simp only [lowerExpr]
    exact DeadB.bind (dead_lowerExpr a) fun v => DeadB.bind (dead_lowerExpr b) fun _ =>
      DeadB.bind (dead_intTyOf v) fun _ => dead_emitDef _
  | .cmp _ a b => by
    simp only [lowerExpr]
    refine DeadB.bind (dead_lowerExpr a) fun v => DeadB.bind (dead_lowerExpr b) fun _ =>
      DeadB.bind (dead_valTy v) fun ty => ?_
    cases ty with
    | view mu el => exact dead_emitDef _
    | data t => cases t <;> exact dead_emitDef _
  | .and a _ | .or a _ => by
    simp only [lowerExpr, shortCircuit]
    exact DeadB.bind (dead_lowerExpr a) fun _ => dead_whenLive _ _
  | .not e => by simp only [lowerExpr]; exact DeadB.bind (dead_lowerExpr e) fun _ => dead_emitDef _
  | .conv _ _ e _ => by
    simp only [lowerExpr]
    exact DeadB.bind (dead_lowerExpr e) fun v => DeadB.bind (dead_intTyOf v) fun _ => dead_emitDef _
  | .call c args _ => by
    have hc : DeadB (implOfContext c) := by
      unfold implOfContext
      exact DeadB.bind dead_read fun _ => DeadB.pure _
    simp only [lowerExpr]
    refine DeadB.bind (dead_lowerArgs args) fun _ => DeadB.bind hc fun _ =>
      DeadB.bind (dead_emitDef _) fun _ => DeadB.bind dead_read fun le => ?_
    split
    · exact DeadB.bind (dead_emitTerm _) fun _ => DeadB.pure _
    · exact DeadB.pure _
  | .push p e _ => by
    simp only [lowerExpr]
    exact DeadB.bind (dead_lowerPlace p) fun _ => DeadB.bind (dead_lowerExpr e) fun _ => dead_emitDef _
  | .pop p _ => by simp only [lowerExpr]; exact DeadB.bind (dead_lowerPlace p) fun _ => dead_emitDef _
  | .ifE c _ _ => by
    simp only [lowerExpr]
    exact DeadB.bind (dead_lowerExpr c) fun _ => dead_whenLive _ _
  | .blockE b => by simp only [lowerExpr]; exact dead_lowerBlock _ _ _ b
  | .arrLit _ es | .structLit _ es => by
    simp only [lowerExpr]
    exact DeadB.bind (dead_lowerExprs es) fun _ => dead_emitDef _
  | .fill _ e => by simp only [lowerExpr]; exact DeadB.bind (dead_lowerExpr e) fun _ => dead_emitDef _

 private theorem dead_lowerExprs : ∀ es, DeadB (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact DeadB.pure _
  | e :: rest => by
    simp only [lowerExprs]
    exact DeadB.bind (dead_lowerExpr e) fun _ => DeadB.bind (dead_lowerExprs rest) fun _ => DeadB.pure _

 private theorem dead_lowerArg : ∀ arg, DeadB (lowerArg arg)
  | .byVal e => by simp only [lowerArg]; exact dead_lowerExpr e
  | .byRef mu p => by
    simp only [lowerArg]
    exact DeadB.bind (dead_lowerPlace p) fun v => dead_freezeTo mu v

 private theorem dead_lowerArgs : ∀ args, DeadB (lowerArgs args)
  | [] => by simp only [lowerArgs]; exact DeadB.pure _
  | arg :: rest => by
    simp only [lowerArgs]
    exact DeadB.bind (dead_lowerArg arg) fun _ => DeadB.bind (dead_lowerArgs rest) fun _ => DeadB.pure _

 private theorem dead_lowerPlace : ∀ p, DeadB (lowerPlace p)
  | .var _ | .global _ => by simp only [lowerPlace]; exact dead_emitDef _
  | .deref e => by simp only [lowerPlace]; exact dead_lowerExpr e
  | .elem v i _ => by
    simp only [lowerPlace]
    exact DeadB.bind (dead_lowerView v) fun _ => DeadB.bind (dead_lowerExpr i) fun _ => dead_emitDef _
  | .field p _ => by simp only [lowerPlace]; exact DeadB.bind (dead_lowerPlace p) fun _ => dead_emitDef _

 private theorem dead_lowerView : ∀ v, DeadB (lowerView v)
  | .of p => by simp only [lowerView]; exact DeadB.bind (dead_lowerPlace p) fun _ => dead_emitDef _
  | .val e => by simp only [lowerView]; exact DeadB.bind (dead_lowerExpr e) fun _ => dead_emitDef _

 private theorem dead_lowerBound : ∀ b, DeadB (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact DeadB.pure _
  | .expr e | .fromEnd e => by
    simp only [lowerBound]
    exact DeadB.bind (dead_lowerExpr e) fun _ => DeadB.pure _

 private theorem dead_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId))
    (want : Bool) : ∀ b, DeadB (lowerBlock lc pre want b)
  | .mk sc ss value => by
    simp only [lowerBlock]
    refine DeadB.bind (dead_emitEffect _) fun _ => dead_inScope sc ?_
    refine DeadB.bind (dead_initSlots pre) fun _ => DeadB.bind ?_ fun _ =>
      DeadB.bind ?_ fun _ => DeadB.bind (dead_emitEffect _) fun _ => DeadB.pure _
    · intro le ls hc
      exact ⟨(), lowerStmts_closed lc ss le ls hc⟩
    · cases value with
      | none => cases want <;> first | exact DeadB.pure _ | exact dead_emitDef _
      | some e => exact dead_lowerExpr e
end

mutual
 /-- Divergence in this fragment closes the path before function finalization. -/
 private theorem fragmentBlock_diverges_closed (b : Core.Block) (le : LEnv) (hok : blockOk b = true)
    (hd : b.diverges le.mod.noReturn = true) (lc : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (ls : LS) (r : ValueId) (ls' : LS)
    (h : lowerBlock lc pre false b le ls = (r, ls')) : ls'.cur = none := by
  cases b with
  | mk sc ss value =>
    have hss : stmtsOk ss = true := by
      rw [blockOk.eq_def] at hok
      exact (Bool.and_eq_true _ _).mp hok |>.1
    have hdss : stmtsDiverge le.mod.noReturn ss = true := hd
    obtain ⟨ls1, ls_p, ls_s, ls_x, ls_l, u0, u, rx, _, _, hs, hx, hl, heq, _⟩ := prefixBlock_unfold h
    have hclosed := fragmentStmts_diverges_closed ss le hss hdss lc ls_p u ls_s hs
    have hx' : ls_x = ls_s := by
      cases value with
      | none => simpa [lowerBlockValue, pure_run] using (Prod.mk.inj hx).2.symm
      | some e =>
        obtain ⟨v, hv⟩ := dead_lowerExpr e le ls_s hclosed
        change lowerExpr e le ls_s = (rx, ls_x) at hx
        rw [hv] at hx
        exact (Prod.mk.inj hx).2.symm
    subst ls_x
    rw [emitEffect_none (.leave sc) le hclosed] at hl
    have hl' : ls_l = ls_s := (Prod.mk.inj hl).2.symm
    subst ls_l
    rw [heq]
    exact hclosed
 termination_by sizeOf b

 private theorem fragmentStmts_diverges_closed (ss : List Stmt) (le : LEnv) (hok : stmtsOk ss = true)
    (hd : stmtsDiverge le.mod.noReturn ss = true) (lc : Option LoopCtx)
    (ls : LS) (r : Unit) (ls' : LS) (h : lowerStmts lc ss le ls = (r, ls')) : ls'.cur = none := by
  cases ss with
  | nil => simp [stmtsDiverge] at hd
  | cons stmt rest =>
    have hok' : stmtOk stmt = true ∧ stmtsOk rest = true := by simpa [stmtsOk] using hok
    have hd' : stmt.diverges le.mod.noReturn = true ∨ stmtsDiverge le.mod.noReturn rest = true := by
      simpa [stmtsDiverge] using hd
    cases hc : ls.cur with
    | none =>
      rw [lowerStmts_closed lc (stmt :: rest) le ls hc] at h
      exact (Prod.mk.inj h).2 ▸ hc
    | some b =>
      simp only [lowerStmts, bind_eq] at h
      obtain ⟨live, same, hlive, hif⟩ := h
      rw [isLive_run hc] at hlive
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlive
      simp only [ite_true] at hif
      obtain ⟨u, mid, hs, hr⟩ := bind_eq.mp hif
      rcases hd' with hdstmt | hdrest
      · have hmid := fragmentStmt_diverges_closed stmt le hok'.1 hdstmt lc ls u mid hs
        rw [lowerStmts_closed lc rest le mid hmid] at hr
        exact (Prod.mk.inj hr).2 ▸ hmid
      · exact fragmentStmts_diverges_closed rest le hok'.2 hdrest lc mid r ls' hr
 termination_by sizeOf ss

 private theorem fragmentStmt_diverges_closed (stmt : Stmt) (le : LEnv) (hok : stmtOk stmt = true)
    (hd : stmt.diverges le.mod.noReturn = true) (lc : Option LoopCtx)
    (ls : LS) (r : Unit) (ls' : LS) (h : lowerStmt lc stmt le ls = (r, ls')) : ls'.cur = none := by
  cases stmt with
  | abort msg org =>
    change emitTerm (.abort .userAbort (some org)) le ls = (r, ls') at h
    exact (congrArg (fun p => p.2.cur) h).symm.trans (emitTerm_closed _ le ls)
  | exit e org =>
    simp only [lowerStmt, bind_eq] at h
    obtain ⟨v, mid, _, ht⟩ := h
    exact (congrArg (fun p => p.2.cur) ht).symm.trans (emitTerm_closed _ le mid)
  | ifS c t f org =>
    cases f with
    | none => simp [Stmt.diverges] at hd
    | some f =>
      simp only [stmtOk, Bool.and_eq_true] at hok
      have htOk : blockOk t = true := hok.1.2
      have hfOk : blockOk f = true := hok.2
      have hdiv : t.diverges le.mod.noReturn = true ∧ f.diverges le.mod.noReturn = true := by
        simpa [Stmt.diverges] using hd
      simp only [lowerStmt, bind_eq] at h
      obtain ⟨cv, mid, _, hw⟩ := h
      cases hc : mid.cur with
      | none =>
        rw [whenLive_none () _ le hc] at hw
        exact (Prod.mk.inj hw).2 ▸ hc
      | some b =>
        rw [whenLive_some () _ le hc] at hw
        simp only [bind_eq] at hw
        obtain ⟨⟨tb, eb⟩, ls1, _, u1, ls2, _, vt, ls3, hT, endT, ls4, hCT,
          u2, ls5, _, vf, ls6, hF, endF, ls7, hCF, hj⟩ := hw
        have hclosedT := fragmentBlock_diverges_closed t le htOk hdiv.1 lc [] ls2 vt ls3 hT
        have hclosedF := fragmentBlock_diverges_closed f le hfOk hdiv.2 lc [] ls5 vf ls6 hF
        rw [curBlock_run] at hCT hCF
        obtain ⟨heT, hsT⟩ := Prod.mk.inj hCT
        obtain ⟨heF, hsF⟩ := Prod.mk.inj hCF
        have heT' : endT = none := heT.symm.trans hclosedT
        have heF' : endF = none := heF.symm.trans hclosedF
        subst endT
        subst endF
        rw [hclosedT, hclosedF] at hj
        simp only [joinArms, setCur_run] at hj
        exact (congrArg (fun p => p.2.cur) hj).symm
  | expr e org => cases e <;> simp_all [Stmt.diverges, stmtOk, exprOk]
  | ret e org => simp_all [stmtOk]
  | brk org => simp_all [stmtOk]
  | cont org => simp_all [stmtOk]
  | «while» c b org => simp_all [stmtOk]
  | forRange x lo hi b org => simp_all [stmtOk]
  | forEach x idx v byRef b org => simp_all [stmtOk]
  | _ => simp_all [Stmt.diverges]
 termination_by sizeOf stmt
end

theorem advB_finishFunction (impl : Impl) (v : ValueId) : AdvB (finishFunction impl v) := by
  unfold finishFunction
  refine AdvB.bind advB_read fun le => AdvB.bind advB_isLive fun live => ?_
  cases live with
  | false => exact AdvB.pure _
  | true =>
    by_cases h : (!impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn) = true
    · rw [if_pos h]
      exact advB_header0 fun sink => advB_emitTerm (.br sink [])
    · rw [if_neg h]
      exact advB_emitTerm _

/-- The result/no-tail sink cannot alter the proved fragment:
its stopping paths have already closed the builder, and other paths do not diverge. -/
theorem finishFunction_fragment (impl : Impl) (le : LEnv) (ls : LS) (v : ValueId) (ls' : LS)
    (hok : blockOk impl.body = true)
    (hlow : lowerBlock none [] false impl.body le ls = (v, ls')) :
    finishFunction impl v le ls' =
      ((do if (← isLive) then
        emitTerm (.ret (if impl.body.value.isSome then [v] else []) none) : B Unit) le ls') := by
  by_cases hd : impl.body.diverges le.mod.noReturn = true
  · have hc := fragmentBlock_diverges_closed impl.body le hok hd none [] ls v ls' hlow
    simp [finishFunction, bind_run, read_apply, isLive_none hc, pure_run]
  · have hd' : impl.body.diverges le.mod.noReturn = false := Bool.eq_false_iff.mpr hd
    simp [finishFunction, bind_run, read_apply, hd']

end Goose.Lower
