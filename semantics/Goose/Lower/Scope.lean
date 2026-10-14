import Goose.Lower.Leaf

namespace Goose.Lower

open Goose.Core Goose.GIR


def coreBlock (n : Nat) (cfg : Cfg) (env : Env) (sc : Nat) (stmts : List Stmt)
    (vf : Env → Flow → M Flow) : M Flow := do
  let si ← freshScope
  let env' : Env := { env with scopes := (sc, si) :: env.scopes }
  let flow ← execStmts n cfg env' stmts
  let flow' ← vf env' flow
  Goose.Core.releaseScope env sc si
  pure flow'


def valueFlow (n : Nat) (cfg : Cfg) : Option Expr → Env → Flow → M Flow
  | some e, env', .normal _ => do pure (Flow.normal (← evalExpr n cfg env' e))
  | _, _, f => pure f

theorem execBlock_nil (n : Nat) (cfg : Cfg) (env : Env) (sc : Nat) (stmts : List Stmt)
    (value : Option Expr) :
    execBlock (n + 1) cfg env [] (.mk sc stmts value) = coreBlock n cfg env sc stmts (valueFlow n cfg value) := by
  rw [execBlock]
  simp only [coreBlock, bindAll, pure_bind]
  congr 1
  funext si
  congr 1
  funext flow
  congr 1
  funext flow'
  cases flow <;> cases value <;> simp [valueFlow]

def blockCells (blk : Core.Block) (want : Bool) (r : ValueId) (v : Val) : List (ValueId × RVal) :=
  if blk.value.isSome || want then [(r, .val v)] else []


def PreRel (fr : Frame) : List (SlotId × ValueId × OriginId) → List (VarId × Val) → Prop
  | [], [] => True
  | (x, r, _) :: ps, (x', v) :: vs => x = x' ∧ fr.vals[r]? = some (.val v) ∧ PreRel fr ps vs
  | _, _ => False

theorem PreRel.ext {fr fr' : Frame} (h : fr'.vals = fr.vals) :
    ∀ {pre pre'}, PreRel fr pre pre' → PreRel fr' pre pre'
  | [], [], _ => trivial
  | (x, r, _) :: ps, (x', v) :: vs, ⟨h1, h2, h3⟩ => ⟨h1, by rw [h]; exact h2, PreRel.ext h h3⟩
  | [], _ :: _, hp => absurd hp (by simp [PreRel])
  | _ :: _, [], hp => absurd hp (by simp [PreRel])


theorem rootOf_head {env : Env} {sc : Nat} {si : ScopeInst} {rest : List (Nat × ScopeInst)} {x : VarId}
    (hs : env.scopes = (sc, si) :: rest) {lv : LocalVar} (hv : env.vars[x]? = some lv)
    (hsc : lv.scope = sc) : rootOf env x = pure (.local env.act si x) := by
  unfold rootOf
  rw [hv]
  simp [hs, hsc, List.lookup]

theorem initSlots_sim {cfg : Cfg} {env : Env} {cx : FnCtx} {sc : ScopeId} {si : ScopeInst}
    (hs : env.scopes.head? = some (sc, si)) :
    ∀ (pre : List (SlotId × ValueId × OriginId)) (pre' : List (VarId × Val)) {le : LEnv}
      {lsk ls_i : LS} {u : Unit} {ptk : Pt} {frk : Frame},
      (∀ p ∈ pre, ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = sc) →
      initSlots pre le lsk = (u, ls_i) → lsk.pp = some ptk → ExtT ls_i cx.fn.blocks →
      Rel cfg env cx frk lsk → PreRel frk pre pre' →
      SimG cx ptk frk (bindAll env.act si pre') (fun _ pt' fr' =>
        ls_i.pp = some pt' ∧ fr' = frk ∧ ls_i.stack = lsk.stack ∧ ls_i.vals = lsk.vals)
  | [], [], le, lsk, ls_i, u, ptk, frk, _, h, hpp, hext, hrel, _ => by
    simp only [initSlots, pure_run] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    exact SimG.ret ⟨hpp, rfl, rfl, rfl⟩
  | (x, r, o) :: rest, (x', v) :: rest', le, lsk, ls_i, u, ptk, frk, hsc, h, hpp, hext, hrel, ⟨hx, hv, hrest⟩ => by
    subst hx
    simp only [initSlots, bind_eq] at h
    obtain ⟨u1, ls1, h1, h2⟩ := h
    have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (advB_initSlots rest _ _ _ _ h2)
    obtain ⟨hv1, hst1, hpp1, hi⟩ := emitEffect_facts h1 hpp hext1
    have hvArray : ls1.vals = lsk.vals := by
      obtain ⟨blk, hc, -, -⟩ := LS.pp_some hpp
      rw [emitEffect_run _ _ hc] at h1
      obtain ⟨-, rfl⟩ := Prod.mk.inj h1
      rfl
    obtain ⟨lv, hlv, hlvs⟩ := hsc (x, r, o) (by simp)
    obtain ⟨rest0, hrest0⟩ : ∃ rest0, env.scopes = (sc, si) :: rest0 := by
      cases hh : env.scopes with
      | nil => simp [hh] at hs
      | cons hd tl => simp [hh] at hs; exact ⟨tl, by rw [hs]⟩
    have hroot := rootOf_head hrest0 hlv hlvs
    have hx : execEff cx.fn frk (.slotInit x r (some o)) =
        bindRoot (.local env.act si x) v >>= fun _ => pure frk := by
      simp only [execEff, slotRoot_eq hrel x, hroot, getVal_of hv, pure_bind]
    simp only [bindAll]
    refine SimG.bind (SimG.eff_step (fun _ => frk) hi (c := bindRoot (.local env.act si x) v) (by
      simpa using hx)) fun _ pt1 fr1 ⟨hpt, hfr⟩ => ?_
    subst pt1; subst fr1
    have hrel1 : Rel cfg env cx frk ls1 := hrel.stack_eq hst1
    have hrest' := initSlots_sim hs rest rest' (fun p hp => hsc p (by simp [hp])) h2 hpp1 hext hrel1
      (PreRel.ext rfl hrest)
    refine SimG.mono hrest' fun a pt' fr' ⟨h1', h2', h3', h4'⟩ => ⟨h1', h2', ?_, ?_⟩
    · rw [h3', hst1]
    · rw [h4', hvArray]


def prefixCoreBlock (n : Nat) (cfg : Cfg) (env : Env) (sc : Nat) (stmts : List Stmt)
    (pre' : List (VarId × Val)) (vf : Env → Flow → M Flow) : M Flow := do
  let si ← freshScope
  let env' : Env := { env with scopes := (sc, si) :: env.scopes }
  bindAll env.act si pre'
  let flow ← execStmts n cfg env' stmts
  let flow' ← vf env' flow
  Goose.Core.releaseScope env sc si
  pure flow'

theorem execBlock_pre (n : Nat) (cfg : Cfg) (env : Env) (sc : Nat) (stmts : List Stmt)
    (pre' : List (VarId × Val)) (value : Option Expr) :
    execBlock (n + 1) cfg env pre' (.mk sc stmts value) =
      prefixCoreBlock n cfg env sc stmts pre' (valueFlow n cfg value) := by
  rw [execBlock]
  simp only [prefixCoreBlock]
  congr 1
  funext si
  congr 1
  funext u
  congr 1
  funext flow
  congr 1
  funext flow'
  cases flow <;> cases value <;> simp [valueFlow]

theorem prefixBlock_unfold {sc : ScopeId} {stmts : List Stmt} {value : Option Expr} {want : Bool}
    {lc : Option LoopCtx} {pre : List (SlotId × ValueId × OriginId)}
    {le : LEnv} {ls : LS} {r : ValueId} {ls' : LS}
    (h : lowerBlock lc pre want (.mk sc stmts value) le ls = (r, ls')) :
    ∃ ls1 ls_p ls_s ls_x ls_l u0 u rx, emitEffect (.enter sc) le ls = ((), ls1) ∧
      initSlots pre le { ls1 with stack := sc :: ls1.stack } = (u0, ls_p) ∧
      lowerStmts lc stmts le ls_p = (u, ls_s) ∧
      lowerBlockValue want value le ls_s = (rx, ls_x) ∧
      emitEffect (.leave sc) le ls_x = ((), ls_l) ∧
      ls' = { ls_l with stack := ls_l.stack.drop 1 } ∧ r = rx := by
  simp only [lowerBlock, bind_eq] at h
  obtain ⟨u1, ls1, h1, hin⟩ := h
  obtain ⟨ls_k, hk, hls'⟩ := inScope_eq hin
  simp only [bind_eq] at hk
  obtain ⟨u2, ls_p, h2, u3, ls_s, h3, rx, ls_x, h4, u5, ls_l, h5, hpure⟩ := hk
  rw [pure_run] at hpure
  obtain ⟨hr, rfl⟩ := Prod.mk.inj hpure
  exact ⟨ls1, ls_p, ls_s, ls_x, ls_l, u2, u3, rx, by simpa using h1, h2, h3, h4, by simpa using h5, hls', hr.symm⟩


end Goose.Lower
