import Goose.Lower.Validate

/-!
Conditional lowering preserves dense definitions and table references through
its concrete fork, arm switches and value join. This proves symbol bounds;
operation typing, dominance and the remaining verifier checks are separate.
-/

namespace Goose.Lower
open Goose.GIR (BlockId ValueId Inst Term)

/-- Only live endpoints carry a usable arm result; a closed arm's dummy result
must never become a branch operand. -/
def LS.armRefs (endpoint : Option BlockId) (value : ValueId) : List SymbolRef :=
  match endpoint with
  | none => []
  | some b => [.block b, .value value]

theorem LS.SymbolRun.armRefs_bound {le : LEnv} {sc : Nat} {ls out : LS}
    {action : B ValueId} {v : ValueId}
    (h : LS.SymbolRun le sc ls (fun v => [v]) action)
    (hw : LS.SymbolWF le sc ls) (hc : LS.CurrentBlocks ls)
    (hr : action le ls = (v, out)) :
    ∀ ref ∈ LS.armRefs out.cur v, SymbolRef.Bound le out ref := by
  obtain ⟨_, hc', _, hv⟩ := h hw hc v out hr
  cases he : out.cur with
  | none => simp [LS.armRefs, he]
  | some b =>
    intro ref href
    simp [LS.armRefs, he] at href
    rcases href with rfl | rfl
    · exact hc' b he
    · exact hv (by simp [he]) v (by simp)

theorem patchBrs_symbols {le : LEnv} {sc : Nat} {jb : BlockId}
    (live : List (BlockId × ValueId)) {ls ls' : LS} {u : Unit}
    (hw : LS.SymbolWF le sc ls) (hj : jb < ls.blocks.size)
    (hl : ∀ p ∈ live, p.1 < ls.blocks.size ∧ p.2 < ls.vals.size)
    (hr : patchBrs jb live le ls = (u, ls')) :
    LS.SymbolWF le sc ls' ∧ ls'.blocks.size = ls.blocks.size ∧
      ls'.vals.size = ls.vals.size := by
  induction live generalizing ls ls' with
  | nil =>
    change ((), ls) = (u, ls') at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    exact ⟨hw, rfl, rfl⟩
  | cons p rest ih =>
    obtain ⟨u1, mid, h1, h2⟩ := bind_eq.mp hr
    rw [patchTerm_run] at h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    have hp := hl p (by simp)
    have ht : Inst.SymbolsWithin le sc ls.vals.size ls.blocks.size
        (.term (.br jb [p.2])) := by
      apply Inst.SymbolsWithin.term
      · simpa [Term.uses] using hp.2
      · simp [Term.origin]
      · simpa [Term.successors] using hj
    have hn := hw.patchTerm hp.1 ht
    simpa using ih hn (by simpa using hj)
      (fun q hq => by simpa using hl q (by simp [hq])) h2

/-- A live first arm can produce a join even when the second arm closes.
Therefore join preservation uses saved endpoint bounds rather than requiring
that the current path be live. -/
theorem joinValue_symbols {le : LEnv} {sc : Nat} {ls ls' : LS}
    {endT endF : Option BlockId} {vt vf r : ValueId}
    (hw : LS.SymbolWF le sc ls)
    (ht : ∀ b, endT = some b → b < ls.blocks.size ∧ vt < ls.vals.size)
    (hf : ∀ b, endF = some b → b < ls.blocks.size ∧ vf < ls.vals.size)
    (hr : joinValue endT vt endF vf le ls = (r, ls')) :
    LS.SymbolWF le sc ls' ∧ LS.CurrentBlocks ls' ∧
      (ls'.cur.isSome → r < ls'.vals.size) := by
  unfold joinValue at hr
  have key : ∀ {live : List (BlockId × ValueId)},
      (∀ p ∈ live, p.1 < ls.blocks.size ∧ p.2 < ls.vals.size) →
      (do
        let ty ← valTy (live.headD (0, 0)).2
        let (jb, js) ← newBlock [ty]
        patchBrs jb live
        setCur (some jb)
        pure (js.headD 0) : B ValueId) le ls = (r, ls') →
      LS.SymbolWF le sc ls' ∧ LS.CurrentBlocks ls' ∧
        (ls'.cur.isSome → r < ls'.vals.size) := by
    intro live hl hk
    simp only [bind_eq] at hk
    obtain ⟨ty, s1, h1, ⟨jb, js⟩, s2, h2, u, s3, h3, u2, s4, h4, h5⟩ := hk
    have hs := valTy_eq h1
    subst hs
    rw [newBlock1_run] at h2
    obtain ⟨hids, rfl⟩ := Prod.mk.inj h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hids
    have hn : LS.SymbolWF le sc
        { s1 with
          blocks := s1.blocks.push ⟨[(s1.vals.size, ty)], #[]⟩
          vals := s1.vals.push (some ty) } := by
      simpa [paramIds, pushParamTypes] using (hw.newBlock (tys := [ty]))
    obtain ⟨hw3, hb3, hv3⟩ := patchBrs_symbols live hn (by simp)
      (fun p hp => by
        have h := hl p hp
        simpa using And.intro (Nat.lt_succ_of_lt h.1) (Nat.lt_succ_of_lt h.2)) h3
    rw [setCur_run] at h4
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
    rw [pure_run] at h5
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h5
    refine ⟨hw3.changeCur _, ?_, ?_⟩
    · intro b he
      change some s1.blocks.size = some b at he
      cases he
      simp [hb3]
    · intro _
      simp [hv3]
  cases endT <;> cases endF
  · simp only [bind_eq] at hr
    obtain ⟨u, s1, h1, h2⟩ := hr
    rw [setCur_run] at h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    rw [pure_run] at h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    exact ⟨hw.changeCur _, by intro b hb; simp at hb, by simp⟩
  · apply key (fun p hp => ?_) hr
    simp at hp; subst hp; exact hf _ rfl
  · apply key (fun p hp => ?_) hr
    simp at hp; subst hp; exact ht _ rfl
  · apply key (fun p hp => ?_) hr
    simp at hp
    rcases hp with rfl | rfl
    · exact ht _ rfl
    · exact hf _ rfl

theorem ifE_core_symbolRun_of {le : LEnv} {sc : Nat} {t f : Core.Block}
    (ht : ∀ ls, LS.SymbolRun le sc ls (fun v => [v]) (lowerBlock none [] true t))
    (hf : ∀ ls, LS.SymbolRun le sc ls (fun v => [v]) (lowerBlock none [] true f))
    {ls : LS} {cv : ValueId} (hcv : ls.cur.isSome → cv < ls.vals.size) :
    LS.SymbolRun le sc ls (fun v => [v]) (whenLive 0 fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let vt ← lowerBlock none [] true t
      let endT ← curBlock
      setCur (some eb)
      let vf ← lowerBlock none [] true f
      let endF ← curBlock
      joinValue endT vt endF vf) := by
  intro hw hc r out hr
  cases hs : ls.cur with
  | none =>
    rw [whenLive_none _ _ _ hs] at hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    exact ⟨hw, hc, fun _ => hs, by simp [hs]⟩
  | some b =>
    rw [whenLive_some _ _ _ hs] at hr
    simp only [bind_eq] at hr
    obtain ⟨⟨tb, eb⟩, s1, hfork, u1, s2, hsetT, vt, s3, hthen,
      endT, s4, hcurT, u2, s5, hsetF, vf, s6, helse,
      endF, s7, hcurF, hjoin⟩ := hr
    have hw1 : LS.SymbolWF le sc s1 := by
      have hh := hw.fork hs (hc b hs) (hcv (by simp [hs]))
      rw [hfork] at hh
      exact hh
    obtain ⟨_, _, _, htb, heb⟩ := adv_fork_step (.refl ls) hfork
    rw [setCur_run] at hsetT
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hsetT
    have hcT : LS.CurrentBlocks { s1 with cur := some tb } := by
      intro x hx
      change some tb = some x at hx
      cases hx
      exact htb
    obtain ⟨hw3, hc3, _, hvT⟩ := ht _ (hw1.changeCur _) hcT vt s3 hthen
    have aT := advB_lowerBlock none [] true t le _ _ _ hthen
    obtain ⟨heT, rfl⟩ := curBlock_eq hcurT
    rw [setCur_run] at hsetF
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hsetF
    have hcF : LS.CurrentBlocks { s4 with cur := some eb } := by
      intro x hx
      change some eb = some x at hx
      cases hx
      exact Nat.lt_of_lt_of_le heb aT.ext.1
    obtain ⟨hw6, hc6, _, hvF⟩ := hf _ (hw3.changeCur _) hcF vf s6 helse
    have aF := advB_lowerBlock none [] true f le _ _ _ helse
    obtain ⟨heF, rfl⟩ := curBlock_eq hcurF
    have bt : ∀ x, endT = some x → x < s7.blocks.size ∧ vt < s7.vals.size := by
      intro x hx
      have hx' : s4.cur = some x := heT.symm.trans hx
      have hv := hvT (by simp [hx']) vt (by simp)
      exact ⟨Nat.lt_of_lt_of_le (hc3 x hx') aF.ext.1,
        Nat.lt_of_lt_of_le hv aF.vals⟩
    have bf : ∀ x, endF = some x → x < s7.blocks.size ∧ vf < s7.vals.size := by
      intro x hx
      have hx' : s7.cur = some x := heF.symm.trans hx
      exact ⟨hc6 x hx', hvF (by simp [hx']) vf (by simp)⟩
    obtain ⟨hw7, hc7, hv7⟩ := joinValue_symbols hw6 bt bf hjoin
    refine ⟨hw7, hc7, ?_, ?_⟩
    · intro hd
      simp at hd
    · intro hl v hv
      simp only [List.mem_singleton] at hv
      subst v
      exact hv7 hl

/-- The condition and both particular arms must preserve symbols; no premise
quantifies over arbitrary unchecked source syntax. -/
theorem lowerExpr_ifE_symbolRunAt_of {le : LEnv} {sc : Nat} {c : Core.Expr} {t f : Core.Block}
    (hc : ∀ ls, LS.SymbolRun le sc ls (fun v => [v]) (lowerExpr c))
    (ht : ∀ ls, LS.SymbolRun le sc ls (fun v => [v]) (lowerBlock none [] true t))
    (hf : ∀ ls, LS.SymbolRun le sc ls (fun v => [v]) (lowerBlock none [] true f))
    (ls : LS) :
    LS.SymbolRunAt le sc ls (LS.valueRefs fun v => [v]) (lowerExpr (.ifE c t f)) := by
  apply LS.SymbolRun.toSymbolRunAt _ (advB_lowerExpr (.ifE c t f))
  change LS.SymbolRun le sc ls (fun v => [v]) (do
    let cv ← lowerExpr c
    whenLive 0 fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let vt ← lowerBlock none [] true t
      let endT ← curBlock
      setCur (some eb)
      let vf ← lowerBlock none [] true f
      let endF ← curBlock
      joinValue endT vt endF vf)
  apply LS.SymbolRun.bind (hc ls)
  intro cv mid _ _ hv
  exact ifE_core_symbolRun_of ht hf (fun hl => hv hl cv (by simp))

private theorem scope_symbolRun {le : LEnv} {sc : Nat} {ls : LS}
    {ids : α → List ValueId} {k : B α} {scope : Nat}
    (hk : ∀ s, LS.SymbolRun le sc s ids k) :
    LS.SymbolRun le sc ls ids (inScope scope k) := by
  intro hw hc r out hr
  simp only [inScope, bind_eq] at hr
  obtain ⟨u, s1, h1, v, s2, h2, u2, s3, h3, h4⟩ := hr
  rw [pushScope_run] at h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
  have hw1 : LS.SymbolWF le sc { ls with stack := scope :: ls.stack } :=
    ⟨hw.definitions, hw.instructions⟩
  obtain ⟨hw2, hc2, hd2, hv2⟩ := hk _ hw1 hc v s2 h2
  rw [popScope_run] at h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
  rw [pure_run] at h4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
  exact ⟨⟨hw2.definitions, hw2.instructions⟩, hc2, hd2, hv2⟩

/-- This arm fragment admits both normal and aborting statements, with a
particular value expression whose preservation has already been established. -/
theorem lowerBlock_value_symbolRun_of {le : LEnv} {sc scope : Nat}
    {stmts : List Core.Stmt} {e : Core.Expr}
    (hs : scope < sc)
    (hstmts : ∀ ls, LS.SymbolRun le sc ls (fun _ => []) (lowerStmts none stmts))
    (he : ∀ ls, LS.SymbolRun le sc ls (fun v => [v]) (lowerExpr e)) (ls : LS) :
    LS.SymbolRun le sc ls (fun v => [v])
      (lowerBlock none [] true (.mk scope stmts (some e))) := by
  change LS.SymbolRun le sc ls (fun v => [v]) (do
    emitEffect (.enter scope)
    inScope scope do
      initSlots []
      lowerStmts none stmts
      let r ← lowerExpr e
      emitEffect (.leave scope)
      pure r)
  have effect : ∀ s (eff : Goose.GIR.Effect),
      eff = .enter scope ∨ eff = .leave scope →
      LS.SymbolRun le sc s (fun _ => []) (emitEffect eff) := by
    intro s eff h
    rcases h with rfl | rfl <;> apply LS.SymbolRun.emitEffect
    all_goals simp [Goose.GIR.Effect.uses, Goose.GIR.Effect.origin,
      Effect.SymbolRefsValid, hs]
  apply LS.SymbolRun.bind (effect ls _ (Or.inl rfl))
  intro _ mid _ _ _
  apply scope_symbolRun
  intro s
  change LS.SymbolRun le sc s (fun v => [v]) (do
    pure ()
    lowerStmts none stmts
    let r ← lowerExpr e
    emitEffect (.leave scope)
    pure r)
  apply LS.SymbolRun.bind (hstmts s)
  intro _ s1 _ _ _
  apply LS.SymbolRun.bind (he s1)
  intro v s2 _ _ hv
  intro hw hc r out hr
  obtain ⟨u, s3, h3, h4⟩ := bind_eq.mp hr
  obtain ⟨hw3, hc3, hd3, _⟩ := effect s2 _ (Or.inr rfl) hw hc u s3 h3
  have ha := adv_emitEffect h3
  rw [pure_run] at h4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
  refine ⟨hw3, hc3, hd3, ?_⟩
  intro hl x hx
  simp only [List.mem_singleton] at hx
  subst x
  have hl2 : s2.cur.isSome := by
    cases hh : s2.cur with
    | none => have hd := hd3 hh; simp [hd] at hl
    | some b => simp
  exact Nat.lt_of_lt_of_le (hv hl2 v (by simp)) ha.vals

def conditionalArm (scope : Nat) (stop : Bool) (org : Core.OriginId) (n : Int) : Core.Block :=
  .mk scope (if stop then [.abort "stop" org] else []) (some (.lit .i64 n))

theorem conditionalArm_symbolRun {le : LEnv} {sc scope : Nat} {org : Core.OriginId}
    (hs : scope < sc) (ho : org < le.mod.origins.size) (stop : Bool) (n : Int) (ls : LS) :
    LS.SymbolRun le sc ls (fun v => [v]) (lowerBlock none [] true (conditionalArm scope stop org n)) := by
  apply lowerBlock_value_symbolRun_of hs _ (fun _ => lowerExpr_lit_symbolRun .i64 n)
  intro s
  cases stop with
  | false => exact LS.SymbolRun.stable ⟨(), rfl⟩
  | true =>
    intro hw hc u out hr
    change (do
      if (← isLive) then
        emitTerm (.abort .userAbort (some org))
        pure () : B Unit) le s = (u, out) at hr
    cases hh : s.cur with
    | none =>
      have hi : isLive le s = (false, s) := by simp [isLive, bind_run, curBlock_run, hh, pure_run]
      simp only [bind_eq] at hr
      obtain ⟨v, mid, h1, h2⟩ := hr
      rw [hi] at h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      change ((), s) = (u, out) at h2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      exact ⟨hw, hc, fun _ => hh, by simp⟩
    | some b =>
      have hi : isLive le s = (true, s) := by simp [isLive, bind_run, curBlock_run, hh, pure_run]
      simp only [bind_eq] at hr
      obtain ⟨v, mid, h1, h2⟩ := hr
      rw [hi] at h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      obtain ⟨v, mid, h3, h4⟩ := bind_eq.mp h2
      have ht : LS.SymbolRun le sc s (fun _ => []) (emitTerm (.abort .userAbort (some org))) := by
        apply LS.SymbolRun.emitTerm
        · simp [Term.uses]
        · simpa [Term.origin] using ho
        · simp [Term.successors]
      obtain ⟨hw3, hc3, hd3, _⟩ := ht hw hc v mid h3
      rw [pure_run] at h4
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h4
      exact ⟨hw3, hc3, by intro hd; simp at hd, by simp⟩

/-- These particular arms have preservation proofs for every choice of abort
flags; neither arm premise needs a universal claim about unchecked blocks. -/
theorem lowerExpr_conditionalArms_symbolRunAt {le : LEnv} {sc scopeT scopeF : Nat}
    {org : Core.OriginId} (ht : scopeT < sc) (hf : scopeF < sc)
    (ho : org < le.mod.origins.size) (c stopT stopF : Bool) (nt nf : Int) (ls : LS) :
    LS.SymbolRunAt le sc ls (LS.valueRefs fun v => [v])
      (lowerExpr (.ifE (.bool c) (conditionalArm scopeT stopT org nt)
        (conditionalArm scopeF stopF org nf))) := by
  exact lowerExpr_ifE_symbolRunAt_of (fun _ => lowerExpr_bool_symbolRun c)
    (conditionalArm_symbolRun ht ho stopT nt)
    (conditionalArm_symbolRun hf ho stopF nf) ls

end Goose.Lower
