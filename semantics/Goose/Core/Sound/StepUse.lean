import Goose.Core.Sound.StepAux

/-!
Running a block from the validator's two checks of it, and the steps for a
block used as a value and for printed arguments.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}
variable {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}

/-- A block the typing pass and the root pass accepted, entered with values
for the variables its construct binds. -/
theorem block_of_checks (hB : BlockSpec m prof n) (hp : Perm m W) (hF : Frame m W tenv penv env s)
    (b : Block) (preT : List (VarId × Ty)) (pre : List (VarId × Val)) {preV : List VarId}
    {tn tn' : Nat} {ty : Ty} {rst rst' : RState} {rho : List RootRef} {rng : Nat × Nat}
    (ht : tyBlock tenv preT b tn = .ok (ty, tn'))
    (hr : rpBlockValue penv preV b rst = .ok ((rho, rng), rst'))
    (hE : EffLe rst'.eff W.E) (hpreV : preT.map Prod.fst = preV)
    (hpre : pre.map Prod.fst = preT.map Prod.fst)
    (hvals : ∀ (k : Nat) (x : VarId) (v : Val) (ty' : Ty), pre[k]? = some (x, v) →
      preT[k]? = some (x, ty') → ∀ lv, env.vars[x]? = some lv → lv.ty = ty' →
      HasTy m W.G s.store v lv.ty ∧ ∀ r, Targets v r → ∃ ann, penv.ann x = some ann ∧
        Gam env W.P ann r) :
    Sat (execBlock n ⟨prof, m⟩ env pre b) s (fun fl s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) (Dset W) s s' ∧
      match fl with
      | .normal v => HasTy m W.G s'.store v ty ∧ (∀ r, Targets v r → Gam env W.P rho r) ∧
          b.diverges = false
      | .brk => tenv.loops ≠ 0 ∧ b.hasBreak = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) := by
  subst hpreV
  obtain ⟨sc, stmts, value⟩ := b
  obtain ⟨hsc, env1, tn1, env2, tn2, hd, hts, htv⟩ := tyBlock_ok _ _ _ _ _ _ _ _ ht
  obtain ⟨hsame, hvis, hrows, hrange⟩ := declarePre_ok _ _ _ _ _ _ hd
  obtain ⟨hpr, st2, hrs, hrv, hkeep, _⟩ := rpBlockValue_ok _ _ _ _ _ _ _ _ _ hr
  have hvis' : ∀ y, y ∈ env1.visible ↔ y ∈ pre.map Prod.fst ∨ y ∈ tenv.visible := by
    intro y; rw [hvis, hpre]
  have hpreOk : PreOk m W penv { env with scopes := (sc, s.nextScope) :: env.scopes } sc rst.nextVar
      (rst.nextVar + (preT.map Prod.fst).length) s.store pre := by
    refine ⟨by rw [hpre, hrange]; exact List.nodup_range', ?_⟩
    intro x v hxv
    have hx : x ∈ preT.map Prod.fst := by
      rw [← hpre]; exact List.mem_map.2 ⟨(x, v), hxv, rfl⟩
    obtain ⟨h1, h2⟩ := hpr x hx
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hxv
    have hk2 : (preT.map Prod.fst)[k]? = some x := by
      rw [← hpre, List.getElem?_map, hk]; rfl
    rw [List.getElem?_map] at hk2
    cases hpk : preT[k]? with
    | none => simp [hpk] at hk2
    | some p =>
      obtain ⟨x', ty'⟩ := p
      simp only [hpk, Option.map_some, Option.some.injEq] at hk2
      subst hk2
      obtain ⟨lv, g1, g2, g3, g4⟩ := hrows _ (List.mem_of_getElem? hpk)
      have g1' : env.vars[x']? = some lv := by rw [← hF.vars_t]; exact g1
      obtain ⟨k1, k2⟩ := hvals k x' v ty' hk hpk lv g1' g4
      refine ⟨h1, h2, lv, g1', g2, paramOk_of_storable g3, k1, fun r hr' => ?_⟩
      obtain ⟨ann, ha, hga⟩ := k2 r hr'
      exact ⟨ann, ha, gam_push hF hsc _ hga⟩
  have hres := hB W tenv env1 env2 penv env s pre sc stmts value tn1 tn2 tn' ty
    { rst with nextVar := rst.nextVar + (preT.map Prod.fst).length } st2 rst' rho rst.nextVar
    hp hF hsc hsame hvis' hpreOk (Nat.le_add_right _ _) hts
    (by cases value with
        | none => exact htv.1
        | some e => exact htv)
    hrs
    (by cases value with
        | none => exact hrv
        | some e => exact hrv)
    hE hkeep
  refine hres.mono ?_
  rintro fl s' ⟨h1, h2, h3⟩
  refine ⟨h1, h2, ?_⟩
  cases fl with
  | normal v => exact ⟨h3.1, h3.2.1, by simpa [Block.diverges] using h3.2.2⟩
  | brk => exact ⟨h3.1, by simpa [Block.hasBreak] using h3.2⟩
  | cont => exact h3
  | ret v => exact h3

/-- A loop body: its variables were numbered and typed by the loop before the
body block was checked, and are bound when the block is entered. -/
theorem block_of_reserved (hB : BlockSpec m prof n) (hp : Perm m W) (hF : Frame m W tenv penv env s)
    (b : Block) (pre : List (VarId × Val)) (xs : List VarId) (lo0 : Nat)
    {tn tn' : Nat} {ty : Ty} {rst rst' : RState} {rho : List RootRef} {rng : Nat × Nat}
    (ht : tyBlock { tenv with visible := xs ++ tenv.visible } [] b tn = .ok (ty, tn'))
    (hr : rpBlockValue penv [] b rst = .ok ((rho, rng), rst'))
    (hE : EffLe rst'.eff W.E) (hxs : pre.map Prod.fst = xs) (hnd : xs.Nodup)
    (hvals : ∀ x v, (x, v) ∈ pre → lo0 ≤ x ∧ x < rst.nextVar ∧ ∃ lv, env.vars[x]? = some lv ∧
      lv.scope = b.scope ∧ lv.ty.paramOk = true ∧ HasTy m W.G s.store v lv.ty ∧
      ∀ r, Targets v r → ∃ ann, penv.ann x = some ann ∧ Gam env W.P ann r)
    (hlo : lo0 ≤ rst.nextVar)
    (hkeep0 : ∀ y, RootRef.local y ∈ rho → ¬ (lo0 ≤ y ∧ y < rst.nextVar)) :
    Sat (execBlock n ⟨prof, m⟩ env pre b) s (fun fl s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) (Dset W) s s' ∧
      match fl with
      | .normal v => HasTy m W.G s'.store v ty ∧ (∀ r, Targets v r → Gam env W.P rho r) ∧
          b.diverges = false
      | .brk => tenv.loops ≠ 0 ∧ b.hasBreak = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) := by
  subst hxs
  obtain ⟨sc, stmts, value⟩ := b
  obtain ⟨hsc, env1, tn1, env2, tn2, hd, hts, htv⟩ := tyBlock_ok _ _ _ _ _ _ _ _ ht
  obtain ⟨hsame, hvis, _, _⟩ := declarePre_ok _ _ _ _ _ _ hd
  obtain ⟨_, st2, hrs, hrv, hkeep, _⟩ := rpBlockValue_ok _ _ _ _ _ _ _ _ _ hr
  have hpreOk : PreOk m W penv { env with scopes := (sc, s.nextScope) :: env.scopes } sc lo0
      (rst.nextVar + ([] : List VarId).length) s.store pre := by
    refine ⟨hnd, ?_⟩
    intro x v hxv
    obtain ⟨h1, h2, lv, g1, g2, g3, k1, k2⟩ := hvals x v hxv
    refine ⟨h1, h2, lv, g1, g2, g3, k1, fun r hr' => ?_⟩
    obtain ⟨ann, ha, hga⟩ := k2 r hr'
    exact ⟨ann, ha, gam_push hF hsc _ hga⟩
  have hres := hB W tenv env1 env2 penv env s pre sc stmts value tn1 tn2 tn' ty
    { rst with nextVar := rst.nextVar + ([] : List VarId).length } st2 rst' rho lo0
    hp hF hsc
    ⟨hsame.mod, hsame.impl, hsame.vars, hsame.loops, hsame.inExpr, hsame.scopes,
      fun x hx => hsame.sub x (List.mem_append_right _ hx)⟩
    (fun y => by rw [hvis y]; simp)
    hpreOk hlo hts
    (by cases value with
        | none => exact htv.1
        | some e => exact htv)
    hrs
    (by cases value with
        | none => exact hrv
        | some e => exact hrv)
    hE
    (fun y hy hc => by
      by_cases h : y < rst.nextVar
      · exact hkeep0 y hy ⟨hc.1, h⟩
      · exact hkeep y hy ⟨Nat.le_of_not_lt h, hc.2⟩)
  refine hres.mono ?_
  rintro fl s' ⟨h1, h2, h3⟩
  refine ⟨h1, h2, ?_⟩
  cases fl with
  | normal v => exact ⟨h3.1, h3.2.1, by simpa [Block.diverges] using h3.2.2⟩
  | brk => exact ⟨h3.1, by simpa [Block.hasBreak] using h3.2⟩
  | cont => exact h3
  | ret v => exact h3

theorem step_blockValue (ih : Specs m prof n) : BlockValueSpec m prof (n + 1) := by
  intro W tenv penv env s b tn tn' ty rst rst' rho rng hp hF ht hr hE
  simp only [blockValue]
  have hF' : Frame m W (exprEnv tenv) penv env s := hF.tenv_congr rfl rfl rfl (fun _ h => h)
  refine Sat.bind (block_of_checks ih.block hp hF' b [] [] ht hr hE rfl rfl
    (fun k x v ty' h => by simp at h)) ?_
  rintro fl s1 ⟨hF1, hX1, hfl⟩
  cases fl with
  | normal v =>
    simp only [expectNormal, sat_pure]
    exact ⟨hF1.tenv_congr rfl rfl rfl (fun _ h => h), hX1, hfl.1, hfl.2.1⟩
  | brk => exact absurd rfl hfl.1
  | cont => exact absurd rfl hfl
  | ret v => exact absurd hfl.1 (by simp [exprEnv])

theorem step_printArg (ih : Specs m prof n) : PrintArgSpec m prof (n + 1) := by
  intro W tenv penv env s a tn tn' rst rst' hp hF ht hr hE
  cases a with
  | text t =>
    simp only [execPrintArg, sat_pure]
    exact ⟨hF, Ext.refl _ _ _⟩
  | expr e =>
    obtain ⟨ty, hte, hty⟩ := ht
    obtain ⟨rho, hre⟩ := hr
    simp only [execPrintArg]
    refine Sat.bind (ih.expr W tenv penv env s e _ _ _ _ _ _ hp hF hte hre hE) ?_
    rintro v s1 ⟨hF1, hX1, hv, _⟩
    rcases hty with ⟨t, rfl⟩ | rfl
    · obtain ⟨k, rfl⟩ := hasTy_int hv
      simp only [render, sat_pure]
      exact ⟨hF1, hX1⟩
    · obtain ⟨b, rfl⟩ := hasTy_bool hv
      cases b <;> (simp only [render, sat_pure]; exact ⟨hF1, hX1⟩)

/-- The arguments of one `print`. -/
theorem printArgs_spec (ihP : PrintArgSpec m prof n) (hp : Perm m W) :
    ∀ (args : List PrintArg) (s : St) (tn tn' : Nat) (rst rst' : RState),
    Frame m W tenv penv env s → tyPrintArgs tenv args tn = .ok ((), tn') →
    rpPrintArgs penv args rst = .ok ((), rst') → EffLe rst'.eff W.E →
    Sat (mapList (execPrintArg n ⟨prof, m⟩ env) args) s (fun _ s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) (Dset W) s s')
  | [], s, tn, tn', rst, rst', hF, _, _, _ => by
    simp only [mapList, sat_pure]
    exact ⟨hF, Ext.refl _ _ _⟩
  | .text t :: rest, s, tn, tn', rst, rst', hF, ht, hr, hE => by
    simp only [tyPrintArgs] at ht
    simp only [rpPrintArgs] at hr
    simp only [mapList]
    refine Sat.bind (ihP W tenv penv env s (.text t) tn tn rst rst hp hF rfl rfl
      ((rpPrintArgs_mono hr).2.trans hE)) ?_
    rintro _ s1 ⟨hF1, hX1⟩
    refine Sat.bind (printArgs_spec ihP hp rest s1 _ _ _ _ hF1 ht hr hE) ?_
    rintro _ s2 ⟨hF2, hX2⟩
    simp only [sat_pure]
    exact ⟨hF2, hX1.trans hX2⟩
  | .expr e :: rest, s, tn, tn', rst, rst', hF, ht, hr, hE => by
    simp only [tyPrintArgs] at ht; inv at ht
    simp only [rpPrintArgs] at hr; inv at hr
    obtain ⟨te, t1, hte, ht⟩ := ht
    obtain ⟨re, r1, hre, hrr⟩ := hr
    have hty : ((∃ t, te = .int t) ∨ te = .bool) ∧ tyPrintArgs tenv rest t1 = .ok ((), tn') := by
      cases te <;> inv at ht <;> first
        | exact ⟨Or.inl ⟨_, rfl⟩, ht⟩
        | exact ⟨Or.inr rfl, ht⟩
    simp only [mapList]
    refine Sat.bind (ihP W tenv penv env s (.expr e) tn t1 rst r1 hp hF ⟨te, hte, hty.1⟩ ⟨re, hre⟩
      ((rpPrintArgs_mono hrr).2.trans hE)) ?_
    rintro _ s1 ⟨hF1, hX1⟩
    refine Sat.bind (printArgs_spec ihP hp rest s1 _ _ _ _ hF1 hty.2 hrr hE) ?_
    rintro _ s2 ⟨hF2, hX2⟩
    simp only [sat_pure]
    exact ⟨hF2, hX1.trans hX2⟩

end Goose.Core.Sound
