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
    (b : Block) (preT : List (VarId × Ty)) (pre : List (VarId × Val))
    {tn tn' : Nat} {ty : Ty} {rst rst' : RState} {rho : List RootRef} {rng : Nat × Nat}
    (ht : tyBlock tenv preT b tn = .ok (ty, tn'))
    (hr : rpBlockValue penv (preT.map Prod.fst) b rst = .ok ((rho, rng), rst'))
    (hE : EffLe rst'.eff W.E) (hpre : pre.map Prod.fst = preT.map Prod.fst)
    (hvals : ∀ x v, (x, v) ∈ pre → ∀ lv, env.vars[x]? = some lv →
      HasTy m W.G s.store v lv.ty ∧ ∀ r, Targets v r → ∃ ann, penv.ann x = some ann ∧
        Gam { env with scopes := (b.scope, s.nextScope) :: env.scopes } W.P ann r) :
    Sat (execBlock n ⟨prof, m⟩ env pre b) s (fun fl s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s' ∧
      match fl with
      | .normal v => HasTy m W.G s'.store v ty ∧ (∀ r, Targets v r → Gam env W.P rho r) ∧
          b.diverges = false
      | .brk => tenv.loops ≠ 0 ∧ b.hasBreak = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) := by
  obtain ⟨sc, stmts, value⟩ := b
  obtain ⟨hsc, env1, tn1, env2, tn2, hd, hts, htv⟩ := tyBlock_ok _ _ _ _ _ _ _ _ ht
  obtain ⟨hsame, hvis, hrows, hrange⟩ := declarePre_ok _ _ _ _ _ _ hd
  obtain ⟨hpr, st2, hrs, hrv, hkeep⟩ := rpBlockValue_ok _ _ _ _ _ _ _ _ _ hr
  have hvis' : ∀ y, y ∈ env1.visible ↔ y ∈ pre.map Prod.fst ∨ y ∈ tenv.visible := by
    intro y; rw [hvis, hpre]
  have hpreOk : PreOk m W penv { env with scopes := (sc, s.nextScope) :: env.scopes } sc rst.nextVar
      (rst.nextVar + (preT.map Prod.fst).length) s.store pre := by
    refine ⟨by rw [hpre, hrange]; exact List.nodup_range', ?_⟩
    intro x v hxv
    have hx : x ∈ preT.map Prod.fst := by
      rw [← hpre]; exact List.mem_map.2 ⟨(x, v), hxv, rfl⟩
    obtain ⟨h1, h2⟩ := hpr x hx
    obtain ⟨⟨x', ty'⟩, hmem, rfl⟩ := List.mem_map.1 hx
    obtain ⟨lv, g1, g2, g3, _⟩ := hrows _ hmem
    have g1' : env.vars[x']? = some lv := by rw [← hF.vars_t]; exact g1
    obtain ⟨k1, k2⟩ := hvals x' v hxv lv g1'
    exact ⟨h1, h2, lv, g1', g2, g3, k1, k2⟩
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

theorem step_blockValue (ih : Specs m prof n) : BlockValueSpec m prof (n + 1) := by
  intro W tenv penv env s b tn tn' ty rst rst' rho rng hp hF ht hr hE
  simp only [blockValue]
  have hF' : Frame m W (exprEnv tenv) penv env s := hF.tenv_congr rfl rfl rfl (fun _ h => h)
  refine Sat.bind (block_of_checks ih.block hp hF' b [] [] ht hr hE rfl
    (fun x v h => by cases h)) ?_
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
    exact ⟨hF, Ext.refl _ _⟩
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
      Frame m W tenv penv env s' ∧ Ext (insts env) s s')
  | [], s, tn, tn', rst, rst', hF, _, _, _ => by
    simp only [mapList, sat_pure]
    exact ⟨hF, Ext.refl _ _⟩
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
