import Goose.Core.Sound.StepAux

/-!
Running a block from the validator's two checks of it, and the steps for a
block used as a value and for printed arguments.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {plans : Array (Array DemandPoint)} {n : Nat}
variable {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}

private theorem gam_push_future {future : List VarId}
    (hF : Frame m W tenv penv env s future) {sc : Nat} (hsc : sc ∉ tenv.scopes)
    (k : ScopeInst) {P : Nat → RootInst → Prop} {rho : List RootRef} {r : RootInst}
    (h : Gam env P rho r) :
    Gam { env with scopes := (sc, k) :: env.scopes } P rho r := by
  have hsc' : sc ∉ env.scopes.map Prod.fst := hF.scopes_t ▸ hsc
  obtain ⟨q, hq, hr⟩ := h
  refine ⟨q, hq, ?_⟩
  cases q with
  | «local» y =>
    obtain ⟨lv, si, h1, h2, h3⟩ := hr
    refine ⟨lv, si, h1, ?_, h3⟩
    show ((sc, k) :: env.scopes).lookup lv.scope = some si
    rw [lookup_cons]
    have : lv.scope ≠ sc := fun e => hsc' (e ▸ lookup_key h2)
    simp [this, h2]
  | global g => exact hr
  | param _ => exact hr

private theorem EvaluationContext.activeMatches_congr
    {path : List Nat} {node : DemandNode} {phase : DemandPhase}
    (ec : EvaluationContext m plans path node phase) {a b : TEnv}
    (h : ec.ActiveMatches a) (hvisible : ∀ x, x ∈ a.visible ↔ x ∈ b.visible) :
    ec.ActiveMatches b := by
  cases ec with
  | pilot profile active =>
    intro x
    exact (h x).trans (hvisible x)
  | shrink profile context =>
    change context.ActiveMatches a at h
    change context.ActiveMatches b
    unfold NodeContext.ActiveMatches at h ⊢
    intro x
    exact (h x).trans (hvisible x)

/-- A block the typing pass and the root pass accepted, entered with values
for the variables its construct binds. -/
theorem block_of_checks (hB : BlockSpec m prof plans n) (hp : Perm m W)
    {path : List Nat} (b : Block)
    (ec : EvaluationContext m plans path (.block b) .block) (observation : Observation)
    (preT : List (VarId × Ty)) (pre : List (VarId × Val)) {preV : List VarId}
    {tn tn' : Nat} {ty : Ty} {rst rst' : RState} {rho : List RootRef} {rng : Nat × Nat}
    (hactive : ∀ env1 tn1,
      declarePre { tenv with scopes := b.scope :: tenv.scopes } b.scope preT tn = .ok (env1, tn1) →
        ec.ActiveMatches env1)
    (haccess : ec.AccessMatches tenv penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hobserved : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (hclassified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (hF : Frame m W tenv penv env s ec.inputFuture)
    (ht : tyBlock tenv preT b tn = .ok (ty, tn'))
    (hr : rpBlockValue penv preV b rst = .ok ((rho, rng), rst'))
    (hE : EffLe rst'.eff W.E) (hpreV : preT.map Prod.fst = preV)
    (hpre : pre.map Prod.fst = preT.map Prod.fst)
    (hvals : ∀ (k : Nat) (x : VarId) (v : Val) (ty' : Ty), pre[k]? = some (x, v) →
      preT[k]? = some (x, ty') → ∀ lv, env.vars[x]? = some lv → lv.ty = ty' →
      HasTy m W.G s.store v lv.ty ∧ ∀ r, Targets v r → ∃ ann,
        penv.ann x = some ann ∧ Gam env W.P ann r ∧
        (OwnerRefTy lv.ty → Gam env W.ownerP ann r)) :
    Sat (execBlock n ⟨prof, m⟩ env pre b) s (fun fl s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧
      (match fl with
      | .normal v => HasTy m W.G s'.store v ty ∧ (∀ r, Targets v r → Gam env W.P rho r) ∧
          b.diverges m.noReturn = false ∧ OwnerRooted env W.ownerP rho v ty
      | .brk => tenv.loops ≠ 0 ∧ b.hasBreak = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store) ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
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
      obtain ⟨ann, ha, hgam, howner⟩ := k2 r hr'
      exact ⟨ann, ha, gam_push_future hF hsc _ hgam,
        fun hty => gam_push_future hF hsc _ (howner hty)⟩
  have hres := hB path sc stmts value ec observation W tenv env1 env2 penv env s pre tn1 tn2 tn' ty
    { rst with nextVar := rst.nextVar + (preT.map Prod.fst).length } st2 rst' rho rst.nextVar
    (hactive env1 tn1 hd) haccess hprotected hobserved hclassified hp hF hsc hsame hvis' hpreOk
    (Nat.le_add_right _ _) hts
    (by cases value with
        | none => exact htv.1
        | some e => exact htv)
    hrs
    (by cases value with
        | none => exact hrv
        | some e => exact hrv)
    hE hkeep
  refine hres.mono ?_
  rintro fl s' ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hForbidden, hMutation⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, h9, hForbidden, hMutation⟩
  cases fl with
  | normal v => exact ⟨h8.1, h8.2.1, by simpa [Block.diverges] using h8.2.2.1, h8.2.2.2⟩
  | brk => exact ⟨h8.1, by simpa [Block.hasBreak] using h8.2⟩
  | cont => exact h8
  | ret v => exact h8

/-- A loop body: its variables were numbered and typed by the loop before the
body block was checked, and are bound when the block is entered. -/
theorem block_of_reserved (hB : BlockSpec m prof plans n) (hp : Perm m W)
    {path : List Nat} (b : Block)
    (ec : EvaluationContext m plans path (.block b) .block) (observation : Observation)
    (pre : List (VarId × Val)) (xs : List VarId) (lo0 : Nat)
    {tn tn' : Nat} {ty : Ty} {rst rst' : RState} {rho : List RootRef} {rng : Nat × Nat}
    (hactive : ∀ env1 tn1,
      declarePre { { tenv with visible := xs ++ tenv.visible } with scopes := b.scope :: tenv.scopes }
        b.scope [] tn = .ok (env1, tn1) → ec.ActiveMatches env1)
    (haccess : ec.AccessMatches tenv penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hobserved : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (hclassified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (hF : Frame m W tenv penv env s ec.inputFuture)
    (ht : tyBlock { tenv with visible := xs ++ tenv.visible } [] b tn = .ok (ty, tn'))
    (hr : rpBlockValue penv [] b rst = .ok ((rho, rng), rst'))
    (hE : EffLe rst'.eff W.E) (hxs : pre.map Prod.fst = xs) (hnd : xs.Nodup)
    (hvals : ∀ x v, (x, v) ∈ pre → lo0 ≤ x ∧ x < rst.nextVar ∧ ∃ lv, env.vars[x]? = some lv ∧
      lv.scope = b.scope ∧ lv.ty.paramOk = true ∧ HasTy m W.G s.store v lv.ty ∧
      ∀ r, Targets v r → ∃ ann, penv.ann x = some ann ∧ Gam env W.P ann r ∧
        (OwnerRefTy lv.ty → Gam env W.ownerP ann r))
    (hlo : lo0 ≤ rst.nextVar)
    (hkeep0 : ∀ y, RootRef.local y ∈ rho → ¬ (lo0 ≤ y ∧ y < rst.nextVar)) :
    Sat (execBlock n ⟨prof, m⟩ env pre b) s (fun fl s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧
      (match fl with
      | .normal v => HasTy m W.G s'.store v ty ∧ (∀ r, Targets v r → Gam env W.P rho r) ∧
          b.diverges m.noReturn = false ∧ OwnerRooted env W.ownerP rho v ty
      | .brk => tenv.loops ≠ 0 ∧ b.hasBreak = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store) ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
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
    obtain ⟨ann, ha, hgam, howner⟩ := k2 r hr'
    exact ⟨ann, ha, gam_push_future hF hsc _ hgam,
      fun hty => gam_push_future hF hsc _ (howner hty)⟩
  have hres := hB path sc stmts value ec observation W tenv env1 env2 penv env s pre tn1 tn2 tn' ty
    { rst with nextVar := rst.nextVar + ([] : List VarId).length } st2 rst' rho lo0
    (hactive env1 tn1 hd) haccess hprotected hobserved hclassified hp hF hsc
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
  rintro fl s' ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hForbidden, hMutation⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, h9, hForbidden, hMutation⟩
  cases fl with
  | normal v => exact ⟨h8.1, h8.2.1, by simpa [Block.diverges] using h8.2.2.1, h8.2.2.2⟩
  | brk => exact ⟨h8.1, by simpa [Block.hasBreak] using h8.2⟩
  | cont => exact h8
  | ret v => exact h8

theorem step_blockValue (ih : Specs m prof plans n) : BlockValueSpec m prof plans (n + 1) := by
  intro path b ec observation W tenv penv env s tn tn' ty rst rst' rho rng
    hactive haccess hprotected hobserved hclassified hp hF ht hr hE
  simp only [blockValue]
  have hF' : Frame m W (exprEnv tenv) penv env s ec.inputFuture :=
    hF.tenv_congr rfl rfl rfl (fun _ h => h)
  have hactive' : ∀ env1 tn1,
      declarePre { exprEnv tenv with scopes := b.scope :: (exprEnv tenv).scopes }
        b.scope [] tn = .ok (env1, tn1) → ec.ActiveMatches env1 := by
    intro env1 tn1 hd
    obtain ⟨_, hvis, _, _⟩ := declarePre_ok _ _ _ _ _ _ hd
    have hvis' : ∀ x, x ∈ (exprEnv tenv).visible ↔ x ∈ env1.visible := by
      intro x
      specialize hvis x
      simpa using hvis.symm
    exact ec.activeMatches_congr hactive hvis'
  have haccess' : ec.AccessMatches (exprEnv tenv) penv := by
    simpa [exprEnv, EvaluationContext.AccessMatches, NodeContext.AccessMatches] using haccess
  refine Sat.bind (block_of_checks ih.block hp b ec observation [] [] hactive' haccess'
    hprotected hobserved hclassified hF' ht hr hE rfl rfl (fun k x v ty' h => by simp at h)) ?_
  rintro fl s1 ⟨hF1, hFoot, hRoots, hValues, hSafe, hRetained, hPilot, hfl, hClass, hForbidden, hMutation⟩
  cases fl with
  | normal v =>
    simp only [expectNormal, sat_pure]
    exact ⟨hF1.tenv_congr rfl rfl rfl (fun _ h => h), hFoot, hRoots, hValues,
      hSafe, hRetained, hPilot, hfl.1, hfl.2.1, hClass, hfl.2.2.2, hForbidden, hMutation⟩
  | brk => exact absurd rfl hfl.1
  | cont => exact absurd rfl hfl
  | ret v => exact absurd hfl.1 (by simp [exprEnv])

theorem step_printArg (ih : Specs m prof plans n) : PrintArgSpec m prof plans (n + 1) := by
  intro path a ac observation W tenv penv env s tn tn' rst rst'
    hactive haccess hprotected hobserved hclassified hp hF ht hr hE
  cases ac with
  | text future retained shrinking =>
    simp only [PrintTy, PrintRp] at ht hr
    simp only [execPrintArg, sat_pure]
    exact ⟨hF, Footprint.refl _ _ _, PreservesRootTypes.refl _, PreservesValues.refl _,
      hobserved, RetainsAliases.refl, fun _ => StoreLe.refl _, hclassified, PreservesForbiddenOwnerRoots.refl _, MutationFootprint.refl _ _ _ _ _⟩
  | expr ec =>
    obtain ⟨ty, hte, hty⟩ := ht
    obtain ⟨rho, hre⟩ := hr
    simp only [execPrintArg]
    refine Sat.bind (ih.expr path _ ec observation W tenv penv env s tn tn' ty rst rst' rho
      hactive haccess hprotected hobserved hclassified hp hF hte hre hE) ?_
    rintro v s1 ⟨hF1, hFoot, hRoots, hValues, hSafe, hRetained, hPilot, hv, _, hClass, _, hForbidden, hMutation⟩
    rcases hty with ⟨t, rfl⟩ | rfl
    · obtain ⟨k, rfl⟩ := hasTy_int hv
      simp only [render, sat_pure]
      exact ⟨hF1, hFoot, hRoots, hValues, hSafe, hRetained, hPilot, hClass, hForbidden, hMutation⟩
    · obtain ⟨b, rfl⟩ := hasTy_bool hv
      cases b <;> (simp only [render, sat_pure]; exact ⟨hF1, hFoot, hRoots, hValues,
        hSafe, hRetained, hPilot, hClass, hForbidden, hMutation⟩)

private def printArgsFuture {path : List Nat} {all : List PrintArg} {origin : OriginId}
    (ec : EvaluationContext m plans path (.statement (.print all origin)) .statement)
    (args : List PrintArg) : List VarId :=
  args.flatMap PrintArg.variables ++ ec.outputFuture

/-- Derive the checked expression context from the argument's original print index. -/
private theorem printExpr_pilotOutputFuture {path : List Nat} {all : List PrintArg} {origin : OriginId}
    (profile : m.profile = .pilot) (active : List VarId)
    (offset : Nat) (e : Expr) (harg : all[offset]? = some (.expr e)) :
    ((@EvaluationContext.pilot m plans path (.statement (.print all origin)) .statement profile active).child
      rfl offset (.expression e) .expression
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture =
        (@EvaluationContext.pilot m plans path (.statement (.print all origin)) .statement profile active).outputFuture := by
  simp [EvaluationContext.child, EvaluationContext.outputFuture,
    DemandNode.visibleForChild, DemandNode.visibleAfter]

private theorem printExpr_shrinkOutputFuture {path : List Nat} {all : List PrintArg} {origin : OriginId}
    {pc : PlanContext m plans} (profile : m.profile = .shrink)
    (context : NodeContext pc path (.statement (.print all origin)) .statement)
    (offset : Nat) (e : Expr) (rest : List PrintArg)
    (harg : all[offset]? = some (.expr e)) (hrest : rest = all.drop (offset + 1)) :
    ((EvaluationContext.shrink profile context :
      EvaluationContext m plans path (.statement (.print all origin)) .statement).child
      rfl offset (.expression e) .expression
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture =
        printArgsFuture (.shrink profile context) rest := by
  have hchild : (DemandNode.statement (.print all origin)).child? offset =
      some (.expression e) := by
    simp [DemandNode.child?, DemandNode.children, harg]
  have hphase : DemandNodeHasPhase (.expression e) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let transition := context.child rfl offset (.expression e) .expression hchild hphase
  let parent : DemandPoint :=
    ⟨path, .expression, context.expected.frame.active, context.expected.frame.future,
      context.expected.frame.retained⟩
  have hoffset : offset < all.length := (List.getElem?_eq_some_iff.mp harg).1
  have hexpectation :
      (DemandNode.statement (.print all origin)).childExpectation?
          pc.approvals.access parent offset =
        some ⟨(DemandNode.statement (.print all origin)).visibleForChild
            context.expected.frame.active offset,
          rest.flatMap PrintArg.variables ++ context.expected.frame.future⟩ := by
    simp [parent, DemandNode.childExpectation?, DemandNode.childFuture, hchild, hrest, hoffset]
  have hfuture : transition.childFrame.future =
      rest.flatMap PrintArg.variables ++ context.expected.frame.future := by
    have h := DemandNode.childFrame_future transition.childFrameEq hexpectation
    simpa [hexpectation] using h
  change transition.context.expected.frame.future =
    rest.flatMap PrintArg.variables ++ context.expected.frame.future
  rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
    hfuture]

/-- Facts for an argument's exact source child and the checked state after it. -/
private structure PrintArgStepContext {path : List Nat} {all : List PrintArg} {origin : OriginId}
    {W : World} {tenv : TEnv} {penv : PEnv} {observation : Observation}
    (ec : EvaluationContext m plans path (.statement (.print all origin)) .statement)
    (offset : Nat) (a : PrintArg) (rest : List PrintArg)
    (suffix : rest = all.drop (offset + 1)) where
  child : PrintArgContext m plans (path ++ [offset]) a
  active : child.ActiveMatches tenv
  access : child.AccessMatches tenv penv
  shrinking : ∀ r, child.mayShrink W.ownerP observation r ↔ ec.mayShrink W.ownerP observation r
  retained : ∀ alias, alias ∈ ec.retained → alias ∈ child.retained
  inputFuture : ∀ x, x ∈ child.inputFuture → x ∈ printArgsFuture ec (a :: rest)

private noncomputable def printArgStepContext {path : List Nat} {all : List PrintArg} {origin : OriginId}
    {W : World} {tenv : TEnv} {penv : PEnv} {observation : Observation}
    (ec : EvaluationContext m plans path (.statement (.print all origin)) .statement)
    (hactive : ec.ActiveMatches tenv) (haccess : ec.AccessMatches tenv penv)
    (offset : Nat) (a : PrintArg) (rest : List PrintArg)
    (harg : all[offset]? = some a) (hrest : rest = all.drop (offset + 1)) :
    PrintArgStepContext (W := W) (tenv := tenv) (penv := penv)
      (observation := observation) ec offset a rest hrest := by
  cases a with
  | text text =>
    refine ⟨.text (printArgsFuture ec rest) ec.retained ec.mayShrink, trivial,
      trivial, ?_, ?_, ?_⟩
    · intro r
      rfl
    · intro alias hmem
      exact hmem
    · intro x hx
      simpa [PrintArgContext.inputFuture, printArgsFuture, PrintArg.variables] using hx
  | expr e =>
    have hchild : (DemandNode.statement (.print all origin)).child? offset =
        some (.expression e) := by
      simp [DemandNode.child?, DemandNode.children, harg]
    have hphase : DemandNodeHasPhase (.expression e) .expression := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let child := ec.child rfl offset (.expression e) .expression hchild hphase
    have hactiveChild : child.ActiveMatches tenv :=
      ec.child_activeMatches rfl offset (.expression e) .expression hchild hphase
        tenv tenv hactive (by
          intro x
          simp [DemandNode.visibleForChild])
    have haccessChild : child.AccessMatches tenv penv :=
      (ec.child_accessMatches_iff rfl offset (.expression e) .expression hchild hphase
        tenv penv).2 haccess
    have hinputChild : child.inputFuture = e.variables ++ child.outputFuture := by
      cases ec <;> rfl
    refine ⟨.expr child, hactiveChild, haccessChild, ?_, ?_, ?_⟩
    · intro r
      exact ec.child_mayShrink_iff rfl offset (.expression e) .expression hchild hphase
        W.ownerP observation r
    · intro alias hmem
      exact ec.child_retained_subset rfl offset (.expression e) .expression hchild hphase hmem
    · intro x hx
      change x ∈ child.inputFuture at hx
      rw [hinputChild] at hx
      cases ec with
      | pilot profile active =>
        have hout := printExpr_pilotOutputFuture (m := m) (plans := plans) (path := path)
          (all := all) (origin := origin) profile active offset e (by simpa using harg)
        rw [hout] at hx
        simp only [printArgsFuture, List.flatMap_cons, PrintArg.variables,
          List.mem_append] at hx ⊢
        rcases hx with hvar | hactive
        · exact Or.inl (Or.inl hvar)
        · exact Or.inr hactive
      | shrink profile context =>
        have hout := printExpr_shrinkOutputFuture profile context offset e rest
          (by simpa using harg) hrest
        rw [hout] at hx
        simp only [printArgsFuture, List.flatMap_cons, PrintArg.variables,
          List.mem_append] at hx ⊢
        rcases hx with hvar | hrest
        · exact Or.inl (Or.inl hvar)
        · rcases hrest with hrest | hfuture
          · exact Or.inl (Or.inr hrest)
          · exact Or.inr hfuture

private theorem printArgs_suffix_spec (ihP : PrintArgSpec m prof plans n) (hp : Perm m W)
    {path : List Nat} {all : List PrintArg} {origin : OriginId}
    (ec : EvaluationContext m plans path (.statement (.print all origin)) .statement)
    (observation : Observation) (hactive : ec.ActiveMatches tenv)
    (haccess : ec.AccessMatches tenv penv) :
    ∀ (offset : Nat) (args : List PrintArg), args = all.drop offset →
      ∀ (s : St) (tn tn' : Nat) (rst rst' : RState),
      ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation) →
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store →
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
      Frame m W tenv penv env s (printArgsFuture ec args) →
      tyPrintArgs tenv args tn = .ok ((), tn') →
      rpPrintArgs penv args rst = .ok ((), rst') → EffLe rst'.eff W.E →
      Sat (mapList (execPrintArg n ⟨prof, m⟩ env) args) s (fun _ s' =>
        Frame m W tenv penv env s' ec.outputFuture ∧
        Footprint (insts env) (Dset W) s s' ∧
        PreservesRootTypes m W.G observation.roots s.store s'.store ∧
        PreservesValues m W.G observation.values s.store s'.store ∧
        ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
        RetainsAliases m W env s.store s'.store ec.retained ∧
        PilotStoreLe m s s' ∧
        (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store) ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s')
  | _, [], hargs, s, tn, tn', rst, rst', hprotected, hobserved, hclassified, hF, _, _, _ => by
    simp only [mapList, sat_pure]
    refine ⟨?_, Footprint.refl _ _ _, PreservesRootTypes.refl _, PreservesValues.refl _,
      hobserved, RetainsAliases.refl, fun hpilot => StoreLe.refl _, hclassified, PreservesForbiddenOwnerRoots.refl _,
      MutationFootprint.refl _ _ _ _ _⟩
    cases ec with
    | pilot profile active => simpa [printArgsFuture, EvaluationContext.outputFuture] using hF
    | shrink profile context => simpa [printArgsFuture, EvaluationContext.outputFuture] using hF
  | offset, .text t :: rest, hargs, s, tn, tn', rst, rst', hprotected, hobserved, hclassified, hF, ht, hr, hE => by
    have hdrop : all.drop offset = .text t :: rest := hargs.symm
    have harg : all[offset]? = some (.text t) := by
      have hfirst : (all.drop offset)[0]? = some (.text t) := by simp [hdrop]
      simpa using hfirst
    have hargs' : rest = all.drop (offset + 1) := by
      have h := congrArg (fun xs : List PrintArg => xs.drop 1) hdrop
      have h' : all.drop (offset + 1) = rest := by simpa using h
      exact h'.symm
    simp only [tyPrintArgs] at ht
    simp only [rpPrintArgs] at hr
    simp only [mapList]
    have htext : Sat (execPrintArg n ⟨prof, m⟩ env (.text t)) s
        (fun _ s1 => s1 = s) := by
      cases n <;> simp [execPrintArg]
    refine Sat.bind htext ?_
    intro text s1 heq
    subst s1
    refine Sat.bind (printArgs_suffix_spec ihP hp ec observation hactive haccess
      (offset + 1) rest hargs' s tn tn' rst rst' hprotected hobserved hclassified
      (by simpa [printArgsFuture, PrintArg.variables] using hF) ht hr hE) ?_
    intro result s' hresult
    simpa only [sat_pure] using hresult
  | offset, .expr e :: rest, hargs, s, tn, tn', rst, rst', hprotected, hobserved, hclassified, hF, ht, hr, hE => by
    have hdrop : all.drop offset = .expr e :: rest := hargs.symm
    have harg : all[offset]? = some (.expr e) := by
      have hfirst : (all.drop offset)[0]? = some (.expr e) := by simp [hdrop]
      simpa using hfirst
    have hargs' : rest = all.drop (offset + 1) := by
      have h := congrArg (fun xs : List PrintArg => xs.drop 1) hdrop
      have h' : all.drop (offset + 1) = rest := by simpa using h
      exact h'.symm
    let step := printArgStepContext (W := W) (observation := observation)
      ec hactive haccess offset (.expr e) rest harg hargs'
    simp only [tyPrintArgs] at ht
    inv at ht
    simp only [rpPrintArgs] at hr
    inv at hr
    obtain ⟨te, t1, hte, ht⟩ := ht
    obtain ⟨re, r1, hre, hrr⟩ := hr
    have hty : ((∃ t, te = .int t) ∨ te = .bool) ∧ tyPrintArgs tenv rest t1 = .ok ((), tn') := by
      cases te <;> inv at ht <;> first
        | exact ⟨Or.inl ⟨_, rfl⟩, ht⟩
        | exact ⟨Or.inr rfl, ht⟩
    simp only [mapList]
    have hprotectedStep : ShrinkProtected W.D W.A (step.child.mayShrink W.ownerP observation) :=
      ShrinkProtected.mono hprotected (fun _ _ h => h) (fun _ _ h => h)
        (fun r h => (step.shrinking r).1 h)
    have hobservedStep : ObservedSafe m W (step.child.mayShrink W.ownerP observation) observation s.store :=
      hobserved.weakenShrinking (fun r h => (step.shrinking r).1 h)
    refine Sat.bind (ihP (path ++ [offset]) (.expr e) step.child observation W tenv penv env s tn t1 rst r1
      step.active step.access hprotectedStep hobservedStep hclassified hp (hF.narrowFuture step.inputFuture)
      ⟨te, hte, hty.1⟩ ⟨re, hre⟩ ((rpPrintArgs_mono hrr).2.trans hE)) ?_
    rintro _ s1 ⟨hF1, hFoot1, hRoots1, hValues1, hSafe1, hRetained1, hPilot1, hClass1, hForbidden1, hMutation1⟩
    have hSafe1' : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s1.store :=
      hSafe1.weakenShrinking (fun r h => (step.shrinking r).2 h)
    have hRetained1' : RetainsAliases m W env s.store s1.store ec.retained :=
      hRetained1.subset step.retained
    have hFrest : Frame m W tenv penv env s1 (printArgsFuture ec rest) := by
      cases ec with
      | pilot profile active =>
        have hactivePilot : ∀ x, x ∈ tenv.visible ↔ x ∈ active := by
          intro x
          exact (hactive x).symm
        have hFactive : Frame m W tenv penv env s1 active := by
          simpa [step, printArgStepContext, PrintArgContext.outputFuture, EvaluationContext.outputFuture,
            EvaluationContext.child, DemandNode.visibleForChild, DemandNode.visibleAfter] using hF1
        apply hFactive.changeFuture
        intro x hxvisible hxnew
        have hxnew' : x ∈ rest.flatMap PrintArg.variables ++ active := by
          simpa [printArgsFuture, EvaluationContext.outputFuture, DemandNode.visibleAfter] using hxnew
        rcases List.mem_append.mp hxnew' with _ | hxactive
        · exact hactivePilot x |>.1 hxvisible
        · exact hxactive
      | shrink profile context =>
        have hout := printExpr_shrinkOutputFuture profile context offset e rest harg hargs'
        simpa [step, printArgStepContext, PrintArgContext.outputFuture, hout] using hF1
    refine Sat.bind (printArgs_suffix_spec ihP hp ec observation hactive haccess
      (offset + 1) rest hargs' s1 _ _ _ _ hprotected hSafe1' hClass1 hFrest hty.2 hrr hE) ?_
    rintro _ s2 ⟨hF2, hFoot2, hRoots2, hValues2, hSafe2, hRetained2, hPilot2, hClass2, hForbidden2, hMutation2⟩
    simp only [sat_pure]
    refine ⟨hF2, hFoot1.trans hFoot2, hRoots1.trans hRoots2, hValues1.trans hValues2,
      hSafe2, hRetained1'.trans hRetained2, ?_, hClass2, ?_, ?_⟩
    · intro hpilot
      exact (hPilot1 hpilot).trans (hPilot2 hpilot)
    · exact (hForbidden1.subset (by
        intro owner hmem
        exact ec.child_forbidden_subset rfl offset (.expression e) .expression
          (by simp [DemandNode.child?, DemandNode.children, harg])
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) owner hmem)).trans hForbidden2
    · exact (hMutation1.weaken (effectMutationRoots.mono m penv.impl
        (rpPrintArgs_mono hrr).2 (rpPrintArgs_rebinds_mono hrr))).trans hMutation2

/-- The arguments of one `print`, evaluated at their original child indices. -/
theorem printArgs_spec (ihP : PrintArgSpec m prof plans n) (hp : Perm m W)
    {path : List Nat} (all : List PrintArg) (origin : OriginId)
    (ec : EvaluationContext m plans path (.statement (.print all origin)) .statement)
    (observation : Observation) (hactive : ec.ActiveMatches tenv)
    (haccess : ec.AccessMatches tenv penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hobserved : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (hclassified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (hF : Frame m W tenv penv env s ec.inputFuture)
    (ht : tyPrintArgs tenv all tn = .ok ((), tn'))
    (hr : rpPrintArgs penv all rst = .ok ((), rst')) (hE : EffLe rst'.eff W.E) :
    Sat (mapList (execPrintArg n ⟨prof, m⟩ env) all) s (fun _ s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store) ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  have hFstart : Frame m W tenv penv env s (printArgsFuture ec all) := by
    cases ec with
    | pilot profile active =>
      simpa [printArgsFuture, EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        DemandNode.variables, Stmt.variables, PrintArg.variables, DemandNode.visibleAfter] using hF
    | shrink profile context =>
      simpa [printArgsFuture, EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
        Stmt.variables, PrintArg.variables] using hF
  simpa [printArgsFuture] using
    (printArgs_suffix_spec ihP hp ec observation hactive haccess 0 all rfl
      s tn tn' rst rst' hprotected hobserved hclassified hFstart ht hr hE)

end Goose.Core.Sound
