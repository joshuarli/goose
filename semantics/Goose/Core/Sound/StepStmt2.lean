import Goose.Core.Sound.StepUse

/-!
One step of the induction on fuel for the control statements.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {plans : Array (Array DemandPoint)} {n : Nat}

private noncomputable def statementExprChildContext {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (index : Nat) (e : Expr)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.expression e)) :
    EvaluationContext m plans (path ++ [index]) (DemandNode.expression e) .expression :=
  ec.child rfl index (DemandNode.expression e) .expression hchild (by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private noncomputable def statementViewChildContext {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (index : Nat) (v : View)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.view v)) :
    EvaluationContext m plans (path ++ [index]) (DemandNode.view v) .view :=
  ec.child rfl index (DemandNode.view v) .view hchild (by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private noncomputable def statementBlockChildContext {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (index : Nat) (b : Block)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.block b)) :
    EvaluationContext m plans (path ++ [index]) (DemandNode.block b) .block :=
  ec.child rfl index (DemandNode.block b) .block hchild (by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private noncomputable def statementMutationContext {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (hphase : DemandNodeHasPhase (DemandNode.statement st) .mutation) :
    EvaluationContext m plans path (DemandNode.statement st) .mutation :=
  ec.phase rfl .mutation hphase

private theorem statementActiveMatchesCongr
    {path : List Nat} {node : DemandNode} {phase : DemandPhase}
    (ec : EvaluationContext m plans path node phase) {a b : TEnv}
    (h : ec.ActiveMatches a) (hvisible : ∀ x, x ∈ a.visible ↔ x ∈ b.visible) :
    ec.ActiveMatches b := by
  cases ec with
  | pilot profile active =>
    intro x
    exact (h x).trans (hvisible x)
  | shrink profile context =>
    rename_i stmtPlanContext
    change context.ActiveMatches a at h
    change context.ActiveMatches b
    unfold NodeContext.ActiveMatches at h ⊢
    intro x
    exact (h x).trans (hvisible x)

private theorem statementOwnerRefTyOfPassable {source target : Ty}
    (passable : source.passableTo target = true) (owner : OwnerRefTy target) :
    OwnerRefTy source := by
  rcases owner with ⟨mu, element, rfl | rfl⟩ <;>
    cases source <;> simp [Ty.passableTo, Bool.and_eq_true, beq_iff_eq] at passable
  all_goals
    rcases passable with ⟨rfl, _⟩
    first | exact ⟨_, _, Or.inl rfl⟩ | exact ⟨_, _, Or.inr rfl⟩

private theorem statementChildFacts {plans : Array (Array DemandPoint)}
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (.statement st) .statement)
    (observation : Observation) (W : World) (tenv tenv' : TEnv) (penv : PEnv)
    (env : Env) (s : St) (index : Nat) (child : DemandNode) (childPhase : DemandPhase)
    (hchild : (DemandNode.statement st).child? index = some child)
    (hchildPhase : DemandNodeHasPhase child childPhase)
    (hactive : ec.ActiveMatches tenv) (haccessChild : ec.AccessMatches tenv' penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hobserved : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (hF : Frame m W tenv' penv env s ec.inputFuture)
    (hvisible : ∀ x, x ∈ tenv'.visible ↔
      x ∈ (DemandNode.statement st).visibleForChild tenv.visible index)
    (hinput : ∀ x,
      x ∈ (ec.child rfl index child childPhase hchild hchildPhase).inputFuture →
      x ∈ ec.inputFuture) :
    (ec.child rfl index child childPhase hchild hchildPhase).ActiveMatches tenv' ∧
    (ec.child rfl index child childPhase hchild hchildPhase).AccessMatches tenv' penv ∧
    ShrinkProtected W.D W.A
      ((ec.child rfl index child childPhase hchild hchildPhase).mayShrink W.ownerP observation) ∧
    ObservedSafe m W
      ((ec.child rfl index child childPhase hchild hchildPhase).mayShrink W.ownerP observation)
      observation s.store ∧
    Frame m W tenv' penv env s
      (ec.child rfl index child childPhase hchild hchildPhase).inputFuture ∧
    (∀ alias, alias ∈ ec.retained →
      alias ∈ (ec.child rfl index child childPhase hchild hchildPhase).retained) := by
  have hmay root := ec.child_mayShrink_iff rfl index child childPhase hchild hchildPhase
    W.ownerP observation root
  refine ⟨ec.child_activeMatches rfl index child childPhase hchild hchildPhase tenv tenv'
      hactive hvisible,
    (ec.child_accessMatches_iff rfl index child childPhase hchild hchildPhase tenv' penv).2
      haccessChild,
    hprotected.mono (fun _ _ h => h) (fun _ _ h => h)
      (fun root h => (hmay root).1 h),
    hobserved.weakenShrinking (fun root h => (hmay root).1 h),
    hF.narrowFuture hinput,
    ?_⟩
  intro alias hmem
  exact ec.child_retained_subset rfl index child childPhase hchild hchildPhase hmem

private theorem statementExprChildSpec (ih : Specs m prof plans n)
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv)
    (env : Env) (s : St) (index : Nat) (e : Expr)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.expression e))
    (hactive : ec.ActiveMatches tenv) (haccess : ec.AccessMatches tenv penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hobserved : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (hclassified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (hp : Perm m W) (hF : Frame m W tenv penv env s ec.inputFuture)
    (hvisible : ∀ x, x ∈ tenv.visible ↔
      x ∈ (DemandNode.statement st).visibleForChild tenv.visible index)
    (hinput : ∀ x,
      x ∈ (ec.child rfl index (DemandNode.expression e) .expression hchild (by
        simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      x ∈ ec.inputFuture)
    (tn tn' : Nat) (ty : Ty) (rst rst' : RState) (rho : List RootRef)
    (ht : tyExpr tenv e tn = .ok (ty, tn'))
    (hr : rpExpr penv e rst = .ok (rho, rst')) (hE : EffLe rst'.eff W.E) :
    Sat (evalExpr n ⟨prof, m⟩ env e) s (fun v s' =>
      Frame m W tenv penv env s'
        (ec.child rfl index (DemandNode.expression e) .expression hchild (by
          simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ HasTy m W.G s'.store v ty ∧
      (∀ r, Targets v r → Gam env W.P rho r) ∧
      OwnerRooted env W.ownerP rho v ty ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        (ec.child rfl index (DemandNode.expression e) .expression hchild (by
          simp [DemandNodeHasPhase, DemandNode.phaseMatches])).forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  let childEc := ec.child rfl index (DemandNode.expression e) .expression hchild (by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  have facts := statementChildFacts ec observation W tenv tenv penv env s index
    (DemandNode.expression e) .expression hchild (by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hactive haccess hprotected
    hobserved hF hvisible hinput
  have hmay root := ec.child_mayShrink_iff rfl index (DemandNode.expression e) .expression
    hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.ownerP observation root
  have hresult := ih.expr (path ++ [index]) e childEc observation W tenv penv env s
    tn tn' ty rst rst' rho facts.1 facts.2.1 facts.2.2.1 facts.2.2.2.1 hclassified hp
    facts.2.2.2.2.1 ht hr hE
  refine hresult.mono ?_
  intro v s' ⟨hF', hfp, hroots, hvalues, hsafe, hret, hpilot, hty, hgam, _, howner, hforbidden, hmutation⟩
  exact ⟨hF', hfp, hroots, hvalues,
    hsafe.weakenShrinking (fun root h => (hmay root).2 h),
    hret.subset (fun alias hmem => ec.child_retained_subset rfl index
      (DemandNode.expression e) .expression hchild
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem),
    hpilot, hty, hgam, howner,
    hforbidden.subset (ec.child_forbidden_subset rfl index (DemandNode.expression e)
      .expression hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])),
    hforbidden, hmutation⟩

private theorem statementViewChildSpec (ih : Specs m prof plans n)
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv)
    (env : Env) (s : St) (index : Nat) (v : View)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.view v))
    (hactive : ec.ActiveMatches tenv) (haccess : ec.AccessMatches tenv penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hobserved : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (hclassified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (hp : Perm m W) (hF : Frame m W tenv penv env s ec.inputFuture)
    (hvisible : ∀ x, x ∈ tenv.visible ↔
      x ∈ (DemandNode.statement st).visibleForChild tenv.visible index)
    (hinput : ∀ x,
      x ∈ (ec.child rfl index (DemandNode.view v) .view hchild (by
        simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      x ∈ ec.inputFuture)
    (tn tn' : Nat) (el : Ty) (mu : Bool) (rst rst' : RState) (rho : List RootRef)
    (ht : tyView tenv v tn = .ok ((el, mu), tn'))
    (hr : rpView penv v rst = .ok (rho, rst')) (hE : EffLe rst'.eff W.E) :
    Sat (evalView n ⟨prof, m⟩ env v) s (fun vw s' =>
      Frame m W tenv penv env s'
        (ec.child rfl index (DemandNode.view v) .view hchild (by
          simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ ViewOk s'.store vw el ∧
      Gam env W.P rho vw.loc.root ∧ ViewAliases m W penv env s'.store v vw el ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  let childEc := ec.child rfl index (DemandNode.view v) .view hchild (by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  have facts := statementChildFacts ec observation W tenv tenv penv env s index
    (DemandNode.view v) .view hchild (by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hactive haccess hprotected
    hobserved hF hvisible hinput
  have hmay root := ec.child_mayShrink_iff rfl index (DemandNode.view v) .view
    hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.ownerP observation root
  have hresult := ih.view (path ++ [index]) v childEc observation W tenv penv env s
    tn tn' el mu rst rst' rho facts.1 facts.2.1 facts.2.2.1 facts.2.2.2.1 hclassified hp
    facts.2.2.2.2.1 ht hr hE
  refine hresult.mono ?_
  intro vw s' ⟨hF', hfp, hroots, hvalues, hsafe, hret, hpilot, hview, hgam, haliases, _, hforbidden, hmutation⟩
  exact ⟨hF', hfp, hroots, hvalues,
    hsafe.weakenShrinking (fun root h => (hmay root).2 h),
    hret.subset (fun alias hmem => ec.child_retained_subset rfl index
      (DemandNode.view v) .view hchild
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem),
    hpilot, hview, hgam, haliases,
    hforbidden.subset (ec.child_forbidden_subset rfl index (DemandNode.view v)
      .view hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])), hmutation⟩

private theorem statementExprChildSpecAtFrame (ih : Specs m prof plans n)
    {path : List Nat} {st : Stmt}
    (ec : EvaluationContext m plans path (DemandNode.statement st) .statement)
    (observation : Observation) (W : World) (tenv tenv' : TEnv) (penv : PEnv)
    (env : Env) (s : St) (index : Nat) (e : Expr)
    (hchild : (DemandNode.statement st).child? index = some (DemandNode.expression e))
    (hactive : ec.ActiveMatches tenv) (haccess : ec.AccessMatches tenv' penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hobserved : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (hclassified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (hp : Perm m W)
    (hF : Frame m W tenv' penv env s
      (ec.child rfl index (DemandNode.expression e) .expression hchild (by
        simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture)
    (hvisible : ∀ x, x ∈ tenv'.visible ↔
      x ∈ (DemandNode.statement st).visibleForChild tenv.visible index)
    (tn tn' : Nat) (ty : Ty) (rst rst' : RState) (rho : List RootRef)
    (ht : tyExpr tenv' e tn = .ok (ty, tn'))
    (hr : rpExpr penv e rst = .ok (rho, rst')) (hE : EffLe rst'.eff W.E) :
    Sat (evalExpr n ⟨prof, m⟩ env e) s (fun v s' =>
      Frame m W tenv' penv env s'
        (ec.child rfl index (DemandNode.expression e) .expression hchild (by
          simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ HasTy m W.G s'.store v ty ∧
      (∀ r, Targets v r → Gam env W.P rho r) ∧
      OwnerRooted env W.ownerP rho v ty ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        (ec.child rfl index (DemandNode.expression e) .expression hchild (by
          simp [DemandNodeHasPhase, DemandNode.phaseMatches])).forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  let childEc := ec.child rfl index (DemandNode.expression e) .expression hchild (by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  have hmay root := ec.child_mayShrink_iff rfl index (DemandNode.expression e) .expression
    hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.ownerP observation root
  have hactiveChild := ec.child_activeMatches rfl index (DemandNode.expression e) .expression
    hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv tenv' hactive hvisible
  have haccessChild := (ec.child_accessMatches_iff rfl index (DemandNode.expression e) .expression
    hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv' penv).2 haccess
  have hprotectedChild := hprotected.mono (fun _ _ h => h) (fun _ _ h => h)
    (fun root h => (hmay root).1 h)
  have hobservedChild := hobserved.weakenShrinking (fun root h => (hmay root).1 h)
  have hresult := ih.expr (path ++ [index]) e childEc observation W tenv' penv env s
    tn tn' ty rst rst' rho hactiveChild haccessChild hprotectedChild hobservedChild
    hclassified hp hF ht hr hE
  refine hresult.mono ?_
  intro v s' ⟨hF', hfp, hroots, hvalues, hsafe, hret, hpilot, hty, hgam, _, howner, hforbidden, hmutation⟩
  exact ⟨hF', hfp, hroots, hvalues,
    hsafe.weakenShrinking (fun root h => (hmay root).2 h),
    hret.subset (fun alias hmem => ec.child_retained_subset rfl index
      (DemandNode.expression e) .expression hchild
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem),
    hpilot, hty, hgam, howner,
    hforbidden.subset (ec.child_forbidden_subset rfl index (DemandNode.expression e)
      .expression hchild (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])),
    hforbidden, hmutation⟩

private theorem statementIfBlockInputFrame
    {path : List Nat} {c : Expr} {t : Block} {f : Option Block} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.ifS c t f o)) .statement)
    (index : Nat) (b : Block)
    (hcond : (DemandNode.statement (.ifS c t f o)).child? 0 =
      some (DemandNode.expression c))
    (hblock : (DemandNode.statement (.ifS c t f o)).child? index =
      some (DemandNode.block b))
    (hblockVars : ∀ x, x ∈ b.variables →
      x ∈ t.variables ++ f.toList.flatMap Block.variables)
    (hactive : ec.ActiveMatches tenv)
    (hFcond : Frame m W tenv penv env s
      (ec.child rfl 0 (DemandNode.expression c) .expression hcond
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Frame m W tenv penv env s
      (ec.child rfl index (DemandNode.block b) .block hblock
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture := by
  have hcondPhase : DemandNodeHasPhase (DemandNode.expression c) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hblockPhase : DemandNodeHasPhase (DemandNode.block b) .block := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile active =>
    have hFactive : Frame m W tenv penv env s active := by
      change Frame m W tenv penv env s
        ((DemandNode.expression c).visibleAfter
          ((DemandNode.statement (.ifS c t f o)).visibleForChild active 0)) at hFcond
      simpa [DemandNode.visibleForChild, DemandNode.visibleAfter] using hFcond
    have hFbranch : Frame m W tenv penv env s (b.variables ++ active) := by
      have hchanged := hFactive.changeFuture (future' := b.variables ++ active) (by
        intro x hxvisible _
        exact (hactive x).2 hxvisible)
      change Frame m W tenv penv env s
        (b.variables ++ (DemandNode.statement (.ifS c t f o)).visibleForChild active index)
      simpa [DemandNode.visibleForChild] using hchanged
    exact hFbranch
  | shrink profile context =>
    rename_i stmtPlanContext
    let condTransition := context.child rfl 0 (DemandNode.expression c) .expression hcond hcondPhase
    let blockTransition := context.child rfl index (DemandNode.block b) .block hblock hblockPhase
    have hcondExpectation :
        (DemandNode.statement (.ifS c t f o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.ifS c t f o)).visibleForChild
                context.expected.frame.active 0,
              (t.variables ++ f.toList.flatMap Block.variables) ++
                context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hcond]
    have hcondFuture := DemandNode.childFrame_future condTransition.childFrameEq hcondExpectation
    have hcondFutureEq : condTransition.context.expected.frame.future =
        (t.variables ++ f.toList.flatMap Block.variables) ++ context.expected.frame.future := by
      rw [condTransition.expectedFrameEq, DemandNode.phaseFrame_future condTransition.phaseFrameEq,
        hcondFuture]
      simp [DemandNode.phaseFuture]
    have hFbranch : Frame m W tenv penv env s
        ((t.variables ++ f.toList.flatMap Block.variables) ++ context.expected.frame.future) := by
      change Frame m W tenv penv env s condTransition.context.expected.frame.future at hFcond
      rw [← hcondFutureEq]
      exact hFcond
    have hindex : index = 1 ∨ index = 2 := by
      cases index with
      | zero => simp [DemandNode.child?, DemandNode.children] at hblock
      | succ index =>
        cases index with
        | zero => exact Or.inl rfl
        | succ index =>
          cases index with
          | zero => exact Or.inr rfl
          | succ index => simp [DemandNode.child?, DemandNode.children] at hblock
    have hblockExpectation :
        (DemandNode.statement (.ifS c t f o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ index = some ⟨
              (DemandNode.statement (.ifS c t f o)).visibleForChild
                context.expected.frame.active index,
              context.expected.frame.future⟩ := by
      rcases hindex with hindex | hindex
      · subst index
        simp [DemandNode.childExpectation?, DemandNode.childFuture,
          DemandNode.child?, DemandNode.children] at hblock ⊢
      · subst index
        have hf : f = some b := by
          simpa [DemandNode.child?, DemandNode.children] using hblock
        simp [DemandNode.childExpectation?, DemandNode.childFuture,
          DemandNode.child?, DemandNode.children, hf]
    have hblockFuture := DemandNode.childFrame_future blockTransition.childFrameEq hblockExpectation
    have hblockFutureEq : blockTransition.context.expected.frame.future =
        context.expected.frame.future := by
      rw [blockTransition.expectedFrameEq,
        DemandNode.phaseFrame_future blockTransition.phaseFrameEq, hblockFuture]
      simp [DemandNode.phaseFuture]
    have hsubset : ∀ x, x ∈ b.variables ++ context.expected.frame.future →
        x ∈ (t.variables ++ f.toList.flatMap Block.variables) ++ context.expected.frame.future := by
      intro x hx
      simp only [List.mem_append] at hx ⊢
      rcases hx with hbody | hfuture
      · have hbody' : x ∈ t.variables ++ f.toList.flatMap Block.variables := hblockVars x hbody
        simp only [List.mem_append] at hbody'
        rcases hbody' with hthen | helse
        · exact Or.inl (Or.inl hthen)
        · exact Or.inl (Or.inr helse)
      · exact Or.inr hfuture
    have hFchild : Frame m W tenv penv env s
        (b.variables ++ blockTransition.context.expected.frame.future) := by
      rw [hblockFutureEq]
      exact hFbranch.narrowFuture hsubset
    change Frame m W tenv penv env s
      (b.variables ++ blockTransition.context.expected.frame.future)
    exact hFchild

private theorem statementIfConditionInputSubset
    {path : List Nat} {c : Expr} {t : Block} {f : Option Block} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.ifS c t f o)) .statement)
    (hcond : (DemandNode.statement (.ifS c t f o)).child? 0 =
      some (DemandNode.expression c)) :
    ∀ x, x ∈ (ec.child rfl 0 (DemandNode.expression c) .expression hcond
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      x ∈ ec.inputFuture := by
  have hcondPhase : DemandNodeHasPhase (DemandNode.expression c) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hvariables : (Stmt.ifS c t f o).variables =
      c.variables ++ (t.variables ++ f.toList.flatMap Block.variables) := by
    cases f <;> simp [Stmt.variables]
  have hprimary : DemandPhase.statement =
      (DemandNode.statement (.ifS c t f o)).primaryPhase := by
    simp [DemandNode.primaryPhase]
  cases ec with
  | pilot profile active =>
    let parent : EvaluationContext m plans path (.statement (.ifS c t f o)) .statement :=
      .pilot profile active
    have hchildInput := EvaluationContext.child_inputFuture parent
      hprimary 0 (DemandNode.expression c) .expression hcond hcondPhase
    intro x hx
    rw [hchildInput] at hx
    simp [parent] at hx
    have hchild : x ∈ c.variables ++ active := by
      simpa [DemandNode.variables, DemandNode.visibleForChild] using hx
    have hparent : x ∈
        (c.variables ++ (t.variables ++ f.toList.flatMap Block.variables)) ++ active := by
      rcases List.mem_append.mp hchild with hc | ha
      · exact List.mem_append_left _ (List.mem_append_left _ hc)
      · exact List.mem_append_right _ ha
    simpa only [parent, EvaluationContext.inputFuture, DemandNode.variables, hvariables] using hparent
  | shrink profile context =>
    rename_i stmtPlanContext
    let parent : EvaluationContext m plans path (.statement (.ifS c t f o)) .statement :=
      .shrink profile context
    let transition := context.child hprimary 0 (DemandNode.expression c) .expression hcond hcondPhase
    have hchildInput := EvaluationContext.child_inputFuture parent
      hprimary 0 (DemandNode.expression c) .expression hcond hcondPhase
    have hexpectation :
        (DemandNode.statement (.ifS c t f o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.ifS c t f o)).visibleForChild
                context.expected.frame.active 0,
              (t.variables ++ f.toList.flatMap Block.variables) ++
                context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hcond]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    intro x hx
    rw [hchildInput] at hx
    simp [parent] at hx
    rw [hfuture] at hx
    simp [DemandNode.phaseFuture] at hx
    have hchild : x ∈ c.variables ++
        ((t.variables ++ f.toList.flatMap Block.variables) ++ context.expected.frame.future) := by
      simpa [DemandNode.variables, List.append_assoc] using hx
    have hparent : x ∈
        (c.variables ++ (t.variables ++ f.toList.flatMap Block.variables)) ++
          context.expected.frame.future := by
      rcases List.mem_append.mp hchild with hc | rest
      · exact List.mem_append_left _ (List.mem_append_left _ hc)
      · rcases List.mem_append.mp rest with hbranch | hfuture
        · rcases List.mem_append.mp hbranch with ht | hf
          · exact List.mem_append_left _ (List.mem_append_right _
              (List.mem_append_left _ ht))
          · exact List.mem_append_left _ (List.mem_append_right _
              (List.mem_append_right _ hf))
        · exact List.mem_append_right _ hfuture
    simpa only [parent, EvaluationContext.inputFuture, DemandNode.variables, NodeContext.inputFuture,
      hvariables] using hparent

private theorem statementIfConditionOutputSubset
    {path : List Nat} {c : Expr} {t : Block} {f : Option Block} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.ifS c t f o)) .statement)
    (hcond : (DemandNode.statement (.ifS c t f o)).child? 0 =
      some (DemandNode.expression c)) :
    ∀ x, x ∈ ec.outputFuture →
      x ∈ (ec.child rfl 0 (DemandNode.expression c) .expression hcond
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture := by
  have hcondPhase : DemandNodeHasPhase (DemandNode.expression c) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile active =>
    intro x hx
    change x ∈ active at hx
    change x ∈ (DemandNode.expression c).visibleAfter
      ((DemandNode.statement (.ifS c t f o)).visibleForChild active 0)
    simpa [DemandNode.visibleForChild, DemandNode.visibleAfter] using hx
  | shrink profile context =>
    rename_i stmtPlanContext
    let transition := context.child rfl 0 (DemandNode.expression c) .expression hcond hcondPhase
    have hexpectation :
        (DemandNode.statement (.ifS c t f o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.ifS c t f o)).visibleForChild
                context.expected.frame.active 0,
              (t.variables ++ f.toList.flatMap Block.variables) ++
                context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hcond]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    have hcondFutureEq : transition.context.expected.frame.future =
        (t.variables ++ f.toList.flatMap Block.variables) ++ context.expected.frame.future := by
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
        hfuture]
      simp [DemandNode.phaseFuture]
    intro x hx
    change x ∈ context.expected.frame.future at hx
    change x ∈ transition.context.expected.frame.future
    rw [hcondFutureEq]
    exact List.mem_append_right _ hx

private theorem statementIfBlockOutputFuture
    {path : List Nat} {c : Expr} {t : Block} {f : Option Block} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.ifS c t f o)) .statement)
    (index : Nat) (b : Block)
    (hblock : (DemandNode.statement (.ifS c t f o)).child? index =
      some (DemandNode.block b)) :
    (ec.child rfl index (DemandNode.block b) .block hblock
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture = ec.outputFuture := by
  have hblockPhase : DemandNodeHasPhase (DemandNode.block b) .block := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hindex : index = 1 ∨ index = 2 := by
    cases index with
    | zero => simp [DemandNode.child?, DemandNode.children] at hblock
    | succ index =>
      cases index with
      | zero => exact Or.inl rfl
      | succ index =>
        cases index with
        | zero => exact Or.inr rfl
        | succ index => simp [DemandNode.child?, DemandNode.children] at hblock
  cases ec with
  | pilot profile active =>
    change (DemandNode.block b).visibleAfter
      ((DemandNode.statement (.ifS c t f o)).visibleForChild active index) =
      (DemandNode.statement (.ifS c t f o)).visibleAfter active
    simp [DemandNode.visibleForChild, DemandNode.visibleAfter]
  | shrink profile context =>
    rename_i stmtPlanContext
    let transition := context.child rfl index (DemandNode.block b) .block hblock hblockPhase
    have hblockExpectation :
        (DemandNode.statement (.ifS c t f o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ index = some ⟨
              (DemandNode.statement (.ifS c t f o)).visibleForChild
                context.expected.frame.active index,
              context.expected.frame.future⟩ := by
      rcases hindex with hindex | hindex
      · subst index
        simp [DemandNode.childExpectation?, DemandNode.childFuture,
          DemandNode.child?, DemandNode.children] at hblock ⊢
      · subst index
        have hf : f = some b := by
          simpa [DemandNode.child?, DemandNode.children] using hblock
        simp [DemandNode.childExpectation?, DemandNode.childFuture,
          DemandNode.child?, DemandNode.children, hf]
    have hblockFuture := DemandNode.childFrame_future transition.childFrameEq hblockExpectation
    change transition.context.expected.frame.future = context.expected.frame.future
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
      hblockFuture]
    simp [DemandNode.phaseFuture]

private theorem statementRangeLowerInputSubset
    {path : List Nat} {x : VarId} {lo hi : Expr} {body : Block} {o : OriginId}
    (ec : EvaluationContext m plans path
      (.statement (.forRange x lo hi body o)) .statement) :
    ∀ y, y ∈ (ec.child rfl 0 (DemandNode.expression lo) .expression
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      y ∈ ec.inputFuture := by
  have hchild : (DemandNode.statement (.forRange x lo hi body o)).child? 0 =
      some (DemandNode.expression lo) := by
    simp [DemandNode.child?, DemandNode.children]
  have hchildPhase : DemandNodeHasPhase (DemandNode.expression lo) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hvariables : (Stmt.forRange x lo hi body o).variables =
      lo.variables ++ (hi.variables ++ body.variables) := by
    simp [Stmt.variables]
  cases ec with
  | pilot profile active =>
    intro y hy
    have hchild : y ∈ lo.variables ++ active := by
      simpa [EvaluationContext.child, EvaluationContext.inputFuture,
        DemandNode.variables, DemandNode.visibleForChild] using hy
    have hparent : y ∈ (lo.variables ++ (hi.variables ++ body.variables)) ++ active := by
      rcases List.mem_append.mp hchild with hlo | hactive
      · exact List.mem_append_left _ (List.mem_append_left _ hlo)
      · exact List.mem_append_right _ hactive
    simpa [EvaluationContext.inputFuture, DemandNode.variables, hvariables] using hparent
  | shrink profile context =>
    rename_i stmtPlanContext
    let transition := context.child rfl 0 (DemandNode.expression lo) .expression hchild hchildPhase
    have hchildEc :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.expression lo) .expression hchild hchildPhase) =
          .shrink profile transition.context := rfl
    have hexpectation :
        (DemandNode.statement (.forRange x lo hi body o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.forRange x lo hi body o)).visibleForChild
                context.expected.frame.active 0,
              (hi.variables ++ body.variables) ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    intro y hy
    rw [hchildEc] at hy
    change y ∈ lo.variables ++ transition.context.expected.frame.future at hy
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
      hfuture] at hy
    simp [DemandNode.phaseFuture] at hy
    have hchild : y ∈ lo.variables ++
        ((hi.variables ++ body.variables) ++ context.expected.frame.future) := by
      simpa [List.append_assoc] using hy
    have hparent : y ∈
        (lo.variables ++ (hi.variables ++ body.variables)) ++ context.expected.frame.future := by
      rcases List.mem_append.mp hchild with hlo | rest
      · exact List.mem_append_left _ (List.mem_append_left _ hlo)
      · rcases List.mem_append.mp rest with hlater | hfuture
        · rcases List.mem_append.mp hlater with hhi | hbody
          · exact List.mem_append_left _ (List.mem_append_right _
              (List.mem_append_left _ hhi))
          · exact List.mem_append_left _ (List.mem_append_right _
              (List.mem_append_right _ hbody))
        · exact List.mem_append_right _ hfuture
    simpa [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, hvariables] using hparent

private theorem statementRangeUpperInputSubset
    {path : List Nat} {x : VarId} {lo hi : Expr} {body : Block} {o : OriginId}
    (ec : EvaluationContext m plans path
      (.statement (.forRange x lo hi body o)) .statement) :
    ∀ y, y ∈ (ec.child rfl 1 (DemandNode.expression hi) .expression
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      y ∈ ec.inputFuture := by
  have hchild : (DemandNode.statement (.forRange x lo hi body o)).child? 1 =
      some (DemandNode.expression hi) := by
    simp [DemandNode.child?, DemandNode.children]
  have hchildPhase : DemandNodeHasPhase (DemandNode.expression hi) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hvariables : (Stmt.forRange x lo hi body o).variables =
      lo.variables ++ (hi.variables ++ body.variables) := by
    simp [Stmt.variables]
  cases ec with
  | pilot profile active =>
    intro y hy
    have hchild : y ∈ hi.variables ++ active := by
      simpa [EvaluationContext.child, EvaluationContext.inputFuture,
        DemandNode.variables, DemandNode.visibleForChild] using hy
    have hparent : y ∈ (lo.variables ++ (hi.variables ++ body.variables)) ++ active := by
      rcases List.mem_append.mp hchild with hhi | hactive
      · exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_append_left _ hhi))
      · exact List.mem_append_right _ hactive
    simpa [EvaluationContext.inputFuture, DemandNode.variables, hvariables] using hparent
  | shrink profile context =>
    rename_i stmtPlanContext
    let transition := context.child rfl 1 (DemandNode.expression hi) .expression hchild hchildPhase
    have hchildEc :
        ((EvaluationContext.shrink profile context).child rfl 1
          (DemandNode.expression hi) .expression hchild hchildPhase) =
          .shrink profile transition.context := rfl
    have hexpectation :
        (DemandNode.statement (.forRange x lo hi body o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 1 = some ⟨
              (DemandNode.statement (.forRange x lo hi body o)).visibleForChild
                context.expected.frame.active 1,
              body.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    intro y hy
    rw [hchildEc] at hy
    change y ∈ hi.variables ++ transition.context.expected.frame.future at hy
    rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
      hfuture] at hy
    simp [DemandNode.phaseFuture] at hy
    have hchild : y ∈ hi.variables ++ (body.variables ++ context.expected.frame.future) := by
      simpa [List.append_assoc] using hy
    have hparent : y ∈
        (lo.variables ++ (hi.variables ++ body.variables)) ++ context.expected.frame.future := by
      rcases List.mem_append.mp hchild with hhi | rest
      · exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_append_left _ hhi))
      · rcases List.mem_append.mp rest with hbody | hfuture
        · exact List.mem_append_left _ (List.mem_append_right _
            (List.mem_append_right _ hbody))
        · exact List.mem_append_right _ hfuture
    simpa [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, hvariables] using hparent

private theorem statementRangeUpperInputFrame
    {path : List Nat} {x : VarId} {lo hi : Expr} {body : Block} {o : OriginId}
    (ec : EvaluationContext m plans path
      (.statement (.forRange x lo hi body o)) .statement)
    (hactive : ec.ActiveMatches tenv)
    (hFLo : Frame m W tenv penv env s
      (ec.child rfl 0 (DemandNode.expression lo) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Frame m W tenv penv env s
      (ec.child rfl 1 (DemandNode.expression hi) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture := by
  have hchildLo : (DemandNode.statement (.forRange x lo hi body o)).child? 0 =
      some (DemandNode.expression lo) := by
    simp [DemandNode.child?, DemandNode.children]
  have hchildHi : (DemandNode.statement (.forRange x lo hi body o)).child? 1 =
      some (DemandNode.expression hi) := by
    simp [DemandNode.child?, DemandNode.children]
  have hchildPhaseLo : DemandNodeHasPhase (DemandNode.expression lo) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hchildPhaseHi : DemandNodeHasPhase (DemandNode.expression hi) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile active =>
    have hFactive : Frame m W tenv penv env s active := by
      change Frame m W tenv penv env s
        ((DemandNode.expression lo).visibleAfter
          ((DemandNode.statement (.forRange x lo hi body o)).visibleForChild active 0)) at hFLo
      simpa [DemandNode.visibleForChild, DemandNode.visibleAfter] using hFLo
    have hFhi : Frame m W tenv penv env s (hi.variables ++ active) := by
      have hchanged := hFactive.changeFuture (future' := hi.variables ++ active) (by
        intro y hyvisible _
        exact (hactive y).2 hyvisible)
      simpa [EvaluationContext.child, EvaluationContext.inputFuture,
        DemandNode.variables, DemandNode.visibleForChild] using hchanged
    simpa [EvaluationContext.child, EvaluationContext.inputFuture,
      DemandNode.variables, DemandNode.visibleForChild] using hFhi
  | shrink profile context =>
    rename_i stmtPlanContext
    let transitionLo := context.child rfl 0 (DemandNode.expression lo) .expression
      hchildLo hchildPhaseLo
    let transitionHi := context.child rfl 1 (DemandNode.expression hi) .expression
      hchildHi hchildPhaseHi
    have hloExpectation :
        (DemandNode.statement (.forRange x lo hi body o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.forRange x lo hi body o)).visibleForChild
                context.expected.frame.active 0,
              (hi.variables ++ body.variables) ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildLo]
    have hhiExpectation :
        (DemandNode.statement (.forRange x lo hi body o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 1 = some ⟨
              (DemandNode.statement (.forRange x lo hi body o)).visibleForChild
                context.expected.frame.active 1,
              body.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildHi]
    have hloFuture := DemandNode.childFrame_future transitionLo.childFrameEq hloExpectation
    have hhiFuture := DemandNode.childFrame_future transitionHi.childFrameEq hhiExpectation
    have hloFutureEq : transitionLo.context.expected.frame.future =
        (hi.variables ++ body.variables) ++ context.expected.frame.future := by
      rw [transitionLo.expectedFrameEq,
        DemandNode.phaseFrame_future transitionLo.phaseFrameEq, hloFuture]
      simp [DemandNode.phaseFuture]
    have hhiFutureEq : transitionHi.context.expected.frame.future =
        body.variables ++ context.expected.frame.future := by
      rw [transitionHi.expectedFrameEq,
        DemandNode.phaseFrame_future transitionHi.phaseFrameEq, hhiFuture]
      simp [DemandNode.phaseFuture]
    have hloContext :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.expression lo) .expression hchildLo hchildPhaseLo) =
          .shrink profile transitionLo.context := rfl
    have hhiContext :
        ((EvaluationContext.shrink profile context).child rfl 1
          (DemandNode.expression hi) .expression hchildHi hchildPhaseHi) =
          .shrink profile transitionHi.context := rfl
    rw [hloContext] at hFLo
    change Frame m W tenv penv env s transitionLo.context.expected.frame.future at hFLo
    rw [hloFutureEq] at hFLo
    have hFhi : Frame m W tenv penv env s
        (hi.variables ++ (body.variables ++ context.expected.frame.future)) := by
      simpa [List.append_assoc] using hFLo
    rw [hhiContext]
    change Frame m W tenv penv env s
      (hi.variables ++ transitionHi.context.expected.frame.future)
    rw [hhiFutureEq]
    exact hFhi

private theorem statementRangeBodyInputFrame
    {path : List Nat} {x : VarId} {lo hi : Expr} {body : Block} {o : OriginId}
    (ec : EvaluationContext m plans path
      (.statement (.forRange x lo hi body o)) .statement)
    (hactive : ec.ActiveMatches tenv)
    (hFHi : Frame m W tenv penv env s
      (ec.child rfl 1 (DemandNode.expression hi) .expression
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Frame m W tenv penv env s (body.variables ++ ec.outputFuture) := by
  have hchildHi : (DemandNode.statement (.forRange x lo hi body o)).child? 1 =
      some (DemandNode.expression hi) := by
    simp [DemandNode.child?, DemandNode.children]
  have hchildPhaseHi : DemandNodeHasPhase (DemandNode.expression hi) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile active =>
    have hFactive : Frame m W tenv penv env s active := by
      change Frame m W tenv penv env s
        ((DemandNode.expression hi).visibleAfter
          ((DemandNode.statement (.forRange x lo hi body o)).visibleForChild active 1)) at hFHi
      simpa [DemandNode.visibleForChild, DemandNode.visibleAfter] using hFHi
    have hchanged := hFactive.changeFuture (future' := body.variables ++ active) (by
      intro y hyvisible _
      exact (hactive y).2 hyvisible)
    simpa [EvaluationContext.outputFuture, DemandNode.visibleAfter] using hchanged
  | shrink profile context =>
    rename_i stmtPlanContext
    let transition := context.child rfl 1 (DemandNode.expression hi) .expression
      hchildHi hchildPhaseHi
    have hexpectation :
        (DemandNode.statement (.forRange x lo hi body o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 1 = some ⟨
              (DemandNode.statement (.forRange x lo hi body o)).visibleForChild
                context.expected.frame.active 1,
              body.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchildHi]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    have hfutureEq :
        ((EvaluationContext.shrink profile context).child rfl 1
          (DemandNode.expression hi) .expression hchildHi hchildPhaseHi).outputFuture =
          body.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change transition.context.expected.frame.future =
        body.variables ++ context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
        hfuture]
      simp [DemandNode.phaseFuture]
    rw [hfutureEq] at hFHi
    exact hFHi

private theorem statementForEachViewInputSubset
    {path : List Nat} {x : VarId} {idx : Option VarId} {v : View}
    {byRef : Bool} {body : Block} {o : OriginId}
    (ec : EvaluationContext m plans path
      (.statement (.forEach x idx v byRef body o)) .statement) :
    ∀ y, y ∈ (ec.child rfl 0 (DemandNode.view v) .view
      (by simp [DemandNode.child?, DemandNode.children])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).inputFuture →
      y ∈ ec.inputFuture := by
  have hchild : (DemandNode.statement (.forEach x idx v byRef body o)).child? 0 =
      some (DemandNode.view v) := by
    simp [DemandNode.child?, DemandNode.children]
  have hchildPhase : DemandNodeHasPhase (DemandNode.view v) .view := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hvariables : (Stmt.forEach x idx v byRef body o).variables =
      v.variables ++ body.variables := by
    simp [Stmt.variables]
  cases ec with
  | pilot profile active =>
    intro y hy
    change y ∈ v.variables ++
      (DemandNode.statement (.forEach x idx v byRef body o)).visibleForChild active 0 at hy
    have hchild : y ∈ v.variables ++ active := by
      simpa [DemandNode.visibleForChild] using hy
    have hparent : y ∈ (v.variables ++ body.variables) ++ active := by
      rcases List.mem_append.mp hchild with hv | hactive
      · exact List.mem_append_left _ (List.mem_append_left _ hv)
      · exact List.mem_append_right _ hactive
    simpa [EvaluationContext.inputFuture, DemandNode.variables, hvariables] using hparent
  | shrink profile context =>
    rename_i stmtPlanContext
    let transition := context.child rfl 0 (DemandNode.view v) .view hchild hchildPhase
    have hexpectation :
        (DemandNode.statement (.forEach x idx v byRef body o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.forEach x idx v byRef body o)).visibleForChild
                context.expected.frame.active 0,
              body.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    have hchildInput :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.view v) .view hchild hchildPhase).inputFuture =
        v.variables ++ (body.variables ++ context.expected.frame.future) := by
      change v.variables ++ transition.context.expected.frame.future = _
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
        hfuture]
      simp [DemandNode.phaseFuture]
    intro y hy
    rw [hchildInput] at hy
    have hparent : y ∈ (v.variables ++ body.variables) ++ context.expected.frame.future := by
      rcases List.mem_append.mp hy with hv | rest
      · exact List.mem_append_left _ (List.mem_append_left _ hv)
      · rcases List.mem_append.mp rest with hbody | hfuture
        · exact List.mem_append_left _ (List.mem_append_right _ hbody)
        · exact List.mem_append_right _ hfuture
    simpa [EvaluationContext.inputFuture, NodeContext.inputFuture,
      DemandNode.variables, hvariables] using hparent

private theorem statementForEachBodyInputFrame
    {path : List Nat} {x : VarId} {idx : Option VarId} {v : View}
    {byRef : Bool} {body : Block} {o : OriginId}
    (ec : EvaluationContext m plans path
      (.statement (.forEach x idx v byRef body o)) .statement)
    (hactive : ec.ActiveMatches tenv)
    (hFView : Frame m W tenv penv env s
      (ec.child rfl 0 (DemandNode.view v) .view
        (by simp [DemandNode.child?, DemandNode.children])
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture) :
    Frame m W tenv penv env s (body.variables ++ ec.outputFuture) := by
  have hchild : (DemandNode.statement (.forEach x idx v byRef body o)).child? 0 =
      some (DemandNode.view v) := by
    simp [DemandNode.child?, DemandNode.children]
  have hchildPhase : DemandNodeHasPhase (DemandNode.view v) .view := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  cases ec with
  | pilot profile active =>
    have hFactive : Frame m W tenv penv env s active := by
      change Frame m W tenv penv env s ((DemandNode.view v).visibleAfter
        ((DemandNode.statement (.forEach x idx v byRef body o)).visibleForChild active 0)) at hFView
      simpa [DemandNode.visibleAfter, DemandNode.visibleForChild] using hFView
    have hchanged := hFactive.changeFuture (future' := body.variables ++ active) (by
      intro y hyvisible _
      exact (hactive y).2 hyvisible)
    simpa [EvaluationContext.outputFuture, DemandNode.visibleAfter] using hchanged
  | shrink profile context =>
    rename_i stmtPlanContext
    let transition := context.child rfl 0 (DemandNode.view v) .view hchild hchildPhase
    have hexpectation :
        (DemandNode.statement (.forEach x idx v byRef body o)).childExpectation?
          stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
            context.expected.frame.retained⟩ 0 = some ⟨
              (DemandNode.statement (.forEach x idx v byRef body o)).visibleForChild
                context.expected.frame.active 0,
              body.variables ++ context.expected.frame.future⟩ := by
      simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
    have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
    have hfutureEq :
        ((EvaluationContext.shrink profile context).child rfl 0
          (DemandNode.view v) .view hchild hchildPhase).outputFuture =
          body.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
      change transition.context.expected.frame.future =
        body.variables ++ context.expected.frame.future
      rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
        hfuture]
      simp [DemandNode.phaseFuture]
    rw [hfutureEq] at hFView
    exact hFView

private theorem statementIfBlockSpec (W : World) (hB : BlockSpec m prof plans n) (hp : Perm m W)
    {path : List Nat} {c : Expr} {t : Block} {f : Option Block} {o : OriginId}
    (ec : EvaluationContext m plans path (.statement (.ifS c t f o)) .statement)
    (observation : Observation) (tenv : TEnv) (penv : PEnv)
    (env : Env) (s : St) (index : Nat) (b : Block)
    (hcond : (DemandNode.statement (.ifS c t f o)).child? 0 =
      some (DemandNode.expression c))
    (hblock : (DemandNode.statement (.ifS c t f o)).child? index =
      some (DemandNode.block b))
    (hblockVars : ∀ x, x ∈ b.variables →
      x ∈ t.variables ++ f.toList.flatMap Block.variables)
    (hactive : ec.ActiveMatches tenv) (haccess : ec.AccessMatches tenv penv)
    (hprotected : ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation))
    (hobserved : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store)
    (hclassified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (hFcond : Frame m W tenv penv env s
      ((ec.child rfl 0 (DemandNode.expression c) .expression hcond
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture))
    {tn tn' : Nat} {ty : Ty} {rst rst' : RState} {rho : List RootRef} {rng : Nat × Nat}
    (ht : tyBlock tenv [] b tn = .ok (ty, tn'))
    (hr : rpBlockValue penv [] b rst = .ok ((rho, rng), rst'))
    (hE : EffLe rst'.eff W.E) :
    Sat (execBlock n ⟨prof, m⟩ env [] b) s (fun fl s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s' ∧
      match fl with
      | .normal v => HasTy m W.G s'.store v ty ∧
          (∀ r, Targets v r → Gam env W.P rho r) ∧ b.diverges m.noReturn = false ∧
          OwnerRooted env W.ownerP rho v ty
      | .brk => tenv.loops ≠ 0 ∧ b.hasBreak = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) := by
  have hcondPhase : DemandNodeHasPhase (DemandNode.expression c) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hblockPhase : DemandNodeHasPhase (DemandNode.block b) .block := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let blockEc := ec.child rfl index (DemandNode.block b) .block hblock hblockPhase
  have hvisible : ∀ x, x ∈ tenv.visible ↔
      x ∈ (DemandNode.statement (.ifS c t f o)).visibleForChild tenv.visible index := by
    simp [DemandNode.visibleForChild]
  have hactiveBlock := ec.child_activeMatches rfl index (DemandNode.block b) .block hblock
    hblockPhase tenv tenv hactive hvisible
  have hactivePre : ∀ env1 tn1,
      declarePre { tenv with scopes := b.scope :: tenv.scopes } b.scope [] tn = .ok (env1, tn1) →
        blockEc.ActiveMatches env1 := by
    intro env1 tn1 hdeclare
    obtain ⟨_, hvis, _, _⟩ := declarePre_ok _ _ _ _ _ _ hdeclare
    have hvis' : ∀ x, x ∈ tenv.visible ↔ x ∈ env1.visible := by
      intro x
      simpa using (hvis x).symm
    exact statementActiveMatchesCongr blockEc hactiveBlock hvis'
  have haccessBlock : blockEc.AccessMatches tenv penv :=
    (ec.child_accessMatches_iff rfl index (DemandNode.block b) .block hblock hblockPhase
      tenv penv).2 haccess
  have hmay := ec.child_mayShrink_iff rfl index (DemandNode.block b) .block
    hblock hblockPhase W.ownerP observation
  have hprotectedBlock : ShrinkProtected W.D W.A (blockEc.mayShrink W.ownerP observation) :=
    hprotected.mono (fun _ _ h => h) (fun _ _ h => h)
      (fun root h => (hmay root).1 h)
  have hobservedBlock := hobserved.weakenShrinking
    (fun root h => (hmay root).1 h)
  have hFblock := statementIfBlockInputFrame ec index b hcond hblock hblockVars hactive hFcond
  have hresultBlock := block_of_checks hB hp b blockEc observation [] [] hactivePre haccessBlock
    hprotectedBlock hobservedBlock hclassified hFblock ht hr hE rfl rfl (by
      intro k x v ty' hpre hpreT lv hvar hty
      simp at hpre)
  refine hresultBlock.mono ?_
  rintro fl s' ⟨hF', hfp, hroots, hvalues, hsafe, hret, hpilot, hflow, _, hforbidden, hmutation⟩
  have houtput := statementIfBlockOutputFuture ec index b hblock
  have hsafe' : ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store :=
    hsafe.weakenShrinking (fun root h => (hmay root).2 h)
  have hretained : ∀ alias, alias ∈ ec.retained → alias ∈ blockEc.retained :=
    fun alias hmem => ec.child_retained_subset rfl index (DemandNode.block b) .block
      hblock hblockPhase hmem
  have hret' := hret.subset hretained
  refine ⟨houtput ▸ hF', hfp, hroots, hvalues, hsafe', hret', hpilot,
    hforbidden.subset (ec.child_forbidden_subset rfl index (DemandNode.block b)
      .block hblock hblockPhase), hmutation, ?_⟩
  cases fl with
  | normal v => exact ⟨hflow.1, hflow.2.1, hflow.2.2.1, hflow.2.2.2⟩
  | brk => exact ⟨hflow.1, hflow.2⟩
  | cont => exact hflow
  | ret v => exact hflow

set_option maxHeartbeats 1600000 in
private theorem step_stmt_b_core (ih : Specs m prof plans n) :
    ∀ (path : List Nat) (st : Stmt)
    (ec : EvaluationContext m plans path (.statement st) .statement)
    (observation : Observation) (W : World) (tenv tenv' : TEnv) (penv : PEnv) (env : Env) (s : St) (sc : Nat)
    (tn tn' : Nat) (rst rst' : RState) (lo : Nat),
    (match st with
      | .letS .. | .assign .. | .assignOp .. | .rebind .. | .expr .. | .append .. |
        .popN .. | .resize .. | .clear .. | .assignWhole .. => False
      | _ => True) →
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation) →
    ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture → tenv.scopes.head? = some sc → TopB env lo rst.nextVar s →
    lo ≤ rst.nextVar →
    tyStmt tenv sc st tn = .ok (tenv', tn') → rpStmt penv st rst = .ok ((), rst') →
    EffLe rst'.eff W.E →
    Sat (execStmt (n + 1) ⟨prof, m⟩ env st) s (fun fl s' =>
      Frame m W tenv' penv env s' ec.outputFuture ∧ FootprintS env (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ TSame tenv tenv' ∧ TopB env lo rst'.nextVar s' ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s' ∧
      match fl with
      | .normal _ => st.diverges m.noReturn = false
      | .brk => tenv.loops ≠ 0 ∧ st.hasBreak = true
      | .cont => tenv.loops ≠ 0
      | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) := by
  intro path st ec observation W tenv tenv' penv env s sc tn tn' rst rst' lo
    hsel hactive haccess hprotected hobserved hclassified hp hF hsc hT hlo ht hr hE
  have hcur := (rpStmt_mono hr).1
  cases st with
  | ifS c t f o =>
    cases f with
    | none =>
      simp only [tyStmt] at ht; inv at ht
      simp only [rpStmt] at hr; inv at hr
      obtain ⟨_, tc, t1, htc, rfl, tt, t2, htt, rfl, rfl⟩ := ht
      obtain ⟨rc, r1, hrc, rt, l1, l2, hrt⟩ := hr
      have hcondChild : (DemandNode.statement (.ifS c t none o)).child? 0 =
          some (DemandNode.expression c) := by
        simp [DemandNode.child?, DemandNode.children]
      have hcondVisible : ∀ x, x ∈ tenv'.visible ↔
          x ∈ (DemandNode.statement (.ifS c t none o)).visibleForChild tenv'.visible 0 := by
        simp [DemandNode.visibleForChild]
      have hcond := statementExprChildSpec ih ec observation W tenv' penv env s 0 c hcondChild
        hactive haccess hprotected hobserved hclassified hp hF hcondVisible
        (statementIfConditionInputSubset ec hcondChild) _ _ _ _ _ _ htc hrc
        ((rpBlockValue_mono hrt).2.trans hE)
      simp only [execStmt]
      refine Sat.bind hcond ?_
      rintro vc s1 ⟨hF1, hfp1, hroots1, hvalues1, hsafe1, hret1, hpilot1, hv, _, _, hforbidden1, _, hmutation1⟩
      obtain ⟨x, rfl⟩ := hasTy_bool hv
      simp only [expectBool, sat_pure_bind]
      cases x
      · simp only [Bool.false_eq_true, if_false, sat_pure_bind, sat_pure]
        have hFout : Frame m W tenv' penv env s1 ec.outputFuture :=
          hF1.narrowFuture (statementIfConditionOutputSubset ec hcondChild)
        exact ⟨hFout, hfp1.toS, hroots1, hvalues1, hsafe1, hret1, hpilot1,
          TSame.refl _, hT.ext hfp1.dom hcur, hforbidden1,
          hmutation1.weaken (effectMutationRoots.mono m penv.impl
            (rpBlockValue_mono hrt).2 (rpBlockValue_rebinds_mono hrt)), rfl⟩
      · simp only [if_true]
        have hblock : (DemandNode.statement (.ifS c t none o)).child? 1 =
            some (DemandNode.block t) := by
          simp [DemandNode.child?, DemandNode.children]
        have hblockVars : ∀ x, x ∈ t.variables →
            x ∈ t.variables ++ none.toList.flatMap Block.variables := by
          intro x hx
          simp [hx]
        have hrunBlock := statementIfBlockSpec W ih.block hp ec observation tenv' penv env s1
          1 t hcondChild hblock hblockVars hactive haccess hprotected hsafe1
          (fun hprof => hF.classifiedParameters_advance (hclassified hprof) hfp1)
          hF1 htt hrt hE
        refine Sat.bind hrunBlock ?_
        rintro fl s2 ⟨hF2, hfp2, hroots2, hvalues2, hsafe2, hret2, hpilot2, hforbidden2, hmutation2, hfl⟩
        have hfp := hfp1.trans hfp2
        have hroots := hroots1.trans hroots2
        have hvalues := hvalues1.trans hvalues2
        have hret := hret1.trans hret2
        have hpilot : PilotStoreLe m s s2 := fun hprof =>
          StoreLe.trans (hpilot1 hprof) (hpilot2 hprof)
        have hforbidden := hforbidden1.trans hforbidden2
        have hmutation := (hmutation1.weaken (effectMutationRoots.mono m penv.impl
          (rpBlockValue_mono hrt).2 (rpBlockValue_rebinds_mono hrt))).trans hmutation2
        cases fl with
        | normal v =>
          simp only [sat_pure]
          exact ⟨hF2, hfp.toS, hroots, hvalues, hsafe2, hret, hpilot, TSame.refl _,
            hT.ext hfp.dom hcur, hforbidden, hmutation, rfl⟩
        | brk =>
          simp only [sat_pure]
          exact ⟨hF2, hfp.toS, hroots, hvalues, hsafe2, hret, hpilot, TSame.refl _,
            hT.ext hfp.dom hcur, hforbidden, hmutation, hfl.1, by simp [Stmt.hasBreak, hfl.2]⟩
        | cont =>
          simp only [sat_pure]
          exact ⟨hF2, hfp.toS, hroots, hvalues, hsafe2, hret, hpilot, TSame.refl _,
            hT.ext hfp.dom hcur, hforbidden, hmutation, hfl⟩
        | ret v =>
          simp only [sat_pure]
          exact ⟨hF2, hfp.toS, hroots, hvalues, hsafe2, hret, hpilot, TSame.refl _,
            hT.ext hfp.dom hcur, hforbidden, hmutation, hfl⟩
    | some fb =>
      simp only [tyStmt] at ht; inv at ht
      simp only [rpStmt] at hr; inv at hr
      obtain ⟨_, tc, t1, htc, rfl, tt, t2, htt, ft, t3, htf, rfl, rfl⟩ := ht
      obtain ⟨rc, r1, hrc, rt, l1, l2, r2, hrt, rf, k1, k2, hrf⟩ := hr
      have hE2 := (rpBlockValue_mono hrf).2.trans hE
      have hcondChild : (DemandNode.statement (.ifS c t (some fb) o)).child? 0 =
          some (DemandNode.expression c) := by
        simp [DemandNode.child?, DemandNode.children]
      have hcondVisible : ∀ x, x ∈ tenv'.visible ↔
          x ∈ (DemandNode.statement (.ifS c t (some fb) o)).visibleForChild tenv'.visible 0 := by
        simp [DemandNode.visibleForChild]
      have hcond := statementExprChildSpec ih ec observation W tenv' penv env s 0 c hcondChild
        hactive haccess hprotected hobserved hclassified hp hF hcondVisible
        (statementIfConditionInputSubset ec hcondChild) _ _ _ _ _ _ htc hrc
        ((rpBlockValue_mono hrt).2.trans hE2)
      simp only [execStmt]
      refine Sat.bind hcond ?_
      rintro vc s1 ⟨hF1, hfp1, hroots1, hvalues1, hsafe1, hret1, hpilot1, hv, _, _, hforbidden1, _, hmutation1⟩
      obtain ⟨x, rfl⟩ := hasTy_bool hv
      simp only [expectBool, sat_pure_bind]
      cases x
      · simp only [Bool.false_eq_true, if_false]
        have hblock : (DemandNode.statement (.ifS c t (some fb) o)).child? 2 =
            some (DemandNode.block fb) := by
          simp [DemandNode.child?, DemandNode.children]
        have hblockVars : ∀ x, x ∈ fb.variables →
            x ∈ t.variables ++ (some fb).toList.flatMap Block.variables := by
          intro x hx
          simp [hx]
        have hrunBlock := statementIfBlockSpec W ih.block hp ec observation tenv' penv env s1
          2 fb hcondChild hblock hblockVars hactive haccess hprotected hsafe1
          (fun hprof => hF.classifiedParameters_advance (hclassified hprof) hfp1)
          hF1 htf hrf hE
        refine Sat.bind hrunBlock ?_
        rintro fl s2 ⟨hF2, hfp2, hroots2, hvalues2, hsafe2, hret2, hpilot2, hforbidden2, hmutation2, hfl⟩
        have hfp := hfp1.trans hfp2
        have hroots := hroots1.trans hroots2
        have hvalues := hvalues1.trans hvalues2
        have hret := hret1.trans hret2
        have hpilot : PilotStoreLe m s s2 := fun hprof =>
          StoreLe.trans (hpilot1 hprof) (hpilot2 hprof)
        have hforbidden := hforbidden1.trans hforbidden2
        have hmutation := (hmutation1.weaken (effectMutationRoots.mono m penv.impl
          ((rpBlockValue_mono hrt).2.trans (rpBlockValue_mono hrf).2)
          (fun target hmem => rpBlockValue_rebinds_mono hrf target
            (rpBlockValue_rebinds_mono hrt target hmem)))).trans hmutation2
        cases fl with
        | normal v =>
          simp only [sat_pure]
          exact ⟨hF2, hfp.toS, hroots, hvalues, hsafe2, hret, hpilot, TSame.refl _,
            hT.ext hfp.dom hcur, hforbidden, hmutation, by simp [Stmt.diverges, hfl.2.2.1]⟩
        | brk =>
          simp only [sat_pure]
          exact ⟨hF2, hfp.toS, hroots, hvalues, hsafe2, hret, hpilot, TSame.refl _,
            hT.ext hfp.dom hcur, hforbidden, hmutation, hfl.1, by simp [Stmt.hasBreak, hfl.2]⟩
        | cont =>
          simp only [sat_pure]
          exact ⟨hF2, hfp.toS, hroots, hvalues, hsafe2, hret, hpilot, TSame.refl _,
            hT.ext hfp.dom hcur, hforbidden, hmutation, hfl⟩
        | ret v =>
          simp only [sat_pure]
          exact ⟨hF2, hfp.toS, hroots, hvalues, hsafe2, hret, hpilot, TSame.refl _,
            hT.ext hfp.dom hcur, hforbidden, hmutation, hfl⟩
      · simp only [if_true]
        have hblock : (DemandNode.statement (.ifS c t (some fb) o)).child? 1 =
            some (DemandNode.block t) := by
          simp [DemandNode.child?, DemandNode.children]
        have hblockVars : ∀ x, x ∈ t.variables →
            x ∈ t.variables ++ (some fb).toList.flatMap Block.variables := by
          intro x hx
          simp [hx]
        have hrunBlock := statementIfBlockSpec W ih.block hp ec observation tenv' penv env s1
          1 t hcondChild hblock hblockVars hactive haccess hprotected hsafe1
          (fun hprof => hF.classifiedParameters_advance (hclassified hprof) hfp1)
          hF1 htt hrt hE2
        refine Sat.bind hrunBlock ?_
        rintro fl s2 ⟨hF2, hfp2, hroots2, hvalues2, hsafe2, hret2, hpilot2, hforbidden2, hmutation2, hfl⟩
        have hfp := hfp1.trans hfp2
        have hroots := hroots1.trans hroots2
        have hvalues := hvalues1.trans hvalues2
        have hret := hret1.trans hret2
        have hpilot : PilotStoreLe m s s2 := fun hprof =>
          StoreLe.trans (hpilot1 hprof) (hpilot2 hprof)
        have hforbidden := hforbidden1.trans hforbidden2
        have hmutation := ((hmutation1.weaken (effectMutationRoots.mono m penv.impl
          (rpBlockValue_mono hrt).2 (rpBlockValue_rebinds_mono hrt))).trans hmutation2).weaken
          (effectMutationRoots.mono m penv.impl (rpBlockValue_mono hrf).2
            (rpBlockValue_rebinds_mono hrf))
        cases fl with
        | normal v =>
          simp only [sat_pure]
          exact ⟨hF2, hfp.toS, hroots, hvalues, hsafe2, hret, hpilot, TSame.refl _,
            hT.ext hfp.dom hcur, hforbidden, hmutation, by simp [Stmt.diverges, hfl.2.2.1]⟩
        | brk =>
          simp only [sat_pure]
          exact ⟨hF2, hfp.toS, hroots, hvalues, hsafe2, hret, hpilot, TSame.refl _,
            hT.ext hfp.dom hcur, hforbidden, hmutation, hfl.1, by simp [Stmt.hasBreak, hfl.2]⟩
        | cont =>
          simp only [sat_pure]
          exact ⟨hF2, hfp.toS, hroots, hvalues, hsafe2, hret, hpilot, TSame.refl _,
            hT.ext hfp.dom hcur, hforbidden, hmutation, hfl⟩
        | ret v =>
          simp only [sat_pure]
          exact ⟨hF2, hfp.toS, hroots, hvalues, hsafe2, hret, hpilot, TSame.refl _,
            hT.ext hfp.dom hcur, hforbidden, hmutation, hfl⟩
  | «while» c b o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, tc, t1, htc, rfl, bt, t2, htb, rfl, rfl⟩ := ht
    obtain ⟨rc, r1, hrc, rb, l1, l2, hrb⟩ := hr
    simp only [execStmt]
    refine (ih.while_ path c b o ec observation W tenv' penv env s _ _ _ _ _ _ _ _ _ _
      hactive haccess hprotected hobserved hclassified hp hF htc htb hrc hrb hE).mono ?_
    rintro fl s1 ⟨hF1, hfp, hroots, hvalues, hsafe, hret, hpilot, hfl, hdv, _, hforbidden, hmutation⟩
    refine ⟨hF1, hfp.toS, hroots, hvalues, hsafe, hret, hpilot,
      TSame.refl _, hT.ext hfp.dom hcur, hforbidden, hmutation, ?_⟩
    cases fl with
    | normal v => exact while_diverges c b o (hdv v rfl)
    | brk => exact hfl.elim
    | cont => exact hfl.elim
    | ret v => exact hfl
  | forRange x lo' hi b o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, lv, t0, hd, tl, t1, htl, it, rfl, th, t2, hth, iu, rfl, rfl, hlty, bt, t3, htb, rfl,
      rfl⟩ := ht
    obtain ⟨hxn, rl, r1, hrl, rh, r2, hrh, rb, l1, l2, r3, hrb, hck, rfl⟩ := hr
    obtain ⟨_, hlv, hlsc, _, _⟩ := declare_ok _ _ _ _ _ hd
    simp only at hlv hlsc
    rw [hF.vars_t] at hlv
    have hlty' : lv.ty = .int it := by simpa using hlty
    have hrng := rpBlockValue_rng _ _ _ _ _ _ _ hrb
    simp only at hrng
    have hk0 : ∀ y, RootRef.local y ∈ rb → ¬ (x ≤ y ∧ y < r2.nextVar) := by
      intro y hy
      have := checkBlockValue_ok _ _ _ hck y hy
      rw [hxn, ← hrng]; exact this
    have hxlt : x < r2.nextVar := by
      rw [hxn]
      exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (rpExpr_mono hrl).1)
        (rpExpr_mono hrh).1
    have hE2 := (rpBlockValue_mono hrb).2.trans hE
    simp only [execStmt]
    have hchildLo : (DemandNode.statement (.forRange x lo' hi b o)).child? 0 =
        some (DemandNode.expression lo') := by
      simp [DemandNode.child?, DemandNode.children]
    have hchildHi : (DemandNode.statement (.forRange x lo' hi b o)).child? 1 =
        some (DemandNode.expression hi) := by
      simp [DemandNode.child?, DemandNode.children]
    have hvisibleLo : ∀ y, y ∈ tenv'.visible ↔
        y ∈ (DemandNode.statement (.forRange x lo' hi b o)).visibleForChild tenv'.visible 0 := by
      simp [DemandNode.visibleForChild]
    have hvisibleHi : ∀ y, y ∈ tenv'.visible ↔
        y ∈ (DemandNode.statement (.forRange x lo' hi b o)).visibleForChild tenv'.visible 1 := by
      simp [DemandNode.visibleForChild]
    have hresultLo := statementExprChildSpec ih ec observation W tenv' penv env s 0 lo'
      hchildLo hactive haccess hprotected hobserved hclassified hp hF hvisibleLo
      (statementRangeLowerInputSubset ec) _ _ _ _ _ _ htl hrl
      ((rpExpr_mono hrh).2.trans hE2)
    refine Sat.bind hresultLo ?_
    rintro va s1 ⟨hF1, hfp1, hroots1, hvalues1, hsafe1, hret1, hpilot1, hv, _, _, hforbidden1, _, hmutation1⟩
    have hclassified1 : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s1.store := by
      intro hprofile
      exact hF.classifiedParameters_advance (hclassified hprofile) hfp1
    obtain ⟨a, rfl⟩ := hasTy_int hv
    simp only [expectInt, sat_pure_bind]
    have hFHi := statementRangeUpperInputFrame ec hactive hF1
    have hresultHi := statementExprChildSpecAtFrame ih ec observation W tenv' tenv' penv env s1 1 hi
      hchildHi hactive haccess hprotected hsafe1 hclassified1 hp hFHi hvisibleHi
      _ _ _ _ _ _ hth hrh hE2
    refine Sat.bind hresultHi ?_
    rintro vb s2 ⟨hF2, hfp2, hroots2, hvalues2, hsafe2, hret2, hpilot2, hv2, _, _, hforbidden2, _, hmutation2⟩
    have hclassified2 : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s2.store := by
      intro hprofile
      exact hF1.classifiedParameters_advance (hclassified1 hprofile) hfp2
    obtain ⟨b', rfl⟩ := hasTy_int hv2
    simp only [expectInt, sat_pure_bind, expectSameTy, if_true]
    have hFbody := statementRangeBodyInputFrame ec hactive hF2
    refine (ih.range path x lo' hi b o ec observation W tenv' penv env s2 it a b'
      _ _ _ _ _ _ _ hactive haccess hprotected hsafe2 hclassified2 hp hFbody
      ⟨lv, hlv, hlsc, hlty'⟩ hxlt htb hrb hE hk0).mono ?_
    rintro fl s3 ⟨hF3, hfp3, hroots3, hvalues3, hsafe3, hret3, hpilot3, hfl, _, hforbidden3, hmutation3⟩
    have hfp := (hfp1.trans hfp2).trans hfp3
    have hroots := (hroots1.trans hroots2).trans hroots3
    have hvalues := (hvalues1.trans hvalues2).trans hvalues3
    have hret := (hret1.trans hret2).trans hret3
    have hpilot : PilotStoreLe m s s3 := fun hprof =>
      StoreLe.trans (hpilot1 hprof) (StoreLe.trans (hpilot2 hprof) (hpilot3 hprof))
    have hforbidden := (hforbidden1.trans hforbidden2).trans hforbidden3
    have hmutation := (((hmutation1.weaken (effectMutationRoots.mono m penv.impl
      (rpExpr_mono hrh).2 (rpExpr_rebinds_mono hrh))).trans hmutation2).weaken
      (effectMutationRoots.mono m penv.impl (rpBlockValue_mono hrb).2
        (rpBlockValue_rebinds_mono hrb))).trans hmutation3
    refine ⟨hF3, hfp.toS, hroots, hvalues, hsafe3, hret, hpilot,
      TSame.refl _, hT.ext hfp.dom hcur, hforbidden, hmutation, ?_⟩
    cases fl with
    | normal v => rfl
    | brk => exact hfl.elim
    | cont => exact hfl.elim
    | ret v => exact hfl
  | forEach x idx v byRef b o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, lv, t0, hd, t1, hdi, el, mu, t2, htv, t3, hlo, bt, t4, htb, rfl, rfl⟩ := ht
    obtain ⟨hxi, rv, r1, hrv, hr⟩ := hr
    obtain ⟨hxt, hlv, hlsc, hst, ht0⟩ := declare_ok _ _ _ _ _ hd
    simp only at hlv hlsc hst ht0
    rw [hF.vars_t] at hlv
    obtain ⟨_, hjs⟩ := declareIndex_ok _ _ _ _ _ hdi
    obtain ⟨_, hxty⟩ := loopVarOk_ok _ _ _ _ _ _ hlo
    have hxn : x = rst.nextVar := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hxi
      exact hxi.1
    have hj : ∀ j, idx = some j → j = x + 1 ∧ ∃ lj, env.vars[j]? = some lj ∧ lj.scope = b.scope ∧
        lj.ty = .int .i64 := by
      intro j e
      obtain ⟨g1, lj, g2, g3, g4⟩ := hjs j e
      rw [hF.vars_t] at g2
      exact ⟨by rw [g1, ht0, hxt], lj, g2, g3, g4⟩
    have hlt1 : x + idx.toList.length < r1.nextVar := by
      have h2 := (rpView_mono hrv).1
      rw [hxn]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right (Nat.lt_succ_self _) _) h2
    have hchildView : (DemandNode.statement (.forEach x idx v byRef b o)).child? 0 =
        some (DemandNode.view v) := by
      simp [DemandNode.child?, DemandNode.children]
    have hvisibleView : ∀ y, y ∈ tenv'.visible ↔
        y ∈ (DemandNode.statement (.forEach x idx v byRef b o)).visibleForChild
          tenv'.visible 0 := by
      simp [DemandNode.visibleForChild]
    have hinputView := statementForEachViewInputSubset ec
    simp only [execStmt]
    rcases hr with ⟨hb1, hbr, rb, l1, l2, r2, hrb, hck, rfl⟩ | ⟨hb1, r2, hrd, rb, l1, l2, r3, hrb, hck, rfl⟩
    · subst hb1
      have hrng := rpBlockValue_rng _ _ _ _ _ _ _ hrb
      simp only at hrng
      have hk0 : ∀ y, RootRef.local y ∈ rb → ¬ (x ≤ y ∧ y < r1.nextVar) := by
        intro y hy
        have := checkBlockValue_ok _ _ _ hck y hy
        rw [hxn, ← hrng]; exact this
      have hresultView := statementViewChildSpec ih ec observation W tenv' penv env s 0 v
        hchildView hactive haccess hprotected hobserved hclassified hp hF hvisibleView hinputView
        _ _ _ _ _ _ _ htv hrv ((rpBlockValue_mono hrb).2.trans hE)
      refine Sat.bind hresultView ?_
      rintro vw s1 ⟨hF1, hfp1, hroots1, hvalues1, hsafe1, hret1, hpilot1,
        hvw, hg, haliases, hforbidden1, hmutation1⟩
      have hclassified1 : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s1.store := by
        intro hprofile
        exact hF.classifiedParameters_advance (hclassified hprofile) hfp1
      have hFEach := statementForEachBodyInputFrame ec hactive hF1
      refine (ih.each (path) x idx v true b o ec observation W tenv' penv env s1 vw 0 el rv
        _ _ _ _ _ _ _ hactive haccess hprotected hsafe1 hclassified1 hp hFEach hvw.eachView haliases hg
        ⟨lv, hlv, hlsc, hst, by rw [if_pos rfl]; exact ⟨by simpa using hxty, hbr⟩⟩
        hj hlt1 htb hrb hE hk0).mono ?_
      rintro fl s3 ⟨hF3, hfp3, hroots3, hvalues3, hsafe3, hret3, hpilot3, hfl, _, hforbidden3, hmutation3⟩
      have hfp := hfp1.trans hfp3
      have hroots := hroots1.trans hroots3
      have hvalues := hvalues1.trans hvalues3
      have hret := hret1.trans hret3
      have hpilot : PilotStoreLe m s s3 := fun hprof =>
        StoreLe.trans (hpilot1 hprof) (hpilot3 hprof)
      have hforbidden := hforbidden1.trans hforbidden3
      have hmutation := (hmutation1.weaken (effectMutationRoots.mono m penv.impl
        (rpBlockValue_mono hrb).2 (rpBlockValue_rebinds_mono hrb))).trans hmutation3
      refine ⟨hF3, hfp.toS, hroots, hvalues, hsafe3, hret, hpilot,
        TSame.refl _, hT.ext hfp.dom hcur, hforbidden, hmutation, ?_⟩
      cases fl with
      | normal v => rfl
      | brk => exact hfl.elim
      | cont => exact hfl.elim
      | ret v => exact hfl
    · have hbf : byRef = false := by simpa using hb1
      subst hbf
      have hrng := rpBlockValue_rng _ _ _ _ _ _ _ hrb
      simp only at hrng
      have hnv := (addReads_ok _ _ _ hrd).1
      simp only at hnv
      have hk0 : ∀ y, RootRef.local y ∈ rb → ¬ (x ≤ y ∧ y < r2.nextVar) := by
        intro y hy
        have := checkBlockValue_ok _ _ _ hck y hy
        rw [hxn, ← hrng]; exact this
      have hresultView := statementViewChildSpec ih ec observation W tenv' penv env s 0 v
        hchildView hactive haccess hprotected hobserved hclassified hp hF hvisibleView hinputView
        _ _ _ _ _ _ _ htv hrv
        ((PMono.addReads _ _ _ _ hrd).2.trans ((rpBlockValue_mono hrb).2.trans hE))
      refine Sat.bind hresultView ?_
      rintro vw s1 ⟨hF1, hfp1, hroots1, hvalues1, hsafe1, hret1, hpilot1,
        hvw, hg, haliases, hforbidden1, hmutation1⟩
      have hclassified1 : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s1.store := by
        intro hprofile
        exact hF.classifiedParameters_advance (hclassified hprofile) hfp1
      have hFEach := statementForEachBodyInputFrame ec hactive hF1
      refine (ih.each (path) x idx v false b o ec observation W tenv' penv env s1 vw 0 el rv
        _ _ _ _ _ _ _ hactive haccess hprotected hsafe1 hclassified1 hp hFEach hvw.eachView haliases hg
        ⟨lv, hlv, hlsc, hst, by simpa using hxty⟩ hj (by rw [hnv]; exact hlt1)
        htb hrb hE hk0).mono ?_
      rintro fl s3 ⟨hF3, hfp3, hroots3, hvalues3, hsafe3, hret3, hpilot3, hfl, _, hforbidden3, hmutation3⟩
      have hfp := hfp1.trans hfp3
      have hroots := hroots1.trans hroots3
      have hvalues := hvalues1.trans hvalues3
      have hret := hret1.trans hret3
      have hpilot : PilotStoreLe m s s3 := fun hprof =>
        StoreLe.trans (hpilot1 hprof) (hpilot3 hprof)
      have hforbidden := hforbidden1.trans hforbidden3
      have hmutation := (hmutation1.weaken (effectMutationRoots.mono m penv.impl
        ((PMono.addReads _ _ _ _ hrd).2.trans (rpBlockValue_mono hrb).2)
        (fun target hmem => rpBlockValue_rebinds_mono hrb target
          (PMonoRebinds.addReads _ _ _ _ hrd target hmem)))).trans hmutation3
      refine ⟨hF3, hfp.toS, hroots, hvalues, hsafe3, hret, hpilot,
        TSame.refl _, hT.ext hfp.dom hcur, hforbidden, hmutation, ?_⟩
      cases fl with
      | normal v => rfl
      | brk => exact hfl.elim
      | cont => exact hfl.elim
      | ret v => exact hfl
  | ret e o =>
    cases e with
    | none =>
      simp only [tyStmt] at ht; inv at ht
      simp only [rpStmt] at hr; inv at hr
      obtain ⟨_, t1, hru, rfl, rfl⟩ := ht
      subst hr
      obtain ⟨_, hne', impl, himpl, hres⟩ := retUnit_ok _ _ _ hru
      simp only [execStmt, sat_pure]
      have hfuture : ec.inputFuture = ec.outputFuture := by
        cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
          NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
          Stmt.variables, DemandNode.visibleAfter]
      have hF' : Frame m W tenv' penv env s ec.outputFuture := by
        rw [← hfuture]
        exact hF
      exact ⟨hF', FootprintS.refl env (Dset W) s, PreservesRootTypes.refl _,
        PreservesValues.refl _, hobserved, RetainsAliases.refl, fun _ => StoreLe.refl _,
        TSame.refl _, hT.ext (fun _ h => h) hcur, PreservesForbiddenOwnerRoots.refl _,
        MutationFootprint.refl _ _ _ _ _, hne', impl, himpl,
        Or.inl ⟨hres, rfl⟩, (fun r hr' => hr'.elim), (by
          intro t ht
          rw [hres] at ht
          cases ht)⟩
    | some e' =>
      simp only [tyStmt] at ht; inv at ht
      simp only [rpStmt] at hr; inv at hr
      obtain ⟨_, t, t0, hrt, te, t1, hte, heq, rfl, rfl⟩ := ht
      obtain ⟨rho, r1, hre, hck, rfl⟩ := hr
      obtain ⟨ht0, hne', impl, himpl, hres⟩ := retTy_ok _ _ _ hrt
      simp only at ht0 hres
      subst ht0
      obtain ⟨hnl, declared, hd, hsub⟩ := checkResultV_ok _ _ hck
      simp only [execStmt]
      have hchild : (DemandNode.statement (.ret (some e') o)).child? 0 =
          some (DemandNode.expression e') := by
        simp [DemandNode.child?, DemandNode.children]
      have hchildPhase : DemandNodeHasPhase (DemandNode.expression e') .expression := by
        simp [DemandNodeHasPhase, DemandNode.phaseMatches]
      let childEc := statementExprChildContext ec 0 e' hchild
      have hvisible : ∀ x, x ∈ tenv'.visible ↔
          x ∈ (DemandNode.statement (.ret (some e') o)).visibleForChild tenv'.visible 0 := by
        simp [DemandNode.visibleForChild]
      have hinput : ∀ x, x ∈ childEc.inputFuture → x ∈ ec.inputFuture := by
        intro x hx
        cases ec with
        | pilot profile active =>
          change x ∈ e'.variables ++ (DemandNode.statement (.ret (some e') o)).visibleForChild active 0 at hx
          change x ∈ (DemandNode.statement (.ret (some e') o)).variables ++ active
          simpa [DemandNode.variables, Stmt.variables, DemandNode.visibleForChild] using hx
        | shrink profile context =>
          rename_i stmtPlanContext
          let transition := context.child rfl 0 (DemandNode.expression e') .expression hchild hchildPhase
          have hchildContext : childEc = .shrink profile transition.context := rfl
          have hexpectation : DemandNode.childExpectation?
              (DemandNode.statement (.ret (some e') o))
              stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
                context.expected.frame.retained⟩ 0 = some ⟨
                  (DemandNode.statement (.ret (some e') o)).visibleForChild context.expected.frame.active 0,
                  context.expected.frame.future⟩ := by
            simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
          have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
          rw [hchildContext] at hx
          change x ∈ e'.variables ++ transition.context.expected.frame.future at hx
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
            hfuture] at hx
          simp [DemandNode.phaseFuture] at hx
          change x ∈ (DemandNode.statement (.ret (some e') o)).variables ++ context.expected.frame.future
          simpa [DemandNode.variables, Stmt.variables] using hx
      have hresult := statementExprChildSpec ih ec observation W tenv' penv env s 0 e' hchild
        hactive haccess hprotected hobserved hclassified hp hF hvisible hinput _ _ _ _ _ _ hte hre hE
      have houtput : childEc.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active =>
          change (DemandNode.expression e').visibleAfter
            ((DemandNode.statement (.ret (some e') o)).visibleForChild active 0) =
            (DemandNode.statement (.ret (some e') o)).visibleAfter active
          simp [DemandNode.visibleForChild, DemandNode.visibleAfter]
        | shrink profile context =>
          rename_i stmtPlanContext
          let transition := context.child rfl 0 (DemandNode.expression e') .expression hchild hchildPhase
          have hexpectation : DemandNode.childExpectation?
              (DemandNode.statement (.ret (some e') o))
              stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
                context.expected.frame.retained⟩ 0 = some ⟨
                  (DemandNode.statement (.ret (some e') o)).visibleForChild context.expected.frame.active 0,
                  context.expected.frame.future⟩ := by
            simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
          have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
            hfuture]
          simp [DemandNode.phaseFuture]
      refine Sat.bind hresult ?_
      rintro v s1 ⟨hF1, hfp, hroots, hvalues, hsafe, hret, hpilot, hv0, hg, howner, hforbidden, hforbiddenChild, hmutation⟩
      have hv := hasTy_passable hv0 heq
      simp only [sat_pure]
      exact ⟨houtput ▸ hF1, hfp.toS, hroots, hvalues, hsafe, hret, hpilot,
        TSame.refl _, hT.ext hfp.dom hcur, hforbidden, hmutation, hne', impl, himpl, Or.inr ⟨_, hres, hv⟩,
        (fun r hr' => ⟨declared, hd, (gam_noEnv (hg r hr') hnl).subset hsub⟩), (by
          intro result hresult
          have hrtype : result = t := by simpa [hres] using hresult.symm
          subst result
          refine ⟨declared, hd, ?_⟩
          intro ho r hr
          exact (gam_noEnv (howner (statementOwnerRefTyOfPassable heq ho) r hr) hnl).subset hsub)⟩
  | brk o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, hl, rfl, rfl⟩ := ht
    subst hr
    simp only [execStmt, sat_pure]
    have hfuture : ec.inputFuture = ec.outputFuture := by
      cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
        Stmt.variables, DemandNode.visibleAfter]
    have hF' : Frame m W tenv' penv env s ec.outputFuture := by
      rw [← hfuture]
      exact hF
    exact ⟨hF', FootprintS.refl env (Dset W) s, PreservesRootTypes.refl _,
      PreservesValues.refl _, hobserved, RetainsAliases.refl, fun _ => StoreLe.refl _,
      TSame.refl _, hT.ext (fun _ h => h) hcur, PreservesForbiddenOwnerRoots.refl _,
        MutationFootprint.refl _ _ _ _ _, hl, rfl⟩
  | cont o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, hl, rfl, rfl⟩ := ht
    subst hr
    simp only [execStmt, sat_pure]
    have hfuture : ec.inputFuture = ec.outputFuture := by
      cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
        Stmt.variables, DemandNode.visibleAfter]
    have hF' : Frame m W tenv' penv env s ec.outputFuture := by
      rw [← hfuture]
      exact hF
    exact ⟨hF', FootprintS.refl env (Dset W) s, PreservesRootTypes.refl _,
      PreservesValues.refl _, hobserved, RetainsAliases.refl, fun _ => StoreLe.refl _,
      TSame.refl _, hT.ext (fun _ h => h) hcur, PreservesForbiddenOwnerRoots.refl _,
        MutationFootprint.refl _ _ _ _ _, hl⟩
  | print args o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, t1, htp, rfl, rfl⟩ := ht
    obtain ⟨r1, hrp, hno⟩ := hr
    simp only [execStmt]
    refine Sat.bind (printArgs_spec ih.printArg hp args o ec observation hactive haccess
      hprotected hobserved hclassified hF htp hrp ((PMono.noteOutputs _ _ _ hno).2.trans hE)) ?_
    rintro parts s1 ⟨hF1, hfp, hroots, hvalues, hsafe, hret, hpilot, _, hforbidden, hmutation⟩
    simp only [sat_emit_bind, sat_pure]
    have htrace := Ext.of_eq (is := insts env) (D := Dset W) (s := s1)
      (s' := { s1 with trace := s1.trace ++ (String.join parts ++ "\n") }) rfl rfl
    have hX := hfp.trans htrace.toFootprint
    exact ⟨hF1.of_eq rfl rfl, hX.toS, hroots, hvalues, hsafe, hret, hpilot,
      TSame.refl _, hT.ext hX.dom hcur, hforbidden,
      (by
        have heq := (st_modify_ok _ _ _).1 hno
        cases heq
        exact hmutation), rfl⟩
  | assertS e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, te, t1, hte, rfl, rfl, rfl⟩ := ht
    obtain ⟨re, r1, hre, hna⟩ := hr
    simp only [execStmt]
    have hchild : (DemandNode.statement (.assertS e o)).child? 0 =
        some (DemandNode.expression e) := by
      simp [DemandNode.child?, DemandNode.children]
    have hchildPhase : DemandNodeHasPhase (DemandNode.expression e) .expression := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let childEc := statementExprChildContext ec 0 e hchild
    have hvisible : ∀ x, x ∈ tenv'.visible ↔
        x ∈ (DemandNode.statement (.assertS e o)).visibleForChild tenv'.visible 0 := by
      simp [DemandNode.visibleForChild]
    have hinput : ∀ x, x ∈ childEc.inputFuture → x ∈ ec.inputFuture := by
      intro x hx
      cases ec with
      | pilot profile active =>
        change x ∈ e.variables ++ (DemandNode.statement (.assertS e o)).visibleForChild active 0 at hx
        change x ∈ (DemandNode.statement (.assertS e o)).variables ++ active
        simpa [DemandNode.variables, Stmt.variables, DemandNode.visibleForChild] using hx
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 0 (DemandNode.expression e) .expression hchild hchildPhase
        have hchildContext : childEc = .shrink profile transition.context := rfl
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.assertS e o))
            stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 0 = some ⟨
                (DemandNode.statement (.assertS e o)).visibleForChild context.expected.frame.active 0,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        rw [hchildContext] at hx
        change x ∈ e.variables ++ transition.context.expected.frame.future at hx
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture] at hx
        simp [DemandNode.phaseFuture] at hx
        change x ∈ (DemandNode.statement (.assertS e o)).variables ++ context.expected.frame.future
        simpa [DemandNode.variables, Stmt.variables] using hx
    have hresult := statementExprChildSpec ih ec observation W tenv' penv env s 0 e hchild
      hactive haccess hprotected hobserved hclassified hp hF hvisible hinput _ _ _ _ _ _ hte hre
      ((PMono.noteAborts _ _ _ hna).2.trans hE)
    have houtput : childEc.outputFuture = ec.outputFuture := by
      cases ec with
      | pilot profile active =>
        change (DemandNode.expression e).visibleAfter
          ((DemandNode.statement (.assertS e o)).visibleForChild active 0) =
          (DemandNode.statement (.assertS e o)).visibleAfter active
        simp [DemandNode.visibleForChild, DemandNode.visibleAfter]
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 0 (DemandNode.expression e) .expression hchild hchildPhase
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.assertS e o))
            stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 0 = some ⟨
                (DemandNode.statement (.assertS e o)).visibleForChild context.expected.frame.active 0,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture]
        simp [DemandNode.phaseFuture]
    refine Sat.bind hresult ?_
    rintro v s1 ⟨hF1, hfp, hroots, hvalues, hsafe, hret, hpilot, hv, _, _, hforbidden, _, hmutation⟩
    obtain ⟨x, rfl⟩ := hasTy_bool hv
    simp only [expectBool, sat_pure_bind]
    cases x
    · simp only [Bool.false_eq_true, if_false, sat_abort]
    · simp only [if_true, sat_pure]
      exact ⟨houtput ▸ hF1, hfp.toS, hroots, hvalues, hsafe, hret, hpilot,
        TSame.refl _, hT.ext hfp.dom hcur, hforbidden, (by
          have heq := (st_modify_ok _ _ _).1 hna
          cases heq
          exact hmutation), rfl⟩
  | abort msg o =>
    simp only [execStmt, sat_abort]
  | exit e o =>
    simp only [tyStmt] at ht; inv at ht
    simp only [rpStmt] at hr; inv at hr
    obtain ⟨_, te, t1, hte, it, rfl, rfl, rfl⟩ := ht
    obtain ⟨re, r1, hre, hna⟩ := hr
    simp only [execStmt]
    have hchild : (DemandNode.statement (.exit e o)).child? 0 =
        some (DemandNode.expression e) := by
      simp [DemandNode.child?, DemandNode.children]
    have hchildPhase : DemandNodeHasPhase (DemandNode.expression e) .expression := by
      simp [DemandNodeHasPhase, DemandNode.phaseMatches]
    let childEc := statementExprChildContext ec 0 e hchild
    have hvisible : ∀ x, x ∈ tenv'.visible ↔
        x ∈ (DemandNode.statement (.exit e o)).visibleForChild tenv'.visible 0 := by
      simp [DemandNode.visibleForChild]
    have hinput : ∀ x, x ∈ childEc.inputFuture → x ∈ ec.inputFuture := by
      intro x hx
      cases ec with
      | pilot profile active =>
        change x ∈ e.variables ++ (DemandNode.statement (.exit e o)).visibleForChild active 0 at hx
        change x ∈ (DemandNode.statement (.exit e o)).variables ++ active
        simpa [DemandNode.variables, Stmt.variables, DemandNode.visibleForChild] using hx
      | shrink profile context =>
        rename_i stmtPlanContext
        let transition := context.child rfl 0 (DemandNode.expression e) .expression hchild hchildPhase
        have hchildContext : childEc = .shrink profile transition.context := rfl
        have hexpectation : DemandNode.childExpectation?
            (DemandNode.statement (.exit e o))
            stmtPlanContext.approvals.access ⟨path, .statement, context.expected.frame.active, context.expected.frame.future,
              context.expected.frame.retained⟩ 0 = some ⟨
                (DemandNode.statement (.exit e o)).visibleForChild context.expected.frame.active 0,
                context.expected.frame.future⟩ := by
          simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild]
        have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
        rw [hchildContext] at hx
        change x ∈ e.variables ++ transition.context.expected.frame.future at hx
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
          hfuture] at hx
        simp [DemandNode.phaseFuture] at hx
        change x ∈ (DemandNode.statement (.exit e o)).variables ++ context.expected.frame.future
        simpa [DemandNode.variables, Stmt.variables] using hx
    have hresult := statementExprChildSpec ih ec observation W tenv' penv env s 0 e hchild
      hactive haccess hprotected hobserved hclassified hp hF hvisible hinput _ _ _ _ _ _ hte hre
      ((PMono.noteAborts _ _ _ hna).2.trans hE)
    refine Sat.bind hresult ?_
    rintro v s1 ⟨_, _, _, _, _, _, _, hv, _⟩
    obtain ⟨k, rfl⟩ := hasTy_int hv
    simp only [expectInt, sat_pure_bind, sat_stop_exit]
  | _ => exact hsel.elim

/-- Lift the statement-step proof with the checked shrink classification that
is carried by every recursive soundness specification. -/
theorem step_stmt_b (ih : Specs m prof plans n) :
    ∀ (path : List Nat) (st : Stmt)
    (ec : EvaluationContext m plans path (.statement st) .statement)
    (observation : Observation) (W : World) (tenv tenv' : TEnv) (penv : PEnv) (env : Env) (s : St) (sc : Nat)
    (tn tn' : Nat) (rst rst' : RState) (lo : Nat),
    (match st with
      | .letS .. | .assign .. | .assignOp .. | .rebind .. | .expr .. | .append .. |
        .popN .. | .resize .. | .clear .. | .assignWhole .. => False
      | _ => True) →
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.ownerP observation) →
    ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture → tenv.scopes.head? = some sc → TopB env lo rst.nextVar s →
    lo ≤ rst.nextVar →
    tyStmt tenv sc st tn = .ok (tenv', tn') → rpStmt penv st rst = .ok ((), rst') →
    EffLe rst'.eff W.E →
    Sat (execStmt (n + 1) ⟨prof, m⟩ env st) s (fun fl s' =>
      Frame m W tenv' penv env s' ec.outputFuture ∧ FootprintS env (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.ownerP observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ TSame tenv tenv' ∧ TopB env lo rst'.nextVar s' ∧
      (match fl with
       | .normal _ => st.diverges m.noReturn = false
       | .brk => tenv.loops ≠ 0 ∧ st.hasBreak = true
       | .cont => tenv.loops ≠ 0
       | .ret v => tenv.inExpr = false ∧ RetOk m W tenv penv s' v) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store) ∧
      PreservesForbiddenOwnerRoots (m := m) (G := W.G) (env := env) (P := W.P)
        ec.forbiddenOwners s s' ∧
      MutationFootprint env W.P W.base (effectMutationRoots m penv.impl rst'.eff) s s') := by
  intro path st ec observation W tenv tenv' penv env s sc tn tn' rst rst' lo
    hsel hactive haccess hprotected hobserved hclassified hp hF hsc hT hlo ht hr hE
  have hcore := step_stmt_b_core ih path st ec observation W tenv tenv' penv env s sc
    tn tn' rst rst' lo hsel hactive haccess hprotected hobserved hclassified hp hF hsc hT
    hlo ht hr hE
  exact hcore.mono (fun fl s' hresult => by
    rcases hresult with ⟨hF', hfp, hroots, hvalues, hsafe, hret, hpilot, hsame, htop, hforbidden, hmutation, hflow⟩
    exact ⟨hF', hfp, hroots, hvalues, hsafe, hret, hpilot, hsame, htop, hflow,
      (fun hprofile => ClassifiedParameters.advanceS (hclassified hprofile) hF hfp),
      hforbidden, hmutation⟩)

end Goose.Core.Sound
