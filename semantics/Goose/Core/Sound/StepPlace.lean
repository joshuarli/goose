import Goose.Core.Sound.StepAux
import Goose.Core.Sound.RetainSyntax
import Goose.Core.Sound.AccessReplay
import Goose.Core.Sound.AccessTyping

/-!
One step of the induction on fuel for places, views, slice bounds and call
arguments.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {plans : Array (Array DemandPoint)} {n : Nat}

private theorem elem_index_retained_alias
    {pc : PlanContext m plans} {path : List Nat} {v : View} {i : Expr} {origin : OriginId}
    (context : NodeContext pc path (.place (.elem v i origin)) .place)
    {aliases : List RetainedAlias} {alias : RetainedAlias}
    (hAliases : pc.approvals.access.aliasView (path ++ [0]) v = .ok aliases)
    (hMem : alias ∈ aliases) :
    alias ∈ (context.child rfl 1 (.expression i) .expression rfl
      (by trivial)).context.expected.frame.retained := by
  let transition := context.child rfl 1 (.expression i) .expression rfl (by trivial)
  have hNew : (DemandNode.place (.elem v i origin)).retainedForChild
      pc.approvals.access path 1 = .ok aliases := by
    simp [DemandNode.retainedForChild, hAliases]
  have hChild := DemandNode.childFrame_newAlias transition.childFrameEq hNew hMem
  change alias ∈ transition.context.expected.frame.retained
  rw [transition.expectedFrameEq]
  exact DemandNode.phaseFrame_retains transition.phaseFrameEq hChild

theorem step_place (hm : ModOk m) (ih : Specs m prof plans n) : PlaceSpec m prof plans (n + 1) := by
  intro path p ec observation W tenv penv env s tn tn' t mu contents rst rst' rho hActive hAccess hProtected hObserved hClass hp hF ht hr hE
  cases p with
  | var x =>
    simp only [tyPlace] at ht; inv at ht
    simp only [rpPlace] at hr; inv at hr
    obtain ⟨hx, lv0, hlv0, rfl, rfl, rfl, rfl⟩ := ht
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨lv, si, v, h1, h2, h3, h4, h5⟩ := hF.vis x hx (by cases ec <;> simp [EvaluationContext.inputFuture, NodeContext.inputFuture, DemandNode.variables, Place.variables])
    rw [hF.vars_t, h1] at hlv0
    cases hlv0
    simp only [evalPlace, rootOf, h1, h2, sat_pure_bind, sat_pure]
    refine ⟨hF.narrowFuture (by intro y hy; cases ec <;> simp_all [EvaluationContext.inputFuture, EvaluationContext.outputFuture, NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.visibleAfter]), Footprint.refl _ _ _, PreservesRootTypes.refl _, PreservesValues.refl _, hObserved, RetainsAliases.refl, (fun _ => StoreLe.refl _), ?_, ⟨.local x, by simp, lv0, si, h1, h2, rfl⟩, hClass⟩
    by_cases hrl : lv0.ty.isRefLike = true
    · exact Or.inr (Or.inl ⟨x, lv0, si, v, rfl, h1, h2, rfl, rfl, hrl, h4, h5⟩)
    · have hrl' : lv0.ty.isRefLike = false := by simpa using hrl
      exact Or.inl ⟨storable_refTarget h3 hrl', Or.inl (locTy_root h4 (hasTy_nonref_flat h5 h3 hrl')),
        HeaderLoc.root⟩
  | global g =>
    simp only [tyPlace] at ht; inv at ht
    obtain ⟨_, ht⟩ := ht
    simp only [rpPlace] at hr; inv at hr
    obtain ⟨rfl, rfl⟩ := hr
    cases hg : tenv.mod.globals[g]? with
    | none => simp only [hg] at ht; inv at ht
    | some gl =>
      simp only [hg] at ht; inv at ht
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
      rw [hF.mod_t] at hg
      have hok := hm.glob g gl hg
      simp only [evalPlace, sat_pure]
      refine ⟨hF.narrowFuture (by intro y hy; cases ec <;> simp_all [EvaluationContext.inputFuture, EvaluationContext.outputFuture, NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.visibleAfter]), Footprint.refl _ _ _, PreservesRootTypes.refl _, PreservesValues.refl _, hObserved, RetainsAliases.refl, (fun _ => StoreLe.refl _), Or.inl ⟨storable_refTarget (paramOk_of_storable hok.ty.1) hok.ty.2, ?_,
        HeaderLoc.root⟩,
        ⟨.global g, by simp, rfl⟩, hClass⟩
      by_cases hG : g < W.G
      · exact Or.inl (hF.inv.globals g gl hG hg)
      · exact Or.inr ⟨g, gl, Nat.le_of_not_lt hG, rfl, hg, FieldPath.root _⟩
  | deref e =>
    simp only [rpPlace] at hr
    simp only [evalPlace]
    cases hs : sliceRefTy tenv e with
    | none =>
      simp only [tyPlace, hs] at ht; inv at ht
      obtain ⟨te, t1, ⟨te', t0, hte, hnr, rfl, rfl⟩, ht⟩ := ht
      cases te <;> inv at ht
      rename_i mm tt
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
      let child := ec.child rfl 0 (.expression e) .expression rfl (by trivial)
      have hChildActive := ec.child_activeMatches rfl 0 (.expression e) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.expression e) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.expression e) .expression rfl
          (by trivial) W.P observation r)
      have hFuture : child.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active => rfl
        | shrink profile context =>
          let transition := context.child rfl 0 (.expression e) .expression rfl (by trivial)
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq,
            DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hInput : child.inputFuture = ec.inputFuture := by
        have hFormula : child.inputFuture = e.variables ++ child.outputFuture := by
          cases ec <;> rfl
        rw [hFormula, hFuture]
        cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
          NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
          DemandNode.visibleAfter, Place.variables]
      refine Sat.bind (ih.expr (path ++ [0]) e child observation W tenv penv env s _ _ _ _ _ _
        hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
        (by simpa [hChildShrink] using hObserved) hClass hp (by simpa [hInput] using hF) hte hr hE) ?_
      rintro v s1 ⟨hF1, hX1, hRoots, hValues, hObserved1, hRetains, hPilotLe, hv, hg, _⟩
      have hClassPost : m.profile = .shrink →
          ClassifiedParameters m W.P W.D observation s1.store :=
        fun profile => hF.classifiedParameters_advance (hClass profile) hX1
      have hFrame : Frame m W tenv penv env s1 ec.outputFuture := by
        simpa [hFuture] using hF1
      have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
        simpa [hChildShrink] using hObserved1
      have hRetained := hRetains.subset (fun alias hmem =>
        ec.child_retained_subset rfl 0 (.expression e) .expression rfl (by trivial) hmem)

      obtain ⟨l, rfl, hh⟩ := hv
      simp only [expectRef, sat_pure]
      rcases hh with ⟨hrt, hl, hheader⟩ | ⟨hsl, _⟩
      · exact ⟨hFrame, hX1, hRoots, hValues, hObservedPost, hRetained, hPilotLe, Or.inl ⟨hrt, hl, hheader⟩, hg _ rfl, hClassPost⟩
      · rw [isRefSlice_ref] at hnr; exact absurd hsl hnr
    | some ty =>
      simp only [tyPlace, hs] at ht
      obtain ⟨x, lv, mu0, mus, E, rfl, hx, hlv, hty, hfl, rfl⟩ := sliceRefTy_some hs
      rw [hty] at ht; inv at ht
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨rp, r1, hrp, r2, hadd, hrr⟩ := hr
      obtain ⟨_, hroots⟩ := readRoots_ok _ _ _ _ hrr
      refine Sat.bind (sat_read_var (prof := prof) hF hx
        (by cases ec <;> simp [EvaluationContext.inputFuture, NodeContext.inputFuture, DemandNode.variables, Place.variables, Expr.variables]) n
        (Q := fun v s' => s' = s ∧ ∃ l, v = .ref l ∧ l.path = [] ∧
          s.store.roots[l.root]? ≠ none ∧
          ∃ ann, penv.ann x = some ann ∧ Gam env W.P ann l.root) ?_) ?_
      · intro lv' si v h1 h2 h4 h5
        rw [hF.vars_t, h1] at hlv
        cases hlv
        rw [hty] at h5
        obtain ⟨l, rfl, hh⟩ := h5
        rcases hh with ⟨hrt, _⟩ | ⟨_, hpath, hlive⟩
        · simp [Ty.refTarget] at hrt
        · exact ⟨rfl, l, rfl, hpath, hlive, hF.rooted x _ si _ h1 h2 h4 _ rfl⟩
      · rintro v s1 ⟨rfl, l, rfl, hpath, hlive, ann, hann, hgl⟩
        simp only [expectRef, sat_pure]
        rw [hF.vars_t] at hlv
        refine ⟨hF.narrowFuture (by intro y hy; cases ec <;> simp_all [EvaluationContext.inputFuture, EvaluationContext.outputFuture, NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.visibleAfter]), Footprint.refl _ _ _, PreservesRootTypes.refl _, PreservesValues.refl _, hObserved, RetainsAliases.refl, (fun _ => StoreLe.refl _), Or.inr (Or.inr ⟨x, lv, mu0, mus, E, ann, rfl, hlv, hty, rfl, hfl, hpath,
          hann, hgl, hlive⟩), ?_, hClass⟩
        rcases hroots with ⟨x', lv', e, _, _, ha'⟩ | ⟨x', e, _⟩ | ⟨_, hnr, _⟩
        · cases e
          simp only at ha'
          rw [hann] at ha'; cases ha'; exact hgl
        · cases e
        · have := hnr x lv rfl (by rw [hF.vars_p]; exact hlv)
          rw [hty] at this; simp [Ty.isRefLike] at this
  | field owner i =>
    simp only [tyPlace] at ht; inv at ht
    obtain ⟨ot, ob, oc, t1, howner, f, t2, hfield, rfl, rfl, rfl, rfl⟩ := ht
    obtain ⟨sid, ts, rfl, hflat, hselector, rfl⟩ := structField_ok _ _ _ _ _ _ hfield
    have hf : f.ty.flat = true := tyList_flat_get ts (by simpa [Ty.flat] using hflat) i f.ty hselector
    simp only [rpPlace] at hr
    simp only [evalPlace]
    let child := ec.child rfl 0 (.place owner) .place rfl (by trivial)
    have hChildActive := ec.child_activeMatches rfl 0 (.place owner) .place rfl
      (by trivial) tenv tenv hActive (by intro x; rfl)
    have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.place owner) .place rfl
      (by trivial) tenv penv).mpr hAccess
    have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
      funext r
      exact propext (ec.child_mayShrink_iff rfl 0 (.place owner) .place rfl
        (by trivial) W.P observation r)
    have hFuture : child.outputFuture = ec.outputFuture := by
      cases ec with
      | pilot profile active => rfl
      | shrink profile context =>
        let transition := context.child rfl 0 (.place owner) .place rfl (by trivial)
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq,
          DemandNode.phaseFrame_future transition.phaseFrameEq]
        exact DemandNode.childFrame_future transition.childFrameEq rfl
    have hInput : child.inputFuture = ec.inputFuture := by
      have hFormula : child.inputFuture = owner.variables ++ child.outputFuture := by
        cases ec <;> rfl
      rw [hFormula, hFuture]
      cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
        DemandNode.visibleAfter, Place.variables]
    refine Sat.bind (ih.place (path ++ [0]) owner child observation W tenv penv env s _ _ _ _ _ _ _ _
      hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
      (by simpa [hChildShrink] using hObserved) hClass hp (by simpa [hInput] using hF) howner hr hE) ?_
    rintro l s1 ⟨hF1, hX1, hRoots, hValues, hObserved1, hRetains, hPilotLe, hpl, hg, _⟩
    have hClassPost : m.profile = .shrink →
        ClassifiedParameters m W.P W.D observation s1.store :=
      fun profile => hF.classifiedParameters_advance (hClass profile) hX1
    simp only [sat_pure]
    refine ⟨by simpa [hFuture] using hF1, hX1, hRoots, hValues,
      by simpa [hChildShrink] using hObserved1,
      hRetains.subset (fun alias hmem => ec.child_retained_subset rfl 0 (.place owner)
        .place rfl (by trivial) hmem), hPilotLe, ?_, hg, hClassPost⟩
    rcases hpl with ⟨hrt, hl, _hheader⟩ | ⟨x, lv, si, v, _, _, _, _, hty, hrl, _⟩ |
      ⟨x, lv, mu0, mus, E, ann, _, _, _, hty, _⟩
    · exact Or.inl ⟨flat_refTarget hf,
        hl.fieldPath (FieldPath.field hselector (FieldPath.root _)), HeaderLoc.ofFlat hf⟩
    · simp [Ty.isRefLike] at hrl
    · cases hty
  | elem v i org =>
    simp only [tyPlace] at ht; inv at ht
    simp only [rpPlace] at hr; inv at hr
    obtain ⟨_, t, b, t1, htv, ti, t2, hti, it, rfl, rfl, rfl, rfl, rfl⟩ := ht
    obtain ⟨rv, r1, hrv, ri, r2, hri, r3, hna, rfl, rfl⟩ := hr
    have hE2 : EffLe r2.eff W.E := (PMono.noteAborts _ _ _ hna).2.trans hE
    simp only [evalPlace]
    let viewContext := ec.child rfl 0 (.view v) .view rfl (by trivial)
    let indexContext := ec.child rfl 1 (.expression i) .expression rfl (by trivial)
    have hViewActive := ec.child_activeMatches rfl 0 (.view v) .view rfl
      (by trivial) tenv tenv hActive (by intro x; rfl)
    have hIndexActive := ec.child_activeMatches rfl 1 (.expression i) .expression rfl
      (by trivial) tenv tenv hActive (by intro x; rfl)
    have hViewAccess := (ec.child_accessMatches_iff rfl 0 (.view v) .view rfl
      (by trivial) tenv penv).mpr hAccess
    have hIndexAccess := (ec.child_accessMatches_iff rfl 1 (.expression i) .expression rfl
      (by trivial) tenv penv).mpr hAccess
    have hViewShrink : viewContext.mayShrink W.P observation = ec.mayShrink W.P observation := by
      funext r
      exact propext (ec.child_mayShrink_iff rfl 0 (.view v) .view rfl
        (by trivial) W.P observation r)
    have hIndexShrink : indexContext.mayShrink W.P observation = ec.mayShrink W.P observation := by
      funext r
      exact propext (ec.child_mayShrink_iff rfl 1 (.expression i) .expression rfl
        (by trivial) W.P observation r)
    have hViewFuture : m.profile = .shrink →
        viewContext.outputFuture = i.variables ++ ec.outputFuture := by
      intro hShrink
      cases ec with
      | pilot profile active => cases profile.symm.trans hShrink
      | shrink profile context =>
        let transition := context.child rfl 0 (.view v) .view rfl (by trivial)
        change transition.context.expected.frame.future =
          i.variables ++ context.expected.frame.future
        rw [transition.expectedFrameEq,
          DemandNode.phaseFrame_future transition.phaseFrameEq]
        exact DemandNode.childFrame_future transition.childFrameEq rfl
    have hIndexFuture : indexContext.outputFuture = ec.outputFuture := by
      cases ec with
      | pilot profile active => rfl
      | shrink profile context =>
        let transition := context.child rfl 1 (.expression i) .expression rfl (by trivial)
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq,
          DemandNode.phaseFrame_future transition.phaseFrameEq]
        exact DemandNode.childFrame_future transition.childFrameEq rfl
    have hViewInputFormula : viewContext.inputFuture =
        v.variables ++ viewContext.outputFuture := by
      cases ec <;> rfl
    have hIndexInput : indexContext.inputFuture = i.variables ++ ec.outputFuture := by
      have hFormula : indexContext.inputFuture = i.variables ++ indexContext.outputFuture := by
        cases ec <;> rfl
      rw [hFormula, hIndexFuture]
    have hViewFrame : Frame m W tenv penv env s viewContext.inputFuture := by
      rw [hViewInputFormula]
      cases ec with
      | pilot profile active =>
        apply hF.narrowFuture
        intro x hx
        change x ∈ v.variables ++ active at hx
        simp only [EvaluationContext.inputFuture, DemandNode.variables, Place.variables]
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ (List.mem_append_left _ hx)
        · exact List.mem_append_right _ hx
      | shrink profile context =>
        rw [hViewFuture profile]
        simpa [EvaluationContext.inputFuture, NodeContext.inputFuture,
          DemandNode.variables, Place.variables, EvaluationContext.outputFuture, NodeContext.outputFuture, List.append_assoc] using hF
    refine Sat.bind (ih.view (path ++ [0]) v viewContext observation W tenv penv env s
      _ _ _ _ _ _ _ hViewActive hViewAccess (by simpa [hViewShrink] using hProtected)
      (by simpa [hViewShrink] using hObserved) hClass hp hViewFrame htv hrv
      ((rpExpr_mono hri).2.trans hE2)) ?_
    rintro vw s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hvw, hg, _, _⟩
    have hClass1 : m.profile = .shrink →
        ClassifiedParameters m W.P W.D observation s1.store :=
      fun profile => hF.classifiedParameters_advance (hClass profile) hX1
    have hIndexFrame : Frame m W tenv penv env s1 indexContext.inputFuture := by
      rw [hIndexInput]
      cases ec with
      | pilot profile active =>
        apply hF1.changeFuture
        intro x hx _
        exact (hActive x).mpr hx
      | shrink profile context =>
        simpa [hViewFuture profile] using hF1
    refine Sat.bind (ih.expr (path ++ [1]) i indexContext observation W tenv penv env s1
      _ _ _ _ _ _ hIndexActive hIndexAccess (by simpa [hIndexShrink] using hProtected)
      (by simpa [hViewShrink, hIndexShrink] using hObserved1) hClass1 hp
      hIndexFrame hti hri hE2) ?_
    rintro vi s2 ⟨hF2, hX2, hRoots2, hValues2, hObserved2, hRetains2, hPilot2, hvi, _, _⟩
    have hClassPost : m.profile = .shrink →
        ClassifiedParameters m W.P W.D observation s2.store :=
      fun profile => hF.classifiedParameters_advance (hClass profile) (hX1.trans hX2)
    obtain ⟨k, rfl⟩ := hasTy_int hvi
    simp only [expectInt, sat_pure_bind]
    by_cases hk : 0 ≤ k ∧ k < (vw.len : Int)
    · simp only [hk, and_self, if_true, sat_pure]
      have hSlicePost : SliceTy s2.store vw.loc vw.start vw.len t := by
        cases ec with
        | pilot profile active => exact (hvw.mono (hPilot2 profile)).2.1
        | @shrink pc profile context =>
          have hMod : tenv.mod = penv.mod := hAccess.1.symm.trans hAccess.2.2.1
          have hVars : tenv.vars = penv.impl.vars :=
            hAccess.2.1.symm.trans (congrArg Impl.vars hAccess.2.2.2.1)
          have hEnv : pc.approvals.access = penv.access := by
            have hAccessMod := hAccess.2.2.1
            have hAccessImpl := hAccess.2.2.2.1
            have hAccessCtx := hAccess.2.2.2.2
            cases hAccessValue : pc.approvals.access
            rw [hAccessValue] at hAccessMod hAccessImpl hAccessCtx
            unfold PEnv.access
            congr 1
          have hElement : pc.approvals.access.viewElement? v = some t := by
            rw [hEnv]
            exact tyView_accessElement hMod hVars htv
          let transition := context.child rfl 1 (.expression i) .expression rfl (by trivial)
          cases hAccessRoots : pc.approvals.access.viewRoots v with
          | error err =>
            have hInvalid : (DemandNode.place (.elem v i org)).childFrame
                pc.approvals.access path context.expected.frame 1 = .error err := by
              have hExpectation : (DemandNode.place (.elem v i org)).childExpectation? pc.approvals.access
                  ⟨path, .expression, context.expected.frame.active,
                    context.expected.frame.future, context.expected.frame.retained⟩ 1 =
                  some ⟨context.expected.frame.active, context.expected.frame.future⟩ := by rfl
              simp [DemandNode.childFrame, hExpectation, DemandNode.retainedForChild,
                AccessEnv.aliasView, hElement, hAccessRoots] <;> rfl
            have hChecked := transition.childFrameEq
            rw [hInvalid] at hChecked
            cases hChecked
          | ok roots =>
            let alias : RetainedAlias := ⟨.slice .readOnly t, roots, .operand (path ++ [0])⟩
            have hAliases : pc.approvals.access.aliasView (path ++ [0]) v =
                .ok [alias] := by
              simp [AccessEnv.aliasView, hElement, hAccessRoots, alias] <;> rfl
            have hAliasMem : alias ∈ indexContext.retained :=
              elem_index_retained_alias context hAliases (by simp)
            have hAlias := AliasAt.ofAliasView (m := m) (alias := alias) (penv := penv)
              (by rw [← hEnv]; exact hAliases)
              (by rw [← hEnv]; exact hElement) hrv hvw hg
            have hPost := (hRetains2 alias hAliasMem).typed (.slice vw.loc vw.start vw.len) hAlias
            obtain ⟨l, start, count, heq, _, hslice⟩ := hPost.1
            cases heq
            exact hslice
      have hRetained1 := hRetains1.subset (fun alias hmem =>
        ec.child_retained_subset rfl 0 (.view v) .view rfl (by trivial) hmem)
      have hRetained2 := hRetains2.subset (fun alias hmem =>
        ec.child_retained_subset rfl 1 (.expression i) .expression rfl (by trivial) hmem)
      refine ⟨by simpa [hIndexFuture] using hF2, hX1.trans hX2,
        hRoots1.trans hRoots2, hValues1.trans hValues2,
        by simpa [hIndexShrink] using hObserved2, hRetained1.trans hRetained2,
        (fun profile => (hPilot1 profile).trans (hPilot2 profile)),
        Or.inl ⟨flat_refTarget hvw.1, Or.inl ?_, HeaderLoc.ofFlat hvw.1⟩, hg, hClassPost⟩
      exact sliceTy_elem hSlicePost (i := k.toNat) (by omega)
    · simp only [hk, if_false, sat_abort]

theorem step_view (ih : Specs m prof plans n) : ViewSpec m prof plans (n + 1) := by
  intro path v ec observation W tenv penv env s tn tn' el mu rst rst' rho hActive hAccess hProtected hObserved hClass hp hF ht hr hE
  have hViewTy := ht
  have hViewRp := hr
  have hMod : tenv.mod = penv.mod := hF.mod_t.trans hF.mod_p.symm
  have hVars : tenv.vars = penv.impl.vars := hF.vars_t.trans hF.vars_p.symm
  have hViewLookup : penv.access.viewElement? v = some el :=
    tyView_accessElement hMod hVars hViewTy
  cases v with
  | of p =>
    simp only [tyView] at ht; inv at ht
    simp only [rpView] at hr; inv at hr
    obtain ⟨tp, b, contents, t1, htp, ht⟩ := ht
    obtain ⟨rp, r1, hrp, r2, hadd, rfl, rfl⟩ := hr
    obtain ⟨_, hin⟩ := addReads_ok _ _ _ hadd
    simp only [evalView]
    let child := ec.child rfl 0 (.place p) .place rfl (by trivial)
    have hChildActive := ec.child_activeMatches rfl 0 (.place p) .place rfl
      (by trivial) tenv tenv hActive (by intro x; rfl)
    have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.place p) .place rfl
      (by trivial) tenv penv).mpr hAccess
    have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
      funext r
      exact propext (ec.child_mayShrink_iff rfl 0 (.place p) .place rfl
        (by trivial) W.P observation r)
    have hFuture : child.outputFuture = ec.outputFuture := by
      cases ec with
      | pilot profile active => rfl
      | shrink profile context =>
        let transition := context.child rfl 0 (.place p) .place rfl (by trivial)
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq,
          DemandNode.phaseFrame_future transition.phaseFrameEq]
        exact DemandNode.childFrame_future transition.childFrameEq rfl
    have hInput : child.inputFuture = ec.inputFuture := by
      have hFormula : child.inputFuture = p.variables ++ child.outputFuture := by
        cases ec <;> rfl
      rw [hFormula, hFuture]
      cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
        DemandNode.visibleAfter, View.variables]
    refine Sat.bind (ih.place (path ++ [0]) p child observation W tenv penv env s _ _ _ _ _ _ _ _
      hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
      (by simpa [hChildShrink] using hObserved) hClass hp (by simpa [hInput] using hF) htp hrp
      ((PMono.addReads _ _ _ _ hadd).2.trans hE)) ?_
    rintro l s1 ⟨hF1, hX1, hRoots, hValues, hObserved1, hRetains, hPilotLe, hpl, hg, _⟩
    have hClassPost : m.profile = .shrink →
        ClassifiedParameters m W.P W.D observation s1.store :=
      fun profile => hF.classifiedParameters_advance (hClass profile) hX1
    have hFrame : Frame m W tenv penv env s1 ec.outputFuture := by
      simpa [hFuture] using hF1
    have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
      simpa [hChildShrink] using hObserved1
    have hRetained := hRetains.subset (fun alias hmem =>
      ec.child_retained_subset rfl 0 (.place p) .place rfl (by trivial) hmem)

    have hacc : ∀ T, LocOk m W.G s1.store l T → LocTy s1.store l T := fun T hl =>
      access hp hl hg (fun t ht' => Or.inl (hE.1 t (hin t ht')))
    have hBound : ∀ T, ¬ Unbound m W.G l T := fun T =>
      Gam.notUnbound_of_access hp hg (fun target htarget => Or.inl (hE.1 target (hin target htarget)))
    have hPlaceLookup : penv.access.placeType? p = some tp :=
      tyPlace_accessType hMod hVars htp
    have hSourcePlace := hpl
    cases tp <;> inv at ht
    · rename_i el' k
      obtain ⟨rfl, rfl, rfl⟩ := ht
      rcases hpl with ⟨hrt, hl, hHeader⟩ | ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
      · have hlt := hacc _ hl
        refine sat_readLoc_bind hlt (fun v hv hT => ?_)
        cases v <;> simp only [FlatTy] at hT
        rename_i es
        simp only [expectArray, sat_pure_bind, sat_pure]
        have hView : ViewOk s1.store ⟨l, 0, es.size, false⟩ el := by
          refine ⟨by simpa [Ty.refTarget] using hrt, ?_, by simp⟩
          rw [hT.1]
          exact sliceTy_of_arr hlt
        exact ⟨hFrame, hX1, hRoots, hValues, hObservedPost, hRetained, hPilotLe, hView, hg,
          ViewAliases.ofFixed rfl (Or.inr ⟨p, k, rfl, hPlaceLookup⟩) hViewLookup hViewRp hView hg, hClassPost⟩
      · simp [Ty.isRefLike] at hrl
      · cases h3
    · rename_i el'
      obtain ⟨rfl, rfl, rfl⟩ := ht
      rcases hpl with ⟨hrt, hl, hHeader⟩ | ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
      · have hlt := hacc _ hl
        refine sat_readLoc_bind hlt (fun v hv hT => ?_)
        cases v <;> simp only [FlatTy] at hT
        rename_i E' es
        simp only [expectArray, sat_pure_bind, sat_pure]
        have hFlat : el.flat = true := by simpa [Ty.refTarget] using hrt
        have hView : ViewOk s1.store ⟨l, 0, es.size, true⟩ el :=
          ⟨hFlat, sliceTy_of_grow hlt hv, fun _ => ⟨rfl, Or.inl hlt⟩⟩
        exact ⟨hFrame, hX1, hRoots, hValues, hObservedPost, hRetained, hPilotLe, hView, hg,
          ViewAliases.ofOwner rfl hFlat (Or.inl rfl) hPlaceLookup hrp hSourcePlace hg (hBound _), hClassPost⟩
      · simp [Ty.isRefLike] at hrl
      · cases h3
    · rename_i el'
      obtain ⟨rfl, rfl, rfl⟩ := ht
      rcases hpl with ⟨hrt, hl, hHeader⟩ | ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
      · have hlt := hacc _ hl
        refine sat_readLoc_bind hlt (fun v hv hT => ?_)
        cases v <;> simp only [FlatTy] at hT
        rename_i E' es
        simp only [expectArray, sat_pure_bind, sat_pure]
        have hFlat : el.flat = true := by simpa [Ty.refTarget] using hrt
        have hView : ViewOk s1.store ⟨l, 0, es.size, true⟩ el :=
          ⟨hFlat, sliceTy_of_growshrink hlt hv, fun _ => ⟨rfl, Or.inr hlt⟩⟩
        exact ⟨hFrame, hX1, hRoots, hValues, hObservedPost, hRetained, hPilotLe, hView, hg,
          ViewAliases.ofOwner rfl hFlat (Or.inr rfl) hPlaceLookup hrp hSourcePlace hg (hBound _), hClassPost⟩
      · simp [Ty.isRefLike] at hrl
      · cases h3
    · rename_i el' capacity
      obtain ⟨rfl, rfl, rfl⟩ := ht
      rcases hpl with ⟨hrt, hl, hHeader⟩ | ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
      · have hlt := hacc _ hl
        refine sat_readLoc_bind hlt (fun v hv hT => ?_)
        cases v <;> simp only [FlatTy] at hT
        rename_i E' capacity' slots len
        have hread : s1.store.read l = .ok (.limited el capacity slots len) := by
          rw [hT.1, hT.2.1]
          exact hv
        simp only [expectArray, sat_pure_bind, sat_pure]
        have hView : ViewOk s1.store ⟨l, 0, len, false⟩ el :=
          ⟨by simpa [Ty.refTarget] using hrt, sliceTy_of_limited hlt hread, by simp⟩
        have hReference : HasTy m W.G s1.store (.ref l) (.ref .mutable (.limited el capacity)) :=
          ⟨l, rfl, Or.inl ⟨hrt, hl, hHeader⟩⟩
        exact ⟨hFrame, hX1, hRoots, hValues, hObservedPost, hRetained, hPilotLe, hView, hg,
          ViewAliases.ofLimited rfl hPlaceLookup hrp hReference hg (hBound _), hClassPost⟩
      · simp [Ty.isRefLike] at hrl
      · cases h3
  | val e =>
    simp only [tyView] at ht; inv at ht
    obtain ⟨te, t1, hte, ht⟩ := ht
    simp only [rpView] at hr
    simp only [evalView]
    cases te <;> inv at ht
    rename_i mm el'
    obtain ⟨rfl, rfl, rfl⟩ := ht
    let child := ec.child rfl 0 (.expression e) .expression rfl (by trivial)
    have hChildActive := ec.child_activeMatches rfl 0 (.expression e) .expression rfl
      (by trivial) tenv tenv hActive (by intro x; rfl)
    have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.expression e) .expression rfl
      (by trivial) tenv penv).mpr hAccess
    have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
      funext r
      exact propext (ec.child_mayShrink_iff rfl 0 (.expression e) .expression rfl
        (by trivial) W.P observation r)
    have hFuture : child.outputFuture = ec.outputFuture := by
      cases ec with
      | pilot profile active => rfl
      | shrink profile context =>
        let transition := context.child rfl 0 (.expression e) .expression rfl (by trivial)
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq,
          DemandNode.phaseFrame_future transition.phaseFrameEq]
        exact DemandNode.childFrame_future transition.childFrameEq rfl
    have hInput : child.inputFuture = ec.inputFuture := by
      have hFormula : child.inputFuture = e.variables ++ child.outputFuture := by
        cases ec <;> rfl
      rw [hFormula, hFuture]
      cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
        DemandNode.visibleAfter, View.variables]
    refine Sat.bind (ih.expr (path ++ [0]) e child observation W tenv penv env s _ _ _ _ _ _
      hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
      (by simpa [hChildShrink] using hObserved) hClass hp (by simpa [hInput] using hF) hte hr hE) ?_
    rintro v s1 ⟨hF1, hX1, hRoots, hValues, hObserved1, hRetains, hPilotLe, hv, hg, _⟩
    have hClassPost : m.profile = .shrink →
        ClassifiedParameters m W.P W.D observation s1.store :=
      fun profile => hF.classifiedParameters_advance (hClass profile) hX1
    have hFrame : Frame m W tenv penv env s1 ec.outputFuture := by
      simpa [hFuture] using hF1
    have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
      simpa [hChildShrink] using hObserved1
    have hRetained := hRetains.subset (fun alias hmem =>
      ec.child_retained_subset rfl 0 (.expression e) .expression rfl (by trivial) hmem)

    obtain ⟨l, st, len, rfl, hfl, hsl⟩ := hv
    simp only [expectSlice, sat_pure_bind, sat_pure]
    have hView : ViewOk s1.store ⟨l, st, len, false⟩ el := ⟨hfl, hsl, by simp⟩
    exact ⟨hFrame, hX1, hRoots, hValues, hObservedPost, hRetained, hPilotLe, hView, hg _ rfl,
      ViewAliases.ofFixed rfl (Or.inl ⟨e, rfl⟩) hViewLookup hViewRp hView (hg _ rfl), hClassPost⟩

theorem step_bound (ih : Specs m prof plans n) : BoundSpec m prof plans (n + 1) := by
  intro path b ec observation W tenv penv env s len d tn tn' rst rst' hActive hAccess hProtected hObserved hClass hp hF ht hr hE
  cases b with
  | omitted =>
    simp only [evalBound, sat_pure]
    exact ⟨hF.narrowFuture (by intro y hy; cases ec <;> simp_all [EvaluationContext.inputFuture, EvaluationContext.outputFuture, NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.visibleAfter]), Footprint.refl _ _ _, PreservesRootTypes.refl _, PreservesValues.refl _, hObserved, RetainsAliases.refl, (fun _ => StoreLe.refl _), hClass⟩
  | expr e =>
    simp only [tyBound] at ht; inv at ht
    simp only [rpBound] at hr; inv at hr
    obtain ⟨te, t1, hte, it, rfl, rfl⟩ := ht
    obtain ⟨re, hre⟩ := hr
    simp only [evalBound]
    let child := ec.child rfl 0 (.expression e) .expression rfl (by trivial)
    have hChildActive := ec.child_activeMatches rfl 0 (.expression e) .expression rfl
      (by trivial) tenv tenv hActive (by intro x; rfl)
    have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.expression e) .expression rfl
      (by trivial) tenv penv).mpr hAccess
    have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
      funext r
      exact propext (ec.child_mayShrink_iff rfl 0 (.expression e) .expression rfl
        (by trivial) W.P observation r)
    have hFuture : child.outputFuture = ec.outputFuture := by
      cases ec with
      | pilot profile active => rfl
      | shrink profile context =>
        let transition := context.child rfl 0 (.expression e) .expression rfl (by trivial)
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq,
          DemandNode.phaseFrame_future transition.phaseFrameEq]
        exact DemandNode.childFrame_future transition.childFrameEq rfl
    have hInput : child.inputFuture = ec.inputFuture := by
      have hFormula : child.inputFuture = e.variables ++ child.outputFuture := by
        cases ec <;> rfl
      rw [hFormula, hFuture]
      cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
        DemandNode.visibleAfter, Bound.variables]
    refine Sat.bind (ih.expr (path ++ [0]) e child observation W tenv penv env s _ _ _ _ _ _
      hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
      (by simpa [hChildShrink] using hObserved) hClass hp (by simpa [hInput] using hF) hte hre hE) ?_
    rintro v s1 ⟨hF1, hX1, hRoots, hValues, hObserved1, hRetains, hPilotLe, hv, _, _⟩
    have hClassPost : m.profile = .shrink →
        ClassifiedParameters m W.P W.D observation s1.store :=
      fun profile => hF.classifiedParameters_advance (hClass profile) hX1
    obtain ⟨k, rfl⟩ := hasTy_int hv
    simp only [expectInt, sat_pure_bind, sat_pure]
    exact ⟨by simpa [hFuture] using hF1, hX1, hRoots, hValues,
      by simpa [hChildShrink] using hObserved1,
      hRetains.subset (fun alias hmem => ec.child_retained_subset rfl 0 (.expression e)
        .expression rfl (by trivial) hmem), hPilotLe, hClassPost⟩
  | fromEnd e =>
    simp only [tyBound] at ht; inv at ht
    simp only [rpBound] at hr; inv at hr
    obtain ⟨te, t1, hte, it, rfl, rfl⟩ := ht
    obtain ⟨re, hre⟩ := hr
    simp only [evalBound]
    let child := ec.child rfl 0 (.expression e) .expression rfl (by trivial)
    have hChildActive := ec.child_activeMatches rfl 0 (.expression e) .expression rfl
      (by trivial) tenv tenv hActive (by intro x; rfl)
    have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.expression e) .expression rfl
      (by trivial) tenv penv).mpr hAccess
    have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
      funext r
      exact propext (ec.child_mayShrink_iff rfl 0 (.expression e) .expression rfl
        (by trivial) W.P observation r)
    have hFuture : child.outputFuture = ec.outputFuture := by
      cases ec with
      | pilot profile active => rfl
      | shrink profile context =>
        let transition := context.child rfl 0 (.expression e) .expression rfl (by trivial)
        change transition.context.expected.frame.future = context.expected.frame.future
        rw [transition.expectedFrameEq,
          DemandNode.phaseFrame_future transition.phaseFrameEq]
        exact DemandNode.childFrame_future transition.childFrameEq rfl
    have hInput : child.inputFuture = ec.inputFuture := by
      have hFormula : child.inputFuture = e.variables ++ child.outputFuture := by
        cases ec <;> rfl
      rw [hFormula, hFuture]
      cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
        DemandNode.visibleAfter, Bound.variables]
    refine Sat.bind (ih.expr (path ++ [0]) e child observation W tenv penv env s _ _ _ _ _ _
      hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
      (by simpa [hChildShrink] using hObserved) hClass hp (by simpa [hInput] using hF) hte hre hE) ?_
    rintro v s1 ⟨hF1, hX1, hRoots, hValues, hObserved1, hRetains, hPilotLe, hv, _, _⟩
    have hClassPost : m.profile = .shrink →
        ClassifiedParameters m W.P W.D observation s1.store :=
      fun profile => hF.classifiedParameters_advance (hClass profile) hX1
    obtain ⟨k, rfl⟩ := hasTy_int hv
    simp only [expectInt, sat_pure_bind, sat_pure]
    exact ⟨by simpa [hFuture] using hF1, hX1, hRoots, hValues,
      by simpa [hChildShrink] using hObserved1,
      hRetains.subset (fun alias hmem => ec.child_retained_subset rfl 0 (.expression e)
        .expression rfl (by trivial) hmem), hPilotLe, hClassPost⟩

theorem step_arg (ih : Specs m prof plans n) : ArgSpec m prof plans (n + 1) := by
  intro path a ac observation W tenv penv env s tn tn' ty rst rst' rho hActive hAccess hProtected hObserved hClass hp hF ht hr hE
  cases ac with
  | byVal ec =>
    simp only [evalArg]
    exact ih.expr path _ ec observation W tenv penv env s _ _ _ _ _ _
      hActive hAccess hProtected hObserved hClass hp hF ht hr hE
  | byRef ec =>
    obtain ⟨t, mu', htp, hrt, rfl⟩ := ht
    simp only [evalArg]
    refine Sat.bind (ih.place path _ ec observation W tenv penv env s _ _ _ _ _ _ _ _
      hActive hAccess hProtected hObserved hClass hp hF htp hr hE) ?_
    rintro l s1 ⟨hF1, hX1, hRoots, hValues, hObserved1, hRetains, hPilotLe, hpl, hg, _⟩
    have hClassPost : m.profile = .shrink →
        ClassifiedParameters m W.P W.D observation s1.store :=
      fun profile => hF.classifiedParameters_advance (hClass profile) hX1
    simp only [sat_pure]
    refine ⟨hF1, hX1, hRoots, hValues, hObserved1, hRetains, hPilotLe, ?_, (fun r hr' => by cases hr'; exact hg), hClassPost⟩
    rcases hpl with ⟨hrt1, hl⟩ | ⟨x, lv, si, v, _, _, _, rfl, _, hrl, h4, h5⟩ |
      ⟨x, lv, mu0, mus, E, ann, _, hlv, hty, rfl, hfl, hpath, hann, hgl, hlive⟩
    · exact ⟨l, rfl, Or.inl ⟨hrt1, hl⟩⟩
    · rcases hrt with hrt | ⟨hsl, _, _⟩
      · rw [refTarget_not_refLike hrt] at hrl; cases hrl
      · exact ⟨_, rfl, Or.inr ⟨hsl, rfl, by rw [h4]; simp⟩⟩
    · -- The pointee is a slice variable of a caller, which the store holds.
      exact ⟨l, rfl, Or.inr ⟨by simpa [Ty.isSlice] using hfl, hpath, hlive⟩⟩

end Goose.Core.Sound
