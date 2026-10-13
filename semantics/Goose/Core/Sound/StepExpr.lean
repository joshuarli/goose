import Goose.Core.Sound.StepAux
import Goose.Core.Sound.RetainSyntax
import Goose.Core.Sound.AccessTyping

/-!
One step of the induction on fuel for expressions.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {plans : Array (Array DemandPoint)} {n : Nat}

theorem noTargets_int {t : IntTy} {x : Int} {P : RootInst → Prop} : ∀ r, Targets (.int t x) r → P r :=
  fun _ h => h.elim

theorem noTargets_bool {b : Bool} {P : RootInst → Prop} : ∀ r, Targets (.bool b) r → P r :=
  fun _ h => h.elim

private theorem pilotStoreLe_refl {m : Module} (s : St) : PilotStoreLe m s s :=
  fun _ => StoreLe.refl _

private theorem pilotStoreLe_trans {m : Module} {s s' s'' : St}
    (h₁ : PilotStoreLe m s s') (h₂ : PilotStoreLe m s' s'') :
    PilotStoreLe m s s'' := by
  intro hprofile
  exact StoreLe.trans (h₁ hprofile) (h₂ hprofile)

private theorem hasTy_refinesFlat {m : Module} {G : Nat} {s' : Store}
    {v v' : Val} {T : Ty} (hrefines : Refines v v')
    (hflat : FlatTy T v) : HasTy m G s' v' T := by
  cases T with
  | ref mu target => simp [FlatTy] at hflat
  | slice mu element => simp [FlatTy] at hflat
  | unit => simp [FlatTy] at hflat
  | tuple elements => simp [FlatTy] at hflat
  | int t =>
      obtain ⟨top, htop, hpreserves, _⟩ := hrefines [] v (get_nil v)
      have htopEq : top = v' := by
        rw [get_nil] at htop
        exact (Option.some.inj htop).symm
      subst top
      simpa [HasTy] using hpreserves (.int t) hflat
  | bool =>
      obtain ⟨top, htop, hpreserves, _⟩ := hrefines [] v (get_nil v)
      have htopEq : top = v' := by
        rw [get_nil] at htop
        exact (Option.some.inj htop).symm
      subst top
      simpa [HasTy] using hpreserves .bool hflat
  | arr element size =>
      obtain ⟨top, htop, hpreserves, _⟩ := hrefines [] v (get_nil v)
      have htopEq : top = v' := by
        rw [get_nil] at htop
        exact (Option.some.inj htop).symm
      subst top
      simpa [HasTy] using hpreserves (.arr element size) hflat
  | grow element =>
      obtain ⟨top, htop, hpreserves, _⟩ := hrefines [] v (get_nil v)
      have htopEq : top = v' := by
        rw [get_nil] at htop
        exact (Option.some.inj htop).symm
      subst top
      simpa [HasTy] using hpreserves (.grow element) hflat
  | growshrink element =>
      obtain ⟨top, htop, hpreserves, _⟩ := hrefines [] v (get_nil v)
      have htopEq : top = v' := by
        rw [get_nil] at htop
        exact (Option.some.inj htop).symm
      subst top
      simpa [HasTy] using hpreserves (.growshrink element) hflat
  | limited element capacity =>
      obtain ⟨top, htop, hpreserves, _⟩ := hrefines [] v (get_nil v)
      have htopEq : top = v' := by
        rw [get_nil] at htop
        exact (Option.some.inj htop).symm
      subst top
      simpa [HasTy] using hpreserves (.limited element capacity) hflat
  | structT id fields =>
      obtain ⟨top, htop, hpreserves, _⟩ := hrefines [] v (get_nil v)
      have htopEq : top = v' := by
        rw [get_nil] at htop
        exact (Option.some.inj htop).symm
      subst top
      simpa [HasTy] using hpreserves (.structT id fields) hflat

private theorem PreservesRootTypes.appendOwner {m : Module} {G : Nat}
    {observed : RootInst → Ty → Prop} {s s' : Store} {l : Loc} {owner : Ty}
    (hle : StoreLe s s')
    (rootsExcept : ∀ r, r ≠ l.root → s'.roots[r]? = s.roots[r]?)
    (hloc : LocTy s l owner) (hheader : l.path = [])
    (howner : owner.ownerElem?.isSome = true) :
    PreservesRootTypes m G observed s s' := by
  intro r T hObserved v hv htyped
  by_cases hroot : r = l.root
  · subst r
    obtain ⟨old, hread, hownerFlat⟩ := hloc
    obtain ⟨rootValue, hrootValue, hget⟩ := (read_ok_iff s l old).1 hread
    have hrootEq : rootValue = old := by
      rw [hheader, get_nil] at hget
      exact Option.some.inj hget
    subst rootValue
    have hvEq : old = v := Option.some.inj (hrootValue.symm.trans hv)
    subst old
    have hrootOld : s.roots[l.root]? = some v := hrootValue
    have hshape : (∃ element es, v = .resizable element es) ∨
        (∃ element capacity slots len, v = .limited element capacity slots len) := by
      cases owner with
      | grow element =>
        cases v with
        | resizable element' es =>
            rcases hownerFlat with ⟨heq, _⟩
            cases heq
            exact Or.inl ⟨element, es, rfl⟩
        | _ => cases hownerFlat
      | growshrink element =>
        cases v with
        | resizable element' es =>
            rcases hownerFlat with ⟨heq, _⟩
            cases heq
            exact Or.inl ⟨element, es, rfl⟩
        | _ => cases hownerFlat
      | limited element capacity =>
        cases v with
        | limited element' capacity' slots len =>
            rcases hownerFlat with ⟨heq, hcap, _, _, _⟩
            cases heq
            cases hcap
            exact Or.inr ⟨element, capacity, slots, len, rfl⟩
        | _ => cases hownerFlat
      | int _ | bool | unit | arr _ _ | ref _ _ | slice _ _ | tuple _ | structT _ _ =>
          change false = true at howner
          cases howner
    have hnotRef : ∀ l', v ≠ .ref l' := by
      intro l' heq
      subst v
      rcases hshape with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
    have hnotSlice : ∀ l' start count, v ≠ .slice l' start count := by
      intro l' start count heq
      subst v
      rcases hshape with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
    have hnotUnit : v ≠ .unit := by
      intro heq
      subst v
      rcases hshape with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h
    obtain ⟨new, hnew, hrefines⟩ := hle l.root v hrootOld
    cases T with
    | ref mu target =>
        obtain ⟨targetLoc, rfl, _⟩ := htyped
        exact False.elim (hnotRef targetLoc rfl)
    | slice mu element =>
        obtain ⟨targetLoc, start, count, rfl, _, _⟩ := htyped
        exact False.elim (hnotSlice targetLoc start count rfl)
    | unit =>
        simp only [HasTy] at htyped
        exact False.elim (hnotUnit htyped)
    | tuple elements => simp [HasTy] at htyped
    | int t =>
        have hflat : FlatTy (.int t) v := by simpa [HasTy] using htyped
        exact ⟨new, hnew, hasTy_refinesFlat hrefines hflat⟩
    | bool =>
        have hflat : FlatTy .bool v := by simpa [HasTy] using htyped
        exact ⟨new, hnew, hasTy_refinesFlat hrefines hflat⟩
    | arr element size =>
        have hflat : FlatTy (.arr element size) v := by simpa [HasTy] using htyped
        exact ⟨new, hnew, hasTy_refinesFlat hrefines hflat⟩
    | grow element =>
        have hflat : FlatTy (.grow element) v := by simpa [HasTy] using htyped
        exact ⟨new, hnew, hasTy_refinesFlat hrefines hflat⟩
    | growshrink element =>
        have hflat : FlatTy (.growshrink element) v := by simpa [HasTy] using htyped
        exact ⟨new, hnew, hasTy_refinesFlat hrefines hflat⟩
    | limited element capacity =>
        have hflat : FlatTy (.limited element capacity) v := by simpa [HasTy] using htyped
        exact ⟨new, hnew, hasTy_refinesFlat hrefines hflat⟩
    | structT id fields =>
        have hflat : FlatTy (.structT id fields) v := by simpa [HasTy] using htyped
        exact ⟨new, hnew, hasTy_refinesFlat hrefines hflat⟩
  · refine ⟨v, ?_, HasTy.mono hle htyped⟩
    rw [rootsExcept r hroot]
    exact hv

private theorem PreservesRootTypes.appendOwnerStep {m : Module} {G : Nat}
    {observed : RootInst → Ty → Prop} {s s' : Store} {l : Loc} {vs : Array Val}
    {n : Nat} {owner elem : Ty} (hloc : LocTy s l owner) (hheader : l.path = [])
    (howner : owner.ownerElem? = some elem) (happend : s.append l vs = .ok (s', n))
    (hstep : FlatStep s s') : PreservesRootTypes m G observed s s' := by
  have hmodify : s.modify l (Val.appendAll vs) = .ok s' := by
    rcases append_spec s s' l vs n happend with ⟨_, _, _, _, hm⟩ | ⟨_, _, _, _, _, _, hm⟩
    · exact hm
    · exact hm
  obtain ⟨old, x, y, new, hroot, hread, hwrite, hmod, hroots⟩ :=
    modify_spec s s' l (Val.appendAll vs) hmodify
  have hrootsExcept : ∀ r, r ≠ l.root → s'.roots[r]? = s.roots[r]? := by
    intro r hne
    rw [hroots]
    have hne' : l.root ≠ r := fun he => hne he.symm
    simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, hne']
  exact PreservesRootTypes.appendOwner hstep.le hrootsExcept hloc hheader
    (by simp [howner])

private theorem hasTy_interiorIsRef {m : Module} {G : Nat} {s : Store} {v : Val} {T : Ty}
    (hty : HasTy m G s v T) (hinterior : T.interiorTarget?.isSome = true) : IsRef v := by
  cases T with
  | ref mu target =>
      obtain ⟨l, rfl, _⟩ := hty
      simp [IsRef]
  | slice mu element =>
      obtain ⟨l, start, count, rfl, _, _⟩ := hty
      simp [IsRef]
  | unit | tuple _ | int _ | bool | arr _ _ | grow _ | growshrink _ | limited _ _ | structT _ _ =>
      simp [Ty.interiorTarget?] at hinterior

private theorem ObservedSafe.flatStep {m : Module} {W : World} {shrinking : RootInst → Prop}
    {observation : Observation} {s s' : Store} (hsafe : ObservedSafe m W shrinking observation s)
    (hroots : PreservesRootTypes m W.G observation.roots s s') (hstep : FlatStep s s') :
    ObservedSafe m W shrinking observation s' := by
  have hvalues : PreservesValues m W.G observation.values s s' := by
    intro v T hv hty
    exact HasTy.mono hstep.le hty
  have htyped' := hsafe.typed.advance hroots hvalues
  refine ⟨htyped', hsafe.rootsOlder, hsafe.valuesOlder, ?_, hsafe.valuesProtected,
    hsafe.holderTypes⟩
  intro r T v hr hv hinterior target htarget hshrink
  obtain ⟨v', hv', hty'⟩ := htyped'.roots r T hr
  have hvEq : v' = v := Option.some.inj (hv'.symm.trans hv)
  subst v'
  have href := hasTy_interiorIsRef hty' hinterior
  rcases hstep.back r v hv with hold | ⟨hnotRef, _⟩
  · obtain ⟨old, holdOld, _⟩ := hsafe.typed.roots r T hr
    have holdEq : old = v := Option.some.inj (holdOld.symm.trans hold)
    subst old
    exact hsafe.rootsProtected r T v hr hold hinterior target htarget hshrink
  · exact False.elim (hnotRef href)

private theorem RetainsAliases.storeLe {m : Module} {W : World} {env : Env} {s s' : Store}
    {aliases : List RetainedAlias} (hle : StoreLe s s') :
    RetainsAliases m W env s s' aliases := by
  intro alias _
  constructor
  · intro v ⟨hty, hroots⟩
    exact ⟨HasTy.mono hle hty, hroots⟩
  · intro mu el capacity l start len hty halias hslice
    exact SliceTy.mono hle hslice

private theorem frame_changeFuture {m : Module} {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future future' : List VarId}
    (h : Frame m W tenv penv env s future)
    (hvisible : ∀ x, x ∈ tenv.visible → x ∈ future) :
    Frame m W tenv penv env s future' := by
  refine { h with vis := ?_, inv := ?_ }
  · intro x hx _
    exact h.vis x hx (hvisible x hx)
  · apply h.inv.changeDemand
    intro r hdem
    cases r with
    | global g => exact Or.inl trivial
    | «local» a si x =>
      rcases hdem with ⟨ha, hx, _, lv, hvar, hlk⟩
      exact Or.inl ⟨ha, hx, hvisible x hx, lv, hvar, hlk⟩

private theorem classified_after {m : Module} {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s s' : St} {future : List VarId} {observation : Observation}
    (frame : Frame m W tenv penv env s future)
    (classified : m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store)
    (footprint : Footprint (insts env) (Dset W) s s') :
    m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store := by
  intro profile
  exact frame.classifiedParameters_advance (classified profile) footprint

private def contextAccess {m : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {node : DemandNode} {phase : DemandPhase}
    (ec : EvaluationContext m plans path node phase) (penv : PEnv) : AccessEnv :=
  match ec with
  | .pilot _ _ => penv.access
  | @EvaluationContext.shrink _ _ _ _ _ pc _ _ => pc.approvals.access

set_option maxHeartbeats 800000 in
theorem step_expr_a (ih : Specs m prof plans n) :
    ∀ (path : List Nat) (e : Expr)
    (ec : EvaluationContext m plans path (.expression e) .expression)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St)
    (tn tn' : Nat) (ty : Ty) (rst rst' : RState) (rho : List RootRef),
    (match e with
      | .lit .. | .bool .. | .not .. | .and .. | .or .. | .un .. | .bin .. | .cmp .. | .conv .. => True
      | _ => False) →
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture →
    tyExpr tenv e tn = .ok (ty, tn') → rpExpr penv e rst = .ok (rho, rst') → EffLe rst'.eff W.E →
    Sat (evalExpr (n + 1) ⟨prof, m⟩ env e) s (fun v s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ HasTy m W.G s'.store v ty ∧
      (∀ r, Targets v r → Gam env W.P rho r) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store)) := by
  intro path e ec observation W tenv penv env s tn tn' ty rst rst' rho hsel hActive hAccess
    hProtected hObserved hClass hp hF ht hr hE
  apply Sat.mono (R := (fun v s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ HasTy m W.G s'.store v ty ∧
      ∀ r, Targets v r → Gam env W.P rho r))
  · cases e with
    | lit t v =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨_, rfl, rfl⟩ := ht
      obtain ⟨rfl, rfl⟩ := hr
      simp only [evalExpr, sat_pure]
      have hFrame : Frame m W tenv penv env s ec.outputFuture := by
        cases ec <;>
          simpa [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
            NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
            Expr.variables, DemandNode.visibleAfter] using hF
      exact ⟨hFrame, Footprint.refl _ _ _, PreservesRootTypes.refl _,
        PreservesValues.refl _, hObserved, RetainsAliases.refl,
        pilotStoreLe_refl s, by rfl, noTargets_int⟩
    | bool b =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨rfl, rfl⟩ := ht
      obtain ⟨rfl, rfl⟩ := hr
      simp only [evalExpr, sat_pure]
      have hFrame : Frame m W tenv penv env s ec.outputFuture := by
        cases ec <;>
          simpa [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
            NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
            Expr.variables, DemandNode.visibleAfter] using hF
      exact ⟨hFrame, Footprint.refl _ _ _, PreservesRootTypes.refl _,
        PreservesValues.refl _, hObserved, RetainsAliases.refl,
        pilotStoreLe_refl s, by trivial, noTargets_bool⟩
    | not a =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨ta, t1, hta, rfl, rfl, rfl⟩ := ht
      obtain ⟨ra, r1, hra, rfl, rfl⟩ := hr
      simp only [evalExpr]
      let child := ec.child rfl 0 (.expression a) .expression rfl (by trivial)
      have hChildActive := ec.child_activeMatches rfl 0 (.expression a) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.expression a) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.expression a) .expression rfl
          (by trivial) W.P observation r)
      have hFuture : child.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active => rfl
          | shrink profile context =>
          let transition := context.child rfl 0 (.expression a) .expression rfl (by trivial)
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hInputFormula : child.inputFuture = a.variables ++ child.outputFuture := by
        cases ec <;> rfl
      have hInput : child.inputFuture = ec.inputFuture := by
        rw [hInputFormula, hFuture]
        cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
          NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
          DemandNode.visibleAfter, Expr.variables]
      refine Sat.bind (ih.expr (path ++ [0]) a child observation W tenv penv env s _ _ _ _ _ _
        hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
        (by simpa [hChildShrink] using hObserved) hClass hp (by simpa [hInput] using hF) hta hra hE) ?_
      rintro va s1 ⟨hF1, hX1, hRoots, hValues, hObserved1, hRetains, hPilotLe, hv, _⟩
      obtain ⟨b, rfl⟩ := hasTy_bool hv
      simp only [expectBool, sat_pure_bind, sat_pure]
      have hFrame : Frame m W tenv penv env s1 ec.outputFuture := by simpa [hFuture] using hF1
      have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
        simpa [hChildShrink] using hObserved1
      have hRetained := hRetains.subset (fun alias hmem =>
        ec.child_retained_subset rfl 0 (.expression a) .expression rfl (by trivial) hmem)
      exact ⟨hFrame, hX1, hRoots, hValues, hObservedPost, hRetained, hPilotLe,
        trivial, noTargets_bool⟩
    | and a b =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨ta, t1, hta, rfl, tb, t2, htb, rfl, rfl, rfl⟩ := ht
      obtain ⟨ra, r1, hra, rb, r2, hrb, rfl, rfl⟩ := hr
      simp only [evalExpr]
      let left := ec.child rfl 0 (.expression a) .expression rfl (by trivial)
      let right := ec.child rfl 1 (.expression b) .expression rfl (by trivial)
      have hLeftActive := ec.child_activeMatches rfl 0 (.expression a) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hRightActive := ec.child_activeMatches rfl 1 (.expression b) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hLeftAccess := (ec.child_accessMatches_iff rfl 0 (.expression a) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hRightAccess := (ec.child_accessMatches_iff rfl 1 (.expression b) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hLeftShrink : left.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.expression a) .expression rfl
          (by trivial) W.P observation r)
      have hRightShrink : right.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 1 (.expression b) .expression rfl
          (by trivial) W.P observation r)
      have hLeftFuture : left.outputFuture =
          match ec with
          | .pilot _ _ => ec.outputFuture
          | .shrink _ context => b.variables ++ context.expected.frame.future := by
        cases ec with
        | pilot profile active =>
          simp [left, EvaluationContext.child, EvaluationContext.outputFuture,
            DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 0 (.expression a) .expression rfl (by trivial)
          change transition.context.expected.frame.future =
            b.variables ++ context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hLeftInput : Frame m W tenv penv env s left.inputFuture := by
        cases ec with
        | pilot profile active =>
          apply hF.narrowFuture
          intro x hx
          change x ∈ a.variables ++ active at hx
          simp only [EvaluationContext.inputFuture, DemandNode.variables, Expr.variables,
            DemandNode.visibleAfter]
          rcases List.mem_append.mp hx with hxa | hactive
          · exact List.mem_append_left _ (List.mem_append_left _ hxa)
          · exact List.mem_append_right _ hactive
        | shrink profile context =>
          have hInputFormula : left.inputFuture = a.variables ++ left.outputFuture := by rfl
          rw [hInputFormula, hLeftFuture]
          simpa [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
            NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
            Expr.variables, List.append_assoc] using hF
      refine Sat.bind (ih.expr (path ++ [0]) a left observation W tenv penv env s _ _ _ _ _ _
        hLeftActive hLeftAccess (by simpa [hLeftShrink] using hProtected)
        (by simpa [hLeftShrink] using hObserved) hClass hp hLeftInput hta hra
        ((rpExpr_mono hrb).2.trans hE)) ?_
      rintro va s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hv, _⟩
      obtain ⟨x, rfl⟩ := hasTy_bool hv
      simp only [expectBool, sat_pure_bind]
      cases x
      · simp only [Bool.false_eq_true, if_false, sat_pure]
        have hFrame : Frame m W tenv penv env s1 ec.outputFuture := by
          cases ec with
          | pilot profile active => simpa [left, EvaluationContext.child,
            EvaluationContext.outputFuture, DemandNode.visibleAfter,
            DemandNode.visibleForChild] using hF1
          | shrink profile context =>
            rw [hLeftFuture] at hF1
            exact hF1.narrowFuture (fun _ hx => List.mem_append_right _ hx)
        have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
          simpa [hLeftShrink] using hObserved1
        have hRetained := hRetains1.subset (fun alias hmem =>
          ec.child_retained_subset rfl 0 (.expression a) .expression rfl (by trivial) hmem)
        exact ⟨hFrame, hX1, hRoots1, hValues1, hObservedPost, hRetained, hPilot1,
          trivial, noTargets_bool⟩
      · simp only [if_true]
        have hRightInputFormula : right.inputFuture = b.variables ++ right.outputFuture := by
          cases ec <;> rfl
        have hRightOutput : right.outputFuture = ec.outputFuture := by
          cases ec with
          | pilot profile active => rfl
          | shrink profile context =>
            let transition := context.child rfl 1 (.expression b) .expression rfl (by trivial)
            change transition.context.expected.frame.future = context.expected.frame.future
            rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
            exact DemandNode.childFrame_future transition.childFrameEq rfl
        have hRightInput : right.inputFuture = b.variables ++ ec.outputFuture := by
          rw [hRightInputFormula, hRightOutput]
        have hFrameRight : Frame m W tenv penv env s1 right.inputFuture := by
          rw [hRightInput]
          cases ec with
          | pilot profile active =>
            apply frame_changeFuture hF1
            intro x hx
            exact (hActive x).mpr hx
          | shrink profile context =>
            have hFutureShrink : left.outputFuture =
                b.variables ++ context.expected.frame.future := by
              simpa [EvaluationContext.outputFuture] using hLeftFuture
            have hF1' : Frame m W tenv penv env s1
                (b.variables ++ context.expected.frame.future) := by
              simpa [hFutureShrink] using hF1
            simpa [EvaluationContext.outputFuture, NodeContext.outputFuture] using hF1'
        have hObservedRight : ObservedSafe m W (right.mayShrink W.P observation) observation s1.store := by
          simpa [hRightShrink, hLeftShrink] using hObserved1
        refine Sat.bind (ih.expr (path ++ [1]) b right observation W tenv penv env s1
          _ _ _ _ _ _ hRightActive hRightAccess (by simpa [hRightShrink] using hProtected)
          hObservedRight (classified_after hF hClass hX1) hp hFrameRight htb hrb hE) ?_
        rintro vb s2 ⟨hF2, hX2, hRoots2, hValues2, hObserved2, hRetains2, hPilot2, hv2, _⟩
        obtain ⟨y, rfl⟩ := hasTy_bool hv2
        simp only [expectBool, sat_pure_bind, sat_pure]
        have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s2.store := by
          simpa [hRightShrink] using hObserved2
        have hRetained : RetainsAliases m W env s.store s2.store ec.retained := by
          intro alias hmem
          exact RetainsAlias.trans
            (hRetains1 alias (ec.child_retained_subset rfl 0 (.expression a) .expression rfl
              (by trivial) hmem))
            (hRetains2 alias (ec.child_retained_subset rfl 1 (.expression b) .expression rfl
              (by trivial) hmem))
        have hFrameOut : Frame m W tenv penv env s2 ec.outputFuture := by
          simpa [hRightOutput] using hF2
        exact ⟨hFrameOut, Footprint.trans hX1 hX2,
          PreservesRootTypes.trans hRoots1 hRoots2, PreservesValues.trans hValues1 hValues2,
          hObservedPost, hRetained, pilotStoreLe_trans hPilot1 hPilot2,
          trivial, noTargets_bool⟩
    | or a b =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨ta, t1, hta, rfl, tb, t2, htb, rfl, rfl, rfl⟩ := ht
      obtain ⟨ra, r1, hra, rb, r2, hrb, rfl, rfl⟩ := hr
      simp only [evalExpr]
      let left := ec.child rfl 0 (.expression a) .expression rfl (by trivial)
      let right := ec.child rfl 1 (.expression b) .expression rfl (by trivial)
      have hLeftActive := ec.child_activeMatches rfl 0 (.expression a) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hRightActive := ec.child_activeMatches rfl 1 (.expression b) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hLeftAccess := (ec.child_accessMatches_iff rfl 0 (.expression a) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hRightAccess := (ec.child_accessMatches_iff rfl 1 (.expression b) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hLeftShrink : left.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.expression a) .expression rfl
          (by trivial) W.P observation r)
      have hRightShrink : right.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 1 (.expression b) .expression rfl
          (by trivial) W.P observation r)
      have hLeftFuture : left.outputFuture =
          match ec with
          | .pilot _ _ => ec.outputFuture
          | .shrink _ context => b.variables ++ context.expected.frame.future := by
        cases ec with
        | pilot profile active =>
          simp [left, EvaluationContext.child, EvaluationContext.outputFuture,
            DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 0 (.expression a) .expression rfl (by trivial)
          change transition.context.expected.frame.future =
            b.variables ++ context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hLeftInput : Frame m W tenv penv env s left.inputFuture := by
        cases ec with
        | pilot profile active =>
          apply hF.narrowFuture
          intro x hx
          change x ∈ a.variables ++ active at hx
          simp only [EvaluationContext.inputFuture, DemandNode.variables, Expr.variables,
            DemandNode.visibleAfter]
          rcases List.mem_append.mp hx with hxa | hactive
          · exact List.mem_append_left _ (List.mem_append_left _ hxa)
          · exact List.mem_append_right _ hactive
        | shrink profile context =>
          have hInputFormula : left.inputFuture = a.variables ++ left.outputFuture := by rfl
          rw [hInputFormula, hLeftFuture]
          simpa [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
            NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
            Expr.variables, List.append_assoc] using hF
      refine Sat.bind (ih.expr (path ++ [0]) a left observation W tenv penv env s _ _ _ _ _ _
        hLeftActive hLeftAccess (by simpa [hLeftShrink] using hProtected)
        (by simpa [hLeftShrink] using hObserved) hClass hp hLeftInput hta hra
        ((rpExpr_mono hrb).2.trans hE)) ?_
      rintro va s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hv, _⟩
      obtain ⟨x, rfl⟩ := hasTy_bool hv
      simp only [expectBool, sat_pure_bind]
      cases x
      · simp only [Bool.false_eq_true, if_false]
        have hRightInputFormula : right.inputFuture = b.variables ++ right.outputFuture := by
          cases ec <;> rfl
        have hRightOutput : right.outputFuture = ec.outputFuture := by
          cases ec with
          | pilot profile active => rfl
          | shrink profile context =>
            let transition := context.child rfl 1 (.expression b) .expression rfl (by trivial)
            change transition.context.expected.frame.future = context.expected.frame.future
            rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
            exact DemandNode.childFrame_future transition.childFrameEq rfl
        have hRightInput : right.inputFuture = b.variables ++ ec.outputFuture := by
          rw [hRightInputFormula, hRightOutput]
        have hFrameRight : Frame m W tenv penv env s1 right.inputFuture := by
          rw [hRightInput]
          cases ec with
          | pilot profile active =>
            apply frame_changeFuture hF1
            intro x hx
            exact (hActive x).mpr hx
          | shrink profile context =>
            have hFutureShrink : left.outputFuture =
                b.variables ++ context.expected.frame.future := by
              simpa [EvaluationContext.outputFuture] using hLeftFuture
            have hF1' : Frame m W tenv penv env s1
                (b.variables ++ context.expected.frame.future) := by
              simpa [hFutureShrink] using hF1
            simpa [EvaluationContext.outputFuture, NodeContext.outputFuture] using hF1'
        have hObservedRight : ObservedSafe m W (right.mayShrink W.P observation) observation s1.store := by
          simpa [hRightShrink, hLeftShrink] using hObserved1
        refine Sat.bind (ih.expr (path ++ [1]) b right observation W tenv penv env s1
          _ _ _ _ _ _ hRightActive hRightAccess (by simpa [hRightShrink] using hProtected)
          hObservedRight (classified_after hF hClass hX1) hp hFrameRight htb hrb hE) ?_
        rintro vb s2 ⟨hF2, hX2, hRoots2, hValues2, hObserved2, hRetains2, hPilot2, hv2, _⟩
        obtain ⟨y, rfl⟩ := hasTy_bool hv2
        simp only [expectBool, sat_pure_bind, sat_pure]
        have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s2.store := by
          simpa [hRightShrink] using hObserved2
        have hRetained : RetainsAliases m W env s.store s2.store ec.retained := by
          intro alias hmem
          exact RetainsAlias.trans
            (hRetains1 alias (ec.child_retained_subset rfl 0 (.expression a) .expression rfl
              (by trivial) hmem))
            (hRetains2 alias (ec.child_retained_subset rfl 1 (.expression b) .expression rfl
              (by trivial) hmem))
        have hFrameOut : Frame m W tenv penv env s2 ec.outputFuture := by
          simpa [hRightOutput] using hF2
        exact ⟨hFrameOut, Footprint.trans hX1 hX2,
          PreservesRootTypes.trans hRoots1 hRoots2, PreservesValues.trans hValues1 hValues2,
          hObservedPost, hRetained, pilotStoreLe_trans hPilot1 hPilot2,
          trivial, noTargets_bool⟩
      · simp only [if_true, sat_pure]
        have hFrame : Frame m W tenv penv env s1 ec.outputFuture := by
          cases ec with
          | pilot profile active => simpa [left, EvaluationContext.child,
            EvaluationContext.outputFuture, DemandNode.visibleAfter,
            DemandNode.visibleForChild] using hF1
          | shrink profile context =>
            have hFutureShrink : left.outputFuture =
                b.variables ++ context.expected.frame.future := by
              simpa [EvaluationContext.outputFuture] using hLeftFuture
            have hF1' : Frame m W tenv penv env s1
                (b.variables ++ context.expected.frame.future) := by
              simpa [hFutureShrink] using hF1
            exact hF1'.narrowFuture (fun _ hx => List.mem_append_right _ hx)
        have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
          simpa [hLeftShrink] using hObserved1
        have hRetained := hRetains1.subset (fun alias hmem =>
          ec.child_retained_subset rfl 0 (.expression a) .expression rfl (by trivial) hmem)
        exact ⟨hFrame, hX1, hRoots1, hValues1, hObservedPost, hRetained, hPilot1,
          trivial, noTargets_bool⟩
    | un op a o =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨_, ta, t1, hta, t, rfl, ht⟩ := ht
      obtain ⟨ra, r1, hra, hr⟩ := hr
      have hty : ty = .int t := by cases op <;> inv at ht <;> first | exact ht.1 | exact ht.2.1
      have hE1 : EffLe r1.eff W.E := by
        refine EffLe.trans ?_ hE
        cases op <;> inv at hr
        · obtain ⟨s2, h2, _, rfl⟩ := hr; exact (PMono.noteAborts _ _ _ h2).2
        · obtain ⟨_, rfl⟩ := hr; exact EffLe.refl _
      subst hty
      simp only [evalExpr]
      let child := ec.child rfl 0 (.expression a) .expression rfl (by trivial)
      have hChildActive := ec.child_activeMatches rfl 0 (.expression a) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.expression a) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.expression a) .expression rfl
          (by trivial) W.P observation r)
      have hFuture : child.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active => rfl
        | shrink profile context =>
          let transition := context.child rfl 0 (.expression a) .expression rfl (by trivial)
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hInputFormula : child.inputFuture = a.variables ++ child.outputFuture := by
        cases ec <;> rfl
      have hInput : child.inputFuture = ec.inputFuture := by
        rw [hInputFormula, hFuture]
        cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
          NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
          DemandNode.visibleAfter, Expr.variables]
      refine Sat.bind (ih.expr (path ++ [0]) a child observation W tenv penv env s _ _ _ _ _ _
        hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
        (by simpa [hChildShrink] using hObserved) hClass hp (by simpa [hInput] using hF) hta hra hE1) ?_
      rintro va s1 ⟨hF1, hX1, hRoots, hValues, hObserved1, hRetains, hPilotLe, hv, _⟩
      obtain ⟨x, rfl⟩ := hasTy_int hv
      simp only [expectInt, sat_pure_bind]
      split
      · have hFrame : Frame m W tenv penv env s1 ec.outputFuture := by simpa [hFuture] using hF1
        have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
          simpa [hChildShrink] using hObserved1
        have hRetained := hRetains.subset (fun alias hmem =>
          ec.child_retained_subset rfl 0 (.expression a) .expression rfl (by trivial) hmem)
        exact ⟨hFrame, hX1, hRoots, hValues, hObservedPost, hRetained, hPilotLe,
          rfl, noTargets_int⟩
      · trivial
    | bin op a b o =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨_, ta, t1, hta, t, rfl, tb, t2, htb, u, rfl, rfl, rfl, rfl⟩ := ht
      obtain ⟨ra, r1, hra, rb, r2, hrb, hr⟩ := hr
      have hE2 : EffLe r2.eff W.E := by
        refine EffLe.trans ?_ hE
        rcases hr with ⟨_, s3, h3, _, rfl⟩ | ⟨_, _, rfl⟩
        · exact (PMono.noteAborts _ _ _ h3).2
        · exact EffLe.refl _
      simp only [evalExpr]
      let left := ec.child rfl 0 (.expression a) .expression rfl (by trivial)
      let right := ec.child rfl 1 (.expression b) .expression rfl (by trivial)
      have hLeftActive := ec.child_activeMatches rfl 0 (.expression a) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hRightActive := ec.child_activeMatches rfl 1 (.expression b) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hLeftAccess := (ec.child_accessMatches_iff rfl 0 (.expression a) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hRightAccess := (ec.child_accessMatches_iff rfl 1 (.expression b) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hLeftShrink : left.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.expression a) .expression rfl
          (by trivial) W.P observation r)
      have hRightShrink : right.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 1 (.expression b) .expression rfl
          (by trivial) W.P observation r)
      have hLeftFuture : left.outputFuture =
          match ec with
          | .pilot _ _ => ec.outputFuture
          | .shrink _ context => b.variables ++ context.expected.frame.future := by
        cases ec with
        | pilot profile active =>
          simp [left, EvaluationContext.child, EvaluationContext.outputFuture,
            DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 0 (.expression a) .expression rfl (by trivial)
          change transition.context.expected.frame.future =
            b.variables ++ context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hLeftInput : Frame m W tenv penv env s left.inputFuture := by
        cases ec with
        | pilot profile active =>
          apply hF.narrowFuture
          intro x hx
          change x ∈ a.variables ++ active at hx
          simp only [EvaluationContext.inputFuture, DemandNode.variables, Expr.variables,
            DemandNode.visibleAfter]
          rcases List.mem_append.mp hx with hxa | hactive
          · exact List.mem_append_left _ (List.mem_append_left _ hxa)
          · exact List.mem_append_right _ hactive
        | shrink profile context =>
          have hInputFormula : left.inputFuture = a.variables ++ left.outputFuture := by rfl
          rw [hInputFormula, hLeftFuture]
          simpa [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
            NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
            Expr.variables, List.append_assoc] using hF
      refine Sat.bind (ih.expr (path ++ [0]) a left observation W tenv penv env s _ _ _ _ _ _
        hLeftActive hLeftAccess (by simpa [hLeftShrink] using hProtected)
        (by simpa [hLeftShrink] using hObserved) hClass hp hLeftInput hta hra
        ((rpExpr_mono hrb).2.trans hE2)) ?_
      rintro va s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hv, _⟩
      obtain ⟨x, rfl⟩ := hasTy_int hv
      simp only [expectInt, sat_pure_bind]
      have hRightInputFormula : right.inputFuture = b.variables ++ right.outputFuture := by
        cases ec <;> rfl
      have hRightOutput : right.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active => rfl
        | shrink profile context =>
          let transition := context.child rfl 1 (.expression b) .expression rfl (by trivial)
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hRightInput : right.inputFuture = b.variables ++ ec.outputFuture := by
        rw [hRightInputFormula, hRightOutput]
      have hFrameRight : Frame m W tenv penv env s1 right.inputFuture := by
        rw [hRightInput]
        cases ec with
        | pilot profile active =>
          apply frame_changeFuture hF1
          intro x hx
          exact (hActive x).mpr hx
        | shrink profile context =>
          have hFutureShrink : left.outputFuture =
              b.variables ++ context.expected.frame.future := by
            simpa [EvaluationContext.outputFuture] using hLeftFuture
          have hF1' : Frame m W tenv penv env s1
              (b.variables ++ context.expected.frame.future) := by
            simpa [hFutureShrink] using hF1
          simpa [EvaluationContext.outputFuture, NodeContext.outputFuture] using hF1'
      have hObservedRight : ObservedSafe m W (right.mayShrink W.P observation) observation s1.store := by
        simpa [hRightShrink, hLeftShrink] using hObserved1
      refine Sat.bind (ih.expr (path ++ [1]) b right observation W tenv penv env s1
        _ _ _ _ _ _ hRightActive hRightAccess (by simpa [hRightShrink] using hProtected)
        hObservedRight (classified_after hF hClass hX1) hp hFrameRight htb hrb hE2) ?_
      rintro vb s2 ⟨hF2, hX2, hRoots2, hValues2, hObserved2, hRetains2, hPilot2, hv2, _⟩
      obtain ⟨y, rfl⟩ := hasTy_int hv2
      simp only [expectInt, sat_pure_bind, expectSameTy, if_true]
      split
      · have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s2.store := by
          simpa [hRightShrink] using hObserved2
        have hRetained : RetainsAliases m W env s.store s2.store ec.retained := by
          intro alias hmem
          exact RetainsAlias.trans
            (hRetains1 alias (ec.child_retained_subset rfl 0 (.expression a) .expression rfl
              (by trivial) hmem))
            (hRetains2 alias (ec.child_retained_subset rfl 1 (.expression b) .expression rfl
              (by trivial) hmem))
        have hFrameOut : Frame m W tenv penv env s2 ec.outputFuture := by
          simpa [hRightOutput] using hF2
        exact ⟨hFrameOut, Footprint.trans hX1 hX2,
          PreservesRootTypes.trans hRoots1 hRoots2, PreservesValues.trans hValues1 hValues2,
          hObservedPost, hRetained, pilotStoreLe_trans hPilot1 hPilot2, rfl, noTargets_int⟩
      · trivial
    | cmp op a b =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨ta, t1, hta, tb, t2, htb, ht⟩ := ht
      obtain ⟨ra, r1, hra, rb, r2, hrb, rfl, rfl⟩ := hr
      simp only [evalExpr]
      let left := ec.child rfl 0 (.expression a) .expression rfl (by trivial)
      let right := ec.child rfl 1 (.expression b) .expression rfl (by trivial)
      have hLeftActive := ec.child_activeMatches rfl 0 (.expression a) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hRightActive := ec.child_activeMatches rfl 1 (.expression b) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hLeftAccess := (ec.child_accessMatches_iff rfl 0 (.expression a) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hRightAccess := (ec.child_accessMatches_iff rfl 1 (.expression b) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hLeftShrink : left.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.expression a) .expression rfl
          (by trivial) W.P observation r)
      have hRightShrink : right.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 1 (.expression b) .expression rfl
          (by trivial) W.P observation r)
      have hLeftFuture : left.outputFuture =
          match ec with
          | .pilot _ _ => ec.outputFuture
          | .shrink _ context => b.variables ++ context.expected.frame.future := by
        cases ec with
        | pilot profile active =>
          simp [left, EvaluationContext.child, EvaluationContext.outputFuture,
            DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 0 (.expression a) .expression rfl (by trivial)
          change transition.context.expected.frame.future =
            b.variables ++ context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hLeftInput : Frame m W tenv penv env s left.inputFuture := by
        cases ec with
        | pilot profile active =>
          apply hF.narrowFuture
          intro x hx
          change x ∈ a.variables ++ active at hx
          simp only [EvaluationContext.inputFuture, DemandNode.variables, Expr.variables,
            DemandNode.visibleAfter]
          rcases List.mem_append.mp hx with hxa | hactive
          · exact List.mem_append_left _ (List.mem_append_left _ hxa)
          · exact List.mem_append_right _ hactive
        | shrink profile context =>
          have hInputFormula : left.inputFuture = a.variables ++ left.outputFuture := by rfl
          rw [hInputFormula, hLeftFuture]
          simpa [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
            NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
            Expr.variables, List.append_assoc] using hF
      refine Sat.bind (ih.expr (path ++ [0]) a left observation W tenv penv env s _ _ _ _ _ _
        hLeftActive hLeftAccess (by simpa [hLeftShrink] using hProtected)
        (by simpa [hLeftShrink] using hObserved) hClass hp hLeftInput hta hra
        ((rpExpr_mono hrb).2.trans hE)) ?_
      rintro va s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hv, _⟩
      have hRightInputFormula : right.inputFuture = b.variables ++ right.outputFuture := by
        cases ec <;> rfl
      have hRightOutput : right.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active => rfl
        | shrink profile context =>
          let transition := context.child rfl 1 (.expression b) .expression rfl (by trivial)
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hRightInput : right.inputFuture = b.variables ++ ec.outputFuture := by
        rw [hRightInputFormula, hRightOutput]
      have hFrameRight : Frame m W tenv penv env s1 right.inputFuture := by
        rw [hRightInput]
        cases ec with
        | pilot profile active =>
          apply frame_changeFuture hF1
          intro x hx
          exact (hActive x).mpr hx
        | shrink profile context =>
          have hFutureShrink : left.outputFuture =
              b.variables ++ context.expected.frame.future := by
            simpa [EvaluationContext.outputFuture] using hLeftFuture
          have hF1' : Frame m W tenv penv env s1
              (b.variables ++ context.expected.frame.future) := by
            simpa [hFutureShrink] using hF1
          simpa [EvaluationContext.outputFuture, NodeContext.outputFuture] using hF1'
      have hObservedRight : ObservedSafe m W (right.mayShrink W.P observation) observation s1.store := by
        simpa [hRightShrink, hLeftShrink] using hObserved1
      refine Sat.bind (ih.expr (path ++ [1]) b right observation W tenv penv env s1
        _ _ _ _ _ _ hRightActive hRightAccess (by simpa [hRightShrink] using hProtected)
        hObservedRight (classified_after hF hClass hX1) hp hFrameRight htb hrb hE) ?_
      rintro vb s2 ⟨hF2, hX2, hRoots2, hValues2, hObserved2, hRetains2, hPilot2, hv2, _⟩
      cases ta <;> cases tb <;> inv at ht
      · obtain ⟨rfl, rfl, rfl⟩ := ht
        obtain ⟨x, rfl⟩ := hasTy_int hv
        obtain ⟨y, rfl⟩ := hasTy_int hv2
        simp only [expectComparable, expectSameTy, if_true, sat_pure_bind, sat_pure]
        have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s2.store := by
          simpa [hRightShrink] using hObserved2
        have hRetained : RetainsAliases m W env s.store s2.store ec.retained := by
          intro alias hmem
          exact RetainsAlias.trans
            (hRetains1 alias (ec.child_retained_subset rfl 0 (.expression a) .expression rfl
              (by trivial) hmem))
            (hRetains2 alias (ec.child_retained_subset rfl 1 (.expression b) .expression rfl
              (by trivial) hmem))
        have hFrameOut : Frame m W tenv penv env s2 ec.outputFuture := by
          simpa [hRightOutput] using hF2
        exact ⟨hFrameOut, Footprint.trans hX1 hX2,
          PreservesRootTypes.trans hRoots1 hRoots2, PreservesValues.trans hValues1 hValues2,
          hObservedPost, hRetained, pilotStoreLe_trans hPilot1 hPilot2,
          trivial, noTargets_bool⟩
      · have hty : ty = .bool := by cases op <;> inv at ht <;> exact ht.1
        subst hty
        obtain ⟨x, rfl⟩ := hasTy_bool hv
        obtain ⟨y, rfl⟩ := hasTy_bool hv2
        simp only [expectComparable, sat_pure_bind, sat_pure]
        have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s2.store := by
          simpa [hRightShrink] using hObserved2
        have hRetained : RetainsAliases m W env s.store s2.store ec.retained := by
          intro alias hmem
          exact RetainsAlias.trans
            (hRetains1 alias (ec.child_retained_subset rfl 0 (.expression a) .expression rfl
              (by trivial) hmem))
            (hRetains2 alias (ec.child_retained_subset rfl 1 (.expression b) .expression rfl
              (by trivial) hmem))
        have hFrameOut : Frame m W tenv penv env s2 ec.outputFuture := by
          simpa [hRightOutput] using hF2
        exact ⟨hFrameOut, Footprint.trans hX1 hX2,
          PreservesRootTypes.trans hRoots1 hRoots2, PreservesValues.trans hValues1 hValues2,
          hObservedPost, hRetained, pilotStoreLe_trans hPilot1 hPilot2,
          trivial, noTargets_bool⟩
    | conv k target a o =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨_, ta, t1, hta, t, rfl, ht⟩ := ht
      obtain ⟨ra, r1, hra, hr⟩ := hr
      have hE1 : EffLe r1.eff W.E := by
        refine EffLe.trans ?_ hE
        cases k <;> inv at hr
        all_goals first
          | (obtain ⟨s2, h2, _, rfl⟩ := hr; exact (PMono.noteAborts _ _ _ h2).2)
          | (obtain ⟨_, rfl⟩ := hr; exact EffLe.refl _)
      simp only [evalExpr]
      let child := ec.child rfl 0 (.expression a) .expression rfl (by trivial)
      have hChildActive := ec.child_activeMatches rfl 0 (.expression a) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.expression a) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.expression a) .expression rfl
          (by trivial) W.P observation r)
      have hFuture : child.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active => rfl
        | shrink profile context =>
          let transition := context.child rfl 0 (.expression a) .expression rfl (by trivial)
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hInputFormula : child.inputFuture = a.variables ++ child.outputFuture := by
        cases ec <;> rfl
      have hInput : child.inputFuture = ec.inputFuture := by
        rw [hInputFormula, hFuture]
        cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
          NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
          DemandNode.visibleAfter, Expr.variables]
      refine Sat.bind (ih.expr (path ++ [0]) a child observation W tenv penv env s _ _ _ _ _ _
        hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
        (by simpa [hChildShrink] using hObserved) hClass hp (by simpa [hInput] using hF) hta hra hE1) ?_
      rintro va s1 ⟨hF1, hX1, hRoots, hValues, hObserved1, hRetains, hPilotLe, hv, _⟩
      obtain ⟨x, rfl⟩ := hasTy_int hv
      simp only [expectInt, sat_pure_bind]
      cases target <;> inv at ht
      rename_i d
      have hty : ty = .int d := by
        cases k <;> inv at ht <;> first | exact ht.1 | exact ht.2.2.1
      subst hty
      simp only [expectIntTy, sat_pure_bind]
      split
      · have hFrame : Frame m W tenv penv env s1 ec.outputFuture := by simpa [hFuture] using hF1
        have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
          simpa [hChildShrink] using hObserved1
        have hRetained := hRetains.subset (fun alias hmem =>
          ec.child_retained_subset rfl 0 (.expression a) .expression rfl (by trivial) hmem)
        exact ⟨hFrame, hX1, hRoots, hValues, hObservedPost, hRetained, hPilotLe,
          rfl, noTargets_int⟩
      · trivial
    | _ => exact hsel.elim
  · intro v s' h
    rcases h with ⟨hFrame', hFoot', hRoots', hValues', hObserved', hRetained', hPilot', hTyped', hGam'⟩
    exact ⟨hFrame', hFoot', hRoots', hValues', hObserved', hRetained', hPilot', hTyped',
      hGam', classified_after hF hClass hFoot'⟩


private theorem drop_getElem? {α : Type} {xs : List α} {offset : Nat} {x : α} {rest : List α}
    (hdrop : xs.drop offset = x :: rest) : xs[offset]? = some x := by
  have hhead : (xs.drop offset)[0]? = some x := by simpa [hdrop]
  simpa only [List.getElem?_drop, Nat.add_zero] using hhead

private theorem drop_tail {α : Type} {xs : List α} {offset : Nat} {x : α} {rest : List α}
    (hdrop : xs.drop offset = x :: rest) : xs.drop (offset + 1) = rest := by
  calc
    xs.drop (offset + 1) = xs.drop (1 + offset) := by congr 1; exact Nat.add_comm offset 1
    _ = (xs.drop offset).drop 1 := by
      rw [List.drop_drop]
      exact congrArg (fun i => xs.drop i) (Nat.add_comm offset 1).symm
    _ = rest := by rw [hdrop]; rfl

private theorem arrLit_child {all : List Expr} {arrayTy : Ty} {offset : Nat}
    {e : Expr} {rest : List Expr} (hdrop : all.drop offset = e :: rest) :
    (DemandNode.expression (.arrLit arrayTy all)).child? offset = some (.expression e) := by
  have hget := drop_getElem? hdrop
  simp [DemandNode.child?, DemandNode.children, hget]

/-- Evaluate an array literal's suffix while tracking its source child index and future. -/
theorem exprs_spec (ihE : ExprSpec m prof plans n) {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    (hp : Perm m W) (path : List Nat) (arrayTy el : Ty) (all : List Expr)
    (ec : EvaluationContext m plans path (.expression (.arrLit arrayTy all)) .expression)
    (observation : Observation) (hfl : el.flat = true) :
    ∀ (offset : Nat) (es : List Expr), all.drop offset = es →
    ∀ (s : St) (tn tn' : Nat) (rst rst' : RState),
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Frame m W tenv penv env s (es.flatMap Expr.variables ++ ec.outputFuture) →
    tyExprsAs tenv el es tn = .ok ((), tn') → rpExprs penv es rst = .ok ((), rst') → EffLe rst'.eff W.E →
    Sat (mapList (evalExpr n ⟨prof, m⟩ env) es) s (fun vs s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ vs.length = es.length ∧ (∀ v, v ∈ vs → FlatTy el v) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store)) := by
  intro offset es hdrop
  induction es generalizing offset with
  | nil =>
    intro s tn tn' rst rst' hActive hAccess hProtected hObserved hClass hF ht hr hE
    simp only [mapList, sat_pure]
    have hFrame : Frame m W tenv penv env s ec.outputFuture := by simpa using hF
    refine ⟨hFrame, Footprint.refl _ _ _, PreservesRootTypes.refl _, PreservesValues.refl _,
      hObserved, RetainsAliases.refl, pilotStoreLe_refl s, rfl, ?_, hClass⟩
    intro v hv
    cases hv
  | cons e rest ih =>
    intro s tn tn' rst rst' hActive hAccess hProtected hObserved hClass hF ht hr hE
    simp only [tyExprsAs] at ht; inv at ht
    simp only [rpExprs] at hr; inv at hr
    obtain ⟨te, t1, hte, heq, htr⟩ := ht
    obtain ⟨re, r1, hre, hrr⟩ := hr
    have hteq : te = el := by simpa using heq
    subst hteq
    have hdropTail := drop_tail hdrop
    have hchild := arrLit_child (arrayTy := arrayTy) hdrop
    let child := ec.child rfl offset (.expression e) .expression hchild (by trivial)
    have hChildActive := ec.child_activeMatches rfl offset (.expression e) .expression hchild
      (by trivial) tenv tenv hActive (by intro x; rfl)
    have hChildAccess := (ec.child_accessMatches_iff rfl offset (.expression e) .expression hchild
      (by trivial) tenv penv).mpr hAccess
    have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
      funext r
      exact propext (ec.child_mayShrink_iff rfl offset (.expression e) .expression hchild
        (by trivial) W.P observation r)
    have hChildOutput : child.outputFuture =
        match ec with
        | .pilot _ active => active
        | .shrink _ context => rest.flatMap Expr.variables ++ context.expected.frame.future := by
      let access := contextAccess ec penv
      cases ec with
      | pilot profile active => rfl
      | shrink profile context =>
        let transition := context.child rfl offset (.expression e) .expression hchild (by trivial)
        change transition.context.expected.frame.future =
          rest.flatMap Expr.variables ++ context.expected.frame.future
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
        have hlt : offset < all.length := by
          have hpos : 0 < (all.drop offset).length := by rw [hdrop]; simp
          rw [List.length_drop] at hpos
          omega
        have hexpect :
            (DemandNode.expression (.arrLit arrayTy all)).childExpectation?
                access
              ⟨path, .expression, context.expected.frame.active, context.expected.frame.future,
                context.expected.frame.retained⟩ offset = some
              ⟨context.expected.frame.active,
                rest.flatMap Expr.variables ++ context.expected.frame.future⟩ := by
          simp [access, contextAccess, DemandNode.childExpectation?, DemandNode.childFuture,
            DemandNode.visibleForChild, hlt, hchild, hdropTail]
        exact DemandNode.childFrame_future transition.childFrameEq hexpect
    have hChildInput : child.inputFuture = e.variables ++ child.outputFuture := by
      cases ec <;> rfl
    have hFrameChild : Frame m W tenv penv env s child.inputFuture := by
      cases ec with
      | pilot profile active =>
        change Frame m W tenv penv env s (e.variables ++ active)
        apply hF.narrowFuture
        intro x hx
        simp only [List.mem_append] at hx
        change x ∈ (e.variables ++ rest.flatMap Expr.variables) ++ active
        rcases hx with he | ha
        · exact List.mem_append_left _ (List.mem_append_left _ he)
        · exact List.mem_append_right _ ha
      | shrink profile context =>
        have hChildFuture : child.outputFuture =
            rest.flatMap Expr.variables ++ context.expected.frame.future := by
          simpa [child, EvaluationContext.child, EvaluationContext.outputFuture,
            NodeContext.outputFuture] using hChildOutput
        rw [hChildInput, hChildFuture]
        have hFutureEq : (e :: rest).flatMap Expr.variables ++ context.expected.frame.future =
            e.variables ++ (rest.flatMap Expr.variables ++ context.expected.frame.future) := by
          simp [List.flatMap_cons, List.append_assoc]
        exact hFutureEq ▸ hF
    have hChildEff : EffLe r1.eff W.E := by
      exact ((rpExprs_mono hrr).2.trans hE)
    simp only [mapList]
    refine Sat.bind (ihE (path ++ [offset]) e child observation W tenv penv env s _ _ _ _ _ _
      hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
      (by simpa [hChildShrink] using hObserved) hClass hp hFrameChild hte hre hChildEff) ?_
    rintro v s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hv, _⟩
    have hTailFrame : Frame m W tenv penv env s1
        (rest.flatMap Expr.variables ++ ec.outputFuture) := by
      cases ec with
      | pilot profile active =>
        have hF1' : Frame m W tenv penv env s1 active := by
          simpa [child, EvaluationContext.child, EvaluationContext.outputFuture,
            DemandNode.visibleAfter, DemandNode.visibleForChild] using hF1
        apply frame_changeFuture hF1'
        intro x hx
        exact (hActive x).mpr hx
      | shrink profile context =>
        have hChildFuture : child.outputFuture =
            rest.flatMap Expr.variables ++ context.expected.frame.future := by
          simpa [child, EvaluationContext.child, EvaluationContext.outputFuture,
            NodeContext.outputFuture] using hChildOutput
        exact hChildFuture ▸ hF1
    have hObservedTail : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
      simpa [hChildShrink] using hObserved1
    refine Sat.bind (ih (offset + 1) hdropTail s1 t1 tn' r1 rst' hActive hAccess
      hProtected hObservedTail (classified_after hF hClass hX1) hTailFrame htr hrr hE) ?_
    rintro vs s2 ⟨hF2, hX2, hRoots2, hValues2, hObserved2, hRetains2, hPilot2, hlen, hall⟩
    simp only [sat_pure]
    refine ⟨hF2, Footprint.trans hX1 hX2, PreservesRootTypes.trans hRoots1 hRoots2,
      PreservesValues.trans hValues1 hValues2, hObserved2, ?_, pilotStoreLe_trans hPilot1 hPilot2,
      by simp [hlen], ?_, classified_after hF hClass (Footprint.trans hX1 hX2)⟩
    · intro alias hmem
      exact RetainsAlias.trans
        (hRetains1 alias (ec.child_retained_subset rfl offset (.expression e) .expression hchild
          (by trivial) hmem)) (hRetains2 alias hmem)
    · intro v' hv'
      rcases List.mem_cons.1 hv' with rfl | hv'
      · exact hv.flat hfl
      · exact hall.1 v' hv'

/-- Initializers produce one independently checked field value in source order. -/
theorem struct_exprs_spec (ihE : ExprSpec m prof plans n) {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}
    (hp : Perm m W) (path : List Nat) (structTy : Ty) (all : List Expr)
    (ec : EvaluationContext m plans path (.expression (.structLit structTy all)) .expression)
    (observation : Observation) :
    ∀ (offset : Nat) (ts : TyList) (es : List Expr), ts.flat = true → all.drop offset = es →
    ∀ (s : St) (tn tn' : Nat) (rst rst' : RState),
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Frame m W tenv penv env s (es.flatMap Expr.variables ++ ec.outputFuture) →
    tyStructExprs tenv ts.toList es tn = .ok ((), tn') → rpExprs penv es rst = .ok ((), rst') → EffLe rst'.eff W.E →
    Sat (mapList (evalExpr n ⟨prof, m⟩ env) es) s (fun vs s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ FieldsTy ts vs ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store)) := by
  intro offset ts es
  induction es generalizing offset ts with
  | nil =>
    intro hflat hdrop s tn tn' rst rst' hActive hAccess hProtected hObserved hClass hF ht hr hE
    cases ts with
    | nil =>
      simp only [mapList, sat_pure]
      have hFrame : Frame m W tenv penv env s ec.outputFuture := by simpa using hF
      exact ⟨hFrame, Footprint.refl _ _ _, PreservesRootTypes.refl _, PreservesValues.refl _,
        hObserved, RetainsAliases.refl, pilotStoreLe_refl s, by trivial, hClass⟩
    | cons t ts => simp only [TyList.toList, tyStructExprs] at ht; inv at ht
  | cons e rest ih =>
    intro hflat hdrop s tn tn' rst rst' hActive hAccess hProtected hObserved hClass hF ht hr hE
    cases ts with
    | nil => simp only [TyList.toList, tyStructExprs] at ht; inv at ht
    | cons t ts =>
      simp only [TyList.flat, Bool.and_eq_true] at hflat
      simp only [TyList.toList, tyStructExprs] at ht; inv at ht
      simp only [rpExprs] at hr; inv at hr
      obtain ⟨te, t1, hte, heq, htr⟩ := ht
      obtain ⟨re, r1, hre, hrr⟩ := hr
      have hteq : te = t := by simpa using heq
      subst hteq
      have hdropTail := drop_tail hdrop
      have hchild : (DemandNode.expression (.structLit structTy all)).child? offset =
          some (.expression e) := by
        have hget := drop_getElem? hdrop
        simp [DemandNode.child?, DemandNode.children, hget]
      let child := ec.child rfl offset (.expression e) .expression hchild (by trivial)
      have hChildActive := ec.child_activeMatches rfl offset (.expression e) .expression hchild
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hChildAccess := (ec.child_accessMatches_iff rfl offset (.expression e) .expression hchild
        (by trivial) tenv penv).mpr hAccess
      have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl offset (.expression e) .expression hchild
          (by trivial) W.P observation r)
      have hChildOutput : child.outputFuture =
          match ec with
          | .pilot _ active => active
          | .shrink _ context => rest.flatMap Expr.variables ++ context.expected.frame.future := by
        let access := contextAccess ec penv
        cases ec with
        | pilot profile active => rfl
        | shrink profile context =>
          let transition := context.child rfl offset (.expression e) .expression hchild (by trivial)
          change transition.context.expected.frame.future =
            rest.flatMap Expr.variables ++ context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          have hlt : offset < all.length := by
            have hpos : 0 < (all.drop offset).length := by rw [hdrop]; simp
            rw [List.length_drop] at hpos
            omega
          have hexpect :
              (DemandNode.expression (.structLit structTy all)).childExpectation?
                access
                ⟨path, .expression, context.expected.frame.active, context.expected.frame.future,
                  context.expected.frame.retained⟩ offset = some
                ⟨context.expected.frame.active,
                  rest.flatMap Expr.variables ++ context.expected.frame.future⟩ := by
            simp [access, contextAccess, DemandNode.childExpectation?, DemandNode.childFuture,
              DemandNode.visibleForChild, hlt, hchild, hdropTail]
          exact DemandNode.childFrame_future transition.childFrameEq hexpect
      have hChildInput : child.inputFuture = e.variables ++ child.outputFuture := by
        cases ec <;> rfl
      have hFrameChild : Frame m W tenv penv env s child.inputFuture := by
        cases ec with
        | pilot profile active =>
          change Frame m W tenv penv env s (e.variables ++ active)
          apply hF.narrowFuture
          intro x hx
          simp only [List.mem_append] at hx
          change x ∈ (e.variables ++ rest.flatMap Expr.variables) ++ active
          rcases hx with he | ha
          · exact List.mem_append_left _ (List.mem_append_left _ he)
          · exact List.mem_append_right _ ha
        | shrink profile context =>
          have hChildFuture : child.outputFuture =
              rest.flatMap Expr.variables ++ context.expected.frame.future := by
            simpa [child, EvaluationContext.child, EvaluationContext.outputFuture,
              NodeContext.outputFuture] using hChildOutput
          rw [hChildInput, hChildFuture]
          have hFutureEq : (e :: rest).flatMap Expr.variables ++ context.expected.frame.future =
              e.variables ++ (rest.flatMap Expr.variables ++ context.expected.frame.future) := by
            simp [List.flatMap_cons, List.append_assoc]
          exact hFutureEq ▸ hF
      have hChildEff : EffLe r1.eff W.E := by exact ((rpExprs_mono hrr).2.trans hE)
      simp only [mapList]
      refine Sat.bind (ihE (path ++ [offset]) e child observation W tenv penv env s _ _ _ _ _ _
        hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
        (by simpa [hChildShrink] using hObserved) hClass hp hFrameChild hte hre hChildEff) ?_
      rintro v s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hv, _⟩
      have hTailFrame : Frame m W tenv penv env s1
          (rest.flatMap Expr.variables ++ ec.outputFuture) := by
        cases ec with
        | pilot profile active =>
          have hF1' : Frame m W tenv penv env s1 active := by
            simpa [child, EvaluationContext.child, EvaluationContext.outputFuture,
              DemandNode.visibleAfter, DemandNode.visibleForChild] using hF1
          apply frame_changeFuture hF1'
          intro x hx
          exact (hActive x).mpr hx
        | shrink profile context =>
          have hChildFuture : child.outputFuture =
              rest.flatMap Expr.variables ++ context.expected.frame.future := by
            simpa [child, EvaluationContext.child, EvaluationContext.outputFuture,
              NodeContext.outputFuture] using hChildOutput
          exact hChildFuture ▸ hF1
      have hObservedTail : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
        simpa [hChildShrink] using hObserved1
      refine Sat.bind (ih (offset + 1) ts hflat.2 hdropTail s1 t1 tn' r1 rst' hActive hAccess
        hProtected hObservedTail (classified_after hF hClass hX1) hTailFrame htr hrr hE) ?_
      rintro vs s2 ⟨hF2, hX2, hRoots2, hValues2, hObserved2, hRetains2, hPilot2, hfields⟩
      simp only [sat_pure]
      refine ⟨hF2, Footprint.trans hX1 hX2, PreservesRootTypes.trans hRoots1 hRoots2,
        PreservesValues.trans hValues1 hValues2, hObserved2, ?_, pilotStoreLe_trans hPilot1 hPilot2,
        ⟨hv.flat hflat.1, hfields.1⟩,
        classified_after hF hClass (Footprint.trans hX1 hX2)⟩
      intro alias hmem
      exact RetainsAlias.trans
        (hRetains1 alias (ec.child_retained_subset rfl offset (.expression e) .expression hchild
          (by trivial) hmem)) (hRetains2 alias hmem)

set_option maxHeartbeats 800000 in
theorem step_expr_b (ih : Specs m prof plans n) :
    ∀ (path : List Nat) (e : Expr)
    (ec : EvaluationContext m plans path (.expression e) .expression)
    (observation : Observation) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St)
    (tn tn' : Nat) (ty : Ty) (rst rst' : RState) (rho : List RootRef),
    (match e with
      | .read .. | .ref .. | .slice .. | .len .. | .push .. | .ifE .. | .blockE .. | .arrLit ..
      | .fill .. | .structLit .. => True
      | _ => False) →
    ec.ActiveMatches tenv → ec.AccessMatches tenv penv →
    ShrinkProtected W.D W.A (ec.mayShrink W.P observation) →
    ObservedSafe m W (ec.mayShrink W.P observation) observation s.store →
    (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s.store) →
    Perm m W → Frame m W tenv penv env s ec.inputFuture →
    tyExpr tenv e tn = .ok (ty, tn') → rpExpr penv e rst = .ok (rho, rst') → EffLe rst'.eff W.E →
    Sat (evalExpr (n + 1) ⟨prof, m⟩ env e) s (fun v s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ HasTy m W.G s'.store v ty ∧
      (∀ r, Targets v r → Gam env W.P rho r) ∧
      (m.profile = .shrink → ClassifiedParameters m W.P W.D observation s'.store)) := by
  intro path e ec observation W tenv penv env s tn tn' ty rst rst' rho hsel hActive hAccess
    hProtected hObserved hClass hp hF ht hr hE
  apply Sat.mono (R := (fun v s' =>
      Frame m W tenv penv env s' ec.outputFuture ∧
      Footprint (insts env) (Dset W) s s' ∧
      PreservesRootTypes m W.G observation.roots s.store s'.store ∧
      PreservesValues m W.G observation.values s.store s'.store ∧
      ObservedSafe m W (ec.mayShrink W.P observation) observation s'.store ∧
      RetainsAliases m W env s.store s'.store ec.retained ∧
      PilotStoreLe m s s' ∧ HasTy m W.G s'.store v ty ∧
      ∀ r, Targets v r → Gam env W.P rho r))
  · cases e with
    | read p =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨t, b, contents, t1, htp, hrd, rfl, rfl⟩ := ht
      obtain ⟨rp, r1, hrp, r2, hadd, hrr⟩ := hr
      obtain ⟨hst, hroots⟩ := readRoots_ok _ _ _ _ hrr
      simp only at hst hroots
      subst hst
      obtain ⟨_, hin⟩ := addReads_ok _ _ _ hadd
      simp only [evalExpr]
      let child := ec.child rfl 0 (.place p) .place rfl (by trivial)
      have hChildActive := ec.child_activeMatches rfl 0 (.place p) .place rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.place p) .place rfl
        (by trivial) tenv penv).mpr hAccess
      have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.place p) .place rfl
          (by trivial) W.P observation r)
      have hChildFuture : child.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active => simp [child, EvaluationContext.child,
            EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 0 (.place p) .place rfl (by trivial)
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hChildInputFormula : child.inputFuture = p.variables ++ child.outputFuture := by
        cases ec <;> rfl
      have hChildInput : child.inputFuture = ec.inputFuture := by
        rw [hChildInputFormula, hChildFuture]
        cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
          NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
          Place.variables, Expr.variables, DemandNode.visibleAfter]
      refine Sat.bind (ih.place (path ++ [0]) p child observation W tenv penv env s
        _ _ _ _ _ _ _ _ hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
        (by simpa [hChildShrink] using hObserved) hClass hp (by simpa [hChildInput] using hF) htp hrp
        ((PMono.addReads _ _ _ _ hadd).2.trans hE)) ?_
      rintro l s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1,
        hpl, ⟨hg, _⟩⟩
      have hFrame1 : Frame m W tenv penv env s1 ec.outputFuture := by
        simpa [hChildFuture] using hF1
      have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
        simpa [hChildShrink] using hObserved1
      have hRetained := hRetains1.subset (fun alias hmem =>
        ec.child_retained_subset rfl 0 (.place p) .place rfl (by trivial) hmem)
      rcases hpl with ⟨hrt, hl, _⟩ | ⟨x, lv, si, v, rfl, h1, h2, rfl, rfl, hrl, h4, h5⟩ |
        ⟨x, lv, mu0, mus, E, ann, rfl, hlv, hty, rfl, hfl, hpath, hann, hgl, hlive⟩
      · have hlt := access hp hl hg (fun t' ht' => Or.inl (hE.1 t' (hin t' ht')))
        refine sat_readLoc hlt (fun v hv hT => ?_)
        exact ⟨hFrame1, hX1, hRoots1, hValues1, hObservedPost, hRetained, hPilot1,
          hasTy_of_flat hT (Or.inl (readable_flat hrd hrt)), flat_no_targets hT⟩
      · refine sat_readRoot h4 ⟨hFrame1, hX1, hRoots1, hValues1, hObservedPost,
          hRetained, hPilot1, h5, ?_⟩
        intro r hr'
        obtain ⟨ann, ha, hga⟩ := hF1.rooted x lv si v h1 h2 h4 r hr'
        rcases hroots with ⟨x', lv', e, _, _, ha'⟩ | ⟨x', e, _⟩ | ⟨_, hnr, _⟩
        · cases e; rw [ha] at ha'; cases ha'; exact hga
        · cases e
        · have := hnr x lv rfl (by rw [hF1.vars_p]; exact h1)
          rw [this] at hrl; cases hrl
      · -- A slice read through a reference to a slice variable of a caller.
        have hsv : penv.isRefSliceVar x = true := by
          simp [PEnv.isRefSliceVar, hF1.vars_p, hlv, hty, Ty.isRefSlice, hfl]
        rcases hroots with ⟨x', lv', e, _⟩ | ⟨x', e, _, hc⟩ | ⟨_, _, hns⟩
        · cases e
        · cases e
          obtain ⟨hnl, hann', hpr⟩ := hF1.pref x _ hc
          rw [hann] at hann'
          cases hann'
          obtain ⟨q, hq, hrq⟩ := hgl
          simp only [List.mem_singleton] at hq
          subst hq
          obtain ⟨hD, hFR, _⟩ := hpr lv mu0 mus E hlv hty _ hrq
          obtain ⟨v, hv1, hv2, hv3⟩ := hF1.sa _ E hD
          have hl : l = ⟨l.root, []⟩ := by
            cases l; simp only at hpath; simp [hpath]
          rw [hl]
          exact sat_readRoot hv1 ⟨hFrame1, hX1, hRoots1, hValues1, hObservedPost,
            hRetained, hPilot1, hasTy_slice_mu hv2,
            fun r hr' => gam_of_noEnv (hFR r (hv3 r hr'))⟩
        · rw [hns x rfl] at hsv; cases hsv
    | ref mu p =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr
      obtain ⟨t, b, contents, t1, htp, hallowed, hrt, ht⟩ := ht
      have hty : ty = .ref mu t ∧ tn' = t1 := by
        rcases ht with ⟨_, _, h1, h2⟩ | ⟨_, h1, h2⟩ <;> exact ⟨h1, h2⟩
      obtain ⟨rfl, rfl⟩ := hty
      simp only [evalExpr]
      let child := ec.child rfl 0 (.place p) .place rfl (by trivial)
      have hChildActive := ec.child_activeMatches rfl 0 (.place p) .place rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.place p) .place rfl
        (by trivial) tenv penv).mpr hAccess
      have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.place p) .place rfl
          (by trivial) W.P observation r)
      have hChildFuture : child.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active => simp [child, EvaluationContext.child,
            EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 0 (.place p) .place rfl (by trivial)
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hChildInputFormula : child.inputFuture = p.variables ++ child.outputFuture := by
        cases ec <;> rfl
      have hChildInput : child.inputFuture = ec.inputFuture := by
        rw [hChildInputFormula, hChildFuture]
        cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
          NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
          Place.variables, Expr.variables, DemandNode.visibleAfter]
      refine Sat.bind (ih.place (path ++ [0]) p child observation W tenv penv env s
        _ _ _ _ _ _ _ _ hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
        (by simpa [hChildShrink] using hObserved) hClass hp (by simpa [hChildInput] using hF) htp hr hE) ?_
      rintro l s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1,
        hpl, ⟨hg, _⟩⟩
      simp only [sat_pure]
      have hFrame1 : Frame m W tenv penv env s1 ec.outputFuture := by
        simpa [hChildFuture] using hF1
      have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
        simpa [hChildShrink] using hObserved1
      have hRetained := hRetains1.subset (fun alias hmem =>
        ec.child_retained_subset rfl 0 (.place p) .place rfl (by trivial) hmem)
      refine ⟨hFrame1, hX1, hRoots1, hValues1, hObservedPost, hRetained, hPilot1,
        ?_, fun r hr' => by cases hr'; exact hg⟩
      rcases hpl with ⟨_, hl⟩ | ⟨x, lv, si, v, _, _, _, _, _, hrl, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
      · exact ⟨l, rfl, Or.inl ⟨hrt, hl⟩⟩
      · rw [refTarget_not_refLike hrt] at hrl; cases hrl
      · subst h3; simp [Ty.refTarget] at hrt
    | len v =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨el, b, t1, htv, rfl, rfl⟩ := ht
      obtain ⟨rv, r1, hrv, rfl, rfl⟩ := hr
      simp only [evalExpr]
      let child := ec.child rfl 0 (.view v) .view rfl (by trivial)
      have hChildActive := ec.child_activeMatches rfl 0 (.view v) .view rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.view v) .view rfl
        (by trivial) tenv penv).mpr hAccess
      have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.view v) .view rfl
          (by trivial) W.P observation r)
      have hChildFuture : child.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active => simp [child, EvaluationContext.child,
            EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 0 (.view v) .view rfl (by trivial)
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hChildInputFormula : child.inputFuture = v.variables ++ child.outputFuture := by
        cases ec <;> rfl
      have hChildInput : child.inputFuture = ec.inputFuture := by
        rw [hChildInputFormula, hChildFuture]
        cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
          NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
          View.variables, Expr.variables, DemandNode.visibleAfter]
      refine Sat.bind (ih.view (path ++ [0]) v child observation W tenv penv env s
        _ _ _ _ _ _ _ hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
        (by simpa [hChildShrink] using hObserved) hClass hp (by simpa [hChildInput] using hF) htv hrv hE) ?_
      rintro vw s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1,
        _, _, _, _⟩
      simp only [sat_pure]
      have hFrame1 : Frame m W tenv penv env s1 ec.outputFuture := by
        simpa [hChildFuture] using hF1
      have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
        simpa [hChildShrink] using hObserved1
      have hRetained := hRetains1.subset (fun alias hmem =>
        ec.child_retained_subset rfl 0 (.view v) .view rfl (by trivial) hmem)
      exact ⟨hFrame1, hX1, hRoots1, hValues1, hObservedPost, hRetained,
        hPilot1, rfl, noTargets_int⟩
    | slice mu v lo hi org =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨_, el, b, t1, htv, t2, hlo, t3, hhi, ht⟩ := ht
      have hty : ty = .slice mu el ∧ tn' = t3 := by
        rcases ht with ⟨_, _, h1, h2⟩ | ⟨_, h1, h2⟩ <;> exact ⟨h1, h2⟩
      obtain ⟨rfl, rfl⟩ := hty
      obtain ⟨rv, r1, hrv, r2, hrlo, r3, hrhi, r4, hna, rfl, rfl⟩ := hr
      have hE3 : EffLe r3.eff W.E := (PMono.noteAborts _ _ _ hna).2.trans hE
      have hE2 := (rpBound_mono hrhi).2.trans hE3
      have hE1 := (rpBound_mono hrlo).2.trans hE2
      simp only [evalExpr]
      let viewContext := ec.child rfl 0 (.view v) .view rfl (by trivial)
      let lowContext := ec.child rfl 1 (.bound lo) .bound rfl (by trivial)
      let highContext := ec.child rfl 2 (.bound hi) .bound rfl (by trivial)
      have hViewActive := ec.child_activeMatches rfl 0 (.view v) .view rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hLowActive := ec.child_activeMatches rfl 1 (.bound lo) .bound rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hHighActive := ec.child_activeMatches rfl 2 (.bound hi) .bound rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hViewAccess := (ec.child_accessMatches_iff rfl 0 (.view v) .view rfl
        (by trivial) tenv penv).mpr hAccess
      have hLowAccess := (ec.child_accessMatches_iff rfl 1 (.bound lo) .bound rfl
        (by trivial) tenv penv).mpr hAccess
      have hHighAccess := (ec.child_accessMatches_iff rfl 2 (.bound hi) .bound rfl
        (by trivial) tenv penv).mpr hAccess
      have hViewShrink : viewContext.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.view v) .view rfl
          (by trivial) W.P observation r)
      have hLowShrink : lowContext.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 1 (.bound lo) .bound rfl
          (by trivial) W.P observation r)
      have hHighShrink : highContext.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 2 (.bound hi) .bound rfl
          (by trivial) W.P observation r)
      have hViewFuture : viewContext.outputFuture =
          match ec with
          | .pilot _ active => active
          | .shrink _ context => lo.variables ++ hi.variables ++ context.expected.frame.future := by
        cases ec with
        | pilot profile active => simp [viewContext, EvaluationContext.child,
            EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 0 (.view v) .view rfl (by trivial)
          change transition.context.expected.frame.future =
            lo.variables ++ hi.variables ++ context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hLowFuture : lowContext.outputFuture =
          match ec with
          | .pilot _ active => active
          | .shrink _ context => hi.variables ++ context.expected.frame.future := by
        cases ec with
        | pilot profile active => simp [lowContext, EvaluationContext.child,
            EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 1 (.bound lo) .bound rfl (by trivial)
          change transition.context.expected.frame.future =
            hi.variables ++ context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hHighFuture : highContext.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active => simp [highContext, EvaluationContext.child,
            EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 2 (.bound hi) .bound rfl (by trivial)
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hViewInputFormula : viewContext.inputFuture = v.variables ++ viewContext.outputFuture := by
        cases ec <;> rfl
      have hLowInputFormula : lowContext.inputFuture = lo.variables ++ lowContext.outputFuture := by
        cases ec <;> rfl
      have hHighInputFormula : highContext.inputFuture = hi.variables ++ highContext.outputFuture := by
        cases ec <;> rfl
      have hViewInput : Frame m W tenv penv env s viewContext.inputFuture := by
        cases ec with
        | pilot profile active =>
          apply hF.narrowFuture
          intro x hx
          simp [viewContext, EvaluationContext.inputFuture, EvaluationContext.outputFuture,
            EvaluationContext.child, DemandNode.variables, Expr.variables, View.variables,
            DemandNode.visibleAfter, List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (Or.inr (Or.inr hx))
        | shrink profile context =>
          have hChildFuture : viewContext.outputFuture =
              lo.variables ++ hi.variables ++ context.expected.frame.future := by
            simpa using hViewFuture
          have hChildInput : viewContext.inputFuture =
              v.variables ++ (lo.variables ++ hi.variables ++ context.expected.frame.future) := by
            rw [hViewInputFormula, hChildFuture]
          rw [hChildInput]
          simpa [EvaluationContext.inputFuture, NodeContext.inputFuture, DemandNode.variables,
            Expr.variables, View.variables, List.append_assoc] using hF
      refine Sat.bind (ih.view (path ++ [0]) v viewContext observation W tenv penv env s
        _ _ _ _ _ _ _ hViewActive hViewAccess (by simpa [hViewShrink] using hProtected)
        (by simpa [hViewShrink] using hObserved) hClass hp hViewInput htv hrv hE1) ?_
      rintro vw s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1,
        hvw, hg, hViewAliases, _⟩
      have hObservedView : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
        simpa [hViewShrink] using hObserved1
      have hLowInput : Frame m W tenv penv env s1 lowContext.inputFuture := by
        cases ec with
        | pilot profile active =>
          have hF1' : Frame m W tenv penv env s1 active := by
            simpa [viewContext, EvaluationContext.child, EvaluationContext.outputFuture,
              DemandNode.visibleAfter, DemandNode.visibleForChild] using hF1
          change Frame m W tenv penv env s1 (lo.variables ++ active)
          apply frame_changeFuture hF1'
          intro x hx
          exact (hActive x).mpr hx
        | shrink profile context =>
          simpa [hLowInputFormula, hLowFuture, hViewFuture, List.append_assoc] using hF1
      refine Sat.bind (ih.bound (path ++ [1]) lo lowContext observation W tenv penv env s1
        vw.len 0 _ _ r1 r2 hLowActive hLowAccess (by simpa [hLowShrink] using hProtected)
        (by simpa [hLowShrink] using hObservedView)
        (classified_after hF hClass hX1) hp hLowInput hlo hrlo hE2) ?_
      rintro lo' s2 ⟨hF2, hX2, hRoots2, hValues2, hObserved2, hRetains2, hPilot2, _⟩
      have hObservedLow : ObservedSafe m W (ec.mayShrink W.P observation) observation s2.store := by
        simpa [hLowShrink] using hObserved2
      have hHighInput : Frame m W tenv penv env s2 highContext.inputFuture := by
        cases ec with
        | pilot profile active =>
          have hF2' : Frame m W tenv penv env s2 active := by
            simpa [lowContext, EvaluationContext.child, EvaluationContext.outputFuture,
              DemandNode.visibleAfter, DemandNode.visibleForChild] using hF2
          change Frame m W tenv penv env s2 (hi.variables ++ active)
          apply frame_changeFuture hF2'
          intro x hx
          exact (hActive x).mpr hx
        | shrink profile context =>
          have hChildFuture : lowContext.outputFuture =
              hi.variables ++ context.expected.frame.future := by
            simpa using hLowFuture
          have hInput : highContext.inputFuture =
              hi.variables ++ context.expected.frame.future := by
            rw [hHighInputFormula, hHighFuture]
            simp [EvaluationContext.outputFuture, NodeContext.outputFuture]
          rw [hInput]
          have hF2' : Frame m W tenv penv env s2 lowContext.outputFuture := hF2
          rw [hChildFuture] at hF2'
          exact hF2'
      refine Sat.bind (ih.bound (path ++ [2]) hi highContext observation W tenv penv env s2
        vw.len vw.len _ _ r2 r3 hHighActive hHighAccess (by simpa [hHighShrink] using hProtected)
        (by simpa [hHighShrink] using hObservedLow)
        (classified_after hF1 (classified_after hF hClass hX1) hX2)
        hp hHighInput hhi hrhi hE3) ?_
      rintro hi' s3 ⟨hF3, hX3, hRoots3, hValues3, hObserved3, hRetains3, hPilot3, _⟩
      by_cases hc : 0 ≤ lo' ∧ lo' ≤ hi' ∧ hi' ≤ (vw.len : Int)
      · simp only [hc, and_self, if_true, sat_pure]
        have hFrame3 : Frame m W tenv penv env s3 ec.outputFuture := by
          simpa [hHighFuture] using hF3
        have hSampleSlice : SliceTy s3.store vw.loc vw.start vw.len el := by
          cases ec with
          | pilot profile active =>
            exact ((hvw.mono (hPilot2 profile)).mono (hPilot3 profile)).2.1
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
            have hElement : pc.approvals.access.viewElement? v = some el := by
              rw [hEnv]
              exact tyView_accessElement hMod hVars htv
            let transition := context.child rfl 1 (.bound lo) .bound rfl (by trivial)
            cases hAccessRoots : pc.approvals.access.viewRoots v with
            | error err =>
              have hInvalid : (DemandNode.expression (.slice mu v lo hi org)).childFrame
                  pc.approvals.access path context.expected.frame 1 = .error err := by
                have hExpectation : (DemandNode.expression (.slice mu v lo hi org)).childExpectation?
                    pc.approvals.access
                    ⟨path, .expression, context.expected.frame.active,
                      context.expected.frame.future, context.expected.frame.retained⟩ 1 =
                    some ⟨context.expected.frame.active,
                      hi.variables ++ context.expected.frame.future⟩ := by
                  simp [DemandNode.childExpectation?, DemandNode.child?, DemandNode.children,
                    DemandNode.childFuture, DemandNode.visibleForChild]
                simp [DemandNode.childFrame, hExpectation, DemandNode.retainedForChild,
                  AccessEnv.aliasView, hElement, hAccessRoots, Functor.map, Except.map]
              have hChecked := transition.childFrameEq
              rw [hInvalid] at hChecked
              cases hChecked
            | ok roots =>
              let alias : RetainedAlias :=
                ⟨.slice .readOnly el, roots, .operand (path ++ [0])⟩
              have hAliases : pc.approvals.access.aliasView (path ++ [0]) v =
                  .ok [alias] := by
                simp [AccessEnv.aliasView, hElement, hAccessRoots, alias] <;> rfl
              have hAliasMem : alias ∈ lowContext.retained := by
                have hNew : (DemandNode.expression (.slice mu v lo hi org)).retainedForChild
                    pc.approvals.access path 1 = .ok [alias] := by
                  simp [DemandNode.retainedForChild, hAliases]
                have hChild := DemandNode.childFrame_newAlias
                  (result := transition.childFrame) (aliases := [alias]) (alias := alias)
                  transition.childFrameEq hNew (by simp)
                change alias ∈ transition.context.expected.frame.retained
                rw [transition.expectedFrameEq]
                exact DemandNode.phaseFrame_retains transition.phaseFrameEq hChild
              have hAlias := AliasAt.ofAliasView (m := m) (alias := alias) (penv := penv)
                (by rw [← hEnv]; exact hAliases)
                (by rw [← hEnv]; exact hElement) hrv hvw hg
              have hPostLow := (hRetains2 alias hAliasMem).typed
                (.slice vw.loc vw.start vw.len) hAlias
              have hAliasMemHigh : alias ∈ highContext.retained := by
                let transition := context.child rfl 2 (.bound hi) .bound rfl (by trivial)
                have hNew : (DemandNode.expression (.slice mu v lo hi org)).retainedForChild
                    pc.approvals.access path 2 = .ok [alias] := by
                  simp [DemandNode.retainedForChild, hAliases]
                have hChild := DemandNode.childFrame_newAlias
                  (result := transition.childFrame) (aliases := [alias]) (alias := alias)
                  transition.childFrameEq hNew (by simp)
                change alias ∈ transition.context.expected.frame.retained
                rw [transition.expectedFrameEq]
                exact DemandNode.phaseFrame_retains transition.phaseFrameEq hChild
              have hPostHigh := (hRetains3 alias hAliasMemHigh).typed
                (.slice vw.loc vw.start vw.len) hPostLow
              obtain ⟨l, start, count, heq, _, hslice⟩ := hPostHigh.1
              cases heq
              exact hslice
        have hRetained1 := hRetains1.subset (fun alias hmem =>
          ec.child_retained_subset rfl 0 (.view v) .view rfl (by trivial) hmem)
        have hRetained2 := hRetains2.subset (fun alias hmem =>
          ec.child_retained_subset rfl 1 (.bound lo) .bound rfl (by trivial) hmem)
        have hRetained3 := hRetains3.subset (fun alias hmem =>
          ec.child_retained_subset rfl 2 (.bound hi) .bound rfl (by trivial) hmem)
        refine ⟨hFrame3, Footprint.trans (Footprint.trans hX1 hX2) hX3,
          PreservesRootTypes.trans (PreservesRootTypes.trans hRoots1 hRoots2) hRoots3,
          PreservesValues.trans (PreservesValues.trans hValues1 hValues2) hValues3,
          by simpa [hHighShrink] using hObserved3,
          hRetained1.trans (hRetained2.trans hRetained3),
          pilotStoreLe_trans hPilot1 (pilotStoreLe_trans hPilot2 hPilot3),
          ⟨_, _, _, rfl, hvw.1, hSampleSlice.sub (by omega)⟩, fun r hr' => by cases hr'; exact hg⟩
      · simp only [hc, if_false, sat_abort]
    | push owner a org =>
      have hprofileOrg :
          (m.profile = ArtifactProfile.pilot ∧ org = none) ∨
          (m.profile = ArtifactProfile.shrink ∧ ∃ o, org = some o) := by
        have hprofileOrg := tyExpr_push_profileOrg_ok tenv owner a org ty tn tn' ht
        rw [hF.mod_t] at hprofileOrg
        exact hprofileOrg
      simp only [tyExpr] at ht
      rw [hF.mod_t] at ht
      have hcore : ∃ t b contents t1,
          tyPlace tenv owner tn = .ok ({ ty := t, bindingWritable := b, contentsWritable := contents }, t1) ∧
            ∃ ownerEl ownerState, ownerElement tenv t t1 = .ok (ownerEl, ownerState) ∧
              ∃ argTy argState, tyExpr tenv a ownerState = .ok (argTy, argState) ∧
                argTy = ownerEl ∧
                  (requireWrite "push"
                    (({ ty := t, bindingWritable := b, contentsWritable := contents } : PlaceInfo).ownerMutationWritable tenv.mod.profile) >>= fun _ => pure (.ref .mutable ownerEl)) argState =
                    .ok (ty, tn') := by
        rcases hprofileOrg with ⟨hprofile, horg⟩ | ⟨hprofile, ⟨origin, horg⟩⟩
        · have hprofileT : tenv.mod.profile = ArtifactProfile.pilot :=
            (congrArg Module.profile hF.mod_t).trans hprofile
          simp [tyExpr, hF.mod_t, hprofile, hprofileT, horg, checkOrg] at ht
          inv at ht
          simpa [hprofileT] using ht
        · have hprofileT : tenv.mod.profile = ArtifactProfile.shrink :=
            (congrArg Module.profile hF.mod_t).trans hprofile
          simp [tyExpr, hF.mod_t, hprofile, hprofileT, horg, checkOrg] at ht
          inv at ht
          simpa [hprofileT] using ht.2
      obtain ⟨t, b, contents, t1, htp, ht⟩ := hcore
      simp only [rpExpr] at hr
      rw [hF.mod_p] at hr
      rcases (st_bind_ok _ _ _ _).1 hr with ⟨rp, r1, hrp, hrest1⟩
      rcases (st_bind_ok _ _ _ _).1 hrest1 with ⟨ra, r2, hra, hrest2⟩
      rcases (st_bind_ok _ _ _ _).1 hrest2 with ⟨_, r3Eval, hgrEval, htail⟩
      let r3 : RState := { r2 with eff := { r2.eff with grows := addTargets r2.eff.grows (rootsTargets rp) } }
      have hgr : addGrows rp r2 = .ok ((), r3) := by
        unfold addGrows addRoots
        apply (st_modify_ok _ _ _).2
        rfl
      have hr3 : r3Eval = r3 := by
        have hstate := congrArg Prod.snd (Except.ok.inj (hgr.symm.trans hgrEval))
        exact hstate.symm
      rw [hr3] at htail
      rw [← hF.mod_p] at htail
      obtain ⟨_, hin⟩ := addGrows_ok _ _ _ hgr
      have hE3 : EffLe r3.eff W.E :=
        ((PMono.profileWriteAbortValue penv owner rp) r3 rho rst' htail).2.trans hE
      have hE2 : EffLe r2.eff W.E := (PMono.addGrows _ _ _ _ hgr).2.trans hE3
      obtain ⟨ownerEl, ownerState, hownerRun, hafterOwner⟩ := ht
      obtain ⟨ta, t2, hta, heq, hwrite⟩ := hafterOwner
      have hownerFacts := ownerElement_ok tenv t ownerEl t1 ownerState hownerRun
      have hresolved : checkResolvedType m t = .ok () := by
        rw [← hF.mod_t]
        exact hownerFacts.1
      have hownerType : t.ownerElem? = some ownerEl := hownerFacts.2.1
      have htaOwner : ta = ownerEl := by simpa using heq
      subst ta
      have hwriteOut : (ty, tn') = (.ref .mutable ownerEl, t2) := by
        have hwriteBind :
            (requireWrite "push"
              (({ ty := t, bindingWritable := b, contentsWritable := contents } : PlaceInfo).ownerMutationWritable tenv.mod.profile) >>= fun _ =>
              pure (.ref .mutable ownerEl)) t2 = .ok (ty, tn') := by
          simpa [Functor.map, StateT.map] using hwrite
        obtain ⟨_, state, hreq, hmap⟩ := (st_bind_ok _ _ _ _).1 hwriteBind
        have hstate := (requireWrite_ok "push"
          (({ ty := t, bindingWritable := b, contentsWritable := contents } : PlaceInfo).ownerMutationWritable tenv.mod.profile)
          t2 ((), state)).1 hreq |>.2
        have hwritePair : (ty, tn') = (.ref .mutable ownerEl, state) :=
          (st_pure_ok _ _ _).1 hmap
        cases hwritePair
        simpa [hstate]
      have htyOut : ty = .ref .mutable ownerEl := congrArg Prod.fst hwriteOut
      subst ty
      have hrho : rho = rp := by
        cases hprofile : penv.mod.profile with
        | pilot =>
            simp [hprofile, st_pure_ok] at htail
            exact htail.1
        | shrink =>
            simp [hprofile, st_bind_ok] at htail
            rcases htail with ⟨_, _, _, htail⟩
            rcases htail with ⟨_, _, hpure⟩ | ⟨state, _, hmap⟩
            · exact congrArg Prod.fst ((st_pure_ok _ _ _).1 hpure)
            · have hmapBind : (noteAborts >>= fun _ => pure rp) state = .ok (rho, rst') := by
                simpa [Functor.map, StateT.map] using hmap
              obtain ⟨_, state, _, hpure⟩ := (st_bind_ok _ _ _ _).1 hmapBind
              exact congrArg Prod.fst ((st_pure_ok _ _ _).1 hpure)
      simp only [evalExpr]
      let placeContext := ec.child rfl 0 (.place owner) .place rfl (by trivial)
      let argContext := ec.child rfl 1 (.expression a) .expression rfl (by trivial)
      have hPlaceActive := ec.child_activeMatches rfl 0 (.place owner) .place rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hArgActive := ec.child_activeMatches rfl 1 (.expression a) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hPlaceAccess := (ec.child_accessMatches_iff rfl 0 (.place owner) .place rfl
        (by trivial) tenv penv).mpr hAccess
      have hArgAccess := (ec.child_accessMatches_iff rfl 1 (.expression a) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hPlaceShrink : placeContext.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.place owner) .place rfl
          (by trivial) W.P observation r)
      have hArgShrink : argContext.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 1 (.expression a) .expression rfl
          (by trivial) W.P observation r)
      have hPlaceFuture : placeContext.outputFuture =
          match ec with
          | .pilot _ active => active
          | .shrink _ context => a.variables ++ context.expected.frame.future := by
        cases ec with
        | pilot profile active => simp [placeContext, EvaluationContext.child,
            EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 0 (.place owner) .place rfl (by trivial)
          change transition.context.expected.frame.future =
            a.variables ++ context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hArgFuture : argContext.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active => simp [argContext, EvaluationContext.child,
            EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 1 (.expression a) .expression rfl (by trivial)
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hPlaceInputFormula : placeContext.inputFuture = owner.variables ++ placeContext.outputFuture := by
        cases ec <;> rfl
      have hArgInputFormula : argContext.inputFuture = a.variables ++ argContext.outputFuture := by
        cases ec <;> rfl
      have hPlaceInput : Frame m W tenv penv env s placeContext.inputFuture := by
        cases ec with
        | pilot profile active =>
          apply hF.narrowFuture
          intro x hx
          simp [placeContext, EvaluationContext.inputFuture, EvaluationContext.outputFuture,
            EvaluationContext.child, DemandNode.variables, Expr.variables, Place.variables,
            DemandNode.visibleAfter, List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (Or.inr hx)
        | shrink profile context =>
          rw [hPlaceInputFormula, hPlaceFuture]
          simpa [EvaluationContext.inputFuture, NodeContext.inputFuture,
            EvaluationContext.outputFuture, NodeContext.outputFuture,
            DemandNode.variables, Expr.variables, Place.variables, List.append_assoc] using hF
      refine Sat.bind (ih.place (path ++ [0]) owner placeContext observation W tenv penv env s
        tn t1 t b contents rst r1 rp hPlaceActive hPlaceAccess
        (by simpa [hPlaceShrink] using hProtected)
        (by simpa [hPlaceShrink] using hObserved) hClass hp hPlaceInput htp hrp
        ((rpExpr_mono hra).2.trans hE2)) ?_
      rintro l s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1,
        hpl, ⟨hg, _⟩⟩
      have hObservedPlace : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
        simpa [hPlaceShrink] using hObserved1
      have hPlaceOk : PlaceOk m W.G W.P penv env s1.store owner l t := hpl
      have hArgInput : Frame m W tenv penv env s1 argContext.inputFuture := by
        cases ec with
        | pilot profile active =>
          have hF1' : Frame m W tenv penv env s1 active := by
            simpa [placeContext, EvaluationContext.child, EvaluationContext.outputFuture,
              DemandNode.visibleAfter, DemandNode.visibleForChild] using hF1
          change Frame m W tenv penv env s1 (a.variables ++ active)
          apply frame_changeFuture hF1'
          intro x hx
          exact (hActive x).mpr hx
        | shrink profile context =>
          rw [hArgInputFormula, hArgFuture]
          rw [hPlaceFuture] at hF1
          simpa [EvaluationContext.inputFuture, NodeContext.inputFuture,
            EvaluationContext.outputFuture, NodeContext.outputFuture,
            DemandNode.variables, Expr.variables, Place.variables, List.append_assoc] using hF1
      refine Sat.bind (ih.expr (path ++ [1]) a argContext observation W tenv penv env s1
        _ _ ownerEl r1 r2 ra hArgActive hArgAccess (by simpa [hArgShrink] using hProtected)
        (by simpa [hArgShrink] using hObservedPlace)
        (classified_after hF hClass hX1) hp hArgInput hta hra hE2) ?_
      rintro v s2 ⟨hF2, hX2, hRoots2, hValues2, hObserved2, hRetains2, hPilot2, hv,
        ⟨hgv, _⟩⟩
      have hFrame2 : Frame m W tenv penv env s2 ec.outputFuture := by
        simpa [hArgFuture] using hF2
      have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s2.store := by
        simpa [hArgShrink] using hObserved2
      have hRetainedArg := hRetains2.subset (fun alias hmem =>
        ec.child_retained_subset rfl 1 (.expression a) .expression rfl (by trivial) hmem)
      have hRetained := hRetains1.subset (fun alias hmem =>
        ec.child_retained_subset rfl 0 (.place owner) .place rfl (by trivial) hmem)
      rcases hpl with ⟨hrt, hl, hheader⟩ | ⟨x, lv, si, v', _, _, _, _, _, hrl, _⟩ |
        ⟨_, _, _, _, _, _, _, _, _, h3, _⟩
      · have hfl : ownerEl.flat = true := by
          cases t <;> simp_all [Ty.ownerElem?, Ty.refTarget]
        have hlt : LocTy s2.store l t := by
          rcases hprofileOrg with ⟨hprofile, _⟩ | ⟨hprofile, _⟩
          · exact access hp (hl.mono (hPilot2 hprofile)) hg
              (fun t' ht' => Or.inr (Or.inr (Or.inl (hE3.2.2.1 t' (hin t' ht')))))
          · cases ec with
            | pilot profile _ => cases profile.symm.trans hprofile
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
              have hplaceType : penv.access.placeType? owner = some t :=
                tyPlace_accessType hMod hVars htp
              let transition := context.child rfl 1 (.expression a) .expression rfl (by trivial)
              have hOwnerRoots : ∃ roots, penv.access.placeRoots owner = .ok roots := by
                cases hroots : penv.access.placeRoots owner with
                | error err =>
                  have hbad :
                      (DemandNode.expression (.push owner a org)).childFrame
                        penv.access path context.expected.frame 1 = .error err := by
                    have hExpectation :
                        (DemandNode.expression (.push owner a org)).childExpectation?
                            penv.access
                            ⟨path, .expression, context.expected.frame.active,
                              context.expected.frame.future, context.expected.frame.retained⟩ 1 =
                          some ⟨context.expected.frame.active, context.expected.frame.future⟩ := by
                      simp [DemandNode.childExpectation?, DemandNode.child?, DemandNode.children,
                        DemandNode.childFuture, DemandNode.visibleForChild]
                    simp [DemandNode.childFrame, hExpectation, DemandNode.retainedForChild,
                      AccessEnv.aliasPlace, hplaceType, hownerType, hroots, Functor.map, Except.map]
                  have htransition := transition.childFrameEq
                  rw [hEnv] at htransition
                  rw [hbad] at htransition
                  cases htransition
                | ok roots => exact ⟨roots, rfl⟩
              obtain ⟨roots, hOwnerRoots⟩ := hOwnerRoots
              let ownerAlias : RetainedAlias :=
                ⟨.ref .mutable t, roots, .operand (path ++ [0])⟩
              have hAliasQuery : penv.access.aliasPlace (path ++ [0]) owner = .ok [ownerAlias] := by
                simp [AccessEnv.aliasPlace, hplaceType, hownerType, hOwnerRoots, ownerAlias,
                  Functor.map, Except.map]
              have hAliasQueryCtx : pc.approvals.access.aliasPlace (path ++ [0]) owner =
                  .ok [ownerAlias] := by rw [hEnv]; exact hAliasQuery
              have hnew : (DemandNode.expression (.push owner a org)).retainedForChild
                  pc.approvals.access path 1 = .ok [ownerAlias] := by
                simp [DemandNode.retainedForChild, hAliasQueryCtx]
              have hAliasMem : ownerAlias ∈ argContext.retained := by
                have hChild := DemandNode.childFrame_newAlias
                  (result := transition.childFrame) (aliases := [ownerAlias])
                  (alias := ownerAlias) transition.childFrameEq hnew
                  (List.mem_cons.mpr (Or.inl rfl))
                change ownerAlias ∈ transition.context.expected.frame.retained
                rw [transition.expectedFrameEq]
                exact DemandNode.phaseFrame_retains transition.phaseFrameEq hChild
              have hrepresentable : t.refTarget = true ∨ t.isSlice = true := by
                cases t <;> simp_all [Ty.ownerElem?, Ty.refTarget, Ty.isSlice]
              have hAliasSource : AliasAt m W env s1.store ownerAlias (.ref l) :=
                AliasAt.ofAliasPlace hAliasQuery hplaceType hrp hPlaceOk hg hrepresentable
              have hAliasPost := (hRetains2 ownerAlias hAliasMem).typed (.ref l) hAliasSource
              have hLocOkPost : LocOk m W.G s2.store l t := by
                rcases hAliasPost.1 with ⟨l', heq, hloc⟩
                cases heq
                rcases hloc with ⟨_, hloc, _⟩ | ⟨hslice, _, _⟩
                · exact hloc
                · cases t <;> simp_all [Ty.isSlice, Ty.ownerElem?]
              exact access hp hLocOkPost hg
                (fun t' ht' => Or.inr (Or.inr (Or.inl (hE3.2.2.1 t' (hin t' ht')))))
        have hvs : ∀ (i : Nat) (e : Val), (#[v] : Array Val)[i]? = some e → FlatTy ownerEl e := by
          intro i e he
          cases i <;> simp at he
          subst he; exact hv.flat hfl
        rcases hprofileOrg with ⟨hprofile, horg⟩ | ⟨_, ⟨origin, horg⟩⟩
        · cases horg
          have hownerGrow : t = .grow ownerEl := by
            cases t with
            | grow el => simpa [Ty.ownerElem?] using hownerType
            | growshrink el =>
              have heq : el = ownerEl := by simpa [Ty.ownerElem?] using hownerType
              subst ownerEl
              simp [checkResolvedType, hprofile, reject, bind, Except.bind] at hresolved
            | limited el capacity =>
              have heq : el = ownerEl := by simpa [Ty.ownerElem?] using hownerType
              subst ownerEl
              simp [checkResolvedType, hprofile, reject, bind, Except.bind] at hresolved
            | int _ | bool | unit | arr _ _ | ref _ _ | slice _ _ | tuple _ | structT _ _ =>
              simp [Ty.ownerElem?] at hownerType
          have hltGrow : LocTy s2.store l (.grow ownerEl) := by simpa [hownerGrow] using hlt
          refine sat_appendLoc_bind hltGrow (fun st' i happ => ?_)
          simp only [sat_pure]
          obtain ⟨hle, _, _, hread, hi, hnew⟩ :=
            append_le s2.store st' l #[v] i ownerEl hltGrow hvs happ
          have hstep := append_flatStep _ _ _ _ _ _ hltGrow hvs happ
          have hpath : l.path = [] :=
            PlaceOk.ownerHeader hPlaceOk (by rw [hownerType]; rfl)
          have hrootsAppend : PreservesRootTypes m W.G observation.roots s2.store st' :=
            PreservesRootTypes.appendOwnerStep (elem := ownerEl) hltGrow hpath
            (by simp [Ty.ownerElem?]) happ hstep
          have hvaluesAppend : PreservesValues m W.G observation.values s2.store st' := by
            intro value valueTy hvalue htyped
            exact HasTy.mono hstep.le htyped
          have hsafeAppend := hObservedPost.flatStep hrootsAppend hstep
          have hretainedAppend : RetainsAliases m W env s2.store st' ec.retained :=
            RetainsAliases.storeLe hstep.le
          have hfootAppend : Footprint (insts env) (Dset W) s2 { s2 with store := st' } :=
            Footprint.of_flatStep hstep
          have hpilotAppend : PilotStoreLe m s2 { s2 with store := st' } := by
            intro _
            exact hstep.le
          have hrootsOut := PreservesRootTypes.trans
            (PreservesRootTypes.trans hRoots1 hRoots2) hrootsAppend
          have hvaluesOut := PreservesValues.trans
            (PreservesValues.trans hValues1 hValues2) hvaluesAppend
          have hsafeOut := hsafeAppend
          have hretainedOut := RetainsAliases.trans
            (RetainsAliases.trans hRetained hRetainedArg) hretainedAppend
          have hpilotOut := pilotStoreLe_trans
            (pilotStoreLe_trans hPilot1 hPilot2) hpilotAppend
          have hnew := hnew 0 v (by simp)
          refine ⟨hFrame2.flatStep hstep, (hX1.trans hX2).trans hfootAppend,
            hrootsOut, hvaluesOut, hsafeOut, hretainedOut, hpilotOut,
            ⟨_, rfl, Or.inl ⟨flat_refTarget hfl, Or.inl ⟨v, ?_, hv.flat hfl⟩,
              HeaderLoc.ofFlat hfl⟩⟩,
            fun r hr' => by cases hr'; simpa [hrho] using hg⟩
          simpa using hnew
        · cases horg
          refine sat_checkedAppendLoc_bind hlt hownerType hfl hvs (fun st' i happ hstep => ?_)
          simp only [sat_pure]
          have happLe : StoreLe s2.store st' ∧ LocTy st' l t ∧
              ∀ (j : Nat) (e : Val), (#[v] : Array Val)[j]? = some e →
                st'.read ⟨l.root, l.path ++ [i + j]⟩ = .ok e := by
            cases t with
            | grow el =>
              have heq : el = ownerEl := by simpa [Ty.ownerElem?] using hownerType
              subst ownerEl
              obtain ⟨hle, hpost, _, _, _, hnew⟩ := append_le s2.store st' l #[v] i el hlt hvs happ
              exact ⟨hle, hpost, hnew⟩
            | growshrink el =>
              have heq : el = ownerEl := by simpa [Ty.ownerElem?] using hownerType
              subst ownerEl
              obtain ⟨hle, hpost, _, _, _, hnew⟩ :=
                append_le_growshrink s2.store st' l #[v] i el hlt hvs happ
              exact ⟨hle, hpost, hnew⟩
            | limited el capacity =>
              have heq : el = ownerEl := by simpa [Ty.ownerElem?] using hownerType
              subst ownerEl
              obtain ⟨hle, hpost, _, _, _, hn, _, _, hnew, _⟩ :=
                append_le_limited s2.store st' l #[v] i el capacity hfl hlt hvs happ
              rw [← hn] at hnew
              exact ⟨hle, hpost, hnew⟩
            | int _ | bool | unit | arr _ _ | ref _ _ | slice _ _ | tuple _ | structT _ _ =>
              simp [Ty.ownerElem?] at hownerType
          have hstep := append_flatStep_owner s2.store st' l #[v] i t ownerEl hownerType hfl hlt hvs happ
          have hnew := happLe.2.2 0 v (by simp)
          have hpath : l.path = [] :=
            PlaceOk.ownerHeader hPlaceOk (by rw [hownerType]; rfl)
          have hrootsAppend : PreservesRootTypes m W.G observation.roots s2.store st' :=
            PreservesRootTypes.appendOwnerStep (elem := ownerEl) hlt hpath
            hownerType happ hstep
          have hvaluesAppend : PreservesValues m W.G observation.values s2.store st' := by
            intro value valueTy hvalue htyped
            exact HasTy.mono hstep.le htyped
          have hsafeAppend := hObservedPost.flatStep hrootsAppend hstep
          have hretainedAppend : RetainsAliases m W env s2.store st' ec.retained :=
            RetainsAliases.storeLe hstep.le
          have hfootAppend : Footprint (insts env) (Dset W) s2 { s2 with store := st' } :=
            Footprint.of_flatStep hstep
          have hpilotAppend : PilotStoreLe m s2 { s2 with store := st' } := by
            intro _
            exact hstep.le
          have hrootsOut := PreservesRootTypes.trans
            (PreservesRootTypes.trans hRoots1 hRoots2) hrootsAppend
          have hvaluesOut := PreservesValues.trans
            (PreservesValues.trans hValues1 hValues2) hvaluesAppend
          have hretainedOut := RetainsAliases.trans
            (RetainsAliases.trans hRetained hRetainedArg) hretainedAppend
          have hpilotOut := pilotStoreLe_trans
            (pilotStoreLe_trans hPilot1 hPilot2) hpilotAppend
          refine ⟨hFrame2.flatStep hstep, (hX1.trans hX2).trans hfootAppend,
            hrootsOut, hvaluesOut, hsafeAppend, hretainedOut, hpilotOut,
            ⟨_, rfl, Or.inl ⟨flat_refTarget hfl, Or.inl ⟨v, ?_, hv.flat hfl⟩,
              HeaderLoc.ofFlat hfl⟩⟩,
            fun r hr' => by cases hr'; simpa [hrho] using hg⟩
          simpa using hnew
      · simp [Ty.isRefLike] at hrl
        cases t <;> simp_all [Ty.isRefLike, Ty.ownerElem?]
      · rw [h3] at hownerType
        simp [Ty.ownerElem?] at hownerType
    | ifE c t f =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨tc, t1, htc, rfl, tt, t2, htt, ft, t3, htf, heq, rfl, rfl⟩ := ht
      obtain ⟨rc, r1, hrc, rt, lt1, lt2, r2, hrt, rf, lf1, lf2, r3, hrf, rfl, rfl⟩ := hr
      have hft : ft = ty := by
        have : ty = ft := by simpa using heq
        exact this.symm
      subst hft
      simp only [evalExpr]
      let condition := ec.child rfl 0 (.expression c) .expression rfl (by trivial)
      let thenContext := ec.child rfl 1 (.block t) .block rfl (by trivial)
      let elseContext := ec.child rfl 2 (.block f) .block rfl (by trivial)
      have hConditionActive := ec.child_activeMatches rfl 0 (.expression c) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hThenActive := ec.child_activeMatches rfl 1 (.block t) .block rfl
        (by trivial) tenv (exprEnv tenv) hActive (by intro x; rfl)
      have hElseActive := ec.child_activeMatches rfl 2 (.block f) .block rfl
        (by trivial) tenv (exprEnv tenv) hActive (by intro x; rfl)
      have hConditionAccess := (ec.child_accessMatches_iff rfl 0 (.expression c) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hThenAccess := (ec.child_accessMatches_iff rfl 1 (.block t) .block rfl
        (by trivial) tenv penv).mpr hAccess
      have hElseAccess := (ec.child_accessMatches_iff rfl 2 (.block f) .block rfl
        (by trivial) tenv penv).mpr hAccess
      have hConditionShrink : condition.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.expression c) .expression rfl
          (by trivial) W.P observation r)
      have hThenShrink : thenContext.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 1 (.block t) .block rfl
          (by trivial) W.P observation r)
      have hElseShrink : elseContext.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 2 (.block f) .block rfl
          (by trivial) W.P observation r)
      have hConditionFuture : condition.outputFuture =
          match ec with
          | .pilot _ active => active
          | .shrink _ context => t.variables ++ f.variables ++ context.expected.frame.future := by
        cases ec with
        | pilot profile active => simp [condition, EvaluationContext.child,
            EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 0 (.expression c) .expression rfl (by trivial)
          change transition.context.expected.frame.future =
            t.variables ++ f.variables ++ context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hConditionInput : condition.inputFuture = c.variables ++ condition.outputFuture := by
        cases ec <;> rfl
      have hConditionFrame : Frame m W tenv penv env s condition.inputFuture := by
        cases ec with
        | pilot profile active =>
          apply hF.narrowFuture
          intro x hx
          simp only [condition, EvaluationContext.child, EvaluationContext.inputFuture,
            DemandNode.variables, Expr.variables, DemandNode.visibleAfter,
            DemandNode.visibleForChild, List.mem_append] at hx ⊢
          rcases hx with hc | ha
          · exact Or.inl (Or.inl (Or.inl hc))
          · exact Or.inr ha
        | shrink profile context =>
          rw [hConditionInput]
          rw [hConditionFuture]
          simpa [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
            NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
            Expr.variables, List.append_assoc] using hF
      refine Sat.bind (ih.expr (path ++ [0]) c condition observation W tenv penv env s
        _ _ _ _ _ _ hConditionActive hConditionAccess
        (by simpa [hConditionShrink] using hProtected)
        (by simpa [hConditionShrink] using hObserved) hClass hp hConditionFrame htc hrc
        ((rpBlockValue_mono hrt).2.trans ((rpBlockValue_mono hrf).2.trans hE))) ?_
      rintro vc s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hv, _⟩
      obtain ⟨x, rfl⟩ := hasTy_bool hv
      simp only [expectBool, sat_pure_bind]
      cases x
      · simp only [Bool.false_eq_true, if_false]
        have hBranchInput : elseContext.inputFuture = f.variables ++ elseContext.outputFuture := by
          cases ec <;> rfl
        have hBranchOutput : elseContext.outputFuture = ec.outputFuture := by
          cases ec with
          | pilot profile active => simp [elseContext, EvaluationContext.child,
              EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
          | shrink profile context =>
            let transition := context.child rfl 2 (.block f) .block rfl (by trivial)
            change transition.context.expected.frame.future = context.expected.frame.future
            rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
            exact DemandNode.childFrame_future transition.childFrameEq rfl
        have hBranchFrame : Frame m W tenv penv env s1 elseContext.inputFuture := by
          cases ec with
          | pilot profile active =>
            have hF1' : Frame m W tenv penv env s1 active := by
              simpa [condition, EvaluationContext.child, EvaluationContext.outputFuture,
                DemandNode.visibleAfter, DemandNode.visibleForChild] using hF1
            change Frame m W tenv penv env s1 (f.variables ++ active)
            apply frame_changeFuture hF1'
            intro y hy
            exact (hActive y).mpr hy
          | shrink profile context =>
            have hCond : Frame m W tenv penv env s1
                (t.variables ++ f.variables ++ context.expected.frame.future) := by
              have hFuture : condition.outputFuture =
                  t.variables ++ f.variables ++ context.expected.frame.future := by
                simpa using hConditionFuture
              exact hFuture ▸ hF1
            rw [hBranchInput, hBranchOutput]
            apply hCond.narrowFuture
            intro y hy
            simp only [List.mem_append] at hy ⊢
            rcases hy with hf | hfuture
            · exact Or.inl (Or.inr hf)
            · exact Or.inr hfuture
        refine (ih.blockValue (path ++ [2]) f elseContext observation W tenv penv env s1
          _ _ _ _ _ _ _ hElseActive hElseAccess (by simpa [hElseShrink] using hProtected)
          (by simpa [hElseShrink, hConditionShrink] using hObserved1)
          (classified_after hF hClass hX1) hp hBranchFrame htf hrf hE).mono ?_
        rintro v s2 ⟨hF2, hX2, hRoots2, hValues2, hObserved2, hRetains2, hPilot2, hv2,
          ⟨hg, _⟩⟩
        have hFrameOut : Frame m W tenv penv env s2 ec.outputFuture := by
          simpa [hBranchOutput] using hF2
        have hRetained1 := hRetains1.subset (fun alias hmem =>
          ec.child_retained_subset rfl 0 (.expression c) .expression rfl (by trivial) hmem)
        have hRetained2 := hRetains2.subset (fun alias hmem =>
          ec.child_retained_subset rfl 2 (.block f) .block rfl (by trivial) hmem)
        refine ⟨hFrameOut, Footprint.trans hX1 hX2, PreservesRootTypes.trans hRoots1 hRoots2,
          PreservesValues.trans hValues1 hValues2, by simpa [hElseShrink] using hObserved2,
          ?_, pilotStoreLe_trans hPilot1 hPilot2, hv2,
          fun r hr' => (hg r hr').subset (unionRoots_right _ _)⟩
        intro alias hmem
        exact RetainsAlias.trans (hRetained1 alias hmem) (hRetained2 alias hmem)
      · simp only [if_true]
        have hBranchInput : thenContext.inputFuture = t.variables ++ thenContext.outputFuture := by
          cases ec <;> rfl
        have hBranchOutput : thenContext.outputFuture = ec.outputFuture := by
          cases ec with
          | pilot profile active => simp [thenContext, EvaluationContext.child,
              EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
          | shrink profile context =>
            let transition := context.child rfl 1 (.block t) .block rfl (by trivial)
            change transition.context.expected.frame.future = context.expected.frame.future
            rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
            exact DemandNode.childFrame_future transition.childFrameEq rfl
        have hBranchFrame : Frame m W tenv penv env s1 thenContext.inputFuture := by
          cases ec with
          | pilot profile active =>
            have hF1' : Frame m W tenv penv env s1 active := by
              simpa [condition, EvaluationContext.child, EvaluationContext.outputFuture,
                DemandNode.visibleAfter, DemandNode.visibleForChild] using hF1
            change Frame m W tenv penv env s1 (t.variables ++ active)
            apply frame_changeFuture hF1'
            intro y hy
            exact (hActive y).mpr hy
          | shrink profile context =>
            have hCond : Frame m W tenv penv env s1
                (t.variables ++ f.variables ++ context.expected.frame.future) := by
              have hFuture : condition.outputFuture =
                  t.variables ++ f.variables ++ context.expected.frame.future := by
                simpa using hConditionFuture
              exact hFuture ▸ hF1
            rw [hBranchInput, hBranchOutput]
            apply hCond.narrowFuture
            intro y hy
            simp only [List.mem_append] at hy ⊢
            rcases hy with ht | hfuture
            · exact Or.inl (Or.inl ht)
            · exact Or.inr hfuture
        refine (ih.blockValue (path ++ [1]) t thenContext observation W tenv penv env s1
          _ _ _ _ _ _ _ hThenActive hThenAccess (by simpa [hThenShrink] using hProtected)
          (by simpa [hThenShrink, hConditionShrink] using hObserved1)
          (classified_after hF hClass hX1) hp hBranchFrame htt hrt
          ((rpBlockValue_mono hrf).2.trans hE)).mono ?_
        rintro v s2 ⟨hF2, hX2, hRoots2, hValues2, hObserved2, hRetains2, hPilot2, hv2,
          ⟨hg, _⟩⟩
        have hFrameOut : Frame m W tenv penv env s2 ec.outputFuture := by
          simpa [hBranchOutput] using hF2
        have hRetained1 := hRetains1.subset (fun alias hmem =>
          ec.child_retained_subset rfl 0 (.expression c) .expression rfl (by trivial) hmem)
        have hRetained2 := hRetains2.subset (fun alias hmem =>
          ec.child_retained_subset rfl 1 (.block t) .block rfl (by trivial) hmem)
        refine ⟨hFrameOut, Footprint.trans hX1 hX2, PreservesRootTypes.trans hRoots1 hRoots2,
          PreservesValues.trans hValues1 hValues2, by simpa [hThenShrink] using hObserved2,
          ?_, pilotStoreLe_trans hPilot1 hPilot2, hv2,
          fun r hr' => (hg r hr').subset (unionRoots_left _ _)⟩
        intro alias hmem
        exact RetainsAlias.trans (hRetained1 alias hmem) (hRetained2 alias hmem)
    | blockE b =>
      simp only [tyExpr] at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨rho', l1, l2, r1, hrb, rfl, rfl⟩ := hr
      simp only [evalExpr]
      let child := ec.child rfl 0 (.block b) .block rfl (by trivial)
      have hChildActive := ec.child_activeMatches rfl 0 (.block b) .block rfl
        (by trivial) tenv (exprEnv tenv) hActive (by intro x; rfl)
      have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.block b) .block rfl
        (by trivial) tenv penv).mpr hAccess
      have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.block b) .block rfl
          (by trivial) W.P observation r)
      have hChildFuture : child.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active => simp [child, EvaluationContext.child,
            EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 0 (.block b) .block rfl (by trivial)
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hChildInputFormula : child.inputFuture = b.variables ++ child.outputFuture := by
        cases ec <;> rfl
      have hChildInput : child.inputFuture = ec.inputFuture := by
        rw [hChildInputFormula, hChildFuture]
        cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
          NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
          Block.variables, Expr.variables, DemandNode.visibleAfter, List.append_assoc]
      have hFrameChild : Frame m W tenv penv env s child.inputFuture := by
        simpa [hChildInput] using hF
      refine (ih.blockValue (path ++ [0]) b child observation W tenv penv env s
        _ _ _ _ _ _ _ hChildActive hChildAccess
      (by simpa [hChildShrink] using hProtected) (by simpa [hChildShrink] using hObserved)
      hClass hp hFrameChild ht hrb hE).mono ?_
      intro v s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hv, hg⟩
      have hFrameExprOut : Frame m W tenv penv env s1 ec.outputFuture := by
        simpa [hChildFuture] using hF1
      have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
        simpa [hChildShrink] using hObserved1
      have hRetained := hRetains1.subset (fun alias hmem =>
        ec.child_retained_subset rfl 0 (.block b) .block rfl (by trivial) hmem)
      exact ⟨hFrameExprOut, hX1, hRoots1, hValues1, hObservedPost, hRetained, hPilot1, hv, hg.1⟩
    | structLit t es =>
      simp only [tyExpr] at ht; inv at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨d, t1, hdef, hlen, t2, hes, rfl, rfl⟩ := ht
      obtain ⟨r1, hres, rfl, rfl⟩ := hr
      obtain ⟨sid, ts, rfl, hflat, hc, hd, rfl⟩ := structDef_ok _ _ _ _ _ hdef
      have htypes : ts.toList = d.fields.toList.map (·.ty) := by
        simp only [Module.structType?, hd, Option.map_some, Option.some.injEq, Ty.structT.injEq] at hc
        obtain ⟨_, rfl⟩ := hc
        exact tyList_toList_ofList _
      simp only [evalExpr]
      rw [← htypes] at hes
      have hListFrame : Frame m W tenv penv env s (es.flatMap Expr.variables ++ ec.outputFuture) := by
        cases ec with
        | pilot profile active => simpa [EvaluationContext.inputFuture,
            EvaluationContext.outputFuture, DemandNode.variables, Expr.variables,
            DemandNode.visibleAfter] using hF
        | shrink profile context => simpa [EvaluationContext.inputFuture,
            EvaluationContext.outputFuture, NodeContext.inputFuture, NodeContext.outputFuture,
            DemandNode.variables, Expr.variables] using hF
      refine Sat.bind (struct_exprs_spec ih.expr hp path (.structT sid ts) es ec observation
        0 ts es (by simpa [Ty.flat] using hflat) rfl s _ _ _ _ hActive hAccess hProtected
        hObserved hClass hListFrame hes hres hE) ?_
      rintro vs s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hfields⟩
      simp only [sat_pure]
      exact ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1,
      ⟨rfl, by simpa using hfields.1⟩, fun r h => h.elim⟩
    | arrLit t es =>
      simp only [tyExpr] at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨r1, hres, rfl, rfl⟩ := hr
      simp only [evalExpr]
      cases t <;> inv at ht
      · rename_i el k
        obtain ⟨hcanon, hfl, hlen, t1, hes, rfl, rfl⟩ := ht
        have hListFrame : Frame m W tenv penv env s (es.flatMap Expr.variables ++ ec.outputFuture) := by
          cases ec with
          | pilot profile active => simpa [EvaluationContext.inputFuture,
              EvaluationContext.outputFuture, DemandNode.variables, Expr.variables,
              DemandNode.visibleAfter] using hF
          | shrink profile context => simpa [EvaluationContext.inputFuture,
              EvaluationContext.outputFuture, NodeContext.inputFuture, NodeContext.outputFuture,
              DemandNode.variables, Expr.variables] using hF
        refine Sat.bind (exprs_spec ih.expr hp path (.arr el k) el es ec observation hfl
          0 es rfl s _ _ _ _ hActive hAccess hProtected hObserved hClass hListFrame hes hres hE) ?_
        rintro vs s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hl, hall⟩
        simp only [expectArrayLit, sat_pure]
        refine ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1,
          ⟨by simp [hl, hlen], ?_⟩, fun r hr' => hr'.elim⟩
        intro i e he
        exact hall.1 e (by simpa using List.mem_of_getElem? (by simpa using he))
      · rename_i el
        obtain ⟨hcanon, hfl, t1, hes, rfl, rfl⟩ := ht
        have hListFrame : Frame m W tenv penv env s (es.flatMap Expr.variables ++ ec.outputFuture) := by
          cases ec with
          | pilot profile active => simpa [EvaluationContext.inputFuture,
              EvaluationContext.outputFuture, DemandNode.variables, Expr.variables,
              DemandNode.visibleAfter] using hF
          | shrink profile context => simpa [EvaluationContext.inputFuture,
              EvaluationContext.outputFuture, NodeContext.inputFuture, NodeContext.outputFuture,
              DemandNode.variables, Expr.variables] using hF
        refine Sat.bind (exprs_spec ih.expr hp path (.grow el) el es ec observation hfl
          0 es rfl s _ _ _ _ hActive hAccess hProtected hObserved hClass hListFrame hes hres hE) ?_
        rintro vs s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hl, hall⟩
        simp only [expectArrayLit, sat_pure]
        refine ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1,
          ⟨rfl, ?_⟩, fun r hr' => hr'.elim⟩
        intro i e he
        exact hall.1 e (by simpa using List.mem_of_getElem? (by simpa using he))
      · rename_i el
        obtain ⟨hcanon, hfl, t1, hes, rfl, rfl⟩ := ht
        have hListFrame : Frame m W tenv penv env s (es.flatMap Expr.variables ++ ec.outputFuture) := by
          cases ec with
          | pilot profile active => simpa [EvaluationContext.inputFuture,
              EvaluationContext.outputFuture, DemandNode.variables, Expr.variables,
              DemandNode.visibleAfter] using hF
          | shrink profile context => simpa [EvaluationContext.inputFuture,
              EvaluationContext.outputFuture, NodeContext.inputFuture, NodeContext.outputFuture,
              DemandNode.variables, Expr.variables] using hF
        refine Sat.bind (exprs_spec ih.expr hp path (.growshrink el) el es ec observation hfl
          0 es rfl s _ _ _ _ hActive hAccess hProtected hObserved hClass hListFrame hes hres hE) ?_
        rintro vs s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hl, hall⟩
        simp only [expectArrayLit, sat_pure]
        refine ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1,
          ?_, fun r hr' => hr'.elim⟩
        change FlatTy (.growshrink el) (.resizable el vs.toArray)
        simp only [FlatTy]
        exact ⟨trivial, fun i e he => hall.1 e (by simpa using List.mem_of_getElem? (by simpa using he))⟩
      · rename_i el capacity
        obtain ⟨hcanon, hflatCap, t1, hes, rfl, rfl⟩ := ht
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hflatCap
        have hflat : el.flat = true := hflatCap.1
        have hcapacity : es.length ≤ capacity := hflatCap.2
        have hListFrame : Frame m W tenv penv env s (es.flatMap Expr.variables ++ ec.outputFuture) := by
          cases ec with
          | pilot profile active => simpa [EvaluationContext.inputFuture,
              EvaluationContext.outputFuture, DemandNode.variables, Expr.variables,
              DemandNode.visibleAfter] using hF
          | shrink profile context => simpa [EvaluationContext.inputFuture,
              EvaluationContext.outputFuture, NodeContext.inputFuture, NodeContext.outputFuture,
              DemandNode.variables, Expr.variables] using hF
        refine Sat.bind (exprs_spec ih.expr hp path (.limited el capacity) el es ec observation hflat
          0 es rfl s _ _ _ _ hActive hAccess hProtected hObserved hClass hListFrame hes hres hE) ?_
        rintro vs s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hl, hall⟩
        have hsize : vs.length = es.length := hl
        have hcapacity' : vs.toArray.size ≤ capacity := by simpa [hsize] using hcapacity
        simp only [expectArrayLit, if_pos hcapacity', sat_pure]
        refine ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1,
          ?_, fun r hr' => hr'.elim⟩
        change FlatTy (.limited el capacity) (.limited el capacity vs.toArray vs.toArray.size)
        simp only [FlatTy]
        refine ⟨trivial, trivial, ?_, ?_, ?_⟩
        · exact hcapacity'
        · exact Nat.le_refl _
        · intro i e he
          exact hall.1 e (by simpa using List.mem_of_getElem? (by simpa using he))
    | fill t a =>
      simp only [tyExpr] at ht
      simp only [rpExpr] at hr; inv at hr
      obtain ⟨ra, r1, hra, rfl, rfl⟩ := hr
      simp only [evalExpr]
      cases t <;> inv at ht
      rename_i el k
      obtain ⟨hcanon, hfl, ta, t1, hta, heq, rfl, rfl⟩ := ht
      have : ta = el := by simpa using heq
      subst this
      simp only [expectFixedCount, sat_pure_bind]
      let child := ec.child rfl 0 (.expression a) .expression rfl (by trivial)
      have hChildActive := ec.child_activeMatches rfl 0 (.expression a) .expression rfl
        (by trivial) tenv tenv hActive (by intro x; rfl)
      have hChildAccess := (ec.child_accessMatches_iff rfl 0 (.expression a) .expression rfl
        (by trivial) tenv penv).mpr hAccess
      have hChildShrink : child.mayShrink W.P observation = ec.mayShrink W.P observation := by
        funext r
        exact propext (ec.child_mayShrink_iff rfl 0 (.expression a) .expression rfl
          (by trivial) W.P observation r)
      have hChildFuture : child.outputFuture = ec.outputFuture := by
        cases ec with
        | pilot profile active => simp [child, EvaluationContext.child,
            EvaluationContext.outputFuture, DemandNode.visibleAfter, DemandNode.visibleForChild]
        | shrink profile context =>
          let transition := context.child rfl 0 (.expression a) .expression rfl (by trivial)
          change transition.context.expected.frame.future = context.expected.frame.future
          rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq]
          exact DemandNode.childFrame_future transition.childFrameEq rfl
      have hChildInputFormula : child.inputFuture = a.variables ++ child.outputFuture := by
        cases ec <;> rfl
      have hChildInput : child.inputFuture = ec.inputFuture := by
        rw [hChildInputFormula, hChildFuture]
        cases ec <;> simp [EvaluationContext.inputFuture, EvaluationContext.outputFuture,
          NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables,
          Expr.variables, DemandNode.visibleAfter]
      refine Sat.bind (ih.expr (path ++ [0]) a child observation W tenv penv env s
        _ _ _ _ _ _ hChildActive hChildAccess (by simpa [hChildShrink] using hProtected)
        (by simpa [hChildShrink] using hObserved) hClass hp (by simpa [hChildInput] using hF) hta hra hE) ?_
      rintro v s1 ⟨hF1, hX1, hRoots1, hValues1, hObserved1, hRetains1, hPilot1, hv, _⟩
      simp only [sat_pure]
      have hFrame1 : Frame m W tenv penv env s1 ec.outputFuture := by
        simpa [hChildFuture] using hF1
      have hObservedPost : ObservedSafe m W (ec.mayShrink W.P observation) observation s1.store := by
        simpa [hChildShrink] using hObserved1
      have hRetained := hRetains1.subset (fun alias hmem =>
        ec.child_retained_subset rfl 0 (.expression a) .expression rfl (by trivial) hmem)
      refine ⟨hFrame1, hX1, hRoots1, hValues1, hObservedPost, hRetained, hPilot1,
        ⟨by simp, ?_⟩, fun r hr' => hr'.elim⟩
      intro i e he
      have : e = v := by
        rw [Array.getElem?_replicate] at he
        split at he <;> simp_all
      subst this
      exact hv.flat hfl
    | _ => exact hsel.elim
  · intro v s' h
    rcases h with ⟨hFrame', hFoot', hRoots', hValues', hObserved', hRetained', hPilot', hTyped', hGam'⟩
    exact ⟨hFrame', hFoot', hRoots', hValues', hObserved', hRetained', hPilot', hTyped',
      hGam', classified_after hF hClass hFoot'⟩


end Goose.Core.Sound
