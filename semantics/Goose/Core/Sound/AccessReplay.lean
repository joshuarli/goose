import Goose.Core.Sound.Spec

/-!
Relate roots returned by the effectful root replay to the context-free access
queries used by demand analysis. Root lists are compared by membership because
the replay removes duplicates when it joins branches and callee results.
-/

namespace Goose.Core.Sound
open Goose.Core

def RootsIncluded (actual expected : List RootRef) : Prop :=
  ∀ root, root ∈ actual → root ∈ expected

def RootListsIncluded (actual expected : List (List RootRef)) : Prop :=
  ∀ (index : Nat) roots, actual[index]? = some roots →
    ∃ expectedRoots, expected[index]? = some expectedRoots ∧ RootsIncluded roots expectedRoots

/-- A successful place alias records its checked place type and static roots. -/
theorem AccessEnv.aliasPlace_singleton (env : AccessEnv) (path : List Nat) (p : Place)
    (alias : RetainedAlias)
    (halias : env.aliasPlace path p = .ok [alias]) :
    ∃ t roots, env.placeType? p = some t ∧ env.placeRoots p = .ok roots ∧
      alias = ⟨.ref .mutable t, roots, .operand path⟩ := by
  cases htype : env.placeType? p with
  | none => simp [AccessEnv.aliasPlace, htype, reject] at halias
  | some t =>
    cases hcond : ((Ty.ref .mutable t).interiorTarget?.isSome || t.ownerElem?.isSome) with
    | false =>
      simp [AccessEnv.aliasPlace, htype, hcond] at halias
      have hbad : ([] : List RetainedAlias) = [alias] := by
        change (Except.ok ([] : List RetainedAlias)) = Except.ok [alias] at halias
        exact Except.ok.inj halias
      cases hbad
    | true =>
      simp only [AccessEnv.aliasPlace, htype, hcond] at halias
      rcases (ex_bind_ok _ _ _).1 halias with ⟨roots, hroots, hpure⟩
      have hrecord : alias = (⟨.ref .mutable t, roots, .operand path⟩ : RetainedAlias) :=
        (List.cons.inj ((ex_pure_ok _ _).1 hpure)).1
      exact ⟨t, roots, rfl, hroots, hrecord⟩

/-- A successful view alias records its sampled element type and static roots. -/
theorem AccessEnv.aliasView_singleton (env : AccessEnv) (path : List Nat) (vw : View)
    (alias : RetainedAlias)
    (halias : env.aliasView path vw = .ok [alias]) :
    ∃ el roots, env.viewElement? vw = some el ∧ env.viewRoots vw = .ok roots ∧
      alias = ⟨.slice .readOnly el, roots, .operand path⟩ := by
  cases htype : env.viewElement? vw with
  | none => simp [AccessEnv.aliasView, htype, reject] at halias
  | some el =>
    simp only [AccessEnv.aliasView, htype] at halias
    rcases (ex_bind_ok _ _ _).1 halias with ⟨roots, hroots, hpure⟩
    have hrecord : alias = (⟨.slice .readOnly el, roots, .operand path⟩ : RetainedAlias) :=
      (List.cons.inj ((ex_pure_ok _ _).1 hpure)).1
    exact ⟨el, roots, rfl, hroots, hrecord⟩

private theorem readRoots_accessRoots (penv : PEnv) (p : Place) (state : RState)
    (rho : List RootRef) (state' : RState) (roots : List RootRef)
    (hreplay : readRoots penv p state = .ok (rho, state'))
    (haccess : penv.access.exprRoots (.read p) = .ok roots) :
    RootsIncluded rho roots := by
  cases p with
  | var x =>
    have hread := readRoots_ok penv (.var x) state (rho, state') hreplay
    rcases hread.2 with h | h | h
    · rcases h with ⟨x', lv, hp, hvar, hlike, hann⟩
      cases hp
      have hann' : (penv.ctx.varRoots.find? (·.1 == x)).map (·.2) = some rho := by
        simpa [PEnv.ann] using hann
      simp only [AccessEnv.exprRoots.eq_1, PEnv.access] at haccess
      simp only [hvar, Option.map_some, hlike, if_pos,
        AccessEnv.variableRoots, hann'] at haccess
      have hroots : rho = roots := by cases haccess; rfl
      intro root hroot
      simpa [hroots] using hroot
    · rcases h with ⟨_, hp, _, _⟩
      cases hp
    · rcases h with ⟨hnil, _, _⟩
      subst rho
      simp [RootsIncluded]
  | deref e =>
    cases e with
    | read p =>
      cases p with
      | var x =>
        have hread := readRoots_ok penv (.deref (.read (.var x))) state (rho, state') hreplay
        rcases hread.2 with h | h | h
        · rcases h with ⟨_, _, hp, _, _, _⟩
          cases hp
        · rcases h with ⟨x', hp, hslice, hcont⟩
          cases hp
          have hvarFacts : ∃ lv, penv.impl.vars[x]? = some lv ∧ lv.ty.isRefSlice = true := by
            clear haccess
            change (match penv.impl.vars[x]? with
              | some lv => lv.ty.isRefSlice
              | none => false) = true at hslice
            cases hv : penv.impl.vars[x]? with
            | none => simp [hv] at hslice
            | some lv =>
              rw [hv] at hslice
              exact ⟨lv, rfl, hslice⟩
          rcases hvarFacts with ⟨lv, hvar, hlike⟩
          have hcont' : (penv.ctx.contentRoots.find? (·.1 == x)).map (·.2) = some rho := by
            simpa [PEnv.cont] using hcont
          simp only [AccessEnv.exprRoots.eq_2, PEnv.access] at haccess
          simp only [hvar, Option.map_some, hlike, if_pos,
            AccessEnv.contentRoots, hcont'] at haccess
          have hroots : rho = roots := by cases haccess; rfl
          intro root hroot
          simpa [hroots] using hroot
        · rcases h with ⟨hnil, _, _⟩
          subst rho
          simp [RootsIncluded]
      | _ =>
        simp [readRoots] at hreplay
        have hpair : (rho, state') = ([], state) :=
          (st_pure_ok ([] : List RootRef) state (rho, state')).1 hreplay
        rcases hpair with ⟨rfl, rfl⟩
        simp [RootsIncluded]
    | _ =>
      simp [readRoots] at hreplay
      have hpair : (rho, state') = ([], state) :=
        (st_pure_ok ([] : List RootRef) state (rho, state')).1 hreplay
      rcases hpair with ⟨rfl, rfl⟩
      simp [RootsIncluded]
  | global g =>
    simp [readRoots] at hreplay
    have hpair : (rho, state') = ([], state) :=
      (st_pure_ok ([] : List RootRef) state (rho, state')).1 hreplay
    rcases hpair with ⟨rfl, rfl⟩
    simp [RootsIncluded]
  | elem view index org =>
    simp [readRoots] at hreplay
    have hpair : (rho, state') = ([], state) :=
      (st_pure_ok ([] : List RootRef) state (rho, state')).1 hreplay
    rcases hpair with ⟨rfl, rfl⟩
    simp [RootsIncluded]
  | field owner index =>
    simp [readRoots] at hreplay
    have hpair : (rho, state') = ([], state) :=
      (st_pure_ok ([] : List RootRef) state (rho, state')).1 hreplay
    rcases hpair with ⟨rfl, rfl⟩
    simp [RootsIncluded]

private theorem bind_pure_output {α β : Type} (x : P α) (value : β)
    (state : RState) (out : β) (state' : RState)
    (h : (do let _ ← x; pure value : P β) state = .ok (out, state')) : out = value := by
  rcases (st_bind_ok _ _ _ _).1 h with ⟨_, state1, _, hpure⟩
  exact congrArg Prod.fst ((st_pure_ok value state1 (out, state')).1 hpure)

private theorem bind2_pure_output {α β γ : Type} (x : P α) (y : P β) (value : γ)
    (state : RState) (out : γ) (state' : RState)
    (h : (do let _ ← x; let _ ← y; pure value : P γ) state = .ok (out, state')) : out = value := by
  rcases (st_bind_ok _ _ _ _).1 h with ⟨_, state1, _, hrest⟩
  exact bind_pure_output y value state1 out state' hrest

private theorem bind3_pure_output {α β γ δ : Type}
    (x : P α) (y : P β) (z : P γ) (value : δ)
    (state : RState) (out : δ) (state' : RState)
    (h : (do let _ ← x; let _ ← y; let _ ← z; pure value : P δ) state = .ok (out, state')) :
    out = value := by
  rcases (st_bind_ok _ _ _ _).1 h with ⟨_, state1, _, hrest⟩
  exact bind2_pure_output y z value state1 out state' hrest

private theorem RootsIncluded.union {a b c d : List RootRef}
    (ha : RootsIncluded a c) (hb : RootsIncluded b d) :
    RootsIncluded (unionRoots a b) (c ++ d) := by
  intro root hroot
  rcases unionRoots_mem _ _ root hroot with hroot | hroot
  · exact List.mem_append_left _ (ha root hroot)
  · exact List.mem_append_right _ (hb root hroot)

private theorem rpPushTail_output (penv : PEnv) (owner : Place) (arg : Expr)
    (ownerRoots : List RootRef) (state : RState) (out : List RootRef) (state' : RState)
    (h : (do
      let _ ← rpExpr penv arg
      addGrows ownerRoots
      if penv.mod.profile == .shrink then
        addWrites ownerRoots
        if (← liftV (penv.limitedOwner owner)) then noteAborts
      pure ownerRoots : P (List RootRef)) state = .ok (out, state')) :
    out = ownerRoots := by
  cases hprofile : penv.mod.profile with
  | pilot =>
    have h' : (do let _ ← rpExpr penv arg; addGrows ownerRoots; pure ownerRoots : P (List RootRef))
        state = .ok (out, state') := by
      simpa [hprofile] using h
    exact bind2_pure_output (rpExpr penv arg) (addGrows ownerRoots) ownerRoots state out state' h'
  | shrink =>
    simp only [hprofile] at h
    rcases (st_bind_ok _ _ _ _).1 h with ⟨_, state1, _, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, state2, _, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, state3, _, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨limited, state4, _, hrest⟩
    cases limited with
    | false =>
      exact congrArg Prod.fst ((st_pure_ok ownerRoots state4 (out, state')).1 hrest)
    | true =>
      exact bind_pure_output noteAborts ownerRoots state4 out state' hrest

private theorem RootsIncluded.left_eq {actual expected replacement : List RootRef}
    (h : RootsIncluded actual expected) (heq : replacement = actual) :
    RootsIncluded replacement expected := by
  intro root hroot
  rw [heq] at hroot
  exact h root hroot

private theorem RootsIncluded.right_eq {actual expected replacement : List RootRef}
    (h : RootsIncluded actual expected) (heq : expected = replacement) :
    RootsIncluded actual replacement := by
  rw [← heq]
  exact h

private def callTargetRoots (args : List (List RootRef)) : RootRef → Option (List RootRef)
  | .global g => some [.global g]
  | .param i => args[i]?
  | .local _ => none

private def accessResultStep (args : List (List RootRef)) (target : RootRef)
    (acc : List RootRef) : V (ForInStep (List RootRef)) :=
  match target with
  | .global g => pure (.yield (acc ++ [.global g]))
  | .param i =>
    match args[i]? with
    | some rs => pure (.yield (acc ++ rs))
    | _ => do
      reject .result "call result names a missing argument"
      pure (.yield acc)
  | .local _ => do
    reject .result "call result names a local root"
    pure (.yield acc)

private theorem accessResultStep_ok (args : List (List RootRef)) (target : RootRef)
    (acc : List RootRef) (out : ForInStep (List RootRef))
    (h : accessResultStep args target acc = .ok out) :
    ∃ added, callTargetRoots args target = some added ∧ out = .yield (acc ++ added) := by
  cases target with
  | global g =>
    have hout : out = .yield (acc ++ [.global g]) :=
      (ex_pure_ok _ _).1 (by simpa [accessResultStep] using h)
    exact ⟨[.global g], rfl, hout⟩
  | param i =>
    cases hi : args[i]? with
    | none => simp [accessResultStep, hi, reject, Functor.map, Except.map] at h
    | some rs =>
      have hout : out = .yield (acc ++ rs) :=
        (ex_pure_ok _ _).1 (by simpa [accessResultStep, hi] using h)
      exact ⟨rs, hi, hout⟩
  | «local» x => simp [accessResultStep, reject, Functor.map, Except.map] at h

private theorem accessResultLoop_preserves (args : List (List RootRef)) :
    ∀ (targets : List RootRef) (acc out : List RootRef),
      forIn targets acc (accessResultStep args) = .ok out →
      ∀ root, root ∈ acc → root ∈ out := by
  intro targets
  induction targets with
  | nil =>
    intro acc out h root hroot
    simp only [List.forIn_nil, ex_pure_ok] at h
    subst out
    exact hroot
  | cons target rest ih =>
    intro acc out h root hroot
    simp only [List.forIn_cons] at h
    rcases (ex_bind_ok _ _ _).1 h with ⟨step, hstep, hcont⟩
    rcases accessResultStep_ok args target acc step hstep with ⟨added, _, hstep⟩
    rw [hstep] at hcont
    have htail : forIn rest (acc ++ added) (accessResultStep args) = .ok out := by
      simpa using hcont
    exact ih (acc ++ added) out htail root (List.mem_append_left _ hroot)

private theorem accessResultLoop_target (args : List (List RootRef)) :
    ∀ (targets : List RootRef) (acc out : List RootRef),
      forIn targets acc (accessResultStep args) = .ok out →
      ∀ target, target ∈ targets → ∀ added,
        callTargetRoots args target = some added → ∀ root, root ∈ added → root ∈ out := by
  intro targets
  induction targets with
  | nil =>
    intro acc out h target htarget added hmap root hroot
    simp at htarget
  | cons target0 rest ih =>
    intro acc out h target htarget added hmap root hroot
    simp only [List.forIn_cons] at h
    rcases (ex_bind_ok _ _ _).1 h with ⟨step, hstep, hcont⟩
    rcases accessResultStep_ok args target0 acc step hstep with ⟨headRoots, hheadRoots, hstep⟩
    rw [hstep] at hcont
    have htail : forIn rest (acc ++ headRoots) (accessResultStep args) = .ok out := by
      simpa using hcont
    rcases List.mem_cons.mp htarget with heq | hmem
    · subst target
      have hroots : headRoots = added := by
        have heq : some headRoots = some added := hheadRoots.symm.trans hmap
        injection heq
      subst headRoots
      exact accessResultLoop_preserves args rest (acc ++ added) out htail root
        (List.mem_append_right _ hroot)
    · exact ih (acc ++ headRoots) out htail target hmem added hmap root hroot

private theorem FromRoot.weakenArgs {actual expected : List (List RootRef)}
    (hincluded : RootListsIncluded actual expected) {root target : RootRef}
    (hfrom : FromRoot actual root target) : FromRoot expected root target := by
  cases target with
  | global g =>
    simpa [FromRoot] using hfrom
  | param i =>
    rcases hfrom with ⟨actualRoots, hactual, hroot⟩
    rcases hincluded i actualRoots hactual with ⟨expectedRoots, hexpected, hsubset⟩
    exact ⟨expectedRoots, hexpected, hsubset root hroot⟩
  | «local» x => exact hfrom.elim

private theorem FromRoot.callTargetRoots {args : List (List RootRef)} {root target : RootRef}
    (hfrom : FromRoot args root target) :
    ∃ added, callTargetRoots args target = some added ∧ root ∈ added := by
  cases target with
  | global g =>
    rcases hfrom with rfl
    exact ⟨[.global g], rfl, by simp⟩
  | param i =>
    rcases hfrom with ⟨added, hadded, hroot⟩
    exact ⟨added, hadded, hroot⟩
  | «local» x => exact hfrom.elim

private theorem callResultRoots_subset_access (callee : Impl) (cctx : Context)
    (actualArgs staticArgs : List (List RootRef)) (actualRoots staticRoots : List RootRef)
    (hargs : RootListsIncluded actualArgs staticArgs)
    (hresult : callResultRoots callee cctx actualArgs = .ok actualRoots)
    (hloop : forIn cctx.resultRoots.flatten [] (accessResultStep staticArgs) = .ok staticRoots) :
    RootsIncluded actualRoots staticRoots := by
  cases hresults : callee.results.toList with
  | nil =>
    have hactual : actualRoots = [] := by
      have hpure : (pure ([] : List RootRef) : V (List RootRef)) = .ok actualRoots := by
        simpa [callResultRoots, hresults] using hresult
      exact (ex_pure_ok _ _).1 hpure
    intro root hroot
    simp [hactual] at hroot
  | cons t rest =>
    cases rest with
    | cons next more =>
      have hactual : actualRoots = [] := by
        have hpure : (pure ([] : List RootRef) : V (List RootRef)) = .ok actualRoots := by
          simpa [callResultRoots, hresults] using hresult
        exact (ex_pure_ok _ _).1 hpure
      intro root hroot
      simp [hactual] at hroot
    | nil =>
      cases hctxRoots : cctx.resultRoots with
      | nil =>
        have hactual : actualRoots = [] := by
          have hpure : (pure ([] : List RootRef) : V (List RootRef)) = .ok actualRoots := by
            simpa [callResultRoots, hresults, hctxRoots] using hresult
          exact (ex_pure_ok _ _).1 hpure
        intro root hroot
        simp [hactual] at hroot
      | cons declared rest =>
        cases rest with
        | cons next more =>
          have hactual : actualRoots = [] := by
            have hpure : (pure ([] : List RootRef) : V (List RootRef)) = .ok actualRoots := by
              simpa [callResultRoots, hresults, hctxRoots] using hresult
            exact (ex_pure_ok _ _).1 hpure
          intro root hroot
          simp [hactual] at hroot
        | nil =>
          cases hRef : t.isRefLike with
          | false =>
            have hactual : actualRoots = [] := by
              have hpure : (pure ([] : List RootRef) : V (List RootRef)) = .ok actualRoots := by
                simpa [callResultRoots, hresults, hctxRoots, hRef] using hresult
              exact (ex_pure_ok _ _).1 hpure
            intro root hroot
            simp [hactual] at hroot
          | true =>
            have hmap : mapResultRoots actualArgs [] declared = .ok actualRoots := by
              simpa [callResultRoots, hresults, hctxRoots, hRef] using hresult
            intro root hroot
            rcases mapResultRoots_sub actualArgs declared [] actualRoots hmap root hroot with hnil |
              ⟨target, htarget, hfrom⟩
            · simp at hnil
            · have hfromStatic : FromRoot staticArgs root target :=
                FromRoot.weakenArgs hargs hfrom
              obtain ⟨added, hadded, hroot⟩ := FromRoot.callTargetRoots hfromStatic
              have htarget' : target ∈ cctx.resultRoots.flatten := by
                simpa [hctxRoots] using htarget
              exact accessResultLoop_target staticArgs cctx.resultRoots.flatten [] staticRoots hloop
                target htarget' added hadded root hroot

mutual

theorem rpPlace_accessRoots (penv : PEnv) (p : Place) (state : RState)
    (rho : List RootRef) (state' : RState) (roots : List RootRef)
    (hreplay : rpPlace penv p state = .ok (rho, state'))
    (haccess : penv.access.placeRoots p = .ok roots) :
    RootsIncluded rho roots := by
  cases p with
  | var x =>
    simp only [rpPlace, AccessEnv.placeRoots] at hreplay haccess
    have hp : (rho, state') = ([.local x], state) :=
      (st_pure_ok _ state (rho, state')).1 hreplay
    have hrho : rho = [.local x] := congrArg Prod.fst hp
    have hroots : roots = [.local x] := by cases haccess; rfl
    simp [RootsIncluded, hrho, hroots]
  | global g =>
    simp only [rpPlace, AccessEnv.placeRoots] at hreplay haccess
    have hp : (rho, state') = ([.global g], state) :=
      (st_pure_ok _ state (rho, state')).1 hreplay
    have hrho : rho = [.global g] := congrArg Prod.fst hp
    have hroots : roots = [.global g] := by cases haccess; rfl
    simp [RootsIncluded, hrho, hroots]
  | deref e =>
    change penv.access.exprRoots e = .ok roots at haccess
    exact rpExpr_accessRoots penv e state rho state' roots hreplay haccess
  | field owner index =>
    change penv.access.placeRoots owner = .ok roots at haccess
    exact rpPlace_accessRoots penv owner state rho state' roots hreplay haccess
  | elem view index org =>
    simp only [rpPlace] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨viewRoots, state1, hview, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, state2, _, hrest⟩
    have hrho : rho = viewRoots := bind_pure_output noteAborts viewRoots state2 rho state' hrest
    simp only [AccessEnv.placeRoots] at haccess
    exact (RootsIncluded.left_eq
      (rpView_accessRoots penv view state viewRoots state1 roots hview haccess) hrho)

theorem rpView_accessRoots (penv : PEnv) (view : View) (state : RState)
    (rho : List RootRef) (state' : RState) (roots : List RootRef)
    (hreplay : rpView penv view state = .ok (rho, state'))
    (haccess : penv.access.viewRoots view = .ok roots) :
    RootsIncluded rho roots := by
  cases view with
  | of p =>
    simp only [rpView] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨placeRoots, state1, hplace, hrest⟩
    have hrho : rho = placeRoots := bind_pure_output (addReads placeRoots) placeRoots state1 rho state' hrest
    simp only [AccessEnv.viewRoots] at haccess
    exact (RootsIncluded.left_eq
      (rpPlace_accessRoots penv p state placeRoots state1 roots hplace haccess) hrho)
  | val e =>
    exact rpExpr_accessRoots penv e state rho state' roots hreplay haccess

theorem rpExpr_accessRoots (penv : PEnv) (e : Expr) (state : RState)
    (rho : List RootRef) (state' : RState) (roots : List RootRef)
    (hreplay : rpExpr penv e state = .ok (rho, state'))
    (haccess : penv.access.exprRoots e = .ok roots) :
    RootsIncluded rho roots := by
  cases e with
  | lit t n =>
    simp only [rpExpr, AccessEnv.exprRoots] at hreplay haccess
    have hp : (rho, state') = ([], state) := (st_pure_ok _ state _).1 hreplay
    have hrho : rho = [] := congrArg Prod.fst hp
    have hroots : roots = [] := by cases haccess; rfl
    simp [RootsIncluded, hrho, hroots]
  | bool b =>
    simp only [rpExpr, AccessEnv.exprRoots] at hreplay haccess
    have hp : (rho, state') = ([], state) := (st_pure_ok _ state _).1 hreplay
    have hrho : rho = [] := congrArg Prod.fst hp
    have hroots : roots = [] := by cases haccess; rfl
    simp [RootsIncluded, hrho, hroots]
  | read p =>
    simp only [rpExpr] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨placeRoots, state1, hplace, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, state2, _, hread⟩
    exact readRoots_accessRoots penv p state2 rho state' roots hread haccess
  | ref mu p =>
    simp only [rpExpr] at hreplay
    change penv.access.placeRoots p = .ok roots at haccess
    exact rpPlace_accessRoots penv p state rho state' roots hreplay haccess
  | slice mu v lo hi org =>
    simp only [rpExpr] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨viewRoots, state1, hview, hrest⟩
    -- The bounds and abort marker do not change the returned owner roots.
    change penv.access.viewRoots v = .ok roots at haccess
    have hrho : rho = viewRoots := bind3_pure_output (rpBound penv lo) (rpBound penv hi)
      noteAborts viewRoots state1 rho state' hrest
    exact RootsIncluded.left_eq
      (rpView_accessRoots penv v state viewRoots state1 roots hview haccess) hrho
  | len v =>
    simp only [rpExpr, AccessEnv.exprRoots] at hreplay haccess
    have hrho : rho = [] := bind_pure_output (rpView penv v) [] state rho state' hreplay
    have hroots : roots = [] := by cases haccess; rfl
    simp [RootsIncluded, hrho, hroots]
  | un op a org =>
    simp only [AccessEnv.exprRoots] at haccess
    have hroots : roots = [] := by cases haccess; rfl
    cases op with
    | neg =>
      simp only [rpExpr] at hreplay
      have hrho : rho = [] := bind2_pure_output (rpExpr penv a) noteAborts [] state rho state' hreplay
      simp [RootsIncluded, hrho, hroots]
    | bitnot =>
      simp only [rpExpr] at hreplay
      have hrho : rho = [] := bind_pure_output (rpExpr penv a) [] state rho state' hreplay
      simp [RootsIncluded, hrho, hroots]
  | bin op a b org =>
    simp only [AccessEnv.exprRoots] at haccess
    have hroots : roots = [] := by cases haccess; rfl
    simp only [rpExpr] at hreplay
    cases hmay : op.mayAbort with
    | false =>
      simp only [hmay] at hreplay
      have hrho : rho = [] := bind2_pure_output (rpExpr penv a) (rpExpr penv b) [] state rho state' hreplay
      simp [RootsIncluded, hrho, hroots]
    | true =>
      simp only [hmay] at hreplay
      have hrho : rho = [] := by
        rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨_, state1, _, htail⟩
        exact bind2_pure_output (rpExpr penv b) noteAborts [] state1 rho state' htail
      simp [RootsIncluded, hrho, hroots]
  | cmp op a b =>
    simp only [rpExpr, AccessEnv.exprRoots] at hreplay haccess
    have hrho : rho = [] := bind2_pure_output (rpExpr penv a) (rpExpr penv b) [] state rho state' hreplay
    have hroots : roots = [] := by cases haccess; rfl
    simp [RootsIncluded, hrho, hroots]
  | and a b =>
    simp only [rpExpr, AccessEnv.exprRoots] at hreplay haccess
    have hrho : rho = [] := bind2_pure_output (rpExpr penv a) (rpExpr penv b) [] state rho state' hreplay
    have hroots : roots = [] := by cases haccess; rfl
    simp [RootsIncluded, hrho, hroots]
  | or a b =>
    simp only [rpExpr, AccessEnv.exprRoots] at hreplay haccess
    have hrho : rho = [] := bind2_pure_output (rpExpr penv a) (rpExpr penv b) [] state rho state' hreplay
    have hroots : roots = [] := by cases haccess; rfl
    simp [RootsIncluded, hrho, hroots]
  | not a =>
    simp only [rpExpr, AccessEnv.exprRoots] at hreplay haccess
    have hrho : rho = [] := bind_pure_output (rpExpr penv a) [] state rho state' hreplay
    have hroots : roots = [] := by cases haccess; rfl
    simp [RootsIncluded, hrho, hroots]
  | conv k target a org =>
    simp only [AccessEnv.exprRoots] at haccess
    have hroots : roots = [] := by cases haccess; rfl
    cases k with
    | as =>
      simp only [rpExpr] at hreplay
      have hrho : rho = [] := bind2_pure_output (rpExpr penv a) noteAborts [] state rho state' hreplay
      simp [RootsIncluded, hrho, hroots]
    | widen | asUnchecked =>
      simp only [rpExpr] at hreplay
      have hrho : rho = [] := bind_pure_output (rpExpr penv a) [] state rho state' hreplay
      simp [RootsIncluded, hrho, hroots]
  | call c args org =>
    simp only [rpExpr] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨actualArgs, state1, hargs, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, state2, _, hcall⟩
    rcases rpCall_ok penv c actualArgs state2 rho state' hcall with
      ⟨cctx, callee, hcctx, hcallee, _, _, hresult⟩
    cases hc : penv.mod.contexts[c]? with
    | none =>
      simp [PEnv.access, AccessEnv.exprRoots, hc, reject] at haccess
    | some staticCtx =>
      simp only [PEnv.access, AccessEnv.exprRoots, hc, ex_bind_ok, ex_pure_ok] at haccess
      rcases haccess with ⟨staticArgs, hstaticArgs, staticRoots, hloop, hroots⟩
      have hctxEq : staticCtx = cctx := Option.some.inj (hc.symm.trans hcctx)
      subst staticCtx
      have hargsIncluded := rpArgs_accessRoots penv args state actualArgs state1 staticArgs hargs hstaticArgs
      have hloop' : forIn cctx.resultRoots.flatten [] (accessResultStep staticArgs) = .ok staticRoots := by
        change forIn cctx.resultRoots.flatten [] (accessResultStep staticArgs) = .ok staticRoots at hloop
        exact hloop
      have hresultIncluded := callResultRoots_subset_access callee cctx actualArgs staticArgs rho staticRoots
        hargsIncluded hresult hloop'
      exact RootsIncluded.right_eq hresultIncluded hroots.symm
  | push owner a org =>
    simp only [rpExpr] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨ownerRoots, state1, howner, hrest⟩
    have hrho : rho = ownerRoots := rpPushTail_output penv owner a ownerRoots state1 rho state' hrest
    change penv.access.placeRoots owner = .ok roots at haccess
    exact RootsIncluded.left_eq
      (rpPlace_accessRoots penv owner state ownerRoots state1 roots howner haccess) hrho
  | pop owner org =>
    simp only [rpExpr] at hreplay
    simp only [AccessEnv.exprRoots] at haccess
    have hrho : rho = [] := by
      rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨ownerRoots, state1, _, hrest⟩
      exact bind3_pure_output (addReads ownerRoots) (addShrinks ownerRoots) noteAborts
        [] state1 rho state' hrest
    have hroots : roots = [] := by cases haccess; rfl
    simp [RootsIncluded, hrho, hroots]
  | ifE c thenB elseB =>
    simp only [rpExpr] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨_, state1, _, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨⟨thenRoots, thenRange⟩, state2, hthen, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨⟨elseRoots, elseRange⟩, state3, helse, hpure⟩
    have hout : rho = unionRoots thenRoots elseRoots :=
      congrArg Prod.fst ((st_pure_ok _ state3 (rho, state')).1 hpure)
    simp only [AccessEnv.exprRoots, ex_bind_ok] at haccess
    rcases haccess with ⟨thenStatic, hthenStatic, hrest⟩
    rcases hrest with ⟨elseStatic, helseStatic, hpure⟩
    have hstatic : roots = thenStatic ++ elseStatic := (ex_pure_ok _ _).1 hpure
    have hthenIncluded := rpBlockValue_accessRoots penv [] thenB state1 thenRoots thenRange state2 thenStatic hthen hthenStatic
    have helseIncluded := rpBlockValue_accessRoots penv [] elseB state2 elseRoots elseRange state3 elseStatic helse helseStatic
    rw [hstatic]
    exact RootsIncluded.left_eq (RootsIncluded.union hthenIncluded helseIncluded) hout
  | blockE b =>
    simp only [rpExpr] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨⟨blockRoots, range⟩, state1, hblock, hpure⟩
    have hout : rho = blockRoots := congrArg Prod.fst ((st_pure_ok _ state1 (rho, state')).1 hpure)
    change penv.access.blockRoots b = .ok roots at haccess
    exact RootsIncluded.left_eq
      (rpBlockValue_accessRoots penv [] b state blockRoots range state1 roots hblock haccess) hout
  | arrLit t es =>
    simp only [rpExpr, AccessEnv.exprRoots] at hreplay haccess
    have hrho : rho = [] := bind_pure_output (rpExprs penv es) [] state rho state' hreplay
    have hroots : roots = [] := by cases haccess; rfl
    simp [RootsIncluded, hrho, hroots]
  | fill t a =>
    simp only [rpExpr] at hreplay
    simp only [AccessEnv.exprRoots] at haccess
    have hrho : rho = [] := bind_pure_output (rpExpr penv a) [] state rho state' hreplay
    have hroots : roots = [] := by cases haccess; rfl
    simp [RootsIncluded, hrho, hroots]
  | structLit t es =>
    simp only [rpExpr, AccessEnv.exprRoots] at hreplay haccess
    have hrho : rho = [] := bind_pure_output (rpExprs penv es) [] state rho state' hreplay
    have hroots : roots = [] := by cases haccess; rfl
    simp [RootsIncluded, hrho, hroots]

theorem rpArgs_accessRoots (penv : PEnv) (args : List Arg) (state : RState)
    (actual : List (List RootRef)) (state' : RState) (expected : List (List RootRef))
    (hreplay : rpArgs penv args state = .ok (actual, state'))
    (haccess : penv.access.argsRoots args = .ok expected) :
    RootListsIncluded actual expected := by
  cases args with
  | nil =>
    simp only [rpArgs, AccessEnv.argsRoots] at hreplay haccess
    have ha : actual = [] := congrArg Prod.fst ((st_pure_ok _ state _).1 hreplay)
    have he : expected = [] := by cases haccess; rfl
    subst actual
    subst expected
    simp [RootListsIncluded]
  | cons arg rest =>
    cases arg with
    | byVal e =>
      simp only [rpArgs] at hreplay
      rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨head, state1, hhead, hrest⟩
      rcases (st_bind_ok _ _ _ _).1 hrest with ⟨tail, state2, htail, hpure⟩
      have hactual : actual = head :: tail := congrArg Prod.fst ((st_pure_ok _ state2 _).1 hpure)
      simp only [AccessEnv.argsRoots, AccessEnv.argRoots] at haccess
      rcases (ex_bind_ok _ _ _).1 haccess with ⟨staticHead, hstaticHead, hrest⟩
      rcases (ex_bind_ok _ _ _).1 hrest with ⟨staticTail, hstaticTail, hpure⟩
      have hexpected : expected = staticHead :: staticTail := (ex_pure_ok _ _).1 hpure
      have hheadIncluded := rpExpr_accessRoots penv e state head state1 staticHead hhead hstaticHead
      have htailIncluded := rpArgs_accessRoots penv rest state1 tail state2 staticTail htail hstaticTail
      intro index roots hindex
      cases index with
      | zero =>
        simp [hactual] at hindex
        have hr : roots = head := hindex.symm
        subst roots
        refine ⟨staticHead, ?_, hheadIncluded⟩
        simp [hexpected]
      | succ index =>
        simp [hactual] at hindex
        rcases htailIncluded index roots hindex with ⟨tailRoots, htailRoots, hincluded⟩
        refine ⟨tailRoots, ?_, hincluded⟩
        simpa [hexpected] using htailRoots
    | byRef mu p =>
      simp only [rpArgs] at hreplay
      rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨head, state1, hhead, hrest⟩
      rcases (st_bind_ok _ _ _ _).1 hrest with ⟨tail, state2, htail, hpure⟩
      have hactual : actual = head :: tail := congrArg Prod.fst ((st_pure_ok _ state2 _).1 hpure)
      simp only [AccessEnv.argsRoots, AccessEnv.argRoots] at haccess
      rcases (ex_bind_ok _ _ _).1 haccess with ⟨staticHead, hstaticHead, hrest⟩
      rcases (ex_bind_ok _ _ _).1 hrest with ⟨staticTail, hstaticTail, hpure⟩
      have hexpected : expected = staticHead :: staticTail := (ex_pure_ok _ _).1 hpure
      have hheadIncluded := rpPlace_accessRoots penv p state head state1 staticHead hhead hstaticHead
      have htailIncluded := rpArgs_accessRoots penv rest state1 tail state2 staticTail htail hstaticTail
      intro index roots hindex
      cases index with
      | zero =>
        simp [hactual] at hindex
        have hr : roots = head := hindex.symm
        subst roots
        refine ⟨staticHead, ?_, hheadIncluded⟩
        simp [hexpected]
      | succ index =>
        simp [hactual] at hindex
        rcases htailIncluded index roots hindex with ⟨tailRoots, htailRoots, hincluded⟩
        refine ⟨tailRoots, ?_, hincluded⟩
        simpa [hexpected] using htailRoots

theorem rpBlockValue_accessRoots (penv : PEnv) (pre : List VarId) (block : Block)
    (state : RState) (rho : List RootRef) (rng : Nat × Nat) (state' : RState)
    (roots : List RootRef)
    (hreplay : rpBlockValue penv pre block state = .ok ((rho, rng), state'))
    (haccess : penv.access.blockRoots block = .ok roots) :
    RootsIncluded rho roots := by
  cases block with
  | mk scope stmts value =>
    cases value with
    | none =>
      have hparts := rpBlockValue_ok penv pre scope stmts none state rho rng state' hreplay
      rcases hparts with ⟨_, state1, _, hvalue, _, _⟩
      rcases hvalue with ⟨hrho, _⟩
      change (pure ([] : List RootRef) : V (List RootRef)) = .ok roots at haccess
      have hroots : roots = [] := by cases haccess; rfl
      simp [RootsIncluded, hrho, hroots]
    | some e =>
      have hparts := rpBlockValue_ok penv pre scope stmts (some e) state rho rng state' hreplay
      rcases hparts with ⟨_, state1, _, hvalue, _, _⟩
      have hvalue : rpExpr { penv with scopes := scope :: penv.scopes } e state1 = .ok (rho, state') := by
        simpa using hvalue
      change penv.access.exprRoots e = .ok roots at haccess
      exact rpExpr_accessRoots { penv with scopes := scope :: penv.scopes } e state1 rho state' roots
        hvalue (by simpa [PEnv.access] using haccess)

end

end Goose.Core.Sound
