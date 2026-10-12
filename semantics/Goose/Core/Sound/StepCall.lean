import Goose.Core.Sound.StepBlock

/-!
One step of the induction on fuel for calls: the call expression, which
evaluates its arguments and checks the callee context's assumptions, and
entering the callee's body.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}

/-! ### Summary targets through a call -/

theorem mapCall_global (callee : Impl) (cctx : Context) (ars : List (List RootRef)) :
    ∀ (ds : List Target) (g : GlobalId), Target.global g ∈ ds →
      Target.global g ∈ mapCallTargets callee cctx ars ds
  | [], g, h => by cases h
  | .global g' :: rest, g, h => by
    simp only [mapCallTargets, List.mem_cons]
    rcases List.mem_cons.1 h with e | h
    · exact Or.inl e
    · exact Or.inr (mapCall_global callee cctx ars rest g h)
  | .param j :: rest, g, h => by
    simp only [mapCallTargets, List.mem_append]
    rcases List.mem_cons.1 h with e | h
    · cases e
    · exact Or.inr (mapCall_global callee cctx ars rest g h)

theorem mapCall_param (callee : Impl) (cctx : Context) (ars : List (List RootRef)) :
    ∀ (ds : List Target) (j : Nat), Target.param j ∈ ds → ∀ t,
      (t ∈ rootsTargets (ars[j]?.getD []) ∨ t ∈ paramGlobals callee cctx j) →
      t ∈ mapCallTargets callee cctx ars ds
  | [], j, h, _, _ => by cases h
  | .global g' :: rest, j, h, t, ht => by
    simp only [mapCallTargets, List.mem_cons]
    rcases List.mem_cons.1 h with e | h
    · cases e
    · exact Or.inr (mapCall_param callee cctx ars rest j h t ht)
  | .param j' :: rest, j, h, t, ht => by
    simp only [mapCallTargets, List.mem_append]
    rcases List.mem_cons.1 h with e | h
    · cases e
      exact Or.inl ht
    · exact Or.inr (mapCall_param callee cctx ars rest j h t ht)

/-- If every target a call charges to the caller is allowed there, every
target the callee's own check lets its summary stand for is allowed in the
callee. -/
theorem expand_ok {env : Env} {G : Nat} {P Pc : Nat → RootInst → Prop} {callee : Impl}
    {cctx : Context} {ars : List (List RootRef)}
    (hPc : ∀ j r, Pc j r → Gam env P (ars[j]?.getD []) r) (hctx : CtxOk m callee cctx)
    (ds : List Target) (hpar : ∀ j, Target.param j ∈ ds → j < callee.params.size)
    (hmap : ∀ t, t ∈ mapCallTargets callee cctx ars ds → TargetOk G P t) :
    ∀ t, t ∈ expandTargets callee cctx ds → TargetOk G Pc t := by
  intro t ht
  simp only [expandTargets, List.mem_flatMap] at ht
  obtain ⟨d, hd, ht⟩ := ht
  cases d with
  | global g =>
    simp only [List.mem_singleton] at ht
    subst ht
    exact hmap _ (mapCall_global callee cctx ars ds g hd)
  | param j =>
    have hpj : TargetOk G Pc (.param j) := by
      intro r hr g hrg
      obtain ⟨q, hq, hrq⟩ := hPc j r hr
      subst hrg
      cases q with
      | «local» y => obtain ⟨_, _, _, _, e⟩ := hrq; cases e
      | global g' =>
        have e : RootInst.global g = RootInst.global g' := hrq
        cases e
        exact hmap _ (mapCall_param callee cctx ars ds j hd _ (Or.inl (mem_rootsTargets_global hq)))
      | param k =>
        exact hmap _ (mapCall_param callee cctx ars ds j hd _ (Or.inl (mem_rootsTargets_param hq)))
          _ hrq g rfl
    cases hv : callee.vars[j]? with
    | none =>
      simp only [hv, List.mem_singleton] at ht
      subst ht; exact hpj
    | some lv =>
      cases hf : cctx.varRoots.find? (·.1 == j) with
      | none =>
        simp only [hv, hf, List.mem_singleton] at ht
        subst ht; exact hpj
      | some pr =>
        obtain ⟨x, rs⟩ := pr
        simp only [hv, hf] at ht
        by_cases hrl : lv.ty.isRefLike = true
        · simp only [hrl, if_true, rootsTargets, List.mem_filterMap] at ht
          obtain ⟨q, hq, hqt⟩ := ht
          cases q with
          | «local» y => simp [rootTarget] at hqt
          | global g =>
            simp only [rootTarget, Option.some.injEq] at hqt
            subst hqt
            have hmem : Target.global g ∈ paramGlobals callee cctx j := by
              simp only [paramGlobals, hv, hf, hrl, if_true, List.mem_filterMap]
              exact ⟨_, hq, rfl⟩
            exact hmap _ (mapCall_param callee cctx ars ds j hd _ (Or.inr hmem))
          | param k =>
            simp only [rootTarget, Option.some.injEq] at hqt
            subst hqt
            rcases hctx.paramAnn j rs (hpar j hd) (by simp [hf]) _ hq with e | ⟨g, e⟩
            · cases e; exact hpj
            · cases e
        · simp only [hrl, Bool.false_eq_true, if_false, List.mem_singleton] at ht
          subst ht; exact hpj

/-! ### Arguments -/

variable {W : World} {tenv : TEnv} {penv : PEnv} {env : Env}

theorem args_spec (ihA : ArgSpec m prof n) (hp : Perm m W) (callee : Impl) :
    ∀ (args : List Arg) (ps : List Param) (s : St) (tn tn' : Nat) (rst rst' : RState)
      (ars : List (List RootRef)),
    Frame m W tenv penv env s → ps.length = args.length →
    tyArgs tenv callee ps args tn = .ok ((), tn') → rpArgs penv args rst = .ok (ars, rst') →
    EffLe rst'.eff W.E →
    Sat (mapList (evalArg n ⟨prof, m⟩ env) args) s (fun vals s' =>
      Frame m W tenv penv env s' ∧ Ext (insts env) s s' ∧ vals.length = args.length ∧
      ∀ (i : Nat) (v : Val), vals[i]? = some v → ∃ (p : Param) (pv : LocalVar) (ar : List RootRef),
        ps[i]? = some p ∧ callee.vars[p.var]? = some pv ∧
        ars[i]? = some ar ∧ HasTy m W.G s'.store v pv.ty ∧ ∀ r, Targets v r → Gam env W.P ar r)
  | [], ps, s, tn, tn', rst, rst', ars, hF, _, _, _, _ => by
    simp only [mapList, sat_pure]
    exact ⟨hF, Ext.refl _ _, rfl, fun i v h => by simp at h⟩
  | a :: as, [], s, tn, tn', rst, rst', ars, hF, hl, _, _, _ => by simp at hl
  | a :: as, p :: ps, s, tn, tn', rst, rst', ars, hF, hl, ht, hr, hE => by
    have hl' : ps.length = as.length := by simpa using hl
    cases hv : callee.vars[p.var]? with
    | none => cases a <;> (simp only [tyArgs, hv] at ht; inv at ht)
    | some pv =>
      -- The argument's own typing and roots, and what is left for the rest.
      have key : ∃ ty t1 rho r1 ars', ArgTy tenv a tn ty t1 ∧ ty.passableTo pv.ty = true ∧
          tyArgs tenv callee ps as t1 = .ok ((), tn') ∧ ArgRp penv a rst rho r1 ∧
          rpArgs penv as r1 = .ok (ars', rst') ∧ ars = rho :: ars' := by
        cases a with
        | byVal e =>
          simp only [tyArgs, hv] at ht; inv at ht
          simp only [rpArgs] at hr; inv at hr
          obtain ⟨_, te, t1, hte, hpass, hrest⟩ := ht
          obtain ⟨rho, r1, hre, ars', r2, hra, rfl, rfl⟩ := hr
          exact ⟨te, t1, rho, r1, ars', hte, hpass, hrest, hre, hra, rfl⟩
        | byRef mu p' =>
          simp only [tyArgs, hv] at ht; inv at ht
          simp only [rpArgs] at hr; inv at hr
          obtain ⟨_, t, b, t1, htp, hrt, ht⟩ := ht
          obtain ⟨rho, r1, hre, ars', r2, hra, rfl, rfl⟩ := hr
          have h2 : (Ty.ref mu t).passableTo pv.ty = true ∧
              tyArgs tenv callee ps as t1 = .ok ((), tn') := by
            rcases ht with ⟨_, _, h1, h2⟩ | ⟨_, h1, h2⟩ <;> exact ⟨h1, h2⟩
          exact ⟨.ref mu t, t1, rho, r1, ars', ⟨t, b, htp, hrt, rfl⟩, h2.1, h2.2, hre, hra, rfl⟩
      obtain ⟨ty, t1, rho, r1, ars', hat, hpass, hrest, har, hra, rfl⟩ := key
      simp only [mapList]
      refine Sat.bind (ihA W tenv penv env s a _ _ _ _ _ _ hp hF hat har
        ((rpArgs_mono hra).2.trans hE)) ?_
      rintro v s1 ⟨hF1, hX1, hv1, hg1⟩
      refine Sat.bind (args_spec ihA hp callee as ps s1 _ _ _ _ _ hF1 hl' hrest hra hE) ?_
      rintro vs s2 ⟨hF2, hX2, hlen, hall⟩
      simp only [sat_pure]
      refine ⟨hF2, hX1.trans hX2, by simp [hlen], ?_⟩
      intro i v' hi
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact ⟨p, pv, rho, rfl, hv, rfl, hasTy_passable (hv1.mono hX2.le) hpass, hg1⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        obtain ⟨p', pv', ar, g1, g2, g3, g4, g5⟩ := hall i v' hi
        exact ⟨p', pv', ar, by simpa using g1, g2, by simpa using g3, g4, g5⟩

end Goose.Core.Sound
