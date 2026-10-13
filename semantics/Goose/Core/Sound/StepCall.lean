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
      Frame m W tenv penv env s' ∧ Ext (insts env) (Dset W) s s' ∧ vals.length = args.length ∧
      ∀ (i : Nat) (v : Val), vals[i]? = some v → ∃ (p : Param) (pv : LocalVar) (ar : List RootRef)
          (a : Arg) (ty : Ty) (tn0 tn1 : Nat) (rst0 rst1 : RState),
        ps[i]? = some p ∧ callee.vars[p.var]? = some pv ∧
        ars[i]? = some ar ∧ HasTy m W.G s'.store v pv.ty ∧ (∀ r, Targets v r → Gam env W.P ar r) ∧
        args[i]? = some a ∧ ArgTy tenv a tn0 ty tn1 ∧ ty.passableTo pv.ty = true ∧
        ArgRp penv a rst0 ar rst1)
  | [], ps, s, tn, tn', rst, rst', ars, hF, _, _, _, _ => by
    simp only [mapList, sat_pure]
    exact ⟨hF, Ext.refl _ _ _, rfl, fun i v h => by simp at h⟩
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
          obtain ⟨_, t, b, contents, t1, htp, hallowed, hrt, ht⟩ := ht
          obtain ⟨rho, r1, hre, ars', r2, hra, rfl, rfl⟩ := hr
          have h2 : (Ty.ref mu t).passableTo pv.ty = true ∧
              tyArgs tenv callee ps as t1 = .ok ((), tn') := by
            rcases ht with ⟨_, _, h1, h2⟩ | ⟨_, h1, h2⟩ <;> exact ⟨h1, h2⟩
          have hrt' : t.refTarget = true ∨ (t.isSlice = true ∧ b = true ∧ p'.sliceArg = true) := by
            simpa [Bool.or_eq_true, Bool.and_eq_true, and_assoc] using hrt
          exact ⟨.ref mu t, t1, rho, r1, ars', ⟨t, (b, contents), htp, hrt', rfl⟩, h2.1, h2.2, hre, hra, rfl⟩
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
        exact ⟨p, pv, rho, a, ty, _, _, _, _, rfl, hv, rfl, hasTy_passable (hv1.mono hX2.le) hpass,
          hg1, rfl, hat, hpass, har⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        obtain ⟨p', pv', ar, a', ty', n0, n1, q0, q1, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hall i v' hi
        exact ⟨p', pv', ar, a', ty', n0, n1, q0, q1, by simpa using g1, g2, by simpa using g3, g4, g5,
          by simpa using g6, g7, g8, g9⟩

/-! ### The caller's slice variables, as the callee sees them -/

variable {s : St}

/-- The slice variables a callee may be given a reference to: those the
caller itself was given, and the caller's own visible slice variables. -/
def callD (W : World) (tenv : TEnv) (env : Env) : RootInst → Ty → Prop := fun r E =>
  W.D r E ∨ ∃ x lv si mu, env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
    r = RootInst.local env.act si x ∧ lv.ty = .slice mu E ∧ x ∈ tenv.visible

/-- What a slice stored in such a variable may point into: for a variable of
the caller, what its annotation denotes and outlives it. -/
def callA (W : World) (penv : PEnv) (env : Env) : RootInst → RootInst → Prop := fun r t =>
  (Dset W r ∧ W.A r t) ∨ ∃ x lv si ann, env.vars[x]? = some lv ∧
    env.scopes.lookup lv.scope = some si ∧ r = RootInst.local env.act si x ∧
    penv.ann x = some ann ∧ Gam env W.P ann t ∧ Older t r

theorem Frame.not_outer (hF : Frame m W tenv penv env s) {x : VarId} {sc si : Nat}
    (hl : env.scopes.lookup sc = some si) : ¬ Dset W (RootInst.local env.act si x) := by
  rintro ⟨E, hd⟩
  obtain ⟨a, si', x', e, hlt⟩ := hF.dOut _ E hd
  cases e
  exact absurd (hF.inst_lt hl).1 (Nat.not_le.2 hlt)

theorem callA_older (hF : Frame m W tenv penv env s) :
    ∀ r t, callA W penv env r t → Older t r := by
  rintro r t (⟨_, h⟩ | ⟨x, lv, si, ann, _, _, _, _, _, h⟩)
  · exact hF.aOlder r t h
  · exact h

theorem callD_out (hF : Frame m W tenv penv env s) :
    ∀ r E, callD W tenv env r E → ∃ a si x, r = RootInst.local a si x ∧ si < s.nextScope := by
  rintro r E (h | ⟨x, lv, si, mu, _, hl, rfl, _⟩)
  · obtain ⟨a, si, x, e, hlt⟩ := hF.dOut r E h
    exact ⟨a, si, x, e, Nat.lt_of_lt_of_le hlt hF.base_le⟩
  · exact ⟨_, _, _, rfl, (hF.inst_lt hl).2⟩

theorem callD_fun (hF : Frame m W tenv penv env s) :
    ∀ r E E', callD W tenv env r E → callD W tenv env r E' → E = E' := by
  rintro r E E' (h | ⟨x, lv, si, mu, hx, hl, rfl, hty, _⟩) (h' | ⟨x', lv', si', mu', hx', hl', e, hty', _⟩)
  · exact hF.dFun r E E' h h'
  · subst e; exact absurd ⟨E, h⟩ (hF.not_outer hl')
  · exact absurd ⟨E', h'⟩ (hF.not_outer hl)
  · cases e
    rw [hx] at hx'; cases hx'
    rw [hty] at hty'; cases hty'; rfl

theorem callOuterOk (hF : Frame m W tenv penv env s) :
    OuterOk m W.G (callD W tenv env) (callA W penv env) s := by
  rintro r E (h | ⟨x, lv, si, mu, hx, hl, rfl, hty, hvis⟩)
  · obtain ⟨v, h1, h2, h3⟩ := hF.sa r E h
    exact ⟨v, h1, h2, fun t ht => Or.inl ⟨⟨E, h⟩, h3 t ht⟩⟩
  · obtain ⟨lv', si', v, g1, g2, _, g4, g5⟩ := hF.vis x hvis
    rw [hx] at g1; cases g1
    rw [hl] at g2; cases g2
    refine ⟨v, g4, by rw [hty] at g5; exact hasTy_slice_mu g5, fun t ht => Or.inr ?_⟩
    obtain ⟨ann, ha, hg⟩ := hF.rooted x lv si v hx hl g4 t ht
    exact ⟨x, lv, si, ann, hx, hl, rfl, ha, hg, hF.inv.age _ v g4 t ht⟩

/-- What the callee may have done to a slice variable, read back in the caller. -/
theorem callD_back (hF : Frame m W tenv penv env s) :
    ∀ r E, callD W tenv env r E → (W.D r E ∧ ∀ t, callA W penv env r t → W.A r t) ∨
      (∃ x lv si mu, env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
        r = RootInst.local env.act si x ∧ lv.ty = .slice mu E ∧
        ∀ t, callA W penv env r t → ∃ ann, penv.ann x = some ann ∧ Gam env W.P ann t) := by
  rintro r E (h | ⟨x, lv, si, mu, hx, hl, rfl, hty, _⟩)
  · refine Or.inl ⟨h, ?_⟩
    rintro t (⟨_, g⟩ | ⟨x, lv, si, ann, _, hl, rfl, _⟩)
    · exact g
    · exact absurd ⟨E, h⟩ (hF.not_outer hl)
  · refine Or.inr ⟨x, lv, si, mu, hx, hl, rfl, hty, ?_⟩
    rintro t (⟨g, _⟩ | ⟨x', lv', si', ann, _, _, e, ha, hg, _⟩)
    · exact absurd g (hF.not_outer hl)
    · cases e
      exact ⟨ann, ha, hg⟩

theorem ext_of_call (hF : Frame m W tenv penv env s) {s2 : St}
    (h : Ext [] (fun r => ∃ E, callD W tenv env r E) s s2) : Ext (insts env) (Dset W) s s2 := by
  refine h.weaken ?_
  intro r hnd hn
  refine ⟨?_, fun _ _ _ _ h' => by cases h'⟩
  rintro ⟨E, (hd | ⟨x, lv, si, mu, _, hl, rfl, _⟩)⟩
  · exact hnd ⟨E, hd⟩
  · exact hn _ _ _ rfl (lookup_inst hl)

/-- The callee context's content roots, read through the arguments, denote in
the callee what their instantiation denotes in the caller. -/
theorem gam_inst {P : Nat → RootInst → Prop} {ars : List (List RootRef)} {cont inst : List RootRef}
    (hmap : mapResultRoots ars [] cont = .ok inst) (t : RootInst) :
    Gam env P inst t ↔ Gam noEnv (fun j r => Gam env P (ars[j]?.getD []) r) cont t := by
  constructor
  · rintro ⟨q, hq, hrq⟩
    rcases mapResultRoots_sub ars cont [] inst hmap q hq with h | ⟨r', hr', hf⟩
    · cases h
    · cases r' with
      | «local» y => exact hf.elim
      | global g =>
        have e : q = RootRef.global g := hf
        subst e
        exact ⟨.global g, hr', hrq⟩
      | param j =>
        obtain ⟨a, ha, hqa⟩ := hf
        exact ⟨.param j, hr', q, by simpa [ha] using hqa, hrq⟩
  · rintro ⟨q', hq', hrq'⟩
    have hm := (mapResultRoots_ok ars cont [] inst hmap).2 q' hq'
    cases q' with
    | «local» y => exact hm.elim
    | global g => exact ⟨.global g, hm, hrq'⟩
    | param j =>
      obtain ⟨a, ha, hsub⟩ := hm
      obtain ⟨q, hq, hrq⟩ := (hrq' : Gam env P (ars[j]?.getD []) t)
      exact ⟨q, hsub q (by simpa [ha] using hq), hrq⟩

end Goose.Core.Sound
