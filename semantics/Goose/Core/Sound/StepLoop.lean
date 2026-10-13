import Goose.Core.Sound.StepBlock

/-!
One step of the induction on fuel for the three loops.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}

/-- The value an index variable of a loop over a run is bound to. -/
def idxVal (i : Nat) (idx : Option VarId) : List (VarId × Val) :=
  match idx with
  | some j => [(j, Val.int .i64 i)]
  | none => []

theorem evalExpr_bool (k : Nat) (cfg : Cfg) (env : Env) (b : Bool) :
    evalExpr k cfg env (.bool b) = if k = 0 then timeout else pure (.bool b) := by
  cases k <;> simp [evalExpr]

/-- One iteration of a loop over a run, with the two choices it makes pulled
out of the continuation. -/
theorem execEach_eq (k : Nat) (cfg : Cfg) (env : Env) (x : VarId) (idx : Option VarId) (byRef : Bool)
    (body : Block) (vw : ViewVal) (i : Nat) :
    execEach (k + 1) cfg env x idx byRef body vw i =
      ((if vw.resizable = true then lengthLoc vw.loc else pure vw.len) >>= fun len =>
        if i < len then
          ((if byRef = true then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
            else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) >>= fun ev =>
          execBlock k cfg env ((x, ev) :: (match idx with
              | some j => [(j, Val.int .i64 i)]
              | none => [])) body >>= fun fl =>
            match fl with
            | .normal _ => execEach k cfg env x idx byRef body vw (i + 1)
            | .cont => execEach k cfg env x idx byRef body vw (i + 1)
            | .brk => pure (.normal .unit)
            | .ret v => pure (.ret v))
        else pure (.normal .unit)) := by
  conv => lhs; unfold execEach
  cases vw.resizable <;> cases byRef <;> rfl

set_option maxHeartbeats 800000 in
theorem step_while (ih : Specs m prof n) : WhileSpec m prof (n + 1) := by
  intro W tenv penv env s c body tn tn1 tn2 bty rst rst1 rst2 rhoc rb rng hp hF htc htb hrc hrb hE
  -- One pass through the body from a state the condition was true in.
  have body_part : ∀ (s1 : St), Frame m W tenv penv env s1 → Ext (insts env) (Dset W) s s1 →
      Sat (execBlock n ⟨prof, m⟩ env [] body >>= fun fl =>
        match fl with
        | .normal _ => execWhile n ⟨prof, m⟩ env c body
        | .cont => execWhile n ⟨prof, m⟩ env c body
        | .brk => pure (.normal .unit)
        | .ret v => pure (.ret v)) s1 (fun fl s' =>
        Frame m W tenv penv env s' ∧ Ext (insts env) (Dset W) s s' ∧ LoopFlow m W tenv penv s' fl ∧
        (∀ v, fl = .normal v → c = .bool true → body.hasBreak = true)) := by
    intro s1 hF1 hX1
    have hFl : Frame m W { tenv with loops := tenv.loops + 1 } penv env s1 :=
      hF1.tenv_congr rfl rfl rfl (fun _ h => h)
    refine Sat.bind (block_of_checks ih.block hp hFl body [] [] htb hrb hE rfl rfl
      (fun k x v ty' h => by simp at h)) ?_
    rintro fl s2 ⟨hF2, hX2, hfl⟩
    have hF2' : Frame m W tenv penv env s2 := hF2.tenv_congr rfl rfl rfl (fun _ h => h)
    have again := (ih.while_ W tenv penv env s2 c body tn tn1 tn2 bty rst rst1 rst2 rhoc rb rng hp
      hF2' htc htb hrc hrb hE).mono (Q := fun fl s' =>
        Frame m W tenv penv env s' ∧ Ext (insts env) (Dset W) s s' ∧ LoopFlow m W tenv penv s' fl ∧
        (∀ v, fl = .normal v → c = .bool true → body.hasBreak = true))
      (fun fl s' ⟨g1, g2, g3, g4⟩ => ⟨g1, (hX1.trans hX2).trans g2, g3, g4⟩)
    cases fl with
    | normal v => exact again
    | cont => exact again
    | brk =>
      simp only [sat_pure]
      exact ⟨hF2', hX1.trans hX2, trivial, fun _ _ _ => hfl.2⟩
    | ret v =>
      simp only [sat_pure]
      exact ⟨hF2', hX1.trans hX2, ⟨hfl.1, hfl.2.tsame rfl rfl⟩, fun v' h => by cases h⟩
  by_cases hc : c = .bool true
  · subst hc
    rw [execWhile, evalExpr_bool]
    by_cases hn : n = 0
    · rw [if_pos hn]; exact trivial
    · rw [if_neg hn]
      exact body_part s hF (Ext.refl _ _ _)
  · simp only [execWhile]
    refine Sat.bind (ih.expr W tenv penv env s c _ _ _ _ _ _ hp hF htc hrc
      ((rpBlockValue_mono hrb).2.trans hE)) ?_
    rintro vc s1 ⟨hF1, hX1, hv, _⟩
    obtain ⟨x, rfl⟩ := hasTy_bool hv
    simp only [expectBool, sat_pure_bind]
    cases x
    · simp only [Bool.false_eq_true, if_false, sat_pure]
      exact ⟨hF1, hX1, trivial, fun _ _ h => absurd h hc⟩
    · simp only [if_true]
      exact body_part s1 hF1 hX1

set_option maxHeartbeats 800000 in
theorem step_range (ih : Specs m prof n) : RangeSpec m prof (n + 1) := by
  intro W tenv penv env s x t i hi body tn1 tn2 bty rst1 rst2 rb rng hp hF hx hlt htb hrb hE hk0
  simp only [execRange]
  by_cases h : i < hi
  · simp only [h, if_true]
    have hFl : Frame m W { tenv with loops := tenv.loops + 1 } penv env s :=
      hF.tenv_congr rfl rfl rfl (fun _ h => h)
    obtain ⟨lv, hlv, hsc, hty⟩ := hx
    refine Sat.bind (block_of_reserved ih.block hp hFl body [(x, .int t i)] [x] x htb hrb hE
      rfl (by simp) ?_ (Nat.le_of_lt hlt) hk0) ?_
    · intro x' v hm
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      refine ⟨Nat.le_refl _, hlt, lv, hlv, hsc, by rw [hty]; rfl, ?_, fun r hr => hr.elim⟩
      rw [hty]
      exact hasTy_of_flat (T := .int t) (show FlatTy (.int t) (.int t i) from rfl) (Or.inl rfl)
    · rintro fl s2 ⟨hF2, hX2, hfl⟩
      have hF2' : Frame m W tenv penv env s2 := hF2.tenv_congr rfl rfl rfl (fun _ h => h)
      have again := (ih.range W tenv penv env s2 x t (i + 1) hi body tn1 tn2 bty rst1 rst2 rb rng hp
        hF2' ⟨lv, hlv, hsc, hty⟩ hlt htb hrb hE hk0).mono (Q := fun fl s' =>
          Frame m W tenv penv env s' ∧ Ext (insts env) (Dset W) s s' ∧ LoopFlow m W tenv penv s' fl)
        (fun fl s' ⟨g1, g2, g3⟩ => ⟨g1, hX2.trans g2, g3⟩)
      cases fl with
      | normal v => exact again
      | cont => exact again
      | brk =>
        simp only [sat_pure]
        exact ⟨hF2', hX2, trivial⟩
      | ret v =>
        simp only [sat_pure]
        exact ⟨hF2', hX2, hfl.1, hfl.2.tsame rfl rfl⟩
  · simp only [h, if_false, sat_pure]
    exact ⟨hF, Ext.refl _ _ _, trivial⟩

set_option maxHeartbeats 1600000 in
theorem step_each (ih : Specs m prof n) : EachSpec m prof (n + 1) := by
  intro W tenv penv env s x idx byRef body vw i el rho tn1 tn2 bty rst1 rst2 rb rng
    hp hF hvw hg hx hj hlt htb hrb hE hk0
  rw [execEach_eq]
  refine Sat.bind (R := fun len s' => s' = s ∧ SliceTy s.store vw.loc vw.start len el) ?_ ?_
  · cases hres : vw.resizable with
    | false =>
      rw [if_neg Bool.false_ne_true]
      exact ⟨rfl, hvw.2.1⟩
    | true =>
      rw [if_pos rfl]
      obtain ⟨hst, hlt'⟩ := hvw.2.2 hres
      rcases hlt' with hgrow | hgrowshrink
      · refine sat_lengthLoc hgrow (fun es hread => ⟨rfl, ?_⟩)
        rw [hst]
        exact sliceTy_of_grow hgrow hread
      · refine sat_lengthLoc_growshrink hgrowshrink (fun es hread => ⟨rfl, ?_⟩)
        rw [hst]
        exact sliceTy_of_growshrink hgrowshrink hread
  · rintro len s' ⟨rfl, hsl⟩
    by_cases h : i < len
    · simp only [h, if_true]
      have hel : LocTy s'.store ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩ el := sliceTy_elem hsl h
      have hFl : Frame m W { tenv with loops := tenv.loops + 1 } penv env s' :=
        hF.tenv_congr rfl rfl rfl (fun _ h => h)
      obtain ⟨lv, hlv, hsc, hst, hxty⟩ := hx
      have hxlt : x < rst1.nextVar := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlt
      have hnd : (x :: idx.toList).Nodup := by
        cases idx with
        | none => simp
        | some j =>
          have hjx := (hj j rfl).1
          simp only [Option.toList_some, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
            not_false_eq_true, List.nodup_nil, and_true]
          intro e
          rw [← e] at hjx
          exact absurd hjx (Nat.ne_of_lt (Nat.lt_succ_self x))
      -- The rest of an iteration, for the value the loop variable gets.
      have rest : ∀ (ev : Val) (pre' : List (VarId × Val)), pre' = idxVal i idx →
          (HasTy m W.G s'.store ev lv.ty ∧ ∀ r, Targets ev r → ∃ ann, penv.ann x = some ann ∧
              Gam env W.P ann r) →
          Sat (execBlock n ⟨prof, m⟩ env ((x, ev) :: pre') body >>= fun fl =>
            match fl with
            | .normal _ => execEach n ⟨prof, m⟩ env x idx byRef body vw (i + 1)
            | .cont => execEach n ⟨prof, m⟩ env x idx byRef body vw (i + 1)
            | .brk => pure (.normal .unit)
            | .ret v => pure (.ret v)) s' (fun fl s2 =>
            Frame m W tenv penv env s2 ∧ Ext (insts env) (Dset W) s' s2 ∧
              LoopFlow m W tenv penv s2 fl) := by
        intro ev pre' hpre' hev
        subst hpre'
        refine Sat.bind (block_of_reserved ih.block hp hFl body ((x, ev) :: idxVal i idx)
          (x :: idx.toList) x htb hrb hE (by cases idx <;> rfl) hnd ?_ (Nat.le_of_lt hxlt) hk0) ?_
        · intro x' v hm
          rcases List.mem_cons.1 hm with e | hm
          · cases e
            exact ⟨Nat.le_refl _, hxlt, lv, hlv, hsc, paramOk_of_storable hst, hev.1, hev.2⟩
          · cases idx with
            | none => simp [idxVal] at hm
            | some j =>
              simp only [idxVal, List.mem_singleton, Prod.mk.injEq] at hm
              obtain ⟨rfl, rfl⟩ := hm
              obtain ⟨hjx, lj, hlj, hljsc, hljty⟩ := hj _ rfl
              refine ⟨by rw [hjx]; exact Nat.le_succ _, by rw [hjx]; simpa using hlt, lj, hlj, hljsc,
                by rw [hljty]; rfl, ?_, fun r hr => hr.elim⟩
              rw [hljty]
              exact hasTy_of_flat (T := .int .i64) (show FlatTy (.int .i64) (.int .i64 i) from rfl)
                (Or.inl rfl)
        · rintro fl s2 ⟨hF2, hX2, hfl⟩
          have hF2' : Frame m W tenv penv env s2 := hF2.tenv_congr rfl rfl rfl (fun _ h => h)
          have again := (ih.each W tenv penv env s2 x idx byRef body vw (i + 1) el rho tn1 tn2 bty
            rst1 rst2 rb rng hp hF2' (hvw.mono hX2.le) hg ⟨lv, hlv, hsc, hst, hxty⟩ hj hlt htb hrb hE
            hk0).mono (Q := fun fl s3 =>
              Frame m W tenv penv env s3 ∧ Ext (insts env) (Dset W) s' s3 ∧
                LoopFlow m W tenv penv s3 fl)
            (fun fl s3 ⟨g1, g2, g3⟩ => ⟨g1, hX2.trans g2, g3⟩)
          cases fl with
          | normal v => exact again
          | cont => exact again
          | brk =>
            simp only [sat_pure]
            exact ⟨hF2', hX2, trivial⟩
          | ret v =>
            simp only [sat_pure]
            exact ⟨hF2', hX2, hfl.1, hfl.2.tsame rfl rfl⟩
      cases byRef with
      | true =>
        simp only [if_true, sat_pure_bind]
        rw [if_pos rfl] at hxty
        obtain ⟨⟨mx, hty⟩, hbr⟩ := hxty
        refine rest _ _ (by cases idx <;> rfl) ⟨?_, fun r hr => ?_⟩
        · rw [hty]
          exact ⟨_, rfl, Or.inl ⟨flat_refTarget hvw.1, Or.inl hel⟩⟩
        · cases hr
          obtain ⟨lv', ann, _, ha, hsub, _⟩ := bindRootsV_ok _ _ _ _ hbr
          exact ⟨ann, ha, hg.subset hsub⟩
      | false =>
        simp only [Bool.false_eq_true, if_false]
        have hty : lv.ty = el := by simpa using hxty
        refine sat_readLoc_bind hel (fun ev _ hT => ?_)
        refine rest _ _ (by cases idx <;> rfl) ⟨?_, flat_no_targets hT⟩
        rw [hty]
        exact hasTy_of_flat hT (Or.inl hvw.1)
    · simp only [h, if_false, sat_pure]
      exact ⟨hF, Ext.refl _ _ _, trivial⟩

end Goose.Core.Sound
