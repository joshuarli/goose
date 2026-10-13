import Goose.Core.Sound.StepBlock

/-!
The steps for a statement list and for a block.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {plans : Array (Array DemandPoint)} {n : Nat}

private theorem blockStmtChild? {sc : Nat} {all : List Stmt} {value : Option Expr}
    {offset : Nat} {st : Stmt} {rest : List Stmt}
    (hdrop : st :: rest = all.drop offset) :
    DemandNode.child? (.block (.mk sc all value)) offset = some (.statement st) := by
  have hget0 : (all.drop offset)[0]? = some st := by rw [← hdrop]; rfl
  rw [List.getElem?_drop] at hget0
  simp only [Nat.add_zero] at hget0
  have hbound : offset < all.length := (List.getElem?_eq_some_iff.mp hget0).choose
  have hbound' : offset < (all.map (some ∘ DemandNode.statement)).length := by
    simpa using hbound
  change ((all.map (some ∘ DemandNode.statement) ++
    [value.map DemandNode.expression])[offset]?).join = _
  rw [List.getElem?_append_left hbound']
  rw [List.getElem?_map, hget0]
  rfl

private noncomputable def blockStmtContext {path : List Nat} {sc : Nat}
    {all : List Stmt} {value : Option Expr}
    (bc : EvaluationContext m plans path (.block (.mk sc all value)) .block)
    (offset : Nat) (st : Stmt)
    (hchild : DemandNode.child? (.block (.mk sc all value)) offset = some (.statement st)) :
    EvaluationContext m plans (path ++ [offset]) (.statement st) .statement :=
  bc.child rfl offset (.statement st) .statement hchild
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])

private theorem stmt_visibleAfter {tenv tenv' : TEnv} {sc tn tn' : Nat} {st : Stmt}
    (ht : tyStmt tenv sc st tn = .ok (tenv', tn')) :
    ∀ x, x ∈ tenv'.visible ↔ x ∈ (DemandNode.statement st).visibleAfter tenv.visible := by
  cases st with
  | resize owner size fill origin =>
    cases fill
    all_goals simp only [tyStmt] at ht
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals simp_all [DemandNode.visibleAfter]
    all_goals try (split <;> simp_all)
  | ret value origin =>
    cases value
    all_goals simp only [tyStmt] at ht
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals simp_all [DemandNode.visibleAfter]
    all_goals try (split <;> simp_all)
  | ifS condition yes no origin =>
    cases no
    all_goals simp only [tyStmt] at ht
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals simp_all [DemandNode.visibleAfter]
    all_goals try (split <;> simp_all)
  | _ =>
    skip
    all_goals simp only [tyStmt] at ht
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals
      repeat first
        | (inv at ht)
        | (rcases ht with ⟨h, ht⟩)
        | (split at ht)
    all_goals simp_all [DemandNode.visibleAfter]
    all_goals try (split <;> simp_all)

private theorem blockSuffixActive_succ {path sc all value offset st rest}
    (bc : EvaluationContext m plans path (.block (.mk sc all value)) .block)
    (hdrop : st :: rest = all.drop offset) :
    blockSuffixActive bc (offset + 1) =
      (DemandNode.statement st).visibleAfter (blockSuffixActive bc offset) := by
  have hget : all[offset]? = some st := by
    have h : (all.drop offset)[0]? = some st := by rw [← hdrop]; rfl
    simpa using h
  cases bc <;> simp only [blockSuffixActive, DemandNode.visibleForChild]
  all_goals rw [List.take_add_one, hget]; simp only [Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]; cases st <;> rfl

private theorem blockStmt_shrinkFuture {path sc all value offset st rest}
    {pc : PlanContext m plans} (profile : m.profile = .shrink)
    (context : NodeContext pc path (.block (.mk sc all value)) .block)
    (hdrop : st :: rest = all.drop offset)
    (hchild : DemandNode.child? (.block (.mk sc all value)) offset = some (.statement st)) :
    (blockStmtContext (.shrink profile context) offset st hchild).outputFuture =
      rest.flatMap Stmt.variables ++ value.toList.flatMap Expr.variables ++ context.outputFuture := by
  have hphase : DemandNodeHasPhase (.statement st) .statement := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  let transition := context.child rfl offset (.statement st) .statement hchild hphase
  have hbound : offset < all.length := by
    have hlen := congrArg List.length hdrop
    rw [List.length_drop] at hlen
    simp only [List.length_cons] at hlen
    omega
  have hrest : rest = all.drop (offset + 1) := by
    rw [List.drop_add_one_eq_tail_drop, ← hdrop]; rfl
  have hexpectation :
      (DemandNode.block (.mk sc all value)).childExpectation?
        ⟨path, .expression, context.expected.frame.active, context.expected.frame.future,
          context.expected.frame.retained⟩ offset =
        some ⟨(DemandNode.block (.mk sc all value)).visibleForChild context.expected.frame.active offset,
          rest.flatMap Stmt.variables ++ value.toList.flatMap Expr.variables ++ context.outputFuture⟩ := by
    simp [DemandNode.childExpectation?, DemandNode.childFuture, hchild, hbound, hrest,
      NodeContext.outputFuture, List.append_assoc]

  have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
  change transition.context.expected.frame.future = _
  rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, hfuture]

set_option maxHeartbeats 800000 in
theorem step_stmts (ih : Specs m prof plans n) : StmtsSpec m prof plans (n + 1) := by
  intro path sc all value bc offset ss observation W tenv tenv' penv env s tn tn' rst rst' lo
    hOffset hDrop hActive hAccess hProtected hObserved hp hF hsc hT hlo ht hr hE
  cases ss with
  | nil =>
    simp only [tyStmts] at ht; inv at ht
    simp only [rpStmts] at hr; inv at hr
    obtain ⟨rfl, rfl⟩ := ht
    subst hr
    simp only [execStmts, sat_pure]
    have hoff : offset = all.length := by
      have hlen := congrArg List.length hDrop
      simp only [List.length_nil, List.length_drop] at hlen
      omega
    subst offset
    refine ⟨⟨tenv', TSame.refl _, hF, fun _ _ => rfl⟩,
      FootprintS.refl env (Dset W) s, PreservesRootTypes.refl s.store,
      PreservesValues.refl s.store, hObserved, RetainsAliases.refl, ?_, hT, ?_⟩
    · intro _
      exact StoreLe.refl _
    · exact ⟨trivial, rfl⟩
  | cons st rest =>
    have hchild := blockStmtChild? (sc := sc) (value := value) hDrop
    let statementContext := blockStmtContext bc offset st hchild
    simp only [tyStmts] at ht; inv at ht
    simp only [rpStmts] at hr; inv at hr
    obtain ⟨tenv1, t1, hts, htr⟩ := ht
    obtain ⟨r1, hrs, hrr⟩ := hr
    have hm1 := rpStmt_mono hrs
    have hm2 := rpStmts_mono hrr
    have hrest : rest = all.drop (offset + 1) := by
      rw [List.drop_add_one_eq_tail_drop, ← hDrop]; rfl
    have hnextBound : offset + 1 ≤ all.length := by
      have hlen := congrArg List.length hDrop
      simp only [List.length_cons, List.length_drop] at hlen
      omega
    have hmay : statementContext.mayShrink W.P = bc.mayShrink W.P := by
      funext r
      exact propext (bc.child_mayShrink_iff rfl offset (.statement st) .statement hchild
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) W.P r)
    have haccess : statementContext.AccessMatches tenv penv :=
      (bc.child_accessMatches_iff rfl offset (.statement st) .statement hchild
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) tenv penv).2 hAccess
    have hactive : statementContext.ActiveMatches tenv := by
      cases bc with
      | pilot profile active => exact hActive
      | shrink profile context =>
        let transition := context.child rfl offset (.statement st) .statement hchild
          (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
        change ∀ x, x ∈ transition.context.expected.frame.active ↔ x ∈ tenv.visible
        rw [transition.expectedFrameEq, DemandNode.phaseFrame_active transition.phaseFrameEq,
          DemandNode.childFrame_active transition.childFrameEq]
        exact hActive
    have hinput : Frame m W tenv penv env s statementContext.inputFuture := by
      apply hF.changeFuture
      intro x hx hf
      cases bc with
      | pilot profile active => exact (hActive x).2 hx
      | shrink profile context =>
        have hout := blockStmt_shrinkFuture profile context hDrop hchild
        have hin : statementContext.inputFuture = st.variables ++ statementContext.outputFuture := rfl
        rw [hin, hout] at hf
        simpa [blockSuffixFuture, EvaluationContext.outputFuture, ← hDrop,
          List.flatMap_cons, List.append_assoc] using hf
    have hout : statementContext.outputFuture = blockSuffixFuture bc (offset + 1) := by
      cases bc with
      | pilot profile active =>
        change (DemandNode.statement st).visibleAfter (blockSuffixActive
          (EvaluationContext.pilot profile active : EvaluationContext m plans path (.block (.mk sc all value)) .block) offset) = _
        exact (blockSuffixActive_succ (EvaluationContext.pilot profile active :
          EvaluationContext m plans path (.block (.mk sc all value)) .block) hDrop).symm
      | shrink profile context =>
        simpa [blockSuffixFuture, EvaluationContext.outputFuture, ← hrest] using
          blockStmt_shrinkFuture profile context hDrop hchild
    have hretSubset : ∀ alias, alias ∈ bc.retained → alias ∈ statementContext.retained := by
      intro alias hmem
      exact bc.child_retained_subset rfl offset (.statement st) .statement hchild
        (by simp [DemandNodeHasPhase, DemandNode.phaseMatches]) hmem
    simp only [execStmts]
    refine Sat.bind (ih.stmt (path ++ [offset]) st statementContext observation W tenv tenv1
      penv env s sc tn t1 rst r1 lo hactive haccess (hmay ▸ hProtected)
      (hmay ▸ hObserved) hp hinput hsc hT hlo hts hrs (hm2.2.trans hE)) ?_
    rintro fl s1 ⟨hF1, hX1, hRoots1, hValues1, hSafe1, hRet1, hPilot1, hS1, hT1, hfl⟩
    rw [hout] at hF1
    rw [hmay] at hSafe1
    have hRet1' := hRet1.subset hretSubset
    have hActive1 : ∀ x, x ∈ blockSuffixActive bc (offset + 1) ↔ x ∈ tenv1.visible := by
      rw [blockSuffixActive_succ bc hDrop]
      intro x
      have htvis := stmt_visibleAfter hts x
      cases st <;> simp only [DemandNode.visibleAfter] at htvis ⊢
      all_goals first
        | exact (hActive x).trans htvis.symm
        | (split <;> split at htvis <;> simp_all [List.contains_iff_mem])
    have hFinal : Frame m W tenv1 penv env s1 (blockSuffixFuture bc all.length) := by
      apply hF1.changeFuture
      intro x hx hf
      cases bc with
      | pilot profile active => exact (hActive1 x).2 hx
      | shrink profile context =>
        simp only [blockSuffixFuture, List.drop_length, List.flatMap_nil, List.nil_append,
          List.mem_append] at hf ⊢
        exact hf.elim (fun h => Or.inl (Or.inr h)) Or.inr
    cases fl with
    | normal v =>
      refine (ih.stmts path sc all value bc (offset + 1) rest observation W tenv1 tenv' penv
        env s1 t1 tn' r1 rst' lo hnextBound hrest hActive1
        (by cases bc <;> simpa [EvaluationContext.AccessMatches, NodeContext.AccessMatches,
          hS1.mod, hS1.vars] using hAccess) hProtected hSafe1 hp hF1
        (by rw [hS1.scopes]; exact hsc) hT1 (Nat.le_trans hlo hm1.1) htr hrr hE).mono ?_
      rintro fl2 s2 ⟨⟨tenv2, hS2, hF2, hn2⟩, hX2, hRoots2, hValues2, hSafe2,
        hRet2, hPilot2, hT2, hfl2⟩
      refine ⟨⟨tenv2, hS1.trans hS2, hF2, hn2⟩, hX1.trans hX2,
        hRoots1.trans hRoots2, hValues1.trans hValues2, hSafe2, hRet1'.trans hRet2,
        fun h => (hPilot1 h).trans (hPilot2 h), hT2, ?_⟩
      cases fl2 with
      | normal v2 => exact ⟨hfl2.1, by simp [stmtsDiverge, hfl, hfl2.2]⟩
      | brk => exact ⟨by rw [← hS1.loops]; exact hfl2.1, by simp [stmtsHaveBreak, hfl2.2]⟩
      | cont => exact (by rw [← hS1.loops]; exact hfl2)
      | ret v2 => exact ⟨by rw [← hS1.inExpr]; exact hfl2.1, hfl2.2.tsame hS1.impl rfl⟩
    | brk =>
      simp only [sat_pure]
      exact ⟨⟨tenv1, hS1, hFinal, fun v h => by cases h⟩, hX1, hRoots1, hValues1,
        hSafe1, hRet1', hPilot1, hT1.ext (fun _ h => h) hm2.1,
        hfl.1, by simp [stmtsHaveBreak, hfl.2]⟩
    | cont =>
      simp only [sat_pure]
      exact ⟨⟨tenv1, hS1, hFinal, fun v h => by cases h⟩, hX1, hRoots1, hValues1,
        hSafe1, hRet1', hPilot1, hT1.ext (fun _ h => h) hm2.1, hfl⟩
    | ret v =>
      simp only [sat_pure]
      exact ⟨⟨tenv1, hS1, hFinal, fun v h => by cases h⟩, hX1, hRoots1, hValues1,
        hSafe1, hRet1', hPilot1, hT1.ext (fun _ h => h) hm2.1, hfl⟩

private theorem blockFold_sub (active : List VarId) (ss : List Stmt) :
    ∀ x, x ∈ active → x ∈ ss.foldl (fun active statement =>
      match statement with
      | .letS x _ _ => if active.contains x then active else x :: active
      | _ => active) active := by
  induction ss generalizing active with
  | nil => intro x hx; exact hx
  | cons st rest ih =>
    intro x hx
    apply ih
    cases st <;> simp only [List.foldl_cons]
    all_goals first | exact hx | (split <;> simp_all)

private theorem blockSuffixFuture_outer {path sc all value}
    (bc : EvaluationContext m plans path (.block (.mk sc all value)) .block)
    (offset : Nat) : ∀ x, x ∈ bc.outputFuture → x ∈ blockSuffixFuture bc offset := by
  cases bc with
  | pilot profile active => exact blockFold_sub active (all.take offset)
  | shrink profile context =>
    intro x hx
    simp only [blockSuffixFuture, List.mem_append]
    exact Or.inr hx

private theorem blockInputFuture_sub {path sc all value}
    (bc : EvaluationContext m plans path (.block (.mk sc all value)) .block) :
    ∀ x, x ∈ bc.outputFuture → x ∈ bc.inputFuture := by
  cases bc <;> intro x hx <;> exact List.mem_append_right _ hx

private theorem stmts_visible {tenv tenv' : TEnv} {sc tn tn' : Nat} {ss : List Stmt}
    (ht : tyStmts tenv sc ss tn = .ok (tenv', tn')) :
    ∀ x, x ∈ tenv'.visible ↔
      x ∈ (DemandNode.block (.mk sc ss none)).visibleForChild tenv.visible ss.length := by
  induction ss generalizing tenv tn with
  | nil =>
    simp only [tyStmts] at ht; inv at ht
    obtain ⟨rfl, rfl⟩ := ht
    intro x; rfl
  | cons st rest ih =>
    simp only [tyStmts] at ht; inv at ht
    obtain ⟨mid, next, hstmt, hrest⟩ := ht
    intro x
    have h1 := ih hrest x
    have h2 := (DemandNode.block (.mk sc rest none)).visibleForChild_mem_congr rest.length
      (stmt_visibleAfter hstmt) x
    cases st <;> simpa only [DemandNode.visibleForChild, List.take_length, List.foldl_cons,
      DemandNode.visibleAfter] using h1.trans h2

private theorem blockValueChild? {sc : Nat} {ss : List Stmt} {e : Expr} :
    (DemandNode.block (.mk sc ss (some e))).child? ss.length = some (.expression e) := by
  change ((ss.map (some ∘ DemandNode.statement) ++ [some (.expression e)])[ss.length]?).join = _
  rw [List.getElem?_append_right (by simp)]
  simp

private theorem blockValue_shrinkFuture {path sc ss e} {pc : PlanContext m plans}
    (profile : m.profile = .shrink)
    (context : NodeContext pc path (.block (.mk sc ss (some e))) .block) :
    ((EvaluationContext.shrink profile context : EvaluationContext m plans path
      (.block (.mk sc ss (some e))) .block).child rfl ss.length (.expression e) .expression
      blockValueChild? (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture =
      context.outputFuture := by
  let transition := context.child rfl ss.length (.expression e) .expression blockValueChild?
    (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])
  have hexpectation : (DemandNode.block (.mk sc ss (some e))).childExpectation?
      ⟨path, .expression, context.expected.frame.active, context.expected.frame.future,
        context.expected.frame.retained⟩ ss.length =
      some ⟨(DemandNode.block (.mk sc ss (some e))).visibleForChild context.expected.frame.active ss.length,
        context.expected.frame.future⟩ := by
    simp [DemandNode.childExpectation?, DemandNode.childFuture, blockValueChild?]
  have hfuture := DemandNode.childFrame_future transition.childFrameEq hexpectation
  change transition.context.expected.frame.future = context.expected.frame.future
  rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq, hfuture]

set_option maxHeartbeats 1600000 in
theorem step_block (ih : Specs m prof plans n) : BlockSpec m prof plans (n + 1) := by
  intro path sc stmts value bc observation W tenv tenv1 tenv2 penv env s pre
    tn1 tn2 tn3 ty rst1 rst2 rst3 rho lo hActive hAccess hProtected hObserved
    hp hF hsc hsame hvis hpre hlo hts htv hrs hrv hE hkeep
  simp only [execBlock, sat_freshScope_bind, sat_bindAll_bind]
  have hF0 := hF.push hsc
  have hfreshAll : ∀ x, s.store.roots[RootInst.local env.act s.nextScope x]? = none := fun x => by
    cases h : s.store.roots[RootInst.local env.act s.nextScope x]? with
    | none => rfl
    | some v => exact absurd (hF.inv.fresh _ _ _ (by rw [h]; simp)) (Nat.lt_irrefl _)
  obtain ⟨hnd, hpreAll⟩ := hpre
  obtain ⟨tfin, hFb, hSb, hvisb, hleb, hkeepb, hbackb⟩ :=
    frame_pre (env := { env with scopes := (sc, s.nextScope) :: env.scopes }) (rest0 := env.scopes)
      rfl pre _ _ hF0 hnd (by
        intro x v hm
        obtain ⟨_, _, lv, g1, g2, g3, g4, g5⟩ := hpreAll x v hm
        refine ⟨hfreshAll x, lv, g1, g2, g3, g4, fun r hr => ⟨g5 r hr, ?_⟩⟩
        rcases hasTy_target_dom g4 hr with ⟨g, rfl⟩ | hd
        · trivial
        · cases r with
          | global g => trivial
          | «local» a si' x' => exact Nat.le_of_lt (hF.inv.fresh _ _ _ hd))
  have hF1 := hFb.tenv_congr (t2 := tenv1) (hsame.mod.trans hSb.mod.symm)
    (hsame.vars.trans hSb.vars.symm) (hsame.scopes.trans hSb.scopes.symm)
    (fun y hy => (hvisb y).2 ((hvis y).1 hy))
  have hTop : TopB { env with scopes := (sc, s.nextScope) :: env.scopes } lo rst1.nextVar
      { s with nextScope := s.nextScope + 1,
               store := preStore env.act s.nextScope pre s.store } := by
    intro sc' si' rest' he y hy
    cases he
    cases hv : (preStore env.act s.nextScope pre s.store).roots[RootInst.local env.act s.nextScope y]? with
    | none => exact absurd hv hy
    | some v' =>
      rcases hbackb _ v' hv with h0 | ⟨x, hx, e⟩
      · have := hfreshAll y
        rw [this] at h0; cases h0
      · cases e
        obtain ⟨⟨x', v''⟩, hm, rfl⟩ := List.mem_map.1 hx
        obtain ⟨g1, g2, _⟩ := hpreAll _ _ hm
        exact ⟨g1, g2⟩
  have hE2 : EffLe rst2.eff W.E := by
    cases value with
    | none => rw [← hrv.2]; exact hE
    | some e => exact (rpExpr_mono hrv).2.trans hE
  let inner := { env with scopes := (sc, s.nextScope) :: env.scopes }
  let bound := { s with nextScope := s.nextScope + 1, store := preStore env.act s.nextScope pre s.store }
  have hPreFoot : FootprintS inner (Dset W) { s with nextScope := s.nextScope + 1 } bound := by
    refine ⟨Nat.le_refl _, fun r v hv _ _ _ => hkeepb r v hv, ?_, ?_⟩
    · intro r v hv hr hn hd
      rcases hbackb r v hv with h0 | ⟨x, hx, rfl⟩
      · exact h0
      · exact False.elim (hn env.act s.nextScope x rfl (by simp [inner, insts]))
    · intro r hr
      cases hv : bound.store.roots[r]? with
      | none => exact False.elim (hr hv)
      | some v =>
        rcases hbackb r v hv with h0 | ⟨x, hx, rfl⟩
        · exact Or.inl (by rw [h0]; simp)
        · obtain ⟨⟨x', v'⟩, hm, hfst⟩ := List.mem_map.1 hx
          simp only at hfst
          subst x'
          obtain ⟨_, _, lv, hlv, hlsc, _⟩ := hpreAll _ _ hm
          exact Or.inr ⟨x, lv, s.nextScope, env.scopes, by simp [inner, hlsc], hlv, rfl⟩
  have hSafeB : ObservedSafe m W (bc.mayShrink W.P) observation bound.store := by
    refine { hObserved with typed := ⟨?_, ?_⟩, rootsProtected := ?_ }
    · intro r T hobs
      obtain ⟨v, hv, hty⟩ := hObserved.typed.roots r T hobs
      exact ⟨v, hkeepb r v hv, hty.mono hleb⟩
    · intro v T hobs
      exact (hObserved.typed.values v T hobs).mono hleb
    · intro r T v hobs hv hi target ht
      rcases hbackb r v hv with hv0 | ⟨x, _, hr⟩
      · exact hObserved.rootsProtected r T v hobs hv0 hi target ht
      · have hbefore := hObserved.rootsOlder r T hobs
        rw [hr] at hbefore
        exact False.elim ((Nat.not_lt_of_ge hF.base_le) hbefore)
  have hStart : Frame m W tenv1 { penv with scopes := sc :: penv.scopes } inner bound
      (blockSuffixFuture bc 0) := by
    apply hF1.narrowFuture
    intro x hx
    apply List.mem_append_right
    cases bc with
    | pilot profile active =>
      apply List.mem_append_right
      simpa [blockSuffixFuture, blockSuffixActive, DemandNode.visibleForChild] using hx
    | shrink profile context =>
      cases value <;> simpa [blockSuffixFuture, EvaluationContext.inputFuture,
        EvaluationContext.outputFuture, NodeContext.inputFuture, NodeContext.outputFuture,
        DemandNode.variables, Block.variables, List.append_assoc] using hx
  have hGamPush : ∀ roots r, Gam env W.P roots r → Gam inner W.P roots r := by
    rintro roots r ⟨q, hq, hr⟩
    refine ⟨q, hq, ?_⟩
    cases q with
    | «local» x =>
      obtain ⟨lv, si, hv, hlk, hroot⟩ := hr
      have hne : lv.scope ≠ sc := by
        intro h
        exact hsc (hF.scopes_t.symm ▸ (h ▸ lookup_key hlk))
      exact ⟨lv, si, hv, by simp [inner, lookup_cons, hne, hlk], hroot⟩
    | global g => exact hr
    | param i => exact hr
  have exit : ∀ (s2 : St) (tf : TEnv),
      Frame m W tf { penv with scopes := sc :: penv.scopes } inner s2 bc.outputFuture →
      TSame tenv1 tf → FootprintS inner (Dset W) bound s2 →
      ObservedSafe m W (bc.mayShrink W.P) observation s2.store →
      RetainsAliases m W inner bound.store s2.store bc.retained →
      PilotStoreLe m bound s2 →
      Frame m W tenv penv env (relSt env sc s.nextScope s2) bc.outputFuture ∧
      Footprint (insts env) (Dset W) s (relSt env sc s.nextScope s2) ∧
      PreservesRootTypes m W.G observation.roots s.store (relSt env sc s.nextScope s2).store ∧
      PreservesValues m W.G observation.values s.store (relSt env sc s.nextScope s2).store ∧
      ObservedSafe m W (bc.mayShrink W.P) observation (relSt env sc s.nextScope s2).store ∧
      RetainsAliases m W env s.store (relSt env sc s.nextScope s2).store bc.retained ∧
      PilotStoreLe m s (relSt env sc s.nextScope s2) := by
    intro s2 tf hFf hSf hXf hSafe hRet hPilot
    have hAllFoot := hPreFoot.trans hXf
    have hdom : ∀ r, s2.store.roots[r]? ≠ none →
        s.store.roots[r]? ≠ none ∨ ScopeRoots env.vars env.act sc s.nextScope r := by
      intro r hr
      rcases hAllFoot.dom r hr with h0 | ⟨x, lv, si, rest, he, hx, rfl⟩
      · exact Or.inl h0
      · cases he
        exact Or.inr ⟨x, lv, hx, rfl, rfl⟩
    have hPop : Frame m W tenv penv env (relSt env sc s.nextScope s2) bc.outputFuture := by
      apply Frame.pop (tenv := tenv) hFf (hSf.mod.trans hsame.mod).symm
        (hSf.vars.trans hsame.vars).symm (hSf.scopes.trans hsame.scopes)
      · intro x hx hf
        refine ⟨hSf.sub x ((hvis x).2 (Or.inr hx)), ?_⟩
        obtain ⟨lv, si, v, hvar, hlookup, _⟩ := hF.vis x hx (blockInputFuture_sub bc x hf)
        exact ⟨lv, hvar, lookup_key hlookup⟩
      · intro x hx; exact hx
      · intro r hr
        rcases hdom r hr with h0 | h0
        · exact Or.inr (fun a si x e => by subst e; exact hF.inv.fresh _ _ _ h0)
        · exact Or.inl h0
    have hSafeOut := hSafe.releaseScope (sc := sc) hFf hF.base_le
    refine ⟨hPop, hAllFoot.releaseBlock hF, ?_, ?_, hSafeOut, ?_, ?_⟩
    · intro r T hr v hv ht
      exact hSafeOut.typed.roots r T hr
    · intro v T hv ht
      exact hSafeOut.typed.values v T hv
    · intro alias hmem v ⟨hty, hroots⟩
      have hin : AliasAt m W inner bound.store alias v :=
        ⟨hty.mono hleb, fun r hr => hGamPush _ _ (hroots r hr)⟩
      have hty2 := (hRet alias hmem v hin).1
      exact (RetainsAliases.releaseScope (s2 := s2) (aliases := bc.retained) hF
        (Nat.le_refl _) alias hmem v ⟨hty2, hroots⟩)
    · apply PilotStoreLe.releaseScope hF (Nat.le_refl _)
      intro hpilot
      exact hleb.trans (hPilot hpilot)
  refine Sat.bind (ih.stmts path sc stmts value bc 0 stmts observation W tenv1 tenv2
    { penv with scopes := sc :: penv.scopes } inner bound tn1 tn2 rst1 rst2 lo
    (Nat.zero_le _) rfl (by cases bc <;> simpa [blockSuffixActive, DemandNode.visibleForChild,
      EvaluationContext.ActiveMatches, NodeContext.ActiveMatches, DemandExpectedPoint.toPoint, DemandPoint.ActiveMatches] using hActive)
    (by cases bc <;> simpa [EvaluationContext.AccessMatches, NodeContext.AccessMatches,
      hsame.mod, hsame.vars] using hAccess) hProtected hSafeB hp hStart
    (by rw [hsame.scopes]; rfl) hTop hlo hts hrs hE2) ?_
  rintro fl s1 ⟨⟨tenv'', hS'', hF'', hnorm⟩, hXS, hRootsS, hValuesS, hSafeS,
    hRetS, hPilotS, hT1, hfl⟩
  have hOuter : Frame m W tenv'' { penv with scopes := sc :: penv.scopes } inner s1 bc.outputFuture :=
    hF''.narrowFuture (blockSuffixFuture_outer bc stmts.length)
  cases fl with
  | normal v =>
    obtain ⟨rfl, hdv⟩ := hfl
    have htt := hnorm _ rfl
    subst tenv''
    cases value with
    | none =>
      obtain ⟨rfl, rfl⟩ := hrv
      subst htv
      simp only [m_pure_bind, sat_release_bind, sat_pure]
      obtain ⟨g1, g2, gRoots, gValues, gSafe, gRet, gPilot⟩ :=
        exit s1 _ hOuter hS'' hXS hSafeS hRetS hPilotS
      exact ⟨g1, g2, gRoots, gValues, gSafe, gRet, gPilot, rfl, fun r hr => hr.elim, hdv⟩
    | some e =>
      simp only [m_bind_assoc, m_pure_bind]
      have hchild : (DemandNode.block (.mk sc stmts (some e))).child? stmts.length =
          some (.expression e) := blockValueChild?
      have hphase : DemandNodeHasPhase (.expression e) .expression := by
        simp [DemandNodeHasPhase, DemandNode.phaseMatches]
      let ec := bc.child rfl stmts.length (.expression e) .expression hchild hphase
      have hAct : ec.ActiveMatches tenv2 :=
        bc.child_activeMatches rfl stmts.length (.expression e) .expression hchild hphase
          tenv1 tenv2 hActive (stmts_visible hts)
      have hAcc : ec.AccessMatches tenv2 { penv with scopes := sc :: penv.scopes } := by
        apply (bc.child_accessMatches_iff rfl stmts.length (.expression e) .expression
          hchild hphase _ _).2
        cases bc <;> simpa [EvaluationContext.AccessMatches, NodeContext.AccessMatches,
          hS''.mod, hsame.mod, hS''.vars, hsame.vars] using hAccess
      have hMay : ec.mayShrink W.P = bc.mayShrink W.P := by
        funext r
        exact propext (bc.child_mayShrink_iff rfl stmts.length (.expression e) .expression
          hchild hphase W.P r)
      have hInput : Frame m W tenv2 { penv with scopes := sc :: penv.scopes } inner s1 ec.inputFuture := by
        apply hF''.changeFuture
        intro x hx hf
        cases bc with
        | pilot profile active => exact (hAct x).2 hx
        | shrink profile context =>
          have hout := blockValue_shrinkFuture profile context
          have hin : ec.inputFuture = e.variables ++ ec.outputFuture := rfl
          rw [hin, hout] at hf
          simpa [blockSuffixFuture, List.drop_length, EvaluationContext.outputFuture,
            List.flatMap_nil, List.nil_append] using hf
      refine Sat.bind (ih.expr (path ++ [stmts.length]) e ec observation W tenv2
        { penv with scopes := sc :: penv.scopes } inner s1 tn2 tn3 ty rst2 rst3 rho
        hAct hAcc (by rw [hMay]; exact hProtected) (by rw [hMay]; exact hSafeS)
        hp hInput htv hrv hE) ?_
      rintro v' s2 ⟨hF2, hX2, hRoots2, hValues2, hSafe2, hRet2, hPilot2, hv2, hg2⟩
      rw [hMay] at hSafe2
      have hFrameOut : Frame m W tenv2 { penv with scopes := sc :: penv.scopes }
          inner s2 bc.outputFuture := by
        apply hF2.narrowFuture
        intro x hx
        cases bc with
        | pilot profile active =>
          exact blockSuffixFuture_outer
            (EvaluationContext.pilot profile active : EvaluationContext m plans path
              (.block (.mk sc stmts (some e))) .block) stmts.length x hx
        | shrink profile context =>
          rw [blockValue_shrinkFuture profile context]
          exact hx
      have hRet2' : RetainsAliases m W inner s1.store s2.store bc.retained :=
        hRet2.subset (fun alias hmem => bc.child_retained_subset rfl stmts.length
          (.expression e) .expression hchild hphase hmem)
      simp only [sat_release_bind, sat_pure]
      obtain ⟨g1, g2, gRoots, gValues, gSafe, gRet, gPilot⟩ := exit s2 _ hFrameOut hS''
        (hXS.trans hX2.toS) hSafe2 (hRetS.trans hRet2')
        (fun h => (hPilotS h).trans (hPilot2 h))
      have hT2 := hT1.ext hX2.dom (rpExpr_mono hrv).1
      have hsurv : ∀ r, Targets v' r →
          ¬ ScopeRoots env.vars env.act sc s.nextScope r ∧ Gam env W.P rho r := by
        intro r hr
        obtain ⟨q, hq, hrq⟩ := hg2 r hr
        cases q with
        | «local» y =>
          obtain ⟨ly, siy, k1, k2, rfl⟩ := hrq
          have k2' : ((sc, s.nextScope) :: env.scopes).lookup ly.scope = some siy := k2
          rw [lookup_cons] at k2'
          by_cases e : ly.scope = sc
          · simp only [e, if_true, Option.some.injEq] at k2'
            subst k2'
            rcases hasTy_target_dom hv2 hr with ⟨g, hg'⟩ | hd
            · cases hg'
            · exact absurd (hT2 _ _ _ rfl y hd) (hkeep y hq)
          · simp only [e, if_false] at k2'
            refine ⟨?_, ⟨.local y, hq, ly, siy, k1, k2', rfl⟩⟩
            rintro ⟨x', lv', _, _, e'⟩
            cases e'
            exact absurd (hF.inst_lt k2').2 (Nat.lt_irrefl _)
        | global g =>
          have hrq' : r = RootInst.global g := hrq
          subst hrq'
          exact ⟨(by rintro ⟨_, _, _, _, e⟩; cases e), ⟨.global g, hq, rfl⟩⟩
        | param j =>
          refine ⟨?_, ⟨.param j, hq, hrq⟩⟩
          rintro ⟨x', lv', _, _, rfl⟩
          exact absurd (Nat.lt_of_lt_of_le (hF.pAge j _ _ _ hrq) hF.base_le) (Nat.lt_irrefl _)
      exact ⟨g1, g2, gRoots, gValues, gSafe, gRet, gPilot,
        hv2.releaseScope (fun r hr => (hsurv r hr).1), fun r hr => (hsurv r hr).2, hdv⟩
  | brk =>
    obtain ⟨g1, g2, gRoots, gValues, gSafe, gRet, gPilot⟩ :=
        exit s1 _ hOuter hS'' hXS hSafeS hRetS hPilotS
    cases value <;> simp only [m_pure_bind, sat_release_bind, sat_pure] <;>
      exact ⟨g1, g2, gRoots, gValues, gSafe, gRet, gPilot, by rw [← hsame.loops]; exact hfl.1, hfl.2⟩
  | cont =>
    obtain ⟨g1, g2, gRoots, gValues, gSafe, gRet, gPilot⟩ :=
        exit s1 _ hOuter hS'' hXS hSafeS hRetS hPilotS
    cases value <;> simp only [m_pure_bind, sat_release_bind, sat_pure] <;>
      exact ⟨g1, g2, gRoots, gValues, gSafe, gRet, gPilot, by rw [← hsame.loops]; exact hfl⟩
  | ret v =>
    obtain ⟨g1, g2, gRoots, gValues, gSafe, gRet, gPilot⟩ :=
        exit s1 _ hOuter hS'' hXS hSafeS hRetS hPilotS
    have hret : RetOk m W tenv penv (relSt env sc s.nextScope s1) v :=
      RetOk.release hF (Nat.le_trans (Nat.le_succ _) hXS.next) hF.base_le
        (hfl.2.tsame hsame.impl rfl)
    cases value <;> simp only [m_pure_bind, sat_release_bind, sat_pure] <;>
      exact ⟨g1, g2, gRoots, gValues, gSafe, gRet, gPilot, by rw [← hsame.inExpr]; exact hfl.1, hret⟩

end Goose.Core.Sound
