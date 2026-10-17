import Goose.Lower.FuelBoundControlSteps
import Goose.Lower.FuelBoundTyped

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private theorem typed_shortCircuit_fuelBoundAt {n fuel : Nat} {isAnd : Bool} {x : ValueId}
    {cfg : Cfg} {env : Env} {cx : FnCtx} {ls1 ls' : LS} {r : ValueId} {pt1 : Pt}
    {fr1 : Frame} {boolean : Bool} {state : St} {results : List Ty} {b : Expr}
    (right : ExprSource cfg env b state)
    (metadata : SourceResults right.typingEnv right.rootsEnv results) (type : right.ty = .bool)
    (child : ∀ residual, residual ≤ fuel → TypedExprFuelBound n residual cfg results b)
    (hs : shortCircuit isAnd x (lowerExpr b) (lowerEnv cfg.mod env.vars results) ls1 = (r,ls'))
    (hpp : ls1.pp = some pt1) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr1 ls1)
    (hx : fr1.vals[x]? = some (.val (.bool boolean)))
    (moduleEq : cx.cfg.mod = lower cfg.mod) (resultsEq : cx.fn.results = results)
    (generated : GeneratedBuilderState ls1) :
    FuelBoundAt n fuel cx pt1 fr1 (fun n => if isAnd then
      if boolean then evalExpr n cfg env b >>= fun v => expectBool v >>= fun selected => pure (.bool selected)
        else pure (.bool false)
      else if boolean then pure (.bool true)
        else evalExpr n cfg env b >>= fun v => expectBool v >>= fun selected => pure (.bool selected))
      (fun v _ pt' fr' => Post cfg env cx ls1 fr1 ls' fr' pt' [(r,.val v)]) state := by
  obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some hpp
  unfold shortCircuit at hs
  rw [whenLive_some _ _ _ hc1] at hs
  simp only [bind_eq] at hs
  obtain ⟨⟨rb, jb, p⟩, ls_c, h1, u2, ls_d, h2, y, ls_e, h3, u4, ls_f, h4, u5, ls_g, h5, hpure⟩ := hs
  rw [pure_run] at hpure
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpure
  have a_rhs : ls_d.Adv ls_e := advB_lowerExpr b _ _ _ _ h3
  have a_f := adv_emitTerm h4
  have hg : ls_g = { ls_f with cur := some jb } := by
    rw [setCur_run] at h5; exact (Prod.mk.inj h5).2.symm
  have hd : ls_d = { ls_c with cur := some rb } := by
    rw [setCur_run] at h2; exact (Prod.mk.inj h2).2.symm
  have hext_f : ExtT ls_f cx.fn.blocks := by rw [hg] at hext; exact hext
  have hext_e : ExtT ls_e cx.fn.blocks := hext_f.of_adv a_f
  have hext_d : ExtT ls_d cx.fn.blocks := hext_e.of_adv a_rhs
  have hext_c : ExtT ls_c cx.fn.blocks := by rw [hd] at hext_d; exact hext_d
  obtain ⟨hrb, hjb, hpv, hvc, hstc, hcurc, hinst, hbrb, hbjb⟩ := scFork_facts h1 hpp hext_c
  obtain ⟨-, hszc⟩ := scFork_ids h1
  cases u2
  cases u4
  cases u5
  subst hrb hjb hpv
  obtain ⟨Trb, hTrb, hTrbp⟩ := hext_c.params hbrb
  obtain ⟨Tjb, hTjb, hTjbp⟩ := hext_c.params hbjb
  have hdb : ls_d.blocks = ls_c.blocks := by rw [hd]
  have hdpp : ls_d.pp = some (ls1.blocks.size, 0) := by
    rw [hd]; exact LS.pp_cur hbrb
  have hstd : ls_d.stack = ls1.stack := by rw [hd]; exact hstc
  have hrel_d : Rel cfg env cx fr1 ls_d := hrel.stack_eq hstd
  have hvd : ls_d.vals.size = ls1.vals.size + 1 := by rw [hd]; exact hvc
  have hjb_d : ls_d.blocks[ls1.blocks.size + 1]? = some ⟨[(ls1.vals.size, .data .bool)], #[]⟩ := by
    rw [hdb]; exact hbjb
  have hjb_e : ls_e.blocks[ls1.blocks.size + 1]? = some ⟨[(ls1.vals.size, .data .bool)], #[]⟩ := by
    refine a_rhs.keep _ _ ?_ hjb_d
    rw [hd]
    intro hh
    have := Option.some.inj hh
    nat_omega
  have hjb_f : ls_f.blocks[ls1.blocks.size + 1]? = some ⟨[(ls1.vals.size, .data .bool)], #[]⟩ := by
    cases hce : ls_e.cur with
    | none =>
      rw [emitTerm_none _ _ hce] at h4
      obtain ⟨-, rfl⟩ := Prod.mk.inj h4
      exact hjb_e
    | some be =>
      rw [emitTerm_run _ _ hce] at h4
      obtain ⟨-, rfl⟩ := Prod.mk.inj h4
      have hbe : be ≠ ls1.blocks.size + 1 := by
        rcases a_rhs.cur with h | h | ⟨c, hc, hc1, _⟩
        · rw [hce] at h; cases h
        · rw [hce, hd] at h
          have := Option.some.inj h
          have hszd : ls_d.blocks.size = ls1.blocks.size + 2 := by rw [hdb]; exact hszc
          nat_omega
        · rw [hce] at hc
          have := Option.some.inj hc
          have hszd : ls_d.blocks.size = ls1.blocks.size + 2 := by rw [hdb]; exact hszc
          nat_omega
      show (ls_e.blocks.modify be _)[ls1.blocks.size + 1]? = _
      rw [getElem?_modify_ne hbe]
      exact hjb_e
  have hpp_g : ls_g.pp = some (ls1.blocks.size + 1, 0) := by
    rw [hg]; exact LS.pp_cur hjb_f
  have hst_g : ls_g.stack = ls1.stack := by
    rw [hg]
    show ls_f.stack = _
    rw [a_f.stack, a_rhs.stack, hstd]
  have hv_g : ls1.vals.size + 1 ≤ ls_g.vals.size := by
    rw [hg]
    show _ ≤ ls_f.vals.size
    have := a_f.vals; have := a_rhs.vals
    nat_omega
  have hmono : ls1.vals.size ≤ ls_g.vals.size := Nat.le_trans (Nat.le_succ _) hv_g
  have hlt : ls1.vals.size < ls_g.vals.size := hv_g
  have hTrb' : cx.fn.blocks[ls1.blocks.size]? = some Trb := hTrb
  have hTjb' : cx.fn.blocks[ls1.blocks.size + 1]? = some Tjb := hTjb
  have genC := generated.scFork isAnd x h1
  have genD := genC.setCur (some ls1.blocks.size)
    (by intro current equal; have same := Option.some.inj equal; rw [← same,hszc]; nat_omega) h2
  have rightReflection (residual : Nat) (bound : residual ≤ fuel) :=
    child residual bound env state right metadata ls_d ls_e y (ls1.blocks.size,0) cx fr1 h3 hdpp
      hext_e hrel_d moduleEq resultsEq genD
  have hjoin : ∀ (vb : Val) (pt_e : Pt) (fr_e : Frame),
      Post cfg env cx ls_d fr1 ls_e fr_e pt_e [(y,.val vb)] → ∀ selected, vb = .bool selected →
      ∀ (residual : Nat) (after : St), FuelBoundAt n residual cx pt_e fr_e
        (fun _ => pure (Val.bool selected)) (fun v _ pt' fr' =>
          Post cfg env cx ls1 fr1 ls_g fr' pt' [(ls1.vals.size,.val v)]) after := by
    intro vb pt_e fr_e P selected equal residual after
    subst vb
    obtain ⟨_,_,_,instruction⟩ := emitTerm_facts h4 P.pp hext_f
    have hy : fr_e.vals[y]? = some (.val (.bool selected)) := P.has (y,_) (by simp)
    cases residual with
    | zero => exact FuelBoundAt.zero n _ _ _ _ _ _
    | succ residual =>
      apply FuelBoundAt.br1 instruction hTjb' hTjbp hy
      apply FuelBoundAt.ret
      have same : Same ls1.vals.size fr1 fr_e := P.same.mono (by nat_omega)
      have rel : Rel cfg env cx fr_e ls1 := P.rel.stack_eq (by rw [a_rhs.stack,hstd])
      exact Post.join same rel (Nat.le_refl _) hlt hmono hst_g hpp_g
  have rightJoin (residual : Nat) (bound : residual ≤ fuel) : FuelBoundAt n residual cx
      (ls1.blocks.size,0) fr1
      (fun n => evalExpr n cfg env b >>= fun v => expectBool v >>= fun selected => pure (.bool selected))
      (fun v _ pt' fr' => Post cfg env cx ls1 fr1 ls_g fr' pt' [(ls1.vals.size,.val v)]) state := by
    refine (rightReflection residual bound).bind ?_
    intro vb after pt_e fr_e done P joinFuel joinBound
    have typed := (right.result n vb done).typed
    rw [type] at typed
    obtain ⟨selected,rfl⟩ := Core.Sound.hasTy_bool typed
    simp only [expectBool,pure_bind]
    exact hjoin (.bool selected) pt_e fr_e P selected rfl joinFuel after
  have shortPost (selected : Bool) :
      Post cfg env cx ls1 fr1 ls_g (fr1.set ls1.vals.size (.val (.bool selected)))
        (ls1.blocks.size + 1,0) [(ls1.vals.size,.val (.bool selected))] :=
    Post.join (Same.refl _ _) hrel (Nat.le_refl _) hlt hmono hst_g hpp_g
  cases fuel with
  | zero => exact FuelBoundAt.zero n _ _ _ _ _ _
  | succ fuel =>
    cases isAnd <;> cases boolean
    · have hi : instAt cx.fn pt1 = some
          (.term (.condbr x (ls1.blocks.size + 1) [x] ls1.blocks.size [])) := hinst
      exact FuelBoundAt.condbr_take0 hi hx hTrb' hTrbp rfl (rightJoin fuel (by omega))
    · have hi : instAt cx.fn pt1 = some
          (.term (.condbr x (ls1.blocks.size + 1) [x] ls1.blocks.size [])) := hinst
      exact FuelBoundAt.condbr_take1 hi hx hTjb' hTjbp rfl hx (FuelBoundAt.ret (shortPost true))
    · have hi : instAt cx.fn pt1 = some
          (.term (.condbr x ls1.blocks.size [] (ls1.blocks.size + 1) [x])) := hinst
      exact FuelBoundAt.condbr_take1 hi hx hTjb' hTjbp rfl hx (FuelBoundAt.ret (shortPost false))
    · have hi : instAt cx.fn pt1 = some
          (.term (.condbr x ls1.blocks.size [] (ls1.blocks.size + 1) [x])) := hinst
      exact FuelBoundAt.condbr_take0 hi hx hTrb' hTrbp rfl (rightJoin fuel (by omega))

private theorem typedExprFuelBound_shortCircuit {n fuel : Nat} {cfg : Cfg} {results : List Ty}
    {a b : Expr} (leftClaim : TypedExprFuelBound n fuel cfg results a)
    (rightClaim : ∀ residual, residual ≤ fuel → TypedExprFuelBound n residual cfg results b) (isAnd : Bool) :
    TypedExprFuelBound (n + 1) fuel cfg results (if isAnd then .and a b else .or a b) := by
  let tail (cfg : Cfg) (env : Env) (n : Nat) (boolean : Bool) : M Val := if isAnd then
    if boolean then evalExpr n cfg env b >>= fun v => expectBool v >>= fun selected => pure (.bool selected)
      else pure (.bool false)
    else if boolean then pure (.bool true)
      else evalExpr n cfg env b >>= fun v => expectBool v >>= fun selected => pure (.bool selected)
  cases isAnd
  all_goals
    intro env state source metadata ls ls' r pt cx fr lowering point extension rel moduleEq resultsEq generated
    obtain ⟨left,typing,roots,type,next⟩ := source.shortCircuitChildren _
    have leftMetadata : SourceResults left.typingEnv left.rootsEnv results := by
      rw [typing,roots]; exact metadata
    simp only [Bool.false_eq_true,ite_false,ite_true,lowerExpr,bind_eq] at lowering
    obtain ⟨x,first,firstRun,shortRun⟩ := lowering
    have firstExtension := extension.of_adv (advB_shortCircuit _ x (advB_lowerExpr b) _ _ _ _ shortRun)
    have firstReflection := leftClaim env state left leftMetadata ls first x pt cx fr firstRun point
      firstExtension rel moduleEq resultsEq generated
    have genFirst := generated.lowerExpr a firstRun
    have composition : FuelBoundAt n fuel cx pt fr
        (fun n => evalExpr n cfg env a >>= fun value => expectBool value >>= fun boolean =>
          tail cfg env n boolean) (fun v _ pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(r,.val v)]) state := by
      refine firstReflection.bind ?_
      · intro value after pt1 fr1 done P1 residual bound
        have typed := (left.result n value done).typed
        rw [type] at typed
        obtain ⟨boolean,rfl⟩ := Core.Sound.hasTy_bool typed
        simp only [expectBool,pure_bind]
        obtain ⟨right,rightTyping,rightRoots,rightType⟩ := next n (.bool boolean) after done
        have rightMetadata : SourceResults right.typingEnv right.rootsEnv results := by
          rw [rightTyping,rightRoots]; exact metadata
        have reflected := typed_shortCircuit_fuelBoundAt (boolean := boolean) right rightMetadata rightType
          (fun remaining remainingBound => rightClaim remaining (Nat.le_trans remainingBound bound))
          shortRun P1.pp extension P1.rel (P1.has (x,_) (by simp)) moduleEq resultsEq genFirst
        exact reflected.mono (fun v _ pt' fr' P => (P1.comp P).sub (by simp))
    exact composition.of_source (otherFuel := n + 1)
      (by simp only [Bool.false_eq_true,ite_false,ite_true,evalExpr,tail])

theorem typedExprFuelBound_and {n fuel : Nat} {cfg : Cfg} {results : List Ty} {a b : Expr}
    (left : TypedExprFuelBound n fuel cfg results a)
    (right : ∀ residual, residual ≤ fuel → TypedExprFuelBound n residual cfg results b) :
    TypedExprFuelBound (n + 1) fuel cfg results (.and a b) := typedExprFuelBound_shortCircuit left right true

theorem typedExprFuelBound_or {n fuel : Nat} {cfg : Cfg} {results : List Ty} {a b : Expr}
    (left : TypedExprFuelBound n fuel cfg results a)
    (right : ∀ residual, residual ≤ fuel → TypedExprFuelBound n residual cfg results b) :
    TypedExprFuelBound (n + 1) fuel cfg results (.or a b) := typedExprFuelBound_shortCircuit left right false

#print axioms typedExprFuelBound_and
#print axioms typedExprFuelBound_or

end Goose.Lower
