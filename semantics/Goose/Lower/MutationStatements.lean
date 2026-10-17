import Goose.Lower.TypedStatements

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem stmt_assign_place_expr_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {results : List Ty} {loop : Option LoopCtx} {place : Place} {expr : Expr} {org : OriginId}
    {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St}
    (source : PlaceSource cfg env place state)
    (hmetadata : SourceResults source.typingEnv source.rootsEnv results)
    (hplace : TypedPlaceClaim n cfg results place)
    (hexpr : TypedExprClaim n cfg results expr)
    (hready : ∀ location after, evalPlace n cfg env place state = .ok location after →
      ∃ child : ExprSource cfg env expr after, SourceResults child.typingEnv child.rootsEnv results)
    (hlow : lowerStmt loop (.assign place expr org) (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.assign place expr org))
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) state := by
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨address, addressed, placeLowered, valueId, evaluated, exprLowered, stored⟩ := hlow
  have exprExtended := hext.of_adv (adv_emitEffect stored)
  have placeExtended := exprExtended.of_adv (advB_lowerExpr expr _ _ _ _ exprLowered)
  simp only [execStmt]
  refine SimEAt.bind (hplace env state source hmetadata ls addressed address pt cx fr placeLowered
    hpp placeExtended hrel hgir hresults) fun location afterPlace pointPlace framePlace donePlace P => ?_
  obtain ⟨child, metadata⟩ := hready location afterPlace donePlace
  refine SimEAt.bind (hexpr env afterPlace child metadata addressed evaluated valueId pointPlace cx
    framePlace exprLowered P.pp exprExtended P.rel hgir hresults)
    fun value afterExpr pointExpr frameExpr _ Q => ?_
  have combined := P.comp Q
  have addressCell := combined.has (address, .val (.ref location)) (by simp)
  have valueCell := combined.has (valueId, .val value) (by simp)
  have storedStep : execEff cx.fn frameExpr (.store address valueId (some org)) =
      writeLoc location value >>= fun _ => pure frameExpr := by
    simp only [execEff, getVal_of addressCell, getVal_of valueCell, Core.expectRef, bind_assoc, pure_bind]
  exact SimEAt.of_simG (leaf_eff combined stored hext (Flow.normal .unit) rfl storedStep) afterExpr

theorem stmt_clear_place_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {results : List Ty} {loop : Option LoopCtx} {owner : Place} {org : OriginId}
    {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St}
    (source : PlaceSource cfg env owner state)
    (hmetadata : SourceResults source.typingEnv source.rootsEnv results)
    (hplace : TypedPlaceClaim n cfg results owner)
    (hlow : lowerStmt loop (.clear owner org) (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.clear owner org))
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) state := by
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨address, addressed, placeLowered, cleared⟩ := hlow
  have placeExtended := hext.of_adv (adv_emitEffect cleared)
  simp only [execStmt]
  refine SimEAt.bind (hplace env state source hmetadata ls addressed address pt cx fr placeLowered
    hpp placeExtended hrel hgir hresults) fun location afterPlace point frame _ P => ?_
  have addressCell := P.has (address, .val (.ref location)) (by simp)
  have clearedStep : execEff cx.fn frame (.clear address (some org)) =
      truncateLoc location 0 >>= fun _ => pure frame := by
    simp only [execEff, getVal_of addressCell, Core.expectRef, bind_assoc, pure_bind]
  exact SimEAt.of_simG (leaf_eff P cleared hext (Flow.normal .unit)
    (by simp only [bind_assoc]) clearedStep) afterPlace

theorem typedStatementLoopSimulation_assign {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {place : Place} {expr : Expr} {org : OriginId}
    (hplace : TypedPlaceClaim n cfg results place) (hexpr : TypedExprClaim n cfg results expr) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.assign place expr org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter
  obtain ⟨destination, destinationTyping, destinationRoots, _, _, ready⟩ := source.assignChildren
  have metadata : SourceResults destination.typingEnv destination.rootsEnv results := by
    rw [destinationTyping, destinationRoots]
    exact hmetadata
  have resultEq : result = () := Subsingleton.elim _ _
  subst result
  apply SimEAt.prepareNormalLoopFlow
  apply stmt_assign_place_expr_sim destination metadata hplace hexpr ?_ hlow hpp hext hrel hgir hresults
  intro location after done
  obtain ⟨child, typingEq, rootsEq, _, _, _⟩ := ready n location after done
  refine ⟨child, ?_⟩
  rw [typingEq, rootsEq]
  exact hmetadata

theorem typedStatementLoopSimulation_clear {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {owner : Place} {org : OriginId}
    (hplace : TypedPlaceClaim n cfg results owner) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.clear owner org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter
  obtain ⟨child, element, typingEq, rootsEq, _⟩ := source.clearChild
  have metadata : SourceResults child.typingEnv child.rootsEnv results := by
    rw [typingEq, rootsEq]
    exact hmetadata
  have resultEq : result = () := Subsingleton.elim _ _
  subst result
  exact (stmt_clear_place_sim child metadata hplace hlow hpp hext hrel hgir hresults).prepareNormalLoopFlow

theorem stmt_popN_place_expr_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {results : List Ty} {loop : Option LoopCtx} {owner : Place} {count : Expr} {org : OriginId}
    {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St}
    (source : PlaceSource cfg env owner state)
    (metadata : SourceResults source.typingEnv source.rootsEnv results)
    (hplace : TypedPlaceClaim n cfg results owner) (hexpr : TypedExprClaim n cfg results count)
    (ready : ∀ location after, evalPlace n cfg env owner state = .ok location after →
      ∃ child : ExprSource cfg env count after, SourceResults child.typingEnv child.rootsEnv results)
    (hlow : lowerStmt loop (.popN owner count org) (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.popN owner count org))
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) state := by
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, v, ls2, h2, h3⟩ := hlow
  have hext2 : ExtT ls2 cx.fn.blocks := hext.of_adv (adv_emitEffect h3)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (advB_lowerExpr count _ _ _ _ h2)
  simp only [execStmt]
  refine SimEAt.bind (hplace env state source metadata ls ls1 rp pt cx fr h1 hpp hext1 hrel hgir hresults)
    fun l afterPlace pt1 fr1 done P1 => ?_
  obtain ⟨child, childMetadata⟩ := ready l afterPlace done
  refine SimEAt.bind (hexpr env afterPlace child childMetadata ls1 ls2 v pt1 cx fr1 h2 P1.pp hext2 P1.rel hgir hresults)
    fun va afterExpr pt2 fr2 _ P2 => ?_
  refine SimEAt.expectInt fun t k hva => ?_
  subst hva
  have P12 := P1.comp P2
  have hl : fr2.vals[rp]? = some (.val (.ref l)) := P12.has (rp, _) (by simp)
  have hc : fr2.vals[v]? = some (.val (.int t k)) := P12.has (v, _) (by simp)
  let action : M Unit := do
    let len ← lengthLoc l
    if k < 0 || k > (len : Int) then abortAt .popNRange org
    else truncateLoc l (len - k.toNat)
  have hx : execEff cx.fn fr2 (.popN rp v (some org)) = action >>= fun _ => pure fr2 := by
    simp [execEff, getVal_of hl, getVal_of hc, Goose.Core.expectRef, Goose.Core.expectInt,
      abortAtOrg, abortAt, action]
    funext s
    cases hlen : lengthLoc l s with
    | stop err state => simp [action, bind_apply, hlen, M.instMonad, M.bind', M.pure', Functor.map]
    | ok len state =>
      by_cases hbad : k < 0 ∨ (len : Int) < k
      · simp [bind_apply, hlen, hbad, M.stop, M.bind', M.pure', Functor.map]
      · simp [bind_apply, hlen, hbad]
  apply SimEAt.of_simG (leaf_eff P12 h3 hext (Flow.normal .unit) ?_ hx) afterExpr
  funext s
  cases hlen : lengthLoc l s with
  | stop err state => simp [action, bind_apply, pure_apply, hlen, M.bind', M.pure', Functor.map]
  | ok len state =>
    by_cases hbad : k < 0 ∨ (len : Int) < k
    · simp [action, bind_apply, pure_apply, hlen, hbad, abortAt, M.stop, M.instMonad, M.bind', M.pure', Functor.map]
    · cases htruncate : truncateLoc l (len - k.toNat) state <;>
        simp [action, bind_apply, pure_apply, hlen, hbad, htruncate, M.instMonad, M.bind', M.pure', Functor.map]

theorem typedStatementLoopSimulation_popN {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {owner : Place} {count : Expr} {org : OriginId}
    (hplace : TypedPlaceClaim n cfg results owner) (hexpr : TypedExprClaim n cfg results count) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.popN owner count org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter
  obtain ⟨destination, element, typingEq, rootsEq, _, _, _, _, ready⟩ := source.popNChildren
  have metadata : SourceResults destination.typingEnv destination.rootsEnv results := by
    rw [typingEq, rootsEq]
    exact hmetadata
  have resultEq : result = () := Subsingleton.elim _ _
  subst result
  apply SimEAt.prepareNormalLoopFlow
  apply stmt_popN_place_expr_sim destination metadata hplace hexpr ?_ hlow hpp hext hrel hgir hresults
  intro location after done
  obtain ⟨child, integer, childTyping, childRoots, _⟩ := ready n location after done
  refine ⟨child, ?_⟩
  rw [childTyping, childRoots]
  exact hmetadata

end Goose.Lower
