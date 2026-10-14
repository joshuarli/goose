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

end Goose.Lower
