import Goose.Lower.MutationStatements

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem stmt_resize_typed_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {results : List Ty} {loop : Option LoopCtx} {owner : Place} {size : Expr} {fill : Option Expr}
    {org : OriginId} {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St}
    (source : StmtSource cfg env (.resize owner size fill org) state)
    (hmetadata : SourceResults source.typingEnv source.rootsEnv results)
    (hplace : TypedPlaceClaim n cfg results owner) (hsize : TypedExprClaim n cfg results size)
    (hfill : match fill with | none => True | some expr => TypedExprClaim n cfg results expr)
    (hlow : lowerStmt loop (.resize owner size fill org) (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.resize owner size fill org))
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) state := by
  obtain ⟨destination, element, typingEq, rootsEq, _, _, _, _, children⟩ := source.resizeSizeChildren
  have metadata : SourceResults destination.typingEnv destination.rootsEnv results := by
    rw [typingEq, rootsEq]
    exact hmetadata
  cases fill with
  | none =>
    simp only [lowerStmt, bind_eq] at hlow
    obtain ⟨rp, ls1, h1, v, ls2, h2, opt, ls2', hopt, h3⟩ := hlow
    rw [pure_run] at hopt
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hopt
    have hext2 : ExtT ls2 cx.fn.blocks := hext.of_adv (adv_emitEffect h3)
    have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (advB_lowerExpr size _ _ _ _ h2)
    simp only [execStmt]
    refine SimEAt.bind (hplace env state destination metadata ls ls1 rp pt cx fr h1 hpp hext1 hrel hgir hresults)
      fun l afterPlace pt1 fr1 donePlace P1 => ?_
    obtain ⟨sizeSource, integer, sizeTyping, sizeRoots, _⟩ := children n l afterPlace donePlace
    have sizeMetadata : SourceResults sizeSource.typingEnv sizeSource.rootsEnv results := by
      rw [sizeTyping, sizeRoots]
      exact hmetadata
    refine SimEAt.bind (hsize env afterPlace sizeSource sizeMetadata ls1 ls2 v pt1 cx fr1 h2 P1.pp hext2 P1.rel hgir hresults)
      fun va afterSize pt2 fr2 doneSize P2 => ?_
    refine SimEAt.expectInt fun t k hva => ?_
    subst hva
    have P12 := P1.comp P2
    have hl : fr2.vals[rp]? = some (.val (.ref l)) := P12.has (rp, _) (by simp)
    have hv : fr2.vals[v]? = some (.val (.int t k)) := P12.has (v, _) (by simp)
    let action : M Unit := do
      let len ← lengthLoc l
      let newLen := wrap .i64 k
      if newLen < 0 then abortAt .resizeNegative org
      else if newLen.toNat < len then truncateLoc l newLen.toNat
      else if newLen.toNat == len then pure ()
      else abortAt .resizeFill org
    have hx : execEff cx.fn fr2 (.resize rp v none (some org)) = action >>= fun _ => pure fr2 := by
      funext s
      cases hlen : lengthLoc l s with
      | stop err state => simp [execEff, getVal_of hl, getVal_of hv, Goose.Core.expectRef,
          Goose.Core.expectInt, abortAtOrg, abortAt, action, hlen, bind_apply, pure_apply,
          M.stop, M.instMonad, M.bind', M.pure', Functor.map]
      | ok len state =>
        by_cases hneg : wrap .i64 k < 0
        · simp [execEff, getVal_of hl, getVal_of hv, Goose.Core.expectRef,
            Goose.Core.expectInt, abortAtOrg, abortAt, action, hlen, hneg, bind_apply, pure_apply,
            M.stop, M.instMonad, M.bind', M.pure', Functor.map]
        · by_cases hshort : (wrap .i64 k).toNat < len
          · cases htr : truncateLoc l (wrap .i64 k).toNat state <;>
              simp [execEff, getVal_of hl, getVal_of hv, Goose.Core.expectRef,
                Goose.Core.expectInt, abortAtOrg, abortAt, action, hlen, hneg, hshort, htr,
                bind_apply, pure_apply, M.stop, M.instMonad, M.bind', M.pure', Functor.map]
          · by_cases heq : (wrap .i64 k).toNat = len
            · simp [execEff, getVal_of hl, getVal_of hv, Goose.Core.expectRef,
                Goose.Core.expectInt, abortAtOrg, abortAt, action, hlen, hneg, hshort, heq,
                bind_apply, pure_apply, M.stop, M.instMonad, M.bind', M.pure', Functor.map]
            · simp [execEff, getVal_of hl, getVal_of hv, Goose.Core.expectRef,
                Goose.Core.expectInt, abortAtOrg, abortAt, action, hlen, hneg, hshort, heq,
                bind_apply, pure_apply, M.stop, M.instMonad, M.bind', M.pure', Functor.map]
    apply SimEAt.of_simG (leaf_eff P12 h3 hext (Flow.normal .unit) ?_ hx) afterSize
    funext s
    cases hlen : lengthLoc l s with
    | stop err state => simp [action, hlen, bind_apply, pure_apply, M.instMonad, M.bind', M.pure', Functor.map]
    | ok len state =>
      by_cases hneg : wrap .i64 k < 0
      · simp [action, hlen, hneg, abortAt, bind_apply, pure_apply, M.stop, M.instMonad, M.bind', M.pure', Functor.map]
      · by_cases hshort : (wrap .i64 k).toNat < len
        · cases htr : truncateLoc l (wrap .i64 k).toNat state <;>
            simp [action, hlen, hneg, hshort, htr, bind_apply, pure_apply, M.stop, M.instMonad, M.bind', M.pure', Functor.map]
        · by_cases heq : (wrap .i64 k).toNat = len
          · simp [action, hlen, hneg, hshort, heq, abortAt, bind_apply, pure_apply, M.stop, M.instMonad, M.bind', M.pure', Functor.map]
          · simp [action, hlen, hneg, hshort, heq, abortAt, bind_apply, pure_apply, M.stop, M.instMonad, M.bind', M.pure', Functor.map]
  | some fillExpr =>
    simp only [lowerStmt, bind_eq] at hlow
    obtain ⟨rp, ls1, h1, v, ls2, h2, fv, ls3, h3, opt, ls3', hopt, h4⟩ := hlow
    rw [pure_run] at hopt
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hopt
    have hext3 : ExtT ls3 cx.fn.blocks := hext.of_adv (adv_emitEffect h4)
    have hext2 : ExtT ls2 cx.fn.blocks := hext3.of_adv (advB_lowerExpr fillExpr _ _ _ _ h3)
    have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (advB_lowerExpr size _ _ _ _ h2)
    simp only [execStmt]
    refine SimEAt.bind (hplace env state destination metadata ls ls1 rp pt cx fr h1 hpp hext1 hrel hgir hresults)
      fun l afterPlace pt1 fr1 donePlace P1 => ?_
    obtain ⟨sizeSource, integer, sizeTyping, sizeRoots, _⟩ := children n l afterPlace donePlace
    have sizeMetadata : SourceResults sizeSource.typingEnv sizeSource.rootsEnv results := by
      rw [sizeTyping, sizeRoots]
      exact hmetadata
    refine SimEAt.bind (hsize env afterPlace sizeSource sizeMetadata ls1 ls2 v pt1 cx fr1 h2 P1.pp hext2 P1.rel hgir hresults)
      fun sizeVal afterSize pt2 fr2 doneSize P2 => ?_
    refine SimEAt.expectInt fun t k hsize => ?_
    subst hsize
    obtain ⟨fillSource, fillTyping, fillRoots, _⟩ := source.resizeFillChild n n l (.int t k) donePlace doneSize
    have fillMetadata : SourceResults fillSource.typingEnv fillSource.rootsEnv results := by
      rw [fillTyping, fillRoots]
      exact hmetadata
    refine SimEAt.bind (hfill env afterSize fillSource fillMetadata ls2 ls3 fv pt2 cx fr2 h3 P2.pp hext3 P2.rel hgir hresults)
      fun fillVal afterFill pt3 fr3 _ P3 => ?_
    have P13 := P1.comp P2 |>.comp P3
    have hl : fr3.vals[rp]? = some (.val (.ref l)) := P13.has (rp, _) (by simp)
    have hs : fr3.vals[v]? = some (.val (.int t k)) := P13.has (v, _) (by simp)
    have hf : fr3.vals[fv]? = some (.val fillVal) := P13.has (fv, _) (by simp)
    let action : M Unit := do
      let len ← lengthLoc l
      let newLen := wrap .i64 k
      if newLen < 0 then abortAt .resizeNegative org
      else if newLen.toNat < len then truncateLoc l newLen.toNat
      else if newLen.toNat == len then pure ()
      else do
        checkAppendCapacity l (newLen.toNat - len) org
        let _ ← appendLoc l (Array.replicate (newLen.toNat - len) fillVal)
        pure ()
    have hx : execEff cx.fn fr3 (.resize rp v (some fv) (some org)) = action >>= fun _ => pure fr3 := by
      funext s
      cases hlen : lengthLoc l s with
      | stop err state => simp [execEff, getVal_of hl, getVal_of hs, getVal_of hf,
          Goose.Core.expectRef, Goose.Core.expectInt, abortAtOrg, abortAt, action, hlen,
          bind_apply, pure_apply, M.instMonad, M.bind', M.pure', Functor.map]
      | ok len state =>
        by_cases hneg : wrap .i64 k < 0
        · simp [execEff, getVal_of hl, getVal_of hs, getVal_of hf, Goose.Core.expectRef,
            Goose.Core.expectInt, abortAtOrg, abortAt, action, hlen, hneg, bind_apply, pure_apply,
            M.stop, M.instMonad, M.bind', M.pure', Functor.map]
        · by_cases hshort : (wrap .i64 k).toNat < len
          · cases htr : truncateLoc l (wrap .i64 k).toNat state <;>
              simp [execEff, getVal_of hl, getVal_of hs, getVal_of hf, Goose.Core.expectRef,
                Goose.Core.expectInt, abortAtOrg, abortAt, action, hlen, hneg, hshort, htr,
                bind_apply, pure_apply, M.instMonad, M.bind', M.pure', Functor.map]
          · by_cases heq : (wrap .i64 k).toNat = len
            · simp [execEff, getVal_of hl, getVal_of hs, getVal_of hf, Goose.Core.expectRef,
                Goose.Core.expectInt, abortAtOrg, abortAt, action, hlen, hneg, hshort, heq,
                bind_apply, pure_apply, M.instMonad, M.bind', M.pure', Functor.map]
            · cases hcap : checkAppendCapacity l ((wrap .i64 k).toNat - len) org state with
              | stop err state' => simp [execEff, getVal_of hl, getVal_of hs, getVal_of hf,
                  Goose.Core.expectRef, Goose.Core.expectInt, abortAtOrg, abortAt, action,
                  hlen, hneg, hshort, heq, hcap, checkCapacityAtOrg_some,
                  bind_apply, pure_apply, M.instMonad, M.bind', M.pure', Functor.map]
              | ok _ state' =>
                cases happ : appendLoc l (Array.replicate ((wrap .i64 k).toNat - len) fillVal) state' <;>
                  simp [execEff, getVal_of hl, getVal_of hs, getVal_of hf, Goose.Core.expectRef,
                    Goose.Core.expectInt, abortAtOrg, abortAt, action, hlen, hneg, hshort, heq,
                    hcap, happ, checkCapacityAtOrg_some, bind_apply, pure_apply,
                    M.instMonad, M.bind', M.pure', Functor.map]
    apply SimEAt.of_simG (leaf_eff P13 h4 hext (Flow.normal .unit) ?_ hx) afterFill
    funext s
    cases hlen : lengthLoc l s with
    | stop err state => simp [action, hlen, bind_apply, pure_apply, M.bind', M.pure', Functor.map]
    | ok len state =>
      by_cases hneg : wrap .i64 k < 0
      · simp [action, hlen, hneg, abortAt, bind_apply, pure_apply, M.stop, M.bind', M.pure', Functor.map]
      · by_cases hshort : (wrap .i64 k).toNat < len
        · cases htr : truncateLoc l (wrap .i64 k).toNat state <;>
            simp [action, hlen, hneg, hshort, htr, bind_apply, pure_apply, M.bind', M.pure', Functor.map]
        · by_cases heq : (wrap .i64 k).toNat = len
          · simp [action, hlen, hneg, hshort, heq, abortAt, bind_apply, pure_apply, M.stop, M.bind', M.pure', Functor.map]
          · cases hcap : checkAppendCapacity l ((wrap .i64 k).toNat - len) org state with
            | stop err state' => simp [action, hlen, hneg, hshort, heq, hcap, bind_apply, pure_apply, M.bind', M.pure', Functor.map]
            | ok _ state' =>
              cases happ : appendLoc l (Array.replicate ((wrap .i64 k).toNat - len) fillVal) state' <;>
                simp [action, hlen, hneg, hshort, heq, hcap, happ, bind_apply, pure_apply, M.bind', M.pure', Functor.map]

theorem typedStatementLoopSimulation_resize {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {owner : Place} {size : Expr} {fill : Option Expr} {org : OriginId}
    (hplace : TypedPlaceClaim n cfg results owner) (hsize : TypedExprClaim n cfg results size)
    (hfill : match fill with | none => True | some expr => TypedExprClaim n cfg results expr) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.resize owner size fill org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter
  have resultEq : result = () := Subsingleton.elim _ _
  subst result
  cases fill with
  | none => exact (stmt_resize_typed_sim source hmetadata hplace hsize (by trivial) hlow hpp hext hrel hgir hresults).prepareNormalLoopFlow
  | some expr => exact (stmt_resize_typed_sim source hmetadata hplace hsize hfill hlow hpp hext hrel hgir hresults).prepareNormalLoopFlow

end Goose.Lower
