import Goose.Lower.MutationStatements

namespace Goose.Lower

open Goose.Core Goose.GIR

private theorem expectSameTyAt {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {t u : IntTy}
    {next : Unit → M α} {post : α → Pt → GIR.Frame → Prop} {state : St}
    (h : t = u → SimEAt cx pt fr (next ()) post state) :
    SimEAt cx pt fr (Core.expectSameTy t u >>= next) post state := by
  by_cases equal : t = u
  · subst u
    simp only [Core.expectSameTy, if_true]
    exact h rfl
  · exact SimEAt.of_simG (SimG.of_fault_bind fun s =>
      ⟨.shape, s, by simp [Core.expectSameTy, equal, Core.fault, M.stop]⟩) state

theorem stmt_assignOp_place_expr_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {results : List Ty} {loop : Option LoopCtx} {p : Place} {e : Expr} {op : BinOp} {org : OriginId}
    {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St}
    (source : PlaceSource cfg env p state)
    (metadata : SourceResults source.typingEnv source.rootsEnv results)
    (hplace : TypedPlaceClaim n cfg results p) (hexpr : TypedExprClaim n cfg results e)
    (ready : ∀ location after, evalPlace n cfg env p state = .ok location after →
      ∃ child : ExprSource cfg env e after, SourceResults child.typingEnv child.rootsEnv results)
    (hlow : lowerStmt loop (.assignOp op p e org) (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.assignOp op p e org))
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) state := by
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, old, ls2, h2, rhs, ls3, h3, ty, ls3', h4, res, ls4, h5, h6⟩ := hlow
  have e4 := intTyOf_eq h4
  subst e4
  have hext4 : ExtT ls4 cx.fn.blocks := hext.of_adv (adv_emitEffect h6)
  have hext3 : ExtT ls3' cx.fn.blocks := hext4.of_adv (adv_emitDef h5)
  have hext2 : ExtT ls2 cx.fn.blocks := hext3.of_adv (advB_lowerExpr e _ _ _ _ h3)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (adv_emitDef h2)
  simp only [execStmt]
  refine SimEAt.bind (hplace env state source metadata ls ls1 rp pt cx fr h1 hpp hext1 hrel hgir hresults)
    fun l afterPlace pt1 fr1 done P1 => ?_
  obtain ⟨child, childMetadata⟩ := ready l afterPlace done
  have hl1 : fr1.vals[rp]? = some (.val (.ref l)) := P1.has (rp, _) (by simp)
  refine SimEAt.bind (SimEAt.of_simG (leaf_def_keep P1 h2 hext2 (by simp) RVal.val (c := readLoc l) ?_) afterPlace)
    fun va afterRead pt2 fr2 readDone P2 => ?_
  · simp only [execPure, getVal_of hl1, Goose.Core.expectRef, bind_assoc, pure_bind]
  have sameState : afterRead = afterPlace := by
    unfold readLoc at readDone
    split at readDone <;> cases readDone <;> rfl
  subst afterRead
  refine SimEAt.expectInt fun t x hva => ?_
  subst hva
  refine SimEAt.bind (hexpr env afterPlace child childMetadata ls2 ls3' rhs pt2 cx fr2 h3 P2.pp hext3 P2.rel hgir hresults)
    fun vb afterExpr pt3 fr3 _ P3 => ?_
  refine SimEAt.expectInt fun u y hvb => ?_
  subst hvb
  refine expectSameTyAt fun htu => ?_
  subst htu
  have P23 := P2.comp P3
  have hx : fr3.vals[old]? = some (.val (.int t x)) := P23.has (old, _) (by simp)
  have hy : fr3.vals[rhs]? = some (.val (.int t y)) := P23.has (rhs, _) (by simp)
  have hexec := execPure_bin P3.rel.prof hx hy (t0 := ty) (op := op) (o := org)
  dsimp only
  generalize evalBin cfg.profile op t x y = ev at hexec ⊢
  cases ev with
  | error k =>
    dsimp only at hexec ⊢
    have key := leaf_def_keep P23 h5 hext4 (by simp) RVal.val hexec
    exact SimEAt.of_simG (SimG.of_stops (c := (abortAt (AbortKind.ofNum k) org : M Val))
      (c' := (abortAt (AbortKind.ofNum k) org : M Flow))
      (fun s b s1 => by simp [abortAt, M.stop])
      (fun s e s1 h => by simp only [abortAt, M.stop, Res.stop.injEq] at h ⊢; exact h) key) afterExpr
  | ok rr =>
    dsimp only at hexec ⊢
    show SimEAt cx pt3 fr3 (pure (Val.int t rr) >>= fun res => writeLoc l res >>= fun _ =>
      pure (Flow.normal Val.unit)) _ afterExpr
    refine SimEAt.bind (SimEAt.of_simG (leaf_def_keep P23 h5 hext4 (by simp) RVal.val hexec) afterExpr)
      fun vr afterBin pt4 fr4 _ P4 => ?_
    have hrp : fr4.vals[rp]? = some (.val (.ref l)) := P4.has (rp, _) (by simp)
    have hrs : fr4.vals[res]? = some (.val vr) := P4.has (res, _) (by simp)
    have hx' : execEff cx.fn fr4 (.store rp res (some org)) = writeLoc l vr >>= fun _ => pure fr4 := by
      simp only [execEff, getVal_of hrp, getVal_of hrs, Goose.Core.expectRef, bind_assoc, pure_bind]
    exact SimEAt.of_simG (leaf_eff P4 h6 hext (Flow.normal .unit) rfl hx') afterBin

theorem typedStatementLoopSimulation_assignOp {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {place : Place} {expr : Expr} {op : BinOp} {org : OriginId}
    (hplace : TypedPlaceClaim n cfg results place) (hexpr : TypedExprClaim n cfg results expr) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.assignOp op place expr org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter
  obtain ⟨destination, typingEq, rootsEq, _, _, ready⟩ := source.assignOpChildren
  have metadata : SourceResults destination.typingEnv destination.rootsEnv results := by
    rw [typingEq, rootsEq]
    exact hmetadata
  have resultEq : result = () := Subsingleton.elim _ _
  subst result
  apply SimEAt.prepareNormalLoopFlow
  apply stmt_assignOp_place_expr_sim destination metadata hplace hexpr ?_ hlow hpp hext hrel hgir hresults
  intro location after done
  obtain ⟨child, childTyping, childRoots, _⟩ := ready n location after done
  refine ⟨child, ?_⟩
  rw [childTyping, childRoots]
  exact hmetadata

end Goose.Lower
