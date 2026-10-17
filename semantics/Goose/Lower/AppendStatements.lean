import Goose.Lower.MutationStatements

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem stmt_append_typed_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {results : List Ty} {loop : Option LoopCtx} {owner : Place} {src : View} {org : OriginId}
    {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St}
    (source : StmtSource cfg env (.append owner src org) state)
    (hmetadata : SourceResults source.typingEnv source.rootsEnv results)
    (hplace : TypedPlaceClaim n cfg results owner) (hview : TypedViewClaim n cfg results src)
    (hlow : lowerStmt loop (.append owner src org) (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.append owner src org))
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) state := by
  obtain ⟨destination, typingEq, rootsEq, children⟩ := source.appendChildren
  have metadata : SourceResults destination.typingEnv destination.rootsEnv results := by
    rw [typingEq, rootsEq]
    exact hmetadata
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, vw, ls2, h2, h3⟩ := hlow
  have hext2 : ExtT ls2 cx.fn.blocks := hext.of_adv (adv_emitEffect h3)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (advB_lowerView src _ _ _ _ h2)
  simp only [execStmt]
  refine SimEAt.bind (hplace env state destination metadata ls ls1 rp pt cx fr h1 hpp hext1 hrel hgir hresults)
    fun l afterPlace pt1 fr1 donePlace P1 => ?_
  obtain ⟨viewSource, viewTyping, viewRoots⟩ := children n l afterPlace donePlace
  have viewMetadata : SourceResults viewSource.typingEnv viewSource.rootsEnv results := by
    rw [viewTyping, viewRoots]
    exact hmetadata
  refine SimEAt.bind (hview env afterPlace viewSource viewMetadata ls1 ls2 vw pt1 cx fr1 h2 P1.pp hext2 P1.rel hgir hresults)
    fun vwv afterView pt2 fr2 _ P2 => ?_
  have P12 := P1.comp P2
  have hl : fr2.vals[rp]? = some (.val (.ref l)) := P12.has (rp, _) (by simp)
  have hv : fr2.vals[vw]? = some (.view vwv) := P12.has (vw, _) (by simp)
  have hx : execEff cx.fn fr2 (.append rp vw (some org)) =
      (readRun vwv >>= fun elems => checkedAppendLoc l elems org) >>= fun _ => pure fr2 := by
    simp only [execEff, getVal_of hl, getView_of hv, Goose.Core.expectRef, bind_assoc, pure_bind,
      Goose.Core.checkedAppendLoc, checkCapacityAtOrg, checkAppendCapacity, abortAtOrg, abortAt]
    rfl
  exact SimEAt.of_simG (leaf_eff P12 h3 hext (Flow.normal .unit) (by simp only [bind_assoc]) hx) afterView

theorem typedStatementLoopSimulation_append {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {owner : Place} {src : View} {org : OriginId}
    (hplace : TypedPlaceClaim n cfg results owner) (hview : TypedViewClaim n cfg results src) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.append owner src org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter
  have resultEq : result = () := Subsingleton.elim _ _
  subst result
  exact (stmt_append_typed_sim source hmetadata hplace hview hlow hpp hext hrel hgir hresults).prepareNormalLoopFlow

end Goose.Lower
