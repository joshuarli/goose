import Goose.Lower.TypedCall
import Goose.Lower.TypedExpressionChecks

namespace Goose.Lower.TypedCallChecks

open Goose.Core Goose.GIR Goose.Proofs.Lower

private theorem emptyBlock_sim {cfg : Cfg} {env : Env} {cx : FnCtx} {scope : ScopeId}
    {pre : List (SlotId × ValueId × OriginId)} {pre' : List (VarId × Val)} {le : LEnv}
    {ls ls' : LS} {r : ValueId} {pt : Pt} {fr : GIR.Frame}
    (hscope : ∀ item ∈ pre, ∃ lv, env.vars[item.1]? = some lv ∧ lv.scope = scope)
    (hlow : lowerBlock none pre false (.mk scope [] none) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hpre : PreRel fr pre pre') :
    SimG cx pt fr (execBlock 2 cfg env pre' (.mk scope [] none))
      (BlockFlowPost cfg env cx ls fr ls' (.mk scope [] none) false r) := by
  obtain ⟨entered, initialized, statements, valued, left, u0, u1, result,
    henter, hinit, hstatements, hvalue, hleave, hfinal, hresult⟩ := prefixBlock_unfold hlow
  simp only [lowerStmts, pure_run] at hstatements
  obtain ⟨_, rfl⟩ := Prod.mk.inj hstatements
  simp only [lowerBlockValue, ite_false, pure_run] at hvalue
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hvalue
  have hextLeft : ExtT left cx.fn.blocks := by simpa [hfinal, ExtT] using hext
  have hextInitialized : ExtT initialized cx.fn.blocks := hextLeft.of_adv (adv_emitEffect hleave)
  have hextEntered : ExtT { entered with stack := scope :: entered.stack } cx.fn.blocks :=
    hextInitialized.of_adv (advB_initSlots pre _ _ _ _ hinit)
  have hextBeforeStack : ExtT entered cx.fn.blocks := by simpa [ExtT] using hextEntered
  rw [execBlock_pre]
  simp only [prefixCoreBlock, execStmts, pure_bind, valueFlow]
  refine SimG.bind (block_enter hpp henter hextBeforeStack hrel)
    fun scopeInst pt1 fr1 ⟨hpp1, hsize1, hvals1, hrel1⟩ => ?_
  let inner : Env := { env with scopes := (scope, scopeInst) :: env.scopes }
  have hpre1 : PreRel fr1 pre pre' := PreRel.ext hvals1 hpre
  refine SimG.bind (initSlots_sim (env := inner) rfl pre pre' hscope hinit hpp1
    hextInitialized hrel1 hpre1) fun _ pt2 fr2 ⟨hpp2, hfr2, hstack2, hvals2⟩ => ?_
  subst fr2
  have hrel2 : Rel cfg inner cx fr1 initialized := hrel1.stack_eq hstack2
  refine SimG.bind (block_leave hpp2 hleave hextLeft hrel2)
    fun _ pt3 fr3 ⟨hpp3, hsize3, hvals3, hrel3⟩ => ?_
  have hrelFinal : Rel cfg env cx fr3 ls' := by simpa [hfinal] using hrel3
  have hppFinal : ls'.pp = some pt3 := by simpa [hfinal, LS.pp] using hpp3
  have hsizeFinal : ls'.vals.size = initialized.vals.size := by simpa [hfinal] using hsize3
  exact SimG.ret (Or.inl ⟨.unit, rfl, fun _ => rfl, by
    simp only [blockCells, Bool.false_eq_true, Bool.or_self, ite_false]
    exact (Post.init hrel2 hpp2).rescope (by simpa [hvals2] using hsize1) hvals1
      hppFinal hsizeFinal hvals3 hrelFinal⟩)

open TypedExpressionChecks in
theorem parameterized_body (profile : NumProfile) (depth : Nat) (values : List Val) (state : St)
    (hp : boolCallee.params.size = values.length) :
    CalleeBodyAt 2 ⟨profile, sourceModule⟩ 1 boolCallee depth values state := by
  let le := lowerEnv sourceModule boolCallee.vars boolCallee.results.toList
  let body := lowerBlock none (callPre boolCallee) false boolCallee.body le (callEntry boolCallee)
  let cx : FnCtx := ⟨⟨profile, lower sourceModule⟩, lowerImplAt sourceModule 1 boolCallee⟩
  have hextTail : ExtT (bodyTail boolCallee le body.1 body.2) cx.fn.blocks := by
    rw [lowerImplAt_call_blocks]
    exact extT_finish _
  have hextBody : ExtT body.2 cx.fn.blocks := hextTail.of_adv
    (advB_finishFunction boolCallee body.1 le body.2
      (finishFunction boolCallee body.1 le body.2).1 (bodyTail boolCallee le body.1 body.2) rfl)
  unfold CalleeBodyAt
  apply SimEAt.of_simG
  exact emptyBlock_sim (le := le) (callPre_scopes (m := sourceModule) (impl := boolCallee) (by cbv))
    rfl (callEntry_pp boolCallee) hextBody
    (callFrame_rel sourceModule profile 1 boolCallee state.nextAct (depth + 1) values)
    (callFrame_preRel boolCallee state.nextAct (depth + 1) values hp)

open TypedExpressionChecks in
theorem parameterized_call (profile : NumProfile) (depth : Nat) (state : St) :
    EventualM (enterCall 3 ⟨profile, sourceModule⟩ depth 1 [.bool true, .bool false])
      (fun fuel => callFn fuel ⟨profile, lower sourceModule⟩ depth 1 [.bool true, .bool false]) state :=
  typedCall_of_body (m := sourceModule) (c := 1) (ctx := ⟨1, "bools", [], [], []⟩)
    (impl := boolCallee) rfl rfl profile 2 depth _ state (parameterized_body profile depth _ state)

open TypedExpressionChecks in
#guard [NumProfile.release, .debug].all fun profile =>
  match enterCall 3 ⟨profile, sourceModule⟩ 4 1 [.bool true, .bool false] St.initial,
      callFn 20 ⟨profile, lower sourceModule⟩ 4 1 [.bool true, .bool false] St.initial with
  | .ok .unit coreState, .ok .unit girState =>
    coreState.trace == girState.trace && coreState.nextAct == girState.nextAct &&
      coreState.nextScope == girState.nextScope &&
      coreState.store.roots.isEmpty && girState.store.roots.isEmpty
  | _, _ => false

end Goose.Lower.TypedCallChecks
