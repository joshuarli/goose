import Goose.Lower.Each
import Goose.Lower.GeneratedBuilder

namespace Goose.Lower

open Goose.Core Goose.GIR

def eachIterationCore (n : Nat) (cfg : Cfg) (env : Env) (x : VarId) (idx : Option VarId)
    (byRef : Bool) (block : Core.Block) (vw : ViewVal) (i : Nat) : M Flow :=
  (if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
    else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) >>= fun ev =>
  execBlock n cfg env (eachCorePre x idx ev i) block >>= prepareReturn env

def EachStepPost (cx : FnCtx) (header : Pt) (headerInv : Nat → Frame → Prop)
    (post : Flow → Pt → Frame → Prop) (i : Nat) (flow : Flow) (pt : Pt) (fr : Frame) : Prop :=
  match flow with
  | .normal _ | .cont => ∃ frh, headerInv (i + 1) frh ∧ Goes cx pt fr header frh
  | .brk => post (.normal .unit) pt fr
  | .ret value => post (.ret value) pt fr

theorem lowerEachSource_of_sim_at (n : Nat) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (le : LEnv) (ls ls' : LS) (fr : Frame) (pt : Pt) (s : St) (place : Place)
    (owner : Option ValueId) (view : ValueId)
    (hlow : lowerEachSource (.of place) le ls = ((owner, view), ls'))
    (generated : GeneratedBuilderState ls)
    (hext : ExtT ls' cx.fn.blocks)
    (hplace : ∀ r output, lowerPlace place le ls = (r, output) → ExtT output cx.fn.blocks →
      GeneratedBuilderState ls →
      SimEAt cx pt fr (evalPlace n cfg env place)
        (fun loc pt' fr' => Post cfg env cx ls fr output fr' pt' [(r, .val (.ref loc))]) s) :
    SimEAt cx pt fr (evalView (n + 1) cfg env (.of place))
      (fun vw pt' fr' => Post cfg env cx ls fr ls' fr' pt' (EachSourceCells owner view vw)) s := by
  simp only [lowerEachSource, bind_eq] at hlow
  obtain ⟨r, lsPlace, hPlace, rv, lsView, hView, hResult⟩ := hlow
  rw [pure_run] at hResult
  obtain ⟨hpair, rfl⟩ := Prod.mk.inj hResult
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
  have hextPlace := hext.of_adv (adv_emitDef hView)
  simp only [evalView]
  refine SimEAt.bind (hplace r lsPlace hPlace hextPlace generated) fun loc s1 pt1 fr1 _ P => ?_
  have hc : fr1.vals[r]? = some (.val (.ref loc)) := P.has (r, _) (by simp)
  have hop : execPure cx fr1 (.snapshot
      (match place with | .var _ | .global _ => .owner | _ => .borrowed) r) =
      (readLoc loc >>= expectArray) >>= fun lr => pure (.view ⟨loc, 0, lr.1, lr.2⟩) := by
    simp [execPure, getVal_of hc, Goose.Core.expectRef]
  rw [← bind_assoc]
  have hs : SimE cx pt1 fr1
      ((readLoc loc >>= expectArray) >>= fun lr => pure (⟨loc, 0, lr.1, lr.2⟩ : ViewVal))
      (fun vw pt' fr' => Post cfg env cx ls fr lsView fr' pt' (EachSourceCells (some r) rv vw)) := by
    refine SimE.bind (SimE.of_simG (leaf_def_keep (c := readLoc loc >>= expectArray)
      P hView hext (by simp) (fun lr => RVal.view ⟨loc, 0, lr.1, lr.2⟩) hop))
      fun lr pt' fr' P' => ?_
    exact SimE.ret (by simpa [EachSourceCells] using P')
  exact hs.at_state s1

theorem lowerEachSource_val_sim_at (n : Nat) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (le : LEnv) (ls ls' : LS) (fr : Frame) (pt : Pt) (s : St) (expr : Expr)
    (owner : Option ValueId) (view : ValueId)
    (hlow : lowerEachSource (.val expr) le ls = ((owner, view), ls'))
    (generated : GeneratedBuilderState ls)
    (hext : ExtT ls' cx.fn.blocks)
    (hexpr : ∀ r output, lowerExpr expr le ls = (r, output) → ExtT output cx.fn.blocks →
      GeneratedBuilderState ls →
      SimEAt cx pt fr (evalExpr n cfg env expr)
        (fun value pt' fr' => Post cfg env cx ls fr output fr' pt' [(r, .val value)]) s) :
    SimEAt cx pt fr (evalView (n + 1) cfg env (.val expr))
      (fun vw pt' fr' => Post cfg env cx ls fr ls' fr' pt' (EachSourceCells owner view vw)) s := by
  simp only [lowerEachSource, bind_eq] at hlow
  obtain ⟨r, lsExpr, hExpr, rv, lsView, hView, hResult⟩ := hlow
  rw [pure_run] at hResult
  obtain ⟨hpair, rfl⟩ := Prod.mk.inj hResult
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
  have hextExpr := hext.of_adv (adv_emitDef hView)
  simp only [evalView]
  refine SimEAt.bind (hexpr r lsExpr hExpr hextExpr generated) fun value s1 pt1 fr1 _ P => ?_
  have hs : SimE cx pt1 fr1
      (expectSlice value >>= fun slice => pure (⟨slice.1, slice.2.1, slice.2.2, false⟩ : ViewVal))
      (fun vw pt' fr' => Post cfg env cx ls fr lsView fr' pt' (EachSourceCells none rv vw)) := by
    refine SimE.expectSlice fun loc start len hv => ?_
    subst value
    have hc : fr1.vals[r]? = some (.val (.slice loc start len)) := P.has (r, _) (by simp)
    have hop : execPure cx fr1 (.sliceView r) = pure (.view ⟨loc, start, len, false⟩) := by
      simp [execPure, getVal_of hc, Goose.Core.expectSlice]
    have hp : SimE cx pt1 fr1 (pure () >>= fun _ => pure (⟨loc, start, len, false⟩ : ViewVal))
        (fun vw pt' fr' => Post cfg env cx ls fr lsView fr' pt' (EachSourceCells none rv vw)) := by
      refine SimE.bind (SimE.of_simG (leaf_def (c := pure ()) P hView hext (by simp)
        (fun _ => RVal.view ⟨loc, start, len, false⟩) (by simpa using hop)))
        fun _ pt' fr' P' => SimE.ret P'
    simpa only [pure_bind] using hp
  exact hs.at_state s1

theorem eachIteration_sim_at (n : Nat) (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (input withElem withValue output : LS) (fr : Frame) (pt : Pt) (s : St)
    (view counter elem value result : ValueId) (vw : ViewVal) (i : Nat)
    (x : VarId) (idx : Option VarId) (byRef : Bool) (block : Core.Block)
    (loop : LoopCtx) (org : OriginId) (post : Flow → Pt → Frame → Prop)
    (hElem : emitDef (.refElem view counter) le input = (elem, withElem))
    (hValue : eachElemValue x byRef elem le withElem = (value, withValue))
    (hBlock : lowerBlock (some loop) (eachIRPre x idx value counter org)
      false block le withValue = (result, output))
    (hpp : input.pp = some pt) (hext : ExtT output cx.fn.blocks)
    (hrel : Rel cfg env cx fr input)
    (hview : fr.vals[view]? = some (.view vw))
    (hcounter : fr.vals[counter]? = some (.val (.int .i64 i)))
    (hc : counter < input.vals.size)
    (hbody : ∀ ev state pt' fr',
      (if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
        else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) s = .ok ev state →
      Post cfg env cx input fr withValue fr' pt' [(value, .val ev)] →
      PreRel fr' (eachIRPre x idx value counter org) (eachCorePre x idx ev i) →
      SimEAt cx pt' fr' (execBlock n cfg env (eachCorePre x idx ev i) block >>=
        prepareReturn env) post state) :
    SimEAt cx pt fr (eachIterationCore n cfg env x idx byRef block vw i) post s := by
  have aBlock := advB_lowerBlock (some loop) (eachIRPre x idx value counter org)
    false block le withValue result output hBlock
  have hextValue := hext.of_adv aBlock
  have hextElem := hextValue.of_adv (advB_eachElemValue x byRef elem le withElem value withValue hValue)
  have hop := execPure_eachElem (cx := cx) hview hcounter
  have hElemSim := leaf_def (c := pure ()) (Post.init hrel hpp) hElem hextElem (by simp)
    (fun _ => RVal.val (.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)) (by simpa using hop)
  have hunit : eachIterationCore n cfg env x idx byRef block vw i =
      (pure () >>= fun _ => eachIterationCore n cfg env x idx byRef block vw i) := by simp
  rw [hunit]
  refine SimEAt.bind (SimEAt.of_simG hElemSim s) fun _ sElem ptElem frElem hsource PElem => ?_
  have hsElem : sElem = s := (Res.ok.inj (by simpa only [pure_apply] using hsource)).2.symm
  subst sElem
  unfold eachIterationCore
  refine SimEAt.bind (SimEAt.of_simG (eachElemValue_sim PElem x byRef le hValue hextValue) s)
    fun ev state ptValue frValue hsourceValue PValue => ?_
  have hcounterValue : frValue.vals[counter]? = some (.val (.int .i64 i)) := by
    rw [PValue.same counter hc]
    exact hcounter
  have hpre : PreRel frValue (eachIRPre x idx value counter org) (eachCorePre x idx ev i) := by
    have hval := PValue.has (value, .val ev) (by simp)
    cases idx <;> simp [PreRel, eachIRPre, eachCorePre, hval, hcounterValue]
  exact hbody ev state ptValue frValue hsourceValue PValue hpre

theorem eachLength_state {vw : ViewVal} {s s' : St} {len : Nat}
    (h : (if vw.resizable then lengthLoc vw.loc else pure vw.len) s = .ok len s') :
    s' = s := by
  cases hr : vw.resizable
  · simp only [hr, Bool.false_eq_true, ite_false, pure_apply] at h
    exact (Res.ok.inj h).2.symm
  · simp only [hr, ite_true, lengthLoc] at h
    cases hm : s.store.length vw.loc <;> simp only [hm] at h
    · cases h
    · exact (Res.ok.inj h).2.symm

theorem each_sim_at (n : Nat) (cx : FnCtx) (cfg : Cfg) (env : Env)
    (x : VarId) (idx : Option VarId) (byRef : Bool) (block : Core.Block) (vw : ViewVal)
    (header body : Pt) (headerInv bodyInv : Nat → Frame → Prop)
    (allowed bodyAllowed : Nat → St → Prop) (post : Flow → Pt → Frame → Prop)
    (hbranch : EachBranch cx vw header body headerInv bodyInv post)
    (henter : ∀ i s len s', allowed i s →
      (if vw.resizable then lengthLoc vw.loc else pure vw.len) s = .ok len s' →
      i < len → bodyAllowed i s)
    (hbody : ∀ k, k < n → ∀ i fr s, bodyInv i fr → bodyAllowed i s →
      SimEAt cx body fr (eachIterationCore k cfg env x idx byRef block vw i)
        (EachStepPost cx header headerInv post i) s)
    (hretain : ∀ k, k < n → ∀ i s flow s', bodyAllowed i s →
      eachIterationCore k cfg env x idx byRef block vw i s = .ok flow s' →
      (match flow with | .normal _ | .cont => allowed (i + 1) s' | _ => True)) :
    ∀ i fr s, headerInv i fr → allowed i s →
      SimEAt cx header fr (execEach n cfg env x idx byRef block vw i >>= prepareReturn env) post s := by
  induction n with
  | zero =>
    intro i fr s _ _
    simp only [execEach]
    exact (SimE.of_simG SimG.of_timeout_bind).at_state s
  | succ n ih =>
    intro i fr s hinv hallowed
    rw [prepareReturn_execEach]
    unfold preparedEach
    refine SimEAt.bind ((hbranch i fr hinv).at_state s) fun len s1 pt1 fr1 hlen hbranchResult => ?_
    have hs1 : s1 = s := eachLength_state hlen
    subst s1
    by_cases hi : i < len
    · simp only [hi, ite_true] at hbranchResult ⊢
      obtain ⟨hpt, hinvBody⟩ := hbranchResult
      subst pt1
      rw [← bind_assoc]
      change SimEAt cx body fr1 (eachIterationCore n cfg env x idx byRef block vw i >>= _) post s
      have hbodyAllowed := henter i s len s hallowed hlen hi
      refine SimEAt.bind (hbody n (Nat.lt_succ_self n) i fr1 s hinvBody hbodyAllowed)
        fun flow s2 pt2 fr2 hsource hflow => ?_
      cases flow with
      | normal value | cont =>
        obtain ⟨frh, hinvh, hgo⟩ := hflow
        have hallowed2 := hretain n (Nat.lt_succ_self n) i s _ s2 hbodyAllowed hsource
        exact SimEAt.goes hgo (ih
          (fun k hk => hbody k (Nat.lt_trans hk (Nat.lt_succ_self n)))
          (fun k hk => hretain k (Nat.lt_trans hk (Nat.lt_succ_self n)))
          (i + 1) frh s2 hinvh hallowed2)
      | brk => exact SimEAt.ret hflow
      | ret value => exact SimEAt.ret hflow
    · simp only [hi, ite_false] at hbranchResult ⊢
      exact SimEAt.ret hbranchResult

end Goose.Lower
