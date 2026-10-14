import Goose.Lower.Leaf

namespace Goose.Lower

open Goose.Core
open Goose.GIR (ValueId BlockId SlotId ScopeId FnId VTy Bnd PrintPart Op Effect Term Inst Pt instAt
  instsAt runAt Frame FnCtx RVal Func Slot)
open Goose.GIR

theorem checkCapacityAtOrg_some (l : Loc) (count : Nat) (org : OriginId) :
    checkCapacityAtOrg l count (some org) = checkAppendCapacity l count org := by
  funext s
  cases hread : readLoc l s with
  | stop err state => simp [checkCapacityAtOrg, checkAppendCapacity, hread, bind_apply]
  | ok value state =>
    cases value <;>
      simp [checkCapacityAtOrg, checkAppendCapacity, hread, abortAtOrg, abortAt,
        M.stop, bind_apply, pure_apply, M.instMonad, M.bind', M.pure']

/-! ### The fragment -/

mutual
/-- Expressions the proof covers. -/
def exprOk : Expr → Bool
  | .lit .. | .bool _ => true
  | .read p => placeOk p
  | .ref _ p => placeOk p
  | .slice _ v lo hi _ => viewOk v && boundOk lo && boundOk hi
  | .len v => viewOk v
  | .un _ e _ => exprOk e
  | .bin _ a b _ => exprOk a && exprOk b
  | .cmp _ a b => exprOk a && exprOk b
  | .and a b | .or a b => exprOk a && exprOk b
  | .not e => exprOk e
  | .conv _ _ e _ => exprOk e
  | .call .. => false
  | .structLit _ es => exprsOk es
  | .push p e _ => placeOk p && exprOk e
  | .pop p _ => placeOk p
  | .ifE c t f => exprOk c && blockOk t && blockOk f
  | .blockE b => blockOk b
  | .arrLit _ es => exprsOk es
  | .fill _ e => exprOk e

def exprsOk : List Expr → Bool
  | [] => true
  | e :: es => exprOk e && exprsOk es

def placeOk : Place → Bool
  | .field owner _ => placeOk owner
  | .var _ | .global _ => true
  | .deref e => exprOk e
  | .elem v i _ => viewOk v && exprOk i

def viewOk : View → Bool
  | .of p => placeOk p
  | .val e => exprOk e

def boundOk : Bound → Bool
  | .omitted => true
  | .expr e | .fromEnd e => exprOk e

def blockOk : Core.Block → Bool
  | .mk _ ss v => stmtsOk ss && (match v with | none => true | some e => exprOk e)

def stmtsOk : List Stmt → Bool
  | [] => true
  | s :: ss => stmtOk s && stmtsOk ss

def printOk : List PrintArg → Bool
  | [] => true
  | .text _ :: rest => printOk rest
  | .expr e :: rest => exprOk e && printOk rest

def stmtOk : Stmt → Bool
  | .letS _ e _ => exprOk e
  | .assign p e _ => placeOk p && exprOk e
  | .assignOp _ p e _ => placeOk p && exprOk e
  | .rebind _ e _ => exprOk e
  | .expr e _ => exprOk e
  | .append p v _ => placeOk p && viewOk v
  | .popN p e _ => placeOk p && exprOk e
  | .resize p e fill _ => placeOk p && exprOk e && (match fill with | none => true | some v => exprOk v)
  | .clear p _ => placeOk p
  | .assignWhole p e _ => placeOk p && exprOk e
  | .ifS c t f _ => exprOk c && blockOk t && (match f with | none => true | some b => blockOk b)
  | .while c body _ => exprOk c && blockOk body
  | .forRange .. | .forEach .. | .ret .. | .brk _ | .cont _ => false
  | .print args _ => printOk args
  | .assertS e _ => exprOk e
  | .abort .. => true
  | .exit e _ => exprOk e
end

set_option hygiene false in
/-- Pull a component out of the fragment predicate. -/
macro "okpf" : tactic => `(tactic| first | assumption | (simp only [exprOk, exprsOk, placeOk, viewOk, boundOk, blockOk, stmtsOk, printOk, stmtOk, Bool.and_eq_true, Bool.true_and, Bool.and_true] at hok; first | exact hok | exact hok.1 | exact hok.2 | exact hok.1.1 | exact hok.1.2 | exact hok.2.1 | exact hok.2.2 | exact hok.1.1.1 | exact hok.2.2.1 | exact hok.2.2.2 | exact hok.2.1.1 | exact hok.2.1.2 | exact hok.1.2.1 | exact hok.1.2.2))

/-! ### Combining the results of fragments -/

/-! ### Claims -/

def ExprClaim (n : Nat) (e : Expr) : Prop :=
  exprOk e = true → ∀ (le : LEnv) (ls : LS) (r : ValueId) (ls' : LS) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : Frame), lowerExpr e le ls = (r, ls') → ls.pp = some pt → ExtT ls' cx.fn.blocks →
    Rel cfg env cx fr ls →
    SimG cx pt fr (evalExpr n cfg env e) (fun v pt' fr' =>
      Post cfg env cx ls fr ls' fr' pt' [(r, .val v)])

def PlaceClaim (n : Nat) (p : Place) : Prop :=
  placeOk p = true → ∀ (le : LEnv) (ls : LS) (r : ValueId) (ls' : LS) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : Frame), lowerPlace p le ls = (r, ls') → ls.pp = some pt → ExtT ls' cx.fn.blocks →
    Rel cfg env cx fr ls →
    SimG cx pt fr (evalPlace n cfg env p) (fun l pt' fr' =>
      Post cfg env cx ls fr ls' fr' pt' [(r, .val (.ref l))])

def ViewClaim (n : Nat) (v : View) : Prop :=
  viewOk v = true → ∀ (le : LEnv) (ls : LS) (r : ValueId) (ls' : LS) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : Frame), lowerView v le ls = (r, ls') → ls.pp = some pt → ExtT ls' cx.fn.blocks →
    Rel cfg env cx fr ls →
    SimG cx pt fr (evalView n cfg env v) (fun vw pt' fr' =>
      Post cfg env cx ls fr ls' fr' pt' [(r, .view vw)])

/-- What a lowered bound stands for. -/
def BndSpec (len : Nat) (dflt : Int) : Bnd → Int → List (ValueId × RVal) → Prop
  | .omitted, k, cells => k = dflt ∧ cells = []
  | .val v, k, cells => ∃ t, cells = [(v, .val (.int t k))]
  | .fromEnd v, k, cells => ∃ t kk, k = (len : Int) - kk ∧ cells = [(v, .val (.int t kk))]

def BoundClaim (n : Nat) (bd : Bound) : Prop :=
  boundOk bd = true → ∀ (le : LEnv) (ls : LS) (bnd : Bnd) (ls' : LS) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : Frame) (len : Nat) (dflt : Int), lowerBound bd le ls = (bnd, ls') → ls.pp = some pt →
    ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    SimG cx pt fr (evalBound n cfg env len dflt bd) (fun k pt' fr' =>
      ∃ cells, BndSpec len dflt bnd k cells ∧ Post cfg env cx ls fr ls' fr' pt' cells)

theorem exprClaim_lit (n : Nat) (t : IntTy) (k : Int) : ExprClaim n (.lit t k) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr] at hlow
  cases n with
  | zero => simp only [evalExpr]; exact SimG.of_timeout
  | succ n =>
    simp only [evalExpr]
    exact leaf_def (Post.init hrel hpp) hlow hext (by simp) RVal.val (by simp [execPure])

theorem exprClaim_bool (n : Nat) (b : Bool) : ExprClaim n (.bool b) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr] at hlow
  cases n with
  | zero => simp only [evalExpr]; exact SimG.of_timeout
  | succ n =>
    simp only [evalExpr]
    exact leaf_def (Post.init hrel hpp) hlow hext (by simp) RVal.val (by simp [execPure])

theorem exprClaim_bin (n : Nat) (ihe : ∀ e, ExprClaim n e) (op : BinOp) (a b : Expr) (org : OriginId) :
    ExprClaim (n + 1) (.bin op a b org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨x, ls1, h1, y, ls2, h2, ty, ls2', h3, h4⟩ := hlow
  have e3 := intTyOf_eq h3
  subst e3
  have hext2 : ExtT ls2' cx.fn.blocks := hext.of_adv (adv_emitDef h4)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (advB_lowerExpr b _ _ _ _ h2)
  simp only [evalExpr]
  refine SimG.bind (ihe a (by okpf) le ls x ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectInt fun t0 x0 hva => ?_
  subst hva
  refine SimG.bind (ihe b (by okpf) le ls1 y ls2' pt1 cfg env cx fr1 h2 P1.pp hext2 P1.rel) fun vb pt2 fr2 P2 => ?_
  refine SimG.expectInt fun u y0 hvb => ?_
  subst hvb
  refine SimG.expectSameTy fun htu => ?_
  subst htu
  have P12 := P1.comp P2
  have hx : fr2.vals[x]? = some (.val (.int t0 x0)) := P12.has (x, _) (by simp)
  have hy : fr2.vals[y]? = some (.val (.int t0 y0)) := P12.has (y, _) (by simp)
  exact leaf_def P12 h4 hext (by simp) RVal.val (execPure_bin P2.rel.prof hx hy)

/-! ### Straight expressions -/

theorem exprClaim_un (n : Nat) (ihe : ∀ e, ExprClaim n e) (op : UnOp) (a : Expr) (org : OriginId) :
    ExprClaim (n + 1) (.un op a org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨x, ls1, h1, ty, ls1', h3, h4⟩ := hlow
  have e3 := intTyOf_eq h3
  subst e3
  have hext1 : ExtT ls1' cx.fn.blocks := hext.of_adv (adv_emitDef h4)
  simp only [evalExpr]
  refine SimG.bind (ihe a (by okpf) le ls x ls1' pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectInt fun t0 x0 hva => ?_
  subst hva
  have hx : fr1.vals[x]? = some (.val (.int t0 x0)) := P1.has (x, _) (by simp)
  exact leaf_def P1 h4 hext (by simp) RVal.val (execPure_un P1.rel.prof hx)

theorem exprClaim_not (n : Nat) (ihe : ∀ e, ExprClaim n e) (a : Expr) : ExprClaim (n + 1) (.not a) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨x, ls1, h1, h4⟩ := hlow
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitDef h4)
  simp only [evalExpr]
  refine SimG.bind (ihe a (by okpf) le ls x ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectBool fun bb hva => ?_
  subst hva
  have hx : fr1.vals[x]? = some (.val (.bool bb)) := P1.has (x, _) (by simp)
  refine leaf_def P1 h4 hext (by simp) RVal.val ?_
  simp only [execPure, getVal_of hx, Goose.Core.expectBool, pure_bind, bind_assoc]

theorem exprClaim_conv (n : Nat) (ihe : ∀ e, ExprClaim n e) (k : ConvKind) (target : Ty) (a : Expr)
    (org : OriginId) : ExprClaim (n + 1) (.conv k target a org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨x, ls1, h1, src, ls1', h3, h4⟩ := hlow
  have e3 := intTyOf_eq h3
  subst e3
  have hext1 : ExtT ls1' cx.fn.blocks := hext.of_adv (adv_emitDef h4)
  simp only [evalExpr]
  refine SimG.bind (ihe a (by okpf) le ls x ls1' pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectInt fun t0 x0 hva => ?_
  subst hva
  refine SimG.expectIntTy fun d hd => ?_
  subst hd
  have hx : fr1.vals[x]? = some (.val (.int t0 x0)) := P1.has (x, _) (by simp)
  exact leaf_def P1 h4 hext (by simp) RVal.val (execPure_conv P1.rel.prof hx)

/-! ### Places, views and bounds -/

theorem placeClaim_var (n : Nat) (x : VarId) : PlaceClaim n (.var x) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerPlace] at hlow
  cases n with
  | zero => simp only [evalPlace]; exact SimG.of_timeout
  | succ n =>
    simp only [evalPlace]
    refine leaf_def (Post.init hrel hpp) hlow hext (by simp) (fun l => RVal.val (.ref l)) ?_
    simp only [execPure, slotRoot_eq hrel x, bind_assoc, pure_bind]

theorem placeClaim_global (n : Nat) (g : GlobalId) : PlaceClaim n (.global g) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerPlace] at hlow
  cases n with
  | zero => simp only [evalPlace]; exact SimG.of_timeout
  | succ n =>
    simp only [evalPlace]
    exact leaf_def (Post.init hrel hpp) hlow hext (by simp) (fun l => RVal.val (.ref l)) (by simp [execPure])

theorem placeClaim_deref (n : Nat) (ihe : ∀ e, ExprClaim n e) (e : Expr) : PlaceClaim (n + 1) (.deref e) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerPlace] at hlow
  simp only [evalPlace]
  refine SimG.bind (ihe e (by okpf) le ls r ls' pt cfg env cx fr hlow hpp hext hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectRef' fun l hva => ?_
  subst hva
  exact SimG.ret P1

theorem placeClaim_field (n : Nat) (ihp : ∀ p, PlaceClaim n p)
    (owner : Place) (index : Nat) : PlaceClaim (n + 1) (.field owner index) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerPlace, bind_eq] at hlow
  obtain ⟨address, middle, hplace, hfield⟩ := hlow
  have hextMiddle := hext.of_adv (adv_emitDef hfield)
  simp only [evalPlace]
  refine SimG.bind (ihp owner (by okpf) le ls address middle pt cfg env cx fr
    hplace hpp hextMiddle hrel) fun location pt' fr' P => ?_
  have hcell : fr'.vals[address]? = some (.val (.ref location)) := P.has (address, _) (by simp)
  refine leaf_def P hfield hext (by simp) (fun l => RVal.val (.ref l)) ?_
  simp only [execPure, getVal_of hcell, Core.expectRef, pure_bind]

theorem placeClaim_elem (n : Nat) (ihe : ∀ e, ExprClaim n e) (ihv : ∀ v, ViewClaim n v)
    (v : View) (i : Expr) (org : OriginId) : PlaceClaim (n + 1) (.elem v i org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerPlace, bind_eq] at hlow
  obtain ⟨vw, ls1, h1, iv, ls2, h2, h3⟩ := hlow
  have hext2 : ExtT ls2 cx.fn.blocks := hext.of_adv (adv_emitDef h3)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (advB_lowerExpr i _ _ _ _ h2)
  simp only [evalPlace]
  refine SimG.bind (ihv v (by okpf) le ls vw ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun vwv pt1 fr1 P1 => ?_
  refine SimG.bind (ihe i (by okpf) le ls1 iv ls2 pt1 cfg env cx fr1 h2 P1.pp hext2 P1.rel) fun va pt2 fr2 P2 => ?_
  refine SimG.expectInt fun t k hva => ?_
  subst hva
  have P12 := P1.comp P2
  have hv : fr2.vals[vw]? = some (.view vwv) := P12.has (vw, _) (by simp)
  have hi : fr2.vals[iv]? = some (.val (.int t k)) := P12.has (iv, _) (by simp)
  refine leaf_def P12 h3 hext (by simp) (fun l => RVal.val (.ref l)) ?_
  simp only [execPure, getView_of hv, getVal_of hi, Goose.Core.expectInt, bind_assoc, pure_bind]
  by_cases hk : 0 ≤ k ∧ k < (vwv.len : Int)
  · simp [hk]
  · simp [hk, abortAtOrg, abortAt, M.stop, bind_apply]
    rfl

theorem viewClaim_of (n : Nat) (ihp : ∀ p, PlaceClaim n p) (p : Place) : ViewClaim (n + 1) (.of p) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerView, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, h2⟩ := hlow
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitDef h2)
  simp only [evalView]
  refine SimG.bind (ihp p (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun l pt1 fr1 P1 => ?_
  have hc : fr1.vals[rp]? = some (.val (.ref l)) := P1.has (rp, _) (by simp)
  refine leaf_def P1 h2 hext (by simp) RVal.view ?_
  simp only [execPure, getVal_of hc, Goose.Core.expectRef, bind_assoc, pure_bind]

theorem viewClaim_val (n : Nat) (ihe : ∀ e, ExprClaim n e) (e : Expr) : ViewClaim (n + 1) (.val e) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerView, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, h2⟩ := hlow
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitDef h2)
  simp only [evalView]
  refine SimG.bind (ihe e (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectSlice fun l st len hva => ?_
  subst hva
  have hc : fr1.vals[rp]? = some (.val (.slice l st len)) := P1.has (rp, _) (by simp)
  refine leaf_def P1 h2 hext (by simp) RVal.view ?_
  simp only [execPure, getVal_of hc, Goose.Core.expectSlice, bind_assoc, pure_bind]

theorem evalBnd_of_spec {fr : Frame} {len : Nat} {dflt : Int} {bnd : Bnd} {k : Int}
    {cells : List (ValueId × RVal)} (hs : BndSpec len dflt bnd k cells)
    (hc : ∀ p ∈ cells, fr.vals[p.1]? = some p.2) : evalBnd fr len dflt bnd = pure k := by
  cases bnd with
  | omitted => obtain ⟨rfl, -⟩ := hs; rfl
  | val v =>
    obtain ⟨t, rfl⟩ := hs
    have := hc (v, .val (.int t k)) (by simp)
    simp only [evalBnd, getVal_of this, Goose.Core.expectInt, pure_bind]
  | fromEnd v =>
    obtain ⟨t, kk, rfl, rfl⟩ := hs
    have := hc (v, .val (.int t kk)) (by simp)
    simp only [evalBnd, getVal_of this, Goose.Core.expectInt, pure_bind]

theorem boundClaim_omitted (n : Nat) : BoundClaim n .omitted := by
  intro hok le ls bnd ls' pt cfg env cx fr len dflt hlow hpp hext hrel
  simp only [lowerBound, pure_run] at hlow
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
  cases n with
  | zero => simp only [evalBound]; exact SimG.of_timeout
  | succ n =>
    simp only [evalBound]
    exact SimG.ret ⟨[], ⟨rfl, rfl⟩, Post.init hrel hpp⟩

theorem boundClaim_expr (n : Nat) (ihe : ∀ e, ExprClaim n e) (e : Expr) : BoundClaim (n + 1) (.expr e) := by
  intro hok le ls bnd ls' pt cfg env cx fr len dflt hlow hpp hext hrel
  simp only [lowerBound, bind_eq] at hlow
  obtain ⟨x, ls1, h1, h2⟩ := hlow
  rw [pure_run] at h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
  simp only [evalBound]
  refine SimG.bind (ihe e (by okpf) le ls x ls1 pt cfg env cx fr h1 hpp hext hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectInt fun t k hva => ?_
  subst hva
  exact SimG.ret ⟨_, ⟨t, rfl⟩, P1⟩

theorem boundClaim_fromEnd (n : Nat) (ihe : ∀ e, ExprClaim n e) (e : Expr) :
    BoundClaim (n + 1) (.fromEnd e) := by
  intro hok le ls bnd ls' pt cfg env cx fr len dflt hlow hpp hext hrel
  simp only [lowerBound, bind_eq] at hlow
  obtain ⟨x, ls1, h1, h2⟩ := hlow
  rw [pure_run] at h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
  simp only [evalBound]
  refine SimG.bind (ihe e (by okpf) le ls x ls1 pt cfg env cx fr h1 hpp hext hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectInt fun t k hva => ?_
  subst hva
  exact SimG.ret ⟨_, ⟨t, k, rfl, rfl⟩, P1⟩

/-! ### More straight expressions -/

theorem exprClaim_read (n : Nat) (ihp : ∀ p, PlaceClaim n p) (p : Place) : ExprClaim (n + 1) (.read p) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, h2⟩ := hlow
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitDef h2)
  simp only [evalExpr]
  refine SimG.bind (ihp p (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun l pt1 fr1 P1 => ?_
  have hc : fr1.vals[rp]? = some (.val (.ref l)) := P1.has (rp, _) (by simp)
  refine leaf_def P1 h2 hext (by simp) RVal.val ?_
  simp only [execPure, getVal_of hc, Goose.Core.expectRef, bind_assoc, pure_bind]

theorem exprClaim_ref (n : Nat) (ihp : ∀ p, PlaceClaim n p) (m : Mutability) (p : Place) :
    ExprClaim (n + 1) (.ref m p) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, h2⟩ := hlow
  rcases freezeTo_cases h2 with ⟨hr, hls⟩ | ⟨hf⟩
  · subst hr; subst hls
    simp only [evalExpr]
    refine SimG.bind (ihp p (by okpf) le ls r ls' pt cfg env cx fr h1 hpp hext hrel) fun l pt1 fr1 P1 => ?_
    exact SimG.ret P1
  · have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitDef hf)
    simp only [evalExpr]
    refine SimG.bind (ihp p (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun l pt1 fr1 P1 => ?_
    have hc : fr1.vals[rp]? = some (.val (.ref l)) := P1.has (rp, _) (by simp)
    refine SimG.mono (leaf_def P1 hf hext (by simp) RVal.val ?_) fun a pt' fr' h => h
    simp only [execPure, getVal_of hc, Goose.Core.expectRef, bind_assoc, pure_bind]

theorem exprClaim_len (n : Nat) (ihv : ∀ v, ViewClaim n v) (v : View) : ExprClaim (n + 1) (.len v) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨rv, ls1, h1, h2⟩ := hlow
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitDef h2)
  simp only [evalExpr]
  refine SimG.bind (ihv v (by okpf) le ls rv ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun vw pt1 fr1 P1 => ?_
  have hc : fr1.vals[rv]? = some (.view vw) := P1.has (rv, _) (by simp)
  refine leaf_def P1 h2 hext (by simp) RVal.val ?_
  simp only [execPure, getView_of hc, bind_assoc, pure_bind]

theorem exprClaim_slice (n : Nat) (ihv : ∀ v, ViewClaim n v) (ihb : ∀ b, BoundClaim n b)
    (m : Mutability) (v : View) (lo hi : Bound) (org : OriginId) :
    ExprClaim (n + 1) (.slice m v lo hi org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨rv, ls1, h1, bl, ls2, h2, bh, ls3, h3, h4⟩ := hlow
  have hext3 : ExtT ls3 cx.fn.blocks := hext.of_adv (adv_emitDef h4)
  have hext2 : ExtT ls2 cx.fn.blocks := hext3.of_adv (advB_lowerBound hi _ _ _ _ h3)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (advB_lowerBound lo _ _ _ _ h2)
  simp only [evalExpr]
  refine SimG.bind (ihv v (by okpf) le ls rv ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun vw pt1 fr1 P1 => ?_
  refine SimG.bind (ihb lo (by okpf) le ls1 bl ls2 pt1 cfg env cx fr1 vw.len 0 h2 P1.pp hext2 P1.rel)
    fun lo' pt2 fr2 ⟨cl, hsl, P2⟩ => ?_
  refine SimG.bind (ihb hi (by okpf) le ls2 bh ls3 pt2 cfg env cx fr2 vw.len vw.len h3 P2.pp hext3 P2.rel)
    fun hi' pt3 fr3 ⟨ch, hsh, P3⟩ => ?_
  have P123 := (P1.comp P2).comp P3
  have hv : fr3.vals[rv]? = some (.view vw) := P123.has (rv, _) (by simp)
  have hcl : ∀ p ∈ cl, fr3.vals[p.1]? = some p.2 := fun p hp => by
    have := P123.has p (by simp [hp]); exact this
  have hch : ∀ p ∈ ch, fr3.vals[p.1]? = some p.2 := fun p hp => by
    have := P123.has p (by simp [hp]); exact this
  have e1 := evalBnd_of_spec hsl hcl
  have e2 := evalBnd_of_spec hsh hch
  refine leaf_def P123 h4 hext (by simp) RVal.val ?_
  simp only [execPure, getView_of hv, e1, e2, bind_assoc, pure_bind]
  by_cases hk : 0 ≤ lo' ∧ lo' ≤ hi' ∧ hi' ≤ (vw.len : Int)
  · simp [hk]
  · simp [hk, abortAtOrg, abortAt, M.stop, bind_apply]
    rfl

theorem exprClaim_cmp (n : Nat) (ihe : ∀ e, ExprClaim n e) (op : CmpOp) (a b : Expr) :
    ExprClaim (n + 1) (.cmp op a b) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨x, ls1, h1, y, ls2, h2, t, ls2', h3, h4⟩ := hlow
  have e3 := valTy_eq h3
  subst e3
  have key : ∃ op', emitDef op' le ls2' = (r, ls') ∧
      (op' = .boolCmp op x y ∨ ∃ t0, op' = .cmp op t0 x y) := by
    cases t with
    | data t =>
      cases t <;> first
        | exact ⟨_, h4, Or.inr ⟨_, rfl⟩⟩
        | exact ⟨_, h4, Or.inl rfl⟩
    | view _ _ => exact ⟨_, h4, Or.inl rfl⟩
  obtain ⟨op', h5, hop⟩ := key
  have hext2 : ExtT ls2' cx.fn.blocks := hext.of_adv (adv_emitDef h5)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (advB_lowerExpr b _ _ _ _ h2)
  simp only [evalExpr]
  refine SimG.bind (ihe a (by okpf) le ls x ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.bind (ihe b (by okpf) le ls1 y ls2' pt1 cfg env cx fr1 h2 P1.pp hext2 P1.rel) fun vb pt2 fr2 P2 => ?_
  have P12 := P1.comp P2
  have hx : fr2.vals[x]? = some (.val va) := P12.has (x, _) (by simp)
  have hy : fr2.vals[y]? = some (.val vb) := P12.has (y, _) (by simp)
  have hnc : ∀ f a o, op' ≠ .call f a o := by
    rcases hop with rfl | ⟨t0, rfl⟩ <;> simp
  refine leaf_def P12 h5 hext hnc RVal.val ?_
  rcases hop with rfl | ⟨t0, rfl⟩
  · exact (execPure_cmp hx hy).2
  · exact (execPure_cmp hx hy).1 t0

theorem exprClaim_push (n : Nat) (ihe : ∀ e, ExprClaim n e) (ihp : ∀ p, PlaceClaim n p) (owner : Place)
    (a : Expr) (org : Option OriginId) : ExprClaim (n + 1) (.push owner a org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, v, ls2, h2, h3⟩ := hlow
  have hext2 : ExtT ls2 cx.fn.blocks := hext.of_adv (adv_emitDef h3)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (advB_lowerExpr a _ _ _ _ h2)
  simp only [evalExpr]
  refine SimG.bind (ihp owner (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun l pt1 fr1 P1 => ?_
  refine SimG.bind (ihe a (by okpf) le ls1 v ls2 pt1 cfg env cx fr1 h2 P1.pp hext2 P1.rel) fun va pt2 fr2 P2 => ?_
  have P12 := P1.comp P2
  have hl : fr2.vals[rp]? = some (.val (.ref l)) := P12.has (rp, _) (by simp)
  have hv : fr2.vals[v]? = some (.val va) := P12.has (v, _) (by simp)
  refine leaf_def P12 h3 hext (by simp) RVal.val ?_
  cases org with
  | none => simp [execPure, getVal_of hl, getVal_of hv, Goose.Core.expectRef]
  | some origin =>
    simp [execPure, getVal_of hl, getVal_of hv, Goose.Core.expectRef, bind_assoc, pure_bind,
      checkCapacityAtOrg, Goose.Core.checkedAppendLoc, checkAppendCapacity, abortAtOrg, abortAt]
    rfl

theorem exprClaim_pop (n : Nat) (ihp : ∀ p, PlaceClaim n p) (owner : Place)
    (org : OriginId) : ExprClaim (n + 1) (.pop owner org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, h2⟩ := hlow
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitDef h2)
  simp only [evalExpr]
  refine SimG.bind (ihp owner (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun l pt1 fr1 P1 => ?_
  have hl : fr1.vals[rp]? = some (.val (.ref l)) := P1.has (rp, _) (by simp)
  refine leaf_def P1 h2 hext (by simp) RVal.val ?_
  simp [execPure, getVal_of hl, Goose.Core.expectRef, abortAtOrg, abortAt]
  funext s
  cases hlen : lengthLoc l s with
  | stop err state => simp [bind_apply, hlen]
  | ok len state =>
    by_cases hzero : len = 0
    · simp [bind_apply, hlen, hzero, Functor.map, M.stop, M.bind', M.pure']
    · simp only [bind_apply, hlen, if_neg hzero]
      cases hread : readLoc { root := l.root, path := l.path ++ [len - 1] } state with
      | stop err state' => simp [bind_apply, hread]
      | ok value state' =>
        cases htruncate : truncateLoc l (len - 1) state' with
        | stop err state'' => simp [bind_apply, hread, htruncate]
        | ok _ state'' => simp [bind_apply, hread, htruncate]

/-! ### Lists of expressions -/

/-- The cells that hold the values of a list of lowered expressions. -/
def ExprsClaim (n : Nat) (es : List Expr) : Prop :=
  exprsOk es = true → ∀ (le : LEnv) (ls : LS) (rs : List ValueId) (ls' : LS) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : Frame), lowerExprs es le ls = (rs, ls') → ls.pp = some pt → ExtT ls' cx.fn.blocks →
    Rel cfg env cx fr ls →
    SimG cx pt fr (mapList (evalExpr n cfg env) es) (fun vs pt' fr' =>
      rs.length = vs.length ∧ Post cfg env cx ls fr ls' fr' pt' (cellsOf rs vs))

theorem exprsClaim (n : Nat) (ihe : ∀ e, ExprClaim n e) : ∀ es, ExprsClaim n es
  | [] => by
    intro hok le ls rs ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [lowerExprs, pure_run] at hlow
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
    simp only [mapList]
    exact SimG.ret ⟨rfl, by simpa [cellsOf] using Post.init hrel hpp⟩
  | e :: es => by
    intro hok le ls rs ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [lowerExprs, bind_eq] at hlow
    obtain ⟨v, ls1, h1, vs, ls2, h2, h3⟩ := hlow
    rw [pure_run] at h3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
    have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (advB_lowerExprs es _ _ _ _ h2)
    simp only [mapList]
    refine SimG.bind (ihe e (by okpf) le ls v ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
    refine SimG.bind (exprsClaim n ihe es (by okpf) le ls1 vs ls2 pt1 cfg env cx fr1 h2 P1.pp hext P1.rel)
      fun vas pt2 fr2 ⟨hlen, P2⟩ => ?_
    exact SimG.ret ⟨by simp [hlen], by simpa [cellsOf] using P1.comp P2⟩

theorem exprClaim_arrLit (n : Nat) (ihes : ∀ es, ExprsClaim n es) (t : Ty) (es : List Expr) :
    ExprClaim (n + 1) (.arrLit t es) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨rs, ls1, h1, h2⟩ := hlow
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitDef h2)
  simp only [evalExpr]
  refine SimG.bind (ihes es (by okpf) le ls rs ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun vs pt1 fr1 ⟨hlen, P1⟩ => ?_
  have hc := mapList_getVal_cells (fr := fr1) hlen (fun p hp => P1.has p hp)
  refine leaf_def P1 h2 hext (by simp) RVal.val ?_
  simp only [execPure, hc, pure_bind, bind_assoc]

theorem exprClaim_structLit (n : Nat) (ihes : ∀ es, ExprsClaim n es) (ty : Ty) (es : List Expr) :
    ExprClaim (n + 1) (.structLit ty es) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨ids, middle, hexprs, hrecord⟩ := hlow
  have hextMiddle := hext.of_adv (adv_emitDef hrecord)
  cases ty with
  | structT id args =>
    simp only [evalExpr]
    refine SimG.bind (ihes es (by okpf) le ls ids middle pt cfg env cx fr
      hexprs hpp hextMiddle hrel) fun values pt' fr' ⟨hlen, P⟩ => ?_
    have hread := mapList_getVal_cells (fr := fr') hlen P.has
    refine leaf_def P hrecord hext (by simp) RVal.val ?_
    simp only [execPure, hread, pure_bind, bind_assoc]
  | _ =>
    simp only [evalExpr]
    exact SimG.of_fault

theorem exprClaim_fill (n : Nat) (ihe : ∀ e, ExprClaim n e) (t : Ty) (a : Expr) :
    ExprClaim (n + 1) (.fill t a) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨v, ls1, h1, h2⟩ := hlow
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitDef h2)
  cases t with
  | arr e k =>
    simp only [evalExpr, Goose.Core.expectFixedCount, pure_bind]
    refine SimG.bind (ihe a (by okpf) le ls v ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
    have hc : fr1.vals[v]? = some (.val va) := P1.has (v, _) (by simp)
    refine leaf_def P1 h2 hext (by simp) RVal.val ?_
    simp only [execPure, getVal_of hc, Goose.Core.expectFixedCount, pure_bind, bind_assoc]
  | _ =>
    simp only [evalExpr, Goose.Core.expectFixedCount]
    exact SimG.of_fault_bind fun s => ⟨_, s, rfl⟩

/-! ### Short-circuit operators -/

/-- What Core does after the left operand of `and`/`or` yielded `β`. -/
def scK : Bool → Bool → M Val → M Val
  | true, β, cb =>
    if β = true then (cb >>= fun vb => Goose.Core.expectBool vb >>= fun bb => pure (Val.bool bb))
    else pure (Val.bool false)
  | false, β, cb =>
    if β = true then pure (Val.bool true)
    else (cb >>= fun vb => Goose.Core.expectBool vb >>= fun bb => pure (Val.bool bb))

theorem sc_sim {isAnd : Bool} {x : ValueId} {rhs : B ValueId} {le : LEnv} {ls1 : LS} {r : ValueId}
    {ls' : LS} {pt1 : Pt} {cfg : Cfg} {env : Env} {cx : FnCtx} {fr1 : Frame} {cb : M Val} {β : Bool}
    (hs : shortCircuit isAnd x rhs le ls1 = (r, ls')) (hpp : ls1.pp = some pt1)
    (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr1 ls1)
    (hx : fr1.vals[x]? = some (.val (.bool β))) (hadv : AdvB rhs)
    (hrhs : ∀ (ls_d : LS) (y : ValueId) (ls_e : LS) (pt_d : Pt), rhs le ls_d = (y, ls_e) →
      ls_d.pp = some pt_d → ExtT ls_e cx.fn.blocks → Rel cfg env cx fr1 ls_d →
      SimG cx pt_d fr1 cb (fun vb pt' fr' => Post cfg env cx ls_d fr1 ls_e fr' pt' [(y, .val vb)])) :
    SimG cx pt1 fr1 (scK isAnd β cb) (fun v pt' fr' => Post cfg env cx ls1 fr1 ls' fr' pt' [(r, .val v)]) := by
  obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some hpp
  unfold shortCircuit at hs
  rw [whenLive_some _ _ _ hc1] at hs
  simp only [bind_eq] at hs
  obtain ⟨⟨rb, jb, p⟩, ls_c, h1, u2, ls_d, h2, y, ls_e, h3, u4, ls_f, h4, u5, ls_g, h5, hpure⟩ := hs
  rw [pure_run] at hpure
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpure
  have a_rhs : ls_d.Adv ls_e := hadv _ _ _ _ h3
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
  subst hrb hjb hpv
  -- the new blocks in the finished function
  obtain ⟨Trb, hTrb, hTrbp⟩ := hext_c.params hbrb
  obtain ⟨Tjb, hTjb, hTjbp⟩ := hext_c.params hbjb
  have hdb : ls_d.blocks = ls_c.blocks := by rw [hd]
  have hdpp : ls_d.pp = some (ls1.blocks.size, 0) := by
    rw [hd]; exact LS.pp_cur hbrb
  have hstd : ls_d.stack = ls1.stack := by rw [hd]; exact hstc
  have hrel_d : Rel cfg env cx fr1 ls_d := hrel.stack_eq hstd
  have hvd : ls_d.vals.size = ls1.vals.size + 1 := by rw [hd]; exact hvc
  -- the join block is untouched by the right operand and its terminator
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
  have hjoin : ∀ (vb : Val) (pt_e : Pt) (fr_e : Frame),
      Post cfg env cx ls_d fr1 ls_e fr_e pt_e [(y, .val vb)] → ∀ bb, vb = .bool bb →
      SimG cx pt_e fr_e (pure (Val.bool bb) : M Val) (fun v pt' fr' =>
        Post cfg env cx ls1 fr1 ls_g fr' pt' [(ls1.vals.size, .val v)]) := by
    intro vb pt_e fr_e P bb hvb
    subst hvb
    obtain ⟨-, -, -, hinst_e⟩ := emitTerm_facts h4 P.pp hext_f
    have hy : fr_e.vals[y]? = some (.val (.bool bb)) := P.has (y, _) (by simp)
    have g2 := goes_br1 (cx := cx) (pt := pt_e) (fr := fr_e) hinst_e hTjb' hTjbp hy
    refine SimG.goes g2 (SimG.ret ?_)
    have hsame : Same ls1.vals.size fr1 fr_e := P.same.mono (by nat_omega)
    have hrel_e : Rel cfg env cx fr_e ls1 := P.rel.stack_eq (by rw [a_rhs.stack, hstd])
    exact Post.join hsame hrel_e (Nat.le_refl _) hlt hmono hst_g hpp_g
  have hshort : ∀ b' : Bool, Goes cx pt1 fr1 (ls1.blocks.size + 1, 0)
      (fr1.set ls1.vals.size (.val (.bool b'))) →
      SimG cx pt1 fr1 (pure (Val.bool b') : M Val) (fun v pt' fr' =>
        Post cfg env cx ls1 fr1 ls_g fr' pt' [(ls1.vals.size, .val v)]) := by
    intro b' hg'
    refine SimG.goes hg' (SimG.ret ?_)
    exact Post.join (Same.refl _ _) hrel (Nat.le_refl _) hlt hmono hst_g hpp_g
  have hrhs' := hrhs ls_d y ls_e (ls1.blocks.size, 0) h3 hdpp hext_e hrel_d
  cases isAnd <;> cases β
  · -- or, false: the right operand
    have hi : instAt cx.fn pt1 = some (.term (.condbr x (ls1.blocks.size + 1) [x] ls1.blocks.size [])) := hinst
    refine SimG.goes (goes_condbr_else0 hi hx hTrb' hTrbp rfl) ?_
    exact SimG.bind hrhs' fun vb pt_e fr_e P => SimG.expectBool fun bb hvb => hjoin vb pt_e fr_e P bb hvb
  · -- or, true: the join directly
    have hi : instAt cx.fn pt1 = some (.term (.condbr x (ls1.blocks.size + 1) [x] ls1.blocks.size [])) := hinst
    exact hshort true (goes_condbr_then1 hi hx hTjb' hTjbp rfl hx)
  · -- and, false: the join directly
    have hi : instAt cx.fn pt1 = some (.term (.condbr x ls1.blocks.size [] (ls1.blocks.size + 1) [x])) := hinst
    exact hshort false (goes_condbr_else1 hi hx hTjb' hTjbp rfl hx)
  · -- and, true: the right operand
    have hi : instAt cx.fn pt1 = some (.term (.condbr x ls1.blocks.size [] (ls1.blocks.size + 1) [x])) := hinst
    refine SimG.goes (goes_condbr_then0 hi hx hTrb' hTrbp rfl) ?_
    exact SimG.bind hrhs' fun vb pt_e fr_e P => SimG.expectBool fun bb hvb => hjoin vb pt_e fr_e P bb hvb

theorem exprClaim_and (n : Nat) (ihe : ∀ e, ExprClaim n e) (a b : Expr) : ExprClaim (n + 1) (.and a b) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨x, ls1, h1, hs⟩ := hlow
  have hadv := advB_lowerExpr b
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (advB_shortCircuit true x hadv _ _ _ _ hs)
  simp only [evalExpr]
  refine SimG.bind (ihe a (by okpf) le ls x ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectBool fun β hva => ?_
  subst hva
  have hx : fr1.vals[x]? = some (.val (.bool β)) := P1.has (x, _) (by simp)
  refine SimG.mono (sc_sim (cb := evalExpr n cfg env b) hs P1.pp hext P1.rel hx hadv ?_) fun v pt' fr' P => ?_
  · intro ls_d y ls_e pt_d h3 hpp_d hext_e hrel_d
    exact ihe b (by okpf) le ls_d y ls_e pt_d cfg env cx fr1 h3 hpp_d hext_e hrel_d
  · exact (P1.comp P).sub (by simp)

theorem exprClaim_or (n : Nat) (ihe : ∀ e, ExprClaim n e) (a b : Expr) : ExprClaim (n + 1) (.or a b) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨x, ls1, h1, hs⟩ := hlow
  have hadv := advB_lowerExpr b
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (advB_shortCircuit false x hadv _ _ _ _ hs)
  simp only [evalExpr]
  refine SimG.bind (ihe a (by okpf) le ls x ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectBool fun β hva => ?_
  subst hva
  have hx : fr1.vals[x]? = some (.val (.bool β)) := P1.has (x, _) (by simp)
  refine SimG.mono (sc_sim (cb := evalExpr n cfg env b) hs P1.pp hext P1.rel hx hadv ?_) fun v pt' fr' P => ?_
  · intro ls_d y ls_e pt_d h3 hpp_d hext_e hrel_d
    exact ihe b (by okpf) le ls_d y ls_e pt_d cfg env cx fr1 h3 hpp_d hext_e hrel_d
  · exact (P1.comp P).sub (by simp)

/-! ### Statements -/

def StmtClaim (n : Nat) (lc : Option LoopCtx) (s : Stmt) : Prop :=
  stmtOk s = true → ∀ (le : LEnv) (ls : LS) (r : Unit) (ls' : LS) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : Frame), lowerStmt lc s le ls = (r, ls') → ls.pp = some pt → ExtT ls' cx.fn.blocks →
    Rel cfg env cx fr ls →
    SimG cx pt fr (execStmt n cfg env s) (fun flow pt' fr' =>
      flow = Flow.normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' [])

theorem stmtClaim_let (n : Nat) (lc : Option LoopCtx) (ihe : ∀ e, ExprClaim n e) (x : VarId) (e : Expr) (org : OriginId) :
    StmtClaim (n + 1) lc (.letS x e org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨v, ls1, h1, h2⟩ := hlow
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitEffect h2)
  simp only [execStmt]
  refine SimG.bind (ihe e (by okpf) le ls v ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  have hc : fr1.vals[v]? = some (.val va) := P1.has (v, _) (by simp)
  have hx : execEff cx.fn fr1 (.slotInit x v (some org)) =
      (rootOf env x >>= fun rt => bindRoot rt va) >>= fun _ => pure fr1 := by
    simp only [execEff, slotRoot_eq P1.rel, getVal_of hc, bind_assoc, pure_bind]
  exact leaf_eff P1 h2 hext (Flow.normal .unit) (by simp only [bind_assoc]) hx

theorem stmtClaim_assign (n : Nat) (lc : Option LoopCtx) (ihe : ∀ e, ExprClaim n e) (ihp : ∀ p, PlaceClaim n p) (p : Place)
    (e : Expr) (org : OriginId) : StmtClaim (n + 1) lc (.assign p e org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, v, ls2, h2, h3⟩ := hlow
  have hext2 : ExtT ls2 cx.fn.blocks := hext.of_adv (adv_emitEffect h3)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (advB_lowerExpr e _ _ _ _ h2)
  simp only [execStmt]
  refine SimG.bind (ihp p (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun l pt1 fr1 P1 => ?_
  refine SimG.bind (ihe e (by okpf) le ls1 v ls2 pt1 cfg env cx fr1 h2 P1.pp hext2 P1.rel) fun va pt2 fr2 P2 => ?_
  have P12 := P1.comp P2
  have hl : fr2.vals[rp]? = some (.val (.ref l)) := P12.has (rp, _) (by simp)
  have hv : fr2.vals[v]? = some (.val va) := P12.has (v, _) (by simp)
  have hx : execEff cx.fn fr2 (.store rp v (some org)) = writeLoc l va >>= fun _ => pure fr2 := by
    simp only [execEff, getVal_of hl, getVal_of hv, Goose.Core.expectRef, bind_assoc, pure_bind]
  exact leaf_eff P12 h3 hext (Flow.normal .unit) rfl hx

theorem stmtClaim_rebind (n : Nat) (lc : Option LoopCtx) (ihe : ∀ e, ExprClaim n e) (x : VarId) (e : Expr) (org : OriginId) :
    StmtClaim (n + 1) lc (.rebind x e org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨v, ls1, h1, rs, ls2, h2, h3⟩ := hlow
  have hext2 : ExtT ls2 cx.fn.blocks := hext.of_adv (adv_emitEffect h3)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (adv_emitDef h2)
  simp only [execStmt]
  refine SimG.bind (ihe e (by okpf) le ls v ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  rw [show (rootOf env x >>= fun rt => writeLoc ⟨rt, []⟩ va >>= fun _ => pure (Flow.normal Val.unit)) =
    ((rootOf env x >>= fun rt => pure (Loc.mk rt [])) >>= fun l => writeLoc l va >>= fun _ =>
      pure (Flow.normal Val.unit)) by simp [bind_assoc]]
  refine SimG.bind (leaf_def_keep P1 h2 hext2 (by simp) (fun l => RVal.val (.ref l)) ?_)
    fun l pt2 fr2 P2 => ?_
  · simp only [execPure, slotRoot_eq P1.rel, bind_assoc, pure_bind]
  have hl : fr2.vals[rs]? = some (.val (.ref l)) := P2.has (rs, _) (by simp)
  have hv : fr2.vals[v]? = some (.val va) := P2.has (v, _) (by simp)
  have hx : execEff cx.fn fr2 (.store rs v (some org)) = writeLoc l va >>= fun _ => pure fr2 := by
    simp only [execEff, getVal_of hl, getVal_of hv, Goose.Core.expectRef, bind_assoc, pure_bind]
  exact leaf_eff P2 h3 hext (Flow.normal .unit) rfl hx

theorem stmtClaim_assignOp (n : Nat) (lc : Option LoopCtx) (ihe : ∀ e, ExprClaim n e) (ihp : ∀ p, PlaceClaim n p)
    (op : BinOp) (p : Place) (e : Expr) (org : OriginId) : StmtClaim (n + 1) lc (.assignOp op p e org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, old, ls2, h2, rhs, ls3, h3, ty, ls3', h4, res, ls4, h5, h6⟩ := hlow
  have e4 := intTyOf_eq h4
  subst e4
  have hext4 : ExtT ls4 cx.fn.blocks := hext.of_adv (adv_emitEffect h6)
  have hext3 : ExtT ls3' cx.fn.blocks := hext4.of_adv (adv_emitDef h5)
  have hext2 : ExtT ls2 cx.fn.blocks := hext3.of_adv (advB_lowerExpr e _ _ _ _ h3)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (adv_emitDef h2)
  simp only [execStmt]
  refine SimG.bind (ihp p (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun l pt1 fr1 P1 => ?_
  have hl1 : fr1.vals[rp]? = some (.val (.ref l)) := P1.has (rp, _) (by simp)
  refine SimG.bind (leaf_def_keep P1 h2 hext2 (by simp) RVal.val (c := readLoc l) ?_)
    fun va pt2 fr2 P2 => ?_
  · simp only [execPure, getVal_of hl1, Goose.Core.expectRef, bind_assoc, pure_bind]
  refine SimG.expectInt fun t x hva => ?_
  subst hva
  refine SimG.bind (ihe e (by okpf) le ls2 rhs ls3' pt2 cfg env cx fr2 h3 P2.pp hext3 P2.rel) fun vb pt3 fr3 P3 => ?_
  refine SimG.expectInt fun u y hvb => ?_
  subst hvb
  refine SimG.expectSameTy fun htu => ?_
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
    exact SimG.of_stops (c := (abortAt (AbortKind.ofNum k) org : M Val))
      (c' := (abortAt (AbortKind.ofNum k) org : M Flow))
      (fun s b s1 => by simp [abortAt, M.stop])
      (fun s e s1 h => by simp only [abortAt, M.stop, Res.stop.injEq] at h ⊢; exact h) key
  | ok rr =>
    dsimp only at hexec ⊢
    show SimG cx pt3 fr3 (pure (Val.int t rr) >>= fun res => writeLoc l res >>= fun _ =>
      pure (Flow.normal Val.unit)) _
    refine SimG.bind (leaf_def_keep P23 h5 hext4 (by simp) RVal.val hexec) fun vr pt4 fr4 P4 => ?_
    have hrp : fr4.vals[rp]? = some (.val (.ref l)) := P4.has (rp, _) (by simp)
    have hrs : fr4.vals[res]? = some (.val vr) := P4.has (res, _) (by simp)
    have hx' : execEff cx.fn fr4 (.store rp res (some org)) = writeLoc l vr >>= fun _ => pure fr4 := by
      simp only [execEff, getVal_of hrp, getVal_of hrs, Goose.Core.expectRef, bind_assoc, pure_bind]
    exact leaf_eff P4 h6 hext (Flow.normal .unit) rfl hx'

theorem stmtClaim_expr (n : Nat) (lc : Option LoopCtx) (ihe : ∀ e, ExprClaim n e) (e : Expr) (org : OriginId) :
    StmtClaim (n + 1) lc (.expr e org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨v, ls1, h1, h2⟩ := hlow
  rw [pure_run] at h2
  obtain ⟨-, rfl⟩ := Prod.mk.inj h2
  simp only [execStmt]
  refine SimG.bind (ihe e (by okpf) le ls v ls1 pt cfg env cx fr h1 hpp hext hrel) fun va pt1 fr1 P1 => ?_
  exact SimG.ret ⟨rfl, P1.sub (cells' := []) (by simp)⟩

theorem stmtClaim_popN (n : Nat) (lc : Option LoopCtx) (ihp : ∀ p, PlaceClaim n p)
    (ihe : ∀ e, ExprClaim n e) (owner : Place) (count : Expr) (org : OriginId) :
    StmtClaim (n + 1) lc (.popN owner count org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, v, ls2, h2, h3⟩ := hlow
  have hext2 : ExtT ls2 cx.fn.blocks := hext.of_adv (adv_emitEffect h3)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (advB_lowerExpr count _ _ _ _ h2)
  simp only [execStmt]
  refine SimG.bind (ihp owner (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun l pt1 fr1 P1 => ?_
  refine SimG.bind (ihe count (by okpf) le ls1 v ls2 pt1 cfg env cx fr1 h2 P1.pp hext2 P1.rel) fun va pt2 fr2 P2 => ?_
  refine SimG.expectInt fun t k hva => ?_
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
  refine leaf_eff P12 h3 hext (Flow.normal .unit) ?_ hx
  funext s
  cases hlen : lengthLoc l s with
  | stop err state => simp [action, bind_apply, pure_apply, hlen, M.bind', M.pure', Functor.map]
  | ok len state =>
    by_cases hbad : k < 0 ∨ (len : Int) < k
    · simp [action, bind_apply, pure_apply, hlen, hbad, abortAt, M.stop, M.instMonad, M.bind', M.pure', Functor.map]
    · cases htruncate : truncateLoc l (len - k.toNat) state <;>
        simp [action, bind_apply, pure_apply, hlen, hbad, htruncate, M.instMonad, M.bind', M.pure', Functor.map]

theorem stmtClaim_resize (n : Nat) (lc : Option LoopCtx) (ihp : ∀ p, PlaceClaim n p)
    (ihe : ∀ e, ExprClaim n e) (owner : Place) (size : Expr) (fill : Option Expr)
    (org : OriginId) : StmtClaim (n + 1) lc (.resize owner size fill org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  cases fill with
  | none =>
    simp only [lowerStmt, bind_eq] at hlow
    obtain ⟨rp, ls1, h1, v, ls2, h2, opt, ls2', hopt, h3⟩ := hlow
    rw [pure_run] at hopt
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hopt
    have hext2 : ExtT ls2 cx.fn.blocks := hext.of_adv (adv_emitEffect h3)
    have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (advB_lowerExpr size _ _ _ _ h2)
    simp only [execStmt]
    refine SimG.bind (ihp owner (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun l pt1 fr1 P1 => ?_
    refine SimG.bind (ihe size (by okpf) le ls1 v ls2 pt1 cfg env cx fr1 h2 P1.pp hext2 P1.rel) fun va pt2 fr2 P2 => ?_
    refine SimG.expectInt fun t k hva => ?_
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
    apply leaf_eff P12 h3 hext (Flow.normal .unit) ?_ hx
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
    refine SimG.bind (ihp owner (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun l pt1 fr1 P1 => ?_
    refine SimG.bind (ihe size (by okpf) le ls1 v ls2 pt1 cfg env cx fr1 h2 P1.pp hext2 P1.rel) fun sizeVal pt2 fr2 P2 => ?_
    refine SimG.expectInt fun t k hsize => ?_
    subst hsize
    refine SimG.bind (ihe fillExpr (by okpf) le ls2 fv ls3 pt2 cfg env cx fr2 h3 P2.pp hext3 P2.rel) fun fillVal pt3 fr3 P3 => ?_
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
    apply leaf_eff P13 h4 hext (Flow.normal .unit) ?_ hx
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

theorem stmtClaim_clear (n : Nat) (lc : Option LoopCtx) (ihp : ∀ p, PlaceClaim n p)
    (owner : Place) (org : OriginId) : StmtClaim (n + 1) lc (.clear owner org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, h2⟩ := hlow
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitEffect h2)
  simp only [execStmt]
  refine SimG.bind (ihp owner (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun l pt1 fr1 P1 => ?_
  have hl : fr1.vals[rp]? = some (.val (.ref l)) := P1.has (rp, _) (by simp)
  have hx : execEff cx.fn fr1 (.clear rp (some org)) = truncateLoc l 0 >>= fun _ => pure fr1 := by
    simp only [execEff, getVal_of hl, Goose.Core.expectRef, bind_assoc, pure_bind]
  exact leaf_eff P1 h2 hext (Flow.normal .unit) (by simp only [bind_assoc]) hx

theorem stmtClaim_assignWhole (n : Nat) (lc : Option LoopCtx) (ihp : ∀ p, PlaceClaim n p)
    (ihe : ∀ e, ExprClaim n e) (owner : Place) (replacement : Expr) (org : OriginId) :
    StmtClaim (n + 1) lc (.assignWhole owner replacement org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, u, ls2, h2, run, ls3, h3, h4⟩ := hlow
  cases u
  have hext3 : ExtT ls3 cx.fn.blocks := hext.of_adv (adv_emitEffect h4)
  have hext2 : ExtT ls2 cx.fn.blocks := hext3.of_adv (advB_lowerExpr replacement _ _ _ _ h3)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (adv_emitEffect h2)
  simp only [execStmt]
  refine SimG.bind (ihp owner (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun l pt1 fr1 P1 => ?_
  obtain ⟨Pclear, hi⟩ := Post.eff_leaf P1 h2 hext2
  have hrp1 : fr1.vals[rp]? = some (.val (.ref l)) := P1.has (rp, _) (by simp)
  have hvals : ls2.vals.size = ls1.vals.size := (emitEffect_facts h2 P1.pp hext2).1
  have PclearKeep : Post cfg env cx ls fr ls2 fr1 (pt1.1, pt1.2 + 1) [(rp, .val (.ref l))] := by
    refine ⟨Pclear.pp, ?_, ?_, Pclear.mono, Pclear.same, Pclear.rel⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      exact hrp1
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      rw [hvals]
      exact P1.lt (rp, .val (.ref l)) (by simp)
  have hclear : execEff cx.fn fr1 (.clear rp (some org)) = truncateLoc l 0 >>= fun _ => pure fr1 := by
    simp only [execEff, getVal_of hrp1, Goose.Core.expectRef, bind_assoc, pure_bind]
  refine SimG.bind (SimG.eff_step (fun _ => fr1) hi hclear) fun _ pt2 fr2 ⟨hpt, hfr⟩ => ?_
  subst pt2
  subst fr2
  refine SimG.bind (ihe replacement (by okpf) le ls2 run ls3 (pt1.1, pt1.2 + 1) cfg env cx fr1 h3 Pclear.pp hext3 Pclear.rel)
      fun replacementVal pt3 fr3 Preplacement => ?_
  have P13 := PclearKeep.comp Preplacement
  have hrp : fr3.vals[rp]? = some (.val (.ref l)) := P13.has (rp, _) (by simp)
  have hr : fr3.vals[run]? = some (.val replacementVal) := P13.has (run, _) (by simp)
  have hx : execEff cx.fn fr3 (.replace rp run (some org)) =
      (match replacementVal with
       | .resizable .. => writeLoc l replacementVal
       | _ => fault .shape) >>= fun _ => pure fr3 := by
    simp only [execEff, getVal_of hrp, getVal_of hr, Goose.Core.expectRef, bind_assoc, pure_bind]
    funext s
    cases replacementVal <;> rfl
  apply leaf_eff P13 h4 hext (Flow.normal .unit) ?_ hx
  funext s
  cases replacementVal <;> rfl

theorem stmtClaim_append (n : Nat) (lc : Option LoopCtx) (ihp : ∀ p, PlaceClaim n p) (ihv : ∀ v, ViewClaim n v) (owner : Place)
    (src : View) (org : OriginId) : StmtClaim (n + 1) lc (.append owner src org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, vw, ls2, h2, h3⟩ := hlow
  have hext2 : ExtT ls2 cx.fn.blocks := hext.of_adv (adv_emitEffect h3)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (advB_lowerView src _ _ _ _ h2)
  simp only [execStmt]
  refine SimG.bind (ihp owner (by okpf) le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun l pt1 fr1 P1 => ?_
  refine SimG.bind (ihv src (by okpf) le ls1 vw ls2 pt1 cfg env cx fr1 h2 P1.pp hext2 P1.rel) fun vwv pt2 fr2 P2 => ?_
  have P12 := P1.comp P2
  have hl : fr2.vals[rp]? = some (.val (.ref l)) := P12.has (rp, _) (by simp)
  have hv : fr2.vals[vw]? = some (.view vwv) := P12.has (vw, _) (by simp)
  have hx : execEff cx.fn fr2 (.append rp vw (some org)) =
      (readRun vwv >>= fun elems => checkedAppendLoc l elems org) >>= fun _ => pure fr2 := by
    simp only [execEff, getVal_of hl, getView_of hv, Goose.Core.expectRef, bind_assoc, pure_bind,
      Goose.Core.checkedAppendLoc, checkCapacityAtOrg, checkAppendCapacity, abortAtOrg, abortAt]
    rfl
  exact leaf_eff P12 h3 hext (Flow.normal .unit) (by simp only [bind_assoc]) hx

theorem stmtClaim_abort (n : Nat) (lc : Option LoopCtx) (msg : String) (org : OriginId) : StmtClaim (n + 1) lc (.abort msg org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt] at hlow
  obtain ⟨-, -, -, hi⟩ := emitTerm_facts hlow hpp hext
  simp only [execStmt]
  exact SimG.abort_term hi

theorem stmtClaim_exit (n : Nat) (lc : Option LoopCtx) (ihe : ∀ e, ExprClaim n e) (e : Expr) (org : OriginId) :
    StmtClaim (n + 1) lc (.exit e org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨v, ls1, h1, h2⟩ := hlow
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitTerm h2)
  simp only [execStmt]
  refine SimG.bind (ihe e (by okpf) le ls v ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectInt fun t code hva => ?_
  subst hva
  have hv : fr1.vals[v]? = some (.val (.int t code)) := P1.has (v, _) (by simp)
  obtain ⟨-, -, -, hi⟩ := emitTerm_facts h2 P1.pp hext
  exact SimG.exit_term hi hv

/-! ### Print -/

def partsIds : List PrintPart → List ValueId
  | [] => []
  | .text _ :: rest => partsIds rest
  | .val v :: rest => v :: partsIds rest

/-- The strings the parts of a print render to in a frame. -/
def PartsRender (fr : Frame) : List PrintPart → List String → Prop
  | [], [] => True
  | .text s :: ps, t :: ts => t = s ∧ PartsRender fr ps ts
  | .val v :: ps, t :: ts => (∃ x, fr.vals[v]? = some (.val x) ∧ Goose.Core.render x = pure t) ∧ PartsRender fr ps ts
  | _, _ => False

theorem PartsRender.congr {fr1 fr2 : Frame} : ∀ {parts : List PrintPart} {strs : List String},
    (∀ i ∈ partsIds parts, fr2.vals[i]? = fr1.vals[i]?) → PartsRender fr1 parts strs →
    PartsRender fr2 parts strs
  | [], [], _, h => h
  | .text s :: ps, t :: ts, hc, ⟨h1, h2⟩ => ⟨h1, PartsRender.congr (by simpa [partsIds] using hc) h2⟩
  | .val v :: ps, t :: ts, hc, ⟨⟨x, hx, hr⟩, h2⟩ =>
    ⟨⟨x, by rw [hc v (by simp [partsIds])]; exact hx, hr⟩,
      PartsRender.congr (fun i hi => hc i (by simp [partsIds, hi])) h2⟩
  | [], _ :: _, _, h => absurd h (by simp [PartsRender])
  | _ :: _, [], _, h => absurd h (by cases ‹PrintPart› <;> simp [PartsRender])

theorem mapList_renderPart_of {fr : Frame} : ∀ {parts : List PrintPart} {strs : List String},
    PartsRender fr parts strs → mapList (renderPart fr) parts = pure strs
  | [], [], _ => rfl
  | .text s :: ps, t :: ts, ⟨h1, h2⟩ => by
    subst h1
    simp only [mapList, renderPart, pure_bind, mapList_renderPart_of h2]
  | .val v :: ps, t :: ts, ⟨⟨x, hx, hr⟩, h2⟩ => by
    simp only [mapList, renderPart, getVal_of hx, hr, pure_bind, mapList_renderPart_of h2]
  | [], _ :: _, h => absurd h (by simp [PartsRender])
  | _ :: _, [], h => absurd h (by cases ‹PrintPart› <;> simp [PartsRender])

def PrintArgsClaim (n : Nat) (args : List PrintArg) : Prop :=
  printOk args = true → ∀ (le : LEnv) (ls : LS) (parts : List PrintPart) (ls' : LS) (pt : Pt) (cfg : Cfg) (env : Env)
    (cx : FnCtx) (fr : Frame), lowerPrintArgs args le ls = (parts, ls') → ls.pp = some pt →
    ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    SimG cx pt fr (mapList (execPrintArg n cfg env) args) (fun strs pt' fr' =>
      ∃ cells, Post cfg env cx ls fr ls' fr' pt' cells ∧
        (∀ i ∈ partsIds parts, ∃ x, (i, x) ∈ cells) ∧ PartsRender fr' parts strs)

theorem printArgsClaim_succ (m : Nat) (ihe : ∀ e, ExprClaim m e) : ∀ args, PrintArgsClaim (m + 1) args
  | [] => by
    intro hok le ls parts ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [lowerPrintArgs, pure_run] at hlow
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
    simp only [mapList]
    exact SimG.ret ⟨[], Post.init hrel hpp, by simp [partsIds], trivial⟩
  | .text s :: rest => by
    intro hok le ls parts ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [lowerPrintArgs, bind_eq] at hlow
    obtain ⟨ps, ls1, h1, h2⟩ := hlow
    rw [pure_run] at h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    simp only [mapList, execPrintArg, pure_bind]
    refine SimG.bind (printArgsClaim_succ m ihe rest (by okpf) le ls ps ls1 pt cfg env cx fr h1 hpp hext hrel)
      fun strs pt1 fr1 ⟨cells, P1, hids, hr⟩ => ?_
    exact SimG.ret ⟨cells, P1, by simpa [partsIds] using hids, rfl, hr⟩
  | .expr e :: rest => by
    intro hok le ls parts ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [lowerPrintArgs, bind_eq] at hlow
    obtain ⟨v, ls1, h1, ps, ls2, h2, h3⟩ := hlow
    rw [pure_run] at h3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
    have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (advB_lowerPrintArgs rest _ _ _ _ h2)
    simp only [mapList, execPrintArg, bind_assoc]
    refine SimG.bind (ihe e (by okpf) le ls v ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
    refine SimG.render fun str hstr => ?_
    refine SimG.bind (printArgsClaim_succ m ihe rest (by okpf) le ls1 ps ls2 pt1 cfg env cx fr1 h2 P1.pp hext P1.rel)
      fun strs pt2 fr2 ⟨cells, P2, hids, hr⟩ => ?_
    refine SimG.ret ⟨(v, .val va) :: cells, ?_, ?_, ?_⟩
    · have := P1.comp P2
      exact this.sub (by intro p hp; simpa using hp)
    · intro i hi
      simp only [partsIds, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact ⟨.val va, by simp⟩
      · obtain ⟨x, hx⟩ := hids i hi
        exact ⟨x, by simp [hx]⟩
    · refine ⟨⟨va, ?_, hstr⟩, hr⟩
      rw [P2.same v (P1.lt (v, .val va) (by simp))]
      exact P1.has (v, .val va) (by simp)

theorem printArgsClaim (n : Nat) (ihe : ∀ m, n = m + 1 → ∀ e, ExprClaim m e) :
    ∀ args, PrintArgsClaim n args := by
  cases n with
  | zero =>
    intro args
    cases args with
    | nil =>
      intro hok le ls parts ls' pt cfg env cx fr hlow hpp hext hrel
      simp only [lowerPrintArgs, pure_run] at hlow
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
      simp only [mapList]
      exact SimG.ret ⟨[], Post.init hrel hpp, by simp [partsIds], trivial⟩
    | cons a rest =>
      intro hok le ls parts ls' pt cfg env cx fr hlow hpp hext hrel
      simp only [mapList, execPrintArg]
      exact SimG.of_timeout_bind
  | succ m => exact printArgsClaim_succ m (ihe m rfl)

theorem stmtClaim_print (n : Nat) (lc : Option LoopCtx) (ihpa : ∀ args, PrintArgsClaim n args) (args : List PrintArg)
    (org : OriginId) : StmtClaim (n + 1) lc (.print args org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨parts, ls1, h1, h2⟩ := hlow
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitEffect h2)
  simp only [execStmt]
  refine SimG.bind (ihpa args (by okpf) le ls parts ls1 pt cfg env cx fr h1 hpp hext1 hrel)
    fun strs pt1 fr1 ⟨cells, P1, hids, hr⟩ => ?_
  have hx : execEff cx.fn fr1 (.print parts (some org)) =
      emit (String.join strs ++ "\n") >>= fun _ => pure fr1 := by
    simp only [execEff, mapList_renderPart_of hr, pure_bind]
  exact leaf_eff P1 h2 hext (Flow.normal .unit) rfl hx

/-! ### Statement lists -/

def StmtsClaim (n : Nat) (lc : Option LoopCtx) (ss : List Stmt) : Prop :=
  stmtsOk ss = true → ∀ (le : LEnv) (ls : LS) (r : Unit) (ls' : LS) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : Frame), lowerStmts lc ss le ls = (r, ls') → ls.pp = some pt → ExtT ls' cx.fn.blocks →
    Rel cfg env cx fr ls →
    SimG cx pt fr (execStmts n cfg env ss) (fun flow pt' fr' =>
      flow = Flow.normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' [])

theorem stmtsClaim_zero (lc : Option LoopCtx) (ss : List Stmt) : StmtsClaim 0 lc ss := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [execStmts]
  exact SimG.of_timeout

theorem stmtsClaim_succ (n : Nat) (lc : Option LoopCtx) (ihs : ∀ s, StmtClaim n lc s) (ihss : ∀ ss, StmtsClaim n lc ss) :
    ∀ ss, StmtsClaim (n + 1) lc ss
  | [] => by
    intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [lowerStmts, pure_run] at hlow
    obtain ⟨-, rfl⟩ := Prod.mk.inj hlow
    simp only [execStmts]
    exact SimG.ret ⟨rfl, Post.init hrel hpp⟩
  | s :: rest => by
    intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
    obtain ⟨blk, hc, -, -⟩ := LS.pp_some hpp
    simp only [lowerStmts, bind_eq] at hlow
    obtain ⟨live, ls0, h0, hlow⟩ := hlow
    rw [isLive_run hc] at h0
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
    simp only [ite_true, bind_eq] at hlow
    obtain ⟨u1, ls1, h1, h2⟩ := hlow
    have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (advB_lowerStmts lc rest _ _ _ _ h2)
    simp only [execStmts]
    refine SimG.bind (ihs s (by okpf) le ls u1 ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun flow pt1 fr1 ⟨hfl, P1⟩ => ?_
    subst hfl
    exact (ihss rest (by okpf) le ls1 r ls' pt1 cfg env cx fr1 h2 P1.pp hext P1.rel).mono
      fun flow2 pt2 fr2 ⟨hfl2, P2⟩ => ⟨hfl2, (P1.comp P2).sub (by simp)⟩

/-! ### Blocks -/

theorem releaseSlots_eq {fn : Func} {vars : Array LocalVar}
    (hs : fn.slots = vars.mapIdx fun i lv => (⟨lv.ty, lv.kind, lv.scope, i⟩ : Slot))
    (act : ActId) (sc : Nat) (si : ScopeInst) :
    ∀ (n : Nat) (st : Store), releaseSlots fn act sc si n st = releaseVars vars act sc si n st
  | 0, st => rfl
  | n + 1, st => by
    simp only [releaseSlots, releaseVars, hs, Array.getElem?_mapIdx]
    cases vars[n]? with
    | none => exact releaseSlots_eq hs act sc si n st
    | some lv => simpa using releaseSlots_eq hs act sc si n _

theorem releaseScope_eq {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls : LS}
    (hrel : Rel cfg env cx fr ls) (sc : Nat) (si : ScopeInst) :
    GIR.releaseScope cx.fn fr.act sc si = Core.releaseScope env sc si := by
  funext s
  have hsz : cx.fn.slots.size = env.vars.size := by rw [hrel.slots]; simp
  simp only [GIR.releaseScope, Core.releaseScope, hrel.act, hsz]
  rw [releaseSlots_eq hrel.slots]

theorem block_enter {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls1 : LS} {fr : Frame} {pt : Pt}
    {le : LEnv} {sc : ScopeId} (hpp : ls.pp = some pt) (h : emitEffect (.enter sc) le ls = ((), ls1))
    (hext : ExtT ls1 cx.fn.blocks) (hrel : Rel cfg env cx fr ls) :
    SimG cx pt fr freshScope (fun si pt1 fr1 =>
      ls1.pp = some pt1 ∧ ls1.vals.size = ls.vals.size ∧ fr1.vals = fr.vals ∧
      Rel cfg { env with scopes := (sc, si) :: env.scopes } cx fr1 { ls1 with stack := sc :: ls1.stack }) := by
  obtain ⟨hv, hst, hpp1, hi⟩ := emitEffect_facts h hpp hext
  have hx : execEff cx.fn fr (.enter sc) =
      freshScope >>= fun si => pure ({ fr with scopes := (sc, si) :: fr.scopes } : Frame) := rfl
  refine (SimG.eff_step (fun si => { fr with scopes := (sc, si) :: fr.scopes }) hi hx).mono
    fun si pt1 fr1 ⟨hpt, hfr⟩ => ?_
  subst hpt; subst hfr
  refine ⟨hpp1, hv, rfl, ?_⟩
  exact ⟨hrel.prof, hrel.slots, hrel.act, by simp [hrel.scopes], hrel.depth, by simp [hst, hrel.stack]⟩

theorem block_leave {cfg : Cfg} {env : Env} {cx : FnCtx} {lsk ls_l : LS} {frk : Frame} {ptk : Pt}
    {le : LEnv} {sc : ScopeId} {si : ScopeInst} (hpp : lsk.pp = some ptk)
    (h : emitEffect (.leave sc) le lsk = ((), ls_l)) (hext : ExtT ls_l cx.fn.blocks)
    (hrel : Rel cfg { env with scopes := (sc, si) :: env.scopes } cx frk lsk) :
    SimG cx ptk frk (Core.releaseScope env sc si) (fun _ pt' fr' =>
      ls_l.pp = some pt' ∧ ls_l.vals.size = lsk.vals.size ∧ fr'.vals = frk.vals ∧
      Rel cfg env cx fr' { ls_l with stack := ls_l.stack.drop 1 }) := by
  obtain ⟨hv, hst, hpp1, hi⟩ := emitEffect_facts h hpp hext
  have hsc : frk.scopes = (sc, si) :: env.scopes := hrel.scopes
  have heq := releaseScope_eq hrel sc si
  have hx : execEff cx.fn frk (.leave sc) =
      Core.releaseScope env sc si >>= fun _ => pure ({ frk with scopes := env.scopes } : Frame) := by
    simp only [execEff, hsc, ↓reduceIte]
    rw [heq]
    rfl
  refine (SimG.eff_step (fun _ => { frk with scopes := env.scopes }) hi hx).mono
    fun u pt1 fr1 ⟨hpt, hfr⟩ => ?_
  subst hpt; subst hfr
  refine ⟨hpp1, hv, rfl, ?_⟩
  refine ⟨hrel.prof, hrel.slots, hrel.act, rfl, hrel.depth, ?_⟩
  have := hrel.stack
  simp only [List.map_cons] at this
  simp [hst, this]

/-- A block's own scope around its statements, and what it does with the flow that ends them. -/
def coreBlock (n : Nat) (cfg : Cfg) (env : Env) (sc : Nat) (stmts : List Stmt)
    (vf : Env → Flow → M Flow) : M Flow := do
  let si ← freshScope
  let env' : Env := { env with scopes := (sc, si) :: env.scopes }
  let flow ← execStmts n cfg env' stmts
  let flow' ← vf env' flow
  Goose.Core.releaseScope env sc si
  pure flow'

/-- What a block does with the flow that ends its statements. -/
def valueFlow (n : Nat) (cfg : Cfg) : Option Expr → Env → Flow → M Flow
  | some e, env', .normal _ => do pure (Flow.normal (← evalExpr n cfg env' e))
  | _, _, f => pure f

theorem execBlock_nil (n : Nat) (cfg : Cfg) (env : Env) (sc : Nat) (stmts : List Stmt)
    (value : Option Expr) :
    execBlock (n + 1) cfg env [] (.mk sc stmts value) = coreBlock n cfg env sc stmts (valueFlow n cfg value) := by
  rw [execBlock]
  simp only [coreBlock, bindAll, pure_bind]
  congr 1
  funext si
  congr 1
  funext flow
  congr 1
  funext flow'
  cases flow <;> cases value <;> simp [valueFlow]

/-- A post-condition of a fragment run in an inner scope, as one of the whole block. -/
theorem Post.rescope {cfg : Cfg} {env env' : Env} {cx : FnCtx} {ls lsp lsk ls_f : LS}
    {fr frp frk fr_f : Frame} {ptk pt : Pt} {cells : List (ValueId × RVal)}
    (hP : Post cfg env' cx lsp frp lsk frk ptk cells) (hv0 : lsp.vals.size = ls.vals.size)
    (hfr0 : frp.vals = fr.vals) (hpp : ls_f.pp = some pt) (hv : ls_f.vals.size = lsk.vals.size)
    (hfr : fr_f.vals = frk.vals) (hrel : Rel cfg env cx fr_f ls_f) :
    Post cfg env cx ls fr ls_f fr_f pt cells := by
  refine ⟨hpp, fun p hp => ?_, fun p hp => ?_, ?_, fun i hi => ?_, hrel⟩
  · rw [hfr]; exact hP.has p hp
  · rw [hv]; exact hP.lt p hp
  · have := hP.mono; rw [hv]; omega
  · have h1 := hP.same i (by omega)
    show fr_f.vals[i]? = fr.vals[i]?
    rw [hfr, h1, hfr0]

theorem block_core {n : Nat} {lc : Option LoopCtx} (ihs : ∀ ss, StmtsClaim n lc ss) {sc : ScopeId} {stmts : List Stmt}
    (hokS : stmtsOk stmts = true) {U : Val → Prop}
    {X : B ValueId} {vf : Env → Flow → M Flow} {cells : ValueId → Val → List (ValueId × RVal)}
    {le : LEnv} {ls ls1 ls_s ls_x ls_l ls' : LS} {u : Unit} {rx r : ValueId} {pt : Pt} {cfg : Cfg}
    {env : Env} {cx : FnCtx} {fr : Frame}
    (h1 : emitEffect (.enter sc) le ls = ((), ls1))
    (h3 : lowerStmts lc stmts le { ls1 with stack := sc :: ls1.stack } = (u, ls_s))
    (h4 : X le ls_s = (rx, ls_x)) (h5 : emitEffect (.leave sc) le ls_x = ((), ls_l))
    (hls' : ls' = { ls_l with stack := ls_l.stack.drop 1 }) (hr : r = rx)
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hadvX : AdvB X)
    (hX : ∀ (env' : Env) (pt_x : Pt) (fr_x : Frame), ls_s.pp = some pt_x →
      ExtT ls_x cx.fn.blocks → Rel cfg env' cx fr_x ls_s →
      SimG cx pt_x fr_x (vf env' (.normal .unit)) (fun flow pt' fr' => ∃ v, flow = .normal v ∧ U v ∧
        Post cfg env' cx ls_s fr_x ls_x fr' pt' (cells rx v))) :
    SimG cx pt fr (coreBlock n cfg env sc stmts vf) (fun flow pt' fr' => ∃ v, flow = .normal v ∧ U v ∧
      Post cfg env cx ls fr ls' fr' pt' (cells r v)) := by
  subst hr
  have hext_l : ExtT ls_l cx.fn.blocks := by rw [hls'] at hext; exact hext
  have hext_x : ExtT ls_x cx.fn.blocks := hext_l.of_adv (adv_emitEffect h5)
  have hext_s : ExtT ls_s cx.fn.blocks := hext_x.of_adv (hadvX _ _ _ _ h4)
  have hext_p : ExtT { ls1 with stack := sc :: ls1.stack } cx.fn.blocks :=
    hext_s.of_adv (advB_lowerStmts lc stmts _ _ _ _ h3)
  have hext_1 : ExtT ls1 cx.fn.blocks := hext_p
  unfold coreBlock
  refine SimG.bind (block_enter hpp h1 hext_1 hrel) fun si pt1 fr1 ⟨hpp1, hv1, hfr1, hrel1⟩ => ?_
  refine SimG.bind (ihs stmts hokS le _ u ls_s pt1 cfg _ cx fr1 h3 hpp1 hext_s hrel1) fun flow pt2 fr2 ⟨hfl, P2⟩ => ?_
  subst hfl
  refine SimG.bind (hX _ pt2 fr2 P2.pp hext_x P2.rel) fun flow' pt3 fr3 ⟨v, hfl', hU, P3⟩ => ?_
  subst hfl'
  refine SimG.bind (block_leave P3.pp h5 hext_l P3.rel) fun _ pt4 fr4 ⟨hpp4, hv4, hfr4, hrel4⟩ => ?_
  refine SimG.ret ⟨v, rfl, hU, ?_⟩
  have P23 := P2.comp P3
  refine Post.rescope (P23.sub (cells' := cells r v) (by simp)) (hv0 := ?_) (hfr0 := hfr1) ?_ ?_ hfr4 ?_
  · exact hv1
  · rw [hls']; exact hpp4
  · rw [hls']; exact hv4
  · rw [hls']; exact hrel4

theorem block_unfold {lc : Option LoopCtx} {sc : ScopeId} {stmts : List Stmt} {value : Option Expr} {want : Bool}
    {le : LEnv} {ls : LS} {r : ValueId} {ls' : LS}
    (h : lowerBlock lc [] want (.mk sc stmts value) le ls = (r, ls')) :
    ∃ ls1 ls_s ls_x ls_l u rx, emitEffect (.enter sc) le ls = ((), ls1) ∧
      lowerStmts lc stmts le { ls1 with stack := sc :: ls1.stack } = (u, ls_s) ∧
      lowerBlockValue want value le ls_s = (rx, ls_x) ∧
      emitEffect (.leave sc) le ls_x = ((), ls_l) ∧
      ls' = { ls_l with stack := ls_l.stack.drop 1 } ∧ r = rx := by
  simp only [lowerBlock, bind_eq] at h
  obtain ⟨u1, ls1, h1, hin⟩ := h
  obtain ⟨ls_k, hk, hls'⟩ := inScope_eq hin
  simp only [bind_eq] at hk
  obtain ⟨u2, ls_p, h2, u3, ls_s, h3, rx, ls_x, h4, u5, ls_l, h5, hpure⟩ := hk
  simp only [initSlots, pure_run] at h2
  obtain ⟨-, rfl⟩ := Prod.mk.inj h2
  rw [pure_run] at hpure
  obtain ⟨hr, rfl⟩ := Prod.mk.inj hpure
  exact ⟨ls1, ls_s, ls_x, ls_l, u3, rx, by simpa using h1, h3, h4, by simpa using h5, hls', hr.symm⟩

def blockCells (blk : Core.Block) (want : Bool) (r : ValueId) (v : Val) : List (ValueId × RVal) :=
  if blk.value.isSome || want then [(r, .val v)] else []

def BlockClaim (n : Nat) (lc : Option LoopCtx) (want : Bool) (blk : Core.Block) : Prop :=
  blockOk blk = true → ∀ (le : LEnv) (ls : LS) (r : ValueId) (ls' : LS) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : Frame), lowerBlock lc [] want blk le ls = (r, ls') → ls.pp = some pt →
    ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    SimG cx pt fr (execBlock n cfg env [] blk) (fun flow pt' fr' => ∃ v, flow = .normal v ∧
      (blk.value = none → v = .unit) ∧ Post cfg env cx ls fr ls' fr' pt' (blockCells blk want r v))

theorem blockClaim_succ (n : Nat) (lc : Option LoopCtx) (ihs : ∀ ss, StmtsClaim n lc ss) (ihe : ∀ e, ExprClaim n e)
    (want : Bool) (blk : Core.Block) : BlockClaim (n + 1) lc want blk := by
  obtain ⟨sc, stmts, value⟩ := blk
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  obtain ⟨ls1, ls_s, ls_x, ls_l, u, rx, h1, h3, h4, h5, hls', hr⟩ := block_unfold hlow
  rw [execBlock_nil]
  cases value with
  | some e =>
    simp only [lowerBlockValue] at h4
    refine (block_core ihs (by okpf) (U := fun _ => True) (cells := fun rx v => [(rx, .val v)])
      (vf := valueFlow n cfg (some e)) h1 h3 h4 h5 hls' hr hpp hext hrel (advB_lowerExpr e) ?_).mono ?_
    · intro env' pt_x fr_x hpp_x hext_x hrel_x
      simp only [valueFlow]
      refine SimG.bind (ihe e (by okpf) le ls_s rx ls_x pt_x cfg env' cx fr_x h4 hpp_x hext_x hrel_x)
        fun v pt' fr' P => ?_
      exact SimG.ret ⟨v, rfl, trivial, P⟩
    · rintro flow pt' fr' ⟨v, hf, -, P⟩
      exact ⟨v, hf, (fun h => by cases h), by
        simp only [blockCells, Core.Block.value, Option.isSome_some, Bool.true_or, ↓reduceIte]; exact P⟩
  | none =>
    cases want
    · have h4' : (pure 0 : B ValueId) le ls_s = (rx, ls_x) := by
        simpa [lowerBlockValue] using h4
      refine (block_core ihs (by okpf) (U := fun v => v = .unit) (cells := fun _ _ => [])
        (vf := valueFlow n cfg none) h1 h3 h4' h5 hls' hr hpp hext hrel (AdvB.pure _) ?_).mono ?_
      · intro env' pt_x fr_x hpp_x hext_x hrel_x
        have hx : ls_x = ls_s := by rw [pure_run] at h4'; exact (Prod.mk.inj h4').2.symm
        subst hx
        exact SimG.ret ⟨.unit, rfl, rfl, Post.init hrel_x hpp_x⟩
      · intro flow pt' fr' ⟨v, hf, hU, P⟩
        exact ⟨v, hf, (fun _ => hU), by simp only [blockCells, Core.Block.value, Option.isSome_none,
          Bool.false_or, Bool.false_eq_true, ↓reduceIte]; exact P⟩
    · have h4' : emitDef .constUnit le ls_s = (rx, ls_x) := by
        simpa [lowerBlockValue] using h4
      refine (block_core ihs (by okpf) (U := fun v => v = .unit) (cells := fun rx v => [(rx, .val v)])
        (vf := valueFlow n cfg none) h1 h3 h4' h5 hls' hr hpp hext hrel (advB_emitDef _) ?_).mono ?_
      · intro env' pt_x fr_x hpp_x hext_x hrel_x
        have hP := Post.init hrel_x hpp_x
        show SimG cx pt_x fr_x ((pure () : M Unit) >>= fun _ => pure (Flow.normal Val.unit)) _
        refine SimG.bind (leaf_def hP h4' hext_x (by simp) (fun _ => RVal.val Val.unit)
          (c := (pure () : M Unit)) (by simp [execPure])) fun _ pt' fr' P => ?_
        exact SimG.ret ⟨.unit, rfl, rfl, P⟩
      · intro flow pt' fr' ⟨v, hf, hU, P⟩
        exact ⟨v, hf, (fun _ => hU), by simp only [blockCells, Core.Block.value, Option.isSome_none,
          Bool.false_or, Bool.or_true, ↓reduceIte]; exact P⟩

def BlockValueClaim (n : Nat) (blk : Core.Block) : Prop :=
  blockOk blk = true → ∀ (le : LEnv) (ls : LS) (r : ValueId) (ls' : LS) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : Frame), lowerBlock none [] true blk le ls = (r, ls') → ls.pp = some pt →
    ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    SimG cx pt fr (blockValue n cfg env blk) (fun v pt' fr' =>
      Post cfg env cx ls fr ls' fr' pt' [(r, .val v)])

theorem blockValueClaim_zero (blk : Core.Block) : BlockValueClaim 0 blk := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [blockValue]
  exact SimG.of_timeout

theorem blockValueClaim_succ (n : Nat) (ihb : ∀ want blk, BlockClaim n none want blk) (blk : Core.Block) :
    BlockValueClaim (n + 1) blk := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [blockValue]
  refine SimG.bind (ihb true blk (by okpf) le ls r ls' pt cfg env cx fr hlow hpp hext hrel)
    fun flow pt' fr' ⟨v, hf, _, P⟩ => ?_
  subst hf
  exact SimG.ret (by simpa [blockCells] using P)

theorem exprClaim_blockE (n : Nat) (ihbv : ∀ blk, BlockValueClaim n blk) (b : Core.Block) :
    ExprClaim (n + 1) (.blockE b) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr] at hlow
  simp only [evalExpr]
  exact ihbv b (by okpf) le ls r ls' pt cfg env cx fr hlow hpp hext hrel

theorem exprClaim_ifE (n : Nat) (ihe : ∀ e, ExprClaim n e) (ihbv : ∀ blk, BlockValueClaim n blk)
    (c : Expr) (t f : Core.Block) : ExprClaim (n + 1) (.ifE c t f) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerExpr, bind_eq] at hlow
  obtain ⟨cv, ls1, h1, hw⟩ := hlow
  have hadv_w : ls1.Adv ls' :=
    advB_ifE_core cv (advB_lowerBlock none [] true t) (advB_lowerBlock none [] true f) _ _ _ _ hw
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv hadv_w
  simp only [evalExpr]
  refine SimG.bind (ihe c (by okpf) le ls cv ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectBool fun β hva => ?_
  subst hva
  have hcv : fr1.vals[cv]? = some (.val (.bool β)) := P1.has (cv, _) (by simp)
  obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some P1.pp
  rw [whenLive_some _ _ _ hc1] at hw
  simp only [bind_eq] at hw
  obtain ⟨⟨tb, eb⟩, lsf, hf, u2, ls2, hs1, vt, ls3, ha1, endT, ls4, hc4, u5, ls5, hs2, vf, ls6, ha2,
    endF, ls7, hc7, hj⟩ := hw
  obtain ⟨e4c, e4⟩ := curBlock_eq hc4
  subst e4
  obtain ⟨e7c, e7⟩ := curBlock_eq hc7
  subst e7
  have hext6 : ExtT ls7 cx.fn.blocks := hext.of_ext (joinValue_ext hj)
  have hadv1 := advB_lowerBlock none [] true t _ _ _ _ ha1
  have hadv2 := advB_lowerBlock none [] true f _ _ _ _ ha2
  obtain ⟨htb, heb, hinst, ⟨Ttb, hTtb, hTtbp⟩, ⟨Teb, hTeb, hTebp⟩, hpp2, hpp5, hst2, hv2, hst3, hst6,
    hv16, hv36, hendT, hendF, hkeep, hsz36, hsz6⟩ :=
    branch_facts hf hs1 hadv1 hs2 hadv2 P1.pp hext6
  have hpp2' : ls2.pp = some (tb, 0) := hpp2
  have hrel2 : Rel cfg env cx fr1 ls2 := P1.rel.stack_eq hst2
  -- the join
  have hltT : ∀ b, endT = some b → b < ls7.blocks.size := by
    intro b hb
    exact Nat.lt_of_lt_of_le (hendT b (by rw [e4c] at hb; exact hb)).1 hsz36
  have hltF : ∀ b, endF = some b → b < ls7.blocks.size := by
    intro b hb
    exact (hendF b (by rw [e7c] at hb; exact hb)).1
  have hnd : ∀ bT bF, endT = some bT → endF = some bF → bT ≠ bF := by
    intro bT bF hT hF
    obtain ⟨hlt, hne, hcase⟩ := hendT bT (by rw [e4c] at hT; exact hT)
    obtain ⟨-, hcase'⟩ := hendF bF (by rw [e7c] at hF; exact hF)
    intro hh
    subst hh
    rcases hcase' with h | h
    · exact hne h
    · nat_omega
  have hinst' : instAt cx.fn pt1 = some (.term (.condbr cv tb [] eb [])) := hinst
  have hmono_all : ls1.vals.size ≤ ls4.vals.size := by
    have := hadv1.vals; nat_omega
  have e5 : ls5 = { ls4 with cur := some eb } := by
    rw [setCur_run] at hs2; exact (Prod.mk.inj hs2).2.symm
  have hext4 : ExtT ls4 cx.fn.blocks := by
    have := hext6.of_adv hadv2
    rw [e5] at this; exact this
  have hm1 := P1.mono
  have hst1 : ls1.stack = ls.stack := P1.rel.stack.trans hrel.stack.symm
  have hst_out : ls7.stack = ls.stack := hst6.trans hst1
  cases β
  · -- the else arm
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine SimG.goes (goes_condbr_else0 hinst' hcv hTeb hTebp rfl) ?_
    have hrel5 : Rel cfg env cx fr1 ls5 := P1.rel.stack_eq (by rw [e5]; exact hst3)
    refine SimG.mono_goes (ihbv f (by okpf) le ls5 vf ls7 (eb, 0) cfg env cx fr1 ha2 hpp5 hext6 hrel5) ?_
    intro v pt7 fr7 P7
    obtain ⟨blk7, hc7', hb7, hp7⟩ := LS.pp_some P7.pp
    have hendF' : endF = some pt7.1 := by rw [e7c]; exact hc7'
    have hlive : endT.isSome ∨ endF.isSome := Or.inr (by rw [hendF']; rfl)
    obtain ⟨ty, hr, hvj, hstj, hbj, hcj, hTj, hFj⟩ := joinValue_facts hj hext hlive hnd hltT hltF
    have hinstF := hFj pt7.1 blk7 hendF' hb7
    obtain ⟨Tjb, hTjb, hTjbp⟩ := hext.params hbj
    have hcell : fr7.vals[vf]? = some (.val v) := P7.has (vf, _) (by simp)
    have hpt7 : pt7 = (pt7.1, blk7.insts.size) := Prod.ext rfl hp7
    have hi7 : instAt cx.fn pt7 = some (.term (.br ls7.blocks.size [vf])) := by
      rw [hpt7]; exact hinstF
    have g2 := goes_br1 hi7 hTjb hTjbp hcell
    refine ⟨(ls7.blocks.size, 0), fr7.set ls7.vals.size (.val v), g2, ?_⟩
    rw [hr]
    have hsame : Same ls.vals.size fr fr7 := by
      refine P1.same.trans (P7.same.mono ?_) P1.mono
      rw [e5]; show ls1.vals.size ≤ ls4.vals.size; exact hmono_all
    exact Post.join hsame (P7.rel.stack_eq (hrel.stack.trans P7.rel.stack.symm)) (by nat_omega)
      (by nat_omega) (by nat_omega) (hstj.trans hst_out) (LS.pp_eq hcj hbj)
  · -- the then arm
    simp only [↓reduceIte]
    refine SimG.goes (goes_condbr_then0 hinst' hcv hTtb hTtbp rfl) ?_
    refine SimG.mono_goes (ihbv t (by okpf) le ls2 vt ls4 (tb, 0) cfg env cx fr1 ha1 hpp2' hext4 hrel2) ?_
    intro v pt3 fr3 P3
    obtain ⟨blk3, hc3, hb3, hp3⟩ := LS.pp_some P3.pp
    have hendT' : endT = some pt3.1 := by rw [e4c]; exact hc3
    have hlive : endT.isSome ∨ endF.isSome := Or.inl (by rw [hendT']; rfl)
    obtain ⟨ty, hr, hvj, hstj, hbj, hcj, hTj, hFj⟩ := joinValue_facts hj hext hlive hnd hltT hltF
    have hne : pt3.1 ≠ eb := (hendT pt3.1 hc3).2.1
    have hb7 : ls7.blocks[pt3.1]? = some blk3 := hkeep pt3.1 blk3 hb3 hne
    have hinstT := hTj pt3.1 blk3 hendT' hb7
    obtain ⟨Tjb, hTjb, hTjbp⟩ := hext.params hbj
    have hcell : fr3.vals[vt]? = some (.val v) := P3.has (vt, _) (by simp)
    have hpt3 : pt3 = (pt3.1, blk3.insts.size) := Prod.ext rfl hp3
    have hi3 : instAt cx.fn pt3 = some (.term (.br ls7.blocks.size [vt])) := by
      rw [hpt3]; exact hinstT
    have g2 := goes_br1 hi3 hTjb hTjbp hcell
    refine ⟨(ls7.blocks.size, 0), fr3.set ls7.vals.size (.val v), g2, ?_⟩
    rw [hr]
    have hsame : Same ls.vals.size fr fr3 := by
      refine P1.same.trans (P3.same.mono ?_) P1.mono
      nat_omega
    exact Post.join hsame (P3.rel.stack_eq (hrel.stack.trans P3.rel.stack.symm)) (by nat_omega)
      (by nat_omega) (by nat_omega) (hstj.trans hst_out) (LS.pp_eq hcj hbj)

/-- A fragment that leaves no result cell. -/
theorem Post.nil {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls' : LS} {fr fr' : Frame} {pt' : Pt}
    (hpp : ls'.pp = some pt') (hmono : ls.vals.size ≤ ls'.vals.size) (hsame : Same ls.vals.size fr fr')
    (hrel : Rel cfg env cx fr' ls') : Post cfg env cx ls fr ls' fr' pt' [] :=
  ⟨hpp, by simp, by simp, hmono, hsame, hrel⟩

theorem stmtClaim_assert (n : Nat) (lc : Option LoopCtx) (ihe : ∀ e, ExprClaim n e) (e : Expr) (org : OriginId) :
    StmtClaim (n + 1) lc (.assertS e org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨cv, ls1, h1, hw⟩ := hlow
  have hadv_w : ls1.Adv ls' := advB_assert_core cv org _ _ _ _ hw
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv hadv_w
  simp only [execStmt]
  refine SimG.bind (ihe e (by okpf) le ls cv ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectBool fun β hva => ?_
  subst hva
  have hcv : fr1.vals[cv]? = some (.val (.bool β)) := P1.has (cv, _) (by simp)
  obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some P1.pp
  rw [whenLive_some _ _ _ hc1] at hw
  simp only [bind_eq] at hw
  obtain ⟨⟨pb, fb⟩, lsf, hf, u2, ls2, hs1, u3, ls4, ht, hs2⟩ := hw
  have e2 : ls2 = { lsf with cur := some fb } := by
    rw [setCur_run] at hs1; exact (Prod.mk.inj hs1).2.symm
  have e5 : ls' = { ls4 with cur := some pb } := by
    rw [setCur_run] at hs2; exact (Prod.mk.inj hs2).2.symm
  have hext4 : ExtT ls4 cx.fn.blocks := by rw [e5] at hext; exact hext
  have hext2 : ExtT ls2 cx.fn.blocks := hext4.of_adv (adv_emitTerm ht)
  have hextf : ExtT lsf cx.fn.blocks := by rw [e2] at hext2; exact hext2
  obtain ⟨htb, heb, hszf, hvf, hstf, hcf, hinst, hbpb, hbfb⟩ := fork_facts hf P1.pp hextf
  have hTpb := hextf.params hbpb
  have hTfb := hextf.params hbfb
  have hpp2 : ls2.pp = some (fb, 0) := by rw [e2]; exact LS.pp_cur hbfb
  obtain ⟨hv4, hst4, hc4, hiabort⟩ := emitTerm_facts ht hpp2 hext4
  have hpb4 : ls4.blocks[pb]? = some ⟨[], #[]⟩ := by
    rw [emitTerm_run _ _ (show ls2.cur = some fb by rw [e2])] at ht
    obtain ⟨-, rfl⟩ := Prod.mk.inj ht
    show (ls2.blocks.modify fb _)[pb]? = _
    rw [getElem?_modify_ne (by nat_omega)]
    rw [e2]; exact hbpb
  have hpp' : ls'.pp = some (pb, 0) := by rw [e5]; exact LS.pp_cur hpb4
  have hst1 : ls1.stack = ls.stack := P1.rel.stack.trans hrel.stack.symm
  have hstl : ls'.stack = ls.stack := by
    rw [e5]; show ls4.stack = _
    rw [hst4]; show ls2.stack = _
    rw [e2]; show lsf.stack = _
    rw [hstf, hst1]
  have hm1 := P1.mono
  have hvl : ls'.vals.size = ls1.vals.size := by
    rw [e5]; show ls4.vals.size = _
    rw [hv4]; show ls2.vals.size = _
    rw [e2]; show lsf.vals.size = _
    rw [hvf]
  have hinst' : instAt cx.fn pt1 = some (.term (.condbr cv pb [] fb [])) := hinst
  cases β
  · -- the abort
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨Tfb, hTfb', hTfbp⟩ := hTfb
    refine SimG.goes (goes_condbr_else0 hinst' hcv hTfb' hTfbp rfl) ?_
    exact SimG.abort_term hiabort
  · simp only [↓reduceIte]
    obtain ⟨Tpb, hTpb', hTpbp⟩ := hTpb
    refine SimG.goes (goes_condbr_then0 hinst' hcv hTpb' hTpbp rfl) ?_
    refine SimG.ret ⟨rfl, Post.nil hpp' (by nat_omega) ?_ ?_⟩
    · exact P1.same.mono (by nat_omega)
    · exact P1.rel.stack_eq (by rw [hstl, hst1])

theorem stmtClaim_ifS_none (n : Nat) (lc : Option LoopCtx) (ihe : ∀ e, ExprClaim n e) (ihb : ∀ want blk, BlockClaim n lc want blk)
    (c : Expr) (t : Core.Block) (org : OriginId) : StmtClaim (n + 1) lc (.ifS c t none org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨cv, ls1, h1, hw⟩ := hlow
  have hadv_w : ls1.Adv ls' := advB_ifS_none_core cv (advB_lowerBlock lc [] false t) _ _ _ _ hw
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv hadv_w
  simp only [execStmt]
  refine SimG.bind (ihe c (by okpf) le ls cv ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectBool fun β hva => ?_
  subst hva
  have hcv : fr1.vals[cv]? = some (.val (.bool β)) := P1.has (cv, _) (by simp)
  obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some P1.pp
  rw [whenLive_some _ _ _ hc1] at hw
  simp only [bind_eq] at hw
  obtain ⟨⟨tb, jb⟩, lsf, hf, u2, ls2, hs1, vt, ls3, ha1, u4, ls4, ht, hs2⟩ := hw
  have e2 : ls2 = { lsf with cur := some tb } := by
    rw [setCur_run] at hs1; exact (Prod.mk.inj hs1).2.symm
  have e5 : ls' = { ls4 with cur := some jb } := by
    rw [setCur_run] at hs2; exact (Prod.mk.inj hs2).2.symm
  have hext4 : ExtT ls4 cx.fn.blocks := by rw [e5] at hext; exact hext
  have hadv1 := advB_lowerBlock lc [] false t _ _ _ _ ha1
  have hext3 : ExtT ls3 cx.fn.blocks := hext4.of_adv (adv_emitTerm ht)
  have hext2 : ExtT ls2 cx.fn.blocks := hext3.of_adv hadv1
  have hextf : ExtT lsf cx.fn.blocks := by rw [e2] at hext2; exact hext2
  obtain ⟨htb, hjb, hszf, hvf, hstf, hcf, hinst, hbtb, hbjb⟩ := fork_facts hf P1.pp hextf
  obtain ⟨Ttb, hTtb, hTtbp⟩ := hextf.params hbtb
  obtain ⟨Tjb, hTjb, hTjbp⟩ := hextf.params hbjb
  have hpp2 : ls2.pp = some (tb, 0) := by rw [e2]; exact LS.pp_cur hbtb
  have hst1 : ls1.stack = ls.stack := P1.rel.stack.trans hrel.stack.symm
  have hst2 : ls2.stack = ls.stack := by rw [e2]; show lsf.stack = _; rw [hstf, hst1]
  have hv2 : ls2.vals.size = ls1.vals.size := by rw [e2]; show lsf.vals.size = _; rw [hvf]
  have hrel2 : Rel cfg env cx fr1 ls2 := P1.rel.stack_eq (by rw [hst2, hst1])
  have hm1 := P1.mono
  have hinst' : instAt cx.fn pt1 = some (.term (.condbr cv tb [] jb [])) := hinst
  have a4 := adv_emitTerm ht
  have hjb3 : ls3.blocks[jb]? = some ⟨[], #[]⟩ := by
    refine hadv1.keep jb ⟨[], #[]⟩ ?_ ?_
    · rw [e2]; show some tb ≠ some jb; intro hh; have := Option.some.inj hh; nat_omega
    · rw [e2]; exact hbjb
  have hjb4 : ls4.blocks[jb]? = some ⟨[], #[]⟩ := by
    cases hce : ls3.cur with
    | none =>
      rw [emitTerm_none _ _ hce] at ht
      obtain ⟨-, rfl⟩ := Prod.mk.inj ht
      exact hjb3
    | some b3 =>
      rw [emitTerm_run _ _ hce] at ht
      obtain ⟨-, rfl⟩ := Prod.mk.inj ht
      have hb3 : b3 ≠ jb := by
        rcases hadv1.cur with h | h | ⟨c, hc, hc1, _⟩
        · rw [hce] at h; cases h
        · rw [hce, e2] at h
          have := Option.some.inj h
          nat_omega
        · rw [hce] at hc
          have := Option.some.inj hc
          have hl2 : ls2.blocks.size = ls1.blocks.size + 2 := by rw [e2]; exact hszf
          nat_omega
      show (ls3.blocks.modify b3 _)[jb]? = _
      rw [getElem?_modify_ne hb3]
      exact hjb3
  have hpp' : ls'.pp = some (jb, 0) := by rw [e5]; exact LS.pp_cur hjb4
  have hstl : ls'.stack = ls.stack := by
    rw [e5]; show ls4.stack = _
    rw [a4.stack, hadv1.stack, hst2]
  have hmono : ls.vals.size ≤ ls'.vals.size := by
    rw [e5]; show _ ≤ ls4.vals.size
    have := a4.vals; have := hadv1.vals; nat_omega
  cases β
  · -- jump over the block
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine SimG.goes (goes_condbr_else0 hinst' hcv hTjb hTjbp rfl) ?_
    exact SimG.ret ⟨rfl, Post.nil hpp' hmono P1.same (P1.rel.stack_eq (by rw [hstl, hst1]))⟩
  · simp only [↓reduceIte]
    refine SimG.goes (goes_condbr_then0 hinst' hcv hTtb hTtbp rfl) ?_
    refine SimG.bind (ihb false t (by okpf) le ls2 vt ls3 (tb, 0) cfg env cx fr1 ha1 hpp2 hext3 hrel2)
      fun flow pt3 fr3 ⟨v, hf, _, P3⟩ => ?_
    subst hf
    obtain ⟨hv4, hst4, hc4, hi3'⟩ := emitTerm_facts ht P3.pp hext4
    obtain ⟨Tjb', hTjb', hTjbp'⟩ : ∃ blk, cx.fn.blocks[jb]? = some blk ∧ blk.params = [] := ⟨Tjb, hTjb, hTjbp⟩
    have hi3 : instAt cx.fn pt3 = some (.term (.br jb [])) := hi3'
    have g2 := goes_br0 (fr := fr3) hi3 hTjb' hTjbp'
    refine SimG.goes g2 (SimG.ret ⟨rfl, Post.nil hpp' hmono ?_ ?_⟩)
    · exact P1.same.trans (P3.same.mono (by nat_omega)) P1.mono
    · exact P3.rel.stack_eq (by rw [hstl, hrel.stack, P3.rel.stack])

theorem stmtClaim_ifS_some (n : Nat) (lc : Option LoopCtx) (ihe : ∀ e, ExprClaim n e) (ihb : ∀ want blk, BlockClaim n lc want blk)
    (c : Expr) (t fb : Core.Block) (org : OriginId) : StmtClaim (n + 1) lc (.ifS c t (some fb) org) := by
  intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨cv, ls1, h1, hw⟩ := hlow
  have hadv_w : ls1.Adv ls' :=
    advB_ifS_some_core cv (advB_lowerBlock lc [] false t) (advB_lowerBlock lc [] false fb)
      _ _ _ _ hw
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv hadv_w
  simp only [execStmt]
  refine SimG.bind (ihe c (by okpf) le ls cv ls1 pt cfg env cx fr h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectBool fun β hva => ?_
  subst hva
  have hcv : fr1.vals[cv]? = some (.val (.bool β)) := P1.has (cv, _) (by simp)
  obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some P1.pp
  rw [whenLive_some _ _ _ hc1] at hw
  simp only [bind_eq] at hw
  obtain ⟨⟨tb, eb⟩, lsf, hf, u2, ls2, hs1, vt, ls3, ha1, endT, ls4, hc4, u5, ls5, hs2, vf, ls6, ha2,
    endF, ls7, hc7, hj⟩ := hw
  obtain ⟨e4c, e4⟩ := curBlock_eq hc4
  subst e4
  obtain ⟨e7c, e7⟩ := curBlock_eq hc7
  subst e7
  have hext6 : ExtT ls7 cx.fn.blocks := hext.of_ext (joinArms_ext hj)
  have hadv1 := advB_lowerBlock lc [] false t _ _ _ _ ha1
  have hadv2 := advB_lowerBlock lc [] false fb _ _ _ _ ha2
  obtain ⟨htb, heb, hinst, ⟨Ttb, hTtb, hTtbp⟩, ⟨Teb, hTeb, hTebp⟩, hpp2, hpp5, hst2, hv2, hst3, hst6,
    hv16, hv36, hendT, hendF, hkeep, hsz36, hsz6⟩ :=
    branch_facts hf hs1 hadv1 hs2 hadv2 P1.pp hext6
  have hpp2' : ls2.pp = some (tb, 0) := hpp2
  have hrel2 : Rel cfg env cx fr1 ls2 := P1.rel.stack_eq hst2
  have hltT : ∀ b, endT = some b → b < ls7.blocks.size := by
    intro b hb
    exact Nat.lt_of_lt_of_le (hendT b (by rw [e4c] at hb; exact hb)).1 hsz36
  have hltF : ∀ b, endF = some b → b < ls7.blocks.size := by
    intro b hb
    exact (hendF b (by rw [e7c] at hb; exact hb)).1
  have hnd : ∀ bT bF, endT = some bT → endF = some bF → bT ≠ bF := by
    intro bT bF hT hF
    obtain ⟨hlt, hne, hcase⟩ := hendT bT (by rw [e4c] at hT; exact hT)
    obtain ⟨-, hcase'⟩ := hendF bF (by rw [e7c] at hF; exact hF)
    intro hh
    subst hh
    rcases hcase' with h | h
    · exact hne h
    · nat_omega
  have hinst' : instAt cx.fn pt1 = some (.term (.condbr cv tb [] eb [])) := hinst
  have hmono_all : ls1.vals.size ≤ ls4.vals.size := by
    have := hadv1.vals; nat_omega
  have e5 : ls5 = { ls4 with cur := some eb } := by
    rw [setCur_run] at hs2; exact (Prod.mk.inj hs2).2.symm
  have hext4 : ExtT ls4 cx.fn.blocks := by
    have := hext6.of_adv hadv2
    rw [e5] at this; exact this
  have hm1 := P1.mono
  have hst1 : ls1.stack = ls.stack := P1.rel.stack.trans hrel.stack.symm
  have hst_out : ls7.stack = ls.stack := hst6.trans hst1
  cases β
  · -- the else arm
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine SimG.goes (goes_condbr_else0 hinst' hcv hTeb hTebp rfl) ?_
    have hrel5 : Rel cfg env cx fr1 ls5 := P1.rel.stack_eq (by rw [e5]; exact hst3)
    refine SimG.bind (ihb false fb (by okpf) le ls5 vf ls7 (eb, 0) cfg env cx fr1 ha2 hpp5 hext6 hrel5)
      fun flow pt7 fr7 ⟨v, hf, _, P7⟩ => ?_
    subst hf
    obtain ⟨blk7, hc7', hb7, hp7⟩ := LS.pp_some P7.pp
    have hendF' : endF = some pt7.1 := by rw [e7c]; exact hc7'
    have hlive : endT.isSome ∨ endF.isSome := Or.inr (by rw [hendF']; rfl)
    obtain ⟨hvj, hstj, hbj, hcj, hTj⟩ := joinArms_facts hj hext hlive hnd hltT hltF
    have hinstF := hTj pt7.1 blk7 (Or.inr hendF') hb7
    obtain ⟨Tjb, hTjb, hTjbp⟩ := hext.params hbj
    have hpt7 : pt7 = (pt7.1, blk7.insts.size) := Prod.ext rfl hp7
    have hi7 : instAt cx.fn pt7 = some (.term (.br ls7.blocks.size [])) := by
      rw [hpt7]; exact hinstF
    have g2 := goes_br0 (fr := fr7) hi7 hTjb hTjbp
    refine SimG.goes g2 (SimG.ret ⟨rfl, Post.nil (LS.pp_eq hcj hbj) (by nat_omega) ?_ ?_⟩)
    · refine P1.same.trans (P7.same.mono ?_) P1.mono
      rw [e5]; show ls1.vals.size ≤ ls4.vals.size; exact hmono_all
    · exact P7.rel.stack_eq hstj
  · -- the then arm
    simp only [↓reduceIte]
    refine SimG.goes (goes_condbr_then0 hinst' hcv hTtb hTtbp rfl) ?_
    refine SimG.bind (ihb false t (by okpf) le ls2 vt ls4 (tb, 0) cfg env cx fr1 ha1 hpp2' hext4 hrel2)
      fun flow pt3 fr3 ⟨v, hf, _, P3⟩ => ?_
    subst hf
    obtain ⟨blk3, hc3, hb3, hp3⟩ := LS.pp_some P3.pp
    have hendT' : endT = some pt3.1 := by rw [e4c]; exact hc3
    have hlive : endT.isSome ∨ endF.isSome := Or.inl (by rw [hendT']; rfl)
    obtain ⟨hvj, hstj, hbj, hcj, hTj⟩ := joinArms_facts hj hext hlive hnd hltT hltF
    have hne : pt3.1 ≠ eb := (hendT pt3.1 hc3).2.1
    have hb7 : ls7.blocks[pt3.1]? = some blk3 := hkeep pt3.1 blk3 hb3 hne
    have hinstT := hTj pt3.1 blk3 (Or.inl hendT') hb7
    obtain ⟨Tjb, hTjb, hTjbp⟩ := hext.params hbj
    have hpt3 : pt3 = (pt3.1, blk3.insts.size) := Prod.ext rfl hp3
    have hi3 : instAt cx.fn pt3 = some (.term (.br ls7.blocks.size [])) := by
      rw [hpt3]; exact hinstT
    have g2 := goes_br0 (fr := fr3) hi3 hTjb hTjbp
    refine SimG.goes g2 (SimG.ret ⟨rfl, Post.nil (LS.pp_eq hcj hbj) (by nat_omega) ?_ ?_⟩)
    · exact P1.same.trans (P3.same.mono (by nat_omega)) P1.mono
    · exact P3.rel.stack_eq (hstj.trans (hst6.trans hst3.symm))

def WhileClaim (n : Nat) : Prop := ∀ (c : Expr) (body : Core.Block)
    (hokC : exprOk c = true) (hokB : blockOk body = true)
    (le : LEnv) (ls ls' : LS) (hb : BlockId) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (hlow : lowerWhile hb (lowerExpr c)
      (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body) le ls = ((), ls'))
    (hpp : ls.pp = some (hb, 0)) (hext : ExtT ls' cx.fn.blocks)
    (hheader : ∃ blk, cx.fn.blocks[hb]? = some blk ∧ blk.params = []),
    ∀ fr, Rel cfg env cx fr ls →
      SimG cx (hb, 0) fr (execWhile n cfg env c body) (fun flow pt' fr' =>
        flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' [])

theorem whileClaim_zero : WhileClaim 0 := by
  intro c body hokC hokB le ls ls' hb cfg env cx hlow hpp hext hheader fr hrel
  simp only [execWhile]
  exact SimG.of_timeout

theorem whileClaim_succ (n : Nat) (ihe : ∀ e, ExprClaim n e)
    (ihb : ∀ lc want blk, BlockClaim n lc want blk) (ih : WhileClaim n) :
    WhileClaim (n + 1) := by
  intro c body hokC hokB le ls ls' hb cfg env cx hlow hpp hext hheader fr hrel
  have hlow0 := hlow
  have hheader0 := hheader
  unfold lowerWhile at hlow
  obtain ⟨cv, ls1, h1, hw⟩ := bind_eq.mp hlow
  have aw : ls1.Adv ls' := advB_whenLive () (fun _ =>
    advB_loopBody cv (fun _ _ => advB_lowerBlock _ [] false body) (advB_emitTerm _))
    _ _ _ _ hw
  have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv aw
  simp only [execWhile]
  refine SimG.bind (ihe c hokC le ls cv ls1 (hb, 0) cfg env cx fr
    h1 hpp hext1 hrel) fun va pt1 fr1 P1 => ?_
  refine SimG.expectBool fun β hva => ?_
  subst hva
  have hcv : fr1.vals[cv]? = some (.val (.bool β)) := P1.has (cv, _) (by simp)
  obtain ⟨blk1, hc1, hb1, hp1⟩ := LS.pp_some P1.pp
  rw [whenLive_some _ _ _ hc1] at hw
  unfold loopBody at hw
  simp only [bind_eq] at hw
  obtain ⟨st, lsG, hg, ⟨tb, jb⟩, lsf, hf, u2, ls2, hs1, vt, ls3, ha1,
    u4, ls4, ht, hs2⟩ := hw
  rw [get_apply] at hg
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
  have e2 : ls2 = { lsf with cur := some tb } := by
    rw [setCur_run] at hs1; exact (Prod.mk.inj hs1).2.symm
  have e5 : ls' = { ls4 with cur := some jb } := by
    rw [setCur_run] at hs2; exact (Prod.mk.inj hs2).2.symm
  have hext4 : ExtT ls4 cx.fn.blocks := by rw [e5] at hext; exact hext
  have hadv1 := advB_lowerBlock (some ⟨ls1.stack.length, jb, .jump hb⟩) [] false body _ _ _ _ ha1
  have hext3 : ExtT ls3 cx.fn.blocks := hext4.of_adv (adv_emitTerm ht)
  have hext2 : ExtT ls2 cx.fn.blocks := hext3.of_adv hadv1
  have hextf : ExtT lsf cx.fn.blocks := by rw [e2] at hext2; exact hext2
  obtain ⟨htb, hjb, hszf, hvf, hstf, hcf, hinst, hbtb, hbjb⟩ := fork_facts hf P1.pp hextf
  obtain ⟨Ttb, hTtb, hTtbp⟩ := hextf.params hbtb
  obtain ⟨Tjb, hTjb, hTjbp⟩ := hextf.params hbjb
  have hpp2 : ls2.pp = some (tb, 0) := by rw [e2]; exact LS.pp_cur hbtb
  have hst1 : ls1.stack = ls.stack := P1.rel.stack.trans hrel.stack.symm
  have hst2 : ls2.stack = ls.stack := by rw [e2]; show lsf.stack = _; rw [hstf, hst1]
  have hv2 : ls2.vals.size = ls1.vals.size := by rw [e2]; show lsf.vals.size = _; rw [hvf]
  have hrel2 : Rel cfg env cx fr1 ls2 := P1.rel.stack_eq (by rw [hst2, hst1])
  have hm1 := P1.mono
  have hinst' : instAt cx.fn pt1 = some (.term (.condbr cv tb [] jb [])) := hinst
  have a4 := adv_emitTerm ht
  have hjb3 : ls3.blocks[jb]? = some ⟨[], #[]⟩ := by
    refine hadv1.keep jb ⟨[], #[]⟩ ?_ ?_
    · rw [e2]; show some tb ≠ some jb; intro hh; have := Option.some.inj hh; nat_omega
    · rw [e2]; exact hbjb
  have hjb4 : ls4.blocks[jb]? = some ⟨[], #[]⟩ := by
    cases hce : ls3.cur with
    | none =>
      rw [emitTerm_none _ _ hce] at ht
      obtain ⟨-, rfl⟩ := Prod.mk.inj ht
      exact hjb3
    | some b3 =>
      rw [emitTerm_run _ _ hce] at ht
      obtain ⟨-, rfl⟩ := Prod.mk.inj ht
      have hb3 : b3 ≠ jb := by
        rcases hadv1.cur with h | h | ⟨c, hc, hc1, _⟩
        · rw [hce] at h; cases h
        · rw [hce, e2] at h
          have := Option.some.inj h
          nat_omega
        · rw [hce] at hc
          have := Option.some.inj hc
          have hl2 : ls2.blocks.size = ls1.blocks.size + 2 := by rw [e2]; exact hszf
          nat_omega
      show (ls3.blocks.modify b3 _)[jb]? = _
      rw [getElem?_modify_ne hb3]
      exact hjb3
  have hpp' : ls'.pp = some (jb, 0) := by rw [e5]; exact LS.pp_cur hjb4
  have hstl : ls'.stack = ls.stack := by
    rw [e5]; show ls4.stack = _
    rw [a4.stack, hadv1.stack, hst2]
  have hmono : ls.vals.size ≤ ls'.vals.size := by
    rw [e5]; show _ ≤ ls4.vals.size
    have := a4.vals; have := hadv1.vals; nat_omega
  cases β
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine SimG.goes (goes_condbr_else0 hinst' hcv hTjb hTjbp rfl) ?_
    exact SimG.ret ⟨rfl, Post.nil hpp' hmono P1.same
      (P1.rel.stack_eq (by rw [hstl, hst1]))⟩
  · simp only [↓reduceIte]
    refine SimG.goes (goes_condbr_then0 hinst' hcv hTtb hTtbp rfl) ?_
    refine SimG.bind (ihb (some ⟨ls1.stack.length, jb, .jump hb⟩) false body
      hokB le ls2 vt ls3 (tb, 0) cfg env cx fr1 ha1 hpp2 hext3 hrel2)
      fun flow pt3 fr3 ⟨v, hf, _, P3⟩ => ?_
    subst hf
    obtain ⟨-, -, -, hi3'⟩ := emitTerm_facts ht P3.pp hext4
    obtain ⟨Thb, hThb, hThbp⟩ := hheader
    have hi3 : instAt cx.fn pt3 = some (.term (.br hb [])) := hi3'
    have hst3 : ls3.stack = ls.stack := P3.rel.stack.trans hrel.stack.symm
    have hrelH : Rel cfg env cx fr3 ls := P3.rel.stack_eq hst3.symm
    refine SimG.goes (goes_br0 (fr := fr3) hi3 hThb hThbp) ((ih c body hokC hokB le ls ls' hb cfg env cx hlow0 hpp hext hheader0 fr3 hrelH).mono ?_)
    rintro flow pt' fr' ⟨hflow, P⟩
    refine ⟨hflow, ⟨P.pp, P.has, P.lt, P.mono, ?_, P.rel⟩⟩
    have hsame : Same ls.vals.size fr fr3 :=
      P1.same.trans (P3.same.mono (by rw [hv2]; exact hm1)) (Nat.le_refl _)
    exact hsame.trans P.same (Nat.le_refl _)


theorem stmtClaim_while (n : Nat) (ih : WhileClaim n) (lc : Option LoopCtx) (c : Expr) (body : Core.Block)
    (org : OriginId) (hokC : exprOk c = true) (hokB : blockOk body = true)
    (le : LEnv) (ls ls' : LS) (r : Unit) (pt : Pt) (cfg : Cfg) (env : Env) (cx : FnCtx)
    (fr : Frame) (hlow : lowerStmt lc (.while c body org) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls) :
    SimG cx pt fr (execStmt (n + 1) cfg env (.while c body org)) (fun flow pt' fr' =>
      flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) := by
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨⟨hb, ps⟩, ls1, hn, u1, ls2, ht, u2, lsH, hs, hw⟩ := hlow
  have hr : r = () := Subsingleton.elim _ _
  subst hr
  have aW := advB_lowerWhile hb (advB_lowerExpr c)
    (fun _ _ => advB_lowerBlock _ [] false body) _ _ _ _ hw
  have hextH : ExtT lsH cx.fn.blocks := hext.of_adv aW
  have eH : lsH = { ls2 with cur := some hb } := by
    rw [setCur_run] at hs; exact (Prod.mk.inj hs).2.symm
  have hext2 : ExtT ls2 cx.fn.blocks := by rw [eH] at hextH; exact hextH
  have hn0 := hn
  rw [newBlock0_run] at hn0
  obtain ⟨hids, e1⟩ := Prod.mk.inj hn0
  obtain ⟨hhb, -⟩ := Prod.mk.inj hids
  have hval1 : ls1.vals = ls.vals := by rw [← e1]
  have hst1 : ls1.stack = ls.stack := by rw [← e1]
  have hc1 : ls1.cur = ls.cur := by rw [← e1]
  obtain ⟨blk, hc, hb0, hp0⟩ := LS.pp_some hpp
  have hlt : pt.1 < ls.blocks.size := (Array.getElem?_eq_some_iff.mp hb0).1
  have hb1 : ls1.blocks[pt.1]? = some blk := by
    rw [← e1]
    exact (getElem?_push_lt hlt).trans hb0
  have hpp1 : ls1.pp = some pt := by
    have h := LS.pp_eq (hc1.trans hc) hb1
    rw [← hp0] at h
    exact h
  obtain ⟨hv2, hst2, -, hinst⟩ := emitTerm_facts ht hpp1 hext2
  have hnew : ls1.blocks[hb]? = some ⟨[], #[]⟩ := by
    rw [← hhb, ← e1]
    simp
  have hne : ls1.cur ≠ some hb := by
    rw [hc1, hc]
    intro h
    have he := Option.some.inj h
    rw [← hhb] at he
    exact Nat.ne_of_lt hlt he
  have hb2 : ls2.blocks[hb]? = some ⟨[], #[]⟩ := (adv_emitTerm ht).keep hb _ hne hnew
  have hppH : lsH.pp = some (hb, 0) := by rw [eH]; exact LS.pp_cur hb2
  obtain ⟨Thb, hThb, hThbp⟩ := hext2.params hb2
  have hrelH : Rel cfg env cx fr lsH := hrel.stack_eq (by
    rw [eH]; show ls2.stack = _; rw [hst2, hst1])
  have hsizeH : lsH.vals.size = ls.vals.size := by
    rw [eH]; show ls2.vals.size = _; rw [hv2, hval1]
  have hi : instAt cx.fn pt = some (.term (.br hb [])) := hinst
  simp only [execStmt]
  refine SimG.goes (goes_br0 hi hThb hThbp)
    ((ih c body hokC hokB le lsH ls' hb cfg env cx hw hppH hext
      ⟨Thb, hThb, hThbp⟩ fr hrelH).mono ?_)
  rintro flow pt' fr' ⟨hflow, P⟩
  refine ⟨hflow, ⟨P.pp, P.has, P.lt, ?_, ?_, P.rel⟩⟩
  · rw [← hsizeH]; exact P.mono
  · rw [← hsizeH]; exact P.same

/-! ### All claims, by induction on Core's fuel -/

structure Claims (n : Nat) : Prop where
  expr : ∀ e, ExprClaim n e
  place : ∀ p, PlaceClaim n p
  view : ∀ v, ViewClaim n v
  bound : ∀ b, BoundClaim n b
  exprs : ∀ es, ExprsClaim n es
  printArgs : ∀ args, PrintArgsClaim n args
  stmt : ∀ lc s, StmtClaim n lc s
  stmts : ∀ lc ss, StmtsClaim n lc ss
  block : ∀ lc want blk, BlockClaim n lc want blk
  blockValue : ∀ blk, BlockValueClaim n blk
  whileLoop : WhileClaim n

theorem claims_zero : Claims 0 where
  expr := fun e => by
    intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [evalExpr]; exact SimG.of_timeout
  place := fun p => by
    intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [evalPlace]; exact SimG.of_timeout
  view := fun v => by
    intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [evalView]; exact SimG.of_timeout
  bound := fun b => by
    intro hok le ls bnd ls' pt cfg env cx fr len dflt hlow hpp hext hrel
    simp only [evalBound]; exact SimG.of_timeout
  exprs := fun es => exprsClaim 0 (fun e => by
    intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [evalExpr]; exact SimG.of_timeout) es
  printArgs := fun args => printArgsClaim 0 (fun m h => absurd h (by omega)) args
  stmt := fun lc s => by
    intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [execStmt]; exact SimG.of_timeout
  stmts := stmtsClaim_zero
  block := fun lc want blk => by
    intro hok le ls r ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [execBlock]; exact SimG.of_timeout
  blockValue := blockValueClaim_zero
  whileLoop := whileClaim_zero

theorem claims_succ (n : Nat) (ih : Claims n) : Claims (n + 1) := by
  have hexpr : ∀ e, ExprClaim (n + 1) e := by
    intro e
    cases e with
    | lit t k => exact exprClaim_lit _ t k
    | bool b => exact exprClaim_bool _ b
    | read p => exact exprClaim_read n ih.place p
    | ref m p => exact exprClaim_ref n ih.place m p
    | slice m v lo hi org => exact exprClaim_slice n ih.view ih.bound m v lo hi org
    | len v => exact exprClaim_len n ih.view v
    | un op a org => exact exprClaim_un n ih.expr op a org
    | bin op a b org => exact exprClaim_bin n ih.expr op a b org
    | cmp op a b => exact exprClaim_cmp n ih.expr op a b
    | and a b => exact exprClaim_and n ih.expr a b
    | or a b => exact exprClaim_or n ih.expr a b
    | not a => exact exprClaim_not n ih.expr a
    | conv k target a org => exact exprClaim_conv n ih.expr k target a org
    | call c args org =>
      intro hok; simp [exprOk] at hok
    | push owner a org => exact exprClaim_push n ih.expr ih.place owner a org
    | pop owner org => exact exprClaim_pop n ih.place owner org
    | ifE c t f => exact exprClaim_ifE n ih.expr ih.blockValue c t f
    | blockE b => exact exprClaim_blockE n ih.blockValue b
    | arrLit t es => exact exprClaim_arrLit n ih.exprs t es
    | fill t a => exact exprClaim_fill n ih.expr t a
    | structLit t es => exact exprClaim_structLit n ih.exprs t es
  have hprint : ∀ args, PrintArgsClaim (n + 1) args :=
    printArgsClaim (n + 1) (fun m h => by cases h; exact ih.expr)
  refine ⟨hexpr, ?_, ?_, ?_, exprsClaim (n + 1) hexpr, hprint, ?_, ?_, ?_, ?_, whileClaim_succ n ih.expr ih.block ih.whileLoop⟩
  · intro p
    cases p with
    | var x => exact placeClaim_var _ x
    | global g => exact placeClaim_global _ g
    | deref e => exact placeClaim_deref n ih.expr e
    | elem v i org => exact placeClaim_elem n ih.expr ih.view v i org
    | field p i => exact placeClaim_field n ih.place p i
  · intro v
    cases v with
    | of p => exact viewClaim_of n ih.place p
    | val e => exact viewClaim_val n ih.expr e
  · intro b
    cases b with
    | omitted => exact boundClaim_omitted _
    | expr e => exact boundClaim_expr n ih.expr e
    | fromEnd e => exact boundClaim_fromEnd n ih.expr e
  · intro lc s
    cases s with
    | letS x e org => exact stmtClaim_let n lc ih.expr x e org
    | assign p e org => exact stmtClaim_assign n lc ih.expr ih.place p e org
    | assignOp op p e org => exact stmtClaim_assignOp n lc ih.expr ih.place op p e org
    | rebind x e org => exact stmtClaim_rebind n lc ih.expr x e org
    | expr e org => exact stmtClaim_expr n lc ih.expr e org
    | append owner src org => exact stmtClaim_append n lc ih.place ih.view owner src org
    | popN owner count org => exact stmtClaim_popN n lc ih.place ih.expr owner count org
    | resize owner size fill org => exact stmtClaim_resize n lc ih.place ih.expr owner size fill org
    | clear owner org => exact stmtClaim_clear n lc ih.place owner org
    | assignWhole owner replacement org => exact stmtClaim_assignWhole n lc ih.place ih.expr owner replacement org
    | ifS c t f org =>
      cases f with
      | none => exact stmtClaim_ifS_none n lc ih.expr (ih.block lc) c t org
      | some fb => exact stmtClaim_ifS_some n lc ih.expr (ih.block lc) c t fb org
    | «while» c body org =>
      intro hok
      have h : exprOk c = true ∧ blockOk body = true := by simpa [stmtOk] using hok
      intro le ls r ls' pt cfg env cx fr hlow hpp hext hrel
      exact stmtClaim_while n ih.whileLoop lc c body org h.1 h.2
        le ls ls' r pt cfg env cx fr hlow hpp hext hrel
    | forRange x lo hi body org => intro hok; simp [stmtOk] at hok
    | forEach x idx v byRef body org => intro hok; simp [stmtOk] at hok
    | ret e org => intro hok; simp [stmtOk] at hok
    | brk org => intro hok; simp [stmtOk] at hok
    | cont org => intro hok; simp [stmtOk] at hok
    | print args org => exact stmtClaim_print n lc ih.printArgs args org
    | assertS e org => exact stmtClaim_assert n lc ih.expr e org
    | abort msg org => exact stmtClaim_abort n lc msg org
    | exit e org => exact stmtClaim_exit n lc ih.expr e org
  · intro lc; exact stmtsClaim_succ n lc (ih.stmt lc) (ih.stmts lc)
  · intro lc; exact blockClaim_succ n lc (ih.stmts lc) ih.expr
  · exact blockValueClaim_succ n (ih.block none)

theorem claims (n : Nat) : Claims n := by
  induction n with
  | zero => exact claims_zero
  | succ n ih => exact claims_succ n ih

end Goose.Lower
