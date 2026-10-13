import Goose.Lower.Claims

namespace Goose.Lower

open Goose.Core Goose.GIR

/-- The condition reaches the body or the exit, preserving the corresponding frame invariant.
The invariant may retain values computed before the loop and the active scope instances. -/
def WhileCondition (cx : FnCtx) (cfg : Cfg) (env : Env) (c : Expr)
    (header body : Pt) (headerInv bodyInv : Frame → Prop)
    (post : Flow → Pt → Frame → Prop) : Prop :=
  ∀ n fr, headerInv fr → SimG cx header fr (evalExpr n cfg env c >>= expectBool)
    (fun b pt' fr' => if b then pt' = body ∧ bodyInv fr'
      else post (.normal .unit) pt' fr')

/-- A normal body completion reaches the same header with its invariant restored.
This premise excludes break, continue and return; abort and exit are still simulated. -/
def WhileBody (cx : FnCtx) (cfg : Cfg) (env : Env) (blk : Core.Block)
    (header body : Pt) (headerInv bodyInv : Frame → Prop) : Prop :=
  ∀ n fr, bodyInv fr → SimG cx body fr (execBlock n cfg env [] blk)
    (fun flow pt' fr' => ∃ v frh, flow = .normal v ∧ headerInv frh ∧
      Goes cx pt' fr' header frh)

/-- Core fuel induction composes condition and body simulations for any number of iterations.
The condition and body premises still have to be discharged for the concrete builder output. -/
theorem while_sim (cx : FnCtx) (cfg : Cfg) (env : Env) (c : Expr) (blk : Core.Block)
    (header body : Pt) (headerInv bodyInv : Frame → Prop)
    (post : Flow → Pt → Frame → Prop)
    (hc : WhileCondition cx cfg env c header body headerInv bodyInv post)
    (hb : WhileBody cx cfg env blk header body headerInv bodyInv) :
    ∀ n fr, headerInv fr → SimG cx header fr (execWhile n cfg env c blk) post := by
  intro n
  induction n with
  | zero =>
    intro fr _
    simp only [execWhile]
    exact SimG.of_timeout
  | succ n ih =>
    intro fr hinv
    simp only [execWhile, ← bind_assoc]
    refine SimG.bind (hc n fr hinv) fun b pt1 fr1 hcond => ?_
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hcond ⊢
      exact SimG.ret hcond
    · simp only [↓reduceIte] at hcond ⊢
      obtain ⟨rfl, hinv1⟩ := hcond
      refine SimG.bind (hb n fr1 hinv1) fun flow pt2 fr2 hbody => ?_
      obtain ⟨v, frh, rfl, hinvh, hback⟩ := hbody
      exact SimG.goes hback (ih frh hinvh)

/-- A counting loop's branch either enters its body with the sampled counter, or exits. -/
def RangeBranch (cx : FnCtx) (header body : Pt) (hi : Int)
    (headerInv bodyInv : Int → Frame → Prop) (post : Flow → Pt → Frame → Prop) : Prop :=
  ∀ i fr, headerInv i fr →
    if i < hi then ∃ frb, bodyInv i frb ∧ Goes cx header fr body frb
    else ∃ pt' fr', post (.normal .unit) pt' fr' ∧ Goes cx header fr pt' fr'

/-- Each body receives the current counter in its own scope and returns to the incremented header.
The sampled upper bound is unchanged throughout the induction. -/
def RangeBody (cx : FnCtx) (cfg : Cfg) (env : Env) (x : VarId) (t : IntTy)
    (blk : Core.Block) (header body : Pt) (headerInv bodyInv : Int → Frame → Prop) : Prop :=
  ∀ n i fr, bodyInv i fr → SimG cx body fr (execBlock n cfg env [(x, .int t i)] blk)
    (fun flow pt' fr' => ∃ v frh, flow = .normal v ∧ headerInv (i + 1) frh ∧
      Goes cx pt' fr' header frh)

/-- The same Core fuel induction for a range with bounds already sampled.
This proves iteration composition; it does not assert that lowering establishes the premises. -/
theorem range_sim (cx : FnCtx) (cfg : Cfg) (env : Env) (x : VarId) (t : IntTy)
    (hi : Int) (blk : Core.Block) (header body : Pt)
    (headerInv bodyInv : Int → Frame → Prop) (post : Flow → Pt → Frame → Prop)
    (hc : RangeBranch cx header body hi headerInv bodyInv post)
    (hb : RangeBody cx cfg env x t blk header body headerInv bodyInv) :
    ∀ n i fr, headerInv i fr → SimG cx header fr (execRange n cfg env x t i hi blk) post := by
  intro n
  induction n with
  | zero =>
    intro i fr _
    simp only [execRange]
    exact SimG.of_timeout
  | succ n ih =>
    intro i fr hinv
    simp only [execRange]
    have hbranch := hc i fr hinv
    by_cases hlt : i < hi
    · simp only [hlt, ↓reduceIte] at hbranch ⊢
      obtain ⟨frb, hinvb, hgo⟩ := hbranch
      refine SimG.goes hgo (SimG.bind (hb n i frb hinvb) fun flow pt1 fr1 hbody => ?_)
      obtain ⟨v, frh, rfl, hinvh, hback⟩ := hbody
      exact SimG.goes hback (ih (i + 1) frh hinvh)
    · simp only [hlt, ↓reduceIte] at hbranch ⊢
      obtain ⟨pt', fr', hpost, hgo⟩ := hbranch
      exact SimG.goes hgo (SimG.ret hpost)

/-- A range back edge may replace its counter while retaining every older value, including
the sampled upper bound. Its invariant must protect this prefix rather than the counter cell. -/
theorem range_reentry_keeps_prefix (fr : Frame) (counter : ValueId) (t : IntTy) (i : Int) :
    Same counter fr (fr.set counter (.val (.int t (i + 1)))) :=
  Same.set fr (Nat.le_refl _) _

/-- Requiring the old counter itself to survive a back edge contradicts its increment. -/
theorem range_reentry_changes_counter (fr : Frame) (counter : ValueId) (t : IntTy) (i : Int)
    (hcounter : fr.vals[counter]? = some (.val (.int t i))) :
    ¬ Same (counter + 1) fr (fr.set counter (.val (.int t (i + 1)))) := by
  intro hsame
  have h := hsame counter (by omega)
  rw [Frame.set_get, hcounter] at h
  have hi : i + 1 = i := by simpa using h
  omega

end Goose.Lower
