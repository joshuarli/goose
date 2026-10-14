import Goose.Lower.Claims

namespace Goose.Lower

open Goose.Core Goose.GIR

def ExprLowerClaim (n : Nat) (e : Expr) : Prop :=
  ∀ (le : LEnv) (ls : LS) (r : ValueId) (ls' : LS) (pt : Pt) (cfg : Cfg)
    (env : Env) (cx : FnCtx) (fr : Frame), lowerExpr e le ls = (r, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    SimG cx pt fr (evalExpr n cfg env e) (fun v pt' fr' =>
      Post cfg env cx ls fr ls' fr' pt' [(r, .val v)])

def PlaceLowerClaim (n : Nat) (p : Place) : Prop :=
  ∀ (le : LEnv) (ls : LS) (r : ValueId) (ls' : LS) (pt : Pt) (cfg : Cfg)
    (env : Env) (cx : FnCtx) (fr : Frame), lowerPlace p le ls = (r, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    SimG cx pt fr (evalPlace n cfg env p) (fun l pt' fr' =>
      Post cfg env cx ls fr ls' fr' pt' [(r, .val (.ref l))])

def ArgClaim (n : Nat) (a : Arg) : Prop :=
  ∀ (le : LEnv) (ls : LS) (r : ValueId) (ls' : LS) (pt : Pt) (cfg : Cfg)
    (env : Env) (cx : FnCtx) (fr : Frame), lowerArg a le ls = (r, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    SimG cx pt fr (evalArg n cfg env a) (fun v pt' fr' =>
      Post cfg env cx ls fr ls' fr' pt' [(r, .val v)])

def ArgsClaim (n : Nat) (args : List Arg) : Prop :=
  ∀ (le : LEnv) (ls : LS) (rs : List ValueId) (ls' : LS) (pt : Pt) (cfg : Cfg)
    (env : Env) (cx : FnCtx) (fr : Frame), lowerArgs args le ls = (rs, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    SimG cx pt fr (mapList (evalArg n cfg env) args) (fun vs pt' fr' =>
      rs.length = vs.length ∧ Post cfg env cx ls fr ls' fr' pt' (cellsOf rs vs))

theorem ExprClaim.toLowerClaim {n : Nat} {e : Expr} (h : ExprClaim n e)
    (hok : exprOk e = true) : ExprLowerClaim n e := h hok

theorem PlaceClaim.toLowerClaim {n : Nat} {p : Place} (h : PlaceClaim n p)
    (hok : placeOk p = true) : PlaceLowerClaim n p := h hok

theorem argClaim_zero (a : Arg) : ArgClaim 0 a := by
  intro le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [evalArg]
  exact SimG.of_timeout

theorem argClaim_byVal {n : Nat} {e : Expr} (he : ExprLowerClaim n e) :
    ArgClaim (n + 1) (.byVal e) := by
  intro le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerArg] at hlow
  simp only [evalArg]
  exact he le ls r ls' pt cfg env cx fr hlow hpp hext hrel

theorem argClaim_byRef {n : Nat} {p : Place} (hp : PlaceLowerClaim n p)
    (m : Mutability) : ArgClaim (n + 1) (.byRef m p) := by
  intro le ls r ls' pt cfg env cx fr hlow hpp hext hrel
  simp only [lowerArg, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, h2⟩ := hlow
  rcases freezeTo_cases h2 with ⟨hr, hls⟩ | hf
  · subst hr; subst hls
    simp only [evalArg]
    refine SimG.bind (hp le ls r ls' pt cfg env cx fr h1 hpp hext hrel)
      fun l pt1 fr1 P1 => ?_
    exact SimG.ret P1
  · have hext1 : ExtT ls1 cx.fn.blocks := hext.of_adv (adv_emitDef hf)
    simp only [evalArg]
    refine SimG.bind (hp le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel)
      fun l pt1 fr1 P1 => ?_
    have hc : fr1.vals[rp]? = some (.val (.ref l)) := P1.has (rp, _) (by simp)
    refine leaf_def P1 hf hext (by simp) RVal.val ?_
    simp only [execPure, getVal_of hc, Goose.Core.expectRef, pure_bind]

theorem argsClaim {n : Nat} : ∀ (args : List Arg),
    (∀ a ∈ args, ArgClaim n a) → ArgsClaim n args
  | [], _ => by
    intro le ls rs ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [lowerArgs, pure_run] at hlow
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
    simp only [mapList]
    exact SimG.ret ⟨rfl, by simpa [cellsOf] using Post.init hrel hpp⟩
  | a :: args, ha => by
    intro le ls rs ls' pt cfg env cx fr hlow hpp hext hrel
    simp only [lowerArgs, bind_eq] at hlow
    obtain ⟨r, ls1, h1, rest, ls2, h2, h3⟩ := hlow
    rw [pure_run] at h3
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
    have hext1 : ExtT ls1 cx.fn.blocks :=
      hext.of_adv (advB_lowerArgs args _ _ _ _ h2)
    simp only [mapList]
    refine SimG.bind (ha a (by simp) le ls r ls1 pt cfg env cx fr h1 hpp hext1 hrel)
      fun va pt1 fr1 P1 => ?_
    refine SimG.bind (argsClaim args (fun b hb => ha b (by simp [hb])) le ls1 rest ls2
      pt1 cfg env cx fr1 h2 P1.pp hext P1.rel) fun vas pt2 fr2 ⟨hlen, P2⟩ => ?_
    exact SimG.ret ⟨by simp [hlen], by simpa [cellsOf] using P1.comp P2⟩

end Goose.Lower
