import Goose.Lower.Claims
import Goose.Lower.RuntimeSim

namespace Goose.Lower

open Goose.Core Goose.GIR

def CoercionValue (target : Ty) (value : Val) : Prop :=
  match target with
  | .ref .readOnly _ => ∃ loc, value = .ref loc
  | .slice .readOnly _ => ∃ loc start len, value = .slice loc start len
  | _ => True

theorem coerceTo_sim {cfg : Cfg} {env : Env} {cx : FnCtx} {le : LEnv}
    {base ls ls' : LS} {before fr : GIR.Frame} {pt : Pt} {r r' : ValueId}
    {target : Ty} {value : Val}
    (P : Post cfg env cx base before ls fr pt [(r, .val value)])
    (hshape : CoercionValue target value)
    (hlow : coerceTo target r le ls = (r', ls')) (hext : ExtT ls' cx.fn.blocks) :
    SimE cx pt fr (pure value : M Val)
      (fun result pt' fr' => result = value ∧
        Post cfg env cx base before ls' fr' pt' [(r', .val value)]) := by
  intro s
  rcases coerceTo_cases hlow with ⟨rfl, rfl⟩ | ⟨elem, rfl, hfreeze⟩ |
      ⟨elem, view, mid, rfl, hview, hslice⟩
  · exact SimEAt.ret ⟨rfl, P⟩
  · obtain ⟨loc, rfl⟩ := hshape
    have hcell := P.has (r, .val (.ref loc)) (by simp)
    have hcast := leaf_def P hfreeze hext (by simp)
      (fun v : Val => RVal.val v) (c := (pure (.ref loc) : M Val))
      (by simp [execPure, getVal_of hcell, Goose.Core.expectRef])
    exact (SimEAt.of_simG hcast s).mono fun result s1 pt' fr' hc Q => by
      have heq : result = .ref loc := ((Res.ok.inj (by simpa only [pure_apply] using hc)).1).symm
      subst result
      exact ⟨rfl, Q⟩
  · obtain ⟨loc, start, len, rfl⟩ := hshape
    have hcell := P.has (r, .val (.slice loc start len)) (by simp)
    have hextmid := hext.of_adv (adv_emitDef hslice)
    have hviewSim := leaf_def P hview hextmid (by simp)
      (fun v : ViewVal => RVal.view v) (c := (pure ⟨loc, start, len, false⟩ : M ViewVal))
      (by simp [execPure, getVal_of hcell, Goose.Core.expectSlice])
    show SimEAt cx pt fr ((pure (⟨loc, start, len, false⟩ : ViewVal) : M ViewVal) >>=
      fun _ => pure (Val.slice loc start len)) _ s
    refine SimEAt.bind (SimEAt.of_simG hviewSim s) fun sampled s1 pt1 fr1 hc Q => ?_
    have heq : sampled = (⟨loc, start, len, false⟩ : ViewVal) :=
      ((Res.ok.inj (by simpa only [pure_apply] using hc)).1).symm
    subst sampled
    have hsampled := Q.has (view, .view ⟨loc, start, len, false⟩) (by simp)
    have hsliceSim := leaf_def Q hslice hext (by simp)
      (fun v : Val => RVal.val v) (c := (pure (.slice loc start len) : M Val)) (by
        simp [execPure, getView_of hsampled, evalBnd])
    exact (SimEAt.of_simG hsliceSim s1).mono fun result s2 pt' fr' hc' R => by
      have heq : result = .slice loc start len := ((Res.ok.inj (by simpa only [pure_apply] using hc')).1).symm
      subst result
      exact ⟨rfl, R.sub (by simp)⟩

end Goose.Lower
