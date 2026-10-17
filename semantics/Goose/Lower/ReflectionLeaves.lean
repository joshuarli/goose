import Goose.Lower.Leaf
import Goose.Lower.ReflectionFuel

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem leaf_def_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx} {ls lsk ls1 : LS}
    {fr frk : Frame} {ptk : Pt} {cellsk : List (ValueId × RVal)}
    {fuel sourceFuel : Nat} {state : St}
    (hP : Post cfg env cx ls fr lsk frk ptk cellsk) {op : Op} {le : LEnv} {r : ValueId}
    (h : emitDef op le lsk = (r, ls1)) (hext : ExtT ls1 cx.fn.blocks)
    (hnc : ∀ f args org, op ≠ .call f args org) {α : Type} {source : Nat → M α}
    (inj : α → RVal)
    (hx : execPure cx frk op = source sourceFuel >>= fun value => pure (inj value)) :
    ReflectAtFuel fuel cx ptk frk source
      (fun value _ pt' fr' => Post cfg env cx ls fr ls1 fr' pt' [(r, inj value)]) state := by
  have instruction := (Post.def_leaf hP h hext (.val .unit)).2
  cases fuel with
  | zero => exact ReflectAtFuel.zero cx ptk frk source _ state
  | succ fuel =>
    have hop : ∀ n, execOp n cx frk op = execPure cx frk op := by
      intro n
      cases op with
      | call f args org => exact (hnc f args org rfl).elim
      | _ => unfold execOp; rfl
    have operation : ReflectMFuel fuel
        (fun n => source n >>= fun value => pure (inj value))
        (fun n => execOp n cx frk op) state :=
      ReflectMFuel.of_eq (by rw [hop fuel, hx])
    refine (ReflectAtFuel.def_step inj instruction operation).mono ?_
    intro value after pt' fr' matched
    rcases matched with ⟨rfl, rfl⟩
    exact (Post.def_leaf hP h hext (inj value)).1

theorem lowerExpr_lit_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls1 : LS}
    {fr : Frame} {pt : Pt} {le : LEnv} {r : ValueId} {fuel : Nat}
    (hrel : Rel cfg env cx fr ls) (hpp : ls.pp = some pt)
    (hlow : lowerExpr (.lit t value) le ls = (r, ls1)) (hext : ExtT ls1 cx.fn.blocks) :
    ReflectAtFuel fuel cx pt fr (fun n => evalExpr n cfg env (.lit t value))
      (fun result _ pt' fr' =>
        Post cfg env cx ls fr ls1 fr' pt' [(r, .val result)]) state := by
  have hdef : emitDef (.constInt t value) le ls = (r, ls1) := by
    simpa only [lowerExpr] using hlow
  have hx : execPure cx fr (.constInt t value) =
      evalExpr 1 cfg env (.lit t value) >>= fun result => pure (.val result) := by
    simp [execPure, evalExpr]
  exact leaf_def_reflectAtFuel (Post.init hrel hpp) hdef hext
    (by intro f args org h; cases h) (.val ·) (sourceFuel := 1) hx

theorem lowerExpr_bool_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls1 : LS}
    {fr : Frame} {pt : Pt} {le : LEnv} {r : ValueId} {fuel : Nat}
    (hrel : Rel cfg env cx fr ls) (hpp : ls.pp = some pt)
    (hlow : lowerExpr (.bool value) le ls = (r, ls1)) (hext : ExtT ls1 cx.fn.blocks) :
    ReflectAtFuel fuel cx pt fr (fun n => evalExpr n cfg env (.bool value))
      (fun result _ pt' fr' =>
        Post cfg env cx ls fr ls1 fr' pt' [(r, .val result)]) state := by
  have hdef : emitDef (.constBool value) le ls = (r, ls1) := by
    simpa only [lowerExpr] using hlow
  have hx : execPure cx fr (.constBool value) =
      evalExpr 1 cfg env (.bool value) >>= fun result => pure (.val result) := by
    simp [execPure, evalExpr]
  exact leaf_def_reflectAtFuel (Post.init hrel hpp) hdef hext
    (by intro f args org h; cases h) (.val ·) (sourceFuel := 1) hx

theorem lowerPlace_var_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls1 : LS}
    {fr : Frame} {pt : Pt} {le : LEnv} {r : ValueId} {fuel : Nat}
    (hrel : Rel cfg env cx fr ls) (hpp : ls.pp = some pt)
    (hlow : lowerPlace (.var x) le ls = (r, ls1)) (hext : ExtT ls1 cx.fn.blocks) :
    ReflectAtFuel fuel cx pt fr (fun n => evalPlace n cfg env (.var x))
      (fun result _ pt' fr' =>
        Post cfg env cx ls fr ls1 fr' pt' [(r, .val (.ref result))]) state := by
  have hdef : emitDef (.slotAddr x) le ls = (r, ls1) := by
    simpa only [lowerPlace] using hlow
  have hx : execPure cx fr (.slotAddr x) =
      evalPlace 1 cfg env (.var x) >>= fun result => pure (.val (.ref result)) := by
    simp only [execPure]
    rw [slotRoot_eq hrel x]
    simp [evalPlace]
  exact leaf_def_reflectAtFuel (Post.init hrel hpp) hdef hext
    (by intro f args org h; cases h) (fun result => .val (.ref result))
    (sourceFuel := 1) hx

theorem lowerPlace_global_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls1 : LS}
    {fr : Frame} {pt : Pt} {le : LEnv} {r : ValueId} {fuel : Nat}
    (hrel : Rel cfg env cx fr ls) (hpp : ls.pp = some pt)
    (hlow : lowerPlace (.global g) le ls = (r, ls1)) (hext : ExtT ls1 cx.fn.blocks) :
    ReflectAtFuel fuel cx pt fr (fun n => evalPlace n cfg env (.global g))
      (fun result _ pt' fr' =>
        Post cfg env cx ls fr ls1 fr' pt' [(r, .val (.ref result))]) state := by
  have hdef : emitDef (.globalAddr g) le ls = (r, ls1) := by
    simpa only [lowerPlace] using hlow
  have hx : execPure cx fr (.globalAddr g) =
      evalPlace 1 cfg env (.global g) >>= fun result => pure (.val (.ref result)) := by
    simp [execPure, evalPlace]
  exact leaf_def_reflectAtFuel (Post.init hrel hpp) hdef hext
    (by intro f args org h; cases h) (fun result => .val (.ref result))
    (sourceFuel := 1) hx

end Goose.Lower
