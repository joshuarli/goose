import Goose.Lower.ReflectionIterationsSteps
import Goose.Lower.ReflectionBlocks
import Goose.Lower.EachReentry

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel Goose.Proofs.Memory

theorem leaf_def_reflectAtFuel_atState {cfg : Cfg} {env : Env} {cx : FnCtx} {ls lsk after : LS}
    {fr frk : Frame} {pt : Pt} {cells : List (ValueId × RVal)} {fuel sourceFuel : Nat} {state : St}
    (post : Post cfg env cx ls fr lsk frk pt cells) {op : Op} {le : LEnv} {id : ValueId}
    (emit : emitDef op le lsk = (id,after)) (extension : ExtT after cx.fn.blocks)
    (noncall : ∀ f args org, op ≠ .call f args org) {source : Nat → M α} (inject : α → RVal)
    (equal : execPure cx frk op state = (source sourceFuel >>= fun value => pure (inject value)) state) :
    ReflectAtFuel fuel cx pt frk source
      (fun value _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(id,inject value)]) state := by
  cases fuel with
  | zero => exact ReflectAtFuel.zero _ _ _ _ _ _
  | succ fuel =>
    have instruction := (Post.def_leaf post emit extension (.val .unit)).2
    have operation : ∀ n, execOp n cx frk op = execPure cx frk op := by
      intro n
      cases op with
      | call f args org => exact (noncall f args org rfl).elim
      | _ => unfold execOp; rfl
    have reflected : ReflectMFuel fuel (fun n => source n >>= fun value => pure (inject value))
        (fun n => execOp n cx frk op) state := ReflectMFuel.of_eq (by rw [operation]; exact equal)
    refine (ReflectAtFuel.def_step inject instruction reflected).mono ?_
    rintro value after pt' fr' ⟨rfl,rfl⟩
    exact (Post.def_leaf post emit extension (inject value)).1

theorem eachLen_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx} {le : LEnv} {ls after : LS}
    {counter view sampled result : ValueId} {owner : Option ValueId} {vw : ViewVal}
    {base fr : Frame} {i : Nat} {pt : Pt} (fuel : Nat) (state : St)
    (typed : Core.Sound.EachViewOk state.store vw element)
    (invariant : EachInv cfg env cx ls counter view sampled owner vw base i fr)
    (counterBound : counter < ls.vals.size) (viewBound : view < counter)
    (ownerBound : vw.resizable = true → owner.getD 0 < counter)
    (sampledBound : vw.resizable = false → sampled < counter)
    (lowering : eachLen vw.resizable owner sampled le ls = (result,after))
    (point : ls.pp = some pt) (extension : ExtT after cx.fn.blocks) :
    ReflectAtFuel fuel cx pt fr (fun _ => if vw.resizable then lengthLoc vw.loc else pure vw.len)
      (fun len _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(result,.val (.int .i64 len))] ∧
        EachInv cfg env cx after counter view sampled owner vw base i fr') state := by
  cases resizable : vw.resizable with
  | false =>
    simp only [resizable,Bool.false_eq_true,ite_false,eachLen,pure_run] at lowering ⊢
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj lowering
    have post : Post cfg env cx ls fr ls fr pt [(sampled,.val (.int .i64 vw.len))] :=
      ⟨point,by simpa using invariant.sampledValue resizable,
        by simpa using Nat.lt_trans (sampledBound resizable) counterBound,Nat.le_refl _,Same.refl _ _,invariant.rel⟩
    exact ReflectAtFuel.ret fuel ⟨post,invariant⟩
  | true =>
    simp only [resizable,ite_true,eachLen] at lowering ⊢
    have ownerValue := invariant.ownerValue resizable
    have equal : execPure cx fr (.arrayLen (owner.getD 0)) state =
        (lengthLoc vw.loc >>= fun len => pure (RVal.val (.int .i64 len))) state := by
      obtain ⟨_,owned⟩ := typed.2.2 resizable
      rcases owned with owned | owned
      all_goals
        obtain ⟨value,read,flat⟩ := owned
        cases value <;> simp only [FlatTy] at flat
        simp [execPure,getVal_of ownerValue,expectRef,readLoc,read,expectArray,lengthLoc,
          Store.length,bind_apply,pure_apply]
    have reflected := leaf_def_reflectAtFuel_atState (fuel := fuel) (Post.init invariant.rel point)
      lowering extension (by simp) (source := fun _ => lengthLoc vw.loc) (sourceFuel := 0)
      (fun len => .val (.int .i64 len)) equal
    exact reflected.mono (fun len after pt' fr' post =>
      ⟨post,invariant.of_post post counterBound viewBound ownerBound sampledBound⟩)

theorem eachElemValue_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls middle after : LS} {fr before : Frame} {pt : Pt} {elem value : ValueId} {loc : Loc}
    (fuel : Nat) (state : St)
    (post : Post cfg env cx ls fr middle before pt [(elem,.val (.ref loc))])
    (x : VarId) (byRef : Bool) (le : LEnv)
    (lowering : eachElemValue x byRef elem le middle = (value,after))
    (extension : ExtT after cx.fn.blocks) :
    ReflectAtFuel fuel cx pt before (fun _ => if byRef then pure (Val.ref loc) else readLoc loc)
      (fun v _ pt' fr' => Post cfg env cx ls fr after fr' pt' [(value,.val v)]) state := by
  have cell := post.has (elem,.val (.ref loc)) (by simp)
  cases byRef with
  | false =>
    simp only [eachElemValue,Bool.false_eq_true,ite_false] at lowering ⊢
    apply leaf_def_reflectAtFuel post lowering extension (by simp) RVal.val (sourceFuel := 0)
    simp [execPure,getVal_of cell,expectRef]
  | true =>
    simp only [ite_true]
    rcases eachElemValue_ref_cases lowering with ⟨rfl,rfl⟩ | frozen
    · exact ReflectAtFuel.ret fuel post
    · apply leaf_def_reflectAtFuel post frozen extension (by simp) RVal.val (sourceFuel := 0)
      simp [execPure,getVal_of cell,expectRef]

end Goose.Lower
