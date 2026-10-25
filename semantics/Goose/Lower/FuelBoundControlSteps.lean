import Goose.Lower.FuelBoundTyped
import Goose.Lower.ReflectionBranchesSteps

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem FuelBoundM.effect_of_eq {fn : Func} {fr : Frame} {e : Effect}
    {source : Nat → M α} {nextFrame : α → Frame} {state : St} {fuel sourceFuel : Nat}
    (equal : execEff fn fr e = source sourceFuel >>= fun value => pure (nextFrame value)) :
    FuelBoundM sourceFuel fuel (fun n => source n >>= fun value => pure (nextFrame value))
      (fun _ => execEff fn fr e) state := by
  intro result final run
  change execEff fn fr e state = result at run
  rw [equal] at run
  exact run

theorem FuelBoundAt.br1 {cx : FnCtx} {pt : Pt} {fr : Frame} {b : BlockId} {blk : GIR.Block}
    {v p : ValueId} {ty : VTy} {x : RVal} {sourceFuel fuel : Nat} {state : St}
    {source : Nat → M α} {post : α → St → Pt → Frame → Prop}
    (instruction : instAt cx.fn pt = some (.term (.br b [v])))
    (blockAt : cx.fn.blocks[b]? = some blk) (parameters : blk.params = [(p,ty)])
    (value : fr.vals[v]? = some x)
    (reflection : FuelBoundAt sourceFuel fuel cx (b,0) (fr.set p x) source post state) :
    FuelBoundAt sourceFuel (fuel + 1) cx pt fr source post state :=
  FuelBoundAt.step (congrFun (runAt_br1_step instruction blockAt parameters value fuel) state) reflection


theorem FuelBoundAt.condbr_take0 {cx : FnCtx} {pt : Pt} {fr : Frame} {c : ValueId}
    {tb eb : BlockId} {targs eargs : List ValueId} {blk : GIR.Block} {selected : Bool}
    {sourceFuel fuel : Nat} {state : St} {source : Nat → M α} {post : α → St → Pt → Frame → Prop}
    (instruction : instAt cx.fn pt = some (.term (.condbr c tb targs eb eargs)))
    (condition : fr.vals[c]? = some (.val (.bool selected)))
    (blockAt : cx.fn.blocks[if selected then tb else eb]? = some blk)
    (parameters : blk.params = []) (arguments : (if selected then targs else eargs) = [])
    (reflection : FuelBoundAt sourceFuel fuel cx (if selected then tb else eb,0) fr source post state) :
    FuelBoundAt sourceFuel (fuel + 1) cx pt fr source post state :=
  FuelBoundAt.step (congrFun
    (runAt_condbr_take0_step instruction condition blockAt parameters arguments fuel) state) reflection


theorem FuelBoundAt.condbr_take1 {cx : FnCtx} {pt : Pt} {fr : Frame} {c v p : ValueId}
    {tb eb : BlockId} {targs eargs : List ValueId} {blk : GIR.Block} {selected : Bool}
    {ty : VTy} {x : RVal} {sourceFuel fuel : Nat} {state : St}
    {source : Nat → M α} {post : α → St → Pt → Frame → Prop}
    (instruction : instAt cx.fn pt = some (.term (.condbr c tb targs eb eargs)))
    (condition : fr.vals[c]? = some (.val (.bool selected)))
    (blockAt : cx.fn.blocks[if selected then tb else eb]? = some blk)
    (parameters : blk.params = [(p,ty)]) (arguments : (if selected then targs else eargs) = [v])
    (value : fr.vals[v]? = some x)
    (reflection : FuelBoundAt sourceFuel fuel cx (if selected then tb else eb,0) (fr.set p x) source post state) :
    FuelBoundAt sourceFuel (fuel + 1) cx pt fr source post state :=
  FuelBoundAt.step (congrFun
    (runAt_condbr_take1_step instruction condition blockAt parameters arguments value fuel) state) reflection


theorem FuelBoundAt.br0 {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {blockId : BlockId} {block : GIR.Block}
    {source : Nat → M α} {post : α → St → Pt → GIR.Frame → Prop} {state : St} {sourceFuel fuel : Nat}
    (instruction : instAt cx.fn pt = some (.term (.br blockId [])))
    (blockAt : cx.fn.blocks[blockId]? = some block) (parameters : block.params = [])
    (reflection : FuelBoundAt sourceFuel fuel cx (blockId,0) fr source post state) :
    FuelBoundAt sourceFuel (fuel + 1) cx pt fr source post state :=
  FuelBoundAt.step (congrFun (runAt_br0_step instruction blockAt parameters fuel) state) reflection


theorem FuelBoundAt.condbr {cx : FnCtx} {pt : Pt} {fr : GIR.Frame} {condition : ValueId}
    {yes no : BlockId} {yesBlock noBlock : GIR.Block} {selected : Bool}
    {source : Nat → M α} {post : α → St → Pt → GIR.Frame → Prop} {state : St} {sourceFuel fuel : Nat}
    (instruction : instAt cx.fn pt = some (.term (.condbr condition yes [] no [])))
    (value : fr.vals[condition]? = some (.val (.bool selected)))
    (yesAt : cx.fn.blocks[yes]? = some yesBlock) (yesParameters : yesBlock.params = [])
    (noAt : cx.fn.blocks[no]? = some noBlock) (noParameters : noBlock.params = [])
    (reflection : FuelBoundAt sourceFuel fuel cx (if selected then (yes,0) else (no,0)) fr source post state) :
    FuelBoundAt sourceFuel (fuel + 1) cx pt fr source post state :=
  FuelBoundAt.step (congrFun
    (runAt_condbr_step instruction value yesAt yesParameters noAt noParameters fuel) state) reflection


theorem FuelBoundAt.eff_step {cx : FnCtx} {pt : Pt} {fr : Frame} {e : Effect}
    {source : Nat → M α} {nextFrame : α → Frame} {sourceFuel fuel : Nat} {state : St}
    (instruction : instAt cx.fn pt = some (.eff e))
    (equal : execEff cx.fn fr e =
      source sourceFuel >>= fun value => pure (nextFrame value)) :
    FuelBoundAt sourceFuel (fuel + 1) cx pt fr source
      (fun value _ pt' fr' => pt' = (pt.1, pt.2 + 1) ∧ fr' = nextFrame value) state := by
  have operation : FuelBoundM sourceFuel fuel
      (fun n => source n >>= fun value => pure (nextFrame value))
      (fun _ => execEff cx.fn fr e) state :=
    FuelBoundM.effect_of_eq (nextFrame := nextFrame) equal
  intro result nonTimeout run
  have step : runAt cx pt fr (fuel + 1) state =
      (execEff cx.fn fr e >>= fun frame => runAt cx (pt.1, pt.2 + 1) frame fuel) state := by
    simp only [runAt, instsAt_cons instruction, exec]
  rw [step, bind_apply] at run
  cases effectRun : execEff cx.fn fr e state with
  | ok frame after =>
      rw [effectRun] at run
      have sourceRun := operation (.ok frame after) (NonTimeout.ok _ _) effectRun
      change (source sourceFuel >>= fun value => pure (nextFrame value)) state = .ok frame after at sourceRun
      rw [bind_apply] at sourceRun
      cases hsource : source sourceFuel state with
      | stop stop sourceAfter => rw [hsource] at sourceRun; cases sourceRun
      | ok value sourceAfter =>
          rw [hsource] at sourceRun
          cases sourceRun
          exact Or.inl ⟨value, after, (pt.1, pt.2 + 1), nextFrame value,
            fuel, rfl, ⟨rfl, rfl⟩, by omega, run⟩
  | stop stop after =>
      rw [effectRun] at run
      have nonTimeoutEffect : NonTimeout (Res.stop stop after : Res Frame) := by
        intro timeoutState equalTimeout
        cases equalTimeout
        exact nonTimeout after run.symm
      have sourceRun := operation (.stop stop after) nonTimeoutEffect effectRun
      change (source sourceFuel >>= fun value => pure (nextFrame value)) state = .stop stop after at sourceRun
      rw [bind_apply] at sourceRun
      cases hsource : source sourceFuel state with
      | ok value sourceAfter => rw [hsource] at sourceRun; cases sourceRun
      | stop sourceStop sourceAfter =>
          rw [hsource] at sourceRun
          cases sourceRun
          exact Or.inr ⟨stop, after, rfl, run.symm⟩

theorem FuelBoundAt.mono_success {sourceFuel fuel : Nat} {cx : FnCtx} {pt : Pt} {fr : Frame}
    {source : Nat → M α} {p q : α → St → Pt → Frame → Prop} {state : St}
    (bounded : FuelBoundAt sourceFuel fuel cx pt fr source p state)
    (weaken : ∀ value after pt' fr', source sourceFuel state = .ok value after →
      p value after pt' fr' → q value after pt' fr') :
    FuelBoundAt sourceFuel fuel cx pt fr source q state := by
  intro result final run
  rcases bounded result final run with success | stopped
  · obtain ⟨value,after,pt',fr',residual,done,matched,bound,continuation⟩ := success
    exact Or.inl ⟨value,after,pt',fr',residual,done,weaken value after pt' fr' done matched,bound,continuation⟩
  · exact Or.inr stopped

theorem FuelBoundAt.typed_bool {sourceFuel fuel : Nat} {cfg : Cfg} {env : Env} {expression : Expr}
    {state : St} {cx : FnCtx} {pt : Pt} {fr : Frame} {post : Val → St → Pt → Frame → Prop}
    (source : ExprSource cfg env expression state) (type : source.ty = .bool)
    (bounded : FuelBoundAt sourceFuel fuel cx pt fr (fun n => evalExpr n cfg env expression) post state) :
    FuelBoundAt sourceFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expression >>= expectBool)
      (fun boolean after pt' fr' => post (.bool boolean) after pt' fr') state := by
  refine bounded.bind ?_
  intro value after pt' fr' done matched residual bound
  have typed := (source.result sourceFuel value done).typed
  rw [type] at typed
  obtain ⟨boolean,rfl⟩ := Core.Sound.hasTy_bool typed
  exact FuelBoundAt.ret matched

theorem leaf_eff_fuelBoundAt {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls middle after : LS} {fr before : Frame} {pt : Pt} {cells : List (ValueId × RVal)}
    {fuel sourceFuel : Nat} {state : St}
    (post : Post cfg env cx ls fr middle before pt cells) {effect : Effect} {le : LEnv}
    (emit : emitEffect effect le middle = ((),after)) (extension : ExtT after cx.fn.blocks)
    {source : Nat → M α}
    (equal : execEff cx.fn before effect = source sourceFuel >>= fun _ => pure before) :
    FuelBoundAt sourceFuel (fuel + 1) cx pt before source
      (fun _ _ pt' fr' => Post cfg env cx ls fr after fr' pt' []) state := by
  obtain ⟨next,instruction⟩ := Post.eff_leaf post emit extension
  refine (FuelBoundAt.eff_step instruction equal).mono ?_
  intro value final pt' fr' matched
  rcases matched with ⟨rfl,rfl⟩
  exact next

#print axioms FuelBoundAt.eff_step
#print axioms FuelBoundAt.condbr_take1
#print axioms FuelBoundAt.typed_bool

end Goose.Lower
