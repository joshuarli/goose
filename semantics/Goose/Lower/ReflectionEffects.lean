import Goose.Lower.Leaf
import Goose.Lower.ReflectionFuel

namespace Goose.Lower

open Goose.Core Goose.GIR

def ReturnEndpoint (cx : FnCtx) (pt : Pt) (fr : Frame) (value : Val) : Prop :=
  ∃ ids org, instAt cx.fn pt = some (.term (.ret ids org)) ∧
    ((ids = [] ∧ value = .unit) ∨
      ∃ id, ids = [id] ∧ fr.vals[id]? = some (.val value))

theorem ReturnEndpoint.run {cx : FnCtx} {pt : Pt} {fr : Frame} {value : Val}
    (endpoint : ReturnEndpoint cx pt fr value) (state : St) :
    ∀ extra, runAt cx pt fr (extra + 1) state = .ok value state := by
  intro extra
  obtain ⟨ids, org, instruction, result⟩ := endpoint
  rcases result with ⟨rfl, rfl⟩ | ⟨id, rfl, cell⟩
  · rw [runAt_ret0 instruction extra]
    rfl
  · rw [runAt_ret1 instruction cell extra]
    rfl

theorem ReflectMFuel.effect_of_eq {fn : Func} {fr : Frame} {e : Effect}
    {source : Nat → M α} {nextFrame : α → Frame} {state : St} {fuel sourceFuel : Nat}
    (equal : execEff fn fr e = source sourceFuel >>= fun value => pure (nextFrame value)) :
    ReflectMFuel fuel (fun n => source n >>= fun value => pure (nextFrame value))
      (fun _ => execEff fn fr e) state := by
  exact ReflectMFuel.of_eq (congrFun equal state)

theorem ReflectAtFuel.eff_step {cx : FnCtx} {pt : Pt} {fr : Frame} {e : Effect}
    {source : Nat → M α} {nextFrame : α → Frame} {sourceFuel fuel : Nat} {state : St}
    (instruction : instAt cx.fn pt = some (.eff e))
    (equal : execEff cx.fn fr e =
      source sourceFuel >>= fun value => pure (nextFrame value)) :
    ReflectAtFuel (fuel + 1) cx pt fr source
      (fun value _ pt' fr' => pt' = (pt.1, pt.2 + 1) ∧ fr' = nextFrame value) state := by
  have operation : ReflectMFuel fuel
      (fun n => source n >>= fun value => pure (nextFrame value))
      (fun _ => execEff cx.fn fr e) state :=
    ReflectMFuel.effect_of_eq (nextFrame := nextFrame) equal
  intro result nonTimeout run
  have step : runAt cx pt fr (fuel + 1) state =
      (execEff cx.fn fr e >>= fun frame => runAt cx (pt.1, pt.2 + 1) frame fuel) state := by
    simp only [runAt, instsAt_cons instruction, exec]
  rw [step, bind_apply] at run
  cases effectRun : execEff cx.fn fr e state with
  | ok frame after =>
      rw [effectRun] at run
      obtain ⟨n, sourceRun⟩ := operation (.ok frame after) (NonTimeout.ok _ _) effectRun
      change (source n >>= fun value => pure (nextFrame value)) state = .ok frame after at sourceRun
      rw [bind_apply] at sourceRun
      cases hsource : source n state with
      | stop stop sourceAfter => rw [hsource] at sourceRun; cases sourceRun
      | ok value sourceAfter =>
          rw [hsource] at sourceRun
          cases sourceRun
          exact Or.inl ⟨n, value, after, (pt.1, pt.2 + 1), nextFrame value,
            fuel, hsource, ⟨rfl, rfl⟩, by omega, run⟩
  | stop stop after =>
      rw [effectRun] at run
      have nonTimeoutEffect : NonTimeout (Res.stop stop after : Res Frame) := by
        intro timeoutState equalTimeout
        cases equalTimeout
        exact nonTimeout after run.symm
      obtain ⟨n, sourceRun⟩ := operation (.stop stop after) nonTimeoutEffect effectRun
      change (source n >>= fun value => pure (nextFrame value)) state = .stop stop after at sourceRun
      rw [bind_apply] at sourceRun
      cases hsource : source n state with
      | ok value sourceAfter => rw [hsource] at sourceRun; cases sourceRun
      | stop sourceStop sourceAfter =>
          rw [hsource] at sourceRun
          cases sourceRun
          exact Or.inr ⟨n, stop, after, hsource, run.symm⟩

theorem leaf_eff_reflectAtFuel {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls lsk ls1 : LS} {fr frk : Frame} {ptk : Pt} {cellsk : List (ValueId × RVal)}
    {fuel sourceFuel : Nat} {state : St}
    (hP : Post cfg env cx ls fr lsk frk ptk cellsk) {e : Effect} {le : LEnv}
    (emit : emitEffect e le lsk = ((), ls1)) (hext : ExtT ls1 cx.fn.blocks)
    {source : Nat → M α}
    (equal : execEff cx.fn frk e = source sourceFuel >>= fun _ => pure frk) :
    ReflectAtFuel (fuel + 1) cx ptk frk source
      (fun _ _ pt' fr' => Post cfg env cx ls fr ls1 fr' pt' []) state := by
  obtain ⟨post, instruction⟩ := Post.eff_leaf hP emit hext
  refine (ReflectAtFuel.eff_step instruction equal).mono ?_
  intro value after pt' fr' matched
  rcases matched with ⟨rfl, rfl⟩
  exact post

theorem ReflectAtFuel.complete_expectReturned {cx : FnCtx} {pt : Pt} {fr : Frame}
    {source : Nat → M Flow} {post : Flow → St → Pt → Frame → Prop} {state : St} {fuel : Nat}
    (reflection : ReflectAtFuel fuel cx pt fr source post state)
    (terminal : ∀ flow after pt' fr', post flow after pt' fr' →
      ∃ value, (flow = .normal value ∨ flow = .ret value) ∧ ReturnEndpoint cx pt' fr' value) :
    ReflectMFuel fuel (fun n => source n >>= expectReturned) (fun n => runAt cx pt fr n) state := by
  intro result nonTimeout run
  rcases reflection result nonTimeout run with success | stopped
  · obtain ⟨n, flow, after, pt', fr', residual, sourceRun, matched, bound, continuation⟩ := success
    obtain ⟨value, sourceFlow, returnEndpoint⟩ := terminal flow after pt' fr' matched
    have coreResult : expectReturned flow after = .ok value after := by
      rcases sourceFlow with sourceNormal | sourceReturn
      · rw [sourceNormal]
        rfl
      · rw [sourceReturn]
        rfl
    have targetResult : result = .ok value after := by
      cases residual with
      | zero =>
          have timeoutResult : result = .stop .timeout after := by
            calc
              result = runAt cx pt' fr' 0 after := continuation.symm
              _ = .stop .timeout after := rfl
          exact (nonTimeout after timeoutResult).elim
      | succ extra =>
          calc
            result = runAt cx pt' fr' (extra + 1) after := continuation.symm
            _ = .ok value after := returnEndpoint.run after extra
    refine ⟨n, ?_⟩
    change (source n >>= expectReturned) state = result
    have sourceResult : (source n >>= expectReturned) state = .ok value after := by
      rw [bind_apply, sourceRun]
      exact coreResult
    exact sourceResult.trans targetResult.symm
  · obtain ⟨n, stop, after, sourceRun, targetRun⟩ := stopped
    refine ⟨n, ?_⟩
    change (source n >>= expectReturned) state = result
    calc
      (source n >>= expectReturned) state = .stop stop after := by rw [bind_apply, sourceRun]
      _ = result := targetRun.symm

end Goose.Lower
