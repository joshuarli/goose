import Goose.Lower.ReflectionControl
import Goose.Lower.ReflectionPlaces
import Goose.Lower.FuelBoundMutationsEffects
import Goose.Lower.FuelBoundTyped

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private theorem typedNormalEffectFuelBound {sourceFuel fuel : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls lsk ls1 : LS} {fr frk : Frame} {ptk : Pt} {cells : List (ValueId × RVal)}
    {state : St} {effect : Effect} {le : LEnv} {loop : Option LoopCtx}
    (post : Post cfg env cx ls fr lsk frk ptk cells)
    (emit : emitEffect effect le lsk = ((), ls1)) (extension : ExtT ls1 cx.fn.blocks)
    {α : Type} {source : Nat → M α}
    (equal : execEff cx.fn frk effect = source sourceFuel >>= fun _ => pure frk) :
    FuelBoundAt sourceFuel fuel cx ptk frk (fun n => source n >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr ls1 loop flow pt' fr') state := by
  have reflected := normalEffectFuelBound (fuel := fuel) (state := state) post emit extension equal
  exact reflected.mono (fun _ _ _ _ matched => Or.inl ⟨matched.1, matched.2⟩)

private theorem normalFlowMap_success {source : M Unit} {state : St} {flow : Flow} {after : St}
    (run : (source >>= fun _ => pure (Flow.normal .unit)) state = .ok flow after) :
    flow = .normal .unit := by
  cases hsource : source state with
  | stop reason next => simp [bind_apply, hsource] at run
  | ok value next => simp [bind_apply, hsource] at run; cases run; rfl

private theorem bindFlow_normal {α : Type} {source : M α} {continuation : α → M Flow}
    (normal : ∀ value state flow after, continuation value state = .ok flow after → flow = .normal .unit)
    {state : St} {flow : Flow} {after : St}
    (run : (source >>= continuation) state = .ok flow after) : flow = .normal .unit := by
  rw [bind_apply] at run
  cases hsource : source state with
  | stop reason next => simp [hsource] at run
  | ok value next =>
    have continuationRun : continuation value next = .ok flow after := by
      simpa [M.bind', hsource] using run
    exact normal value next flow after continuationRun

private theorem prepareLoopFlow_normal_only (env : Env) (loop : Option LoopCtx)
    (source : M Flow)
    (normal : ∀ state flow after, source state = .ok flow after → flow = .normal .unit) :
    source >>= prepareLoopFlow env loop = source := by
  funext state
  cases hsource : source state with
  | stop reason next => simp [bind_apply, hsource]
  | ok flow next =>
    have hflow := normal state flow next hsource
    subst flow
    cases loop <;> simp [bind_apply, pure_apply, hsource, prepareLoopFlow, prepareReturn, prepareLoopExit]

theorem typedStatementFuelBound_popN {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {place : Place} {countExpr : Expr} {origin : OriginId}
    (placeChild : TypedPlaceFuelBound sourceFuel fuel cfg results place)
    (countChild : ∀ residual, residual ≤ fuel → TypedExprFuelBound sourceFuel residual cfg results countExpr) :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.popN place countExpr origin) := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq depth
    targets counter generated frames
  obtain ⟨destination, element, destinationTyping, destinationRoots, _, _, _, _, countChildren⟩ :=
    source.popNChildren
  have destinationMetadata : SourceResults destination.typingEnv destination.rootsEnv results := by
    rw [destinationTyping, destinationRoots]
    exact metadata
  simp only [lowerStmt, bind_eq] at lowering
  obtain ⟨address, middle, placeRun, countId, last, countRun, emit⟩ := lowering
  have lastExtension := extension.of_adv (adv_emitEffect emit)
  have middleExtension := lastExtension.of_adv (advB_lowerExpr countExpr _ _ _ _ countRun)
  have first := placeChild env state destination destinationMetadata ls middle address pt cx fr placeRun
    point middleExtension rel moduleEq resultsEq generated
  have middleGenerated := generated.lowerPlace place placeRun
  let popAction (location : Loc) (countValue : Val) : M Unit := do
    let (_, count) ← expectInt countValue
    let length ← lengthLoc location
    if count < 0 || count > (length : Int) then abortAt .popNRange origin
    else truncateLoc location (length - count.toNat)
  let sourceAction (location : Loc) (countValue : Val) : M Flow := do
    let (_, count) ← expectInt countValue
    let length ← lengthLoc location
    if count < 0 || count > (length : Int) then abortAt .popNRange origin
    else do
      truncateLoc location (length - count.toNat)
      pure (Flow.normal .unit)
  have sourceActionMap (location : Loc) (countValue : Val) :
      sourceAction location countValue = popAction location countValue >>= fun _ => pure (Flow.normal .unit) := by
    funext s
    cases hcount : expectInt countValue s with
    | stop reason next =>
      simp [sourceAction, popAction, bind_apply, hcount, Functor.map]
    | ok pair next =>
      cases hlength : lengthLoc location next with
      | stop reason after =>
        simp [sourceAction, popAction, bind_apply, hcount, hlength, Functor.map]
      | ok length after =>
        by_cases invalid : pair.2 < 0 ∨ pair.2 > (length : Int)
        · simp [sourceAction, popAction, bind_apply, hcount, hlength, invalid,
            abortAt, M.stop, Functor.map]
        · cases htruncate : truncateLoc location (length - pair.2.toNat) after <;>
            simp [sourceAction, popAction, bind_apply, hcount, hlength, invalid, htruncate,
              pure_apply, M.bind', M.pure', Functor.map]
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun n => evalPlace n cfg env place >>= fun location =>
        evalExpr n cfg env countExpr >>= fun countValue => do
          let (_, count) ← expectInt countValue
          let length ← lengthLoc location
          if count < 0 || count > (length : Int) then abortAt .popNRange origin
          else do
            truncateLoc location (length - count.toNat)
            pure (Flow.normal .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_
    intro location next pt1 fr1 placeDone placePost residual residualBound
    obtain ⟨countSource, integer, countTyping, countRoots, _, _, countType⟩ :=
      countChildren sourceFuel location next placeDone
    have countMetadata : SourceResults countSource.typingEnv countSource.rootsEnv results := by
      rw [countTyping, countRoots]
      exact metadata
    have second := (countChild residual residualBound) env next countSource countMetadata
      middle last countId pt1 cx fr1 countRun placePost.pp lastExtension placePost.rel
      moduleEq resultsEq middleGenerated
    have composedCount : FuelBoundAt sourceFuel residual cx pt1 fr1
        (fun k => evalExpr k cfg env countExpr >>= fun countValue => do
          let (_, count) ← expectInt countValue
          let length ← lengthLoc location
          if count < 0 || count > (length : Int) then abortAt .popNRange origin
          else do
            truncateLoc location (length - count.toNat)
            pure (Flow.normal .unit))
        (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') next := by
      refine second.bind ?_
      intro countValue final pt2 fr2 countDone countPost remaining remainingBound
      have countTyped := (countSource.result sourceFuel countValue countDone).typed
      rw [countType] at countTyped
      obtain ⟨count, rfl⟩ := Core.Sound.hasTy_int countTyped
      have combined := placePost.comp countPost
      have addressCell := combined.has (address, .val (.ref location)) (by simp)
      have countCell := combined.has (countId, .val (.int integer count)) (by simp)
      let action : M Unit := do
        let length ← lengthLoc location
        if count < 0 || count > (length : Int) then abortAt .popNRange origin
        else truncateLoc location (length - count.toNat)
      have equal : execEff cx.fn fr2 (.popN address countId (some origin)) =
          action >>= fun _ => pure fr2 := by
        simp [execEff, getVal_of addressCell, getVal_of countCell, Goose.Core.expectRef,
          Goose.Core.expectInt, abortAtOrg, abortAt, action]
        funext s
        cases hlen : lengthLoc location s with
        | stop err next => simp [bind_apply, hlen, Functor.map]
        | ok length next =>
          by_cases invalid : count < 0 ∨ count > (length : Int)
          · simp [bind_apply, hlen, invalid, M.stop, M.bind', Functor.map]
          · simp [bind_apply, hlen, invalid]
      have reflected := typedNormalEffectFuelBound (fuel := remaining) (state := final) (loop := loop)
          combined emit extension
          (source := fun _ => action)
          (sourceFuel := sourceFuel) equal
      have actionEqual : popAction location (.int integer count) = action := by
        simp [popAction, action, expectInt, pure_bind]
      exact reflected.of_source ((congrFun (sourceActionMap location (.int integer count)) final).trans
          (congrFun (congrArg (fun m : M Unit => m >>= fun _ => pure (Flow.normal .unit)) actionEqual) final))
    exact composedCount
  refine composition.of_source (otherFuel := sourceFuel + 1) ?_
  have rawSource : execStmt (sourceFuel + 1) cfg env (.popN place countExpr origin) =
      (evalPlace sourceFuel cfg env place >>= fun location =>
        evalExpr sourceFuel cfg env countExpr >>= fun countValue => do
          let (_, count) ← expectInt countValue
          let length ← lengthLoc location
          if count < 0 || count > (length : Int) then abortAt .popNRange origin
          else do
            truncateLoc location (length - count.toNat)
            pure (Flow.normal .unit)) := by
    simp only [execStmt]
  rw [rawSource]
  have sourceNormal : ∀ state flow after,
      (evalPlace sourceFuel cfg env place >>= fun location =>
        evalExpr sourceFuel cfg env countExpr >>= fun countValue => sourceAction location countValue) state =
        .ok flow after → flow = .normal .unit := by
    apply bindFlow_normal
    intro location
    apply bindFlow_normal
    intro countValue sourceState flow after run
    change sourceAction location countValue sourceState = .ok flow after at run
    rw [sourceActionMap] at run
    exact normalFlowMap_success run
  exact congrFun (prepareLoopFlow_normal_only env loop _ sourceNormal) state

end Goose.Lower
