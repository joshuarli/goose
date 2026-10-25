import Goose.Lower.ReflectionControl
import Goose.Lower.ReflectionPlaces
import Goose.Lower.FuelBoundMutationsEffects
import Goose.Lower.FuelBoundTyped

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private def resizeFlow (location : Loc) (size : Int) (fill : Option Val) (origin : OriginId) : M Flow := do
  let len ← lengthLoc location
  let size := wrap .i64 size
  if size < 0 then abortAt .resizeNegative origin
  else if size.toNat < len then
    truncateLoc location size.toNat
    pure (.normal .unit)
  else if size.toNat == len then pure (.normal .unit)
  else match fill with
    | none => abortAt .resizeFill origin
    | some value => do
      checkAppendCapacity location (size.toNat - len) origin
      let _ ← appendLoc location (Array.replicate (size.toNat - len) value)
      pure (.normal .unit)

private theorem normalMap_success {action : M α} {state after : St} {flow : Flow}
    (done : (action >>= fun _ => pure (Flow.normal .unit)) state = .ok flow after) :
    flow = .normal .unit := by
  rw [bind_apply] at done
  cases run : action state with
  | stop reason final => rw [run] at done; cases done
  | ok value final => rw [run] at done; exact (Res.ok.inj done).1.symm

private theorem resizeFlow_normal {location : Loc} {size : Int} {fill : Option Val} {origin : OriginId}
    {state after : St} {flow : Flow} (done : resizeFlow location size fill origin state = .ok flow after) :
    flow = .normal .unit := by
  unfold resizeFlow at done
  rw [bind_apply] at done
  cases lengthRun : lengthLoc location state with
  | stop reason final => rw [lengthRun] at done; cases done
  | ok len ready =>
    rw [lengthRun] at done
    by_cases negative : wrap .i64 size < 0
    · simp [negative,abortAt,M.stop] at done
    · simp only [negative,ite_false] at done
      by_cases smaller : (wrap .i64 size).toNat < len
      · simp only [smaller,ite_true] at done
        exact normalMap_success done
      · simp only [smaller,ite_false] at done
        by_cases same : (wrap .i64 size).toNat == len
        · simp only [same,ite_true] at done
          exact (Res.ok.inj done).1.symm
        · simp only [same,Bool.false_eq_true,ite_false] at done
          cases fill with
          | none => simp [abortAt,M.stop] at done
          | some value =>
            exact normalMap_success (action := checkAppendCapacity location ((wrap .i64 size).toNat - len) origin >>=
              fun _ => appendLoc location (Array.replicate ((wrap .i64 size).toNat - len) value))
              (by simpa only [bind_assoc] using done)

private theorem resizeEffect_eq {cx : FnCtx} {frame : Frame} {address sizeId : ValueId}
    {location : Loc} {ty : IntTy} {size : Int} (fill : Option (ValueId × Val)) (origin : OriginId)
    (addressCell : frame.vals[address]? = some (.val (.ref location)))
    (sizeCell : frame.vals[sizeId]? = some (.val (.int ty size)))
    (fillCell : ∀ id value, fill = some (id,value) → frame.vals[id]? = some (.val value)) :
    execEff cx.fn frame (.resize address sizeId (fill.map Prod.fst) (some origin)) =
      resizeFlow location size (fill.map Prod.snd) origin >>= fun _ => pure frame := by
  cases fill with
  | none =>
    simp only [Option.map_none,execEff,getVal_of addressCell,getVal_of sizeCell,expectRef,expectInt,
      pure_bind,resizeFlow,bind_assoc]
    congr 1
    funext len
    by_cases negative : wrap .i64 size < 0
    · simp only [negative,ite_true,abortAtOrg,abortAt]; rfl
    · simp only [negative,ite_false]
      by_cases smaller : (wrap .i64 size).toNat < len
      · simp [smaller]
      · simp only [smaller,ite_false]
        by_cases same : (wrap .i64 size).toNat == len <;> simp only [same,ite_true,abortAtOrg,abortAt] <;> rfl
  | some pair =>
    obtain ⟨id,value⟩ := pair
    have cell := fillCell id value rfl
    simp only [Option.map_some,execEff,getVal_of addressCell,getVal_of sizeCell,getVal_of cell,
      expectRef,expectInt,pure_bind,resizeFlow,bind_assoc]
    congr 1
    funext len
    by_cases negative : wrap .i64 size < 0
    · simp only [negative,ite_true,abortAtOrg,abortAt]; rfl
    · simp only [negative,ite_false]
      by_cases smaller : (wrap .i64 size).toNat < len
      · simp [smaller]
      · simp only [smaller,ite_false]
        by_cases same : (wrap .i64 size).toNat == len <;>
          simp [same,checkCapacityAtOrg_some]

private theorem resizeEffectFuelBound {sourceFuel fuel : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls middle after : LS} {fr before : Frame} {pt : Pt} {cells : List (ValueId × RVal)}
    {loop : Option LoopCtx} {state : St} {address sizeId : ValueId} {location : Loc} {ty : IntTy} {size : Int}
    (post : Post cfg env cx ls fr middle before pt cells) (fill : Option (ValueId × Val)) (origin : OriginId)
    (addressCell : before.vals[address]? = some (.val (.ref location)))
    (sizeCell : before.vals[sizeId]? = some (.val (.int ty size)))
    (fillCell : ∀ id value, fill = some (id,value) → before.vals[id]? = some (.val value))
    {le : LEnv} (emit : emitEffect (.resize address sizeId (fill.map Prod.fst) (some origin)) le middle = ((),after))
    (extension : ExtT after cx.fn.blocks) :
    FuelBoundAt sourceFuel fuel cx pt before (fun _ => resizeFlow location size (fill.map Prod.snd) origin)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
  cases fuel with
  | zero => exact FuelBoundAt.zero _ _ _ _ _ _ _
  | succ fuel =>
    have first := leaf_eff_fuelBoundAt (fuel := fuel) (state := state) post emit extension
      (source := fun _ => resizeFlow location size (fill.map Prod.snd) origin) (sourceFuel := sourceFuel)
      (resizeEffect_eq fill origin addressCell sizeCell fillCell)
    have composed : FuelBoundAt sourceFuel (fuel + 1) cx pt before
        (fun _ => resizeFlow location size (fill.map Prod.snd) origin >>= pure)
        (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
      refine first.bind ?_
      intro flow next pt' fr' done matched residual bound
      exact FuelBoundAt.ret (sourceFuel := sourceFuel) (targetFuel := residual) (Or.inl ⟨resizeFlow_normal done,matched⟩)
    simpa only [bind_pure] using composed

private theorem resizeFlow_prepare (env : Env) (loop : Option LoopCtx) (location : Loc)
    (size : Int) (fill : Option Val) (origin : OriginId) :
    resizeFlow location size fill origin >>= prepareLoopFlow env loop = resizeFlow location size fill origin := by
  funext state
  rw [bind_apply]
  cases run : resizeFlow location size fill origin state with
  | stop reason final => rfl
  | ok flow final =>
    have same := resizeFlow_normal run
    subst flow
    cases loop <;> rfl

theorem typedStatementFuelBound_resize_none {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {owner : Place} {size : Expr} {origin : OriginId}
    (placeChild : TypedPlaceFuelBound sourceFuel fuel cfg results owner)
    (sizeChild : ∀ residual, residual ≤ fuel → TypedExprFuelBound sourceFuel residual cfg results size) :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.resize owner size none origin) := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq depth
    targets counter generated frames
  obtain ⟨placeSource,element,placeTyping,placeRoots,_,_,_,_,sizeSources⟩ := source.resizeSizeChildren
  have placeMetadata : SourceResults placeSource.typingEnv placeSource.rootsEnv results := by
    rw [placeTyping,placeRoots]
    exact metadata
  simp only [lowerStmt,bind_eq] at lowering
  obtain ⟨address,middle,placeRun,sizeId,last,sizeRun,fillId,finish,fillRun,emit⟩ := lowering
  rw [pure_run] at fillRun
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj fillRun
  have lastExtension := extension.of_adv (adv_emitEffect emit)
  have middleExtension := lastExtension.of_adv (advB_lowerExpr size _ _ _ _ sizeRun)
  have middleGenerated := generated.lowerPlace owner placeRun
  have first := placeChild env state placeSource placeMetadata ls middle address pt cx fr placeRun point
    middleExtension rel moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun n => evalPlace n cfg env owner >>= fun location => evalExpr n cfg env size >>= fun value =>
        expectInt value >>= fun pair => resizeFlow location pair.2 none origin)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_
    intro location next pt1 fr1 placeDone post1 residual bound
    obtain ⟨sizeSource,integer,sizeTyping,sizeRoots,_,_,sizeType⟩ := sizeSources sourceFuel location next placeDone
    have sizeMetadata : SourceResults sizeSource.typingEnv sizeSource.rootsEnv results := by
      rw [sizeTyping,sizeRoots]
      exact metadata
    have second := sizeChild residual bound env next sizeSource sizeMetadata middle last sizeId pt1 cx fr1
      sizeRun post1.pp lastExtension post1.rel moduleEq resultsEq middleGenerated
    refine second.bind ?_
    intro value final pt2 fr2 sizeDone post2 remaining remainingBound
    have typed := (sizeSource.result sourceFuel value sizeDone).typed
    rw [sizeType] at typed
    obtain ⟨count,rfl⟩ := Core.Sound.hasTy_int typed
    have combined := post1.comp post2
    have addressCell := combined.has (address,.val (.ref location)) (by simp)
    have sizeCell := combined.has (sizeId,.val (.int integer count)) (by simp)
    simpa only [expectInt,pure_bind,Option.map_none] using
      (resizeEffectFuelBound (fuel := remaining) combined none origin addressCell sizeCell
        (by intro id value impossible; cases impossible) emit extension)
  refine composition.of_source (otherFuel := sourceFuel + 1) ?_
  have equal : execStmt (sourceFuel + 1) cfg env (.resize owner size none origin) =
      evalPlace sourceFuel cfg env owner >>= fun location => evalExpr sourceFuel cfg env size >>= fun value =>
        expectInt value >>= fun pair => resizeFlow location pair.2 none origin := by
    simp only [execStmt,resizeFlow,pure_bind]
  rw [equal]
  simp only [bind_assoc,resizeFlow_prepare]

theorem typedStatementFuelBound_resize_some {sourceFuel fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {owner : Place} {size fill : Expr} {origin : OriginId}
    (placeChild : TypedPlaceFuelBound sourceFuel fuel cfg results owner)
    (sizeChild : ∀ residual, residual ≤ fuel → TypedExprFuelBound sourceFuel residual cfg results size)
    (fillChild : ∀ residual, residual ≤ fuel → TypedExprFuelBound sourceFuel residual cfg results fill) :
    TypedStatementFuelBound (sourceFuel + 1) fuel cfg results loop (.resize owner size (some fill) origin) := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq depth
    targets counter generated frames
  obtain ⟨placeSource,element,placeTyping,placeRoots,_,_,_,_,sizeSources⟩ := source.resizeSizeChildren
  have placeMetadata : SourceResults placeSource.typingEnv placeSource.rootsEnv results := by
    rw [placeTyping,placeRoots]
    exact metadata
  simp only [lowerStmt,bind_eq] at lowering
  obtain ⟨address,middle,placeRun,sizeId,last,sizeRun,fillId,filled,fillExprRun,
    fillOption,finish,fillPure,emit⟩ := lowering
  rw [pure_run] at fillPure
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj fillPure
  have filledExtension := extension.of_adv (adv_emitEffect emit)
  have lastExtension := filledExtension.of_adv (advB_lowerExpr fill _ _ _ _ fillExprRun)
  have middleExtension := lastExtension.of_adv (advB_lowerExpr size _ _ _ _ sizeRun)
  have middleGenerated := generated.lowerPlace owner placeRun
  have lastGenerated := middleGenerated.lowerExpr size sizeRun
  have first := placeChild env state placeSource placeMetadata ls middle address pt cx fr placeRun point
    middleExtension rel moduleEq resultsEq generated
  have composition : FuelBoundAt sourceFuel fuel cx pt fr
      (fun n => evalPlace n cfg env owner >>= fun location => evalExpr n cfg env size >>= fun value =>
        expectInt value >>= fun pair => evalExpr n cfg env fill >>= fun fillValue =>
          resizeFlow location pair.2 (some fillValue) origin)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_
    intro location next pt1 fr1 placeDone post1 residual bound
    obtain ⟨sizeSource,integer,sizeTyping,sizeRoots,_,_,sizeType⟩ := sizeSources sourceFuel location next placeDone
    have sizeMetadata : SourceResults sizeSource.typingEnv sizeSource.rootsEnv results := by
      rw [sizeTyping,sizeRoots]
      exact metadata
    have second := sizeChild residual bound env next sizeSource sizeMetadata middle last sizeId pt1 cx fr1
      sizeRun post1.pp lastExtension post1.rel moduleEq resultsEq middleGenerated
    refine second.bind ?_
    intro value final pt2 fr2 sizeDone post2 remaining remainingBound
    have typed := (sizeSource.result sourceFuel value sizeDone).typed
    rw [sizeType] at typed
    obtain ⟨count,rfl⟩ := Core.Sound.hasTy_int typed
    obtain ⟨fillSource,fillTyping,fillRoots,_,_⟩ := source.resizeFillChild sourceFuel sourceFuel location
      (.int integer count) placeDone sizeDone
    have fillMetadata : SourceResults fillSource.typingEnv fillSource.rootsEnv results := by
      rw [fillTyping,fillRoots]
      exact metadata
    have third := fillChild remaining (Nat.le_trans remainingBound bound) env final fillSource fillMetadata last filled
      fillId pt2 cx fr2 fillExprRun post2.pp filledExtension post2.rel moduleEq resultsEq lastGenerated
    have tail : FuelBoundAt sourceFuel remaining cx pt2 fr2
        (fun n => evalExpr n cfg env fill >>= fun fillValue => resizeFlow location count (some fillValue) origin)
        (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') final := by
      refine third.bind ?_
      intro fillValue ready pt3 fr3 fillDone post3 available availableBound
      have combined := (post1.comp post2).comp post3
      have addressCell := combined.has (address,.val (.ref location)) (by simp)
      have sizeCell := combined.has (sizeId,.val (.int integer count)) (by simp)
      have fillCell := combined.has (fillId,.val fillValue) (by simp)
      simpa only [Option.map_some] using
        (resizeEffectFuelBound (fuel := available) combined (some (fillId,fillValue)) origin addressCell sizeCell
          (by intro id value same; obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj same); exact fillCell)
          emit extension)
    simpa only [expectInt,pure_bind] using tail
  refine composition.of_source (otherFuel := sourceFuel + 1) ?_
  have equal : execStmt (sourceFuel + 1) cfg env (.resize owner size (some fill) origin) =
      evalPlace sourceFuel cfg env owner >>= fun location => evalExpr sourceFuel cfg env size >>= fun value =>
        expectInt value >>= fun pair => evalExpr sourceFuel cfg env fill >>= fun fillValue =>
          resizeFlow location pair.2 (some fillValue) origin := by
    simp only [execStmt,resizeFlow,pure_bind]
  rw [equal]
  simp only [bind_assoc,resizeFlow_prepare]

end Goose.Lower
