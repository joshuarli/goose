import Goose.Lower.Validation.ReplacementScopedOperandsAccess

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def RhsLoopFresh (floor : Nat) : Option LoopCtx → Prop
  | none => True
  | some loop => match loop.cont with
    | .next _ _ counter => floor ≤ counter
    | .jump _ => True

def RhsPreFresh (floor : Nat) (pre : List (SlotId × ValueId × OriginId)) : Prop :=
  ∀ entry ∈ pre, floor ≤ entry.2.1

theorem RhsOperandsAt.leaveAll (floor : Nat) (env : LEnv) (before : LS) (scopes : List ScopeId) :
    RhsOperandsAt floor env before (Goose.Lower.leaveAll scopes) := by
  induction scopes generalizing before with
  | nil => exact RhsOperandsAt.pure _ _ _ _
  | cons scope rest ih =>
    simp only [Goose.Lower.leaveAll]
    exact (RhsOperandsAt.emitEffect _ _ _ _ (by simp [Effect.uses])).bind (ih _)

theorem RhsOperandsAt.leaveTo (floor : Nat) (env : LEnv) (before : LS) (depth : Nat) :
    RhsOperandsAt floor env before (Goose.Lower.leaveTo depth) := by
  unfold Goose.Lower.leaveTo
  exact (RhsOperandsAt.get _ _ _).bind (RhsOperandsAt.leaveAll _ _ _ _)

theorem RhsOperandsAt.initSlots (floor : Nat) (env : LEnv) (before : LS)
    (pre : List (SlotId × ValueId × OriginId)) (fresh : RhsPreFresh floor pre) :
    RhsOperandsAt floor env before (Goose.Lower.initSlots pre) := by
  induction pre generalizing before with
  | nil => exact RhsOperandsAt.pure _ _ _ _
  | cons entry rest ih =>
    simp only [Goose.Lower.initSlots]
    apply (RhsOperandsAt.emitEffect floor env before (.slotInit entry.1 entry.2.1 (some entry.2.2)) ?_).bind
    · exact ih _ (fun item member => fresh item (by simp [member]))
    · simpa only [Effect.uses, List.mem_singleton] using
        fun _ value equal => equal ▸ fresh entry (by simp)

theorem rhsOperands_rangeBack (floor : Nat) (type : IntTy) (counter : ValueId) (header : BlockId)
    (counterFresh : floor ≤ counter) : RhsOperandsRun floor (rangeBack type counter header) := by
  intro env before bound
  unfold rangeBack
  apply (RhsOperandsAt.isLive _ _ _).bind
  split
  · apply RhsOperandsAt.bindFresh bound
      (RhsOperandsAt.emitDef _ _ _ _ (by simp [Op.uses, counterFresh]))
      (advB_emitDef _) (freshValue_emitDef _)
    intro next middle _ _ nextFresh
    exact RhsOperandsAt.emitTerm _ _ _ _ (by simpa only [Term.uses, List.mem_singleton] using
      fun live value equal => equal ▸ nextFresh live)
  · exact RhsOperandsAt.pure _ _ _ _

theorem rhsOperands_loopBody (floor : Nat) (condition : ValueId)
    (body : Nat → BlockId → B ValueId) (back : B Unit)
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyChild : ∀ depth exit, RhsOperandsRun floor (body depth exit))
    (backChild : RhsOperandsRun floor back) (env : LEnv) (before : LS)
    (bound : floor ≤ before.vals.size) (fresh : RhsValueFresh floor before condition) :
    RhsOperandsAt floor env before (loopBody condition body back) := by
  let forked := Goose.Lower.fork condition env before
  let entered := Goose.Lower.setCur (some forked.1.1) env forked.2
  let ended := body before.stack.length forked.1.2 env entered.2
  have enteredBound : floor ≤ entered.2.vals.size :=
    Nat.le_trans bound (advB_fork condition env before forked.1 forked.2 rfl).vals
  have endedBound : floor ≤ ended.2.vals.size := Nat.le_trans enteredBound
    (bodyAdvance _ _ env entered.2 ended.1 ended.2 rfl).vals
  unfold loopBody
  apply (RhsOperandsAt.get _ _ _).bind
  apply (RhsOperandsAt.fork _ _ _ _ fresh).bind
  apply (RhsOperandsAt.setCur _ _ _ _).bind
  exact (bodyChild _ _ env entered.2 enteredBound).bind
    ((backChild env ended.2 endedBound).bind (RhsOperandsAt.setCur _ _ _ _))

theorem rhsOperands_lowerWhile (floor : Nat) (header : BlockId) (condition : B ValueId)
    (body : Nat → BlockId → B ValueId) (conditionAdvance : AdvB condition)
    (conditionFresh : FreshValueRun condition) (conditionChild : RhsOperandsRun floor condition)
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyChild : ∀ depth exit, RhsOperandsRun floor (body depth exit)) :
    RhsOperandsRun floor (lowerWhile header condition body) := by
  intro env before bound
  unfold lowerWhile
  apply RhsOperandsAt.bindFresh bound (conditionChild env before bound) conditionAdvance conditionFresh
  intro value middle _ middleBound valueFresh
  apply RhsOperandsAt.whenLive
  intro block live
  exact rhsOperands_loopBody floor value body (emitTerm (.br header [])) bodyAdvance bodyChild
    (fun env before _ => RhsOperandsAt.emitTerm _ _ _ _ (by simp [Term.uses]))
    env middle middleBound valueFresh

theorem rhsOperands_lowerRange (floor : Nat) (type : IntTy) (counter limit : ValueId)
    (header : BlockId) (body : Nat → BlockId → B ValueId)
    (counterFresh : floor ≤ counter) (limitFresh : floor ≤ limit)
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyChild : ∀ depth exit, RhsOperandsRun floor (body depth exit)) :
    RhsOperandsRun floor (lowerRange type counter limit header body) := by
  intro env before bound
  unfold lowerRange
  apply RhsOperandsAt.bindFresh bound
    (RhsOperandsAt.emitDef _ _ _ _ (by simp [Op.uses, counterFresh, limitFresh]))
    (advB_emitDef _) (freshValue_emitDef _)
  intro condition middle _ middleBound conditionFresh
  exact rhsOperands_loopBody floor condition body (rangeBack type counter header) bodyAdvance bodyChild
    (rhsOperands_rangeBack floor type counter header counterFresh) env middle middleBound conditionFresh

end Goose.Lower.Validation
