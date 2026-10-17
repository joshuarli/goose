import Goose.Lower.Validation.ReplacementScopedOperandsEach

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def RhsBlockChild (floor : Nat) (block : Core.Block) : Prop :=
  ∀ loop pre want env before, floor ≤ before.vals.size → RhsLoopFresh floor loop →
    (before.cur.isSome = true → RhsPreFresh floor pre) →
    RhsOperandsAt floor env before (lowerBlock loop pre want block)

theorem rhsOperands_whileStatement (floor : Nat) (loop : Option LoopCtx)
    (condition : Expr) (body : Core.Block) (origin : OriginId)
    (conditionChild : RhsOperandsRun floor (lowerExpr condition)) (bodyChild : RhsBlockChild floor body) :
    RhsOperandsRun floor (lowerStmt loop (.while condition body origin)) := by
  intro env before bound
  simp only [lowerStmt]
  apply (RhsOperandsAt.newBlock _ _ _ _).bindRun
  intro header allocated allocation
  have allocatedBound := Nat.le_trans bound (advB_newBlock0 env before header allocated allocation).vals
  apply (RhsOperandsAt.emitTerm _ _ _ _ (by simp [Term.uses])).bind
  apply (RhsOperandsAt.setCur _ _ _ _).bind
  apply rhsOperands_lowerWhile floor header.1 (lowerExpr condition)
    (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header.1⟩) [] false body)
    (advB_lowerExpr condition) (freshValue_lowerExpr condition) conditionChild
    (fun _ _ => advB_lowerBlock _ _ _ _)
  · intro depth exit env state stateBound
    exact bodyChild _ _ _ _ _ stateBound (by trivial) (by simp [RhsPreFresh])
  · exact Nat.le_trans allocatedBound (advB_emitTerm (.br header.1 []) env allocated _ _ rfl).vals

theorem rhsOperands_rangeStatement (floor : Nat) (loop : Option LoopCtx)
    (slot : VarId) (lo hi : Expr) (body : Core.Block) (origin : OriginId)
    (loChild : RhsOperandsRun floor (lowerExpr lo)) (hiChild : RhsOperandsRun floor (lowerExpr hi))
    (bodyChild : RhsBlockChild floor body) :
    RhsOperandsRun floor (lowerStmt loop (.forRange slot lo hi body origin)) := by
  intro env before bound
  simp only [lowerStmt]
  apply RhsOperandsAt.bindFresh bound (loChild env before bound) (advB_lowerExpr lo) (freshValue_lowerExpr lo)
  intro low lowered _ lowerBound lowFresh
  apply RhsOperandsAt.bindFresh lowerBound (hiChild env lowered lowerBound)
    (advB_lowerExpr hi) (freshValue_lowerExpr hi)
  intro high ranged highRun rangeBound highFresh
  have lowRetained := lowFresh.after (dead_lowerExpr hi) highRun
  apply RhsOperandsAt.whenLive
  intro block active
  have live : ranged.cur.isSome = true := congrArg Option.isSome active
  have lowBound := lowRetained live
  have highBound := highFresh live
  apply RhsOperandsAt.bindUnchanged (fun _ _ => intTyOf_eq rfl)
  intro type
  apply (RhsOperandsAt.newBlock _ _ _ _).bindRun
  intro header allocated allocation
  have counterBound : floor ≤ header.2.headD 0 := by
    have ids := congrArg Prod.fst allocation
    rw [newBlock1_run] at ids
    have equal : ranged.vals.size = header.2.headD 0 := by
      simpa using congrArg (fun pair => pair.2.headD 0) ids
    exact equal ▸ rangeBound
  have allocatedBound := Nat.le_trans rangeBound (advB_newBlock1 _ env ranged header allocated allocation).vals
  apply (RhsOperandsAt.emitTerm floor env allocated (.br header.1 [low])
    (by simp [Term.uses, lowBound])).bind
  apply (RhsOperandsAt.setCur _ _ _ _).bind
  apply rhsOperands_lowerRange floor type (header.2.headD 0) high header.1
    (fun depth exit => lowerBlock (some ⟨depth, exit, .next header.1 type (header.2.headD 0)⟩)
      [(slot, header.2.headD 0, origin)] false body) counterBound highBound
    (fun _ _ => advB_lowerBlock _ _ _ _)
  · intro depth exit env state stateBound
    exact bodyChild _ _ _ _ _ stateBound counterBound (by
      intro _ entry member
      have equal : entry = (slot, header.2.headD 0, origin) := List.mem_singleton.mp member
      subst entry
      exact counterBound)
  · exact Nat.le_trans allocatedBound (advB_emitTerm (.br header.1 [low]) env allocated _ _ rfl).vals

end Goose.Lower.Validation
