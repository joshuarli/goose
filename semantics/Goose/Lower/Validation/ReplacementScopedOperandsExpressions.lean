import Goose.Lower.Validation.ReplacementScopedOperandsControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem rhsOperands_read (floor : Nat) (place : Place)
    (child : RhsOperandsRun floor (lowerPlace place)) :
    RhsOperandsRun floor (lowerExpr (.read place)) := by
  intro env before bound
  simp only [lowerExpr]
  apply RhsOperandsAt.bindFresh bound (child env before bound)
    (advB_lowerPlace place) (freshValue_lowerPlace place)
  intro address addressed addressRun addressedBound addressFresh
  apply (RhsOperandsAt.emitDef floor env addressed (.load address) ?_).bind
  · exact (RhsOperandsAt.recordRead _ _ _ _ _).bind (RhsOperandsAt.pure _ _ _ _)
  · simpa only [Op.uses, List.mem_singleton] using
      fun live source equal => equal ▸ addressFresh live

theorem rhsOperands_ref (floor : Nat) (mu : Mutability) (place : Place)
    (child : RhsOperandsRun floor (lowerPlace place)) :
    RhsOperandsRun floor (lowerExpr (.ref mu place)) := by
  intro env before bound
  simp only [lowerExpr]
  apply RhsOperandsAt.bindFresh bound (child env before bound)
    (advB_lowerPlace place) (freshValue_lowerPlace place)
  intro address addressed _ _ addressFresh
  exact RhsOperandsAt.borrowTo _ _ _ _ _ addressFresh

theorem rhsOperands_intUnary (floor : Nat) (child : Expr)
    (receipt : RhsOperandsRun floor (lowerExpr child))
    (op : IntTy → ValueId → Op) (uses : ∀ type value, (op type value).uses ⊆ [value]) :
    RhsOperandsRun floor (do let value ← lowerExpr child; let type ← intTyOf value; emitDef (op type value)) := by
  intro env before bound
  apply RhsOperandsAt.bindFresh bound (receipt env before bound)
    (advB_lowerExpr child) (freshValue_lowerExpr child)
  intro value middle _ _ valueFresh
  apply RhsOperandsAt.bindUnchanged (fun _ _ => intTyOf_eq rfl)
  intro type
  apply RhsOperandsAt.emitDef
  intro live source member
  have equal : source = value := List.mem_singleton.mp (uses type value member)
  exact equal ▸ valueFresh live

theorem rhsOperands_intBinary (floor : Nat) (left right : Expr)
    (one : RhsOperandsRun floor (lowerExpr left)) (two : RhsOperandsRun floor (lowerExpr right))
    (op : IntTy → ValueId → ValueId → Op)
    (uses : ∀ type first second, (op type first second).uses ⊆ [first, second]) :
    RhsOperandsRun floor (do
      let first ← lowerExpr left
      let second ← lowerExpr right
      let type ← intTyOf first
      emitDef (op type first second)) := by
  intro env before bound
  apply RhsOperandsAt.bindFresh bound (one env before bound)
    (advB_lowerExpr left) (freshValue_lowerExpr left)
  intro first middle _ middleBound firstFresh
  apply RhsOperandsAt.bindFresh middleBound (two env middle middleBound)
    (advB_lowerExpr right) (freshValue_lowerExpr right)
  intro second after secondRun _ secondFresh
  have retained := firstFresh.after (dead_lowerExpr right) secondRun
  apply RhsOperandsAt.bindUnchanged (fun _ _ => intTyOf_eq rfl)
  intro type
  apply RhsOperandsAt.emitDef
  intro live source member
  have selected := uses type first second member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl
  · exact retained live
  · exact secondFresh live

theorem rhsOperands_compare (floor : Nat) (comparison : CmpOp) (left right : Expr)
    (one : RhsOperandsRun floor (lowerExpr left)) (two : RhsOperandsRun floor (lowerExpr right)) :
    RhsOperandsRun floor (lowerExpr (.cmp comparison left right)) := by
  intro env before bound
  simp only [lowerExpr]
  apply RhsOperandsAt.bindFresh bound (one env before bound)
    (advB_lowerExpr left) (freshValue_lowerExpr left)
  intro first middle _ middleBound firstFresh
  apply RhsOperandsAt.bindFresh middleBound (two env middle middleBound)
    (advB_lowerExpr right) (freshValue_lowerExpr right)
  intro second after secondRun _ secondFresh
  have retained := firstFresh.after (dead_lowerExpr right) secondRun
  apply RhsOperandsAt.bindUnchanged (fun _ _ => valTy_run _ _ _)
  intro type
  have operands : ∀ live : after.cur.isSome = true, ∀ value ∈ [first, second], floor ≤ value := by
    intro live value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact retained live
    · exact secondFresh live
  cases type with
  | data type => cases type <;> exact RhsOperandsAt.emitDef _ _ _ _ operands
  | view _ _ => exact RhsOperandsAt.emitDef _ _ _ _ operands

theorem rhsOperands_listDef {floor : Nat} {action : B (List ValueId)}
    (child : RhsOperandsRun floor action) (fresh : FreshValueListRun action)
    (op : List ValueId → Op) (uses : ∀ values, (op values).uses ⊆ values) :
    RhsOperandsRun floor (do let values ← action; emitDef (op values)) := by
  intro env before bound
  apply RhsOperandsAt.bindRun (child env before bound)
  intro values middle run
  exact RhsOperandsAt.emitDef floor env middle (op values) fun live value member =>
    Nat.le_trans bound (fresh env before values middle run live value (uses values member))

theorem rhsOperands_call (floor : Nat) (context : ContextId) (args : List Arg) (origin : OriginId)
    (child : RhsOperandsRun floor (lowerArgs args)) :
    RhsOperandsRun floor (lowerExpr (.call context args origin)) := by
  intro env before bound
  simp only [lowerExpr]
  apply RhsOperandsAt.bindRun (child env before bound)
  intro values middle run
  apply (RhsOperandsAt.emitDef floor env middle (.call context values (some origin)) ?_).bind
  · apply (RhsOperandsAt.read _ _ _).bind
    simp only [read_apply]
    by_cases stopping : env.mod.noReturn context = true
    · simp only [stopping, ↓reduceIte]
      exact (RhsOperandsAt.emitTerm _ _ _ .unreachable (by simp [Term.uses])).bind
        (RhsOperandsAt.pure _ _ _ _)
    · simp only [stopping, ↓reduceIte]
      exact RhsOperandsAt.pure _ _ _ _
  · intro live value member
    exact Nat.le_trans bound (freshValues_lowerArgs args env before values middle run live value member)

theorem rhsOperands_valueListCons {floor : Nat} {head : B ValueId} {tail : B (List ValueId)}
    (one : RhsOperandsRun floor head) (two : RhsOperandsRun floor tail) (advance : AdvB head) :
    RhsOperandsRun floor (do let value ← head; let values ← tail; pure (value :: values)) := by
  intro env before bound
  apply RhsOperandsAt.bindRun (one env before bound)
  intro value middle run
  exact (two env middle (Nat.le_trans bound (advance env before value middle run).vals)).bind
    (RhsOperandsAt.pure _ _ _ _)

end Goose.Lower.Validation
