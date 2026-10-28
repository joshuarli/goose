import Goose.Proofs.ConstructionAcceptedRegisterBreakOutcome

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem blockResultTypes_integerTail (fuel : Nat) (environment : DeclarationEnv)
    (scope : Nat) (statements : List Stmt) (ty : Goose.Core.IntTy) (value : Int) :
    let block : Block := ⟨scope, statements, some (.lit ty value)⟩
    blockResultTypes? (max fuel (blockQueryBudget block)) environment block = some [.int ty] := by
  let block : Block := ⟨scope, statements, some (.lit ty value)⟩
  have enough : 2 ≤ max fuel (blockQueryBudget block) := by
    apply Nat.le_trans _ (Nat.le_max_right _ _)
    simp [block, blockQueryBudget, expressionQueryBudget]
  obtain ⟨other, same⟩ := Nat.exists_eq_add_of_le enough
  change blockResultTypes? (max fuel (blockQueryBudget block)) environment block = some [.int ty]
  rw [same]
  rw [Nat.add_comm 2 other]
  simp [block, blockResultTypes?, expressionResultTypes?, DeclarationEnv.exprType?]

theorem blockResultTypes_booleanTail (fuel : Nat) (environment : DeclarationEnv)
    (scope : Nat) (statements : List Stmt) (value : Bool) :
    let block : Block := ⟨scope, statements, some (.bool value)⟩
    blockResultTypes? (max fuel (blockQueryBudget block)) environment block = some [.bool] := by
  let block : Block := ⟨scope, statements, some (.bool value)⟩
  have enough : 2 ≤ max fuel (blockQueryBudget block) := by
    apply Nat.le_trans _ (Nat.le_max_right _ _)
    simp [block, blockQueryBudget, expressionQueryBudget]
  obtain ⟨other, same⟩ := Nat.exists_eq_add_of_le enough
  change blockResultTypes? (max fuel (blockQueryBudget block)) environment block = some [.bool]
  rw [same, Nat.add_comm 2 other]
  simp [block, blockResultTypes?, expressionResultTypes?, DeclarationEnv.exprType?]

theorem channelsFor_scalarRegister (layout : LayoutEnv) (act : Nat) (ty : Ty) (origin : Nat)
    (state : ExecutionState) (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool) :
    channelsFor layout act [⟨ty, if ty.nonfixed then .value else .register, none⟩] origin state =
      .ok [.register ty] state := by
  rcases scalar with ⟨intTy, same⟩ | same <;> simp [same, Ty.nonfixed, channelsFor, bind, pure]

#print axioms channelsFor_scalarRegister
#print axioms blockResultTypes_booleanTail
#print axioms blockResultTypes_integerTail
end Goose.Proofs.ConstructionAcceptedExecution
