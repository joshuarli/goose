import Goose.Lower.Validation.ExpressionTypingWritable
import Goose.Lower.Validation.ExpressionTypingAuthorityChecks

namespace Goose.Lower.Validation.ExpressionTypingWritableChecks

open Goose.Core Goose.GIR ExpressionTypingAuthorityChecks

def writable (value : ValueId) : Prop := value = 1 ∨ value = 2

theorem closed : WritableClosed #[] #[] chain types writable authorized := by
  constructor
  · intro value member
    rcases member with rfl | rfl <;> decide
  · simp [chain]
  · intro block blockMember value op member allowed
    simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at blockMember
    subst block
    simp only [List.mem_cons, List.not_mem_nil, or_false, Inst.def.injEq, reduceCtorEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [writable] at allowed
    · change 0 < 3
      decide
    · change 1 < 3
      decide
    · simp [writable] at allowed
  · intro block blockMember term member
    simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at blockMember
    subst block
    simp only [List.mem_cons, List.not_mem_nil, or_false, Inst.term.injEq, reduceCtorEq, false_or] at member
    subst term
    simp [Term.permissionEdges]

theorem immutable_binding_mutable_element :
    (permissionsAt (chain.permissionsFromTables #[] #[] types) 0).1 = false ∧
    (permissionsAt (chain.permissionsFromTables #[] #[] types) 2).1 = true := by
  constructor
  · decide
  · exact closed.permissions ExpressionTypingAuthorityChecks.closed 2 (Or.inr rfl)

#print axioms WritableClosed.permissions

end Goose.Lower.Validation.ExpressionTypingWritableChecks
