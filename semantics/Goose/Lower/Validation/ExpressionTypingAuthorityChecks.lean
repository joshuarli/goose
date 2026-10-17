import Goose.Lower.Validation.ExpressionTypingAuthority

namespace Goose.Lower.Validation.ExpressionTypingAuthorityChecks

open Goose.Core Goose.GIR

def arrayTy : Ty := .arr (.int .i64) 4

def chain : Func :=
  { name := "contents", params := [], results := [],
    slots := #[⟨arrayTy, .immutable, 0, 0⟩], scopes := #[], summary := .unknown, org := none,
    blocks := #[⟨[], [.def 0 (.slotAddr 0), .def 1 (.snapshot .borrowed 0),
      .def 2 (.refElem 1 3), .def 3 (.constInt .i64 0), .term (.ret [] none)]⟩] }

def types : Array (Option VTy) :=
  #[some (.data (.ref .readOnly arrayTy)), some (.view .mutable (.int .i64)),
    some (.data (.ref .mutable (.int .i64))), some (.data (.int .i64))]

def authorized (value : ValueId) : Prop := value < 3

theorem closed : ContentsClosed #[] #[] chain types authorized := by
  constructor
  · intro value member
    change value < 3 at member
    change value < 4
    exact Nat.lt_trans member (by decide)
  · simp [chain]
  · intro block blockMember value op member allowed
    simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at blockMember
    subst block
    simp only [List.mem_cons, List.not_mem_nil, or_false, Inst.def.injEq, reduceCtorEq] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, rfl⟩
    · change 0 < 3
      decide
    · change 1 < 3
      decide
    · change 3 < 3 at allowed
      exact (Nat.lt_irrefl 3 allowed).elim
  · intro block blockMember term member
    simp only [chain, List.mem_cons, List.not_mem_nil, or_false] at blockMember
    subst block
    simp only [List.mem_cons, List.not_mem_nil, or_false, Inst.term.injEq, reduceCtorEq, false_or] at member
    subst term
    simp [Term.permissionEdges]

theorem readonly_owner_contents :
    (permissionsAt (chain.permissionsFromTables #[] #[] types) 0).2 = true := closed.permissions 0 (by change 0 < 3; decide)

theorem mutable_element_contents :
    (permissionsAt (chain.permissionsFromTables #[] #[] types) 2).2 = true := closed.permissions 2 (by change 2 < 3; decide)

#guard chain.permissionsFromTables #[] #[] types == #[(false, true), (true, true), (true, true), (false, false)]

#print axioms ContentsClosed.round
#print axioms ContentsClosed.permissions

end Goose.Lower.Validation.ExpressionTypingAuthorityChecks
