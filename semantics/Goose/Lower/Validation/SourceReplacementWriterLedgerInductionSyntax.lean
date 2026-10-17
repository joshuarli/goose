import Goose.Core.Demand

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core

theorem demand_child_size (parent child : DemandNode) (member : some child ∈ parent.children) :
    sizeOf child < sizeOf parent := by
  cases parent with
  | expression expression =>
    cases expression with
    | call callee arguments origin =>
      simp only [DemandNode.children, List.mem_map] at member
      rcases member with ⟨argument, argumentMember, childEq⟩
      cases argument with
      | byVal expression =>
        simp only [Option.some.injEq] at childEq
        subst child
        have childLeArgument : sizeOf (DemandNode.expression expression) ≤ sizeOf (Arg.byVal expression) := by
          simp +arith
        have argumentList := List.sizeOf_lt_of_mem argumentMember
        have childList := Nat.lt_of_le_of_lt childLeArgument argumentList
        simp +arith at childList ⊢
        omega
      | byRef mutability place =>
        simp only [Option.some.injEq] at childEq
        subst child
        have childLeArgument : sizeOf (DemandNode.place place) ≤ sizeOf (Arg.byRef mutability place) := by
          simp +arith
        have argumentList := List.sizeOf_lt_of_mem argumentMember
        have childList := Nat.lt_of_le_of_lt childLeArgument argumentList
        simp +arith at childList ⊢
        omega
    | arrLit ty expressions | structLit ty expressions =>
      simp only [DemandNode.children, List.mem_map, Function.comp_apply] at member
      rcases member with ⟨expression, expressionMember, childEq⟩
      simp only [Option.some.injEq] at childEq
      subst child
      have expressionList := List.sizeOf_lt_of_mem expressionMember
      have childLeList : sizeOf (DemandNode.expression expression) ≤ sizeOf expressions := by
        simp +arith at expressionList ⊢
        omega
      simp +arith at childLeList ⊢
      omega
    | _ =>
      simp only [DemandNode.children] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
      repeat' first
        | (rcases member with member | member)
        | contradiction
        | subst child
      all_goals simp +arith
  | place place =>
    cases place <;> simp only [DemandNode.children] at member
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
      repeat' first
        | (rcases member with member | member)
        | contradiction
        | subst child
      all_goals simp +arith
  | view view =>
    cases view <;> simp only [DemandNode.children] at member
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
      repeat' first
        | (rcases member with member | member)
        | contradiction
        | subst child
      all_goals simp +arith
  | bound bound =>
    cases bound <;> simp only [DemandNode.children] at member
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
      repeat' first
        | (rcases member with member | member)
        | contradiction
        | subst child
      all_goals simp +arith
  | statement statement =>
    cases statement with
    | print arguments origin =>
      simp only [DemandNode.children, List.mem_map] at member
      rcases member with ⟨argument, argumentMember, childEq⟩
      cases argument with
      | text text => simp at childEq
      | expr expression =>
        simp only [Option.some.injEq] at childEq
        subst child
        have childPrintArgument : sizeOf (DemandNode.expression expression) ≤ sizeOf (PrintArg.expr expression) := by
          simp +arith
        have argumentList := List.sizeOf_lt_of_mem argumentMember
        have childList := Nat.lt_of_le_of_lt childPrintArgument argumentList
        simp +arith at childList ⊢
        omega
    | resize place size fill origin =>
      cases fill <;> simp only [DemandNode.children, Option.map_none, Option.map_some] at member
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
        repeat' first
          | (rcases member with member | member)
          | contradiction
          | subst child
        all_goals simp +arith
    | ifS condition yes no origin =>
      cases no <;> simp only [DemandNode.children, Option.map_none, Option.map_some] at member
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
        repeat' first
          | (rcases member with member | member)
          | contradiction
          | subst child
        all_goals simp +arith
    | ret value origin =>
      cases value <;> simp only [DemandNode.children, Option.map_none, Option.map_some] at member
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
        repeat' first
          | (rcases member with member | member)
          | contradiction
          | subst child
        all_goals simp +arith
    | _ =>
      simp only [DemandNode.children] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at member
      repeat' first
        | (rcases member with member | member)
        | contradiction
        | subst child
      all_goals simp +arith
  | block block =>
    cases block with
    | mk scope statements value =>
      cases value with
      | none =>
        simp only [DemandNode.children, Option.map_none, List.mem_append] at member
        rcases member with statementMember | valueMember
        · simp only [List.mem_map, Function.comp_apply] at statementMember
          rcases statementMember with ⟨statement, statementMember, childEq⟩
          simp only [Option.some.injEq] at childEq
          subst child
          have statementList := List.sizeOf_lt_of_mem statementMember
          have childLeList : sizeOf (DemandNode.statement statement) ≤ sizeOf statements := by
            simp +arith at statementList ⊢
            omega
          simp +arith at childLeList ⊢
          omega
        · simp at valueMember
      | some expression =>
        simp only [DemandNode.children, Option.map_some, List.mem_append] at member
        rcases member with statementMember | valueMember
        · simp only [List.mem_map, Function.comp_apply] at statementMember
          rcases statementMember with ⟨statement, statementMember, childEq⟩
          simp only [Option.some.injEq] at childEq
          subst child
          have statementList := List.sizeOf_lt_of_mem statementMember
          have childLeList : sizeOf (DemandNode.statement statement) ≤ sizeOf statements := by
            simp +arith at statementList ⊢
            omega
          simp +arith at childLeList ⊢
          omega
        · simp only [List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at valueMember
          subst child
          simp +arith

#print axioms demand_child_size

end Goose.Lower.Validation.SourceReplacementWriterLedger
