import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceMutationsCommon

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem printArguments_no_reference {typingEnv : TEnv} {env : PEnv}
    {vt : Array (Option VTy)} {returnTypes : List Ty}
    (arguments : List PrintArg) (tables : SourceRootTables typingEnv env)
    {initial : LS} {start finish : Nat}
    (typed : Core.tyPrintArgs typingEnv arguments start = .ok ((), finish))
    (generated : GeneratedBuilderState initial)
    (native : NativeRows vt (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2)
    (live : (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).2.cur.isSome = true) :
    ∀ value ∈ (lowerPrintArgs arguments (lowerEnv env.mod env.impl.vars returnTypes) initial).1.flatMap PrintPart.uses,
      ∀ mutability payload, vt[value]? ≠ some (some (.data (.ref mutability payload))) := by
  cases arguments with
  | nil => simp [lowerPrintArgs, pure_run]
  | cons argument rest =>
    cases argument with
    | text text =>
      simpa only [lowerPrintArgs, bind_run, pure_run, List.flatMap_cons, PrintPart.uses, List.nil_append] using
        printArguments_no_reference rest tables typed generated native live
    | expr expression =>
      obtain ⟨type, middle, expressionTyped, tailTyped⟩ := (st_bind_ok _ _ _ _).mp typed
      have scalar : (∃ integer, type = .int integer) ∨ type = .bool := by
        cases type <;> first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr rfl | exact ((rej_ok _ _ _ _).mp tailTyped).elim
      have tailTyped : Core.tyPrintArgs typingEnv rest middle = .ok ((), finish) := by
        rcases scalar with ⟨integer, rfl⟩ | rfl <;> exact tailTyped
      let le := lowerEnv env.mod env.impl.vars returnTypes
      let child := lowerExpr expression le initial
      have childLive : child.2.cur.isSome = true :=
        (dead_lowerPrintArgs rest).live_before rfl live
      have childNative : NativeRows vt child.2 := native.of_prefix (types_lowerPrintArgs rest le child.2 _ _ rfl)
      have childRow := tables.occurrence_native_expression_row childNative generated expressionTyped
        (rfl : lowerExpr expression le initial = child) childLive
      intro value member mutability payload reference
      simp only [lowerPrintArgs, bind_run, pure_run, List.flatMap_cons, PrintPart.uses,
        List.singleton_append, List.mem_cons] at member
      rcases member with same | member
      · subst value
        rw [childRow] at reference
        rcases scalar with ⟨integer, rfl⟩ | rfl <;> cases reference
      · exact printArguments_no_reference rest tables tailTyped (generated.lowerExpr expression (env := le) rfl)
          native live value member mutability payload reference
termination_by arguments.length

end Goose.Lower.Validation.ReplacementContentFlowSource
