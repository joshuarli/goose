import Goose.Proofs.ConstructionAcceptedNumericComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem typeExpr_bin_operands (fuel : Nat) (environment : TypingEnv) (operation : Goose.Core.BinOp)
    (left right : Expr) (origin : Goose.Core.OriginId) (before after : Nat) (ty : Ty)
    (checked : typeExpr (fuel + 1) environment (.bin operation left right origin) before = .ok ([ty], after)) :
    ∃ integer middle, ty = .int integer ∧
      typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } left before =
        .ok ([.int integer], middle) ∧
      typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } right middle =
        .ok ([.int integer], after) := by
  simp only [typeExpr, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel
    { environment with use := .ordinary, request := .value, resultRequests := [] } left before) _) = _ at checked
  cases leftResult : typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] } left before with
  | error failure => simp only [leftResult, Except.bind] at checked; cases checked
  | ok result =>
    obtain ⟨leftTypes, middle⟩ := result
    simp only [leftResult, Except.bind] at checked
    cases leftTypes with
    | nil => change Except.error _ = Except.ok _ at checked; cases checked
    | cons leftType tail =>
      cases tail with
      | cons other rest => change Except.error _ = Except.ok _ at checked; cases checked
      | nil =>
        change (Except.bind (typeExpr fuel
          { environment with use := .ordinary, request := .value, resultRequests := [] } right middle) _) = _ at checked
        cases rightResult : typeExpr fuel
            { environment with use := .ordinary, request := .value, resultRequests := [] } right middle with
        | error failure => simp only [rightResult, Except.bind] at checked; cases checked
        | ok result =>
          obtain ⟨rightTypes, next⟩ := result
          simp only [rightResult, Except.bind] at checked
          cases rightTypes with
          | nil => change Except.error _ = Except.ok _ at checked; cases checked
          | cons rightType tail =>
            cases tail with
            | cons other rest => change Except.error _ = Except.ok _ at checked; cases checked
            | nil =>
              cases leftType <;> try (change Except.error _ = Except.ok _ at checked; cases checked)
              case int integer =>
                cases rightType <;> try (change Except.error _ = Except.ok _ at checked; cases checked)
                case int other =>
                  cases integer <;> cases other <;> first
                    | change Except.error _ = Except.ok _ at checked; cases checked
                    | change Except.ok _ = Except.ok _ at checked; cases checked; exact ⟨_, middle, rfl, rfl, rightResult⟩

theorem typeExpr_cmp_operands (fuel : Nat) (environment : TypingEnv) (operation : Goose.Core.CmpOp)
    (left right : Expr) (before after : Nat) (ty : Ty)
    (checked : typeExpr (fuel + 1) environment (.cmp operation left right) before = .ok ([ty], after)) :
    ∃ operandTy middle, ty = .bool ∧ (operandTy = .bool ∨ ∃ integer, operandTy = .int integer) ∧
      typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } left before =
        .ok ([operandTy], middle) ∧
      typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } right middle =
        .ok ([operandTy], after) := by
  simp only [typeExpr, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel
    { environment with use := .ordinary, request := .value, resultRequests := [] } left before) _) = _ at checked
  cases leftResult : typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] } left before with
  | error failure => simp only [leftResult, Except.bind] at checked; cases checked
  | ok result =>
    obtain ⟨leftTypes, middle⟩ := result
    simp only [leftResult, Except.bind] at checked
    cases leftTypes with
    | nil => change Except.error _ = Except.ok _ at checked; cases checked
    | cons leftType tail =>
      cases tail with
      | cons other rest => change Except.error _ = Except.ok _ at checked; cases checked
      | nil =>
        change (Except.bind (typeExpr fuel
          { environment with use := .ordinary, request := .value, resultRequests := [] } right middle) _) = _ at checked
        cases rightResult : typeExpr fuel
            { environment with use := .ordinary, request := .value, resultRequests := [] } right middle with
        | error failure => simp only [rightResult, Except.bind] at checked; cases checked
        | ok result =>
          obtain ⟨rightTypes, next⟩ := result
          simp only [rightResult, Except.bind] at checked
          cases rightTypes with
          | nil => change Except.error _ = Except.ok _ at checked; cases checked
          | cons rightType tail =>
            cases tail with
            | cons other rest => change Except.error _ = Except.ok _ at checked; cases checked
            | nil =>
              cases leftType <;> cases rightType <;> try (change Except.error _ = Except.ok _ at checked; cases checked)
              case int.int integer other =>
                cases integer <;> cases other <;> first
                  | change Except.error _ = Except.ok _ at checked; cases checked
                  | change Except.ok _ = Except.ok _ at checked; cases checked; exact ⟨_, middle, rfl, Or.inr ⟨_, rfl⟩, rfl, rightResult⟩
              case bool.bool =>
                cases operation <;> first
                  | change Except.error _ = Except.ok _ at checked; cases checked
                  | change Except.ok _ = Except.ok _ at checked; cases checked; exact ⟨_, middle, rfl, Or.inl rfl, rfl, rightResult⟩

theorem rpExpr_cmp_operands (environment : PEnv) (operation : Goose.Core.CmpOp) (left right : Expr)
    (before after : RState) (roots : List RootRef)
    (checked : rpExpr environment (.cmp operation left right) before = .ok (roots, after)) :
    roots = [] ∧ ∃ leftRoots rightRoots middle,
      rpExpr environment left before = .ok (leftRoots, middle) ∧
      rpExpr environment right middle = .ok (rightRoots, after) ∧
      EffectTargetsIncluded middle.eff after.eff := by
  change (Except.bind (rpExpr environment left before) _) = .ok (roots, after) at checked
  cases first : rpExpr environment left before with
  | error failure => simp only [first, Except.bind] at checked; cases checked
  | ok value =>
    obtain ⟨leftRoots, middle⟩ := value
    simp only [first, Except.bind] at checked
    change (Except.bind (rpExpr environment right middle) _) = .ok (roots, after) at checked
    cases second : rpExpr environment right middle with
    | error failure => simp only [second, Except.bind] at checked; cases checked
    | ok value =>
      obtain ⟨rightRoots, final⟩ := value
      simp only [second, Except.bind] at checked
      change Except.ok ([], final) = Except.ok (roots, after) at checked
      cases checked
      exact ⟨rfl, leftRoots, rightRoots, middle, rfl, second, rpExpr_effectTargetsIncluded second⟩

theorem rpExpr_bin_operands (environment : PEnv) (operation : Goose.Core.BinOp) (left right : Expr)
    (origin : Goose.Core.OriginId) (before after : RState) (roots : List RootRef)
    (checked : rpExpr environment (.bin operation left right origin) before = .ok (roots, after)) :
    roots = [] ∧ ∃ leftRoots rightRoots middle final,
      rpExpr environment left before = .ok (leftRoots, middle) ∧
      rpExpr environment right middle = .ok (rightRoots, final) ∧
      EffectTargetsIncluded middle.eff after.eff ∧ EffectTargetsIncluded final.eff after.eff := by
  change (Except.bind (rpExpr environment left before) _) = .ok (roots, after) at checked
  cases first : rpExpr environment left before with
  | error failure => simp only [first, Except.bind] at checked; cases checked
  | ok value =>
    obtain ⟨leftRoots, middle⟩ := value
    simp only [first, Except.bind] at checked
    change (Except.bind (rpExpr environment right middle) _) = .ok (roots, after) at checked
    cases second : rpExpr environment right middle with
    | error failure => simp only [second, Except.bind] at checked; cases checked
    | ok value =>
      obtain ⟨rightRoots, final⟩ := value
      simp only [second, Except.bind] at checked
      cases operation <;> first
        | change Except.ok ([], final) = Except.ok (roots, after) at checked
          cases checked
          exact ⟨rfl, leftRoots, rightRoots, middle, _, rfl, second, rpExpr_effectTargetsIncluded second, EffectTargetsIncluded.refl _⟩
        | change Except.ok ([], { final with eff := { final.eff with aborts := true } }) = Except.ok (roots, after) at checked
          cases checked
          refine ⟨rfl, leftRoots, rightRoots, middle, final, rfl, second, ?_, ?_⟩
          · simpa only [EffectTargetsIncluded, Eff.accessTargets] using rpExpr_effectTargetsIncluded second
          · simpa only [EffectTargetsIncluded, Eff.accessTargets] using EffectTargetsIncluded.refl final.eff

theorem checkedValue_bin_operands (frame : ConstructionSourceFrame) (fuel : Nat)
    (operation : Goose.Core.BinOp) (left right : Expr) (origin : Goose.Core.OriginId) (ty : Ty)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (fuelAt : frame.typingFuel = fuel + 1)
    (checked : CheckedValue frame (.bin operation left right origin) ty roots typingAfter rootsAfter) :
    ∃ integer middle leftRoots rightRoots rootMiddle rootFinal,
      ty = .int integer ∧ roots = [] ∧
      CheckedValue (ordinaryOperandFrame frame fuel) left (.int integer) leftRoots middle rootMiddle ∧
      CheckedValue { ordinaryOperandFrame frame fuel with typingCounter := middle, rootCursor := rootMiddle }
        right (.int integer) rightRoots typingAfter rootFinal := by
  have typing := checked.typing
  rw [fuelAt] at typing
  obtain ⟨integer, middle, sameTy, leftTyping, rightTyping⟩ :=
    typeExpr_bin_operands fuel frame.typing operation left right origin frame.typingCounter typingAfter ty typing
  obtain ⟨sameRoots, leftRoots, rightRoots, rootMiddle, rootFinal, leftRootsChecked, rightRootsChecked, leftIncluded, rightIncluded⟩ :=
    rpExpr_bin_operands frame.source operation left right origin frame.rootCursor rootsAfter roots checked.provenance
  have leftAvailable : GlobalEffectsAvailable frame.interpretation frame.initialized rootMiddle.eff := by
    intro target member global rooted
    exact checked.available target (leftIncluded member) global rooted
  have rightAvailable : GlobalEffectsAvailable frame.interpretation frame.initialized rootFinal.eff := by
    intro target member global rooted
    exact checked.available target (rightIncluded member) global rooted
  exact ⟨integer, middle, leftRoots, rightRoots, rootMiddle, rootFinal, sameTy, sameRoots,
    ⟨leftTyping, leftRootsChecked, leftAvailable⟩, ⟨rightTyping, rightRootsChecked, rightAvailable⟩⟩

theorem checkedValue_cmp_operands (frame : ConstructionSourceFrame) (fuel : Nat)
    (operation : Goose.Core.CmpOp) (left right : Expr) (ty : Ty)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (fuelAt : frame.typingFuel = fuel + 1)
    (checked : CheckedValue frame (.cmp operation left right) ty roots typingAfter rootsAfter) :
    ∃ operandTy middle leftRoots rightRoots rootMiddle,
      ty = .bool ∧ roots = [] ∧ (operandTy = .bool ∨ ∃ integer, operandTy = .int integer) ∧
      CheckedValue (ordinaryOperandFrame frame fuel) left operandTy leftRoots middle rootMiddle ∧
      CheckedValue { ordinaryOperandFrame frame fuel with typingCounter := middle, rootCursor := rootMiddle }
        right operandTy rightRoots typingAfter rootsAfter := by
  have typing := checked.typing
  rw [fuelAt] at typing
  obtain ⟨operandTy, middle, sameTy, form, leftTyping, rightTyping⟩ :=
    typeExpr_cmp_operands fuel frame.typing operation left right frame.typingCounter typingAfter ty typing
  obtain ⟨sameRoots, leftRoots, rightRoots, rootMiddle, leftRootsChecked, rightRootsChecked, leftIncluded⟩ :=
    rpExpr_cmp_operands frame.source operation left right frame.rootCursor rootsAfter roots checked.provenance
  have leftAvailable : GlobalEffectsAvailable frame.interpretation frame.initialized rootMiddle.eff := by
    intro target member global rooted
    exact checked.available target (leftIncluded member) global rooted
  exact ⟨operandTy, middle, leftRoots, rightRoots, rootMiddle, sameTy, sameRoots, form,
    ⟨leftTyping, leftRootsChecked, leftAvailable⟩, ⟨rightTyping, rightRootsChecked, checked.available⟩⟩

#print axioms checkedValue_bin_operands
#print axioms checkedValue_cmp_operands
#print axioms rpExpr_bin_operands
#print axioms rpExpr_cmp_operands
#print axioms typeExpr_cmp_operands
#print axioms typeExpr_bin_operands
end Goose.Proofs.ConstructionAcceptedExecution
