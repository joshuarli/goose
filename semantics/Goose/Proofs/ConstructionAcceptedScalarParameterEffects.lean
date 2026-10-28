import Goose.Proofs.ConstructionAcceptedScalarEffects
import Goose.Proofs.ConstructionRootCorrespondenceCursors

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

def NoParameterAccess (effects : Eff) : Prop := ∀ id, .param id ∉ effects.accessTargets

theorem scalarGlobalRead_noParameter (source : PEnv) (global : Nat) (before after : RState) (roots : List RootRef)
    (clear : NoParameterAccess before.eff) (rooted : rpExpr source (.read (.global global)) before = .ok (roots, after)) :
    NoParameterAccess after.eff := by
  have extracted := congrArg
    (fun result : Except Goose.Core.Rejection (List RootRef × RState) =>
      result.toOption.map (fun pair => pair.2.eff.accessTargets)) rooted
  change some (addTargets before.eff.reads [.global global] ++ before.eff.writes ++ before.eff.grows ++ before.eff.shrinks) =
    some after.eff.accessTargets at extracted
  have access := (Option.some.inj extracted).symm
  intro id member
  rw [access] at member
  simp only [addTargets, List.foldl_cons, List.foldl_nil] at member
  split at member
  · exact clear id member
  · simp only [List.mem_append, List.mem_singleton] at member
    rcases member with (((read | same) | write) | grow) | shrink
    · exact clear id (by simp only [Eff.accessTargets, List.mem_append]; exact Or.inl (Or.inl (Or.inl read)))
    · cases same
    · exact clear id (by simp only [Eff.accessTargets, List.mem_append]; exact Or.inl (Or.inl (Or.inr write)))
    · exact clear id (by simp only [Eff.accessTargets, List.mem_append]; exact Or.inl (Or.inr grow))
    · exact clear id (by simp only [Eff.accessTargets, List.mem_append]; exact Or.inr shrink)

theorem scalarLeaf_noParameter {expression : Expr} (form : AcceptedScalarExpression expression)
    (source : PEnv) (before after : RState) (roots : List RootRef)
    (clear : NoParameterAccess before.eff) (rooted : rpExpr source expression before = .ok (roots, after)) : NoParameterAccess after.eff := by
  cases form with
  | integer type value | boolean value =>
    change Except.ok ([], before) = Except.ok (roots, after) at rooted
    cases rooted
    exact clear
  | localRead id =>
    have same := localRead_accessTargets source id before after roots rooted
    intro parameter member
    exact clear parameter (by rw [← same]; exact member)
  | globalRead id => exact scalarGlobalRead_noParameter source id before after roots clear rooted

theorem notScalar_noParameter {expression : Expr} (form : AcceptedNotExpression expression) :
    ∀ (source : PEnv) (before after : RState) (roots : List RootRef), NoParameterAccess before.eff →
      rpExpr source expression before = .ok (roots, after) → NoParameterAccess after.eff := by
  induction form with
  | scalar form => exact scalarLeaf_noParameter form
  | @not expression form ih =>
    intro source before after roots clear rooted
    obtain ⟨_, operandRoots, operandRooted⟩ := rpExpr_not_operand source expression before after roots rooted
    exact ih source before after operandRoots clear operandRooted

theorem numericScalar_noParameter {expression : Expr} (form : AcceptedNumericExpression expression) :
    ∀ (source : PEnv) (before after : RState) (roots : List RootRef), NoParameterAccess before.eff →
      rpExpr source expression before = .ok (roots, after) → NoParameterAccess after.eff := by
  induction form with
  | scalar form => exact notScalar_noParameter form
  | @unary expression operation origin form ih =>
    intro source before after roots clear rooted
    obtain ⟨operandRoots, middle, operandRooted, same⟩ := unaryEffect_operands source operation expression origin before after roots rooted
    have result := ih source before middle operandRoots clear operandRooted
    intro id member
    exact result id (by rw [← same]; exact member)
  | @conversion expression kind target origin form ih =>
    intro source before after roots clear rooted
    obtain ⟨operandRoots, middle, operandRooted, same⟩ := conversionEffect_operands source kind target expression origin before after roots rooted
    have result := ih source before middle operandRoots clear operandRooted
    intro id member
    exact result id (by rw [← same]; exact member)

theorem recursiveScalar_noParameter {expression : Expr} (form : AcceptedBinaryExpression expression) :
    ∀ (source : PEnv) (before after : RState) (roots : List RootRef), NoParameterAccess before.eff →
      rpExpr source expression before = .ok (roots, after) → NoParameterAccess after.eff := by
  induction form with
  | numeric form => exact numericScalar_noParameter form
  | @binary left right operation origin leftForm rightForm leftIH rightIH =>
    intro source before after roots clear rooted
    obtain ⟨_, leftRoots, rightRoots, middle, final, leftRooted, rightRooted, _, _⟩ :=
      rpExpr_bin_operands source operation left right origin before after roots rooted
    have first := leftIH source before middle leftRoots clear leftRooted
    have second := rightIH source middle final rightRoots first rightRooted
    have same := binaryEffect_end source operation left right origin roots leftRoots rightRoots before after middle final rooted leftRooted rightRooted
    intro id member
    exact second id (by rw [← same]; exact member)
  | @comparison left right operation leftForm rightForm leftIH rightIH =>
    intro source before after roots clear rooted
    obtain ⟨_, leftRoots, rightRoots, middle, leftRooted, rightRooted, _⟩ := rpExpr_cmp_operands source operation left right before after roots rooted
    exact rightIH source middle after rightRoots (leftIH source before middle leftRoots clear leftRooted) rightRooted
  | @conjunction left right leftForm rightForm leftIH rightIH =>
    intro source before after roots clear rooted
    have cmpRooted : rpExpr source (.cmp .eq left right) before = .ok (roots, after) := rooted
    obtain ⟨_, leftRoots, rightRoots, middle, leftRooted, rightRooted, _⟩ := rpExpr_cmp_operands source .eq left right before after roots cmpRooted
    exact rightIH source middle after rightRoots (leftIH source before middle leftRoots clear leftRooted) rightRooted
  | @disjunction left right leftForm rightForm leftIH rightIH =>
    intro source before after roots clear rooted
    have cmpRooted : rpExpr source (.cmp .eq left right) before = .ok (roots, after) := rooted
    obtain ⟨_, leftRoots, rightRoots, middle, leftRooted, rightRooted, _⟩ := rpExpr_cmp_operands source .eq left right before after roots cmpRooted
    exact rightIH source middle after rightRoots (leftIH source before middle leftRoots clear leftRooted) rightRooted
  | @not expression form ih =>
    intro source before after roots clear rooted
    obtain ⟨_, operandRoots, operandRooted⟩ := rpExpr_not_operand source expression before after roots rooted
    exact ih source before after operandRoots clear operandRooted
  | @unary expression operation origin form ih =>
    intro source before after roots clear rooted
    obtain ⟨operandRoots, middle, operandRooted, same⟩ := unaryEffect_operands source operation expression origin before after roots rooted
    have result := ih source before middle operandRoots clear operandRooted
    intro id member
    exact result id (by rw [← same]; exact member)
  | @conversion expression kind target origin form ih =>
    intro source before after roots clear rooted
    obtain ⟨operandRoots, middle, operandRooted, same⟩ := conversionEffect_operands source kind target expression origin before after roots rooted
    have result := ih source before middle operandRoots clear operandRooted
    intro id member
    exact result id (by rw [← same]; exact member)

theorem scalarTail_noParameter (source : PEnv) (scope : Nat) (expression : Expr) (form : AcceptedBinaryExpression expression)
    (before after : RState) (result : List RootRef × (Nat × Nat)) (clear : NoParameterAccess before.eff)
    (rooted : rpBlockValue source [] ⟨scope, [], some expression⟩ before = .ok (result, after)) : NoParameterAccess after.eff := by
  obtain ⟨_, middle, roots, statements, tail, resultEq⟩ := rpBlockValue_body rooted
  simp only [List.length_nil, Nat.add_zero, rpStmts, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at statements
  cases statements.2
  exact recursiveScalar_noParameter form _ before after roots clear tail

#print axioms scalarTail_noParameter
#print axioms recursiveScalar_noParameter
end Goose.Proofs.ConstructionAcceptedExecution
