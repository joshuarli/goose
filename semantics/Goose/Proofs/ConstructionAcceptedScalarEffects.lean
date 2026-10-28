import Goose.Proofs.ConstructionAcceptedScalarEntryWitness

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

def GlobalEffectTargetsBounded (effects : Eff) (count : Nat) : Prop :=
  ∀ id, .global id ∈ effects.accessTargets → id < count

theorem globalEffectsAvailable_iff_bounded (interpretation : RootInterpretation) (effects : Eff) :
    GlobalEffectsAvailable interpretation interpretation.globalCount effects ↔
      GlobalEffectTargetsBounded effects interpretation.globalCount := by
  constructor
  · intro available id member
    exact available (.global id) member id rfl
  · intro bounded target member global rooted
    cases target with
    | global id =>
      change global = id at rooted
      subst global
      exact bounded id member
    | param id =>
      exact rooted.2

theorem typeExpr_globalRead_bound (fuel : Nat) (environment : TypingEnv) (id : Nat)
    (before after : Nat) (types : List Ty)
    (typed : typeExpr fuel environment (.read (.global id)) before = .ok (types, after)) :
    id < environment.globalLimit := by
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at typed; cases typed
  | succ fuel =>
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      by_cases available : id < environment.globalLimit
      · exact available
      · have outside : id ≥ environment.globalLimit := Nat.le_of_not_gt available
        simp only [typeExpr, typePlace, outside, ↓reduceIte, bind, StateT.bind] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed

theorem globalRead_effects_bounded (environment : PEnv) (id count : Nat) (before after : RState)
    (roots : List RootRef) (bounded : GlobalEffectTargetsBounded before.eff count) (inside : id < count)
    (rooted : rpExpr environment (.read (.global id)) before = .ok (roots, after)) :
    GlobalEffectTargetsBounded after.eff count := by
  have extracted := congrArg
    (fun result : Except Goose.Core.Rejection (List RootRef × RState) =>
      result.toOption.map (fun pair => pair.2.eff.accessTargets)) rooted
  change some (addTargets before.eff.reads [.global id] ++ before.eff.writes ++ before.eff.grows ++ before.eff.shrinks) =
    some after.eff.accessTargets at extracted
  have access := (Option.some.inj extracted).symm
  intro target member
  rw [access] at member
  simp only [addTargets, List.foldl_cons, List.foldl_nil] at member
  split at member
  · exact bounded target member
  · simp only [List.mem_append, List.mem_singleton] at member
    rcases member with (((old | same) | writes) | grows) | shrinks
    · exact bounded target (by simp only [Eff.accessTargets, List.mem_append]; exact Or.inl (Or.inl (Or.inl old)))
    · cases same; exact inside
    · exact bounded target (by simp only [Eff.accessTargets, List.mem_append]; exact Or.inl (Or.inl (Or.inr writes)))
    · exact bounded target (by simp only [Eff.accessTargets, List.mem_append]; exact Or.inl (Or.inr grows))
    · exact bounded target (by simp only [Eff.accessTargets, List.mem_append]; exact Or.inr shrinks)

theorem localRead_accessTargets (environment : PEnv) (id : Nat) (before after : RState)
    (roots : List RootRef) (rooted : rpExpr environment (.read (.var id)) before = .ok (roots, after)) :
    after.eff.accessTargets = before.eff.accessTargets := by
  cases declared : environment.impl.vars[id]? with
  | none =>
    have extracted := congrArg
      (fun result : Except Goose.Core.Rejection (List RootRef × RState) =>
        result.toOption.map (fun pair => pair.2.eff.accessTargets)) rooted
    simp [rpExpr, rpPlace, readRoots, declared, addReads, addRoots, rootsTargets, addTargets,
      modify, bind, pure] at extracted
    change some before.eff.accessTargets = some after.eff.accessTargets at extracted
    exact (Option.some.inj extracted).symm
  | some descriptor =>
    cases refLike : descriptor.ty.isRefLike with
    | false =>
      have extracted := congrArg
        (fun result : Except Goose.Core.Rejection (List RootRef × RState) =>
          result.toOption.map (fun pair => pair.2.eff.accessTargets)) rooted
      simp [rpExpr, rpPlace, readRoots, declared, refLike, addReads, addRoots, rootsTargets, addTargets,
        modify, bind, pure] at extracted
      change some before.eff.accessTargets = some after.eff.accessTargets at extracted
      exact (Option.some.inj extracted).symm
    | true =>
      cases annotation : environment.ann id with
      | none =>
        simp [rpExpr, rpPlace, readRoots, declared, refLike, annotation, addReads, addRoots, rootsTargets, addTargets,
          modify, bind, pure] at rooted
        change Except.error _ = Except.ok _ at rooted
        cases rooted
      | some resultRoots =>
        have extracted := congrArg
          (fun result : Except Goose.Core.Rejection (List RootRef × RState) =>
            result.toOption.map (fun pair => pair.2.eff.accessTargets)) rooted
        simp [rpExpr, rpPlace, readRoots, declared, refLike, annotation, addReads, addRoots, rootsTargets, addTargets,
          modify, bind, pure] at extracted
        change some before.eff.accessTargets = some after.eff.accessTargets at extracted
        exact (Option.some.inj extracted).symm

theorem unaryEffect_operands (source : PEnv) (operation : Goose.Core.UnOp) (expression : Expr)
    (origin : Goose.Core.OriginId) (before after : RState) (roots : List RootRef)
    (rooted : rpExpr source (.un operation expression origin) before = .ok (roots, after)) :
    ∃ operandRoots middle, rpExpr source expression before = .ok (operandRoots, middle) ∧
      after.eff.accessTargets = middle.eff.accessTargets := by
  change (Except.bind (rpExpr source expression before) _) = .ok (roots, after) at rooted
  cases operand : rpExpr source expression before with
  | error failure => simp only [operand, Except.bind] at rooted; cases rooted
  | ok value =>
    obtain ⟨operandRoots, middle⟩ := value
    simp only [operand, Except.bind] at rooted
    cases operation with
    | bitnot =>
      change Except.ok ([], middle) = Except.ok (roots, after) at rooted
      cases rooted
      exact ⟨operandRoots, _, rfl, rfl⟩
    | neg =>
      change Except.ok ([], { middle with eff := { middle.eff with aborts := true } }) = Except.ok (roots, after) at rooted
      cases rooted
      exact ⟨operandRoots, middle, rfl, rfl⟩

theorem conversionEffect_operands (source : PEnv) (kind : Goose.Core.ConvKind) (target : Ty) (expression : Expr)
    (origin : Goose.Core.OriginId) (before after : RState) (roots : List RootRef)
    (rooted : rpExpr source (.conv kind target expression origin) before = .ok (roots, after)) :
    ∃ operandRoots middle, rpExpr source expression before = .ok (operandRoots, middle) ∧
      after.eff.accessTargets = middle.eff.accessTargets := by
  change (Except.bind (rpExpr source expression before) _) = .ok (roots, after) at rooted
  cases operand : rpExpr source expression before with
  | error failure => simp only [operand, Except.bind] at rooted; cases rooted
  | ok value =>
    obtain ⟨operandRoots, middle⟩ := value
    simp only [operand, Except.bind] at rooted
    cases kind with
    | widen | asUnchecked =>
      change Except.ok ([], middle) = Except.ok (roots, after) at rooted
      cases rooted
      exact ⟨operandRoots, _, rfl, rfl⟩
    | as =>
      change Except.ok ([], { middle with eff := { middle.eff with aborts := true } }) = Except.ok (roots, after) at rooted
      cases rooted
      exact ⟨operandRoots, middle, rfl, rfl⟩

#print axioms unaryEffect_operands
#print axioms conversionEffect_operands
theorem binaryEffect_end (source : PEnv) (operation : Goose.Core.BinOp) (left right : Expr)
    (origin : Goose.Core.OriginId) (roots leftRoots rightRoots : List RootRef) (before after middle final : RState)
    (rooted : rpExpr source (.bin operation left right origin) before = .ok (roots, after))
    (first : rpExpr source left before = .ok (leftRoots, middle))
    (second : rpExpr source right middle = .ok (rightRoots, final)) : after.eff.accessTargets = final.eff.accessTargets := by
  change (Except.bind (rpExpr source left before) _) = .ok (roots, after) at rooted
  simp only [first, Except.bind] at rooted
  change (Except.bind (rpExpr source right middle) _) = .ok (roots, after) at rooted
  simp only [second, Except.bind] at rooted
  cases operation <;> first
    | change Except.ok ([], final) = Except.ok (roots, after) at rooted; cases rooted; rfl
    | change Except.ok ([], { final with eff := { final.eff with aborts := true } }) = Except.ok (roots, after) at rooted
      cases rooted; rfl

#print axioms binaryEffect_end
theorem scalarLeaf_effects_bounded {expression : Expr} (form : AcceptedScalarExpression expression)
    (fuel : Nat) (environment : TypingEnv) (source : PEnv) (count : Nat)
    (beforeCounter afterCounter : Nat) (before after : RState) (types : List Ty) (roots : List RootRef)
    (limit : environment.globalLimit ≤ count) (bounded : GlobalEffectTargetsBounded before.eff count)
    (typed : typeExpr fuel environment expression beforeCounter = .ok (types, afterCounter))
    (rooted : rpExpr source expression before = .ok (roots, after)) : GlobalEffectTargetsBounded after.eff count := by
  cases form with
  | integer type value =>
    change Except.ok ([], before) = Except.ok (roots, after) at rooted
    cases rooted
    exact bounded
  | boolean value =>
    change Except.ok ([], before) = Except.ok (roots, after) at rooted
    cases rooted
    exact bounded
  | localRead id =>
    have same := localRead_accessTargets source id before after roots rooted
    intro target member
    exact bounded target (by rw [← same]; exact member)
  | globalRead id =>
    have inside := Nat.lt_of_lt_of_le (typeExpr_globalRead_bound fuel environment id beforeCounter afterCounter types typed) limit
    exact globalRead_effects_bounded source id count before after roots bounded inside rooted

theorem notScalar_effects_bounded {expression : Expr} (form : AcceptedNotExpression expression) :
    ∀ (fuel : Nat) (environment : TypingEnv) (source : PEnv) (count : Nat)
      (beforeCounter afterCounter : Nat) (before after : RState) (types : List Ty) (roots : List RootRef),
      environment.globalLimit ≤ count → GlobalEffectTargetsBounded before.eff count →
      typeExpr fuel environment expression beforeCounter = .ok (types, afterCounter) →
      rpExpr source expression before = .ok (roots, after) → GlobalEffectTargetsBounded after.eff count := by
  induction form with
  | scalar form =>
    intro fuel environment source count beforeCounter afterCounter before after types roots limit bounded typed rooted
    exact scalarLeaf_effects_bounded form fuel environment source count beforeCounter afterCounter before after types roots
      limit bounded typed rooted
  | @not expression form ih =>
    intro fuel environment source count beforeCounter afterCounter before after types roots limit bounded typed rooted
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      have shape := typeExpr_not_singleton (fuel + 1) environment expression beforeCounter afterCounter types typed
      subst types
      obtain ⟨_, operandTyped⟩ := typeExpr_not_operand fuel environment expression beforeCounter afterCounter .bool typed
      obtain ⟨_, operandRoots, operandRooted⟩ := rpExpr_not_operand source expression before after roots rooted
      exact ih fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        beforeCounter afterCounter before after [.bool] operandRoots limit bounded operandTyped operandRooted

theorem numericScalar_effects_bounded {expression : Expr} (form : AcceptedNumericExpression expression) :
    ∀ (fuel : Nat) (environment : TypingEnv) (source : PEnv) (count : Nat)
      (beforeCounter afterCounter : Nat) (before after : RState) (types : List Ty) (roots : List RootRef),
      environment.globalLimit ≤ count → GlobalEffectTargetsBounded before.eff count →
      typeExpr fuel environment expression beforeCounter = .ok (types, afterCounter) →
      rpExpr source expression before = .ok (roots, after) → GlobalEffectTargetsBounded after.eff count := by
  induction form with
  | scalar form =>
    intro fuel environment source count beforeCounter afterCounter before after types roots limit bounded typed rooted
    exact notScalar_effects_bounded form fuel environment source count beforeCounter afterCounter before after types roots
      limit bounded typed rooted
  | @unary expression operation origin form ih =>
    intro fuel environment source count beforeCounter afterCounter before after types roots limit bounded typed rooted
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      obtain ⟨ty, shape⟩ := typeExpr_unary_singleton (fuel + 1) environment expression operation origin beforeCounter afterCounter types typed
      subst types
      obtain ⟨integer, _, operandTyped⟩ := typeExpr_un_operand fuel environment operation expression origin beforeCounter afterCounter ty typed
      obtain ⟨operandRoots, middle, operandRooted, same⟩ := unaryEffect_operands source operation expression origin before after roots rooted
      have result := ih fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        beforeCounter afterCounter before middle [.int integer] operandRoots limit bounded operandTyped operandRooted
      intro id member
      apply result id
      rw [← same]
      exact member
  | @conversion expression kind target origin form ih =>
    intro fuel environment source count beforeCounter afterCounter before after types roots limit bounded typed rooted
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      have shape := typeExpr_conversion_singleton (fuel + 1) environment expression kind target origin beforeCounter afterCounter types typed
      subst types
      obtain ⟨integer, _, _, _, operandTyped⟩ := typeExpr_conv_operand fuel environment kind target expression origin beforeCounter afterCounter target typed
      obtain ⟨operandRoots, middle, operandRooted, same⟩ := conversionEffect_operands source kind target expression origin before after roots rooted
      have result := ih fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        beforeCounter afterCounter before middle [.int integer] operandRoots limit bounded operandTyped operandRooted
      intro id member
      apply result id
      rw [← same]
      exact member

theorem recursiveScalar_effects_bounded {expression : Expr} (form : AcceptedBinaryExpression expression) :
    ∀ (fuel : Nat) (environment : TypingEnv) (source : PEnv) (count : Nat)
      (beforeCounter afterCounter : Nat) (before after : RState) (types : List Ty) (roots : List RootRef),
      environment.globalLimit ≤ count → GlobalEffectTargetsBounded before.eff count →
      typeExpr fuel environment expression beforeCounter = .ok (types, afterCounter) →
      rpExpr source expression before = .ok (roots, after) → GlobalEffectTargetsBounded after.eff count := by
  induction form with
  | numeric form =>
    intro fuel environment source count beforeCounter afterCounter before after types roots limit bounded typed rooted
    exact numericScalar_effects_bounded form fuel environment source count beforeCounter afterCounter before after types roots
      limit bounded typed rooted
  | @binary left right operation origin leftForm rightForm leftIH rightIH =>
    intro fuel environment source count beforeCounter afterCounter before after types roots limit bounded typed rooted
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      obtain ⟨ty, shape⟩ := typeExpr_binary_singleton (fuel + 1) environment left right operation origin beforeCounter afterCounter types typed
      subst types
      obtain ⟨integer, counter, _, leftTyped, rightTyped⟩ := typeExpr_bin_operands fuel environment operation left right origin beforeCounter afterCounter ty typed
      obtain ⟨_, leftRoots, rightRoots, middle, final, leftRooted, rightRooted, _, _⟩ := rpExpr_bin_operands source operation left right origin before after roots rooted
      have first := leftIH fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        beforeCounter counter before middle [.int integer] leftRoots limit bounded leftTyped leftRooted
      have second := rightIH fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        counter afterCounter middle final [.int integer] rightRoots limit first rightTyped rightRooted
      have same := binaryEffect_end source operation left right origin roots leftRoots rightRoots before after middle final rooted leftRooted rightRooted
      intro id member
      exact second id (by rw [← same]; exact member)
  | @comparison left right operation leftForm rightForm leftIH rightIH =>
    intro fuel environment source count beforeCounter afterCounter before after types roots limit bounded typed rooted
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      have shape := typeExpr_comparison_singleton (fuel + 1) environment left right operation beforeCounter afterCounter types typed
      subst types
      obtain ⟨ty, counter, _, _, leftTyped, rightTyped⟩ := typeExpr_cmp_operands fuel environment operation left right beforeCounter afterCounter .bool typed
      obtain ⟨_, leftRoots, rightRoots, middle, leftRooted, rightRooted, _⟩ := rpExpr_cmp_operands source operation left right before after roots rooted
      have first := leftIH fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        beforeCounter counter before middle [ty] leftRoots limit bounded leftTyped leftRooted
      exact rightIH fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        counter afterCounter middle after [ty] rightRoots limit first rightTyped rightRooted
  | @conjunction left right leftForm rightForm leftIH rightIH =>
    intro fuel environment source count beforeCounter afterCounter before after types roots limit bounded typed rooted
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      have shape := typeExpr_booleanBinary_singleton (fuel + 1) environment left right true beforeCounter afterCounter types typed
      subst types
      obtain ⟨counter, _, leftTyped, rightTyped⟩ := typeExpr_shortCircuit_operands true fuel environment left right beforeCounter afterCounter .bool typed
      have cmpRooted : rpExpr source (.cmp .eq left right) before = .ok (roots, after) := rooted
      obtain ⟨_, leftRoots, rightRoots, middle, leftRooted, rightRooted, _⟩ := rpExpr_cmp_operands source .eq left right before after roots cmpRooted
      have first := leftIH fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        beforeCounter counter before middle [.bool] leftRoots limit bounded leftTyped leftRooted
      exact rightIH fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        counter afterCounter middle after [.bool] rightRoots limit first rightTyped rightRooted
  | @disjunction left right leftForm rightForm leftIH rightIH =>
    intro fuel environment source count beforeCounter afterCounter before after types roots limit bounded typed rooted
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      have shape := typeExpr_booleanBinary_singleton (fuel + 1) environment left right false beforeCounter afterCounter types typed
      subst types
      obtain ⟨counter, _, leftTyped, rightTyped⟩ := typeExpr_shortCircuit_operands false fuel environment left right beforeCounter afterCounter .bool typed
      have cmpRooted : rpExpr source (.cmp .eq left right) before = .ok (roots, after) := rooted
      obtain ⟨_, leftRoots, rightRoots, middle, leftRooted, rightRooted, _⟩ := rpExpr_cmp_operands source .eq left right before after roots cmpRooted
      have first := leftIH fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        beforeCounter counter before middle [.bool] leftRoots limit bounded leftTyped leftRooted
      exact rightIH fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        counter afterCounter middle after [.bool] rightRoots limit first rightTyped rightRooted
  | @not expression form ih =>
    intro fuel environment source count beforeCounter afterCounter before after types roots limit bounded typed rooted
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      have shape := typeExpr_not_singleton (fuel + 1) environment expression beforeCounter afterCounter types typed
      subst types
      obtain ⟨_, operandTyped⟩ := typeExpr_not_operand fuel environment expression beforeCounter afterCounter .bool typed
      obtain ⟨_, operandRoots, operandRooted⟩ := rpExpr_not_operand source expression before after roots rooted
      exact ih fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        beforeCounter afterCounter before after [.bool] operandRoots limit bounded operandTyped operandRooted
  | @unary expression operation origin form ih =>
    intro fuel environment source count beforeCounter afterCounter before after types roots limit bounded typed rooted
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      obtain ⟨ty, shape⟩ := typeExpr_unary_singleton (fuel + 1) environment expression operation origin beforeCounter afterCounter types typed
      subst types
      obtain ⟨integer, _, operandTyped⟩ := typeExpr_un_operand fuel environment operation expression origin beforeCounter afterCounter ty typed
      obtain ⟨operandRoots, middle, operandRooted, same⟩ := unaryEffect_operands source operation expression origin before after roots rooted
      have result := ih fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        beforeCounter afterCounter before middle [.int integer] operandRoots limit bounded operandTyped operandRooted
      intro id member
      apply result id
      rw [← same]
      exact member
  | @conversion expression kind target origin form ih =>
    intro fuel environment source count beforeCounter afterCounter before after types roots limit bounded typed rooted
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      have shape := typeExpr_conversion_singleton (fuel + 1) environment expression kind target origin beforeCounter afterCounter types typed
      subst types
      obtain ⟨integer, _, _, _, operandTyped⟩ := typeExpr_conv_operand fuel environment kind target expression origin beforeCounter afterCounter target typed
      obtain ⟨operandRoots, middle, operandRooted, same⟩ := conversionEffect_operands source kind target expression origin before after roots rooted
      have result := ih fuel { environment with use := .ordinary, request := .value, resultRequests := [] } source count
        beforeCounter afterCounter before middle [.int integer] operandRoots limit bounded operandTyped operandRooted
      intro id member
      apply result id
      rw [← same]
      exact member


#print axioms recursiveScalar_effects_bounded
#print axioms numericScalar_effects_bounded
#print axioms notScalar_effects_bounded
#print axioms scalarLeaf_effects_bounded
#print axioms localRead_accessTargets
#print axioms globalRead_effects_bounded
#print axioms globalEffectsAvailable_iff_bounded
#print axioms typeExpr_globalRead_bound
end Goose.Proofs.ConstructionAcceptedExecution
