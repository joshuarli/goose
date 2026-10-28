import Goose.Proofs.ConstructionAcceptedParameterCallAccess
import Goose.Proofs.ConstructionAcceptedCallCheckedEffects
import Goose.Proofs.ConstructionAcceptedRecursiveRegisterArithmetic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem callEffects_zeroArgument_noParameter (callee : Impl) (context : Context) (before : Eff)
    (clear : NoParameterAccess before) : NoParameterAccess (callEffects callee context [] before) := by
  cases known : callee.summary with
  | known summary =>
    exact callEffects_noParameter callee context [] summary before known clear (by simp)
  | unknown =>
    intro id member
    apply clear id
    simpa [callEffects, known, Eff.accessTargets, rootsTargets, addTargets] using member

theorem rpExpr_zeroArgument_accessUpper {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {before after : RState} {roots : List RootRef} {origin : Nat}
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[])
    (checked : rpExpr env (.call target [] origin) before = .ok (roots, after)) :
    ∀ access ∈ after.eff.accessTargets,
      access ∈ before.eff.accessTargets ∨ access ∈ (callEffects callee context [] {}).accessTargets := by
  unfold rpExpr at checked
  simp only [rpArgs, pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind, contextAt, calleeAt,
    parameters, Array.toList_empty, List.zip, List.zipWith, List.forIn_nil] at checked
  cases content : checkContents env target [] [] with
  | error failure => simp [content, liftV] at checked
  | ok result =>
    cases result
    simp only [content, liftV] at checked
    split at checked
    · simp only [bind, StateT.bind] at checked
      cases updated : noteResultConstruction env before with
      | error failure => simp [updated, Except.bind] at checked
      | ok pair =>
        have call : rpCall env target [] pair.2 = .ok (roots, after) := by
          simpa [updated, Except.bind] using checked
        have same : pair.2.eff.accessTargets = before.eff.accessTargets := by
          simp [noteResultConstruction, modify, Eff.accessTargets] at updated ⊢
          cases updated
          rfl
        intro access member
        simpa [same] using rpCall_accessUpper [] contextAt calleeAt call access member
    · exact rpCall_accessUpper [] contextAt calleeAt checked

theorem rpExpr_zeroArgument_noParameter {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {before after : RState} {roots : List RootRef} {origin : Nat}
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (clear : NoParameterAccess before.eff)
    (checked : rpExpr env (.call target [] origin) before = .ok (roots, after)) : NoParameterAccess after.eff := by
  have mapped : NoParameterAccess (callEffects callee context [] {}) :=
    callEffects_zeroArgument_noParameter callee context {} (by simp [NoParameterAccess, Eff.accessTargets])
  intro id member
  rcases rpExpr_zeroArgument_accessUpper contextAt calleeAt parameters checked (.param id) member with prior | call
  · exact clear id prior
  · exact mapped id call

theorem unaryRegister_noParameter {config : EvalConfig} {integer : Goose.Core.IntTy} {expression : Expr}
    (form : UnaryRegisterExpression config integer expression) :
    ∀ (source : PEnv) (before after : RState) (roots : List RootRef), source.mod = config.module →
      NoParameterAccess before.eff → rpExpr source expression before = .ok (roots, after) → NoParameterAccess after.eff := by
  induction form with
  | scalar form =>
    intro source before after roots moduleEq clear rooted
    exact recursiveScalar_noParameter form source before after roots clear rooted
  | call target origin context callee contextAt calleeAt parameters results =>
    intro source before after roots moduleEq clear rooted
    exact rpExpr_zeroArgument_noParameter (by simpa [moduleEq] using contextAt) (by simpa [moduleEq] using calleeAt) parameters clear rooted
  | unary operation expression origin form ih =>
    intro source before after roots moduleEq clear rooted
    obtain ⟨operandRoots, middle, operand, same⟩ := unaryEffect_operands source operation expression origin before after roots rooted
    have result := ih source before middle operandRoots moduleEq clear operand
    intro id member
    exact result id (by rw [← same]; exact member)

theorem registerArithmetic_noParameter {config : EvalConfig} {integer : Goose.Core.IntTy} {expression : Expr}
    (form : RegisterArithmeticExpression config integer expression) :
    ∀ (source : PEnv) (before after : RState) (roots : List RootRef), source.mod = config.module →
      NoParameterAccess before.eff → rpExpr source expression before = .ok (roots, after) → NoParameterAccess after.eff := by
  induction form with
  | operand form => exact unaryRegister_noParameter form
  | @binary left right operation origin leftForm rightForm leftIH rightIH =>
    intro source before after roots moduleEq clear rooted
    obtain ⟨_, leftRoots, rightRoots, middle, final, leftRooted, rightRooted, _, _⟩ :=
      rpExpr_bin_operands source operation left right origin before after roots rooted
    have first := leftIH source before middle leftRoots moduleEq clear leftRooted
    have second := rightIH source middle final rightRoots moduleEq first rightRooted
    have same := binaryEffect_end source operation left right origin roots leftRoots rightRoots before after middle final rooted leftRooted rightRooted
    intro id member
    exact second id (by rw [← same]; exact member)

#print axioms registerArithmetic_noParameter
#print axioms unaryRegister_noParameter
#print axioms rpExpr_zeroArgument_noParameter
#print axioms rpExpr_zeroArgument_accessUpper
#print axioms callEffects_zeroArgument_noParameter
end Goose.Proofs.ConstructionAcceptedExecution
