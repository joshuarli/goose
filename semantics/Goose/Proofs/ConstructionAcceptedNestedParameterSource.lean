import Goose.Proofs.ConstructionAcceptedNestedParameterCallEffects
import Goose.Proofs.ConstructionAcceptedCallResultRoots
import Goose.Proofs.ConstructionAcceptedBinaryTyping
import Goose.Proofs.ConstructionAcceptedZeroCallParameterEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

inductive NestedParameterExpression (config : EvalConfig) (integer : Goose.Core.IntTy) (implementation : Impl) : Expr → Prop
  | literal (value : Int) : NestedParameterExpression config integer implementation (.lit integer value)
  | localRead (id : Nat) (descriptor : LocalVar) : implementation.vars[id]? = some descriptor →
      ((∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool) →
      NestedParameterExpression config integer implementation (.read (.var id))
  | binary {left right : Expr} (operation : Goose.Core.BinOp) (origin : Nat) :
      NestedParameterExpression config integer implementation left → NestedParameterExpression config integer implementation right →
      NestedParameterExpression config integer implementation (.bin operation left right origin)
  | zeroCall (target origin : Nat) (context : Context) (callee : Impl) :
      config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some callee →
      callee.params = #[] → callee.results = #[⟨.int integer, .register, none⟩] →
      NestedParameterExpression config integer implementation (.call target [] origin)
  | call {argument : Expr} (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (summary : Summary) :
      config.module.contexts[target]? = some context → config.module.impls[context.impl]? = some callee →
      callee.params = #[parameter] → callee.results = #[⟨.int integer, .register, none⟩] →
      callee.summary = .known summary → NestedParameterExpression config integer implementation argument →
      NestedParameterExpression config integer implementation (.call target [.byVal argument] origin)

theorem nestedParameterExpression_source {config : EvalConfig} {integer : Goose.Core.IntTy} {implementation : Impl} {expression : Expr}
    (form : NestedParameterExpression config integer implementation expression) :
    ∀ (source : PEnv) (before after : RState) (roots : List RootRef), source.mod = config.module → source.impl = implementation →
      NoParameterAccess before.eff → rpExpr source expression before = .ok (roots, after) →
      roots = [] ∧ NoParameterAccess after.eff := by
  induction form with
  | literal value =>
    intro source before after roots moduleEq implementationEq clear rooted
    change Except.ok ([], before) = Except.ok (roots, after) at rooted
    cases rooted
    exact ⟨rfl, clear⟩
  | localRead id descriptor declared scalar =>
    intro source before after roots moduleEq implementationEq clear rooted
    have sourceDeclared : source.impl.vars[id]? = some descriptor := by simpa [implementationEq] using declared
    have empty := scalarLocal_argument_roots source id descriptor before after roots sourceDeclared scalar rooted
    have same := localRead_accessTargets source id before after roots rooted
    refine ⟨empty, ?_⟩
    intro parameter member
    exact clear parameter (by rw [← same]; exact member)
  | @binary left right operation origin leftForm rightForm leftIH rightIH =>
    intro source before after roots moduleEq implementationEq clear rooted
    obtain ⟨rootsEmpty, leftRoots, rightRoots, middle, final, leftRooted, rightRooted, _, _⟩ :=
      rpExpr_bin_operands source operation left right origin before after roots rooted
    have first := leftIH source before middle leftRoots moduleEq implementationEq clear leftRooted
    have second := rightIH source middle final rightRoots moduleEq implementationEq first.2 rightRooted
    have same := binaryEffect_end source operation left right origin roots leftRoots rightRoots before after middle final rooted leftRooted rightRooted
    refine ⟨rootsEmpty, ?_⟩
    intro id member
    exact second.2 id (by rw [← same]; exact member)
  | zeroCall target origin context callee contextAt calleeAt parameters results =>
    intro source before after roots moduleEq implementationEq clear rooted
    have contextFound : source.mod.contexts[target]? = some context := by simpa [moduleEq] using contextAt
    have calleeFound : source.mod.impls[context.impl]? = some callee := by simpa [moduleEq] using calleeAt
    exact ⟨rpExpr_zeroArgument_scalarRegister_roots (.int integer) contextFound calleeFound parameters results (Or.inl ⟨integer, rfl⟩) rooted,
      rpExpr_zeroArgument_noParameter contextFound calleeFound parameters clear rooted⟩
  | @call argument target origin context callee parameter summary contextAt calleeAt parameters results known argumentForm ih =>
    intro source before after roots moduleEq implementationEq clear rooted
    have contextFound : source.mod.contexts[target]? = some context := by simpa [moduleEq] using contextAt
    have calleeFound : source.mod.impls[context.impl]? = some callee := by simpa [moduleEq] using calleeAt
    have effects := rpExpr_parameterCall_noParameter summary contextFound calleeFound parameters known (by
      intro operandAfter operandRoots operand
      obtain ⟨empty, available⟩ := ih source before operandAfter operandRoots moduleEq implementationEq clear operand
      refine ⟨available, ?_⟩
      intro id
      simp [empty, rootsTargets]) rooted
    obtain ⟨selected, actual, argumentRoots, middle, selectedAt, actualAt, arguments, contents⟩ := rpExpr_call_argumentChecks rooted
    have sameContext : selected = context := Option.some.inj (selectedAt.symm.trans contextFound)
    subst selected
    have sameCallee : actual = callee := Option.some.inj (actualAt.symm.trans calleeFound)
    subst actual
    have empty := rpExpr_singleByValue_scalarRegister_roots (.int integer) contextFound calleeFound parameters results
      (Or.inl ⟨integer, rfl⟩) arguments rooted
    exact ⟨empty, effects⟩

#print axioms nestedParameterExpression_source
end Goose.Proofs.ConstructionAcceptedExecution
