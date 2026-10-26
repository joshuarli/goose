import Goose.Lower.DemandGeneratedScalarRuntime

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

def ScalarExpression.OwnerAt {cfg : Cfg} {env : Env} {expression : Expr} {state ownerState : St}
    (form : ScalarExpression expression) (source : ExprSource cfg env expression state)
    (owner : ExprSource cfg env form.ownerExpression ownerState) : Prop :=
  match form with
  | .literal .. | .boolean .. => ownerState = state ∧ HEq source owner
  | .negate .. | .unary .. | .convert .. => source.ChildAt owner 0 rfl
  | .binary .. | .compare .. => source.ChildAt owner 1 rfl

def ScalarExpression.ownerFuture {expression : Expr} (form : ScalarExpression expression)
    {cfg : Cfg} {env : Env} {state : St} (owner : ExprSource cfg env form.ownerExpression state) : List VarId :=
  match form.boundary with
  | .entry => owner.context.inputFuture
  | .exit => owner.context.outputFuture

theorem ScalarExpression.canonical_owner {expression : Expr} (form : ScalarExpression expression)
    (inputs : form.Inputs) {cfg : Cfg} {env : Env} {fuel : Nat} {state intermediate : St}
    (source : ExprSource cfg env expression state)
    (evaluated : form.PrefixEvaluated inputs fuel cfg env state intermediate) :
    ∃ (ownerState : St) (owner : ExprSource cfg env form.ownerExpression ownerState),
      form.OwnerAt source owner ∧ owner.world = source.world ∧ owner.path = form.ownerPath source.path ∧
      Core.Sound.Frame cfg.mod owner.world owner.typingEnv owner.rootsEnv env intermediate (form.ownerFuture owner) := by
  cases form with
  | literal | boolean =>
    subst intermediate
    exact ⟨state, source, ⟨rfl, HEq.rfl⟩, rfl, rfl, source.frame⟩
  | negate child =>
    obtain ⟨owner, _, _, _, metadata⟩ := source.notChild
    exact ⟨state, owner, metadata, metadata.world, metadata.path, (owner.result fuel (.bool inputs) evaluated).frame⟩
  | unary operation child origin =>
    obtain ⟨owner, _, _, _, _, metadata⟩ := source.unChild operation origin
    exact ⟨state, owner, metadata, metadata.world, metadata.path, (owner.result fuel (.int inputs.1 inputs.2) evaluated).frame⟩
  | convert kind target child origin =>
    obtain ⟨owner, _, _, _, _, _, _, metadata⟩ := source.convChild kind (.int target) origin
    exact ⟨state, owner, metadata, metadata.world, metadata.path, (owner.result fuel (.int inputs.1 inputs.2) evaluated).frame⟩
  | binary operation left right origin =>
    obtain ⟨afterLeft, leftDone, rightDone⟩ := evaluated
    obtain ⟨_, leftSource, _, _, _, _, next⟩ := source.binChildren operation origin
    obtain ⟨owner, _, _, _, metadata⟩ := next fuel (.int inputs.1 inputs.2.1) afterLeft leftDone
    exact ⟨afterLeft, owner, metadata, metadata.world, metadata.path,
      (owner.result fuel (.int inputs.1 inputs.2.2) rightDone).frame⟩
  | compare operation left right =>
    obtain ⟨afterLeft, leftDone, rightDone⟩ := evaluated
    obtain ⟨leftSource, _, _, _, next⟩ := source.cmpChildren operation
    obtain ⟨owner, _, _, metadata⟩ := next fuel (ScalarExpression.leftValue inputs) afterLeft leftDone
    exact ⟨afterLeft, owner, metadata, metadata.world, metadata.path,
      (owner.result fuel (ScalarExpression.rightValue inputs) rightDone).frame⟩

theorem generated_scalar_binary_rows {cfg : Cfg} {env : Env} {state : St} {operation : BinOp}
    {left right : Expr} {origin : OriginId} (source : ExprSource cfg env (.bin operation left right origin) state)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS} {required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root source.path
      (.expression (.bin operation left right origin)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required) :
    GeneratedDemandRows cfg.mod source.rootsEnv.access
      ((ScalarExpression.binary operation left right origin).ownerOccurrence occurrence) required := by
  obtain ⟨type, child, _, roots, typed, metadata, _⟩ := source.binChildren operation origin
  have lookup := tyExpr_accessType (child.frame.mod_t.trans child.frame.mod_p.symm)
    (child.frame.vars_t.trans child.frame.vars_p.symm) child.typed
  have query : source.rootsEnv.access.aliasExpr (source.path ++ [0]) left = .ok [] := by
    rw [← roots, ← metadata.path]
    simp [AccessEnv.aliasExpr, lookup, typed, Ty.interiorTarget?, pure, Except.pure]
  change GeneratedDemandRows cfg.mod source.rootsEnv.access (.binaryRight occurrence) required
  cases required
  simpa only [RetainedSsaMap.addValues, List.map_nil, List.nil_append] using
    (GeneratedDemandRows.binaryRight (aliases := []) rows query)

theorem generated_scalar_comparison_rows {cfg : Cfg} {env : Env} {state intermediate : St}
    {operation : CmpOp} {left right : Expr} (source : ExprSource cfg env (.cmp operation left right) state)
    (inputs : (ScalarExpression.compare operation left right).Inputs) {fuel : Nat}
    (evaluated : (ScalarExpression.compare operation left right).PrefixEvaluated inputs fuel cfg env state intermediate)
    {cx : FnCtx} {le : LEnv} {root : DemandNode} {before : LS} {required : RetainedSsaMap}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root source.path (.expression (.cmp operation left right)) before)
    (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required) :
    GeneratedDemandRows cfg.mod source.rootsEnv.access
      ((ScalarExpression.compare operation left right).ownerOccurrence occurrence) required := by
  obtain ⟨afterLeft, leftDone, _⟩ := evaluated
  obtain ⟨child, _, roots, metadata, _⟩ := source.cmpChildren operation
  have scalar : child.ty.interiorTarget?.isSome = false := by
    have typed := (child.result fuel (ScalarExpression.leftValue inputs) leftDone).typed
    cases inputs with
    | inl integers =>
      rcases integers with ⟨type, number, other⟩
      cases actual : child.ty <;> simp [ScalarExpression.leftValue, HasTy, Goose.Proofs.Memory.FlatTy,
        actual, Ty.interiorTarget?] at typed ⊢
    | inr booleans =>
      rcases booleans with ⟨value, other⟩
      cases actual : child.ty <;> simp [ScalarExpression.leftValue, HasTy, Goose.Proofs.Memory.FlatTy,
        actual, Ty.interiorTarget?] at typed ⊢
  have lookup := tyExpr_accessType (child.frame.mod_t.trans child.frame.mod_p.symm)
    (child.frame.vars_t.trans child.frame.vars_p.symm) child.typed
  have query : source.rootsEnv.access.aliasExpr (source.path ++ [0]) left = .ok [] := by
    rw [← roots, ← metadata.path]
    simp [AccessEnv.aliasExpr, lookup, scalar, pure, Except.pure]
  change GeneratedDemandRows cfg.mod source.rootsEnv.access (.comparisonRight occurrence) required
  cases required
  simpa only [RetainedSsaMap.addValues, List.map_nil, List.nil_append] using
    (GeneratedDemandRows.comparisonRight (aliases := []) rows query)

end Goose.Lower
