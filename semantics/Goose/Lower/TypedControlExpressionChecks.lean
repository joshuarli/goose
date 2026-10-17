import Goose.Lower.TypedControlExpressions
import Goose.GIR.Validate

namespace Goose.Lower.TypedControlExpressionChecks

open Goose.Core Goose.GIR Goose.Core.Sound

def blockModule (artifact : ArtifactProfile) : Core.Module :=
  { files := #["expression-block.goose"], types := #[.bool],
    globals := #[⟨"value", .bool, .mutable, .blockE (.mk 0 [] (some (.bool true))), 0⟩],
    impls := #[{ initImpl with body := .mk 0 [.assertS (.read (.global 0)) 0] none }],
    contexts := #[initContext], entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := artifact }

theorem block_claim (artifact : ArtifactProfile) (profile : NumProfile) :
    TypedExprClaim 4 ⟨profile, blockModule artifact⟩ [.bool]
      (.blockE (.mk 0 [] (some (.bool true)))) := by
  apply typedExprClaim_blockE
  apply typedBlockValueClaim_succ
  exact typedBlockLoopSimulation_succ 1 _ _ none [] [] true 0 [] (some (.bool true))
    (typedStatementsLoopSimulation_nil 1 _ _ none) (typedExprClaim_bool 1 _ _ true)

theorem block_child_source (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (blockModule artifact) = .ok ()) :
    ∃ child : BlockSource ⟨profile, blockModule artifact⟩ ⟨#[], 0, [], 0⟩ []
      (.mk 0 [] (some (.bool true))) { St.initial with nextAct := 1 },
      child.typingEnv.loops = 0 ∧ child.typingEnv.inExpr = true := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, blockModule artifact⟩) (state := St.initial) (g := 0)
    (global := ⟨"value", .bool, .mutable, .blockE (.mk 0 [] (some (.bool true))), 0⟩)
    accepted rfl (InitializedGlobals.initial _).invariant
  obtain ⟨child, hchildTyping, hchildRoots⟩ := source.blockEChild
  exact ⟨child, by simp [hchildTyping, exprEnv], by simp [hchildTyping, exprEnv]⟩

theorem block_flow (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (blockModule artifact) = .ok ()) :
    ∃ child : BlockSource ⟨profile, blockModule artifact⟩ ⟨#[], 0, [], 0⟩ []
      (.mk 0 [] (some (.bool true))) { St.initial with nextAct := 1 },
      BlockResult child (.normal (.bool true))
        { St.initial with nextAct := 1, nextScope := 1 } := by
  obtain ⟨child, loops, inExpr⟩ := block_child_source artifact profile accepted
  refine ⟨child, child.result 2 (.normal (.bool true)) ?_⟩
  simp [execBlock, execStmts, evalExpr, freshScope, bindAll, Core.releaseScope, releaseVars,
    St.initial, bind_apply, pure_apply, Functor.map, M.bind', M.pure']

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := blockModule artifact
  match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact => [NumProfile.release, .debug].all fun profile =>
  let source := blockModule artifact
  match Core.eval 100 profile source, GIR.run 200 profile (lower source) with
  | .done .returned "", .done .returned "" => true
  | _, _ => false

def abortingValue : Expr := .cmp .eq (.bin .div (.lit .i64 1) (.lit .i64 0) 0) (.lit .i64 0)

def conditionalExpression (branch : Bool) : Expr :=
  .ifE (.bool branch) (.mk 0 [] (some (.bool true))) (.mk 1 [] (some abortingValue))

def conditionalModule (artifact : ArtifactProfile) (branch : Bool) : Core.Module :=
  { files := #["conditional-expression.goose"], types := #[.bool, .int .i64],
    globals := #[⟨"selected", .bool, .mutable, conditionalExpression branch, 0⟩],
    impls := #[{ initImpl with body := .mk 0 [.assertS (.read (.global 0)) 0] none }],
    contexts := #[initContext], entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := artifact }

theorem conditional_claim (artifact : ArtifactProfile) (profile : NumProfile) (branch : Bool) :
    TypedExprClaim 6 ⟨profile, conditionalModule artifact branch⟩ [.bool]
      (conditionalExpression branch) := by
  apply typedExprClaim_ifE (typedExprClaim_bool 5 _ _ branch)
  · apply typedBlockValueClaim_succ
    exact typedBlockLoopSimulation_succ 3 _ _ none [] [] true 0 [] (some (.bool true))
      (typedStatementsLoopSimulation_nil 3 _ _ none) (typedExprClaim_bool 3 _ _ true)
  · apply typedBlockValueClaim_succ
    apply typedBlockLoopSimulation_succ 3 _ _ none [] [] true 1 [] (some abortingValue)
      (typedStatementsLoopSimulation_nil 3 _ _ none)
    exact typedExprClaim_cmp
      (typedExprClaim_bin (typedExprClaim_lit 1 _ _ .i64 1)
        (typedExprClaim_lit 1 _ _ .i64 0) .div 0) (typedExprClaim_lit 2 _ _ .i64 0) .eq

theorem conditional_branch_source (artifact : ArtifactProfile) (profile : NumProfile) (branch : Bool)
    (accepted : Core.validate (conditionalModule artifact branch) = .ok ()) :
    ∃ child : BlockSource ⟨profile, conditionalModule artifact branch⟩ ⟨#[], 0, [], 0⟩ []
      (if branch then .mk 0 [] (some (.bool true)) else .mk 1 [] (some abortingValue))
      { St.initial with nextAct := 1 },
      child.typingEnv.loops = 0 ∧ child.typingEnv.inExpr = true := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, conditionalModule artifact branch⟩) (state := St.initial) (g := 0)
    (global := ⟨"selected", .bool, .mutable, conditionalExpression branch, 0⟩)
    accepted rfl (InitializedGlobals.initial _).invariant
  obtain ⟨condition, conditionTyping, conditionRoots, conditionType, next⟩ := source.ifEChildren 5
  simp only [St.initial] at next ⊢
  obtain ⟨body, bodyTyping, bodyRoots⟩ := next branch { St.initial with nextAct := 1 }
    (by simp [evalExpr, pure_apply, St.initial])
  exact ⟨body, by simp [bodyTyping, exprEnv], by simp [bodyTyping, exprEnv]⟩

example : ∃ child : BlockSource ⟨.release, conditionalModule .pilot true⟩ ⟨#[], 0, [], 0⟩ []
    (.mk 0 [] (some (.bool true))) { St.initial with nextAct := 1 },
    child.typingEnv.loops = 0 ∧ child.typingEnv.inExpr = true :=
  conditional_branch_source .pilot .release true (by cbv)

#guard [ArtifactProfile.pilot, .shrink].all fun artifact => [false, true].all fun branch =>
  let source := conditionalModule artifact branch
  match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact => [NumProfile.release, .debug].all fun profile =>
  let source := conditionalModule artifact true
  match Core.eval 100 profile source, GIR.run 200 profile (lower source) with
  | .done .returned "", .done .returned "" => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact => [NumProfile.release, .debug].all fun profile =>
  let source := conditionalModule artifact false
  match Core.eval 100 profile source, GIR.run 200 profile (lower source) with
  | .done (.aborted .divZero 0) "", .done (.aborted .divZero 0) "" => true
  | _, _ => false

#guard match (lowerGlobal (conditionalModule .pilot true)
    ⟨"selected", .bool, .mutable, conditionalExpression true, 0⟩).init.blocks[3]?.map (·.params) with
  | some [(_, VTy.data .bool)] => true
  | _ => false

end Goose.Lower.TypedControlExpressionChecks
