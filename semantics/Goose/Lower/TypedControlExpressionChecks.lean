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

end Goose.Lower.TypedControlExpressionChecks
