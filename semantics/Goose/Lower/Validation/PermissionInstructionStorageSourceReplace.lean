import Goose.Lower.Validation.PermissionInstructionStorageSourceMutations

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem permissionInstructions_assignWhole_source {env output : Core.TEnv} {func : Func} {results : List Ty}
    {owner : Place} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assignWhole owner expr origin) start = .ok (output, finish))
    (placeChild : PermissionStoragePlaceChild env func results owner)
    (exprChild : PermissionStorageExprChild env func results expr)
    {loop : Option LoopCtx} {before after : LS} {result : Unit} {first : Nat}
    (bound : first ≤ before.vals.size) (generated : GeneratedBuilderState before)
    (run : lowerStmt loop (.assignWhole owner expr origin) (lowerEnv env.mod env.vars results) before = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  obtain ⟨info, element, next, placeSource, shape, exprSource, binding, contents, _⟩ := tyStmt_assignWhole_children source
  have container : ContentsTarget info.ty := by rcases shape with same | same <;> simp [same, ContentsTarget]
  have demand : BindingTarget env.mod.profile info.ty := by
    rcases shape with same | same <;> simp [same, BindingTarget, tyStmt_assignWhole_profile source]
  simp only [lowerStmt] at run
  obtain ⟨address, middle, placeRun, run⟩ := bind_eq.mp run
  obtain ⟨_, cleared, clearRun, run⟩ := bind_eq.mp run
  obtain ⟨value, evaluated, exprRun, effectRun⟩ := bind_eq.mp run
  have middleGenerated := generated.lowerPlace owner placeRun
  have clearedGenerated := middleGenerated.emitEffect (.clear address (some origin)) clearRun
  have evaluatedGenerated := clearedGenerated.lowerExpr expr exprRun
  have issuedClear := permissionStorage_mutation_tail placeSource container contents placeChild bound generated placeRun
    (action := pure ()) (value := ()) (effectState := middle) rfl (.of_blocks_eq rfl)
    (.pure ()) (.pure ()) (.pure ()) (generatedTargetFrame_pure none ()) (.pure ())
    middleGenerated (.clear address (some origin)) clearRun
  have clearedBound : first ≤ cleared.vals.size := Nat.le_trans bound
    (Nat.le_trans (advB_lowerPlace owner _ _ _ _ placeRun).vals (advB_emitEffect _ _ _ _ _ clearRun).vals)
  have priorIssued := issuedClear.compose_framed ((exprChild exprSource clearedGenerated exprRun).weaken clearedBound)
    exprRun (dense_lowerExpr expr) (advB_lowerExpr expr) (types_lowerExpr expr)
    (generatedTargetFrame_lowerExpr none expr) clearedGenerated (by trivial)
  apply permissionStorage_appendEffect priorIssued evaluatedGenerated effectRun
  intro live
  have clearedLive := (dead_lowerExpr expr).live_before exprRun live
  have middleLive := (dead_emitEffect (.clear address (some origin))).live_before clearRun clearedLive
  have writable := (lowerPlace_generated_binding owner placeSource binding demand placeRun middleLive generated).weaken bound
  have content := (lowerPlace_generated_contents owner placeSource container contents placeRun middleLive generated).weaken bound
  have writableCleared := writable.of_framed_run clearRun (dense_emitEffect _) (advB_emitEffect _)
    (types_emitEffect _) (generatedTargetFrame_emitEffect none _) middleGenerated.dense middleGenerated.live (by trivial)
  have contentCleared := content.of_framed_run clearRun (dense_emitEffect _) (advB_emitEffect _)
    (types_emitEffect _) (generatedTargetFrame_emitEffect none _) middleGenerated.dense middleGenerated.live (by trivial)
  have writableEvaluated := writableCleared.of_framed_run exprRun (dense_lowerExpr expr) (advB_lowerExpr expr)
    (types_lowerExpr expr) (generatedTargetFrame_lowerExpr none expr) clearedGenerated.dense clearedGenerated.live (by trivial)
  have contentEvaluated := contentCleared.of_framed_run exprRun (dense_lowerExpr expr) (advB_lowerExpr expr)
    (types_lowerExpr expr) (generatedTargetFrame_lowerExpr none expr) clearedGenerated.dense clearedGenerated.live (by trivial)
  exact .replace
    (writableEvaluated.of_framed_run effectRun (dense_emitEffect _) (advB_emitEffect _)
      (types_emitEffect _) (generatedTargetFrame_emitEffect none _) evaluatedGenerated.dense evaluatedGenerated.live (by trivial))
    (contentEvaluated.of_framed_run effectRun (dense_emitEffect _) (advB_emitEffect _)
      (types_emitEffect _) (generatedTargetFrame_emitEffect none _) evaluatedGenerated.dense evaluatedGenerated.live (by trivial))

#print axioms permissionInstructions_assignWhole_source

end Goose.Lower.Validation
