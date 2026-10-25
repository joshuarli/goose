import Goose.Lower.Validation.PermissionInstructionStorageSourceEffects
import Goose.Lower.Validation.PermissionInstructionReferencesOps

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem permissionStorage_intTyOf_state {le : LEnv} {before after : LS} {value : ValueId} {integer : IntTy}
    (run : intTyOf value le before = (integer, after)) : after = before := by
  simp only [intTyOf] at run
  obtain ⟨type, middle, typeRun, run⟩ := bind_eq.mp run
  have same := valTy_run value le before
  rw [typeRun] at same
  dsimp only at same
  subst middle
  cases type with
  | data type => cases type <;> exact (pure_eq.mp run).2.symm
  | view _ _ => exact (pure_eq.mp run).2.symm

theorem permissionInstructions_assign_source {env output : Core.TEnv} {func : Func} {results : List Ty}
    {place : Place} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assign place expr origin) start = .ok (output, finish))
    (placeChild : PermissionStoragePlaceChild env func results place)
    (exprChild : PermissionStorageExprChild env func results expr)
    {loop : Option LoopCtx} {before after : LS} {result : Unit} {first : Nat}
    (bound : first ≤ before.vals.size) (generated : GeneratedBuilderState before)
    (run : lowerStmt loop (.assign place expr origin) (lowerEnv env.mod env.vars results) before = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  obtain ⟨info, next, placeSource, exprSource, copyable, binding, _⟩ := tyStmt_assign_children source
  have readable : info.ty.readable = true := by
    apply flat_or_slice_readable
    rcases Bool.or_eq_true_iff.mp copyable with flat | slice
    · exact Or.inl flat
    · exact Or.inr (Bool.and_eq_true_iff.mp slice).1
  simp only [lowerStmt] at run
  obtain ⟨address, middle, placeRun, run⟩ := bind_eq.mp run
  obtain ⟨value, effectState, exprRun, effectRun⟩ := bind_eq.mp run
  have middleGenerated := generated.lowerPlace place placeRun
  apply permissionStorage_store_tail placeSource binding
    (permissionStorage_readable_binding_target readable _) placeChild bound generated placeRun exprRun
    (exprChild exprSource middleGenerated exprRun) (dense_lowerExpr expr) (advB_lowerExpr expr)
    (types_lowerExpr expr) (generatedTargetFrame_lowerExpr none expr) (dead_lowerExpr expr)
    (middleGenerated.lowerExpr expr exprRun) ?_ effectRun
  intro live
  exact (lowerExpr_generated_permissionTransfer expr exprSource (permissionStorage_passable_self _)
    exprRun live middleGenerated).fresh_weaken (Nat.le_trans bound (advB_lowerPlace place _ _ _ _ placeRun).vals)

theorem permissionInstructions_assignOp_source {env output : Core.TEnv} {func : Func} {results : List Ty}
    {place : Place} {expr : Expr} {operation : BinOp} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assignOp operation place expr origin) start = .ok (output, finish))
    (placeChild : PermissionStoragePlaceChild env func results place)
    (exprChild : PermissionStorageExprChild env func results expr)
    {loop : Option LoopCtx} {before after : LS} {result : Unit} {first : Nat}
    (bound : first ≤ before.vals.size) (generated : GeneratedBuilderState before)
    (run : lowerStmt loop (.assignOp operation place expr origin) (lowerEnv env.mod env.vars results) before = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  obtain ⟨info, integer, next, placeSource, infoType, exprSource, binding, _⟩ := tyStmt_assignOp_children source
  simp only [lowerStmt] at run
  obtain ⟨address, middle, placeRun, run⟩ := bind_eq.mp run
  obtain ⟨old, loaded, loadRun, run⟩ := bind_eq.mp run
  obtain ⟨rhs, evaluated, exprRun, run⟩ := bind_eq.mp run
  obtain ⟨kind, classified, kindRun, run⟩ := bind_eq.mp run
  obtain ⟨value, effectState, binaryRun, effectRun⟩ := bind_eq.mp run
  have middleGenerated := generated.lowerPlace place placeRun
  have loadedGenerated := middleGenerated.emitDef (.load address) loadRun
  have evaluatedGenerated := loadedGenerated.lowerExpr expr exprRun
  have classifiedGenerated := evaluatedGenerated.intTyOf old kindRun
  have effectGenerated := classifiedGenerated.emitDef (.bin operation kind old rhs (some origin)) binaryRun
  have firstIssued := (newPermissions_free_emitDef (module := lower env.mod) (func := func)
    (first := middle.vals.size) (by trivial) loadRun).compose_framed
      ((exprChild exprSource loadedGenerated exprRun).weaken (advB_emitDef _ _ _ _ _ loadRun).vals)
      exprRun (dense_lowerExpr expr) (advB_lowerExpr expr) (types_lowerExpr expr)
      (generatedTargetFrame_lowerExpr none expr) loadedGenerated (by trivial)
  have kindIssued : NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results)
      middle.vals.size evaluated classified := .of_blocks_eq (congrArg LS.blocks (permissionStorage_intTyOf_state kindRun))
  have secondIssued := firstIssued.compose_framed kindIssued kindRun (dense_intTyOf old) (advB_intTyOf old)
    (types_intTyOf old) (generatedTargetFrame_intTyOf none old) evaluatedGenerated (by trivial)
  have tailIssued := secondIssued.compose_framed (newPermissions_free_emitDef (by trivial) binaryRun) binaryRun
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _) classifiedGenerated (by trivial)
  let action : B ValueId := do
    let old ← emitDef (.load address)
    let rhs ← lowerExpr expr
    let kind ← intTyOf old
    emitDef (.bin operation kind old rhs (some origin))
  have tailRun : action (lowerEnv env.mod env.vars results) middle = (value, effectState) := by
    simp only [action, bind_run, loadRun, exprRun, kindRun, binaryRun]
  apply permissionStorage_store_tail placeSource binding (by rw [infoType]; trivial) placeChild bound generated
    placeRun tailRun tailIssued
    (.bind (dense_emitDef _) fun _ => .bind (dense_lowerExpr expr) fun _ => .bind (dense_intTyOf _) fun _ => dense_emitDef _)
    (.bind (advB_emitDef _) fun _ => .bind (advB_lowerExpr expr) fun _ => .bind (advB_intTyOf _) fun _ => advB_emitDef _)
    (.bind (types_emitDef _) fun _ => .bind (types_lowerExpr expr) fun _ => .bind (types_intTyOf _) fun _ => types_emitDef _)
    (.bind (generatedTargetFrame_emitDef none _) fun _ => .bind (generatedTargetFrame_lowerExpr none expr) fun _ =>
      .bind (generatedTargetFrame_intTyOf none _) fun _ => generatedTargetFrame_emitDef none _)
    (.bind (dead_emitDef _) fun _ => .bind (dead_lowerExpr expr) fun _ => .bind (dead_intTyOf _) fun _ => dead_emitDef _)
    effectGenerated ?_ effectRun
  intro live
  rw [infoType]
  trivial

#print axioms permissionInstructions_assign_source
#print axioms permissionInstructions_assignOp_source

end Goose.Lower.Validation
