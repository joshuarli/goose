import Goose.Lower.Validation.PermissionInstructionStorageSourceEffects

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem permissionInstructions_append_source {env output : Core.TEnv} {func : Func} {results : List Ty}
    {owner : Place} {view : View} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.append owner view origin) start = .ok (output, finish))
    (placeChild : PermissionStoragePlaceChild env func results owner)
    (viewChild : PermissionStorageViewChild env func results view)
    {loop : Option LoopCtx} {before after : LS} {result : Unit} {first : Nat}
    (bound : first ≤ before.vals.size) (generated : GeneratedBuilderState before)
    (run : lowerStmt loop (.append owner view origin) (lowerEnv env.mod env.vars results) before = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  obtain ⟨info, element, writable, next, placeSource, ownerType, viewSource, permission, _⟩ := tyStmt_append_children source
  simp only [lowerStmt] at run
  obtain ⟨address, middle, placeRun, run⟩ := bind_eq.mp run
  obtain ⟨value, effectState, viewRun, effectRun⟩ := bind_eq.mp run
  have middleGenerated := generated.lowerPlace owner placeRun
  exact permissionStorage_mutation_tail placeSource (permissionStorage_owner_target ownerType)
    (permissionStorage_owner_contents placeSource permission) placeChild bound generated placeRun viewRun
    (viewChild viewSource middleGenerated viewRun) (dense_lowerView view) (advB_lowerView view)
    (types_lowerView view) (generatedTargetFrame_lowerView none view) (dead_lowerView view)
    (middleGenerated.lowerView view viewRun) (.append address value (some origin)) effectRun

theorem permissionInstructions_popN_source {env output : Core.TEnv} {func : Func} {results : List Ty}
    {owner : Place} {count : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.popN owner count origin) start = .ok (output, finish))
    (placeChild : PermissionStoragePlaceChild env func results owner)
    (countChild : PermissionStorageExprChild env func results count)
    {loop : Option LoopCtx} {before after : LS} {result : Unit} {first : Nat}
    (bound : first ≤ before.vals.size) (generated : GeneratedBuilderState before)
    (run : lowerStmt loop (.popN owner count origin) (lowerEnv env.mod env.vars results) before = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  obtain ⟨info, element, integer, next, placeSource, ownerType, countSource, permission, _⟩ := tyStmt_popN_children source
  simp only [lowerStmt] at run
  obtain ⟨address, middle, placeRun, run⟩ := bind_eq.mp run
  obtain ⟨value, effectState, countRun, effectRun⟩ := bind_eq.mp run
  have middleGenerated := generated.lowerPlace owner placeRun
  exact permissionStorage_mutation_tail placeSource (permissionStorage_owner_target ownerType) permission
    placeChild bound generated placeRun countRun (countChild countSource middleGenerated countRun)
    (dense_lowerExpr count) (advB_lowerExpr count) (types_lowerExpr count)
    (generatedTargetFrame_lowerExpr none count) (dead_lowerExpr count)
    (middleGenerated.lowerExpr count countRun) (.popN address value (some origin)) effectRun

theorem permissionInstructions_clear_source {env output : Core.TEnv} {func : Func} {results : List Ty}
    {owner : Place} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.clear owner origin) start = .ok (output, finish))
    (placeChild : PermissionStoragePlaceChild env func results owner)
    {loop : Option LoopCtx} {before after : LS} {result : Unit} {first : Nat}
    (bound : first ≤ before.vals.size) (generated : GeneratedBuilderState before)
    (run : lowerStmt loop (.clear owner origin) (lowerEnv env.mod env.vars results) before = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  obtain ⟨info, element, placeSource, ownerType, permission, _⟩ := tyStmt_clear_children source
  simp only [lowerStmt] at run
  obtain ⟨address, middle, placeRun, effectRun⟩ := bind_eq.mp run
  exact permissionStorage_mutation_tail placeSource (permissionStorage_owner_target ownerType) permission
    placeChild bound generated placeRun (action := pure ()) (value := ()) (effectState := middle) rfl (.of_blocks_eq rfl)
    (.pure ()) (.pure ()) (.pure ()) (generatedTargetFrame_pure none ()) (.pure ())
    (generated.lowerPlace owner placeRun) (.clear address (some origin)) effectRun

theorem permissionInstructions_resize_source {env output : Core.TEnv} {func : Func} {results : List Ty}
    {owner : Place} {count : Expr} {fill : Option Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.resize owner count fill origin) start = .ok (output, finish))
    (placeChild : PermissionStoragePlaceChild env func results owner)
    (countChild : PermissionStorageExprChild env func results count)
    (fillChild : ∀ expression, fill = some expression → PermissionStorageExprChild env func results expression)
    {loop : Option LoopCtx} {before after : LS} {result : Unit} {first : Nat}
    (bound : first ≤ before.vals.size) (generated : GeneratedBuilderState before)
    (run : lowerStmt loop (.resize owner count fill origin) (lowerEnv env.mod env.vars results) before = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  cases fill with
  | none =>
    obtain ⟨info, element, integer, next, countFinish, placeSource, ownerType, countSource, _, permission, _⟩ :=
      tyStmt_resize_children source
    simp only [lowerStmt] at run
    obtain ⟨address, middle, placeRun, run⟩ := bind_eq.mp run
    obtain ⟨value, effectState, countRun, effectRun⟩ := bind_eq.mp run
    have middleGenerated := generated.lowerPlace owner placeRun
    exact permissionStorage_mutation_tail placeSource (permissionStorage_owner_target ownerType) permission
      placeChild bound generated placeRun countRun (countChild countSource middleGenerated countRun)
      (dense_lowerExpr count) (advB_lowerExpr count) (types_lowerExpr count)
      (generatedTargetFrame_lowerExpr none count) (dead_lowerExpr count)
      (middleGenerated.lowerExpr count countRun) (.resize address value none (some origin)) effectRun
  | some expression =>
    obtain ⟨info, element, integer, next, countFinish, placeSource, ownerType, countSource, fillSource, permission, _⟩ :=
      tyStmt_resize_children source
    simp only [lowerStmt] at run
    obtain ⟨address, middle, placeRun, run⟩ := bind_eq.mp run
    obtain ⟨countValue, counted, countRun, run⟩ := bind_eq.mp run
    obtain ⟨fillValue, filled, fillRun, effectRun⟩ := bind_eq.mp run
    have middleGenerated := generated.lowerPlace owner placeRun
    have countedGenerated := middleGenerated.lowerExpr count countRun
    have filledGenerated := countedGenerated.lowerExpr expression fillRun
    let action : B (ValueId × Option ValueId) := do
      let countValue ← lowerExpr count
      let fillValue ← lowerExpr expression
      pure (countValue, some fillValue)
    have tailRun : action (lowerEnv env.mod env.vars results) middle = ((countValue, some fillValue), filled) := by
      simp only [action, bind_run, countRun, fillRun, pure_run]
    have tailIssued := (countChild countSource middleGenerated countRun).compose_framed
      ((fillChild expression rfl fillSource countedGenerated fillRun).weaken
        (advB_lowerExpr count _ _ _ _ countRun).vals)
      fillRun (dense_lowerExpr expression) (advB_lowerExpr expression) (types_lowerExpr expression)
      (generatedTargetFrame_lowerExpr none expression) countedGenerated (by trivial)
    exact permissionStorage_mutation_tail placeSource (permissionStorage_owner_target ownerType) permission
      placeChild bound generated placeRun tailRun tailIssued
      (.bind (dense_lowerExpr count) fun _ => .bind (dense_lowerExpr expression) fun _ => .pure _)
      (.bind (advB_lowerExpr count) fun _ => .bind (advB_lowerExpr expression) fun _ => .pure _)
      (.bind (types_lowerExpr count) fun _ => .bind (types_lowerExpr expression) fun _ => .pure _)
      (.bind (generatedTargetFrame_lowerExpr none count) fun _ =>
        .bind (generatedTargetFrame_lowerExpr none expression) fun _ => generatedTargetFrame_pure none _)
      (.bind (dead_lowerExpr count) fun _ => .bind (dead_lowerExpr expression) fun _ => .pure _)
      filledGenerated (.resize address countValue (some fillValue) (some origin)) effectRun

#print axioms permissionInstructions_append_source
#print axioms permissionInstructions_popN_source
#print axioms permissionInstructions_clear_source
#print axioms permissionInstructions_resize_source

end Goose.Lower.Validation
