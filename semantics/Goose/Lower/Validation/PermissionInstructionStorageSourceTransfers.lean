import Goose.Lower.Validation.PermissionInstructionStorageSourceStores
import Goose.Lower.Validation.PermissionPreservationControlEffects

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem permissionStorage_dead_coerceTo (target : Ty) (value : ValueId) (origin : OriginId) :
    DeadRun (coerceTo target value origin) := by
  intro le before result after run dead
  rcases coerceTo_cases run with ⟨_, rfl⟩ | ⟨_, _, emitted⟩ | ⟨_, view, middle, _, firstRun, lastRun⟩
  · exact dead
  · exact dead_emitDef _ _ _ _ _ emitted dead
  · exact dead_emitDef _ _ _ _ _ lastRun (dead_emitDef _ _ _ _ _ firstRun dead)

private theorem permissionStorage_dead_coerceSlot (slot : SlotId) (value : ValueId) (origin : OriginId) :
    DeadRun (coerceSlot slot value origin) := by
  intro le before result after run dead
  simp only [coerceSlot, bind_run, read_apply] at run
  cases row : le.slots[slot]? with
  | none =>
    simp only [row, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact dead
  | some destination =>
    simp only [row] at run
    exact permissionStorage_dead_coerceTo _ _ _ _ _ _ _ run dead

private theorem permissionStorage_dead_coerceResult (value : ValueId) (origin : OriginId) :
    DeadRun (coerceResult value origin) := by
  intro le before result after run dead
  simp only [coerceResult, bind_run, read_apply] at run
  cases row : le.results.head? with
  | none =>
    simp only [row, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact dead
  | some destination =>
    simp only [row] at run
    exact permissionStorage_dead_coerceTo _ _ _ _ _ _ _ run dead

private theorem permissionStorage_dead_leaveAll (scopes : List ScopeId) : DeadRun (leaveAll scopes) := by
  induction scopes with
  | nil => exact .pure ()
  | cons scope rest ih => exact .bind (dead_emitEffect (.leave scope)) fun _ => ih

private theorem permissionStorage_dead_leaveTo (depth : Nat) : DeadRun (leaveTo depth) := by
  intro le before result after run dead
  change leaveAll (before.stack.take (before.stack.length - depth)) le before = (result, after) at run
  exact permissionStorage_dead_leaveAll _ _ _ _ _ run dead

theorem permissionInstructions_let_source {env output : Core.TEnv} {func : Func} {results : List Ty}
    (slots : func.slots = (lowerEnv env.mod env.vars results).slots)
    {slot : VarId} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.letS slot expr origin) start = .ok (output, finish))
    (exprChild : PermissionStorageExprChild env func results expr)
    {loop : Option LoopCtx} {before after : LS} {result : Unit} {first : Nat}
    (bound : first ≤ before.vals.size) (generated : GeneratedBuilderState before)
    (run : lowerStmt loop (.letS slot expr origin) (lowerEnv env.mod env.vars results) before = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  obtain ⟨localVar, type, next, declared, exprSource, passable, _⟩ := tyStmt_let_children source
  have row := (declare_ok _ _ _ _ _ declared).2.1
  have slotRow : (lowerEnv env.mod env.vars results).slots[slot]? =
      some ⟨localVar.ty, localVar.kind, localVar.scope, slot⟩ := by
    simp [lowerEnv, Array.getElem?_mapIdx, row]
  simp only [lowerStmt] at run
  obtain ⟨value, evaluated, exprRun, run⟩ := bind_eq.mp run
  obtain ⟨coercedValue, coerced, coerceRun, effectRun⟩ := bind_eq.mp run
  have evaluatedGenerated := generated.lowerExpr expr exprRun
  have coercedGenerated := evaluatedGenerated.coerceSlot slot value origin coerceRun
  have priorIssued := ((exprChild exprSource generated exprRun).weaken bound).compose_framed
    (newPermissions_coerceSlot coerceRun) coerceRun (dense_coerceSlot slot value origin)
    (advB_coerceSlot slot value origin) (types_coerceSlot slot value origin)
    (generatedTargetFrame_coerceSlot none slot value origin) evaluatedGenerated (by trivial)
  apply permissionStorage_appendEffect priorIssued coercedGenerated effectRun
  intro live
  apply FreshPermissionInstruction.slotInit
  intro descriptor descriptorRow
  rw [slots, slotRow] at descriptorRow
  cases descriptorRow
  have evaluatedLive := (permissionStorage_dead_coerceSlot slot value origin).live_before coerceRun live
  have transfer := (lowerExpr_generated_permissionTransfer expr exprSource passable exprRun evaluatedLive generated).fresh_weaken bound
  have coercedTransfer := permissionTransfer_coerceSlot slotRow transfer coerceRun
  exact coercedTransfer.fresh_of_framed_run effectRun (dense_emitEffect _) (advB_emitEffect _)
    (types_emitEffect _) (generatedTargetFrame_emitEffect none _) coercedGenerated (by trivial)

theorem permissionInstructions_rebind_source {env output : Core.TEnv} {func : Func} {results : List Ty}
    {slot : VarId} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.rebind slot expr origin) start = .ok (output, finish))
    (exprChild : PermissionStorageExprChild env func results expr)
    {loop : Option LoopCtx} {before after : LS} {result : Unit} {first : Nat}
    (bound : first ≤ before.vals.size) (generated : GeneratedBuilderState before)
    (run : lowerStmt loop (.rebind slot expr origin) (lowerEnv env.mod env.vars results) before = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  obtain ⟨localVar, type, row, _, reference, mutable, exprSource, passable, _⟩ := tyStmt_rebind_children source
  let le := lowerEnv env.mod env.vars results
  have slotRow : le.slots[slot]? = some ⟨localVar.ty, localVar.kind, localVar.scope, slot⟩ := by
    simp [le, lowerEnv, Array.getElem?_mapIdx, row]
  simp only [lowerStmt] at run
  obtain ⟨value, evaluated, exprRun, run⟩ := bind_eq.mp run
  obtain ⟨coercedValue, coerced, coerceRun, run⟩ := bind_eq.mp run
  obtain ⟨address, addressed, addressRun, effectRun⟩ := bind_eq.mp run
  have evaluatedGenerated := generated.lowerExpr expr exprRun
  have coercedGenerated := evaluatedGenerated.coerceSlot slot value origin coerceRun
  have addressedGenerated := coercedGenerated.emitDef (.slotAddr slot) addressRun
  have priorIssued := ((exprChild exprSource generated exprRun).weaken bound).compose_framed
    (newPermissions_coerceSlot coerceRun) coerceRun (dense_coerceSlot slot value origin)
    (advB_coerceSlot slot value origin) (types_coerceSlot slot value origin)
    (generatedTargetFrame_coerceSlot none slot value origin) evaluatedGenerated (by trivial)
  have appended := priorIssued.compose_framed (newPermissions_free_emitDef (by trivial) addressRun) addressRun
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _) coercedGenerated (by trivial)
  apply permissionStorage_appendEffect appended addressedGenerated effectRun
  intro live
  have coercedLive := (dead_emitDef (.slotAddr slot)).live_before addressRun live
  have evaluatedLive := (permissionStorage_dead_coerceSlot slot value origin).live_before coerceRun coercedLive
  cases active : coerced.cur with
  | none => simp [active] at coercedLive
  | some block =>
    have writable := freshWritableEvidence_slot coercedGenerated.dense coercedGenerated.live active slotRow mutable addressRun
    have freshBound : first ≤ coerced.vals.size := Nat.le_trans bound
      (Nat.le_trans (advB_lowerExpr expr _ _ _ _ exprRun).vals (advB_coerceSlot slot value origin _ _ _ _ coerceRun).vals)
    have finalWritable := (writable.weaken freshBound).of_framed_run effectRun (dense_emitEffect _)
      (advB_emitEffect _) (types_emitEffect _) (generatedTargetFrame_emitEffect none _) addressedGenerated.dense
      addressedGenerated.live (by trivial)
    have operation : (Op.slotAddr slot).resultTy (tyEnv le coerced) = .ok (.data (.ref .mutable localVar.ty)) := by
      simp only [Op.resultTy, tyEnv, slotRow, mutable]
      cases shape : localVar.ty <;> simp only [shape, Ty.isRefLike, Bool.false_eq_true] at reference
      all_goals rfl
    have recorded := emitDef_recorded active operation
    rw [addressRun] at recorded
    have finalRow := types_emitEffect _ _ _ _ _ effectRun _ _ recorded.2.2.1
    have transferred := permissionTransfer_coerceSlot slotRow
      ((lowerExpr_generated_permissionTransfer expr exprSource passable exprRun evaluatedLive generated).fresh_weaken bound) coerceRun
    have addressedTransfer := transferred.fresh_of_framed_run addressRun (dense_emitDef _) (advB_emitDef _)
      (types_emitDef _) (generatedTargetFrame_emitDef none _) coercedGenerated (by trivial)
    exact .store finalRow finalWritable (addressedTransfer.fresh_of_framed_run effectRun
      (dense_emitEffect _) (advB_emitEffect _) (types_emitEffect _) (generatedTargetFrame_emitEffect none _) addressedGenerated (by trivial))

theorem permissionInstructions_return_source {env output : Core.TEnv} {func : Func} {results : List Ty}
    (resultTypes : func.results = results)
    (implementationResults : ∀ impl, env.impl = some impl → results = impl.results.toList)
    {value : Option Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.ret value origin) start = .ok (output, finish))
    (exprChild : ∀ expression, value = some expression → PermissionStorageExprChild env func results expression)
    {loop : Option LoopCtx} {before after : LS} {result : Unit} {first : Nat}
    (bound : first ≤ before.vals.size) (generated : GeneratedBuilderState before)
    (run : lowerStmt loop (.ret value origin) (lowerEnv env.mod env.vars results) before = (result, after)) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  cases value with
  | none =>
    simp only [lowerStmt] at run
    obtain ⟨values, initial, valuesRun, run⟩ := bind_eq.mp run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp valuesRun
    obtain ⟨_, left, leaveRun, emitted⟩ := bind_eq.mp run
    have leftGenerated := generated.leaveTo 0 leaveRun
    exact (NewPermissionInstructions.leaveTo 0 leaveRun generated).compose_framed
      (.emitTerm emitted (fun _ => .ret (by simp))) emitted (dense_emitTerm _)
      (advB_emitTerm _) (types_emitTerm _) (generatedTargetFrame_emitNoSuccessors none _ rfl) leftGenerated (by trivial)
  | some expression =>
    obtain ⟨expected, actual, impl, _, implAt, implResults, exprSource, passable, _⟩ := tyStmt_return_children source
    have resultsRow : results = [expected] := (implementationResults impl implAt).trans implResults
    have headRow : (lowerEnv env.mod env.vars results).results.head? = some expected := by simp [lowerEnv, resultsRow]
    simp only [lowerStmt] at run
    obtain ⟨value, evaluated, exprRun, run⟩ := bind_eq.mp run
    obtain ⟨coercedValue, coerced, coerceRun, run⟩ := bind_eq.mp run
    obtain ⟨values, initial, valuesRun, run⟩ := bind_eq.mp run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp valuesRun
    obtain ⟨_, left, leaveRun, emitted⟩ := bind_eq.mp run
    have evaluatedGenerated := generated.lowerExpr expression exprRun
    have coercedGenerated := evaluatedGenerated.coerceResult value origin coerceRun
    have leftGenerated := coercedGenerated.leaveTo 0 leaveRun
    have firstIssued := ((exprChild expression rfl exprSource generated exprRun).weaken bound).compose_framed
      (newPermissions_coerceResult coerceRun) coerceRun (dense_coerceResult value origin)
      (advB_coerceResult value origin) (types_coerceResult value origin)
      (generatedTargetFrame_coerceResult none value origin) evaluatedGenerated (by trivial)
    have priorIssued := firstIssued.compose_framed (.leaveTo 0 leaveRun coercedGenerated) leaveRun
      (dense_leaveTo 0) (advB_leaveTo 0) (types_leaveTo 0) (generatedTargetFrame_leaveTo none 0) coercedGenerated (by trivial)
    refine priorIssued.compose_framed (.emitTerm emitted ?_) emitted (dense_emitTerm _) (advB_emitTerm _)
      (types_emitTerm _) (generatedTargetFrame_emitNoSuccessors none _ rfl) leftGenerated (by trivial)
    intro live
    apply FreshPermissionInstruction.ret
    intro entry member
    have same : entry = (expected, coercedValue) := by simpa [resultTypes, resultsRow] using member
    subst entry
    have coercedLive := (permissionStorage_dead_leaveTo 0).live_before leaveRun live
    have evaluatedLive := (permissionStorage_dead_coerceResult value origin).live_before coerceRun coercedLive
    have initial := (lowerExpr_generated_permissionTransfer expression exprSource passable exprRun evaluatedLive generated).fresh_weaken bound
    have transferred := permissionTransfer_coerceResult headRow initial coerceRun
    have leaving := transferred.fresh_of_framed_run leaveRun (dense_leaveTo 0) (advB_leaveTo 0)
      (types_leaveTo 0) (generatedTargetFrame_leaveTo none 0) coercedGenerated (by trivial)
    exact leaving.fresh_of_framed_run emitted (dense_emitTerm _) (advB_emitTerm _) (types_emitTerm _)
      (generatedTargetFrame_emitNoSuccessors none _ rfl) leftGenerated (by trivial)

#print axioms permissionInstructions_let_source
#print axioms permissionInstructions_rebind_source
#print axioms permissionInstructions_return_source

end Goose.Lower.Validation
