import Goose.Lower.Validation.SourceReplacementLexicalWritersStorePhysics
import Goose.Lower.Validation.SourceReplacementLexicalWritersPhysics
import Goose.Lower.Validation.SourceStatementTypingStorage

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource

theorem rebind_store_tracked_visible (facts : SourceReadyFunction)
    {typing : TEnv} {slot : VarId} {expression : Expr} {origin : OriginId} {loop : Option LoopCtx}
    {scope start finish : Nat} {output : TEnv}
    (source : tyStmt typing scope (.rebind slot expression origin) start = .ok (output,finish))
    {results : List Ty} {before : LS} (generated : GeneratedBuilderState before)
    (continuation : NativeBuilderContinuation facts.func
      (lowerStmt loop (.rebind slot expression origin) (lowerEnv typing.mod typing.vars results) before).2)
    (live : (emitDef (.slotAddr slot) (lowerEnv typing.mod typing.vars results)
      (coerceSlot slot (lowerExpr expression (lowerEnv typing.mod typing.vars results) before).1 origin
        (lowerEnv typing.mod typing.vars results)
        (lowerExpr expression (lowerEnv typing.mod typing.vars results) before).2).2).2.cur.isSome = true)
    {tracked : VarId}
    (upper : rootsAt facts.upper.vals
      (emitDef (.slotAddr slot) (lowerEnv typing.mod typing.vars results)
        (coerceSlot slot (lowerExpr expression (lowerEnv typing.mod typing.vars results) before).1 origin
          (lowerEnv typing.mod typing.vars results)
          (lowerExpr expression (lowerEnv typing.mod typing.vars results) before).2).2).1 = [.local tracked]) :
    tracked ∈ typing.visible := by
  let env := lowerEnv typing.mod typing.vars results
  let lowered := lowerExpr expression env before
  let coerced := coerceSlot slot lowered.1 origin env lowered.2
  let addressed := emitDef (.slotAddr slot) env coerced.2
  have loweredGenerated := generated.lowerExpr expression (env := env) rfl
  have coercedGenerated : GeneratedBuilderState coerced.2 :=
    loweredGenerated.coerceSlot slot lowered.1 origin (env := env) rfl
  have addressedContinuation : NativeBuilderContinuation facts.func addressed.2 :=
    continuation.of_advance (advB_emitEffect (.store addressed.1 coerced.1 (some origin)) env addressed.2 _ _ rfl)
  have floor := emitted_slotAddr_native_floor facts.native coercedGenerated.live
    (rfl : emitDef (.slotAddr slot) env coerced.2 = addressed) live addressedContinuation
  have literal := facts.below addressed.1 floor
  rw [upper] at literal
  have same : slot = tracked := by simpa using literal
  obtain ⟨localVar, type, variableAt, visible, _⟩ := tyStmt_rebind_children source
  exact same ▸ visible

#print axioms rebind_store_tracked_visible

end Goose.Lower.Validation.SourceReplacementLexicalWriters
