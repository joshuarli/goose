import Goose.Lower.Validation.SummaryPreservationReplayNativeLoopsEachPrelude
import Goose.Lower.Validation.SourceRootShapeReads

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem types_nativeEachPrelude (regrow : Bool) (owner : Option ValueId) (view : ValueId)
    {body : Nat → BlockId → BlockId → ValueId → B ValueId}
    (bodyTypes : ∀ depth header exit counter, TypeRun (body depth header exit counter)) :
    TypeRun (nativeEachPrelude regrow owner view body) := by
  unfold nativeEachPrelude
  apply TypeRun.bind (types_eachSampled _ _)
  intro sampled
  apply TypeRun.bind (types_emitDef _)
  intro initial
  apply TypeRun.bind (types_newBlock _)
  intro pair
  rcases pair with ⟨header, parameters⟩
  exact TypeRun.bind (types_emitTerm _) (fun _ => TypeRun.bind (types_setCur _)
    (fun _ => types_lowerEach _ _ _ _ _ (fun depth exit => bodyTypes depth header exit (parameters.headD 0))))

theorem native_each_prefix_stack (regrow : Bool) (view : ValueId) (le : LEnv) (state : LS) :
    (nativeEachPrefix regrow view le state).state.stack = state.stack := by
  let sampled := eachSampled regrow view le state
  let initial := Goose.Lower.emitDef (.constInt .i64 0) le sampled.2
  let allocated := newBlock [.data (.int .i64)] le initial.2
  let bridged := Goose.Lower.emitTerm (.br allocated.1.1 [initial.1]) le allocated.2
  change bridged.2.stack = state.stack
  exact (advB_emitTerm _ le allocated.2 () bridged.2 rfl).stack.trans
    ((advB_newBlock1 (.data (.int .i64)) le initial.2 allocated.1 allocated.2 rfl).stack.trans
      ((advB_emitDef (.constInt .i64 0) le sampled.2 initial.1 initial.2 rfl).stack.trans
        (advB_eachSampled regrow view le state sampled.1 sampled.2 rfl).stack))

theorem native_each_entry_stack (regrow : Bool) (owner : Option ValueId) (sampled counter : ValueId)
    (le : LEnv) (state : LS) : (ReplayBuilder.eachLoopBodyEntry regrow owner sampled counter le state).stack = state.stack := by
  let length := eachLen regrow owner sampled le state
  exact (ReplayBuilder.native_range_body_stack .i64 counter length.1 le length.2).trans
    (advB_eachLen regrow owner sampled le state length.1 length.2 rfl).stack

theorem native_eachSource_view_row {typingEnv : TEnv} {env : PEnv} {view : View} {info : Ty × Bool}
    {start finish : Nat} {initial : LS}
    (tables : SourceRootTables typingEnv env) (generated : GeneratedBuilderState initial)
    (source : Core.tyView typingEnv view start = .ok (info, finish))
    (live : (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.cur.isSome = true) :
    ∃ mu, (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2.vals[
      (lowerEachSource view (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1.2]? = some (some (.view mu info.1)) := by
  let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
  let produced := lowerEachSource view le initial
  have environment : lowerEnv typingEnv.mod typingEnv.vars env.impl.results.toList = le := by
    rw [← tables.moduleEq, ← tables.variablesEq]
  have viewRun : lowerView view le initial = (produced.1.2, produced.2) := by cases view <;> rfl
  apply lowerView_generated_typed view source
  · rw [environment]
    exact viewRun
  · exact live

#print axioms native_eachSource_view_row

end Goose.Lower.Validation.SummaryPreservation
