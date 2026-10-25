import Goose.Lower.Validation.SummaryPreservationReplayBuilder
import Goose.Lower.Validation.SummaryPreservationTypedSlots

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def entryRootValues (types : List VTy) : Array (List RootRef) :=
  types.toArray.mapIdx fun index ty => if ty.refLike then [.param index] else []

def entryReplayState (types : List VTy) (le : LEnv) : LS :=
  let start := newBlock types le initState
  { start.2 with cur := some start.1.1 }

theorem entryReplayState_values_size (types : List VTy) (le : LEnv) :
    (entryReplayState types le).vals.size = types.length := by
  change (pushParamTypes types #[]).size = types.length
  simpa using array_size_pushParamTypes types #[]

theorem entryReplayState_instructions (types : List VTy) (le : LEnv) :
    (entryReplayState types le).insts = [] := by
  change (#[({ params := ((List.range types.length).map (0 + ·)).zip types, insts := #[] } : BlockB)]).toList.flatMap
    (fun block => block.insts.toList) = []
  simp

theorem entryReplayState_current (types : List VTy) (le : LEnv) :
    (entryReplayState types le).CurrentBlocks := by
  intro block current
  have identity : block = 0 := by
    simpa [entryReplayState, newBlock, bind_run, initState, pure_run] using current.symm
  subst block
  change 0 < (#[({ params := ((List.range types.length).map (0 + ·)).zip types, insts := #[] } : BlockB)]).size
  simp

theorem entryReplayBuilder (module : GIR.Module) (results : Array (List RootRef))
    (vt : Array (Option VTy)) (func : Func) (target : Core.Eff) (le : LEnv)
    (scopeCount : Nat) (slots : Array (List RootRef)) (types : List VTy) :
    ReplayBuilder module results vt func target le scopeCount slots (entryReplayState types le)
      ⟨slots, entryRootValues types⟩ := by
  have symbols : (entryReplayState types le).SymbolWF le scopeCount := by
    exact (LS.symbolWF_initState le scopeCount).newBlockCur
  have empty := entryReplayState_instructions types le
  refine ⟨⟨?_, ?_⟩, ?_, symbols, entryReplayState_current types le, rfl, RecipeBounds.empty rfl⟩
  · simp [entryRootValues, entryReplayState_values_size]
  · intro inst member
    rw [empty] at member
    cases member
  · intro inst member
    rw [empty] at member
    cases member

theorem lowerContext_entryReplayBuilder (module : Core.Module) (ctx : Context) (impl : Impl)
    (results : Array (List RootRef)) (vt : Array (Option VTy)) (target : Core.Eff) (scopeCount : Nat) :
    ReplayBuilder (lower module) results vt (lowerContextAt module ctx impl) target
      (lowerEnv module impl.vars impl.results.toList) scopeCount (typedContextSlotUpper module ctx impl)
      (entryReplayState (impl.params.toList.map fun param => .data (tyOfVar impl param.var))
        (lowerEnv module impl.vars impl.results.toList))
      ⟨typedContextSlotUpper module ctx impl,
        entryRootValues (impl.params.toList.map fun param => .data (tyOfVar impl param.var))⟩ :=
  entryReplayBuilder _ _ _ _ _ _ _ _ _

end Goose.Lower.Validation.SummaryPreservation
