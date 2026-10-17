import Goose.Lower.Validation.EmittedMetadataActions
import Goose.Lower.Validation.DeadFrontier
import Goose.Lower.Validation.Typing

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem metadata_dead_coerceTo (target : Ty) (value : ValueId) (origin : OriginId) :
    DeadRun (Goose.Lower.coerceTo target value origin) := by
  unfold Goose.Lower.coerceTo
  refine DeadRun.bind (dead_valTy value) fun source => ?_
  split
  · exact dead_emitDef _
  · exact DeadRun.bind (dead_emitDef _) fun _ => dead_emitDef _
  · exact DeadRun.pure value

theorem metadata_dead_coerceSlot (slot : SlotId) (value : ValueId) (origin : OriginId) :
    DeadRun (Goose.Lower.coerceSlot slot value origin) := by
  unfold Goose.Lower.coerceSlot
  exact DeadRun.bind dead_read fun env => match env.slots[slot]? with
    | none => DeadRun.pure value
    | some destination => metadata_dead_coerceTo destination.ty value origin

theorem metadata_dead_coerceResult (value : ValueId) (origin : OriginId) :
    DeadRun (Goose.Lower.coerceResult value origin) := by
  unfold Goose.Lower.coerceResult
  exact DeadRun.bind dead_read fun env => match env.results.head? with
    | none => DeadRun.pure value
    | some destination => metadata_dead_coerceTo destination value origin

theorem metadata_coerceSlot_typed {le : LEnv} {before : LS} {slot value : ValueId} {source : Ty}
    {descriptor : Slot} {block : BlockId} (slotAt : le.slots[slot]? = some descriptor)
    (valueAt : before.vals[value]? = some (some (.data source)))
    (permission : source.passableTo descriptor.ty = true) (live : before.cur = some block) (origin : OriginId) :
    let output := Goose.Lower.coerceSlot slot value origin le before
    output.2.vals[output.1]? = some (some (.data descriptor.ty)) := by
  have same : Goose.Lower.coerceSlot slot value origin le before = Goose.Lower.coerceTo descriptor.ty value origin le before := by
    simp only [Goose.Lower.coerceSlot, bind_run, read_apply, slotAt]
  dsimp only
  rw [same]
  exact (coerceTo_typed (le := le) valueAt permission live origin).2

theorem metadata_coerceResult_typed {le : LEnv} {before : LS} {value : ValueId} {source target : Ty}
    {block : BlockId} (results : le.results = [target])
    (valueAt : before.vals[value]? = some (some (.data source)))
    (permission : source.passableTo target = true) (live : before.cur = some block) (origin : OriginId) :
    let output := Goose.Lower.coerceResult value origin le before
    output.2.vals[output.1]? = some (some (.data target)) := by
  have same : Goose.Lower.coerceResult value origin le before = Goose.Lower.coerceTo target value origin le before := by
    simp only [Goose.Lower.coerceResult, bind_run, read_apply, results, List.head?_cons]
  dsimp only
  rw [same]
  exact (coerceTo_typed (le := le) valueAt permission live origin).2


theorem metadata_dead_leaveAll : ∀ scopes, DeadRun (Goose.Lower.leaveAll scopes)
  | [] => .pure ()
  | scope :: rest => DeadRun.bind (dead_emitEffect (.leave scope)) fun _ => metadata_dead_leaveAll rest

theorem metadata_dead_leaveTo (depth : Nat) : DeadRun (Goose.Lower.leaveTo depth) := by
  unfold Goose.Lower.leaveTo
  refine DeadRun.bind ?_ fun state => metadata_dead_leaveAll _
  intro le before result after run live
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact live

end Goose.Lower.Validation
