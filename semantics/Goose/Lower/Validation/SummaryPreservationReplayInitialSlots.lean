import Goose.Lower.Validation.SummaryPreservationReplayBuilder
import Goose.Lower.Validation.SummaryPreservationInitialSlots

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem initialSlots (bindings : List (SlotId × ValueId × OriginId))
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (metadata : ∀ binding ∈ bindings,
      binding.1 < le.slots.size ∧ binding.2.2 < le.mod.origins.size)
    (values : ls.cur.isSome = true → ∀ binding ∈ bindings, binding.2.1 < ls.vals.size)
    (roots : ∀ binding ∈ bindings, ∀ root ∈ rootsAt upper.vals binding.2.1,
      root ∈ rootsAt upper.slots binding.1) :
    ReplayBuilder module results vt func target le scopeCount slots
      (initSlots bindings le ls).2 upper := by
  induction bindings generalizing ls with
  | nil => exact ready
  | cons binding rest ih =>
    rcases binding with ⟨slot, value, origin⟩
    have restMetadata := fun binding member => metadata binding (List.mem_cons_of_mem _ member)
    have restRoots := fun binding member => roots binding (List.mem_cons_of_mem _ member)
    cases current : ls.cur with
    | none =>
      have run : initSlots ((slot, value, origin) :: rest) le ls = initSlots rest le ls := by
        simp only [initSlots, bind_run, emitEffect_none _ _ current]
      rw [run]
      exact ih ready restMetadata (by simp [current]) restRoots
    | some block =>
      have live : ls.cur.isSome = true := by simp [current]
      have generated := ready.emitEffect (.slotInit slot value (some origin))
        (by
          apply Inst.SymbolsWithin.eff
          · simpa [Effect.uses] using values live (slot, value, origin) (by simp)
          · intro candidate row
            cases row
            exact (metadata (slot, value, origin) (by simp)).2
          · exact (metadata (slot, value, origin) (by simp)).1)
        (roots (slot, value, origin) (by simp)) (effectRefinement_empty func target)
      have restValues : (Goose.Lower.emitEffect (.slotInit slot value (some origin)) le ls).2.cur.isSome = true →
          ∀ binding ∈ rest, binding.2.1 < (Goose.Lower.emitEffect (.slotInit slot value (some origin)) le ls).2.vals.size := by
        rw [emitEffect_run _ _ current]
        intro _ binding member
        exact values live binding (List.mem_cons_of_mem _ member)
      have completed := ih generated restMetadata restValues restRoots
      simpa only [initSlots, bind_run] using completed

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
