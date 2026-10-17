import Goose.Lower.Validation.SourceReadyObservationValues
import Goose.Lower.Validation.ReplacementControl

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {func : Func} {state : State}

theorem observation_bind {property : Inst → Prop} {action : B α} {next : α → B β}
    {le : LEnv} {before : LS}
    (first : EmitsOnly property before (action le before).2)
    (second : EmitsOnly property (action le before).2
      (next (action le before).1 le (action le before).2).2) :
    EmitsOnly property before ((action >>= next) le before).2 := by
  simpa only [bind_run] using first.trans second

theorem observation_whenLive {property : Inst → Prop} (default : α) (action : BlockId → B α)
    (le : LEnv) (before : LS)
    (child : ∀ block, before.cur = some block → EmitsOnly property before (action block le before).2) :
    EmitsOnly property before (whenLive default action le before).2 := by
  cases current : before.cur with
  | none => rw [whenLive_none _ _ _ current]; exact .refl _ _
  | some block => rw [whenLive_some _ _ _ current]; exact child block current

theorem observation_unchanged {property : Inst → Prop} {action : B α} {le : LEnv} {before : LS}
    (same : (action le before).2.blocks = before.blocks) :
    EmitsOnly property before (action le before).2 := .of_blocks same

theorem observation_effect (effect : Effect) :
    EmitsOnlyRun (ReadyCallObservations module func state) (emitEffect effect) :=
  emitsOnly_emitEffect effect (.effect module func state effect)

theorem observation_term (term : Term) :
    EmitsOnlyRun (ReadyCallObservations module func state) (emitTerm term) :=
  emitsOnly_emitTerm term (.term module func state term)

theorem observation_initSlots (bindings : List (SlotId × ValueId × OriginId)) :
    EmitsOnlyRun (ReadyCallObservations module func state) (initSlots bindings) := by
  induction bindings with
  | nil => exact .pure _ _
  | cons binding rest ih => exact (observation_effect _).bind fun _ => ih

theorem observation_joinArms (yes no : Option BlockId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (joinArms yes no) := by
  unfold joinArms
  split
  · exact emitsOnly_setCur _ none
  · apply (emitsOnly_newBlock _ []).bind
    rintro ⟨join, parameters⟩
    apply EmitsOnlyRun.bind (next := fun _ => setCur (some join))
    · induction (yes.toList ++ no.toList) with
      | nil => exact .pure _ _
      | cons block rest ih =>
        exact (emitsOnly_pushInst block (.term (.br join [])) (.term module func state _)).bind fun _ => ih
    · intro _
      exact emitsOnly_setCur _ _

#print axioms observation_bind
#print axioms observation_whenLive
#print axioms observation_initSlots
#print axioms observation_joinArms

end Goose.Lower.Validation.ReplacementContentFlowSource
