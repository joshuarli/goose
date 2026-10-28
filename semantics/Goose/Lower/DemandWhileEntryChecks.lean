import Goose.Lower.DemandWhileEntryBody
import Goose.Lower.DemandWhileMixedChecks

namespace Goose.Lower.DemandWhileEntryChecks
open Goose.Core Goose.GIR Goose.Lower.DemandWhileMixedChecks

def entryContext : Context := ⟨0, "main", [], [], []⟩

theorem checked_entry_ready (profile : NumProfile) {state : St}
    (accepted : Core.validate (module .shrink) = .ok ())
    (initialized : initGlobals 50 ⟨profile, module .shrink⟩ (List.range (module .shrink).globals.size) St.initial = .ok () state) :
    Nonempty (EntryBodyDemandReady ⟨profile, module .shrink⟩ state entryContext implementation (by rfl) (by rfl)) :=
  accepted_generated_entry_body_ready accepted initialized (by rfl) (by rfl)

#guard [NumProfile.release, .debug].all fun profile =>
  match initGlobals 50 ⟨profile, module .shrink⟩ (List.range (module .shrink).globals.size) St.initial with
  | .ok () _ => true
  | _ => false

#print axioms checked_entry_ready
end Goose.Lower.DemandWhileEntryChecks
