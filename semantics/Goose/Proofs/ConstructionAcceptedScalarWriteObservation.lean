import Goose.Proofs.ConstructionAcceptedScalarWriteRuntime
import Goose.Proofs.ConstructionAcceptedBindingCounters

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem writeLoc_root_observation (fuel : Nat) (layout : LayoutEnv) (root : Goose.Core.RootInst)
    (old value : Value) (before : ExecutionState) (found : before.objects.lookup root = some old) :
    let step := writeLoc fuel layout ⟨root, []⟩ value before
    let after := Goose.Proofs.Exit.stepState step
    after.nextAct = before.nextAct ∧ after.nextScope = before.nextScope ∧
      (∀ other, other ≠ root → after.objects.lookup other = before.objects.lookup other ∧
        after.objectOrdinals.lookup other = before.objectOrdinals.lookup other) ∧
      match step with | .ok _ _ => after.objects.lookup root = some value | .stop .. => True | _ => False := by
  cases fuel with
  | zero => simp [writeLoc, EvalM.get, found, bind, writeValuePath, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
  | succ fuel =>
    obtain ⟨after, bound, objects⟩ := bindRoot_objects root value before
    have counters := bindRoot_counters root value before after bound
    have outside : ∀ other, other ≠ root → after.objects.lookup other = before.objects.lookup other ∧
        after.objectOrdinals.lookup other = before.objectOrdinals.lookup other := by
      intro other different
      exact ⟨bindRoot_lookup_other root other value before after bound different,
        bindRoot_ordinals_other root other value before after bound different⟩
    have current : after.objects.lookup root = some value := by simp [objects]
    simpa [writeLoc, EvalM.get, found, bind, writeValuePath, pure, bound, Goose.Proofs.Exit.stepState] using
      And.intro counters.1 (And.intro counters.2 (And.intro outside current))

#print axioms writeLoc_root_observation
end Goose.Proofs.ConstructionAcceptedExecution
