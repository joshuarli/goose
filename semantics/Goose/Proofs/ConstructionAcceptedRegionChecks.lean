import Goose.Proofs.ConstructionAcceptedAllocation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation

theorem freshRegion_excludes_later_sample (layout : LayoutEnv) (before state : ExecutionState)
    (regionId storageId : Nat) (root : Goose.Core.RootInst) (stored : StoredValue)
    (live : Goose.Core.RootInst → Prop) (bytes : ByteArray) (run : SampledRun)
    (protection : ReceivingProtection layout state live (freshReceivingRegion before regionId))
    (retained : live root) (present : state.objects.lookup root = some (.stored stored))
    (storage : stored.storage = storageId) (fresh : before.construction.storage[storageId]? = none)
    (sampled : sampledStored stored state = .ok (bytes, run) state) (positive : 0 < run.byteStart) : False := by
  have observed := protection.observations.observations root ⟨retained, by simp [freshReceivingRegion]⟩
    (.stored stored) present stored (.stored stored)
  obtain ⟨actual, actualRun, fuel, finish, found, actualSampled, measured, lower, upper⟩ := observed.observed
  have same := ExecutionStep.ok.inj (sampled.symm.trans actualSampled)
  have sameRun : run = actualRun := (Prod.mk.inj same.1).2
  subst actualRun
  have zero : (freshReceivingRegion before regionId).limit stored.storage = 0 := by
    simp only [freshReceivingRegion, storageExtent, storage, fresh, Option.map_none, Option.getD_none]
  rw [zero] at upper
  omega

private def laterPackedOwner : Option (Nat × Nat × Nat) := Id.run do
  let layout : LayoutEnv := ⟨#[]⟩
  let action : EvalM (Nat × Nat × Nat) := do
    let outer ← newDestination layout 0 (.varr (.int .u8)) .value 0 none (some 0)
    let inner ← newDestination layout 0 (.varr (.int .u8)) .value 0 none (some 0)
    liftConstruction 0 (finishDestination inner)
    let stored ← storedDestination inner
    bindRoot (.local 0 0 0) (.stored stored)
    let (_, run) ← sampledStored stored
    let some (.stored current) := (← EvalM.get).objects.lookup (.local 0 0 0) | fault .unbound
    pure (outer, current.storage, run.byteStart)
  match action .initial with
  | .ok result _ => return some result
  | _ => return none

#guard laterPackedOwner == some (0, 1, 4)

private def nestedOwnerModule : Module := Id.run do
  let byteOwner : Ty := .varr (.int .u8)
  let vars : Array LocalVar := #[⟨"outer", byteOwner, .mutable, 0, 0⟩, ⟨"inner", byteOwner, .mutable, 1, 0⟩]
  let nested : Expr := .blockE (.mk 1 [.letS 1 (.bytes byteOwner [65] 0) 0] (some (.lit .u8 66))) 0
  let body : Block := .mk 0 [.letS 0 (.arrLit byteOwner [nested] 0) 0] none
  let implementation : Impl := ⟨"entry", #[], #[], vars, body, .unknown⟩
  return ⟨#["regions.goose"], #[], #[], #[implementation], #[⟨0, "", [], [], []⟩], 0,
    #[⟨0, 1, "let"⟩], #[], #[]⟩

#guard (match validate nestedOwnerModule with | .ok () => true | _ => false)
#guard (match eval 100 .release nestedOwnerModule with
  | .done .returned _ events => events == [.begin 0, .begin 1, .write 1 0, .publish 1, .write 0 0, .publish 0]
  | _ => false)

private def laterAcceptedOwner : Option (Nat × Nat × Nat × Nat) := Id.run do
  let action : EvalM (Nat × Nat × Nat × Nat) := do
    let activation ← freshAct
    let outerScope ← freshScope
    let before ← EvalM.get
    let config : EvalConfig := ⟨.release, nestedOwnerModule⟩
    let outer ← newDestination config.layout activation (.varr (.int .u8)) .value 0 none (some 1)
    let innerScope ← freshScope
    let some implementation := nestedOwnerModule.impls[0]? | fault .unbound
    let environment : RuntimeActivation := ⟨0, activation, implementation.vars, [(1, innerScope), (0, outerScope)], []⟩
    let _ ← execStmt 100 config environment (.letS 1 (.bytes (.varr (.int .u8)) [65] 0) 0)
    let some (.stored stored) := (← EvalM.get).objects.lookup (.local activation innerScope 1) | fault .unbound
    let (_, run) ← sampledStored stored
    pure (outer, stored.storage, run.byteStart, (freshReceivingRegion before outer).limit stored.storage)
  match action .initial with
  | .ok result _ => return some result
  | _ => return none

#guard laterAcceptedOwner == some (0, 1, 4, 0)

#print axioms freshRegion_excludes_later_sample

end Goose.Proofs.ConstructionAcceptedExecution
