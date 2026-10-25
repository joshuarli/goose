import Goose.Lower.Validation.ActualContentsAmbient

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ActualContentsIndependent : Op → Prop
  | .fieldAddr .. | .ownerBorrow .. | .snapshot .. | .refElem .. | .indexChecked .. | .indexProven .. => False
  | _ => True

theorem actualContents_terminal {le : LEnv} {before after : LS} {value : ValueId} {op : Op}
    {type : VTy} {current : BlockId}
    (independent : ActualContentsIndependent op) (generated : GeneratedBuilderState before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (typed : after.vals[value]? = some (some type)) :
    ActualContentsExtraction le before.vals.size after value := by
  intro ambient allowed
  have operation := ambient.emitted live (generated.live current live) run allowed
  have futureTyped := ambient.types value type typed
  apply freshContentsEvidence_definition generated.dense generated.live live run
  cases op <;> first
    | contradiction
    | exact operation
    | simpa only [ContentsOperation, typedPermissions, futureTyped, typed] using operation

theorem actualContents_terminal_read {le : LEnv} {before after : LS}
    {address value : ValueId} {place : Place} {type : VTy} {current : BlockId}
    (generated : GeneratedBuilderState before) (live : before.cur = some current)
    (run : (do
      let loaded ← emitDef (.load address)
      recordReadValueRootRecipe loaded place
      pure loaded) le before = (value, after))
    (typed : after.vals[value]? = some (some type)) :
    ActualContentsExtraction le before.vals.size after value := by
  obtain ⟨loaded, middle, emitted, tail⟩ := bind_eq.mp run
  obtain ⟨_, recorded, recordRun, returned⟩ := bind_eq.mp tail
  obtain ⟨rfl, rfl⟩ := pure_eq.mp returned
  have values : recorded.vals = middle.vals := by
    have same : (recordReadValueRootRecipe loaded place le middle).2.vals = middle.vals := by
      cases place <;> simp only [recordReadValueRootRecipe_run] <;> first
        | rfl
        | (split <;> simp only [recordValueRootSource_run] <;> rfl)
    simpa only [recordRun] using same
  have extract := actualContents_terminal (by trivial) generated live emitted (values ▸ typed)
  intro ambient allowed
  have evidence := extract
    (ambient.before (advB_recordReadValueRootRecipe loaded place _ _ _ _ recordRun).ext
      (types_recordReadValueRootRecipe loaded place _ _ _ _ recordRun)) allowed
  have final := evidence.recordReadValueRootRecipe place
  simpa only [recordRun] using final

theorem actualContents_borrowTo {le : LEnv} {before after : LS} {first : Nat}
    {owner value : ValueId} {mu : Mutability} {current : BlockId}
    (generated : GeneratedBuilderState before) (live : before.cur = some current)
    (run : borrowTo mu owner le before = (value, after))
    (extract : ActualContentsExtraction le first before owner) :
    ActualContentsExtraction le first after value := by
  intro ambient allowed
  rcases borrowTo_cases run with freeze | borrow
  · rcases freezeTo_cases freeze with ⟨rfl, rfl⟩ | frozen
    · exact extract ambient allowed
    · have impossible := ambient.emitted live (generated.live current live) frozen allowed
      exact impossible.elim
  · have ownerAllowed := ambient.emitted live (generated.live current live) borrow allowed
    have evidence := extract (ambient.before (advB_emitDef _ _ _ _ _ borrow).ext
      (types_emitDef _ _ _ _ _ borrow)) ownerAllowed
    exact evidence.emitDef_dependency generated.dense generated.live live borrow (fun _ permitted => permitted)

theorem ActualContentsExtraction.weaken {le : LEnv} {first earlier : Nat} {site : LS} {value : ValueId}
    (extract : ActualContentsExtraction le first site value) (bound : earlier ≤ first) :
    ActualContentsExtraction le earlier site value := fun ambient allowed => (extract ambient allowed).weaken bound

end Goose.Lower.Validation
