import Goose.Lower.Validation.PermissionPreservationContents
import Goose.Lower.Validation.ExpressionTypingFreshContents

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def FreshWritableEvidence (le : LEnv) (first : Nat) (state : LS) (value : ValueId) : Prop :=
  ∃ writable contents,
    WritableClosed (le.globals.map (·.2)) le.mod.structs (permissionFunc le state) state.vals writable contents ∧
    ContentsClosed (le.globals.map (·.2)) le.mod.structs (permissionFunc le state) state.vals contents ∧
    NonIntegerParameters (permissionFunc le state) writable ∧
    NonIntegerParameters (permissionFunc le state) contents ∧ writable value ∧
    (∀ candidate, writable candidate → first ≤ candidate) ∧
    (∀ candidate, contents candidate → first ≤ candidate)

theorem FreshWritableEvidence.forget {le : LEnv} {first : Nat} {state : LS} {value : ValueId}
    (evidence : FreshWritableEvidence le first state value) : WritableEvidence le state value := by
  obtain ⟨writable, contents, bindings, elements, bindingParams, contentParams, permitted, _, _⟩ := evidence
  exact ⟨writable, contents, bindings, elements, bindingParams, contentParams, permitted⟩

theorem FreshWritableEvidence.weaken {le : LEnv} {first earlier : Nat} {state : LS} {value : ValueId}
    (evidence : FreshWritableEvidence le first state value) (bound : earlier ≤ first) :
    FreshWritableEvidence le earlier state value := by
  obtain ⟨writable, contents, bindings, elements, bindingParams, contentParams, permitted, freshW, freshC⟩ := evidence
  exact ⟨writable, contents, bindings, elements, bindingParams, contentParams, permitted,
    fun candidate member => Nat.le_trans bound (freshW candidate member),
    fun candidate member => Nat.le_trans bound (freshC candidate member)⟩

theorem FreshWritableEvidence.ext {le : LEnv} {first : Nat} {before after : LS} {value : ValueId}
    {loop : Option LoopCtx} (evidence : FreshWritableEvidence le first before value)
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (grows : before.vals.size ≤ after.vals.size)
    (types : TypePrefix before after) (frames : LoopBuilderFrames loop before)
    (framed : TermEdgesFramed loop before after) : FreshWritableEvidence le first after value := by
  obtain ⟨writable, contents, bindings, elements, bindingParams, contentParams, permitted, freshW, freshC⟩ := evidence
  refine ⟨writable, contents,
    bindings.ext beforeDense afterDense extension grows types frames framed bindingParams,
    elements.ext beforeDense afterDense extension grows types frames framed contentParams,
    ?_, ?_, permitted, freshW, freshC⟩
  · apply bindingParams.ext beforeDense afterDense extension
    intro candidate member
    simpa only [permissionFunc_numValues beforeDense le] using bindings.bounded candidate member
  · apply contentParams.ext beforeDense afterDense extension
    intro candidate member
    simpa only [permissionFunc_numValues beforeDense le] using elements.bounded candidate member

theorem FreshWritableEvidence.of_run {α : Type} {action : B α} {le : LEnv} {first : Nat}
    {before after : LS} {value : ValueId} {result : α} {loop : Option LoopCtx}
    (evidence : FreshWritableEvidence le first before value) (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (beforeDense : before.DenseDefinitions) (bounded : LiveBound before)
    (frames : LoopBuilderFrames loop before) (framed : TermEdgesFramed loop before after) :
    FreshWritableEvidence le first after value := by
  have afterDense := (dense le before result after run beforeDense bounded).1
  have advanced := advances le before result after run
  exact evidence.ext beforeDense afterDense advanced.ext advanced.vals
    (typed le before result after run) frames framed

theorem FreshWritableEvidence.of_framed_run {α : Type} {action : B α} {le : LEnv} {first : Nat}
    {before after : LS} {value : ValueId} {result : α} {loop : Option LoopCtx}
    (evidence : FreshWritableEvidence le first before value) (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (frameRun : GeneratedTargetFrameRun loop action)
    (beforeDense : before.DenseDefinitions) (bounded : LiveBound before)
    (frames : LoopBuilderFrames loop before) : FreshWritableEvidence le first after value := by
  have framed := (frameRun before le before result after (.refl _) frames (.refl loop before) run).1
  exact evidence.of_run run dense advances typed beforeDense bounded frames framed

theorem freshWritableEvidence_definition {le : LEnv} {first : Nat} {before after : LS}
    {value : ValueId} {op : Op} {current : BlockId} {contents : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (elements : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals contents)
    (parameters : NonIntegerParameters (permissionFunc le after) contents)
    (fresh : ∀ candidate, contents candidate → first ≤ candidate) (bound : first ≤ before.vals.size)
    (operation : WritableOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals contents value op) :
    FreshWritableEvidence le first after value := by
  refine ⟨_, contents, writableClosed_fresh_definition checked bounded live run operation,
    elements, nonIntegerParameters_fresh_definition checked live run, parameters, rfl, ?_, fresh⟩
  intro candidate member
  rw [member, (emitDef_fresh_size live run).1]
  exact bound

theorem FreshContentsEvidence.emitDef_binding_dependency {le : LEnv} {first : Nat} {before after : LS}
    {owner value : ValueId} {op : Op} {current : BlockId}
    (evidence : FreshContentsEvidence le first before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (operation : ∀ contents, contents owner →
      WritableOperation (le.globals.map (·.2)) le.mod.structs
        (permissionFunc le after) after.vals contents value op) :
    FreshWritableEvidence le first after value := by
  obtain ⟨contents, elements, parameters, permitted, fresh⟩ := evidence
  have ownerBound : owner < before.vals.size := by
    simpa only [permissionFunc_numValues checked le] using elements.bounded owner permitted
  exact freshWritableEvidence_definition checked bounded live run
    (elements.emitDef_preserve checked bounded live run) (parameters.emitDef_preserve live run)
    fresh (Nat.le_trans (fresh owner permitted) (Nat.le_of_lt ownerBound)) (operation contents permitted)

#print axioms FreshWritableEvidence.of_framed_run
#print axioms freshWritableEvidence_definition
#print axioms FreshContentsEvidence.emitDef_binding_dependency

end Goose.Lower.Validation
