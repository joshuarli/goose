import Goose.Lower.Validation.ExpressionTypingContentsEvidence

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def FreshContentsEvidence (le : LEnv) (first : Nat) (state : LS) (value : ValueId) : Prop :=
  ∃ authorized,
    ContentsClosed (le.globals.map (·.2)) le.mod.structs (permissionFunc le state) state.vals authorized ∧
    NonIntegerParameters (permissionFunc le state) authorized ∧ authorized value ∧
    ∀ candidate, authorized candidate → first ≤ candidate

theorem FreshContentsEvidence.forget {le : LEnv} {first : Nat} {state : LS} {value : ValueId}
    (evidence : FreshContentsEvidence le first state value) : ContentsEvidence le state value := by
  obtain ⟨authorized, closed, noninteger, member, _⟩ := evidence
  exact ⟨authorized, closed, noninteger, member⟩

theorem FreshContentsEvidence.weaken {le : LEnv} {first earlier : Nat} {state : LS} {value : ValueId}
    (evidence : FreshContentsEvidence le first state value) (bound : earlier ≤ first) :
    FreshContentsEvidence le earlier state value := by
  obtain ⟨authorized, closed, noninteger, member, fresh⟩ := evidence
  exact ⟨authorized, closed, noninteger, member, fun candidate allowed => Nat.le_trans bound (fresh candidate allowed)⟩

theorem FreshContentsEvidence.ext {le : LEnv} {first : Nat} {before after : LS} {value : ValueId}
    {loop : Option LoopCtx} (evidence : FreshContentsEvidence le first before value)
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (grows : before.vals.size ≤ after.vals.size)
    (types : TypePrefix before after) (frames : LoopBuilderFrames loop before)
    (framed : TermEdgesFramed loop before after) : FreshContentsEvidence le first after value := by
  obtain ⟨authorized, closed, noninteger, permitted, fresh⟩ := evidence
  refine ⟨authorized, closed.ext beforeDense afterDense extension grows types frames framed noninteger, ?_, permitted, fresh⟩
  apply noninteger.ext beforeDense afterDense extension
  intro candidate member
  simpa only [permissionFunc_numValues beforeDense le] using closed.bounded candidate member

theorem FreshContentsEvidence.of_run {α : Type} {action : B α} {le : LEnv} {first : Nat}
    {before after : LS} {value : ValueId} {result : α} {loop : Option LoopCtx}
    (evidence : FreshContentsEvidence le first before value) (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (beforeDense : before.DenseDefinitions) (bounded : LiveBound before)
    (frames : LoopBuilderFrames loop before) (framed : TermEdgesFramed loop before after) :
    FreshContentsEvidence le first after value := by
  have afterDense := (dense le before result after run beforeDense bounded).1
  have advanced := advances le before result after run
  exact evidence.ext beforeDense afterDense advanced.ext advanced.vals
    (typed le before result after run) frames framed

theorem FreshContentsEvidence.of_framed_run {α : Type} {action : B α} {le : LEnv} {first : Nat}
    {before after : LS} {value : ValueId} {result : α} {loop : Option LoopCtx}
    (evidence : FreshContentsEvidence le first before value) (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (frameRun : GeneratedTargetFrameRun loop action)
    (beforeDense : before.DenseDefinitions) (bounded : LiveBound before)
    (frames : LoopBuilderFrames loop before) : FreshContentsEvidence le first after value := by
  have framed := (frameRun before le before result after (.refl _) frames (.refl loop before) run).1
  exact evidence.of_run run dense advances typed beforeDense bounded frames framed

theorem freshContentsEvidence_definition {le : LEnv} {before after : LS} {value : ValueId} {op : Op}
    {current : BlockId} (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (operation : ContentsOperation (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals (fun candidate => candidate = value) value op) :
    FreshContentsEvidence le before.vals.size after value := by
  refine ⟨_, contentsClosed_fresh_definition checked bounded live run operation,
    nonIntegerParameters_fresh_definition checked live run, rfl, ?_⟩
  intro candidate member
  rw [member, (emitDef_fresh_size live run).1]
  exact Nat.le_refl _

theorem FreshContentsEvidence.emitDef_dependency {le : LEnv} {first : Nat} {before after : LS}
    {owner value : ValueId} {op : Op} {current : BlockId}
    (evidence : FreshContentsEvidence le first before owner)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after))
    (operation : ∀ authorized, authorized owner →
      ContentsOperation (le.globals.map (·.2)) le.mod.structs
        (permissionFunc le after) after.vals authorized value op) :
    FreshContentsEvidence le first after value := by
  obtain ⟨authorized, closed, noninteger, permitted, fresh⟩ := evidence
  refine ⟨fun candidate => authorized candidate ∨ candidate = value, ?_, ?_, Or.inr rfl, ?_⟩
  · exact closed.emitDef_extend checked bounded live run (operation _ (Or.inl permitted))
  · exact (noninteger.emitDef_preserve live run).union (nonIntegerParameters_fresh_definition checked live run)
  · intro candidate allowed
    rcases allowed with allowed | rfl
    · exact fresh candidate allowed
    · have ownerBound : owner < before.vals.size := by
        simpa only [permissionFunc_numValues checked le] using closed.bounded owner permitted
      rw [(emitDef_fresh_size live run).1]
      exact Nat.le_trans (fresh owner permitted) (Nat.le_of_lt ownerBound)

#print axioms FreshContentsEvidence.emitDef_dependency

end Goose.Lower.Validation
