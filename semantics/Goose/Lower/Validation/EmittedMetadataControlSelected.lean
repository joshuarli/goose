import Goose.Lower.Validation.EmittedMetadataControlBranches

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem metadata_control_selected {le : LEnv} {loop : Option LoopCtx} {before : LS}
    (checked : EmittedMetadata le before) (generated : GeneratedBuilderState before)
    (loopBounds : LoopBuilderTargets loop before) (loopTypes : EmittedLoopTypes loop before)
    {opening : B (BlockId × BlockId × α)} {body : B ValueId}
    (openingChecked : EmittedMetadata le (opening le before).2)
    (openingDense : DenseRun opening) (openingAdvance : AdvB opening) (openingTypes : TypeRun opening)
    (openingTargets : GeneratedTargetRun loop opening)
    (openingBounds : ∀ result after, opening le before = (result, after) →
      result.1 < after.blocks.size)
    (bodySource : EmittedMetadataAction le loop body) (arguments : ValueId → List ValueId) :
    EmittedMetadata le ((do
      let (target, join, payload) ← opening
      Goose.Lower.setCur (some target)
      let value ← body
      Goose.Lower.emitTerm (.br join (arguments value))
      Goose.Lower.setCur (some join)
      pure payload) le before).2 := by
  let opened := opening le before
  let selected := Goose.Lower.setCur (some opened.1.1) le opened.2
  let evaluated := body le selected.2
  have openingRun : opening le before = opened := rfl
  have openedGenerated := generated.of_runs openingDense openingTargets loopBounds openingRun
  have selectedGenerated := openedGenerated.setCur (some opened.1.1) (by
    intro target equal
    have equal := Option.some.inj equal
    subst target
    exact openingBounds _ _ rfl) (show Goose.Lower.setCur (some opened.1.1) le opened.2 = selected from rfl)
  have selectedChecked := openingChecked.setCur (some opened.1.1)
  have selectedBounds : LoopBuilderTargets loop selected.2 :=
    loopBounds.mono (openingAdvance le before _ _ rfl).ext.1
  have selectedTypes := loopTypes.retained ((openingTypes le before _ _ rfl).trans
    (types_setCur (some opened.1.1) le opened.2 _ _ rfl))
  have bodyChecked := bodySource.metadata selected.2 evaluated.1 evaluated.2 selectedGenerated selectedBounds selectedTypes rfl selectedChecked
  have closedChecked := bodyChecked.emitTerm (.br opened.1.2.1 (arguments evaluated.1)) (fun _ => .br _ _)
  have final := closedChecked.setCur (some opened.1.2.1)
  simpa only [bind_run, pure_run, opened, selected, evaluated] using final

theorem EmittedMetadata.shortCircuit {le : LEnv} {loop : Option LoopCtx} {before : LS}
    (checked : EmittedMetadata le before) (generated : GeneratedBuilderState before)
    (loopBounds : LoopBuilderTargets loop before) (loopTypes : EmittedLoopTypes loop before)
    (isAnd : Bool) (condition : ValueId)
    (conditionAt : before.cur.isSome = true → before.vals[condition]? = some (some (.data .bool)))
    {body : B ValueId} (bodySource : EmittedMetadataAction le loop body) :
    EmittedMetadata le (Goose.Lower.shortCircuit isAnd condition body le before).2 := by
  unfold Goose.Lower.shortCircuit
  cases live : before.cur with
  | none => rw [whenLive_none _ _ _ live]; exact checked
  | some current =>
    rw [whenLive_some _ _ _ live]
    exact metadata_control_selected checked generated loopBounds loopTypes (checked.scFork isAnd condition conditionAt)
      (dense_scFork isAnd condition) (advB_scFork isAnd condition) (types_scFork isAnd condition)
      (generatedTargets_scFork loop isAnd condition)
      (by
        intro result after run
        have ids := scFork_ids run
        have id := congrArg Prod.fst ids.1
        have size := ids.2
        nat_omega) bodySource (fun value => [value])

theorem EmittedMetadata.ifThen {le : LEnv} {loop : Option LoopCtx} {before : LS}
    (checked : EmittedMetadata le before) (generated : GeneratedBuilderState before)
    (loopBounds : LoopBuilderTargets loop before) (loopTypes : EmittedLoopTypes loop before)
    (condition : ValueId)
    (conditionAt : before.cur.isSome = true → before.vals[condition]? = some (some (.data .bool)))
    {body : B ValueId} (bodySource : EmittedMetadataAction le loop body) :
    EmittedMetadata le ((Goose.Lower.whenLive () fun _ => do
      let (target, join) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some target)
      let _ ← body
      Goose.Lower.emitTerm (.br join [])
      Goose.Lower.setCur (some join)) le before).2 := by
  cases live : before.cur with
  | none => rw [whenLive_none _ _ _ live]; exact checked
  | some current =>
    rw [whenLive_some _ _ _ live]
    have output := metadata_control_selected checked generated loopBounds loopTypes
      (opening := do let pair ← Goose.Lower.fork condition; pure (pair.1, pair.2, ()))
      (by simpa only [bind_run, pure_run] using checked.fork condition conditionAt)
      (DenseRun.bind (dense_fork condition) fun pair => DenseRun.pure (pair.1, pair.2, ()))
      (AdvB.bind (advB_fork condition) fun pair => AdvB.pure (pair.1, pair.2, ()))
      (TypeRun.bind (types_fork condition) fun pair => TypeRun.pure (pair.1, pair.2, ()))
      (GeneratedTargetRun.bind (generatedTargets_fork loop condition) fun pair => generatedTargets_pure loop (pair.1, pair.2, ()))
      (by
        intro result after run
        obtain ⟨pair, state, forkRun, done⟩ := bind_eq.mp run
        obtain ⟨rfl, rfl⟩ := pure_eq.mp done
        have ids := fork_ids forkRun
        have id := congrArg Prod.fst ids.1
        have size := ids.2
        nat_omega) bodySource (fun _ => [])
    simpa only [bind_run, pure_run] using output

end Goose.Lower.Validation
