import Goose.Lower.Validation.EmittedMetadataControlBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem metadata_control_branches {le : LEnv} {loop : Option LoopCtx} {before after : LS}
    {result : α} (checked : EmittedMetadata le before) (generated : GeneratedBuilderState before)
    (loopBounds : LoopBuilderTargets loop before) (loopTypes : EmittedLoopTypes loop before)
    (condition : ValueId)
    (conditionAt : before.cur.isSome = true → before.vals[condition]? = some (some (.data .bool)))
    {yes no : B ValueId} (yesSource : EmittedMetadataAction le loop yes) (noSource : EmittedMetadataAction le loop no)
    (tail : Option BlockId → ValueId → Option BlockId → ValueId → B α)
    (tailChecked : ∀ state endT valueT endF valueF, EmittedMetadata le state →
      EmittedMetadata le (tail endT valueT endF valueF le state).2)
    (run : (do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← yes
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← no
      let endF ← Goose.Lower.curBlock
      tail endT valueT endF valueF) le before = (result, after)) : EmittedMetadata le after := by
  simp only [bind_eq] at run
  obtain ⟨⟨tb, eb⟩, forked, forkRun, u1, startedT, startTRun, valueT, evaluatedT, firstRun,
    endT, readT, curTRun, u2, startedF, startFRun, valueF, evaluatedF, secondRun,
    endF, readF, curFRun, tailRun⟩ := run
  rw [curBlock_run] at curTRun curFRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj curTRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj curFRun
  have ids := fork_ids forkRun
  have advance := advB_fork condition le before _ _ forkRun
  have forkGenerated := generated.fork condition forkRun
  have forkChecked := checked.fork condition conditionAt
  rw [forkRun] at forkChecked
  have thenBound : ∀ block, some tb = some block → block < forked.blocks.size := by
    intro block same
    have sameId := congrArg Prod.fst ids.1
    have size := ids.2
    have equal := Option.some.inj same
    nat_omega
  have thenGenerated := forkGenerated.setCur (some tb) thenBound startTRun
  have thenChecked := forkChecked.setCur (some tb)
  rw [startTRun] at thenChecked
  have thenExt : forked.Ext startedT := by
    rw [setCur_run] at startTRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj startTRun
    exact .refl _
  have thenBounds := loopBounds.mono (advance.ext.trans thenExt).1
  have thenTypes := loopTypes.retained ((types_fork condition le before _ _ forkRun).trans
    (types_setCur (some tb) le forked _ _ startTRun))
  have firstChecked := yesSource.metadata startedT valueT evaluatedT thenGenerated thenBounds thenTypes firstRun thenChecked
  have firstGenerated := thenGenerated.of_runs yesSource.dense yesSource.targets thenBounds firstRun
  have firstAdvance := yesSource.advance le startedT _ _ firstRun
  have elseBound : ∀ block, some eb = some block → block < evaluatedT.blocks.size := by
    intro block same
    have sameId := congrArg Prod.snd ids.1
    have size := ids.2
    have equal := Option.some.inj same
    have grows := firstAdvance.ext.1
    have initial := thenExt.1
    nat_omega
  have elseGenerated := firstGenerated.setCur (some eb) elseBound startFRun
  have elseChecked := firstChecked.setCur (some eb)
  rw [startFRun] at elseChecked
  have elseExt : evaluatedT.Ext startedF := by
    rw [setCur_run] at startFRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj startFRun
    exact .refl _
  have elseBounds := thenBounds.mono (firstAdvance.ext.trans elseExt).1
  have elseTypes := thenTypes.retained ((yesSource.types le startedT _ _ firstRun).trans
    (types_setCur (some eb) le evaluatedT _ _ startFRun))
  have secondChecked := noSource.metadata startedF valueF evaluatedF elseGenerated elseBounds elseTypes secondRun elseChecked
  have final := tailChecked evaluatedF evaluatedT.cur valueT evaluatedF.cur valueF secondChecked
  simpa only [tailRun] using final

theorem EmittedMetadata.ifValue {le : LEnv} {loop : Option LoopCtx} {before : LS}
    (checked : EmittedMetadata le before) (generated : GeneratedBuilderState before)
    (loopBounds : LoopBuilderTargets loop before) (loopTypes : EmittedLoopTypes loop before)
    (condition : ValueId)
    (conditionAt : before.cur.isSome = true → before.vals[condition]? = some (some (.data .bool)))
    {yes no : B ValueId} (yesSource : EmittedMetadataAction le loop yes) (noSource : EmittedMetadataAction le loop no) :
    EmittedMetadata le ((Goose.Lower.whenLive 0 fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← yes
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← no
      let endF ← Goose.Lower.curBlock
      Goose.Lower.joinValue endT valueT endF valueF) le before).2 := by
  cases live : before.cur with
  | none => rw [whenLive_none _ _ _ live]; exact checked
  | some current =>
    rw [whenLive_some _ _ _ live]
    exact metadata_control_branches checked generated loopBounds loopTypes condition conditionAt yesSource noSource
      (fun endT valueT endF valueF => Goose.Lower.joinValue endT valueT endF valueF)
      (fun _ _ _ _ _ checked => checked.joinValue _ _ _ _) rfl

theorem EmittedMetadata.ifValue_recorded {le : LEnv} {loop : Option LoopCtx} {before : LS}
    (checked : EmittedMetadata le before) (generated : GeneratedBuilderState before)
    (loopBounds : LoopBuilderTargets loop before) (loopTypes : EmittedLoopTypes loop before)
    (condition : ValueId) (sourceScope : ScopeId)
    (conditionAt : before.cur.isSome = true → before.vals[condition]? = some (some (.data .bool)))
    {yes no : B ValueId} (yesSource : EmittedMetadataAction le loop yes) (noSource : EmittedMetadataAction le loop no) :
    EmittedMetadata le ((Goose.Lower.whenLive 0 fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← yes
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← no
      let endF ← Goose.Lower.curBlock
      let value ← Goose.Lower.joinValue endT valueT endF valueF
      Goose.Lower.recordValueRootRecipe value sourceScope
      Pure.pure value) le before).2 := by
  cases live : before.cur with
  | none => rw [whenLive_none _ _ _ live]; exact checked
  | some current =>
    rw [whenLive_some _ _ _ live]
    exact metadata_control_branches checked generated loopBounds loopTypes condition conditionAt yesSource noSource
      (fun endT valueT endF valueF => do
        let value ← Goose.Lower.joinValue endT valueT endF valueF
        Goose.Lower.recordValueRootRecipe value sourceScope
        Pure.pure value)
      (fun state endT valueT endF valueF checked => by
        let joined := Goose.Lower.joinValue endT valueT endF valueF le state
        exact (checked.joinValue endT endF valueT valueF).recordValueRootRecipe joined.1 sourceScope) rfl

theorem EmittedMetadata.ifArms {le : LEnv} {loop : Option LoopCtx} {before : LS}
    (checked : EmittedMetadata le before) (generated : GeneratedBuilderState before)
    (loopBounds : LoopBuilderTargets loop before) (loopTypes : EmittedLoopTypes loop before)
    (condition : ValueId)
    (conditionAt : before.cur.isSome = true → before.vals[condition]? = some (some (.data .bool)))
    {yes no : B ValueId} (yesSource : EmittedMetadataAction le loop yes) (noSource : EmittedMetadataAction le loop no) :
    EmittedMetadata le ((Goose.Lower.whenLive () fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← yes
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← no
      let endF ← Goose.Lower.curBlock
      Goose.Lower.joinArms endT endF) le before).2 := by
  cases live : before.cur with
  | none => rw [whenLive_none _ _ _ live]; exact checked
  | some current =>
    rw [whenLive_some _ _ _ live]
    exact metadata_control_branches checked generated loopBounds loopTypes condition conditionAt yesSource noSource
      (fun endT _ endF _ => Goose.Lower.joinArms endT endF)
      (fun _ _ _ _ _ checked => checked.joinArms _ _) rfl

end Goose.Lower.Validation
