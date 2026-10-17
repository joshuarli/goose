import Goose.Lower.Validation.ReplacementSourceSitesStatements

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

variable {targets : List BlockId}

theorem ReplacementSitesBuilder.emitReplacement {le : LEnv} {before after : LS}
    {owner value : ValueId} {origin : OriginId}
    (checked : ReplacementSitesBuilder (targets := targets) le before)
    (run : Goose.Lower.emitEffect (.replace owner value (some origin)) le before = ((), after))
    (source : ∀ block body, before.cur = some block → before.blocks[block]? = some body →
      Nonempty (ReservedReplacementSiteAt targets le after block body.insts.size owner value origin)) :
    ReplacementSitesBuilder (targets := targets) le after := by
  have extension := (advB_emitEffect (.replace owner value (some origin)) le before () after run).ext
  have preserved : ReplacementIntervalsPreserved targets before after :=
    .of_run (generatedTargetFrame_emitEffect none _) run
  have types := types_emitEffect (.replace owner value (some origin)) le before () after run
  cases current : before.cur with
  | none =>
    rw [emitEffect_none _ _ current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some index =>
    rw [emitEffect_run _ _ current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    intro block body row position instruction lookup
    change (before.blocks.modify index (fun body =>
      { body with insts := body.insts.push (.eff (.replace owner value (some origin))) }))[block]? = some body at row
    rw [Array.getElem?_modify] at row
    by_cases same : index = block
    · subst block
      simp only [ite_true] at row
      cases oldRow : before.blocks[index]? with
      | none => simp [oldRow] at row
      | some previous =>
        simp only [oldRow, Option.map_some, Option.some.injEq] at row
        subst body
        change (previous.insts.push (.eff (.replace owner value (some origin))))[position]? = some instruction at lookup
        by_cases fresh : position = previous.insts.size
        · subst position
          simp only [Array.getElem?_push_eq, Option.some.injEq] at lookup
          subst instruction
          exact source index previous current oldRow
        · rw [Array.getElem?_push, if_neg fresh] at lookup
          exact (checked index previous oldRow position instruction lookup).retained extension types preserved
    · simp only [same, ite_false] at row
      exact (checked block body row position instruction lookup).retained extension types preserved

theorem replacementSites_assignWhole_source {env output : Core.TEnv} {results : List Ty}
    {owner : Place} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assignWhole owner expr origin) start = .ok (output, finish))
    (placeChild : ReplacementSitesPlaceChild (targets := targets) env results owner)
    (exprChild : ReplacementSitesExprChild (targets := targets) env results expr)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (targets := targets) (lowerEnv env.mod env.vars results) before
      (lowerStmt loop (.assignWhole owner expr origin)) := by
  obtain ⟨info, element, childStart, placeSource, shape, childSource, _, _, _⟩ :=
    tyStmt_assignWhole_children source
  let le := lowerEnv env.mod env.vars results
  let addressed := lowerPlace owner le before
  let cleared := emitEffect (.clear addressed.1 (some origin)) le addressed.2
  let captured := lowerExpr expr le cleared.2
  let published := emitEffect (.replace addressed.1 captured.1 (some origin)) le captured.2
  have addressedGenerated := generated.lowerPlace owner
    (show lowerPlace owner le before = addressed from rfl)
  have clearedGenerated := addressedGenerated.emitEffect (.clear addressed.1 (some origin))
    (show emitEffect _ le addressed.2 = cleared from rfl)
  have addressedTypes := (types_emitEffect (.clear addressed.1 (some origin)) le addressed.2 cleared.1 cleared.2 rfl).trans
    ((types_lowerExpr expr le cleared.2 captured.1 captured.2 rfl).trans
      (types_emitEffect (.replace addressed.1 captured.1 (some origin)) le captured.2 published.1 published.2 rfl))
  intro bounded checked
  have addressedResult := placeChild placeSource generated bounded checked
  have clearedExt := (advB_emitEffect (.clear addressed.1 (some origin)) le addressed.2 _ _ rfl).ext
  have clearedChecked : ReplacementSitesBuilder (targets := targets) le cleared.2 :=
    addressedResult.2.emitEffect (effect := .clear addressed.1 (some origin)) trivial rfl
  have capturedResult := exprChild childSource clearedGenerated
    (bounded.mono (addressedResult.1.trans clearedExt)) clearedChecked
  have publishedExt := (advB_emitEffect (.replace addressed.1 captured.1 (some origin)) le captured.2 _ _ rfl).ext
  have avoids : IntervalTargetsAvoid cleared.2 captured.2 targets := by
    intro target member
    exact Or.inl (Nat.lt_of_lt_of_le (bounded target member) (addressedResult.1.trans clearedExt).1)
  have publishedFrames : IntervalEdgesFramed cleared.2 captured.2 published.2 :=
    ReplacementIntervalsPreserved.of_run (targets := targets) (generatedTargetFrame_emitEffect none _)
      (show emitEffect (.replace addressed.1 captured.1 (some origin)) le captured.2 = published from rfl)
      cleared.2 captured.2 (.refl _) avoids (.refl _ _)
  refine ⟨addressedResult.1.trans (clearedExt.trans (capturedResult.1.trans publishedExt)), ?_⟩
  change ReplacementSitesBuilder (targets := targets) le published.2
  cases live : captured.2.cur with
  | none =>
    have same : published.2 = captured.2 := congrArg Prod.snd
      (emitEffect_none (.replace addressed.1 captured.1 (some origin)) le live)
    rw [same]
    exact capturedResult.2
  | some block =>
    apply capturedResult.2.emitReplacement (show emitEffect _ le captured.2 = ((), published.2) from rfl)
    intro selected capturedBody selectedCurrent selectedRow
    refine ⟨{
      site := {
      source := {
      sourceEnv := env
      results := results
      environment := rfl
      place := owner
      rhs := expr
      scope := scope
      start := start
      finish := finish
      output := output
      accepted := source
      initial := before
      finished := published.2
      site := {
        owner := addressed.1
        value := captured.1
        addressed := addressed.2
        cleared := cleared.2
        captured := captured.2
        addressRun := rfl
        clearRun := rfl
        rhsRun := rfl
        publishRun := rfl }
      owner_eq := rfl
      value_eq := rfl
      generated := generated
      live := by simp [live]
      extension := .refl _
      types := addressedTypes
      framed := publishedFrames }
      capturedBody := capturedBody
      current := selectedCurrent
      row := selectedRow
      position_eq := rfl }
      avoids := avoids }⟩

end Goose.Lower.Validation
