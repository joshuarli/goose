import Goose.Lower.Validation.ReplacementSourceSitesStatements

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReplacementSitesBuilder.emitReplacement {le : LEnv} {before after : LS}
    {owner value : ValueId} {origin : OriginId}
    (checked : ReplacementSitesBuilder le before)
    (run : Goose.Lower.emitEffect (.replace owner value (some origin)) le before = ((), after))
    (source : ∀ block body, before.cur = some block → before.blocks[block]? = some body →
      Nonempty (ReplacementSiteAt le after block body.insts.size owner value origin)) :
    ReplacementSitesBuilder le after := by
  have extension := (advB_emitEffect (.replace owner value (some origin)) le before () after run).ext
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
          exact (checked index previous oldRow position instruction lookup).retained extension types
    · simp only [same, ite_false] at row
      exact (checked block body row position instruction lookup).retained extension types

theorem replacementSites_assignWhole_source {env output : Core.TEnv} {results : List Ty}
    {owner : Place} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assignWhole owner expr origin) start = .ok (output, finish))
    (placeChild : ReplacementSitesPlaceChild env results owner)
    (exprChild : ReplacementSitesExprChild env results expr)
    (loop : Option LoopCtx) {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (lowerEnv env.mod env.vars results) before
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
  intro checked
  have addressedChecked := placeChild placeSource generated checked
  have clearedChecked : ReplacementSitesBuilder le cleared.2 :=
    addressedChecked.emitEffect (effect := .clear addressed.1 (some origin)) trivial rfl
  have capturedChecked := exprChild childSource clearedGenerated clearedChecked
  change ReplacementSitesBuilder le published.2
  cases live : captured.2.cur with
  | none =>
    have same : published.2 = captured.2 := congrArg Prod.snd
      (emitEffect_none (.replace addressed.1 captured.1 (some origin)) le live)
    rw [same]
    exact capturedChecked
  | some block =>
    apply capturedChecked.emitReplacement (show emitEffect _ le captured.2 = ((), published.2) from rfl)
    intro selected capturedBody selectedCurrent selectedRow
    refine ⟨{
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
      types := addressedTypes }
      capturedBody := capturedBody
      current := selectedCurrent
      row := selectedRow
      position_eq := rfl }⟩

end Goose.Lower.Validation
