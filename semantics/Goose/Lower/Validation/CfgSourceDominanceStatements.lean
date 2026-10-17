import Goose.Lower.Validation.CfgSourceDominanceExpressions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ssa_pure_bind (value : α) (next : α → B β) :
    ((pure value : B α) >>= next) = next value := rfl

theorem ssa_letStmt (loop : Option LoopCtx) (slot : SlotId) (origin : OriginId) {expr : Expr}
    (source : SSARun loop [] (fun result => [result]) (lowerExpr expr)) :
    SSARun loop [] (fun _ => []) (lowerStmt loop (.letS slot expr origin)) := by
  exact source.bind fun value => (ssa_coerceSlot loop slot value origin).bind fun _ => ssa_emitEffect loop _

theorem ssa_assignStmt (loop : Option LoopCtx) (origin : OriginId) {place : Place} {expr : Expr}
    (placeSource : SSARun loop [] (fun result => [result]) (lowerPlace place))
    (exprSource : SSARun loop [] (fun result => [result]) (lowerExpr expr)) :
    SSARun loop [] (fun _ => []) (lowerStmt loop (.assign place expr origin)) := by
  exact placeSource.bind fun address => (exprSource.keep [address]).bind fun _ => ssa_emitEffect loop _

theorem ssa_assignOpStmt (loop : Option LoopCtx) (op : BinOp) (origin : OriginId) {place : Place} {expr : Expr}
    (placeSource : SSARun loop [] (fun result => [result]) (lowerPlace place))
    (exprSource : SSARun loop [] (fun result => [result]) (lowerExpr expr)) :
    SSARun loop [] (fun _ => []) (lowerStmt loop (.assignOp op place expr origin)) := by
  refine placeSource.bind fun address => ?_
  refine (((ssa_emitDef loop (.load address)).keep [address]).weaken (more := [address]) (by simp [Op.uses])).bind fun old => ?_
  refine (show SSARun loop [address, old] (fun rhs => [address, old, rhs]) (lowerExpr expr) from exprSource.keep [address, old]).bind fun rhs => ?_
  refine ((ssa_intTyOf loop old).keep [address, old, rhs]).bind fun type => ?_
  refine (((ssa_emitDef loop (.bin op type old rhs (some origin))).keep [address]).weaken
    (more := [address, old, rhs]) (by simp [Op.uses])).bind fun _ => ?_
  exact ssa_emitEffect loop _

theorem ssa_rebindStmt (loop : Option LoopCtx) (slot : SlotId) (origin : OriginId) {expr : Expr}
    (source : SSARun loop [] (fun result => [result]) (lowerExpr expr)) :
    SSARun loop [] (fun _ => []) (lowerStmt loop (.rebind slot expr origin)) := by
  refine source.bind fun value => ?_
  refine (ssa_coerceSlot loop slot value origin).bind fun coerced => ?_
  refine ((ssa_emitDef loop (.slotAddr slot)).keep [coerced]).bind fun address => ?_
  exact (ssa_emitEffect loop (.store address coerced (some origin))).weaken (by simp [Effect.uses, List.subset_def, or_comm])

theorem ssa_twoEffectStmt (loop : Option LoopCtx) (effect : ValueId → ValueId → Effect)
    {left right : B ValueId}
    (leftSource : SSARun loop [] (fun result => [result]) left)
    (rightSource : SSARun loop [] (fun result => [result]) right)
    (uses : ∀ a b, (effect a b).uses ⊆ [a, b]) :
    SSARun loop [] (fun _ => []) (do
      let a ← left
      let b ← right
      emitEffect (effect a b)) := by
  exact leftSource.bind fun a => (rightSource.keep [a]).bind fun b => (ssa_emitEffect loop _).weaken (uses a b)

theorem ssa_resizeStmt (loop : Option LoopCtx) (origin : OriginId) {place : Place} {size : Expr} {fill : Option Expr}
    (placeSource : SSARun loop [] (fun result => [result]) (lowerPlace place))
    (sizeSource : SSARun loop [] (fun result => [result]) (lowerExpr size))
    (fillSource : ∀ expr, fill = some expr → SSARun loop [] (fun result => [result]) (lowerExpr expr)) :
    SSARun loop [] (fun _ => []) (lowerStmt loop (.resize place size fill origin)) := by
  cases fill with
  | none =>
    simpa only [lowerStmt, ssa_pure_bind] using ssa_twoEffectStmt loop
      (fun address count => .resize address count none (some origin)) placeSource sizeSource (by simp [Effect.uses])
  | some expr =>
    simp only [lowerStmt, ssa_pure_bind]
    refine placeSource.bind fun address => ?_
    refine (sizeSource.keep [address]).bind fun count => ?_
    exact ((fillSource expr rfl).keep [address, count]).bind fun _ => ssa_emitEffect loop _

theorem ssa_assignWholeStmt (loop : Option LoopCtx) (origin : OriginId) {place : Place} {expr : Expr}
    (placeSource : SSARun loop [] (fun result => [result]) (lowerPlace place))
    (exprSource : SSARun loop [] (fun result => [result]) (lowerExpr expr)) :
    SSARun loop [] (fun _ => []) (lowerStmt loop (.assignWhole place expr origin)) := by
  refine placeSource.bind fun address => ?_
  refine (((ssa_emitEffect loop (.clear address (some origin))).keep [address]).weaken
    (more := [address]) (by simp [Effect.uses])).bind fun _ => ?_
  exact (exprSource.keep [address]).bind fun _ => ssa_emitEffect loop _

theorem ssa_returnStmt (loop : Option LoopCtx) (origin : OriginId) {expr : Option Expr}
    (source : ∀ value, expr = some value → SSARun loop [] (fun result => [result]) (lowerExpr value)) :
    SSARun loop [] (fun _ => []) (lowerStmt loop (.ret expr origin)) := by
  cases expr with
  | none =>
    simp only [lowerStmt, ssa_pure_bind]
    exact (ssa_leaveTo loop 0).bind fun _ => ssa_emitTerm loop (.ret [] (some origin))
      (by simp [Term.successors])
  | some expr =>
    simp only [lowerStmt, ssa_pure_bind]
    refine (source expr rfl).bind fun value => ?_
    refine (ssa_coerceResult loop value origin).bind fun result => ?_
    exact ((ssa_leaveTo loop 0).keep [result]).bind fun _ => ssa_emitTerm loop (.ret [result] (some origin))
      (by simp [Term.successors])

theorem ssa_breakStmt (loop : Option LoopCtx) (origin : OriginId) :
    SSARun loop [] (fun _ => []) (lowerStmt loop (.brk origin)) := by
  cases loop with
  | none => exact ssa_pure none ()
  | some context =>
    exact (ssa_leaveTo (some context) context.depth).bind fun _ =>
      ssa_emitTerm (some context) (.br context.breakTo []) (by simp [Term.successors, loopTargets])

theorem ssa_continueStmt (loop : Option LoopCtx) (origin : OriginId) :
    SSARun loop [] (fun _ => []) (lowerStmt loop (.cont origin)) := by
  cases loop with
  | none => exact ssa_pure none ()
  | some context =>
    rcases context with ⟨depth, exit, cont⟩
    refine (ssa_leaveTo (some ⟨depth, exit, cont⟩) depth).bind fun _ => ?_
    cases cont with
    | jump header =>
      exact ssa_emitTerm (some ⟨depth, exit, .jump header⟩) (.br header []) (by simp [Term.successors, loopTargets])
    | next header type counter =>
      have counterSource : SSARun (some ⟨depth, exit, .next header type counter⟩) [] (fun result => [result]) (pure counter) := by
        intro env before result after run imports checked ready _
        obtain ⟨rfl, rfl⟩ := pure_eq.mp run
        exact ⟨imports, checked, .refl before, fun _ _ => rfl, fun _ frame => frame,
          by simpa [loopValues] using ready.counters⟩
      have nextSource := counterSource.bind fun value => ssa_emitDef (some ⟨depth, exit, .next header type counter⟩) (.next type value)
      have nextSource : SSARun (some ⟨depth, exit, .next header type counter⟩) [] (fun result => [result]) (emitDef (.next type counter)) :=
        by simpa only [ssa_pure_bind] using nextSource
      exact nextSource.bind fun value => ssa_emitTerm (some ⟨depth, exit, .next header type counter⟩) (.br header [value])
        (by simp [Term.successors, loopTargets])

end Goose.Lower.Validation
