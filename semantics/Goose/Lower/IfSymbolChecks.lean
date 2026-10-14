import Goose.Lower.IfSymbols

namespace Goose.Lower.IfSymbolChecks

private def m : Core.Module :=
  { files := #["conditional.goose"], types := #[.int .i64], globals := #[],
    impls := #[], contexts := #[], entry := 0, origins := #[⟨0, 1, "abort"⟩] }

private def env : Core.TEnv :=
  { mod := m, impl := none, vars := #[], visible := [], loops := 0,
    inExpr := false, scopes := [], globalLimit := 0, initializing := none }

private def expr (t f : Bool) : Core.Expr :=
  .ifE (.bool true) (conditionalArm 0 t 0 7) (conditionalArm 1 f 0 9)

/-- All four syntactic arm combinations have a successful Core typing run,
including the aborting arms whose values are never produced at runtime. -/
theorem typed_arms (t f : Bool) : HasTypedExpr env (expr t f) := by
  cases t <;> cases f <;> exact ⟨0, .int .i64, 0, by rfl⟩

private def le : LEnv :=
  { mod := m, slots := #[], vars := #[], globals := #[], sigs := #[] }

private def start : LS :=
  { blocks := #[⟨[], #[]⟩], vals := #[], cur := some 0, stack := [] }

#guard (lowerExpr (expr false false) le start).2.cur.isSome
#guard (lowerExpr (expr false true) le start).2.cur.isSome
#guard (lowerExpr (expr true false) le start).2.cur.isSome
#guard !(lowerExpr (expr true true) le start).2.cur.isSome

/-- The concrete typed examples satisfy the invariant's premises; this is a
proof witness rather than an implication from an impossible builder state. -/
theorem conditional_run (t f : Bool) :
    HasTypedExpr env (expr t f) ∧
    LS.SymbolWF le 2 (lowerExpr (expr t f) le start).2 ∧
    LS.CurrentBlocks (lowerExpr (expr t f) le start).2 ∧
    (∀ r ∈ LS.valueRefs (fun v => [v]) (lowerExpr (expr t f) le start).1
      (lowerExpr (expr t f) le start).2,
      SymbolRef.Bound le (lowerExpr (expr t f) le start).2 r) := by
  have hw : LS.SymbolWF le 2 start := by
    constructor
    · change List.Perm [] []; exact .refl _
    · intro i hi; simp [LS.insts, start] at hi
  have hc : LS.CurrentBlocks start := by
    intro b hb
    simp [start] at hb
    subst b
    decide
  have h := lowerExpr_conditionalArms_symbolRunAt (le := le)
    (sc := 2) (scopeT := 0) (scopeF := 1) (org := 0)
    (by decide) (by decide) (by decide) true t f 7 9 start
  obtain ⟨_, hw', hc', _, refs⟩ := h hw hc _ _ rfl
  exact ⟨typed_arms t f, hw', hc', refs⟩

private def arithmetic : Core.Expr :=
  .bin .add (.lit .i64 3) (.lit .i64 4) 0

private theorem arithmetic_shape : V001Expr (Core.exprEnv env) arithmetic := by
  apply V001Expr.bin ⟨0, .int .i64, 0, by rfl⟩
  · exact V001Expr.lit ⟨0, .int .i64, 0, by rfl⟩
  · exact V001Expr.lit ⟨0, .int .i64, 0, by rfl⟩

private theorem arithmetic_arm (scope : Nat) (bound : scope < 2) :
    V001Block 2 (Core.exprEnv env) (.mk scope [] (some arithmetic)) := by
  exact .value ⟨0, .int .i64, 0, by rfl⟩ bound arithmetic_shape

theorem arithmetic_conditional_typed (condition : Bool) :
    HasTypedExpr env (.ifE (.bool condition) (.mk 0 [] (some arithmetic))
      (.mk 1 [] (some arithmetic))) := by
  exact ⟨0, .int .i64, 0, by rfl⟩

theorem typed_conditional_run (condition : Bool) (result : Goose.GIR.ValueId) (out : LS)
    (run : lowerExpr (.ifE (.bool condition) (.mk 0 [] (some arithmetic))
      (.mk 1 [] (some arithmetic))) le start = (result, out)) :
    LS.SymbolWF le 2 out ∧ LS.CurrentBlocks out := by
  have h := lowerExpr_ifE_v001_symbolRunAt (le := le) (env := env)
    (scopeCount := 2) (condition := .bool condition) (V001Expr.bool ⟨0, .bool, 0, by rfl⟩)
    (arithmetic_arm 0 (by decide)) (arithmetic_arm 1 (by decide))
    (by rfl) (by decide) (by rfl) start
  have hw : LS.SymbolWF le 2 start := by
    constructor
    · change List.Perm [] []; exact .refl _
    · intro i hi; simp [LS.insts, start] at hi
  have hc : LS.CurrentBlocks start := by
    intro b hb
    simp [start] at hb
    subst b
    decide
  obtain ⟨_, hw', hc', _, _⟩ := h hw hc result out run
  exact ⟨hw', hc'⟩

theorem undersized_scope_table :
    ¬ V001Block 1 (Core.exprEnv env) (.mk 1 [] (some arithmetic)) := by
  intro shape
  cases shape with
  | value typed scopeBound valueShape => omega

end Goose.Lower.IfSymbolChecks
