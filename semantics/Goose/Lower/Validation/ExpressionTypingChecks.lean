import Goose.Lower.Validation.ExpressionTypingBlocks

namespace Goose.Lower.Validation.ExpressionTypingChecks

open Goose.Core Goose.GIR

def module : Core.Module :=
  { files := #["expression.goose"], types := #[], globals := #[], impls := #[],
    contexts := #[], entry := 0, origins := #[⟨0, 1, "expression"⟩] }

def env : Core.TEnv :=
  { mod := module, impl := none,
    vars := #[⟨"reference", .ref .mutable (.int .i64), .immutable, 0, 0⟩,
      ⟨"array", .arr (.int .i64) 4, .mutable, 0, 0⟩],
    visible := [0, 1], loops := 0, inExpr := false, scopes := [0],
    globalLimit := 0, initializing := none }

def initial : LS := ⟨#[⟨[], #[]⟩], #[], some 0, [0]⟩

def computedIndex : Expr := .bin .add (.lit .i64 1) (.lit .i64 1) 0

def element : Place := .elem (.of (.var 1)) computedIndex 0

def compoundBody : Core.Block :=
  .mk 1 [.expr (.bool true) 0] (some (.read (.var 0)))

theorem computed_element_source : Core.tyPlace env element 2 =
    .ok (⟨.int .i64, true, true⟩, 2) := by rfl

theorem compound_deref_source : Core.tyPlace env (.deref (.blockE compoundBody)) 2 =
    .ok (⟨.int .i64, true, true⟩, 2) := by rfl

theorem computed_element_typed :
    let (value, after) := lowerPlace element (lowerEnv module env.vars []) initial
    ∃ mu, after.vals[value]? = some (some (.data (.ref mu (.int .i64)))) := by
  obtain ⟨mu, _, typed⟩ := lowerPlace_static_typed element (by trivial)
    computed_element_source [] initial rfl
  exact ⟨mu, typed⟩

set_option maxHeartbeats 800000 in
theorem compound_deref_typed :
    let (value, after) := lowerPlace (.deref (.blockE compoundBody))
      (lowerEnv module env.vars []) initial
    ∃ mu, after.vals[value]? = some (some (.data (.ref mu (.int .i64)))) := by
  exact lowerPlace_deref_blockE_static_result_typed (env := env) (results := [])
    (before := initial) (by trivial)
    compound_deref_source rfl rfl

#print axioms lowerExpr_static_typed
#print axioms lowerPlace_static_live_typed
#print axioms lowerBlock_static_result_typed
#print axioms lowerPlace_deref_blockE_static_result_typed

end Goose.Lower.Validation.ExpressionTypingChecks
