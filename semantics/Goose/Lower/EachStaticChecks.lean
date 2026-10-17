import Goose.Lower.EachStatic
namespace Goose.Lower.EachStaticChecks
open Goose.Core Goose.GIR
private def reference : Expr :=
  .ifE (.bool true) (.mk 1 [] (some (.ref .mutable (.var 0))))
    (.mk 2 [] (some (.ref .mutable (.var 0))))
private def place : Place :=
  .elem (.val (.slice .mutable (.of (.deref reference)) .omitted .omitted 0)) (.lit .i64 0) 0
private def vars : Array LocalVar := #[⟨"owner", .grow (.int .i64), .immutable, 0, 0⟩]
private def main : Impl :=
  { name := "main", params := #[], results := #[], vars := vars,
    body := .mk 0 [.letS 0 (.arrLit (.grow (.int .i64)) [.lit .i64 0]) 0,
      .expr (.read place) 0] none, summary := .unknown }
private def module : Core.Module :=
  { files := #["borrow.goose"], types := #[], globals := #[], impls := #[main],
    contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "expr"⟩], profile := .shrink }
private def env : TEnv :=
  { mod := module, impl := some main, vars := vars,
    visible := [0], loops := 0, inExpr := false, scopes := [0],
    globalLimit := 0, initializing := none }
private def futureEdge : LS := ⟨#[⟨[], #[.term (.br 3 [0])]⟩], #[], some 0, [0]⟩
set_option maxHeartbeats 4000000 in
#guard (Core.validate module).isOk
#guard match tyPlace env place 1 with
  | .ok (info, _) => info.ty == .int .i64
  | _ => false
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
#guard let (address, after) := lowerPlace place (lowerEnv module env.vars []) futureEdge
  after.cur.isSome && after.vals[address]? == some (some (.data .unit))
private def legalEntry : LS := ⟨#[⟨[], #[]⟩], #[], some 0, [0]⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
#guard let (address, after) := lowerPlace place (lowerEnv module env.vars []) legalEntry
  after.cur.isSome && after.vals[address]? == some (some (.data (.ref .mutable (.int .i64))))

example : futureEdge.DenseDefinitions ∧ Validation.LiveBound futureEdge ∧
    ¬ GeneratedBuilderState futureEdge := by
  refine ⟨?_, ?_, ?_⟩
  · simp [futureEdge, LS.DenseDefinitions, LS.defs, BlockB.defs]
  · intro block current
    change some 0 = some block at current
    cases current
    decide
  · intro generated
    have invalid := generated.targets 0 ⟨[], #[.term (.br 3 [0])]⟩ rfl 3 (by decide)
    exact (by decide : ¬ 3 < 1) invalid

end Goose.Lower.EachStaticChecks
