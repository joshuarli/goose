import Goose.Lower.Validation.CfgSourceDominanceStatements

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def blockValues (want : Bool) (tail : Option Expr) (value : ValueId) : List ValueId :=
  if want || tail.isSome then [value] else []

@[simp] theorem blockValues_true (tail : Option Expr) : blockValues true tail = (fun value => [value]) := rfl

@[simp] theorem blockValues_some (want : Bool) (expr : Expr) : blockValues want (some expr) = (fun value => [value]) := by
  funext value
  simp [blockValues]

theorem ssa_block (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool)
    (scope : ScopeId) (statements : List Stmt) (tail : Option Expr)
    (statementsSource : SSARun loop [] (fun _ => []) (lowerStmts loop statements))
    (tailSource : SSARun loop [] (blockValues want tail) (lowerBlockValue want tail)) :
    SSARun loop (pre.map fun entry => entry.2.1) (blockValues want tail)
      (lowerBlock loop pre want (.mk scope statements tail)) := by
  refine (show SSARun loop (pre.map fun entry => entry.2.1) (fun _ => pre.map fun entry => entry.2.1)
    (emitEffect (.enter scope)) from by
      simpa only [Effect.uses, List.append_nil] using (ssa_emitEffect loop (.enter scope)).keep
        (pre.map fun entry => entry.2.1)).bind fun _ => ?_
  refine ssa_inScope scope
    (AdvB.bind (advB_initSlots _) fun _ => AdvB.bind (advB_lowerStmts loop statements) fun _ =>
      AdvB.bind (advB_lowerBlockValue want tail) fun _ => AdvB.bind (advB_emitEffect _) fun _ => AdvB.pure _) ?_
  refine (ssa_initSlots loop pre).bind fun _ => ?_
  refine statementsSource.bind fun _ => ?_
  refine tailSource.bind fun value => ?_
  refine (show SSARun loop (blockValues want tail value) (fun _ => blockValues want tail value)
    (emitEffect (.leave scope)) from by
      simpa only [Effect.uses, List.append_nil] using (ssa_emitEffect loop (.leave scope)).keep
        (blockValues want tail value)).bind fun _ => ?_
  exact SSARun.pure loop value (blockValues want tail value) (blockValues want tail) (fun _ member => member)

theorem ssa_stmts_cons (loop : Option LoopCtx) (stmt : Stmt) (rest : List Stmt)
    (source : LiveSSARun loop [] (fun _ => []) (lowerStmt loop stmt))
    (restSource : SSARun loop [] (fun _ => []) (lowerStmts loop rest)) :
    SSARun loop [] (fun _ => []) (lowerStmts loop (stmt :: rest)) := by
  intro env before result after run imports checked ready arguments
  cases current : before.cur with
  | none =>
    simp only [lowerStmts, bind_run, isLive_none current, Bool.false_eq_true, ↓reduceIte] at run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    exact ⟨imports, checked, .refl before, fun _ _ => rfl, fun _ frame => frame, arguments⟩
  | some block =>
    simp only [lowerStmts, bind_run, isLive_run current, ↓reduceIte] at run
    obtain ⟨middleImports, first⟩ := source env before _ _ rfl imports checked ready arguments
      (by simp [current])
    obtain ⟨nextImports, last⟩ := restSource env _ result after run middleImports
      first.checked (first.loop ready) first.available
    exact ⟨nextImports, first.trans last⟩

end Goose.Lower.Validation
