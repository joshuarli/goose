import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem canonical_ifExpression_yes_child (le : LEnv) (initial : LS)
    (condition : Expr) (yes no : Core.Block)
    (live : (lowerExpr condition le initial).2.cur.isSome = true) :
    let lowered := lowerExpr condition le initial
    (Fragment.expression (.ifE condition yes no)).child? le initial 1 =
      some (.block none [] true yes,
        { (fork lowered.1 le lowered.2).2 with cur := some lowered.2.blocks.size }) := by
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
  simp [Fragment.child?, Fragment.children, branchChildren, current, fork_run, setCur_run]

theorem canonical_ifExpression_no_child (le : LEnv) (initial : LS)
    (condition : Expr) (yes no : Core.Block)
    (live : (lowerExpr condition le initial).2.cur.isSome = true) :
    let lowered := lowerExpr condition le initial
    let yesStart := { (fork lowered.1 le lowered.2).2 with cur := some lowered.2.blocks.size }
    (Fragment.expression (.ifE condition yes no)).child? le initial 2 =
      some (.block none [] true no,
        { (lowerBlock none [] true yes le yesStart).2 with cur := some (lowered.2.blocks.size + 1) }) := by
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
  simp [Fragment.child?, Fragment.children, branchChildren, current, fork_run, setCur_run]

theorem canonical_ifStatement_yes_child (le : LEnv) (initial : LS) (loop : Option LoopCtx)
    (condition : Expr) (yes : Core.Block) (no : Option Core.Block) (origin : OriginId)
    (live : (lowerExpr condition le initial).2.cur.isSome = true) :
    let lowered := lowerExpr condition le initial
    (Fragment.statement loop (.ifS condition yes no origin)).child? le initial 1 =
      some (.block loop [] false yes,
        { (fork lowered.1 le lowered.2).2 with cur := some lowered.2.blocks.size }) := by
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
  simp [Fragment.child?, Fragment.children, branchChildren, current, fork_run, setCur_run]

theorem canonical_ifStatement_no_child (le : LEnv) (initial : LS) (loop : Option LoopCtx)
    (condition : Expr) (yes no : Core.Block) (origin : OriginId)
    (live : (lowerExpr condition le initial).2.cur.isSome = true) :
    let lowered := lowerExpr condition le initial
    let yesStart := { (fork lowered.1 le lowered.2).2 with cur := some lowered.2.blocks.size }
    (Fragment.statement loop (.ifS condition yes (some no) origin)).child? le initial 2 =
      some (.block loop [] false no,
        { (lowerBlock loop [] false yes le yesStart).2 with cur := some (lowered.2.blocks.size + 1) }) := by
  obtain ⟨block, current⟩ := Option.isSome_iff_exists.mp live
  simp [Fragment.child?, Fragment.children, branchChildren, current, fork_run, setCur_run]

#print axioms canonical_ifExpression_yes_child
#print axioms canonical_ifExpression_no_child
#print axioms canonical_ifStatement_yes_child
#print axioms canonical_ifStatement_no_child

end Goose.Lower.Validation.SourceReplacementWriterLedger
