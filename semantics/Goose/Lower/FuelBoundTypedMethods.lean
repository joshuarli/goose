import Goose.Lower.FuelBoundTyped

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

theorem TypedExprFuelBound.source_mono {sourceFuel larger fuel : Nat} {cfg : Cfg}
    {results : List Ty} {expression : Expr}
    (bounded : TypedExprFuelBound sourceFuel fuel cfg results expression)
    (enough : sourceFuel ≤ larger) : TypedExprFuelBound larger fuel cfg results expression := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact (bounded env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated).source_mono
    (fun n k bound => (monoAll n k bound).expr cfg env expression) enough

theorem TypedPlaceFuelBound.source_mono {sourceFuel larger fuel : Nat} {cfg : Cfg}
    {results : List Ty} {place : Place}
    (bounded : TypedPlaceFuelBound sourceFuel fuel cfg results place)
    (enough : sourceFuel ≤ larger) : TypedPlaceFuelBound larger fuel cfg results place := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact (bounded env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated).source_mono
    (fun n k bound => (monoAll n k bound).place cfg env place) enough

theorem TypedViewFuelBound.source_mono {sourceFuel larger fuel : Nat} {cfg : Cfg}
    {results : List Ty} {view : View}
    (bounded : TypedViewFuelBound sourceFuel fuel cfg results view)
    (enough : sourceFuel ≤ larger) : TypedViewFuelBound larger fuel cfg results view := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact (bounded env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated).source_mono
    (fun n k bound => (monoAll n k bound).view cfg env view) enough

theorem TypedBoundFuelBound.source_mono {sourceFuel larger fuel : Nat} {cfg : Cfg}
    {results : List Ty} {boundary : Bound}
    (bounded : TypedBoundFuelBound sourceFuel fuel cfg results boundary)
    (enough : sourceFuel ≤ larger) : TypedBoundFuelBound larger fuel cfg results boundary := by
  intro env state source metadata ls after id pt cx fr length default lowering point extension rel moduleEq resultsEq generated
  exact (bounded env state source metadata ls after id pt cx fr length default lowering point extension rel moduleEq resultsEq generated).source_mono
    (fun n k bound => (monoAll n k bound).bound cfg env length default boundary) enough

theorem TypedArgFuelBound.source_mono {sourceFuel larger fuel : Nat} {cfg : Cfg}
    {results : List Ty} {argument : Arg}
    (bounded : TypedArgFuelBound sourceFuel fuel cfg results argument)
    (enough : sourceFuel ≤ larger) : TypedArgFuelBound larger fuel cfg results argument := by
  intro env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact (bounded env state source metadata ls after id pt cx fr lowering point extension rel moduleEq resultsEq generated).source_mono
    (fun n k bound => (monoAll n k bound).arg cfg env argument) enough

theorem TypedArgsFuelBound.source_mono {sourceFuel larger fuel : Nat} {cfg : Cfg}
    {results : List Ty} {arguments : List Arg}
    (bounded : TypedArgsFuelBound sourceFuel fuel cfg results arguments)
    (enough : sourceFuel ≤ larger) : TypedArgsFuelBound larger fuel cfg results arguments := by
  intro env state source metadata ls after ids pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact (bounded env state source metadata ls after ids pt cx fr lowering point extension rel moduleEq resultsEq generated).source_mono
    (fun n k bound => MonoM.mapList (fun argument => (monoAll n k bound).arg cfg env argument) arguments) enough

theorem TypedExprsFuelBound.source_mono {sourceFuel larger fuel : Nat} {cfg : Cfg}
    {results : List Ty} {expressions : List Expr}
    (bounded : TypedExprsFuelBound sourceFuel fuel cfg results expressions)
    (enough : sourceFuel ≤ larger) : TypedExprsFuelBound larger fuel cfg results expressions := by
  intro env state source metadata ls after ids pt cx fr lowering point extension rel moduleEq resultsEq generated
  exact (bounded env state source metadata ls after ids pt cx fr lowering point extension rel moduleEq resultsEq generated).source_mono
    (fun n k bound => MonoM.mapList (fun expression => (monoAll n k bound).expr cfg env expression) expressions) enough

theorem TypedStatementFuelBound.source_mono {sourceFuel larger fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {statement : Stmt}
    (bounded : TypedStatementFuelBound sourceFuel fuel cfg results loop statement)
    (enough : sourceFuel ≤ larger) : TypedStatementFuelBound larger fuel cfg results loop statement := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq depth targets counter generated frames
  exact (bounded env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq depth targets counter generated frames).source_mono
    (fun n k bound => ((monoAll n k bound).stmt cfg env statement).bind (fun _ => MonoM.refl _)) enough

theorem TypedStatementsFuelBound.source_mono {sourceFuel larger fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {statements : List Stmt}
    (bounded : TypedStatementsFuelBound sourceFuel fuel cfg results loop statements)
    (enough : sourceFuel ≤ larger) : TypedStatementsFuelBound larger fuel cfg results loop statements := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq depth targets counter generated frames
  exact (bounded env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq depth targets counter generated frames).source_mono
    (fun n k bound => ((monoAll n k bound).stmts cfg env statements).bind (fun _ => MonoM.refl _)) enough

theorem TypedBlockFuelBound.source_mono {sourceFuel larger fuel : Nat} {cfg : Cfg}
    {results : List Ty} {loop : Option LoopCtx} {pre : List (SlotId × ValueId × OriginId)} {pre' : List (VarId × Val)} {want : Bool} {block : Core.Block}
    (bounded : TypedBlockFuelBound sourceFuel fuel cfg results loop pre pre' want block)
    (enough : sourceFuel ≤ larger) : TypedBlockFuelBound larger fuel cfg results loop pre pre' want block := by
  intro env state source metadata loops ls after result pt cx fr lowering point extension rel prerel moduleEq resultsEq depth targets counter generated frames
  exact (bounded env state source metadata loops ls after result pt cx fr lowering point extension rel prerel moduleEq resultsEq depth targets counter generated frames).source_mono
    (fun n k bound => ((monoAll n k bound).block cfg env pre' block).bind (fun _ => MonoM.refl _)) enough

theorem TypedWhileFuelBound.source_mono {sourceFuel larger fuel : Nat} {cfg : Cfg}
    {results : List Ty} {condition : Expr} {block : Core.Block} {origin : OriginId}
    (bounded : TypedWhileFuelBound sourceFuel fuel cfg results condition block origin)
    (enough : sourceFuel ≤ larger) : TypedWhileFuelBound larger fuel cfg results condition block origin := by
  intro env state source metadata ls after header cx fr lowering point extension parameters rel moduleEq resultsEq generated
  exact (bounded env state source metadata ls after header cx fr lowering point extension parameters rel moduleEq resultsEq generated).source_mono
    (fun n k bound => ((monoAll n k bound).while_ cfg env condition block).bind (fun _ => MonoM.refl _)) enough

theorem TypedRangeFuelBound.source_mono {sourceFuel larger fuel : Nat} {cfg : Cfg}
    {results : List Ty} {x : VarId} {lo hi : Expr} {block : Core.Block} {origin : OriginId}
    (bounded : TypedRangeFuelBound sourceFuel fuel cfg results x lo hi block origin)
    (enough : sourceFuel ≤ larger) : TypedRangeFuelBound larger fuel cfg results x lo hi block origin := by
  intro env initial source plan metadata cx header output counter upperBound hb hint upper base lowering point extension parameters ordered sized moduleEq resultsEq generated current frame state invariant loopState
  exact (bounded env initial source plan metadata cx header output counter upperBound hb hint upper base lowering point extension parameters ordered sized moduleEq resultsEq generated current frame state invariant loopState).source_mono
    (fun n k bound => ((monoAll n k bound).range cfg env x plan.intTy current upper block).bind (fun _ => MonoM.refl _)) enough

theorem TypedEachFuelBound.source_mono {sourceFuel larger fuel : Nat} {cfg : Cfg}
    {results : List Ty} {x : VarId} {idx : Option VarId} {view : View} {byRef : Bool} {block : Core.Block} {origin : OriginId}
    (bounded : TypedEachFuelBound sourceFuel fuel cfg results x idx view byRef block origin)
    (enough : sourceFuel ≤ larger) : TypedEachFuelBound larger fuel cfg results x idx view byRef block origin := by
  intro env initial source plan metadata cx header output counter irView sampled hb owner vw base lowering point extension parameters counterBound irViewBound ownerBound sampledBound moduleEq resultsEq generated index frame state invariant loopState
  exact (bounded env initial source plan metadata cx header output counter irView sampled hb owner vw base lowering point extension parameters counterBound irViewBound ownerBound sampledBound moduleEq resultsEq generated index frame state invariant loopState).source_mono
    (fun n k bound => ((monoAll n k bound).each cfg env x idx byRef block vw index).bind (fun _ => MonoM.refl _)) enough

end Goose.Lower
