import Goose.Lower.DemandShortCircuit
import Goose.Lower.LifetimeChecks

namespace Goose.Lower.DemandShortCircuitChecks

open Goose.Core Goose.GIR

private def opposite : ShortCircuitPath → ShortCircuitPath
  | .rhs => .skip
  | .skip => .rhs

theorem opposite_branch_rejected {isAnd : Bool} {condition : ValueId} {le : LEnv}
    {before forked : LS} {rhs join result : Nat} {point : Pt} {cx : FnCtx} {frame other : GIR.Frame}
    {state after : St} (path : ShortCircuitPath)
    (fork : scFork isAnd condition le before = ((rhs, join, result), forked))
    (atPoint : before.pp = some point) (extension : ExtT forked cx.fn.blocks)
    (cell : frame.vals[condition]? = some (.val (.bool (path.leftValue isAnd)))) (fuel : Nat) :
    ¬ DemandInstructionStep cx fuel ⟨point, frame, state⟩ ⟨(opposite path).target rhs join, other, after⟩ := by
  intro wrong
  have same := (shortCircuit_control_step path fork atPoint extension cell fuel).deterministic wrong
  have blocks := congrArg (fun runtime : DemandRuntimePoint => runtime.point.1) same
  obtain ⟨rhsFresh, joinFresh, _⟩ := scFork_facts fork atPoint extension
  have different : rhs ≠ join := by
    rw [rhsFresh, joinFresh]
    exact Nat.ne_of_lt (Nat.lt_succ_self _)
  cases path with
  | rhs => exact different blocks
  | skip => exact different blocks.symm

private def sourceModule : Core.Module :=
  { files := #[], types := #[], globals := #[], impls := #[], contexts := #[], entry := 0, origins := #[] }

private def before : LS :=
  { initState with blocks := #[⟨[], #[]⟩], vals := #[some (.data .bool), some (.view .readOnly (.int .i64))], cur := some 0 }

private def forked (isAnd : Bool) : (BlockId × BlockId × ValueId) × LS :=
  scFork isAnd 0 (lowerEnv sourceModule #[] []) before

private def function (isAnd : Bool) : Func :=
  { name := "control", params := [], results := [], slots := #[], scopes := #[],
    blocks := finishBlocks (forked isAnd).2.blocks, summary := .unknown, org := none }

private def branch (isAnd : Bool) : DemandBranch :=
  if isAnd then .conditional 0 (forked isAnd).1.1 [] (forked isAnd).1.2.1 [0]
  else .conditional 0 (forked isAnd).1.2.1 [0] (forked isAnd).1.1 []

private def initialFrame (isAnd : Bool) (path : ShortCircuitPath) : GIR.Frame :=
  ((⟨0, [], {}, 0⟩ : GIR.Frame).set 0 (.val (.bool (path.leftValue isAnd)))).set 1 (.view LifetimeChecks.sampledView)

#guard [false, true].all fun isAnd => [ShortCircuitPath.rhs, .skip].all fun path =>
  match (branch isAnd).enter (function isAnd) (initialFrame isAnd path)
      ⟨LifetimeChecks.clearedOwner, "", 0, 0⟩ with
  | .ok (target, _, next) after =>
    target == (path.target (forked isAnd).1.1 (forked isAnd).1.2.1).1 &&
    (match (getView next 1 >>= readRun) after with
      | .ok values _ => values.size == 1 && (match values[0]? with
        | some (Val.int IntTy.i64 9) => true
        | _ => false)
      | .stop _ _ => false) &&
    (match path, next.vals[(forked isAnd).1.2.2]? with
      | .rhs, none => true
      | .skip, some (.val (.bool value)) => value == !isAnd
      | _, _ => false)
  | .stop _ _ => false

end Goose.Lower.DemandShortCircuitChecks
