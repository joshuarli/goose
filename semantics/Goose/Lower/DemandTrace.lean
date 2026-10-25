import Goose.Lower.Lifetime

namespace Goose.Lower

open Goose.Core Goose.GIR

structure DemandRuntimePoint where
  point : Pt
  frame : GIR.Frame
  state : St

inductive DemandLinearStep (cx : FnCtx) (fuel : Nat) : DemandRuntimePoint → DemandRuntimePoint → Prop
  | definition {point : Pt} {frame : GIR.Frame} {state after : St} {id : ValueId} {op : Op} {value : RVal}
      (instruction : instAt cx.fn point = some (.def id op))
      (execution : execOp fuel cx frame op state = .ok value after) :
      DemandLinearStep cx fuel ⟨point, frame, state⟩
        ⟨(point.1, point.2 + 1), frame.set id value, after⟩
  | effect {point : Pt} {frame next : GIR.Frame} {state after : St} {effect : Effect}
      (instruction : instAt cx.fn point = some (.eff effect))
      (execution : execEff cx.fn frame effect state = .ok next after) :
      DemandLinearStep cx fuel ⟨point, frame, state⟩ ⟨(point.1, point.2 + 1), next, after⟩

theorem DemandLinearStep.deterministic {cx : FnCtx} {fuel : Nat} {before left right : DemandRuntimePoint}
    (first : DemandLinearStep cx fuel before left) (second : DemandLinearStep cx fuel before right) :
    left = right := by
  cases first with
  | definition instruction execution =>
    cases second with
    | definition instruction' execution' =>
      have same := instruction.symm.trans instruction'
      cases same
      have result := execution.symm.trans execution'
      cases result
      rfl
    | effect instruction' execution' =>
      have same := instruction.symm.trans instruction'
      cases same
  | effect instruction execution =>
    cases second with
    | definition instruction' execution' =>
      have same := instruction.symm.trans instruction'
      cases same
    | effect instruction' execution' =>
      have same := instruction.symm.trans instruction'
      cases same
      have result := execution.symm.trans execution'
      cases result
      rfl

theorem DemandLinearStep.runAt {cx : FnCtx} {fuel : Nat} {before after : DemandRuntimePoint}
    (step : DemandLinearStep cx fuel before after) :
    runAt cx before.point before.frame (fuel + 1) before.state =
      runAt cx after.point after.frame fuel after.state := by
  cases step with
  | definition instruction execution =>
    simp only [GIR.runAt, instsAt_cons instruction, exec, bind_apply, execution,
      setCell_eq, pure_apply]
  | effect instruction execution =>
    simp only [GIR.runAt, instsAt_cons instruction, exec, bind_apply, execution]

inductive DemandLinearPrefix (cx : FnCtx) : Nat → Nat → DemandRuntimePoint → DemandRuntimePoint → Prop
  | zero (fuel : Nat) (point : DemandRuntimePoint) : DemandLinearPrefix cx 0 fuel point point
  | next {length fuel : Nat} {before middle after : DemandRuntimePoint}
      (step : DemandLinearStep cx fuel before middle)
      (rest : DemandLinearPrefix cx length fuel middle after) :
      DemandLinearPrefix cx (length + 1) (fuel + 1) before after

theorem DemandLinearPrefix.fuel_bound {cx : FnCtx} {taken fuel : Nat}
    {before after : DemandRuntimePoint} (steps : DemandLinearPrefix cx taken fuel before after) :
    taken ≤ fuel := by
  induction steps with
  | zero => omega
  | next step rest induction => omega

theorem DemandLinearPrefix.runAt {cx : FnCtx} {taken fuel : Nat}
    {before after : DemandRuntimePoint} (steps : DemandLinearPrefix cx taken fuel before after) :
    GIR.runAt cx before.point before.frame fuel before.state =
      GIR.runAt cx after.point after.frame (fuel - taken) after.state := by
  induction steps with
  | zero => rfl
  | next step rest induction =>
    simpa only [Nat.add_sub_add_right] using step.runAt.trans induction

inductive DemandLinearTraversal (cx : FnCtx) (invariant : DemandRuntimePoint → Prop) :
    Nat → DemandRuntimePoint → DemandRuntimePoint → Prop
  | done {point : DemandRuntimePoint} (valid : invariant point) :
      DemandLinearTraversal cx invariant 0 point point
  | next {length : Nat} {before middle after : DemandRuntimePoint}
      (valid : invariant before)
      (step : ∀ fuel, DemandLinearStep cx fuel before middle)
      (rest : DemandLinearTraversal cx invariant length middle after) :
      DemandLinearTraversal cx invariant (length + 1) before after

theorem DemandLinearTraversal.prefix_invariant {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandLinearTraversal cx invariant length before after)
    {taken fuel : Nat} {reached : DemandRuntimePoint}
    (bounded : taken ≤ length) (tracePrefix : DemandLinearPrefix cx taken fuel before reached) :
    invariant reached := by
  induction traversal generalizing taken fuel reached with
  | done valid =>
    have zero : taken = 0 := by omega
    subst taken
    cases tracePrefix
    exact valid
  | next valid step rest induction =>
    cases tracePrefix with
    | zero => exact valid
    | next first tail =>
      have same := (step _).deterministic first
      cases same
      exact induction (by omega) tail

theorem DemandLinearTraversal.mono {cx : FnCtx} {first second : DemandRuntimePoint → Prop}
    {length : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandLinearTraversal cx first length before after)
    (weaken : ∀ point, first point → second point) :
    DemandLinearTraversal cx second length before after := by
  induction traversal with
  | done valid => exact .done (weaken _ valid)
  | next valid step rest induction => exact .next (weaken _ valid) step induction

theorem DemandLinearTraversal.append {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {firstLength secondLength : Nat} {before middle after : DemandRuntimePoint}
    (first : DemandLinearTraversal cx invariant firstLength before middle)
    (second : DemandLinearTraversal cx invariant secondLength middle after) :
    DemandLinearTraversal cx invariant (firstLength + secondLength) before after := by
  induction first with
  | done valid => simpa only [Nat.zero_add] using second
  | next valid step rest induction =>
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      DemandLinearTraversal.next valid step (induction second)

structure DemandFrameAt (cfg : Cfg) (env : Env) (cx : FnCtx)
    (world : Core.Sound.World) (typing : TEnv) (roots : PEnv) (future : List VarId)
    (values runs : List (ValueId × RetainedAlias)) (point : DemandRuntimePoint) : Prop where
  builder : ∃ state : LS, state.pp = some point.point ∧ Rel cfg env cx point.frame state
  source : Core.Sound.Frame cfg.mod world typing roots env point.state future
  operands : RetainedOperandsAt cfg.mod world env point.state.store point.frame values runs

theorem DemandFrameAt.demanded_slot {cfg : Cfg} {env : Env} {cx : FnCtx}
    {world : Core.Sound.World} {typing : TEnv} {roots : PEnv} {future : List VarId}
    {values runs : List (ValueId × RetainedAlias)} {point : DemandRuntimePoint}
    (valid : DemandFrameAt cfg env cx world typing roots future values runs point)
    {varId : VarId} (visible : varId ∈ typing.visible) (demanded : varId ∈ future) :
    ∃ value, (slotRoot cx.fn point.frame varId >>= fun root => readLoc ⟨root, []⟩)
      point.state = .ok value point.state := by
  obtain ⟨state, _, relation⟩ := valid.builder
  exact relation.demanded_slot_read valid.source visible demanded

theorem DemandFrameAt.run_read_safe {cfg : Cfg} {env : Env} {cx : FnCtx}
    {world : Core.Sound.World} {typing : TEnv} {roots : PEnv} {future : List VarId}
    {values runs : List (ValueId × RetainedAlias)} {point : DemandRuntimePoint}
    (valid : DemandFrameAt cfg env cx world typing roots future values runs point)
    {cell : ValueId × RetainedAlias} (member : cell ∈ runs) :
    ∃ values, (getView point.frame cell.1 >>= readRun) point.state = .ok values point.state :=
  (valid.operands.2 cell member).read_safe

end Goose.Lower
