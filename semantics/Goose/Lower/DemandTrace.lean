import Goose.Lower.Lifetime

namespace Goose.Lower

open Goose.Core Goose.GIR

inductive DemandBoundary where
  | entry
  | exit
  deriving DecidableEq

structure DemandSourceLabel where
  path : List Nat
  phase : DemandPhase
  boundary : DemandBoundary

structure DemandPointMapEntry where
  target : Pt
  source : DemandSourceLabel

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

inductive DemandTraversal (cx : FnCtx) (invariant : DemandRuntimePoint → Prop) :
    Nat → Nat → DemandRuntimePoint → DemandRuntimePoint → Prop
  | done {point : DemandRuntimePoint} (fuel : Nat) (valid : invariant point) :
      DemandTraversal cx invariant 0 fuel point point
  | next {length fuel : Nat} {before middle after : DemandRuntimePoint}
      (valid : invariant before)
      (step : DemandLinearStep cx fuel before middle)
      (rest : DemandTraversal cx invariant length fuel middle after) :
      DemandTraversal cx invariant (length + 1) (fuel + 1) before after

theorem DemandTraversal.prefix_invariant {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length fuel : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandTraversal cx invariant length fuel before after)
    {taken : Nat} {reached : DemandRuntimePoint}
    (bounded : taken ≤ length) (steps : DemandLinearPrefix cx taken fuel before reached) :
    invariant reached := by
  induction traversal generalizing taken reached with
  | done fuel valid =>
    have zero : taken = 0 := by omega
    subst taken
    cases steps
    exact valid
  | next valid step rest induction =>
    cases steps with
    | zero => exact valid
    | next first tail =>
      have same := step.deterministic first
      cases same
      exact induction (by omega) tail

theorem DemandTraversal.fuel_bound {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length fuel : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandTraversal cx invariant length fuel before after) : length ≤ fuel := by
  induction traversal with
  | done => omega
  | next valid step rest induction => omega

theorem DemandTraversal.last_valid {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length fuel : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandTraversal cx invariant length fuel before after) : invariant after := by
  induction traversal with
  | done fuel valid => exact valid
  | next valid step rest induction => exact induction

theorem DemandTraversal.mono {cx : FnCtx} {first second : DemandRuntimePoint → Prop}
    {length fuel : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandTraversal cx first length fuel before after)
    (weaken : ∀ point, first point → second point) :
    DemandTraversal cx second length fuel before after := by
  induction traversal with
  | done fuel valid => exact .done fuel (weaken _ valid)
  | next valid step rest induction => exact .next (weaken _ valid) step induction

theorem DemandTraversal.append {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {firstLength secondLength fuel : Nat} {before middle after : DemandRuntimePoint}
    (first : DemandTraversal cx invariant firstLength fuel before middle)
    (second : DemandTraversal cx invariant secondLength (fuel - firstLength) middle after) :
    DemandTraversal cx invariant (firstLength + secondLength) fuel before after := by
  induction first with
  | done fuel valid => simpa only [Nat.zero_add, Nat.sub_zero] using second
  | next valid step rest induction =>
    have tail := induction (by simpa only [Nat.add_sub_add_right] using second)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      DemandTraversal.next valid step tail

theorem DemandTraversal.runAt {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length fuel : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandTraversal cx invariant length fuel before after) :
    GIR.runAt cx before.point before.frame fuel before.state =
      GIR.runAt cx after.point after.frame (fuel - length) after.state := by
  induction traversal with
  | done fuel valid => rfl
  | next valid step rest induction =>
    simpa only [Nat.add_sub_add_right] using step.runAt.trans induction

inductive DemandInstructionStop (cx : FnCtx) : Nat → DemandRuntimePoint → Stop → St → Prop
  | timeout (point : DemandRuntimePoint) : DemandInstructionStop cx 0 point .timeout point.state
  | definition {fuel : Nat} {point : DemandRuntimePoint} {id : ValueId} {op : Op} {stop : Stop} {after : St}
      (instruction : instAt cx.fn point.point = some (.def id op))
      (execution : execOp fuel cx point.frame op point.state = .stop stop after) :
      DemandInstructionStop cx (fuel + 1) point stop after
  | effect {fuel : Nat} {point : DemandRuntimePoint} {effect : Effect} {stop : Stop} {after : St}
      (instruction : instAt cx.fn point.point = some (.eff effect))
      (execution : execEff cx.fn point.frame effect point.state = .stop stop after) :
      DemandInstructionStop cx (fuel + 1) point stop after

theorem DemandInstructionStop.runAt {cx : FnCtx} {fuel : Nat} {point : DemandRuntimePoint}
    {stop : Stop} {after : St} (stopped : DemandInstructionStop cx fuel point stop after) :
    GIR.runAt cx point.point point.frame fuel point.state = .stop stop after := by
  cases stopped with
  | timeout => rfl
  | definition instruction execution =>
    simp only [GIR.runAt, instsAt_cons instruction, exec, bind_apply, execution]
  | effect instruction execution =>
    simp only [GIR.runAt, instsAt_cons instruction, exec, bind_apply, execution]

def DemandStoppedTraversal (cx : FnCtx) (invariant : DemandRuntimePoint → Prop)
    (length fuel : Nat) (before : DemandRuntimePoint) (stop : Stop) (after : St) : Prop :=
  ∃ checkpoint, DemandTraversal cx invariant length fuel before checkpoint ∧
    DemandInstructionStop cx (fuel - length) checkpoint stop after

theorem DemandStoppedTraversal.runAt {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length fuel : Nat} {before : DemandRuntimePoint} {stop : Stop} {after : St}
    (traversal : DemandStoppedTraversal cx invariant length fuel before stop after) :
    GIR.runAt cx before.point before.frame fuel before.state = .stop stop after := by
  obtain ⟨checkpoint, steps, stopped⟩ := traversal
  exact steps.runAt.trans stopped.runAt

inductive DemandUniformTraversal (cx : FnCtx) (invariant : DemandRuntimePoint → Prop) :
    Nat → DemandRuntimePoint → DemandRuntimePoint → Prop
  | done {point : DemandRuntimePoint} (valid : invariant point) :
      DemandUniformTraversal cx invariant 0 point point
  | next {length : Nat} {before middle after : DemandRuntimePoint}
      (valid : invariant before)
      (step : ∀ fuel, DemandLinearStep cx fuel before middle)
      (rest : DemandUniformTraversal cx invariant length middle after) :
      DemandUniformTraversal cx invariant (length + 1) before after

theorem DemandUniformTraversal.prefix_invariant {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandUniformTraversal cx invariant length before after)
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

theorem DemandUniformTraversal.atFuel {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandUniformTraversal cx invariant length before after)
    {fuel : Nat} (enough : length ≤ fuel) :
    DemandTraversal cx invariant length fuel before after := by
  induction traversal generalizing fuel with
  | done valid => exact .done fuel valid
  | next valid step rest induction =>
    cases fuel with
    | zero => omega
    | succ fuel => exact .next valid (step fuel) (induction (by omega))

def DemandFramePreserved (frontier : ValueId) (frame : GIR.Frame) (before after : St)
    (point : DemandRuntimePoint) : Prop :=
  Same frontier frame point.frame ∧ (point.state = before ∨ point.state = after)

theorem DemandUniformTraversal.last_valid {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {length : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandUniformTraversal cx invariant length before after) : invariant after := by
  induction traversal with
  | done valid => exact valid
  | next valid step rest induction => exact induction

theorem DemandUniformTraversal.mono {cx : FnCtx} {first second : DemandRuntimePoint → Prop}
    {length : Nat} {before after : DemandRuntimePoint}
    (traversal : DemandUniformTraversal cx first length before after)
    (weaken : ∀ point, first point → second point) :
    DemandUniformTraversal cx second length before after := by
  induction traversal with
  | done valid => exact .done (weaken _ valid)
  | next valid step rest induction => exact .next (weaken _ valid) step induction

theorem DemandUniformTraversal.append {cx : FnCtx} {invariant : DemandRuntimePoint → Prop}
    {firstLength secondLength : Nat} {before middle after : DemandRuntimePoint}
    (first : DemandUniformTraversal cx invariant firstLength before middle)
    (second : DemandUniformTraversal cx invariant secondLength middle after) :
    DemandUniformTraversal cx invariant (firstLength + secondLength) before after := by
  induction first with
  | done valid => simpa only [Nat.zero_add] using second
  | next valid step rest induction =>
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      DemandUniformTraversal.next valid step (induction second)

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
