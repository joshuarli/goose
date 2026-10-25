import Goose.Construct.Eval

set_option Elab.async false

namespace Goose.Proofs.ConstructionInvocationReplay
open Goose.Construct

structure Invocation (α β : Type) where
  ordinal : Nat
  operand : α
  before : ExecutionState
  outcome : ExecutionStep β

def Invocation.path (parent : List Nat) (invocation : Invocation α β) : List Nat :=
  parent ++ [invocation.ordinal]

inductive OperandReplay (action : α → EvalM β) : Nat → List α → List β →
    ExecutionState → ExecutionStep (List β) → List (Invocation α β) → Prop
  | done (offset : Nat) (accumulator : List β) (state : ExecutionState) :
      OperandReplay action offset [] accumulator state (.ok accumulator.reverse state) []
  | next {offset : Nat} {operand : α} {rest : List α} {accumulator : List β}
      {before middle : ExecutionState} {value : β} {outcome : ExecutionStep (List β)}
      {visits : List (Invocation α β)}
      (head : action operand before = .ok value middle)
      (tail : OperandReplay action (offset + 1) rest (value :: accumulator) middle outcome visits) :
      OperandReplay action offset (operand :: rest) accumulator before outcome
        (⟨offset, operand, before, .ok value middle⟩ :: visits)
  | stopped {offset : Nat} {operand : α} {rest : List α} {accumulator : List β}
      {before after : ExecutionState} {reason : Goose.Core.Stop}
      (head : action operand before = .stop reason after) :
      OperandReplay action offset (operand :: rest) accumulator before (.stop reason after)
        [⟨offset, operand, before, .stop reason after⟩]
  | escaped {offset : Nat} {operand : α} {rest : List α} {accumulator : List β}
      {before after : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
      (head : action operand before = .escape address carriers after) :
      OperandReplay action offset (operand :: rest) accumulator before (.escape address carriers after)
        [⟨offset, operand, before, .escape address carriers after⟩]
  | jumped {offset : Nat} {operand : α} {rest : List α} {accumulator : List β}
      {before after : ExecutionState} {target : Nat} {kind : JumpKind}
      (head : action operand before = .jump target kind after) :
      OperandReplay action offset (operand :: rest) accumulator before (.jump target kind after)
        [⟨offset, operand, before, .jump target kind after⟩]

theorem derive (action : α → EvalM β) (offset : Nat) (operands : List α)
    (accumulator : List β) (before : ExecutionState) :
    ∃ visits, OperandReplay action offset operands accumulator before
      (List.mapM.loop action operands accumulator before) visits := by
  induction operands generalizing offset accumulator before with
  | nil => exact ⟨[], .done offset accumulator before⟩
  | cons operand rest ih =>
      rw [List.mapM.loop.eq_2]
      cases head : action operand before with
      | ok value middle =>
          simp only [bind, head]
          obtain ⟨visits, tail⟩ := ih (offset + 1) (value :: accumulator) middle
          exact ⟨_, .next head tail⟩
      | stop reason after =>
          simp only [bind, head]
          exact ⟨_, .stopped head⟩
      | escape address carriers after =>
          simp only [bind, head]
          exact ⟨_, .escaped head⟩
      | jump target kind after =>
          simp only [bind, head]
          exact ⟨_, .jumped head⟩

theorem OperandReplay.execute
    (replay : OperandReplay action offset operands accumulator before outcome visits) :
    List.mapM.loop action operands accumulator before = outcome := by
  induction replay with
  | done => rfl
  | next head tail ih => simp only [List.mapM.loop.eq_2, bind, head]; exact ih
  | stopped head => simp only [List.mapM.loop.eq_2, bind, head]
  | escaped head => simp only [List.mapM.loop.eq_2, bind, head]
  | jumped head => simp only [List.mapM.loop.eq_2, bind, head]

theorem OperandReplay.bound
    (replay : OperandReplay action offset operands accumulator before outcome visits) :
    visits.length ≤ operands.length := by
  induction replay <;> simp_all

theorem OperandReplay.ordinals
    (replay : OperandReplay action offset operands accumulator before outcome visits) :
    visits.map Invocation.ordinal = List.range' offset visits.length := by
  induction replay with
  | done => rfl
  | next head tail ih => simpa [List.range'_succ] using congrArg (offset :: ·) ih
  | stopped | escaped | jumped => simp [List.range'_succ]

theorem OperandReplay.sourceOrder
    (replay : OperandReplay action offset operands accumulator before outcome visits) :
    visits.map Invocation.operand = operands.take visits.length := by
  induction replay with
  | done => rfl
  | next head tail ih => simpa using ih
  | stopped | escaped | jumped => rfl

theorem OperandReplay.once
    (replay : OperandReplay action offset operands accumulator before outcome visits) :
    (visits.map Invocation.ordinal).Nodup := by
  rw [replay.ordinals]
  exact List.nodup_range'

theorem OperandReplay.noSkippedOccurrence
    {action : α → EvalM β} {visits : List (Invocation α β)}
    (replay : OperandReplay action offset operands accumulator before outcome visits)
    (visit : Invocation α β) (present : visit ∈ visits) :
    offset ≤ visit.ordinal ∧ visit.ordinal < offset + visits.length := by
  have member : visit.ordinal ∈ visits.map Invocation.ordinal := List.mem_map.mpr ⟨visit, present, rfl⟩
  rw [replay.ordinals] at member
  obtain ⟨index, bound, ordinal⟩ := List.mem_range'.mp member
  omega

theorem OperandReplay.exactSourcePrefix
    (replay : OperandReplay action offset operands accumulator before outcome visits) :
    ∃ suffix, operands = visits.map Invocation.operand ++ suffix := by
  refine ⟨operands.drop visits.length, ?_⟩
  rw [replay.sourceOrder]
  exact (List.take_append_drop visits.length operands).symm

theorem mapM_replay (action : α → EvalM β) (operands : List α) (before : ExecutionState) :
    ∃ visits, OperandReplay action 0 operands [] before ((operands.mapM action) before) visits :=
  derive action 0 operands [] before

theorem fixedArray_replay (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (ty : Ty) (operands : List Expr)
    (origin : Goose.Core.OriginId) (before : ExecutionState) (fixed : ty.nonfixed = false) :
    ∃ mapped visits,
      OperandReplay (evalValue fuel config environment) 0 operands [] before mapped visits ∧
      evalValue (fuel + 1) config environment (.arrLit ty operands origin) before =
        match mapped with
        | .ok values after => .ok (.fixed values.toArray) after
        | .stop reason after => .stop reason after
        | .escape address carriers after => .escape address carriers after
        | .jump target kind after => .jump target kind after := by
  obtain ⟨visits, replay⟩ := mapM_replay (evalValue fuel config environment) operands before
  refine ⟨_, visits, replay, ?_⟩
  simp only [evalValue]
  have notTrue : ¬ ty.nonfixed = true := by simp [fixed]
  rw [ite_eq_right notTrue]
  simp only [bind, pure]
  cases (operands.mapM (evalValue fuel config environment)) before <;> rfl

private def tick (_ : Nat) : EvalM Nat := fun state =>
  .ok state.nextAct { state with nextAct := state.nextAct + 1 }

example : OperandReplay tick 0 [7, 7] [] .initial
    (.ok [0, 1] { ExecutionState.initial with nextAct := 2 })
    [⟨0, 7, .initial, .ok 0 { ExecutionState.initial with nextAct := 1 }⟩,
     ⟨1, 7, { ExecutionState.initial with nextAct := 1 },
       .ok 1 { ExecutionState.initial with nextAct := 2 }⟩] :=
  .next rfl (.next rfl (.done 2 [1, 0] _))

example (before : ExecutionState) :
    OperandReplay (fun (_ : Nat) => (EvalM.stop (.fault .shape) : EvalM Nat))
      0 [7, 8] [] before (.stop (.fault .shape) before)
      [⟨0, 7, before, .stop (.fault .shape) before⟩] := .stopped rfl

example (before : ExecutionState) (address : ExitAddress) (carriers : List Carrier) :
    OperandReplay (fun (_ : Nat) _ => (ExecutionStep.escape address carriers before : ExecutionStep Nat))
      0 [7, 8] [] before (.escape address carriers before)
      [⟨0, 7, before, .escape address carriers before⟩] := .escaped rfl

example (before : ExecutionState) :
    OperandReplay (fun (_ : Nat) _ => (ExecutionStep.jump 3 .continueLoop before : ExecutionStep Nat))
      0 [7, 8] [] before (.jump 3 .continueLoop before)
      [⟨0, 7, before, .jump 3 .continueLoop before⟩] := .jumped rfl

example (first second : Invocation α β) (action : α → EvalM β)
    (operands : List α) (accumulator : List β) (before : ExecutionState)
    (outcome : ExecutionStep (List β)) (firstIndex : first.ordinal = 0)
    (repeated : second.ordinal = 0) :
    ¬ OperandReplay action 0 operands accumulator before outcome [first, second] := by
  intro replay
  have ordered := replay.ordinals
  simp [firstIndex, repeated, List.range'_succ] at ordered

example (first second : Invocation α β) (action : α → EvalM β)
    (operands : List α) (accumulator : List β) (before : ExecutionState)
    (outcome : ExecutionStep (List β)) (firstIndex : first.ordinal = 0)
    (skipped : second.ordinal = 2) :
    ¬ OperandReplay action 0 operands accumulator before outcome [first, second] := by
  intro replay
  have ordered := replay.ordinals
  simp [firstIndex, skipped, List.range'_succ] at ordered

example (first second : Invocation Nat Nat) (before : ExecutionState)
    (outcome : ExecutionStep (List Nat)) :
    ¬ OperandReplay (fun _ => (EvalM.stop (.fault .shape) : EvalM Nat))
      0 [7, 8] [] before outcome [first, second] := by
  intro replay
  cases replay with
  | next head tail => cases head

#print axioms derive
#print axioms OperandReplay.once
#print axioms fixedArray_replay

end Goose.Proofs.ConstructionInvocationReplay
