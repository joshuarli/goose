import Goose.Lower.DemandCallSliceArgumentStage

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound
open Goose.Lower.Validation.ReplacementContentFlowSource

def OrdinaryCallArgument (access : AccessEnv) (argument : Arg) : Prop :=
  ¬ ∃ borrow slot mutability element, argument = .byRef borrow (.var slot) ∧
    access.placeType? (.var slot) = some (.slice mutability element)

inductive SplitCallArgumentRows (access : AccessEnv) (path : List Nat) :
    Nat → List Arg → List ValueId → List (ValueId × RetainedAlias) → List SliceSlotArgumentCell → Prop
  | nil (index : Nat) : SplitCallArgumentRows access path index [] [] [] []
  | value {index : Nat} {argument : Arg} {arguments : List Arg} {id : ValueId} {ids : List ValueId}
      {aliases : List RetainedAlias} {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell}
      (ordinary : OrdinaryCallArgument access argument)
      (query : access.aliasArg (path ++ [index]) argument = .ok aliases)
      (tail : SplitCallArgumentRows access path (index + 1) arguments ids values slots) :
      SplitCallArgumentRows access path index (argument :: arguments) (id :: ids)
        (aliases.map (fun alias => (id, alias)) ++ values) slots
  | slot {index : Nat} {arguments : List Arg} {ids : List ValueId}
      {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell} {cell : SliceSlotArgumentCell}
      (ordinal : cell.argument = index)
      (type : access.placeType? (.var cell.slot) = some (.slice cell.mutability cell.element))
      (query : access.aliasArg (path ++ [index]) (.byRef cell.borrow (.var cell.slot)) = .ok [cell.alias])
      (tail : SplitCallArgumentRows access path (index + 1) arguments ids values slots) :
      SplitCallArgumentRows access path index (.byRef cell.borrow (.var cell.slot) :: arguments) (cell.value :: ids)
        values (cell :: slots)

theorem SplitCallArgumentRows.length {access : AccessEnv} {path : List Nat} {index : Nat}
    {arguments : List Arg} {ids : List ValueId} {values : List (ValueId × RetainedAlias)}
    {slots : List SliceSlotArgumentCell} (rows : SplitCallArgumentRows access path index arguments ids values slots) :
    arguments.length = ids.length := by
  induction rows with
  | nil => rfl
  | value ordinary query tail ih => simp [ih]
  | slot ordinal type query tail ih => simp [ih]

theorem SplitCallArgumentRows.generatedRows {access : AccessEnv} {path : List Nat} {index : Nat}
    {arguments : List Arg} {ids : List ValueId} {values : List (ValueId × RetainedAlias)}
    {slots : List SliceSlotArgumentCell} (rows : SplitCallArgumentRows access path index arguments ids values slots) :
    ∃ retained, GeneratedCallArgumentRows access path index arguments ids retained ∧
      (∀ value ∈ values, value ∈ retained) ∧
      (∀ cell ∈ slots, (cell.value, cell.alias) ∈ retained) ∧
      (∀ value ∈ retained, value ∈ values ∨ ∃ cell ∈ slots, (cell.value, cell.alias) = value) := by
  induction rows with
  | nil index => exact ⟨[], .nil index, by simp, by simp, by simp⟩
  | @value index argument arguments id ids aliases values slots ordinary query tail ih =>
    obtain ⟨retained, tracked, valueSubset, slotSubset, exactRetained⟩ := ih
    refine ⟨aliases.map (fun alias => (id, alias)) ++ retained, .cons query tracked, ?_, ?_, ?_⟩
    · intro value member
      rcases List.mem_append.mp member with current | previous
      · exact List.mem_append_left _ current
      · exact List.mem_append_right _ (valueSubset value previous)
    · intro cell member
      exact List.mem_append_right _ (slotSubset cell member)
    · intro value member
      rcases List.mem_append.mp member with current | previous
      · exact Or.inl (List.mem_append_left _ current)
      · rcases exactRetained value previous with inValues | inSlots
        · exact Or.inl (List.mem_append_right _ inValues)
        · exact Or.inr inSlots
  | @slot index arguments ids values slots cell ordinal type query tail ih =>
    obtain ⟨retained, tracked, valueSubset, slotSubset, exactRetained⟩ := ih
    refine ⟨[(cell.value, cell.alias)] ++ retained, ?_, ?_, ?_, ?_⟩
    · simpa using (GeneratedCallArgumentRows.cons query tracked)
    · intro value member
      exact List.mem_append_right _ (valueSubset value member)
    · intro current member
      rcases List.mem_cons.mp member with same | previous
      · subst current
        exact List.mem_append_left _ (by simp)
      · exact List.mem_append_right _ (slotSubset current previous)
    · intro value member
      rcases List.mem_append.mp member with current | previous
      · simp only [List.mem_singleton] at current
        exact Or.inr ⟨cell, by simp, current.symm⟩
      · rcases exactRetained value previous with inValues | ⟨other, inSlots, equal⟩
        · exact Or.inl inValues
        · exact Or.inr ⟨other, by simp [inSlots], equal⟩

#print axioms SplitCallArgumentRows.generatedRows

theorem GeneratedDemandRows.splitArgument {m : Core.Module} {access : AccessEnv} {function : Func} {le : LEnv}
    {root : DemandNode} {path : List Nat} {before : LS} {context : ContextId} {arguments : List Arg}
    {origin : OriginId} {index : Nat} {argument : Arg}
    {occurrence : GeneratedDemandOccurrence m function le root path (.expression (.call context arguments origin)) before}
    {argumentAt : arguments[index]? = some argument} {required : RetainedSsaMap}
    (rows : GeneratedDemandRows m access occurrence required)
    {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell}
    (split : SplitCallArgumentRows access path 0 (arguments.take index)
      (lowerArgs (arguments.take index) le before).1 values slots) :
    ∃ retained, GeneratedDemandRows m access (.argument occurrence argumentAt)
        ⟨retained ++ required.values, required.runs⟩ ∧
      (∀ value ∈ values, value ∈ retained) ∧
      (∀ cell ∈ slots, (cell.value, cell.alias) ∈ retained) ∧
      (∀ value ∈ retained, value ∈ values ∨ ∃ cell ∈ slots, (cell.value, cell.alias) = value) := by
  obtain ⟨retained, tracked, valuesIncluded, slotsIncluded, exactRetained⟩ := split.generatedRows
  exact ⟨retained, .argument (argumentAt := argumentAt) rows tracked, valuesIncluded, slotsIncluded, exactRetained⟩

#print axioms GeneratedDemandRows.splitArgument

theorem SplitCallArgumentRows.snocSlot {access : AccessEnv} {path : List Nat} {index : Nat}
    {arguments : List Arg} {ids : List ValueId} {values : List (ValueId × RetainedAlias)}
    {slots : List SliceSlotArgumentCell} (rows : SplitCallArgumentRows access path index arguments ids values slots)
    {cell : SliceSlotArgumentCell} (ordinal : cell.argument = index + arguments.length)
    (type : access.placeType? (.var cell.slot) = some (.slice cell.mutability cell.element))
    (query : access.aliasArg (path ++ [cell.argument]) (.byRef cell.borrow (.var cell.slot)) = .ok [cell.alias]) :
    SplitCallArgumentRows access path index (arguments ++ [.byRef cell.borrow (.var cell.slot)])
      (ids ++ [cell.value]) values (slots ++ [cell]) := by
  induction rows with
  | nil index =>
    have ordinal' : cell.argument = index := by simpa using ordinal
    have query' : access.aliasArg (path ++ [index]) (.byRef cell.borrow (.var cell.slot)) = .ok [cell.alias] := by
      simpa only [← ordinal'] using query
    simpa using (SplitCallArgumentRows.slot ordinal' type query' (SplitCallArgumentRows.nil (index + 1)))
  | @value index argument arguments id ids aliases values slots ordinary queryHead tail ih =>
    have nextOrdinal : cell.argument = (index + 1) + arguments.length := by
      simp only [List.length_cons] at ordinal
      omega
    have next := ih nextOrdinal
    simpa only [List.cons_append] using (SplitCallArgumentRows.value ordinary queryHead next)
  | @slot index arguments ids values slots head headOrdinal headType queryHead tail ih =>
    have nextOrdinal : cell.argument = (index + 1) + arguments.length := by
      simp only [List.length_cons] at ordinal
      omega
    have next := ih nextOrdinal
    simpa only [List.cons_append] using (SplitCallArgumentRows.slot headOrdinal headType queryHead next)

theorem SplitCallArgumentRows.snocCheckedSlot {cfg : Cfg} {env : Env} {initial : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    {source : ExprSource cfg env (.call context arguments origin) initial}
    {index offset : Nat} {prior : List Arg} {ids : List ValueId} {values : List (ValueId × RetainedAlias)}
    {slots : List SliceSlotArgumentCell}
    (rows : SplitCallArgumentRows source.rootsEnv.access source.path index prior ids values slots)
    {cell : SliceSlotArgumentCell} {frame : GIR.Frame} (checked : cell.Checked source offset frame)
    (ordinal : cell.argument = index + prior.length) :
    SplitCallArgumentRows source.rootsEnv.access source.path index (prior ++ [.byRef cell.borrow (.var cell.slot)])
      (ids ++ [cell.value]) values (slots ++ [cell]) := by
  have query := SliceSlotArgumentCell.query checked
  obtain ⟨found, priorAt, visible, variableAt, scope, variableType, annotation, aliasType, aliasSource, valueAt⟩ := checked
  have accessVariable : source.rootsEnv.impl.vars[cell.slot]? = some cell.descriptor := by
    rw [source.frame.vars_p]
    exact variableAt
  have type : source.rootsEnv.access.placeType? (.var cell.slot) = some (.slice cell.mutability cell.element) := by
    simp [AccessEnv.placeType?, PEnv.access, accessVariable, variableType]
  exact rows.snocSlot ordinal type query


theorem accepted_generated_call_slice_argument_rows {cfg : Cfg} {env : Env} {initialState state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (source : ExprSource cfg env (.call context arguments origin) initialState)
    {index : Nat} {borrow : Mutability} {slot : VarId}
    (found : arguments[index]? = some (.byRef borrow (.var slot)))
    (child : PlaceSource cfg env (.var slot) state)
    (target : child.ty.refTarget = true ∨ (child.ty.isSlice = true ∧ child.mutable = true ∧ (Place.var slot).sliceArg = true))
    (canonical : (ArgSource.byRef borrow child target).MatchesContext source.world source.typingEnv source.rootsEnv
      (callArgContext source.context index (.byRef borrow (.var slot)) found))
    {mutability : Mutability} {element : Ty} (type : child.ty = .slice mutability element)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.call context arguments origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {prior : List (ValueId × RetainedAlias)}
    (tracked : GeneratedCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 prior)
    {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell}
    (split : SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take index)
      (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).1 values slots)
    {initial : GIR.Frame} {start : Pt}
    (atPoint : (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2.pp = some start)
    (related : Rel cfg env cx initial (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2)
    (extended : ExtT (lowerExpr (.call context arguments origin) (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (location : Loc) (length : Nat) (point : Pt) (frame : GIR.Frame) (cell : SliceSlotArgumentCell),
      let stage := (lowerArgs (arguments.take index) (lowerEnv cfg.mod env.vars results) before).2
      let id := (lowerArg (.byRef borrow (.var slot)) (lowerEnv cfg.mod env.vars results) stage).1
      evalArg 2 cfg env (.byRef borrow (.var slot)) state = .ok (.ref location) state ∧
      DemandRuntimePrefix cx length ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      Post cfg env cx stage initial (lowerArg (.byRef borrow (.var slot)) (lowerEnv cfg.mod env.vars results) stage).2
        frame point [(id, .val (.ref location))] ∧
      cell.value = id ∧ cell.argument = index ∧ cell.Checked source (index + 1) frame ∧
      SliceSlotAliasAt cfg.mod source.world env state.store frame id cell.alias mutability element ∧
      SplitCallArgumentRows source.rootsEnv.access source.path 0 (arguments.take (index + 1))
        (lowerArgs (arguments.take (index + 1)) (lowerEnv cfg.mod env.vars results) before).1 values (slots ++ [cell]) := by
  obtain ⟨location, length, point, frame, cell, evaluated, executed, post, cellValue, cellIndex, checked, alias⟩ :=
    accepted_generated_call_slice_argument source found child target canonical type occurrence rows tracked atPoint related extended
  have bound : index < arguments.length := (List.getElem?_eq_some_iff.mp found).1
  have ordinal : cell.argument = 0 + (arguments.take index).length := by
    simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)] using cellIndex
  have next := split.snocCheckedSlot checked ordinal
  have takeEq : arguments.take (index + 1) = arguments.take index ++ [.byRef borrow (.var slot)] := by
    rw [List.take_add_one, found]
    simp
  have sameArgument : Arg.byRef cell.borrow (.var cell.slot) = Arg.byRef borrow (.var slot) := by
    have checkedFound := checked.1
    rw [cellIndex, found] at checkedFound
    exact Option.some.inj checkedFound.symm
  refine ⟨location, length, point, frame, cell, evaluated, executed, post, cellValue, cellIndex, checked, alias, ?_⟩
  rw [takeEq, lowerArgs_append_run]
  simpa [lowerArgs, bind_run, pure_run, sameArgument, cellValue] using next

#print axioms accepted_generated_call_slice_argument_rows

#print axioms SplitCallArgumentRows.snocCheckedSlot

#print axioms SplitCallArgumentRows.snocSlot
#print axioms SplitCallArgumentRows.length
end Goose.Lower
