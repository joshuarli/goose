import Goose.Lower.DemandCallSliceRows
import Goose.Lower.DemandCallSliceControlCursor

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

structure SplitCallRetained where
  ordinary : RetainedSsaMap
  slots : List SliceSlotArgumentCell

def SplitCallRetained.Covers (map : SplitCallRetained) (required : RetainedSsaMap) : Prop :=
  (∀ cell ∈ required.values, cell ∈ map.ordinary.values ∨
    ∃ slot ∈ map.slots, (slot.value, slot.alias) = cell) ∧
  (∀ cell ∈ required.runs, cell ∈ map.ordinary.runs)

def SplitCallRetained.Admitted (map : SplitCallRetained) (profile : ArtifactProfile)
    (retained : List RetainedAlias) : Prop :=
  map.ordinary.Admitted profile retained ∧
    (profile = .shrink → ∀ cell ∈ map.slots, cell.alias ∈ retained)

def SplitCallRetained.Bounded (map : SplitCallRetained) (frontier : ValueId) : Prop :=
  map.ordinary.Bounded frontier ∧ ∀ cell ∈ map.slots, cell.value < frontier

def SplitCallRetained.Realizes (map : SplitCallRetained) (m : Core.Module) (world : World) (env : Env)
    (point : DemandRuntimePoint) : Prop :=
  map.ordinary.Realizes m world env point ∧ SliceSlotArgumentCells.Realizes map.slots m world env point

theorem SplitCallRetained.argumentCoverage {m : Core.Module} {access : AccessEnv} {function : Func} {le : LEnv}
    {root : DemandNode} {path : List Nat} {before : LS} {context : ContextId} {arguments : List Arg}
    {origin : OriginId} {index : Nat} {argument : Arg}
    {occurrence : GeneratedDemandOccurrence m function le root path (.expression (.call context arguments origin)) before}
    {argumentAt : arguments[index]? = some argument} {required map : RetainedSsaMap}
    (rows : GeneratedDemandRows m access occurrence required) (coverage : map.Covers required)
    {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell}
    (split : SplitCallArgumentRows access path 0 (arguments.take index)
      (lowerArgs (arguments.take index) le before).1 values slots) :
    ∃ retained, GeneratedDemandRows m access (.argument occurrence argumentAt)
        ⟨retained ++ required.values, required.runs⟩ ∧
      (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Covers
        ⟨retained ++ required.values, required.runs⟩ := by
  obtain ⟨retained, generated, _, _, exactRetained⟩ := rows.splitArgument (argumentAt := argumentAt) split
  refine ⟨retained, generated, ?_, ?_⟩
  · intro cell member
    rcases List.mem_append.mp member with prior | inherited
    · rcases exactRetained cell prior with inValues | ⟨slot, inSlots, same⟩
      · exact Or.inl (List.mem_append_left _ inValues)
      · exact Or.inr ⟨slot, inSlots, same⟩
    · exact Or.inl (List.mem_append_right _ (coverage.1 cell inherited))
  · exact coverage.2

theorem SplitCallRetained.byValAdmission {cfg : Cfg} {env : Env} {initial state : St}
    {context : ContextId} {arguments : List Arg} {origin : OriginId}
    (root : ExprSource cfg env (.call context arguments origin) initial)
    {index : Nat} {expression : Expr} (found : arguments[index]? = some (.byVal expression))
    (child : ExprSource cfg env expression state)
    (canonical : (ArgSource.byVal child).MatchesContext root.world root.typingEnv root.rootsEnv
      (callArgContext root.context index (.byVal expression) found))
    {map : RetainedSsaMap} (admitted : map.Admitted cfg.mod.profile root.context.retained)
    {values : List (ValueId × RetainedAlias)} {slots : List SliceSlotArgumentCell} {ids : List ValueId}
    (split : SplitCallArgumentRows root.rootsEnv.access root.path 0 (arguments.take index) ids values slots) :
    (⟨⟨values ++ map.values, map.runs⟩, slots⟩ : SplitCallRetained).Admitted cfg.mod.profile child.context.retained := by
  obtain ⟨retained, tracked, valueSubset, slotSubset, exactRetained⟩ := split.generatedRows
  have childAt := ArgSource.byVal_callChild root found child canonical
  constructor
  · intro shrink alias member
    simp only [RetainedSsaMap.values, RetainedSsaMap.runs, List.map_append, List.mem_append] at member
    rcases member with (prior | inherited) | inherited
    · obtain ⟨cell, present, same⟩ := List.mem_map.mp prior
      rw [← same]
      exact ArgSource.byVal_callRetainsPrior root found child canonical tracked shrink cell (valueSubset cell present)
    · exact childAt.retained alias (admitted shrink alias (List.mem_append_left _ inherited))
    · exact childAt.retained alias (admitted shrink alias (List.mem_append_right _ inherited))
  · intro shrink cell member
    exact ArgSource.byVal_callRetainsPrior root found child canonical tracked shrink
      (cell.value, cell.alias) (slotSubset cell member)

#print axioms SplitCallRetained.byValAdmission

theorem SplitCallRetained.bounded_mono {map : SplitCallRetained} {before after : ValueId}
    (bounded : map.Bounded before) (larger : before ≤ after) : map.Bounded after :=
  ⟨bounded.1.mono larger, fun cell member => Nat.lt_of_lt_of_le (bounded.2 cell member) larger⟩

#print axioms SplitCallRetained.argumentCoverage
#print axioms SplitCallRetained.bounded_mono
end Goose.Lower
