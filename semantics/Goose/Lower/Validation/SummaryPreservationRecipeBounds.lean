import Goose.Lower.Frag
import Goose.GIR.Effects
import Goose.Core.Sound.Invert

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def RecipeBounds (func : Func) (upper : Prov) (state : LS) : Prop :=
  ∀ recipe ∈ state.valueRootRecipes, recipe.1 < upper.vals.size ∧
    ∀ row ∈ func.roots.values.getD #[], row.1 = recipe.1 →
      row.2 ⊆ rootsAt upper.vals recipe.1 ∧ rootsAt upper.vals recipe.1 ⊆ row.2

theorem RecipeBounds.empty {func : Func} {upper : Prov} {state : LS}
    (empty : state.valueRootRecipes = #[]) : RecipeBounds func upper state := by
  intro recipe member
  simp [empty] at member

theorem RecipeBounds.frame {func : Func} {before after : LS} {upper next : Prov}
    (bound : RecipeBounds func upper before)
    (recipes : after.valueRootRecipes = before.valueRootRecipes)
    (size : upper.vals.size ≤ next.vals.size)
    (roots : ∀ recipe ∈ before.valueRootRecipes,
      rootsAt next.vals recipe.1 = rootsAt upper.vals recipe.1) :
    RecipeBounds func next after := by
  intro recipe member
  rw [recipes] at member
  obtain ⟨bounded, rows⟩ := bound recipe member
  refine ⟨Nat.lt_of_lt_of_le bounded size, ?_⟩
  intro row rowMember same
  rw [roots recipe member]
  exact rows row rowMember same

theorem RecipeBounds.same {func : Func} {before after : LS} {upper : Prov}
    (bound : RecipeBounds func upper before)
    (recipes : after.valueRootRecipes = before.valueRootRecipes) :
    RecipeBounds func upper after :=
  bound.frame recipes (Nat.le_refl _) (fun _ _ => rfl)

theorem RecipeBounds.prefix {func : Func} {before after : LS} {upper next : Prov}
    (bound : RecipeBounds func upper before)
    (recipes : after.valueRootRecipes = before.valueRootRecipes)
    (retained : ∀ value, value < upper.vals.size →
      rootsAt next.vals value = rootsAt upper.vals value)
    (size : upper.vals.size ≤ next.vals.size) :
    RecipeBounds func next after := by
  exact bound.frame recipes size (fun recipe member => retained recipe.1 (bound recipe member).1)

theorem RecipeBounds.valueRootSeeds {func : Func} {state : LS} {upper : Prov}
    (bound : RecipeBounds func upper state)
    (covered : ∀ row ∈ func.roots.values.getD #[],
      ∃ source, (row.1, source) ∈ state.valueRootRecipes) :
    ∀ value, rootsAt func.valueRootSeeds value ⊆ rootsAt upper.vals value := by
  intro value
  simp only [Func.valueRootSeeds, rootsAt, Array.getElem?_mapIdx]
  cases cell : (Array.replicate func.numValues ([] : List RootRef))[value]? with
  | none => simp
  | some initial =>
    simp only [Option.map_some, Option.getD_some]
    rw [← Array.foldl_toList]
    apply List.foldlRecOn (motive := fun roots => roots ⊆ rootsAt upper.vals value) _ _ (by simp)
    intro roots prior row member
    by_cases same : row.1 == value
    · rw [if_pos same]
      intro root rootMember
      rcases Goose.Core.Sound.unionRoots_mem _ _ _ rootMember with old | added
      · exact prior old
      have rowMember := Array.mem_toList_iff.mp member
      obtain ⟨source, recipe⟩ := covered row rowMember
      have equal : row.1 = value := by simpa using same
      subst value
      exact ((bound (row.1, source) recipe).2 row rowMember rfl).1 added
    · simpa only [same, Bool.false_eq_true, ite_false] using prior

theorem RecipeBounds.valueRoots {func : Func} {state : LS} {upper : Prov}
    (bound : RecipeBounds func upper state)
    (covered : ∀ row ∈ func.roots.values.getD #[],
      ∃ source, (row.1, source) ∈ state.valueRootRecipes) :
    ∀ row ∈ func.roots.values.getD #[], rootsAt upper.vals row.1 ⊆ row.2 := by
  intro row rowMember
  obtain ⟨source, recipe⟩ := covered row rowMember
  exact ((bound (row.1, source) recipe).2 row rowMember rfl).2

theorem recordValueRootSource_bound {value : ValueId} {source : ValueRootSource} {le : LEnv} {state : LS}
    (recorded : (recordValueRootSource value source le state).2.valueRootRecipes =
      state.valueRootRecipes.push (value, source)) : value < state.vals.size := by
  by_cases inside : value < state.vals.size
  · exact inside
  · exfalso
    have absent : state.vals[value]? = none := Array.getElem?_eq_none (Nat.le_of_not_gt inside)
    have unchanged : (recordValueRootSource value source le state).2.valueRootRecipes =
        state.valueRootRecipes := by
      simp [recordValueRootSource_run, absent]
    have sizes := congrArg Array.size (unchanged.symm.trans recorded)
    simp at sizes

theorem RecipeBounds.recordSourceWhen {func : Func} {state : LS} {upper : Prov}
    (bound : RecipeBounds func upper state) (value : ValueId) (source : ValueRootSource)
    (le : LEnv)
    (valueBound : (recordValueRootSource value source le state).2.valueRootRecipes =
      state.valueRootRecipes.push (value, source) → value < upper.vals.size)
    (rows : (recordValueRootSource value source le state).2.valueRootRecipes =
      state.valueRootRecipes.push (value, source) →
      ∀ row ∈ func.roots.values.getD #[], row.1 = value →
        row.2 ⊆ rootsAt upper.vals value ∧ rootsAt upper.vals value ⊆ row.2) :
    RecipeBounds func upper (recordValueRootSource value source le state).2 := by
  let reference := match state.vals[value]?.join with
    | some (.data type) => type.isRefLike
    | some (.view ..) => true
    | none => false
  change RecipeBounds func upper (if state.cur.isSome && reference then
    {state with valueRootRecipes := state.valueRootRecipes.push (value, source)} else state)
  by_cases active : (state.cur.isSome && reference) = true
  · rw [if_pos active]
    intro recipe member
    rcases Array.mem_push.mp member with old | equal
    · exact bound recipe old
    · subst recipe
      have recorded : (recordValueRootSource value source le state).2.valueRootRecipes =
          state.valueRootRecipes.push (value, source) := by
        change (if state.cur.isSome && reference then
          {state with valueRootRecipes := state.valueRootRecipes.push (value, source)} else state).valueRootRecipes = _
        rw [if_pos active]
      exact ⟨valueBound recorded, rows recorded⟩
  · rw [if_neg active]
    exact bound

theorem RecipeBounds.recordSource {func : Func} {state : LS} {upper : Prov}
    (bound : RecipeBounds func upper state) (value : ValueId) (source : ValueRootSource)
    (valueBound : value < upper.vals.size)
    (rows : ∀ row ∈ func.roots.values.getD #[], row.1 = value →
      row.2 ⊆ rootsAt upper.vals value ∧ rootsAt upper.vals value ⊆ row.2) (le : LEnv) :
    RecipeBounds func upper (recordValueRootSource value source le state).2 := by
  exact bound.recordSourceWhen value source le (fun _ => valueBound) (fun _ => rows)

theorem lowerValueRootRows_covered (env : PEnv) (table : SourceRootTable)
    (recipes : Array (ValueId × ValueRootSource)) :
    ∀ row ∈ (lowerValueRootRows env table recipes).getD #[],
      ∃ source, (row.1, source) ∈ recipes := by
  intro row member
  unfold lowerValueRootRows at member
  split at member
  · simp at member
  · simp only [Option.getD_some, Array.mem_map] at member
    obtain ⟨⟨value, source⟩, recipe, same⟩ := member
    cases same
    exact ⟨source, recipe⟩

end Goose.Lower.Validation.SummaryPreservation
