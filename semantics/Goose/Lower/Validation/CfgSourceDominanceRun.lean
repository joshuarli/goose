import Goose.Lower.Validation.CfgSourceDominanceBlocks
import Goose.Lower.Validation.CfgCurrentOpen

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def AvailableValues (state : LS) (imports : ImportedValues) (values : List ValueId) : Prop :=
  ∀ block, state.cur = some block → ∀ value ∈ values, BuilderAvailable state imports block value

theorem AvailableValues.subset {state : LS} {imports : ImportedValues} {before after : List ValueId}
    (available : AvailableValues state imports before) (subset : after ⊆ before) :
    AvailableValues state imports after := fun block current value member =>
  available block current value (subset member)

theorem AvailableValues.append {state : LS} {imports : ImportedValues} {left right : List ValueId}
    (one : AvailableValues state imports left) (two : AvailableValues state imports right) :
    AvailableValues state imports (left ++ right) := by
  intro block current value member
  rcases List.mem_append.mp member with member | member
  · exact one block current value member
  · exact two block current value member

def loopTargets : Option LoopCtx → List BlockId
  | none => []
  | some context => context.breakTo :: [match context.cont with
    | .jump header | .next header _ _ => header]

def loopValues : Option LoopCtx → List ValueId
  | some ⟨_, _, .next _ _ counter⟩ => [counter]
  | _ => []

structure LoopImportsReady (loop : Option LoopCtx) (state : LS) (imports : ImportedValues) : Prop where
  bounds : ∀ target ∈ loopTargets loop, target < state.blocks.size
  available : ∀ target ∈ loopTargets loop, AvailableValues state imports (imports target)
  counters : AvailableValues state imports (loopValues loop)

structure ImportedState (state : LS) (imports : ImportedValues) : Prop where
  certificate : BuilderImportedSSA state imports
  definitions : state.DenseDefinitions
  targets : TargetsBounded state
  opened : CurrentOpen state
  importsBounded : ∀ block, block < state.blocks.size →
    ∀ value ∈ imports block, value < state.vals.size

structure SSAResult (before after : LS) (beforeImports afterImports : ImportedValues)
    (values : List ValueId) : Prop where
  checked : ImportedState after afterImports
  advance : before.Adv after
  imports : ∀ block, block < before.blocks.size → afterImports block = beforeImports block
  frame : ∀ values, AvailableValues before beforeImports values → AvailableValues after afterImports values
  available : AvailableValues after afterImports values

theorem SSAResult.loop {before after : LS} {beforeImports afterImports : ImportedValues}
    {values : List ValueId} (result : SSAResult before after beforeImports afterImports values)
    {loop : Option LoopCtx} (ready : LoopImportsReady loop before beforeImports) :
    LoopImportsReady loop after afterImports := by
  refine ⟨?_, ?_, result.frame _ ready.counters⟩
  · intro target member
    exact Nat.lt_of_lt_of_le (ready.bounds target member) result.advance.ext.1
  · intro target member
    rw [result.imports target (ready.bounds target member)]
    exact result.frame _ (ready.available target member)

theorem SSAResult.trans {before middle after : LS} {beforeImports middleImports afterImports : ImportedValues}
    {firstValues lastValues : List ValueId}
    (one : SSAResult before middle beforeImports middleImports firstValues)
    (two : SSAResult middle after middleImports afterImports lastValues) :
    SSAResult before after beforeImports afterImports lastValues := by
  refine ⟨two.checked, one.advance.trans two.advance, ?_, ?_, two.available⟩
  · intro block bound
    exact (two.imports block (Nat.lt_of_lt_of_le bound one.advance.ext.1)).trans (one.imports block bound)
  · intro values available
    exact two.frame values (one.frame values available)

def SSARun (loop : Option LoopCtx) (inputs : List ValueId) (outputs : α → List ValueId)
    (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) →
    ∀ imports, ImportedState before imports → LoopImportsReady loop before imports →
      AvailableValues before imports inputs →
        ∃ nextImports, SSAResult before after imports nextImports (outputs result)

theorem SSARun.pure (loop : Option LoopCtx) (value : α) (inputs : List ValueId)
    (outputs : α → List ValueId) (available : outputs value ⊆ inputs) :
    SSARun loop inputs outputs (pure value) := by
  intro env before result after run imports checked _ arguments
  obtain ⟨rfl, rfl⟩ := pure_eq.mp run
  exact ⟨imports, checked, .refl before, fun _ _ => rfl, fun _ frame => frame,
    arguments.subset available⟩

theorem SSARun.unchanged (loop : Option LoopCtx) (action : B α)
    (same : ∀ env state, (action env state).2 = state) :
    SSARun loop [] (fun _ => []) action := by
  intro env before result after run imports checked _ arguments
  have equal := same env before
  rw [run] at equal
  change after = before at equal
  subst after
  exact ⟨imports, checked, .refl before, fun _ _ => rfl, fun _ frame => frame, arguments⟩

theorem SSARun.weaken {loop : Option LoopCtx} {inputs more : List ValueId}
    {outputs : α → List ValueId} {action : B α} (source : SSARun loop inputs outputs action)
    (subset : inputs ⊆ more) : SSARun loop more outputs action := by
  intro env before result after run imports checked ready arguments
  exact source env before result after run imports checked ready (arguments.subset subset)

theorem SSARun.keep {loop : Option LoopCtx} {inputs : List ValueId}
    {outputs : α → List ValueId} {action : B α} (source : SSARun loop inputs outputs action)
    (saved : List ValueId) : SSARun loop (saved ++ inputs) (fun result => saved ++ outputs result) action := by
  intro env before result after run imports checked ready arguments
  have inputValues := arguments.subset (List.subset_append_right saved inputs)
  obtain ⟨nextImports, preserved⟩ := source env before result after run imports checked ready inputValues
  refine ⟨nextImports, { preserved with available := ?_ }⟩
  apply AvailableValues.append
  · exact preserved.frame saved (arguments.subset (List.subset_append_left saved inputs))
  · exact preserved.available

theorem SSARun.bind {loop : Option LoopCtx} {inputs : List ValueId}
    {intermediate : α → List ValueId} {outputs : β → List ValueId}
    {first : B α} {next : α → B β} (one : SSARun loop inputs intermediate first)
    (two : ∀ value, SSARun loop (intermediate value) outputs (next value)) :
    SSARun loop inputs outputs (first >>= next) := by
  intro env before result after run imports checked ready arguments
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  obtain ⟨middleImports, one⟩ := one env before value middle firstRun imports checked ready arguments
  obtain ⟨nextImports, two⟩ := two value env middle result after nextRun middleImports
    one.checked (one.loop ready) one.available
  refine ⟨nextImports, two.checked, one.advance.trans two.advance, ?_, ?_, two.available⟩
  · intro block bound
    rw [two.imports block (Nat.lt_of_lt_of_le bound one.advance.ext.1), one.imports block bound]
  · intro values available
    exact two.frame values (one.frame values available)

theorem SSARun.congr_outputs {loop : Option LoopCtx} {inputs : List ValueId}
    {outputs nextOutputs : α → List ValueId} {action : B α}
    (source : SSARun loop inputs outputs action) (subset : ∀ value, nextOutputs value ⊆ outputs value) :
    SSARun loop inputs nextOutputs action := by
  intro env before result after run imports checked ready arguments
  obtain ⟨nextImports, preserved⟩ := source env before result after run imports checked ready arguments
  exact ⟨nextImports, { preserved with available := preserved.available.subset (subset result) }⟩

theorem SSARun.withLoop {inputs : List ValueId} {outputs : α → List ValueId} {action : B α}
    (source : SSARun none inputs outputs action) (loop : Option LoopCtx) :
    SSARun loop inputs outputs action := by
  intro env before result after run imports checked _ arguments
  exact source env before result after run imports checked
    ⟨by simp [loopTargets], by simp [loopTargets], by simp [AvailableValues, loopValues]⟩ arguments

theorem ImportedState.initState : ImportedState initState (fun _ => []) := by
  refine ⟨BuilderImportedSSA.initState, LS.denseDefinitions_initState, ?_, ?_, ?_⟩
  · intro block body row
    simp [Goose.Lower.initState] at row
  · exact currentOpen_none rfl
  · intro block bound
    simp [Goose.Lower.initState] at bound

end Goose.Lower.Validation
