import Goose.Lower.Validation.ReplacementClosure
import Goose.Lower.Validation.ReplacementMustScan

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure ReplacementInstApart (module : GIR.Module) (types : Array (Option VTy))
    (queries : ReplacementQueries) (owner : ValueId) (instruction : Inst) : Prop where
  sources : ∀ value ∈ emptyFactSourceOperands instruction, valRefLike types value = true →
    ReplacementApart queries owner (queries.ownerDependencies value)
  loaded : ∀ value ∈ ReplacementContentFlow.Model.loadedResults instruction,
    valRefLike types value = true → ReplacementApart queries owner (queries.ownerDependencies value)
  call : ∀ value fn args origin, instruction = .def value (.call fn args origin) →
    ReplacementApart queries owner (callDependencies module types queries fn args)

theorem callDependencies_callRoots_subset {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {fn : FnId} {args : List ValueId} {roots : List RootRef}
    (known : callDependencies module types queries fn args = some roots) :
    ∃ called, queries.callRoots fn args = some called ∧ called ⊆ roots := by
  unfold callDependencies at known
  obtain ⟨arguments, _, remainder⟩ := Option.bind_eq_some_iff.mp known
  obtain ⟨called, calledAt, remainder⟩ := Option.bind_eq_some_iff.mp remainder
  obtain ⟨declared, _, result⟩ := Option.bind_eq_some_iff.mp remainder
  have rootsAt : unionRoots arguments (unionRoots called declared) = roots := Option.some.inj result
  refine ⟨called, calledAt, ?_⟩
  intro root member
  rw [← rootsAt]
  exact Core.Sound.unionRoots_right arguments (unionRoots called declared) root
    (Core.Sound.unionRoots_left called declared root member)

theorem callDependencies_within {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {fn : FnId} {args : List ValueId} {source : List RootRef}
    (arguments : ∀ argument ∈ args, valRefLike types argument = true →
      ReplacementRootsWithin (queries.ownerDependencies argument) source)
    (called : ReplacementRootsWithin (queries.callRoots fn args) source)
    (declared : ReplacementRootsWithin (callSummaryRoots module queries fn args) source) :
    ReplacementRootsWithin (callDependencies module types queries fn args) source := by
  let step := fun (roots : List RootRef) (argument : ValueId) => do
    if !valRefLike types argument then pure roots else
      let actual ← queries.ownerDependencies argument
      pure (unionRoots roots actual)
  have accumulate : ∀ inputs : List ValueId,
      (∀ argument ∈ inputs, valRefLike types argument = true →
        ReplacementRootsWithin (queries.ownerDependencies argument) source) →
      ∀ prior, prior ⊆ source → ReplacementRootsWithin (inputs.foldlM step prior) source := by
    intro inputs
    induction inputs with
    | nil => intro _ prior bounded; exact ⟨prior, rfl, bounded⟩
    | cons argument rest ih =>
      intro known prior bounded
      have tailKnown := fun next member => known next (List.mem_cons_of_mem argument member)
      by_cases reference : valRefLike types argument = true
      · obtain ⟨roots, found, included⟩ := known argument (by simp) reference
        have merged : unionRoots prior roots ⊆ source := by
          intro root member
          rcases Core.Sound.unionRoots_mem _ _ _ member with left | right
          · exact bounded left
          · exact included right
        simpa [List.foldlM_cons, step, reference, found] using ih tailKnown (unionRoots prior roots) merged
      · simpa [List.foldlM_cons, step, reference] using ih tailKnown prior bounded
  obtain ⟨argumentRoots, argumentAt, argumentBound⟩ := accumulate args arguments [] (by simp)
  obtain ⟨calledRoots, callAt, callBound⟩ := called
  obtain ⟨declaredRoots, declaredAt, declaredBound⟩ := declared
  refine ⟨unionRoots argumentRoots (unionRoots calledRoots declaredRoots), ?_, ?_⟩
  · change ((args.foldlM step []).bind fun roots => do
      let actual ← queries.callRoots fn args
      let touched ← callSummaryRoots module queries fn args
      pure (unionRoots roots (unionRoots actual touched))) = _
    rw [argumentAt]
    simp [callAt, declaredAt]
  · intro root member
    rcases Core.Sound.unionRoots_mem _ _ _ member with argument | dependency
    · exact argumentBound argument
    · rcases Core.Sound.unionRoots_mem _ _ _ dependency with actual | policy
      · exact callBound actual
      · exact declaredBound policy

theorem transferEmptyInst_retains_of_apart {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner : ValueId} {inst : Inst}
    (apart : ReplacementInstApart module types queries owner inst)
    {facts : List ValueId} (present : owner ∈ facts) :
    owner ∈ transferEmptyInst module types queries facts inst := by
  have initial : owner ∈ (match inst with
      | .eff (.clear r _) => if facts.contains r then facts else facts ++ [r]
      | .def _ (.call fn args _) => killEmptyFacts facts (callDependencies module types queries fn args) queries
      | _ => facts) := by
    cases inst with
    | «def» value op =>
      cases op <;> first
        | exact present
        | exact killEmptyFacts_retains present (apart.call _ _ _ _ rfl)
    | eff effect =>
      cases effect <;> dsimp only
      all_goals try exact present
      split
      · exact present
      · exact List.mem_append_left _ present
    | term term => exact present
  exact killEmptyFactSources_retains
    (killEmptyFactSources_retains initial apart.sources) apart.loaded

theorem transferEmptyBlock_retains_of_apart {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner : ValueId} {block : GIR.Block}
    (apart : ∀ inst ∈ block.insts, ReplacementInstApart module types queries owner inst)
    {facts : List ValueId} (present : owner ∈ facts) :
    owner ∈ transferEmptyBlock module types queries facts block := by
  unfold transferEmptyBlock
  apply List.foldlRecOn (motive := fun current => owner ∈ current)
  · exact present
  · intro current known inst member
    exact transferEmptyInst_retains_of_apart (apart inst member) known

end Goose.Lower.Validation
