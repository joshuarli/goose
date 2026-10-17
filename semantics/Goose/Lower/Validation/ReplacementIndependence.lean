import Goose.Lower.Validation.ReplacementClosure
import Goose.Lower.Validation.ReplacementMustScan

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure ReplacementInstApart (module : GIR.Module) (types : Array (Option VTy))
    (queries : ReplacementQueries) (owner : ValueId) (instruction : Inst) : Prop where
  sources : ∀ value ∈ emptyFactSourceOperands instruction, valRefLike types value = true →
    ReplacementApart queries owner (queries.value value)
  loaded : ∀ value ∈ ReplacementContentFlow.Model.loadedResults instruction,
    valRefLike types value = true → ReplacementApart queries owner (queries.value value)
  call : ∀ value fn args origin, instruction = .def value (.call fn args origin) →
    ReplacementApart queries owner (callDependencies module types queries fn args)

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
