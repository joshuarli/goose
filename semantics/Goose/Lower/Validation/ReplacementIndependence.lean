import Goose.Lower.Validation.ReplacementClosure
import Goose.Lower.Validation.ReplacementMustScan

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

inductive EmptyFactReceiver : ValueId → Inst → Prop
  | load (result owner) : EmptyFactReceiver owner (.def result (.load owner))
  | snapshot (result mode owner) : EmptyFactReceiver owner (.def result (.snapshot mode owner))
  | arrayLen (result owner) : EmptyFactReceiver owner (.def result (.arrayLen owner))
  | sliceView (result owner) : EmptyFactReceiver owner (.def result (.sliceView owner))
  | viewLen (result owner) : EmptyFactReceiver owner (.def result (.viewLen owner))
  | viewSlice (result mode owner lower upper origin) :
      EmptyFactReceiver owner (.def result (.viewSlice mode owner lower upper origin))
  | indexChecked (result owner index origin) : EmptyFactReceiver owner (.def result (.indexChecked owner index origin))
  | indexProven (result owner index) : EmptyFactReceiver owner (.def result (.indexProven owner index))
  | push (result owner value origin) : EmptyFactReceiver owner (.def result (.push owner value origin))
  | pop (result owner origin) : EmptyFactReceiver owner (.def result (.pop owner origin))
  | store (owner value origin) : EmptyFactReceiver owner (.eff (.store owner value origin))
  | append (owner value origin) : EmptyFactReceiver owner (.eff (.append owner value origin))
  | popN (owner count origin) : EmptyFactReceiver owner (.eff (.popN owner count origin))
  | resize (owner count value origin) : EmptyFactReceiver owner (.eff (.resize owner count value origin))
  | replace (owner value origin) : EmptyFactReceiver owner (.eff (.replace owner value origin))

structure ReplacementInstApart (module : GIR.Module) (types : Array (Option VTy))
    (queries : ReplacementQueries) (owner : ValueId) (instruction : Inst) : Prop where
  sources : ∀ value ∈ emptyFactSourceOperands instruction, valRefLike types value = true →
    ReplacementApart queries owner (queries.value value)
  result : ∀ value op, instruction = .def value op → valRefLike types value = true →
    ReplacementApart queries owner (queries.value value)
  receiver : ∀ value, EmptyFactReceiver value instruction → ReplacementApart queries owner (queries.value value)
  call : ∀ value fn args origin, instruction = .def value (.call fn args origin) →
    ReplacementApart queries owner (callDependencies module types queries fn args)

theorem transferEmptyInst_retains_of_apart {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner : ValueId} {inst : Inst}
    (apart : ReplacementInstApart module types queries owner inst)
    {facts : List ValueId} (present : owner ∈ facts) :
    owner ∈ transferEmptyInst module types queries facts inst := by
  have sources : ∀ current, owner ∈ current →
      owner ∈ killEmptyFactSources current (emptyFactSourceOperands inst) types queries :=
    fun _ known => killEmptyFactSources_retains known apart.sources
  cases inst with
  | «def» result op =>
    have finish : ∀ current, owner ∈ current → owner ∈
        (if valRefLike types result then
          killEmptyFacts (killEmptyFactSources current (emptyFactSourceOperands (.def result op)) types queries)
            (queries.value result) queries
        else killEmptyFactSources current (emptyFactSourceOperands (.def result op)) types queries) := by
      intro current known
      split
      · rename_i reference
        exact killEmptyFacts_retains (sources current known) (apart.result result op rfl reference)
      · exact sources current known
    cases op <;> dsimp only [transferEmptyInst]
    all_goals apply finish
    all_goals first
      | exact present
      | exact killEmptyFacts_retains present (apart.call _ _ _ _ rfl)
      | exact killEmptyFacts_retains present (apart.receiver _ (by constructor))
  | eff effect =>
    cases effect <;> dsimp only [transferEmptyInst]
    all_goals apply sources
    all_goals first
      | exact present
      | exact killEmptyFacts_retains present (apart.receiver _ (by constructor))
      | split
    all_goals first
      | exact present
      | exact List.mem_append_left _ present
  | term term => exact sources facts present

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
