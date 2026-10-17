import Goose.Lower.Validation.CfgUseDominance
import Goose.Lower.Validation.CfgPredecessors
import Goose.Lower.Validation.CfgReachability

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Evidence

def FuncEdgeArguments (func : Func) (types : Array (Option VTy))
    (target : BlockId) (arguments : List ValueId) : Prop :=
  ∃ body, func.blocks[target]? = some body ∧ body.params.length = arguments.length ∧
    ∀ pair ∈ body.params.zip arguments, types[pair.2]? = some (some pair.1.2)

def TermArguments (func : Func) (types : Array (Option VTy)) : Term → Prop
  | .br target arguments => FuncEdgeArguments func types target arguments
  | .condbr _ thenTarget thenArguments elseTarget elseArguments =>
    FuncEdgeArguments func types thenTarget thenArguments ∧
      FuncEdgeArguments func types elseTarget elseArguments
  | _ => True

structure CfgFacts (func : Func) (types : Array (Option VTy)) : Prop where
  terminators : ∀ block ∈ func.blocks.toList,
    block.terms.length = 1 ∧ block.lastTerm?.isSome = true
  arguments : ∀ block (bound : block < func.blocks.size) term,
    func.blocks[block].lastTerm? = some term → TermArguments func types term
  entry : NoEntryTargets func
  paths : ∀ block, block < func.blocks.size → BlockReachable func block
  uses : DominatingUses func

private theorem forIn_ok {items : List α} {body : α → PUnit → Check (ForInStep PUnit)}
    (accepted : ∀ item ∈ items, body item () = .ok (.yield ())) :
    forIn items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn_cons, accepted item (by simp)]
    simp only [bind, Except.bind]
    exact ih fun next member => accepted next (by simp [member])

private theorem forIn'_ok {items : List α}
    {body : (item : α) → item ∈ items → PUnit → Check (ForInStep PUnit)}
    (accepted : ∀ item member, body item member () = .ok (.yield ())) :
    forIn' items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn'_cons, accepted item (by simp)]
    simp only [bind, Except.bind]
    exact ih fun next member => accepted next (by simp [member])

private theorem loop_done {loop : Check PUnit} {value : α}
    (checked : loop = .ok ()) : (loop >>= fun _ => pure value) = .ok value := by
  simp [checked, bind, Except.bind, pure, Except.pure]

private theorem sequence {first : Check α} {next : α → Check β} {value : α} {result : β}
    (one : first = .ok value) (two : next value = .ok result) :
    (first >>= next) = .ok result := by rw [one]; exact two

private theorem all_ok {items : List α} {action : α → Check Unit}
    (accepted : ∀ item ∈ items, action item = .ok ()) : checkAll items action = .ok () := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [checkAll, accepted item (by simp), bind, Except.bind]
    exact ih fun next member => accepted next (by simp [member])

private theorem edge_checked {func : Func} {types : Array (Option VTy)}
    {target : BlockId} {arguments : List ValueId}
    (edge : FuncEdgeArguments func types target arguments) (label : String) (source : BlockId) :
    (do
      let some body := func.blocks[target]? |
        violation .v020 s!"{label}: block {source} branches outside the block table"
      unless body.params.length = arguments.length do
        violation .v020 s!"{label}: the branch from block {source} to block {target} passes {arguments.length} arguments for {body.params.length} parameters"
      for (param, argument) in body.params.zip arguments do
        unless types[argument]? == some (some param.2) do
          violation .v020 s!"{label}: argument %{argument} of the branch from block {source} to block {target} has another type than parameter %{param.1}") = .ok () := by
  obtain ⟨body, row, length, typed⟩ := edge
  simp only [row, length, ite_true, pure, Except.pure, bind, Except.bind]
  apply loop_done
  apply forIn_ok
  intro pair member
  rcases pair with ⟨param, argument⟩
  have type := typed (param, argument) member
  simp [type]

theorem cfgFacts_checked {func : Func} {types : Array (Option VTy)}
    (facts : CfgFacts func types) (label : String) : checkCfg label func types = .ok () := by
  unfold checkCfg
  have terms : (checkAll func.blocks.toList.zipIdx fun (block, index) => do
      unless block.terms.length = 1 do
        violation .v020 s!"{label}: block {index} has {block.terms.length} terminators, expected one"
      if block.lastTerm?.isNone then
        violation .v020 s!"{label}: block {index} does not end in its terminator") = .ok () := by
    apply all_ok
    intro pair member
    have shape := facts.terminators pair.1 (List.fst_mem_of_mem_zipIdx member)
    have last : pair.1.lastTerm?.isNone = false := by
      cases row : pair.1.lastTerm? <;> simp_all
    simp [shape.1, last, pure, Except.pure]
  rw [terms]
  simp only [bind, Except.bind]
  apply sequence (value := ())
  · rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
    apply forIn'_ok
    intro block member
    have bound : block < func.blocks.size := by
      simpa [Std.Legacy.Range.size, List.mem_range'] using member
    cases row : func.blocks[block].lastTerm? with
    | none => rfl
    | some term =>
      have arguments := facts.arguments block bound term row
      cases term <;> try rfl
      · exact sequence (edge_checked arguments label block) rfl
      · apply sequence (edge_checked arguments.1 label block)
        exact sequence (edge_checked arguments.2 label block) rfl
  · have entry := predecessors_entry func facts.entry
    simp only [entry, List.isEmpty_nil, ite_true, pure, Except.pure]
    apply sequence (value := ())
    · rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
      apply forIn'_ok
      intro block member
      have bound : block < func.blocks.size := by
        simpa [Std.Legacy.Range.size, List.mem_range'] using member
      have seen := reachable_complete func (Nat.zero_lt_of_lt bound) facts.paths block bound
      simp [seen]
    · exact dominatingUses_checked func facts.uses label

end Goose.Lower.Validation
