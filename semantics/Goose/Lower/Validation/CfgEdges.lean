import Goose.Lower.Validation.CfgTerminators

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EdgeArguments (state : LS) (target : BlockId) (arguments : List ValueId) : Prop :=
  ∃ block, state.blocks[target]? = some block ∧
    block.params.length = arguments.length ∧
    ∀ pair ∈ block.params.zip arguments, state.vals[pair.2]? = some (some pair.1.2)

theorem edgeArguments_of_ext {before after : LS} (extension : before.Ext after)
    (types : ∀ (value : ValueId) (ty : VTy), before.vals[value]? = some (some ty) →
      after.vals[value]? = some (some ty))
    {target : BlockId} {arguments : List ValueId} (edge : EdgeArguments before target arguments) :
    EdgeArguments after target arguments := by
  obtain ⟨block, row, arity, typed⟩ := edge
  obtain ⟨next, rowNext, params, _⟩ := extension.2 target block row
  refine ⟨next, rowNext, params ▸ arity, ?_⟩
  intro pair member
  rw [params] at member
  exact types _ _ (typed pair member)

theorem edgeArguments_newBlock0 (env : LEnv) (state : LS) :
    EdgeArguments (newBlock [] env state).2 state.blocks.size [] := by
  rw [newBlock0_run]
  exact ⟨⟨[], #[]⟩, by simp, rfl, by simp⟩

theorem edgeArguments_newBlock1 {state : LS} {value : ValueId} {ty : VTy}
    (typed : state.vals[value]? = some (some ty)) (env : LEnv) :
    EdgeArguments (newBlock [ty] env state).2 state.blocks.size [value] := by
  rw [newBlock1_run]
  refine ⟨⟨[(state.vals.size, ty)], #[]⟩, by simp, rfl, ?_⟩
  intro pair member
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at member
  subst pair
  have bound : value < state.vals.size := (Array.getElem?_eq_some_iff.mp typed).1
  simp [Array.getElem?_push, Nat.ne_of_lt bound, typed]

private theorem cfg_forIn_ok (items : List α) (action : α → Check (ForInStep PUnit))
    (checked : ∀ item ∈ items, action item = .ok (.yield PUnit.unit)) :
    (forIn items PUnit.unit (fun item _ => action item) >>= fun _ => pure () : Check Unit) = .ok () := by
  have loop : forIn items PUnit.unit (fun item _ => action item) = .ok PUnit.unit := by
    induction items with
    | nil => rfl
    | cons item rest ih =>
      simp only [List.forIn_cons, checked item (by simp), bind, Except.bind]
      exact ih fun next member => checked next (by simp [member])
  simp [loop, bind, Except.bind, pure, Except.pure]

theorem edgeArguments_checked {state : LS} {target : BlockId} {arguments : List ValueId}
    (edge : EdgeArguments state target arguments) (label : String) (source : BlockId) :
    (do
      let some block := state.blocks[target]? |
        violation .v020 s!"{label}: block {source} branches outside the block table"
      unless block.params.length = arguments.length do
        violation .v020 s!"{label}: the branch from block {source} to block {target} passes {arguments.length} arguments for {block.params.length} parameters"
      for (parameter, argument) in block.params.zip arguments do
        unless state.vals[argument]? == some (some parameter.2) do
          violation .v020 s!"{label}: argument %{argument} of the branch from block {source} to block {target} has another type than parameter %{parameter.1}"
      : Check Unit) = .ok () := by
  obtain ⟨block, row, arity, typed⟩ := edge
  simp only [row, arity, ite_true]
  apply cfg_forIn_ok
  intro pair member
  simp [typed pair member, pure, Except.pure]

theorem edgeArguments_patchTerm {state : LS} {target block : BlockId} {arguments : List ValueId}
    (edge : EdgeArguments state target arguments) (term : Term) (env : LEnv) :
    EdgeArguments (patchTerm block term env state).2 target arguments := by
  rw [patchTerm_run]
  exact edgeArguments_of_ext ((LS.Ext.refl state).modify (appends_push _) block)
    (fun _ _ typed => typed) edge

theorem edgeArguments_patchBrs (env : LEnv) (target : BlockId) (incoming : List (BlockId × ValueId))
    (state : LS) {destination : BlockId} {arguments : List ValueId}
    (edge : EdgeArguments state destination arguments) :
    EdgeArguments (patchBrs target incoming env state).2 destination arguments := by
  induction incoming generalizing state with
  | nil => exact edge
  | cons pair rest ih =>
    simp only [patchBrs, bind_run]
    exact ih _ (edgeArguments_patchTerm edge _ env)

theorem edgeArguments_patchBrs0 (env : LEnv) (target : BlockId) (incoming : List BlockId)
    (state : LS) {destination : BlockId} {arguments : List ValueId}
    (edge : EdgeArguments state destination arguments) :
    EdgeArguments (patchBrs0 target incoming env state).2 destination arguments := by
  induction incoming generalizing state with
  | nil => exact edge
  | cons block rest ih =>
    simp only [patchBrs0, bind_run]
    exact ih _ (edgeArguments_patchTerm edge _ env)

theorem edgeArguments_fork {state : LS} {block : BlockId} (current : state.cur = some block)
    (bounded : block < state.blocks.size) (condition : ValueId) (env : LEnv) :
    let (pair, after) := fork condition env state
    EdgeArguments after pair.1 [] ∧ EdgeArguments after pair.2 [] := by
  rw [fork_run condition env current]
  refine ⟨⟨⟨[], #[]⟩, ?_, rfl, by simp⟩, ⟨⟨[], #[]⟩, ?_, rfl, by simp⟩⟩
  · simp [Array.getElem?_modify, Nat.ne_of_lt bounded, Array.getElem?_push]
  · have distinct : block ≠ state.blocks.size + 1 := by nat_omega
    simp only [Array.getElem?_modify, distinct, ite_false, Array.getElem?_push, Array.size_push, ite_true]

theorem edgeArguments_scFork {state : LS} {block : BlockId} (current : state.cur = some block)
    (bounded : block < state.blocks.size) {value : ValueId}
    (typed : state.vals[value]? = some (some (.data .bool))) (isAnd : Bool) (env : LEnv) :
    let (pair, after) := scFork isAnd value env state
    EdgeArguments after pair.1 [] ∧ EdgeArguments after pair.2.1 [value] := by
  rw [scFork_run isAnd value env current]
  refine ⟨⟨⟨[], #[]⟩, ?_, rfl, by simp⟩,
    ⟨⟨[(state.vals.size, .data .bool)], #[]⟩, ?_, rfl, ?_⟩⟩
  · simp [Array.getElem?_modify, Nat.ne_of_lt bounded, Array.getElem?_push]
  · have distinct : block ≠ state.blocks.size + 1 := by nat_omega
    simp only [Array.getElem?_modify, distinct, ite_false, Array.getElem?_push, Array.size_push, ite_true]
  · intro pair member
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at member
    subst pair
    have bound : value < state.vals.size := (Array.getElem?_eq_some_iff.mp typed).1
    simp [Array.getElem?_push, Nat.ne_of_lt bound, typed]

theorem joinLive_edgeArguments {state : LS} {incoming : List (BlockId × ValueId)} {ty : VTy}
    (headTyped : state.vals[(incoming.headD (0, 0)).2]? = some (some ty))
    (allTyped : ∀ pair ∈ incoming, state.vals[pair.2]? = some (some ty)) (env : LEnv) :
    let action : B ValueId := do
      let valueTy ← valTy (incoming.headD (0, 0)).2
      let (join, params) ← newBlock [valueTy]
      patchBrs join incoming
      setCur (some join)
      pure (params.headD 0)
    let (_, after) := action env state
    ∀ pair ∈ incoming, EdgeArguments after state.blocks.size [pair.2] := by
  have readTy : valTy (incoming.headD (0, 0)).2 env state = (ty, state) := by
    simp only [valTy, bind_run, get_apply]; rw [headTyped]; rfl
  simp only [bind_run, readTy, newBlock1_run, setCur_run, pure_run]
  intro pair member
  exact edgeArguments_patchBrs env state.blocks.size incoming _
    (edgeArguments_newBlock1 (allTyped pair member) env)

theorem joinValue_edgeArguments {state : LS} {endT endF : Option BlockId}
    {valueT valueF : ValueId} {ty : VTy}
    (thenTyped : endT.isSome = true → state.vals[valueT]? = some (some ty))
    (elseTyped : endF.isSome = true → state.vals[valueF]? = some (some ty)) (env : LEnv) :
    let (_, after) := joinValue endT valueT endF valueF env state
    ∀ pair ∈ (endT.map (·, valueT)).toList ++ (endF.map (·, valueF)).toList,
      EdgeArguments after state.blocks.size [pair.2] := by
  cases endT with
  | none =>
    cases endF with
    | none => simp
    | some elseBlock =>
      have typed := elseTyped rfl
      simpa only [joinValue, Option.map_none, Option.map_some, Option.toList_none,
        Option.toList_some, List.nil_append] using
        (joinLive_edgeArguments (incoming := [(elseBlock, valueF)]) typed
          (by intro pair member; simp only [List.mem_singleton] at member; subst pair; exact typed) env)
  | some thenBlock =>
    have typed := thenTyped rfl
    cases endF with
    | none =>
      simpa only [joinValue, Option.map_none, Option.map_some, Option.toList_none,
        Option.toList_some, List.append_nil] using
        (joinLive_edgeArguments (incoming := [(thenBlock, valueT)]) typed
          (by intro pair member; simp only [List.mem_singleton] at member; subst pair; exact typed) env)
    | some elseBlock =>
      have otherTyped := elseTyped rfl
      simpa only [joinValue, Option.map_some, Option.toList_some, List.cons_append,
        List.nil_append] using
        (joinLive_edgeArguments (incoming := [(thenBlock, valueT), (elseBlock, valueF)]) typed
          (by
            intro pair member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl
            · exact typed
            · exact otherTyped) env)

end Goose.Lower.Validation
