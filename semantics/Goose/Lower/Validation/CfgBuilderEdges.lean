import Goose.Lower.Validation.CfgEdges

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure EdgeExtension (before after : LS) : Prop where
  blocks : before.Ext after
  types : ∀ (value : ValueId) (ty : VTy), before.vals[value]? = some (some ty) → after.vals[value]? = some (some ty)

theorem EdgeExtension.refl (state : LS) : EdgeExtension state state :=
  ⟨.refl state, fun _ _ typed => typed⟩

theorem EdgeExtension.trans {before middle after : LS}
    (one : EdgeExtension before middle) (two : EdgeExtension middle after) : EdgeExtension before after :=
  ⟨one.blocks.trans two.blocks, fun value ty typed => two.types value ty (one.types value ty typed)⟩

def BuilderTermArguments (state : LS) : Term → Prop
  | .br target args => EdgeArguments state target args
  | .condbr _ yes yesArgs no noArgs => EdgeArguments state yes yesArgs ∧ EdgeArguments state no noArgs
  | _ => True

def BuilderInstArguments (state : LS) (inst : Inst) : Prop :=
  match inst.term? with
  | none => True
  | some term => BuilderTermArguments state term

def BuilderEdgeArguments (state : LS) : Prop :=
  ∀ (index : BlockId) (body : BlockB), state.blocks[index]? = some body →
    ∀ inst ∈ body.insts.toList, BuilderInstArguments state inst

theorem EdgeArguments.extend {before after : LS} (edge : EdgeExtension before after)
    {target : BlockId} {args : List ValueId} (typed : EdgeArguments before target args) :
    EdgeArguments after target args := edgeArguments_of_ext edge.blocks edge.types typed

theorem BuilderTermArguments.extend {before after : LS} (edge : EdgeExtension before after)
    {term : Term} (typed : BuilderTermArguments before term) : BuilderTermArguments after term := by
  cases term <;> try trivial
  case br target args => exact edgeArguments_of_ext edge.blocks edge.types typed
  case condbr condition yes yesArgs no noArgs => exact ⟨edgeArguments_of_ext edge.blocks edge.types typed.1, edgeArguments_of_ext edge.blocks edge.types typed.2⟩

theorem BuilderInstArguments.extend {before after : LS} (edge : EdgeExtension before after)
    {inst : Inst} (typed : BuilderInstArguments before inst) : BuilderInstArguments after inst := by
  cases inst with
  | «def» value op => trivial
  | eff effect => trivial
  | term term => exact BuilderTermArguments.extend edge typed

theorem BuilderEdgeArguments.of_blocks {before after : LS} (checked : BuilderEdgeArguments before)
    (blocks : after.blocks = before.blocks)
    (types : ∀ (value : ValueId) (ty : VTy), before.vals[value]? = some (some ty) → after.vals[value]? = some (some ty)) :
    BuilderEdgeArguments after := by
  have extension : before.Ext after := by
    constructor
    · simp [blocks]
    · intro index body row
      exact ⟨body, by rw [blocks]; exact row, rfl, [], by simp⟩
  intro index body row inst member
  rw [blocks] at row
  exact (checked index body row inst member).extend ⟨extension, types⟩

theorem BuilderEdgeArguments.pushInst {state : LS} (checked : BuilderEdgeArguments state)
    (index : BlockId) (inst : Inst) (env : LEnv)
    (typed : BuilderInstArguments state inst) :
    BuilderEdgeArguments (Goose.Lower.pushInst index inst env state).2 := by
  have extension : EdgeExtension state (Goose.Lower.pushInst index inst env state).2 :=
    ⟨(LS.Ext.refl state).modify (appends_push _) index, fun _ _ typed => typed⟩
  intro position body row next member
  change (state.blocks.modify index (fun body => { body with insts := body.insts.push inst }))[position]? = some body at row
  simp only [Array.getElem?_modify] at row
  by_cases same : index = position
  · simp only [same, ite_true, Option.map_eq_some_iff] at row
    obtain ⟨prior, found, rfl⟩ := row
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact (checked position prior found next old).extend extension
    · exact typed.extend extension
  · simp only [same, ite_false] at row
    exact (checked position body row next member).extend extension

theorem BuilderEdgeArguments.emitDef {state : LS} (checked : BuilderEdgeArguments state)
    (op : Op) (env : LEnv) : BuilderEdgeArguments (emitDef op env state).2 := by
  cases current : state.cur with
  | none => rw [emitDef_none op env current]; exact checked
  | some block =>
    apply (checked.pushInst block (.def state.vals.size op) env trivial).of_blocks
    · rw [emitDef_run op env current]
      rfl
    · intro value ty typed
      change state.vals[value]? = some (some ty) at typed
      rw [emitDef_run op env current]
      have bound := (Array.getElem?_eq_some_iff.mp typed).1
      simp [Array.getElem?_push, Nat.ne_of_lt bound, typed]

theorem BuilderEdgeArguments.emitEffect {state : LS} (checked : BuilderEdgeArguments state)
    (effect : Effect) (env : LEnv) : BuilderEdgeArguments (emitEffect effect env state).2 := by
  cases current : state.cur with
  | none => rw [emitEffect_none effect env current]; exact checked
  | some block =>
    apply (checked.pushInst block (.eff effect) env trivial).of_blocks
    · rw [emitEffect_run effect env current]
      rfl
    · intro value ty typed
      rw [emitEffect_run effect env current]
      exact typed

theorem BuilderEdgeArguments.emitTerm {state : LS} (checked : BuilderEdgeArguments state)
    (term : Term) (typed : BuilderTermArguments state term) (env : LEnv) :
    BuilderEdgeArguments (emitTerm term env state).2 := by
  cases current : state.cur with
  | none => rw [emitTerm_none term env current]; exact checked
  | some block =>
    apply (checked.pushInst block (.term term) env typed).of_blocks
    · rw [emitTerm_run term env current]
      rfl
    · intro value ty typed
      rw [emitTerm_run term env current]
      exact typed

theorem BuilderEdgeArguments.patchTerm {state : LS} (checked : BuilderEdgeArguments state)
    (block : BlockId) (term : Term) (typed : BuilderTermArguments state term) (env : LEnv) :
    BuilderEdgeArguments (patchTerm block term env state).2 := checked.pushInst block (.term term) env typed

theorem BuilderEdgeArguments.newBlock0 {state : LS} (checked : BuilderEdgeArguments state) (env : LEnv) :
    BuilderEdgeArguments (newBlock [] env state).2 := by
  have extension : EdgeExtension state (newBlock [] env state).2 :=
    ⟨(advB_newBlock0 env state _ _ rfl).ext, fun _ _ typed => typed⟩
  intro index body row inst member
  rw [newBlock0_run] at row
  simp only [Array.getElem?_push] at row
  split at row
  · obtain rfl := Option.some.inj row
    simp at member
  · exact (checked index body row inst member).extend extension

theorem BuilderEdgeArguments.newBlock1 {state : LS} (checked : BuilderEdgeArguments state)
    (ty : VTy) (env : LEnv) : BuilderEdgeArguments (newBlock [ty] env state).2 := by
  have extension : EdgeExtension state (newBlock [ty] env state).2 := by
    refine ⟨(advB_newBlock1 ty env state _ _ rfl).ext, ?_⟩
    intro value vty typed
    rw [newBlock1_run]
    have bound := (Array.getElem?_eq_some_iff.mp typed).1
    simp [Array.getElem?_push, Nat.ne_of_lt bound, typed]
  intro index body row inst member
  rw [newBlock1_run] at row
  simp only [Array.getElem?_push] at row
  split at row
  · obtain rfl := Option.some.inj row
    simp at member
  · exact (checked index body row inst member).extend extension

theorem BuilderEdgeArguments.setCur {state : LS} (checked : BuilderEdgeArguments state)
    (current : Option BlockId) (env : LEnv) : BuilderEdgeArguments (setCur current env state).2 :=
  checked.of_blocks rfl (fun _ _ typed => typed)

end Goose.Lower.Validation
