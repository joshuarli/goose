import Goose.Lower.Validation.CfgBuilderEdges

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EdgeRun (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) → BuilderEdgeArguments before →
    EdgeExtension before after ∧ BuilderEdgeArguments after

theorem EdgeRun.pure (value : α) : EdgeRun (pure value) := by
  intro env before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact ⟨.refl before, checked⟩

theorem EdgeRun.bind {first : B α} {next : α → B β}
    (one : EdgeRun first) (two : ∀ value, EdgeRun (next value)) : EdgeRun (first >>= next) := by
  intro env before result after run checked
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  obtain ⟨firstExtension, firstChecked⟩ := one env before value middle firstRun checked
  obtain ⟨nextExtension, nextChecked⟩ := two value env middle result after nextRun firstChecked
  exact ⟨firstExtension.trans nextExtension, nextChecked⟩

theorem EdgeRun.unchanged {action : B α} (same : ∀ env state, (action env state).2 = state) : EdgeRun action := by
  intro env before result after run checked
  have equal := same env before
  rw [run] at equal
  change after = before at equal
  subst after
  exact ⟨.refl before, checked⟩

theorem edge_read : EdgeRun (read : B LEnv) := EdgeRun.unchanged (by intros; rfl)

theorem edge_get : EdgeRun (get : B LS) := EdgeRun.unchanged (by intros; rfl)

theorem edge_valTy (value : ValueId) : EdgeRun (valTy value) := EdgeRun.unchanged (valTy_run value)

theorem edge_isLive : EdgeRun isLive := EdgeRun.unchanged (by intros; rfl)

theorem edge_curBlock : EdgeRun curBlock := EdgeRun.unchanged (by intros; rw [curBlock_run])

theorem edge_emitDef (op : Op) : EdgeRun (emitDef op) := by
  intro env before result after run checked
  refine ⟨⟨(advB_emitDef op env before result after run).ext, ?_⟩, ?_⟩
  · intro value ty typed
    cases current : before.cur with
    | none =>
      rw [emitDef_none op env current] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      exact typed
    | some block =>
      rw [emitDef_run op env current] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      have bound := (Array.getElem?_eq_some_iff.mp typed).1
      simp [Array.getElem?_push, Nat.ne_of_lt bound, typed]
  · have emitted := checked.emitDef op env
    rw [run] at emitted
    exact emitted

theorem edge_emitEffect (effect : Effect) : EdgeRun (emitEffect effect) := by
  intro env before result after run checked
  have types : after.vals = before.vals := by
    cases current : before.cur with
    | none => rw [emitEffect_none effect env current] at run; exact congrArg (LS.vals ∘ Prod.snd) run.symm
    | some block => rw [emitEffect_run effect env current] at run; exact congrArg (LS.vals ∘ Prod.snd) run.symm
  have emitted := checked.emitEffect effect env
  rw [run] at emitted
  exact ⟨⟨(advB_emitEffect effect env before result after run).ext, fun value ty typed => by rw [types]; exact typed⟩, emitted⟩

theorem edge_emitTerm_at (term : Term) (env : LEnv) (before after : LS) (result : Unit)
    (run : emitTerm term env before = (result, after)) (checked : BuilderEdgeArguments before)
    (typed : before.cur.isSome = true → BuilderTermArguments before term) :
    EdgeExtension before after ∧ BuilderEdgeArguments after := by
  have types : after.vals = before.vals := by
    cases current : before.cur with
    | none => rw [emitTerm_none term env current] at run; exact congrArg (LS.vals ∘ Prod.snd) run.symm
    | some block => rw [emitTerm_run term env current] at run; exact congrArg (LS.vals ∘ Prod.snd) run.symm
  refine ⟨⟨(advB_emitTerm term env before result after run).ext,
    fun value ty recorded => by rw [types]; exact recorded⟩, ?_⟩
  cases current : before.cur with
  | none =>
    rw [emitTerm_none term env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    have emitted := checked.emitTerm term (typed (by simp [current])) env
    rw [run] at emitted
    exact emitted

theorem edge_emitTerm (term : Term) (typed : ∀ state, BuilderTermArguments state term) : EdgeRun (emitTerm term) :=
  fun env before result after run checked => edge_emitTerm_at term env before after result run checked (fun _ => typed before)

theorem edge_patchTerm_at (block : BlockId) (term : Term) (env : LEnv) (before after : LS) (result : Unit)
    (run : patchTerm block term env before = (result, after)) (checked : BuilderEdgeArguments before)
    (typed : BuilderTermArguments before term) : EdgeExtension before after ∧ BuilderEdgeArguments after := by
  have extension := (LS.Ext.refl before).modify (appends_push (.term term)) block
  have emitted := checked.patchTerm block term typed env
  rw [run] at emitted
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨⟨extension, fun _ _ typed => typed⟩, emitted⟩

theorem edge_newBlock0 : EdgeRun (newBlock []) := by
  intro env before result after run checked
  have emitted := checked.newBlock0 env
  rw [run] at emitted
  have extension := (advB_newBlock0 env before result after run).ext
  rw [newBlock0_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨⟨extension, fun _ _ typed => typed⟩, emitted⟩

theorem edge_newBlock1 (ty : VTy) : EdgeRun (newBlock [ty]) := by
  intro env before result after run checked
  have emitted := checked.newBlock1 ty env
  rw [run] at emitted
  refine ⟨⟨(advB_newBlock1 ty env before result after run).ext, ?_⟩, emitted⟩
  intro value vty typed
  rw [newBlock1_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  have bound := (Array.getElem?_eq_some_iff.mp typed).1
  simp [Array.getElem?_push, Nat.ne_of_lt bound, typed]

theorem edge_setCur (current : Option BlockId) : EdgeRun (setCur current) := by
  intro env before result after run checked
  have emitted := checked.setCur current env
  rw [run] at emitted
  rw [setCur_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨⟨.refl before, fun _ _ typed => typed⟩, emitted⟩

theorem edge_whenLive (fallback : α) {body : BlockId → B α}
    (checked : ∀ block, EdgeRun (body block)) : EdgeRun (whenLive fallback body) := by
  unfold whenLive
  refine EdgeRun.bind edge_curBlock fun current => ?_
  cases current with
  | none => exact EdgeRun.pure fallback
  | some block => exact checked block

end Goose.Lower.Validation
