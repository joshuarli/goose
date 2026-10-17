import Goose.Lower.Validation.CfgSourceDominanceRun

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem SSAResult.of_current {before after : LS} {imports : ImportedValues} {values : List ValueId}
    (checked : ImportedState after imports) (advance : before.Adv after)
    (current : after.cur = none ∨ after.cur = before.cur)
    (available : AvailableValues after imports values) : SSAResult before after imports imports values := by
  refine ⟨checked, advance, fun _ _ => rfl, ?_, available⟩
  intro values framed block live value member
  rcases current with stopped | same
  · rw [stopped] at live
    cases live
  · exact (framed block (same.symm.trans live) value member).of_ext advance.ext (fun _ _ => rfl)

theorem ImportedState.emitDef {state : LS} {imports : ImportedValues}
    (checked : ImportedState state imports) (op : Op) (env : LEnv)
    (operands : AvailableValues state imports op.uses) :
    ImportedState (emitDef op env state).2 imports := by
  have advance := advB_emitDef op env state _ _ rfl
  have blocksSize : (Goose.Lower.emitDef op env state).2.blocks.size = state.blocks.size := by
    cases current : state.cur with
    | none => rw [emitDef_none op env current]
    | some block => rw [emitDef_run op env current]; simp
  refine ⟨?_, ?_, checked.targets.emitDef op env, checked.opened.emitDef op env, ?_⟩
  · apply checked.certificate.emitDef op env
    · intro block current imported
      exact Nat.lt_irrefl _ (checked.importsBounded block (checked.opened.bound block current) _ imported)
    · exact operands
  · cases current : state.cur with
    | none => rw [emitDef_none op env current]; exact checked.definitions
    | some block =>
      rw [emitDef_run op env current]
      exact checked.definitions.emitDef (op := op) (le := env) current (checked.opened.bound block current)
  · intro block bound value imported
    have beforeBound : block < state.blocks.size := blocksSize ▸ bound
    exact Nat.lt_of_lt_of_le (checked.importsBounded block beforeBound value imported) advance.vals

theorem ssa_emitDef (loop : Option LoopCtx) (op : Op) :
    SSARun loop op.uses (fun value => [value]) (emitDef op) := by
  intro env before result after run imports checked _ operands
  have afterChecked := checked.emitDef op env operands
  rw [run] at afterChecked
  have advance := advB_emitDef op env before result after run
  have current : after.cur = before.cur := by
    have same := emitDef_current op env before
    rw [run] at same
    exact same
  refine ⟨imports, SSAResult.of_current afterChecked advance (Or.inr current) ?_⟩
  intro block live value member
  have sameValue : value = result := by simpa using member
  subst value
  have beforeLive : before.cur = some block := current.symm.trans live
  obtain ⟨body, row, _⟩ := checked.opened block beforeLive
  rw [emitDef_run op env beforeLive] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  refine ⟨{ body with insts := body.insts.push (.def before.vals.size op) }, ?_, Or.inr ?_⟩
  · simp [Array.getElem?_modify, row]
  · simp [cfgBlock, GIR.Block.defs, List.filterMap_append]

theorem ImportedState.emitEffect {state : LS} {imports : ImportedValues}
    (checked : ImportedState state imports) (effect : Effect) (env : LEnv)
    (operands : AvailableValues state imports effect.uses) :
    ImportedState (emitEffect effect env state).2 imports := by
  refine ⟨checked.certificate.emitEffect effect env operands, ?_, checked.targets.emitEffect effect env,
    checked.opened.emitEffect effect env, ?_⟩
  · cases current : state.cur with
    | none => rw [emitEffect_none effect env current]; exact checked.definitions
    | some block =>
      rw [emitEffect_run effect env current]
      exact checked.definitions.emitEffect (e := effect) (le := env) (checked.opened.bound block current)
  · cases current : state.cur with
    | none => rw [emitEffect_none effect env current]; exact checked.importsBounded
    | some block =>
      rw [emitEffect_run effect env current]
      simpa using checked.importsBounded

theorem ssa_emitEffect (loop : Option LoopCtx) (effect : Effect) :
    SSARun loop effect.uses (fun _ => []) (emitEffect effect) := by
  intro env before result after run imports checked _ operands
  have afterChecked := checked.emitEffect effect env operands
  rw [run] at afterChecked
  refine ⟨imports, SSAResult.of_current afterChecked (advB_emitEffect effect env before result after run)
    (Or.inr ?_) (by simp [AvailableValues])⟩
  cases current : before.cur with
  | none => rw [emitEffect_none effect env current] at run; rw [← (Prod.mk.inj run).2]; exact current
  | some block => rw [emitEffect_run effect env current] at run; rw [← (Prod.mk.inj run).2]; exact current

theorem ssa_emitTerm (loop : Option LoopCtx) (term : Term)
    (targets : term.successors ⊆ loopTargets loop) :
    SSARun loop term.uses (fun _ => []) (emitTerm term) := by
  intro env before result after run imports checked ready operands
  have afterCertificate := checked.certificate.emitTerm term env operands
    (fun block current target member value imported => ready.available target (targets member)
      block current value imported)
  have afterTargets := checked.targets.emitTerm term
    (fun target member => ready.bounds target (targets member)) env
  have afterOpened := currentOpen_emitTerm before term env
  rw [run] at afterCertificate afterTargets afterOpened
  have afterDefinitions : after.DenseDefinitions := by
    cases current : before.cur with
    | none => rw [emitTerm_none term env current] at run; exact (Prod.mk.inj run).2 ▸ checked.definitions
    | some block =>
      rw [emitTerm_run term env current] at run
      exact (Prod.mk.inj run).2 ▸ checked.definitions.emitTerm (le := env) (t := term)
        (checked.opened.bound block current)
  have afterBounds : ∀ block, block < after.blocks.size →
      ∀ value ∈ imports block, value < after.vals.size := by
    cases current : before.cur with
    | none => rw [emitTerm_none term env current] at run; exact (Prod.mk.inj run).2 ▸ checked.importsBounded
    | some block =>
      rw [emitTerm_run term env current] at run
      obtain ⟨_, rfl⟩ := Prod.mk.inj run
      simpa using checked.importsBounded
  have stopped : after.cur = none := by
    cases current : before.cur with
    | none =>
      rw [emitTerm_none term env current] at run
      rw [← (Prod.mk.inj run).2]
      exact current
    | some block =>
      rw [emitTerm_run term env current] at run
      rw [← (Prod.mk.inj run).2]
  exact ⟨imports, SSAResult.of_current
    ⟨afterCertificate, afterDefinitions, afterTargets, afterOpened, afterBounds⟩
    (advB_emitTerm term env before result after run) (Or.inl stopped) (by simp [AvailableValues, stopped])⟩

theorem ssa_read (loop : Option LoopCtx) : SSARun loop [] (fun _ => []) (read : B LEnv) :=
  SSARun.unchanged loop _ (fun _ _ => rfl)

theorem ssa_get (loop : Option LoopCtx) : SSARun loop [] (fun _ => []) (get : B LS) :=
  SSARun.unchanged loop _ (fun _ _ => rfl)

theorem ssa_valTy (loop : Option LoopCtx) (value : ValueId) :
    SSARun loop [] (fun _ => []) (valTy value) :=
  SSARun.unchanged loop _ (valTy_run value)

theorem ssa_curBlock (loop : Option LoopCtx) : SSARun loop [] (fun _ => []) curBlock :=
  SSARun.unchanged loop _ (fun env state => by rw [curBlock_run])

theorem ssa_isLive (loop : Option LoopCtx) : SSARun loop [] (fun _ => []) isLive :=
  SSARun.unchanged loop _ (fun env state => by simp [isLive, bind_run, curBlock_run, pure_run])

end Goose.Lower.Validation
