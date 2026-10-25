import Goose.Lower.Validation.SourceReadyObservations

namespace Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

variable {module : GIR.Module} {func : Func} {state : State}

theorem emits_noncall_def (operation : Op)
    (absent : ∀ callee arguments origin, operation ≠ .call callee arguments origin) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.emitDef operation) := by
  intro le before value after run
  exact emitsOnly_emitDef run (.definition before.vals.size operation absent)

theorem emits_effect (effect : Effect) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.emitEffect effect) :=
  emitsOnly_emitEffect effect (.effect module func state effect)

theorem emits_term (term : Term) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.emitTerm term) :=
  emitsOnly_emitTerm term (.term module func state term)

theorem emits_get : EmitsOnlyRun (ReadyCallObservations module func state) (get : B LS) := by
  intro le before value after run
  cases run
  exact .refl _ _

theorem emits_read : EmitsOnlyRun (ReadyCallObservations module func state) (read : B LEnv) := by
  intro le before value after run
  cases run
  exact .refl _ _

theorem emits_valTy (value : ValueId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.valTy value) := by
  intro le before result after run
  apply EmitsOnly.of_blocks
  simpa only [run] using congrArg LS.blocks (valTy_run value le before)

theorem emits_setCur (current : Option BlockId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.setCur current) := by
  intro le before value after run
  apply EmitsOnly.of_blocks
  have same := congrArg (fun result => result.2.blocks) run
  simpa only [setCur_run] using same.symm

theorem emits_newBlock (types : List VTy) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.newBlock types) := by
  intro le before value after run
  change ((before.blocks.size, (List.range types.length).map (before.vals.size + ·)),
    { before with
      blocks := before.blocks.push
        ⟨((List.range types.length).map (before.vals.size + ·)).zip types, #[]⟩,
      vals := types.foldl (fun values type => values.push (some type)) before.vals }) = (value, after) at run
  cases run
  exact (EmitsOnly.newBlock before _).trans (.of_blocks rfl)

theorem emits_whenLive (default : α) (next : BlockId → B α)
    (children : ∀ block, EmitsOnlyRun (ReadyCallObservations module func state) (next block)) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.whenLive default next) := by
  unfold Goose.Lower.whenLive
  refine EmitsOnlyRun.bind ?_ ?_
  · exact EmitsOnlyRun.bind emits_get (fun before => EmitsOnlyRun.pure _ before.cur)
  · intro current
    cases current with
    | none => exact .pure _ _
    | some block => exact children block

theorem emits_fork (value : ValueId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.fork value) := by
  unfold Goose.Lower.fork
  apply EmitsOnlyRun.bind (emits_newBlock [])
  rintro ⟨passed, _⟩
  apply EmitsOnlyRun.bind (emits_newBlock [])
  rintro ⟨failed, _⟩
  apply EmitsOnlyRun.bind (emits_term (.condbr value passed [] failed []))
  intro _
  exact .pure _ _

theorem emits_intTyOf (value : ValueId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.intTyOf value) := by
  unfold Goose.Lower.intTyOf
  apply EmitsOnlyRun.bind (emits_valTy value)
  intro type
  split <;> exact .pure _ _

theorem emits_coerceTo (type : Ty) (value : ValueId) (origin : OriginId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.coerceTo type value origin) := by
  unfold Goose.Lower.coerceTo
  apply EmitsOnlyRun.bind (emits_valTy value)
  intro actual
  split
  · exact emits_noncall_def _ (by intro callee arguments origin same; cases same)
  · apply EmitsOnlyRun.bind (emits_noncall_def _ (by intro callee arguments origin same; cases same))
    intro view
    exact emits_noncall_def _ (by intro callee arguments origin same; cases same)
  · exact .pure _ _

theorem emits_coerceSlot (slot : SlotId) (value : ValueId) (origin : OriginId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.coerceSlot slot value origin) := by
  unfold Goose.Lower.coerceSlot
  apply EmitsOnlyRun.bind (emits_read)
  intro le
  cases le.slots[slot]? with
  | none => exact .pure _ _
  | some destination => exact emits_coerceTo destination.ty value origin

theorem emits_coerceResult (value : ValueId) (origin : OriginId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.coerceResult value origin) := by
  unfold Goose.Lower.coerceResult
  apply EmitsOnlyRun.bind (emits_read)
  intro le
  cases le.results.head? with
  | none => exact .pure _ _
  | some destination => exact emits_coerceTo destination value origin

theorem emits_leaveAll (scopes : List ScopeId) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.leaveAll scopes) := by
  induction scopes with
  | nil => exact .pure _ _
  | cons scope rest ih => exact EmitsOnlyRun.bind (emits_effect (.leave scope)) (fun _ => ih)

theorem emits_leaveTo (depth : Nat) :
    EmitsOnlyRun (ReadyCallObservations module func state) (Goose.Lower.leaveTo depth) := by
  unfold Goose.Lower.leaveTo
  apply EmitsOnlyRun.bind (emits_get)
  intro before
  exact emits_leaveAll _

end Goose.Lower.Validation.ReplacementContentFlowSource.ReadyCallObservations
