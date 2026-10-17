import Goose.Lower.Validation.ReplacementEmission

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

inductive ReplacementControlInst : Inst → Prop
  | term (term) : ReplacementControlInst (.term term)
  | enter (scope) : ReplacementControlInst (.eff (.enter scope))
  | leave (scope) : ReplacementControlInst (.eff (.leave scope))
  | clear (owner origin) : ReplacementControlInst (.eff (.clear owner origin))

theorem ReplacementInstApart.control {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner : ValueId} {inst : Inst}
    (control : ReplacementControlInst inst) : ReplacementInstApart module types queries owner inst := by
  constructor
  · intro value member reference
    cases control <;> simp [emptyFactSourceOperands] at member
  · intro value op same reference
    cases control <;> cases same
  · intro value receiver
    cases control <;> cases receiver
  · intro value function args origin same
    cases control <;> cases same

theorem EmitsOnlyRun.unchanged {property : Inst → Prop} {action : B α}
    (same : ∀ env state, (action env state).2.blocks = state.blocks) : EmitsOnlyRun property action := by
  intro env before value after run
  apply EmitsOnly.of_blocks
  simpa only [run] using same env before

theorem emitsOnly_newBlock (property : Inst → Prop) (types : List VTy) :
    EmitsOnlyRun property (newBlock types) := by
  intro env before value after run
  change ((before.blocks.size, (List.range types.length).map (before.vals.size + ·)),
    { before with
      blocks := (before.blocks.push
        ⟨((List.range types.length).map (before.vals.size + ·)).zip types, #[]⟩),
      vals := (types.foldl (fun values type => values.push (some type)) before.vals) }) = (value, after) at run
  cases run
  exact (EmitsOnly.newBlock before _).trans (.of_blocks rfl)

theorem emitsOnly_setCur (property : Inst → Prop) (current : Option BlockId) :
    EmitsOnlyRun property (setCur current) := by
  apply EmitsOnlyRun.unchanged
  intro env state
  rw [setCur_run]

theorem emitsOnly_patchTerm {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner : ValueId} (index : BlockId) (term : Term) :
    EmitsOnlyRun (ReplacementInstApart module types queries owner) (patchTerm index term) :=
  emitsOnly_pushInst index (.term term) (.control (.term term))

theorem emitsOnly_controlTerm {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {owner : ValueId} (term : Term) :
    EmitsOnlyRun (ReplacementInstApart module types queries owner) (emitTerm term) :=
  emitsOnly_emitTerm term (.control (.term term))

end Goose.Lower.Validation
