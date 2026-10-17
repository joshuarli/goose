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

theorem EmitsOnlyRun.whenLive {property : Inst → Prop} (default : α) (next : BlockId → B α)
    (preserves : ∀ block, EmitsOnlyRun property (next block)) :
    EmitsOnlyRun property (Goose.Lower.whenLive default next) := by
  unfold Goose.Lower.whenLive
  apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (fun _ _ => rfl))
  intro current
  cases current with
  | none => exact .pure _ _
  | some index => exact preserves index

theorem emitsOnly_scFork (property : Inst → Prop) (terms : ∀ term, property (.term term))
    (isAnd : Bool) (value : ValueId) : EmitsOnlyRun property (scFork isAnd value) := by
  unfold scFork
  apply EmitsOnlyRun.bind (emitsOnly_newBlock property [])
  rintro ⟨right, _⟩
  apply EmitsOnlyRun.bind (emitsOnly_newBlock property [.data .bool])
  rintro ⟨join, params⟩
  dsimp only
  split
  all_goals
    apply EmitsOnlyRun.bind (emitsOnly_emitTerm _ (terms _))
    intro _
    exact .pure _ _

theorem emitsOnly_shortCircuit {property : Inst → Prop} (terms : ∀ term, property (.term term))
    (isAnd : Bool) (value : ValueId) {rhs : B ValueId} (preserves : EmitsOnlyRun property rhs) :
    EmitsOnlyRun property (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  apply EmitsOnlyRun.whenLive
  intro index
  apply EmitsOnlyRun.bind (emitsOnly_scFork property terms isAnd value)
  rintro ⟨right, join, parameter⟩
  apply EmitsOnlyRun.bind (emitsOnly_setCur property (some right))
  intro _
  apply EmitsOnlyRun.bind preserves
  intro result
  apply EmitsOnlyRun.bind (emitsOnly_emitTerm _ (terms _))
  intro _
  apply EmitsOnlyRun.bind (emitsOnly_setCur property (some join))
  intro _
  exact .pure _ _

theorem emitsOnly_fork (property : Inst → Prop) (terms : ∀ term, property (.term term))
    (value : ValueId) : EmitsOnlyRun property (fork value) := by
  unfold fork
  apply EmitsOnlyRun.bind (emitsOnly_newBlock property [])
  rintro ⟨yes, _⟩
  apply EmitsOnlyRun.bind (emitsOnly_newBlock property [])
  rintro ⟨no, _⟩
  apply EmitsOnlyRun.bind (emitsOnly_emitTerm _ (terms _))
  intro _
  exact .pure _ _

theorem emitsOnly_patchBrs (property : Inst → Prop) (terms : ∀ term, property (.term term))
    (join : BlockId) (branches : List (BlockId × ValueId)) : EmitsOnlyRun property (patchBrs join branches) := by
  induction branches with
  | nil => exact .pure _ _
  | cons branch rest ih =>
    obtain ⟨block, value⟩ := branch
    apply EmitsOnlyRun.bind (emitsOnly_pushInst block (.term (.br join [value])) (terms _))
    intro _
    exact ih

theorem emitsOnly_joinValue (property : Inst → Prop) (terms : ∀ term, property (.term term))
    (yes no : Option BlockId) (yesValue noValue : ValueId) :
    EmitsOnlyRun property (joinValue yes yesValue no noValue) := by
  unfold joinValue
  split
  · apply EmitsOnlyRun.bind (emitsOnly_setCur property none)
    intro _
    exact .pure _ _
  · apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (fun env state => congrArg LS.blocks (valTy_run _ env state)))
    intro type
    apply EmitsOnlyRun.bind (emitsOnly_newBlock property [type])
    rintro ⟨join, params⟩
    apply EmitsOnlyRun.bind (emitsOnly_patchBrs property terms join _)
    intro _
    apply EmitsOnlyRun.bind (emitsOnly_setCur property (some join))
    intro _
    exact .pure _ _

theorem EmitsOnlyRun.inScope {property : Inst → Prop} (scope : ScopeId) {action : B α}
    (emitted : EmitsOnlyRun property action) : EmitsOnlyRun property (Goose.Lower.inScope scope action) := by
  unfold Goose.Lower.inScope
  apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (fun _ _ => rfl))
  intro _
  apply EmitsOnlyRun.bind emitted
  intro value
  apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (fun _ _ => rfl))
  intro _
  exact .pure _ _

end Goose.Lower.Validation
