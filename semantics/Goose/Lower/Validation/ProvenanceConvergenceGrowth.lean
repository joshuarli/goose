import Goose.Lower.Validation.ProvenanceConvergenceCells

namespace Goose.Lower.Validation.ProvenanceConvergence

open Goose.Core Goose.GIR

theorem Growth.flag_false {before after : Prov × Bool} (growth : Growth before after)
    (quiet : after.2 = false) : before.2 = false := by
  cases flag : before.2 with
  | false => rfl
  | true => have := growth.changed flag; simp_all

theorem Growth.quiet_eq {before after : Prov × Bool} (growth : Growth before after)
    (quiet : after.2 = false) : after = before := by
  apply Prod.ext (growth.quiet quiet)
  rw [quiet, growth.flag_false quiet]

theorem fold_growth (items : List α) (step : Prov × Bool → α → Prov × Bool)
    (grows : ∀ state item, Growth state (step state item)) (start : Prov × Bool) :
    Growth start (items.foldl step start) := by
  apply List.foldlRecOn (motive := fun state => Growth start state) items step (Growth.refl start)
  intro state prior item _
  exact prior.trans (grows state item)

private theorem edge_growth (func : Func) (state : Prov × Bool) (target : BlockId) (args : List ValueId) :
    Growth state
      (match func.blocks[target]? with
      | none => state
      | some block =>
        (block.params.zip args).foldl (fun (acc : Prov × Bool) (pair : (ValueId × VTy) × ValueId) =>
          let (p, changed) := acc
          let (param, argument) := pair
          let (values, inserted) := GIR.addTo p.vals param.1 (rootsAt p.vals argument)
          ({ p with vals := values }, changed || inserted)) state) := by
  cases row : func.blocks[target]? with
  | none => exact Growth.refl state
  | some block =>
    exact fold_growth _ _ (fun _ _ => Growth.addValues _ _ _) state

theorem provStep_growth (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (state : Prov × Bool) (inst : Inst) :
    Growth state (func.provStep results types state inst) := by
  cases inst with
  | «def» value op => exact Growth.addValues _ _ _
  | eff effect =>
    cases effect with
    | slotInit slot value origin => exact Growth.addSlots _ _ _
    | store address value origin =>
      exact fold_growth _ _ (fun acc root => by
        cases root with
        | «local» slot => exact Growth.addSlots _ _ _
        | _ => exact Growth.refl acc) state
    | _ => exact Growth.refl state
  | term term =>
    cases term with
    | br target args => exact edge_growth func state target args
    | condbr condition left leftArgs right rightArgs =>
      exact (edge_growth func state left leftArgs).trans (edge_growth func _ right rightArgs)
    | _ => exact Growth.refl state

theorem provRound_growth (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (provenance : Prov) :
    Growth (provenance, false) (provRound results types func provenance) := by
  unfold provRound
  rw [← Array.foldl_toList]
  exact fold_growth _ _ (fun _ _ => fold_growth _ _ (provStep_growth results types func) _) _

theorem provRound_changed_weight (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (provenance : Prov)
    (changed : (provRound results types func provenance).2 = true) :
    weight provenance < weight (provRound results types func provenance).1 :=
  (provRound_growth results types func provenance).strict rfl changed

theorem provRound_quiet (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (provenance : Prov)
    (quiet : (provRound results types func provenance).2 = false) :
    provRound results types func provenance = (provenance, false) :=
  (provRound_growth results types func provenance).quiet_eq quiet

theorem fold_step_quiet {items : List α} {step : Prov × Bool → α → Prov × Bool}
    (grows : ∀ state item, Growth state (step state item)) {start : Prov × Bool}
    (quiet : (items.foldl step start).2 = false) {item : α} (member : item ∈ items) :
    step start item = start := by
  induction items generalizing start with
  | nil => cases member
  | cons first rest ih =>
    have headQuiet := (fold_growth rest step grows (step start first)).flag_false quiet
    have same := (grows start first).quiet_eq headQuiet
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact same
    · apply ih (start := start) ?_ member
      simpa only [List.foldl_cons, same] using quiet

def InstructionRootsClosed (results : Array (List RootRef)) (types : Array (Option VTy))
    (func : Func) (provenance : Prov) : Prop :=
  ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts,
    func.provStep results types (provenance, false) inst = (provenance, false)

theorem instructionRootsClosed_of_quiet {results : Array (List RootRef)} {types : Array (Option VTy)}
    {func : Func} {provenance : Prov}
    (quiet : (provRound results types func provenance).2 = false) :
    InstructionRootsClosed results types func provenance := by
  intro block blockMember inst instMember
  unfold provRound at quiet
  rw [← Array.foldl_toList] at quiet
  have blockSame := fold_step_quiet
    (fun _ block => fold_growth block.insts _ (provStep_growth results types func) _)
    quiet blockMember
  apply fold_step_quiet (provStep_growth results types func) ?_ instMember
  rw [blockSame]

end Goose.Lower.Validation.ProvenanceConvergence
