import Goose.GIR.Typing

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ReconstructionPartial (n : Nat) (types : ValueId → VTy)
    (vals : Array (Option VTy)) : Prop :=
  vals.size = n ∧ ∀ v t, vals[v]? = some (some t) → t = types v

def ReconstructionPrefix (types : ValueId → VTy)
    (vals : Array (Option VTy)) (k : Nat) : Prop :=
  ∀ v, v < k → vals[v]? = some (some (types v))

def ReconstructionExtends (before after : Array (Option VTy)) : Prop :=
  ∀ (v : ValueId) (t : VTy), before[v]? = some (some t) → after[v]? = some (some t)

def reconstructionEnv (m : GIR.Module) (f : Func)
    (roundStart vals : Array (Option VTy)) : TyEnv :=
  { slots := f.slots
    globals := m.globals.map fun g => (g.ty, g.kind)
    sigs := m.funcs.map fun h => (h.params, h.results)
    vals
    structs := m.structs
    profile := m.profile
    contentsWritable := fun v => (f.permissions m roundStart)[v]?.map (·.2) }

structure OrderedReconstruction (m : GIR.Module) (f : Func) (types : ValueId → VTy) : Prop where
  parameters : ∀ b ∈ f.blocks.toList, ∀ v t, (v, t) ∈ b.params → t = types v
  covers : ∀ v, v < f.numValues →
    (∃ b ∈ f.blocks.toList, (v, types v) ∈ b.params) ∨
    (∃ b ∈ f.blocks.toList, ∃ op, .def v op ∈ b.insts)
  sound : ∀ b ∈ f.blocks.toList, ∀ v op, .def v op ∈ b.insts →
    ∀ roundStart vals t,
      ReconstructionPartial f.numValues types roundStart →
      ReconstructionPartial f.numValues types vals →
      op.resultTy (reconstructionEnv m f roundStart vals) = .ok t → t = types v
  ready : ∀ b ∈ f.blocks.toList, ∀ v op, .def v op ∈ b.insts →
    v < f.numValues → ∀ roundStart vals,
      ReconstructionPartial f.numValues types roundStart →
      ReconstructionPartial f.numValues types vals →
      ReconstructionPrefix types vals v →
      op.resultTy (reconstructionEnv m f roundStart vals) = .ok (types v)

private theorem partial_set {n types vals v t}
    (known : ReconstructionPartial n types vals) (typed : t = types v) :
    ReconstructionPartial n types (vals.set! v (some t)) := by
  refine ⟨by simpa using known.1, ?_⟩
  intro w u lookup
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at lookup
  split at lookup
  · split at lookup
    · cases lookup
      simp_all
    · contradiction
  · exact known.2 w u lookup

private theorem extends_set {n types vals v t}
    (known : ReconstructionPartial n types vals) (typed : t = types v) :
    ReconstructionExtends vals (vals.set! v (some t)) := by
  intro w u lookup
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  split
  · next same =>
      subst w
      have bound := (Array.getElem?_eq_some_iff.mp lookup).1
      simp [bound, known.2 _ _ lookup, typed]
  · exact lookup

private theorem fold_preserves {α β : Type} (xs : List α) (step : β → α → β)
    (property : β → Prop) (initial : β) (start : property initial)
    (preserve : ∀ x ∈ xs, ∀ state, property state → property (step state x)) :
    property (xs.foldl step initial) := by
  induction xs generalizing initial with
  | nil => exact start
  | cons x xs ih =>
    exact ih _ (preserve x (by simp) initial start)
      (fun y member => preserve y (by simp [member]))

private theorem fold_reaches {α β : Type} (xs : List α) (step : β → α → β)
    (property goal : β → Prop) (initial : β) (start : property initial)
    (preserve : ∀ x ∈ xs, ∀ state, property state → property (step state x))
    (retain : ∀ x ∈ xs, ∀ state, property state → goal state → goal (step state x))
    (witness : ∃ x ∈ xs, ∀ state, property state → goal (step state x)) :
    goal (xs.foldl step initial) := by
  induction xs generalizing initial with
  | nil => simp at witness
  | cons x xs ih =>
    obtain ⟨y, member, produces⟩ := witness
    rcases List.mem_cons.mp member with same | tail
    · subst y
      have both := fold_preserves xs step (fun s => property s ∧ goal s)
        (step initial x) ⟨preserve x (by simp) initial start, produces initial start⟩
        (fun z hz state established =>
          ⟨preserve z (by simp [hz]) state established.1,
            retain z (by simp [hz]) state established.1 established.2⟩)
      exact both.2
    · exact ih _ (preserve x (by simp) initial start)
        (fun z hz => preserve z (by simp [hz]))
        (fun z hz => retain z (by simp [hz])) ⟨y, tail, produces⟩

def reconstructionInstruction (m : GIR.Module) (f : Func)
    (roundStart : Array (Option VTy)) (acc : Array (Option VTy) × Bool)
    (instruction : Inst) : Array (Option VTy) × Bool :=
  match instruction with
  | .def r op =>
    if r < f.numValues then
      match op.resultTy (reconstructionEnv m f roundStart acc.1) with
      | .ok t => (acc.1.set! r (some t), acc.2 || acc.1[r]? != some (some t))
      | .error _ => acc
    else acc
  | _ => acc

def reconstructionInstructions (f : Func) : List Inst :=
  f.blocks.toList.flatMap (·.insts)

def reconstructionRound (m : GIR.Module) (f : Func)
    (vals : Array (Option VTy)) : Array (Option VTy) × Bool :=
  (reconstructionInstructions f).foldl (reconstructionInstruction m f vals) (vals, false)

def reconstructionStart (f : Func) : Array (Option VTy) :=
  f.blocks.toList.foldl (fun a b =>
    b.params.foldl (fun a (v, t) =>
      if v < f.numValues then a.set! v (some t) else a) a)
    (Array.replicate f.numValues none)

theorem valueTypes_eq_reconstruction (m : GIR.Module) (f : Func) :
    f.valueTypes m = Func.valueTypes.go (reconstructionRound m f)
      (2 * f.numValues + 2) (reconstructionStart f) := by
  unfold Func.valueTypes reconstructionRound reconstructionInstructions reconstructionStart
  simp only [List.foldl_flatMap, Array.foldl_toList]
  rfl

private theorem instruction_preserves {m : GIR.Module} {f : Func} {types : ValueId → VTy}
    (ordered : OrderedReconstruction m f types)
    {roundStart : Array (Option VTy)}
    (roundKnown : ReconstructionPartial f.numValues types roundStart)
    {instruction : Inst} (member : instruction ∈ reconstructionInstructions f)
    (acc : Array (Option VTy) × Bool)
    (known : ReconstructionPartial f.numValues types acc.1) :
    ReconstructionPartial f.numValues types
      (reconstructionInstruction m f roundStart acc instruction).1 ∧
    ReconstructionExtends acc.1
      (reconstructionInstruction m f roundStart acc instruction).1 := by
  obtain ⟨b, blockMember, instructionMember⟩ := List.mem_flatMap.mp member
  cases instruction <;> simp only [reconstructionInstruction]
  case «def» v op =>
    split
    · split
      · next t typed =>
          have agrees := ordered.sound b blockMember v op instructionMember
            roundStart acc.1 t roundKnown known typed
          exact ⟨partial_set known agrees, extends_set known agrees⟩
      · exact ⟨known, fun _ _ lookup => lookup⟩
    · exact ⟨known, fun _ _ lookup => lookup⟩
  all_goals exact ⟨known, fun _ _ lookup => lookup⟩

private theorem round_preserves {m : GIR.Module} {f : Func} {types : ValueId → VTy}
    (ordered : OrderedReconstruction m f types)
    {vals : Array (Option VTy)} (known : ReconstructionPartial f.numValues types vals) :
    ReconstructionPartial f.numValues types (reconstructionRound m f vals).1 ∧
    ReconstructionExtends vals (reconstructionRound m f vals).1 := by
  apply fold_preserves (reconstructionInstructions f) (reconstructionInstruction m f vals)
    (fun acc => ReconstructionPartial f.numValues types acc.1 ∧
      ReconstructionExtends vals acc.1) (vals, false)
  · exact ⟨known, fun _ _ lookup => lookup⟩
  · intro inst member acc established
    obtain ⟨nextKnown, extension⟩ := instruction_preserves ordered known member acc established.1
    exact ⟨nextKnown, fun v t lookup => extension v t (established.2 v t lookup)⟩

private theorem start_known {m : GIR.Module} {f : Func} {types : ValueId → VTy}
    (ordered : OrderedReconstruction m f types) :
    ReconstructionPartial f.numValues types (reconstructionStart f) := by
  unfold reconstructionStart
  apply fold_preserves f.blocks.toList _
    (ReconstructionPartial f.numValues types) _
  · refine ⟨by simp, ?_⟩
    intro v t lookup
    simp only [Array.getElem?_replicate] at lookup
    split at lookup <;> simp at lookup
  · intro b member vals known
    apply fold_preserves b.params _ (ReconstructionPartial f.numValues types) vals known
    intro pair pairMember acc established
    dsimp
    split
    · exact partial_set established (ordered.parameters b member pair.1 pair.2 pairMember)
    · exact established

private theorem start_parameter {m : GIR.Module} {f : Func} {types : ValueId → VTy}
    (ordered : OrderedReconstruction m f types) {v : ValueId}
    (bound : v < f.numValues)
    (parameter : ∃ b ∈ f.blocks.toList, (v, types v) ∈ b.params) :
    (reconstructionStart f)[v]? = some (some (types v)) := by
  let pairs := f.blocks.toList.flatMap (·.params)
  let step := fun (vals : Array (Option VTy)) (pair : ValueId × VTy) =>
    if pair.1 < f.numValues then vals.set! pair.1 (some pair.2) else vals
  have pairTyped : ∀ pair ∈ pairs, pair.2 = types pair.1 := by
    intro pair member
    obtain ⟨b, member, pairMember⟩ := List.mem_flatMap.mp member
    exact ordered.parameters b member pair.1 pair.2 pairMember
  have preserves : ∀ pair ∈ pairs, ∀ vals,
      ReconstructionPartial f.numValues types vals →
      ReconstructionPartial f.numValues types (step vals pair) := by
    intro pair member vals known
    dsimp [step]
    split
    · exact partial_set known (pairTyped pair member)
    · exact known
  have retained : ∀ pair ∈ pairs, ∀ vals,
      ReconstructionPartial f.numValues types vals →
      vals[v]? = some (some (types v)) → (step vals pair)[v]? = some (some (types v)) := by
    intro pair member vals known lookup
    dsimp [step]
    split
    · exact extends_set known (pairTyped pair member) v (types v) lookup
    · exact lookup
  have initial : ReconstructionPartial f.numValues types (Array.replicate f.numValues none) := by
    refine ⟨by simp, ?_⟩
    intro w t lookup
    simp only [Array.getElem?_replicate] at lookup
    split at lookup <;> simp at lookup
  have produced := fold_reaches pairs step (ReconstructionPartial f.numValues types)
    (fun vals => vals[v]? = some (some (types v))) _ initial preserves retained
    ⟨(v, types v), List.mem_flatMap.mpr parameter, by
      intro vals known
      simp [step, bound, Array.set!_eq_setIfInBounds,
        known.1]⟩
  simpa only [pairs, step, reconstructionStart, List.foldl_flatMap] using produced

private theorem round_prefix {m : GIR.Module} {f : Func} {types : ValueId → VTy}
    (ordered : OrderedReconstruction m f types)
    {vals : Array (Option VTy)} (known : ReconstructionPartial f.numValues types vals)
    {k : Nat} (front : ReconstructionPrefix types vals k) :
    ReconstructionPrefix types (reconstructionRound m f vals).1 k := by
  intro v bound
  exact (round_preserves ordered known).2 v (types v) (front v bound)

private theorem round_next {m : GIR.Module} {f : Func} {types : ValueId → VTy}
    (ordered : OrderedReconstruction m f types)
    {vals : Array (Option VTy)} (known : ReconstructionPartial f.numValues types vals)
    {k : Nat} (bound : k < f.numValues) (front : ReconstructionPrefix types vals k)
    (seeded : ∀ v, v < f.numValues →
      (∃ b ∈ f.blocks.toList, (v, types v) ∈ b.params) →
      vals[v]? = some (some (types v))) :
    ReconstructionPrefix types (reconstructionRound m f vals).1 (k + 1) := by
  have kept := round_prefix ordered known front
  intro v below
  by_cases old : v < k
  · exact kept v old
  have same : v = k := by omega
  subst v
  rcases ordered.covers k bound with parameter | definition
  · exact (round_preserves ordered known).2 k (types k) (seeded k bound parameter)
  · obtain ⟨b, blockMember, op, member⟩ := definition
    have witness : Inst.def k op ∈ reconstructionInstructions f :=
      List.mem_flatMap.mpr ⟨b, blockMember, member⟩
    apply fold_reaches (reconstructionInstructions f) (reconstructionInstruction m f vals)
      (fun acc => ReconstructionPartial f.numValues types acc.1 ∧
        ReconstructionPrefix types acc.1 k)
      (fun acc => acc.1[k]? = some (some (types k))) (vals, false) ⟨known, front⟩
    · intro inst imem acc established
      obtain ⟨nextKnown, extension⟩ := instruction_preserves ordered known imem acc established.1
      exact ⟨nextKnown, fun w h => extension w (types w) (established.2 w h)⟩
    · intro inst imem acc established typed
      exact (instruction_preserves ordered known imem acc established.1).2 k (types k) typed
    · refine ⟨.def k op, witness, ?_⟩
      intro acc established
      have typed := ordered.ready b blockMember k op member bound vals acc.1
        known established.1 established.2
      simp [reconstructionInstruction, bound, typed, Array.set!_eq_setIfInBounds,
        established.1.1]

private theorem set_same {vals : Array (Option VTy)} {v : ValueId} {t : VTy}
    (lookup : vals[v]? = some (some t)) : vals.set! v (some t) = vals := by
  apply Array.ext_getElem?
  intro w
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  split
  · next same =>
      subst w
      rw [ite_eq_left (Array.getElem?_eq_some_iff.mp lookup).1]
      exact lookup.symm
  · rfl

private theorem instruction_unchanged {m : GIR.Module} {f : Func}
    {roundStart : Array (Option VTy)} {acc : Array (Option VTy) × Bool} {inst : Inst}
    (unchanged : (reconstructionInstruction m f roundStart acc inst).2 = false) :
    reconstructionInstruction m f roundStart acc inst = acc ∧ acc.2 = false := by
  cases inst <;> dsimp only [reconstructionInstruction] at unchanged ⊢
  case «def» v op =>
    by_cases bound : v < f.numValues
    · simp only [ite_eq_left bound] at unchanged ⊢
      cases typed : op.resultTy (reconstructionEnv m f roundStart acc.1) with
      | error e => simp only [typed] at unchanged ⊢; exact ⟨trivial, unchanged⟩
      | ok t =>
          simp only [typed] at unchanged ⊢
          have facts : acc.2 = false ∧ acc.1[v]? = some (some t) := by
            simpa using unchanged
          exact ⟨Prod.ext (set_same facts.2) (unchanged.trans facts.1.symm), facts.1⟩
    · simp only [ite_eq_right (by omega)] at unchanged ⊢
      exact ⟨trivial, unchanged⟩
  all_goals exact ⟨rfl, unchanged⟩

private theorem round_unchanged {m : GIR.Module} {f : Func}
    {vals : Array (Option VTy)} (unchanged : (reconstructionRound m f vals).2 = false) :
    (reconstructionRound m f vals).1 = vals := by
  have foldFalse : ∀ (xs : List Inst) (acc : Array (Option VTy) × Bool),
      (xs.foldl (reconstructionInstruction m f vals) acc).2 = false →
      xs.foldl (reconstructionInstruction m f vals) acc = acc := by
    intro xs
    induction xs with
    | nil => intros; rfl
    | cons inst xs ih =>
      intro acc endFalse
      have rest := ih _ endFalse
      have firstFalse : (reconstructionInstruction m f vals acc inst).2 = false := by
        rw [← rest]
        exact endFalse
      rw [List.foldl_cons, rest, (instruction_unchanged firstFalse).1]
  exact congrArg Prod.fst (foldFalse _ (vals, false) unchanged)

private theorem round_total_of_unchanged {m : GIR.Module} {f : Func} {types : ValueId → VTy}
    (ordered : OrderedReconstruction m f types)
    {vals : Array (Option VTy)} (known : ReconstructionPartial f.numValues types vals)
    (seeded : ∀ v, v < f.numValues →
      (∃ b ∈ f.blocks.toList, (v, types v) ∈ b.params) →
      vals[v]? = some (some (types v)))
    (unchanged : (reconstructionRound m f vals).2 = false) :
    ReconstructionPrefix types vals f.numValues := by
  have progress : ∀ k, k ≤ f.numValues → ReconstructionPrefix types vals k := by
    intro k
    induction k with
    | zero => intros; intro v h; omega
    | succ k ih =>
      intro bound
      have next := round_next ordered known (by omega) (ih (by omega)) seeded
      rwa [round_unchanged unchanged] at next
  exact progress _ (Nat.le_refl _)

private theorem go_reconstructs {m : GIR.Module} {f : Func} {types : ValueId → VTy}
    (ordered : OrderedReconstruction m f types)
    (fuel : Nat) {vals : Array (Option VTy)}
    (known : ReconstructionPartial f.numValues types vals)
    (seeded : ∀ v, v < f.numValues →
      (∃ b ∈ f.blocks.toList, (v, types v) ∈ b.params) →
      vals[v]? = some (some (types v)))
    {k : Nat} (front : ReconstructionPrefix types vals k)
    (enough : f.numValues ≤ k + fuel) :
    ReconstructionPrefix types
      (Func.valueTypes.go (reconstructionRound m f) fuel vals) f.numValues := by
  induction fuel generalizing vals k with
  | zero =>
    simp only [Func.valueTypes.go.eq_1]
    intro v bound
    exact front v (by omega)
  | succ fuel ih =>
    rw [Func.valueTypes.go.eq_2]
    change ReconstructionPrefix types
      (if (reconstructionRound m f vals).2 = true then
        Func.valueTypes.go (reconstructionRound m f) fuel (reconstructionRound m f vals).1
      else (reconstructionRound m f vals).1) f.numValues
    split
    · next changed =>
        have nextKnown := (round_preserves ordered known).1
        have nextSeeded : ∀ v, v < f.numValues →
            (∃ b ∈ f.blocks.toList, (v, types v) ∈ b.params) →
            (reconstructionRound m f vals).1[v]? = some (some (types v)) := by
          intro v bound parameter
          exact (round_preserves ordered known).2 v (types v) (seeded v bound parameter)
        by_cases complete : f.numValues ≤ k
        · exact ih nextKnown nextSeeded (round_prefix ordered known front) (by omega)
        · exact ih nextKnown nextSeeded
            (round_next ordered known (by omega) front seeded) (by omega)
    · next stopped =>
        have stoppedFalse : (reconstructionRound m f vals).2 = false := by
          cases h : (reconstructionRound m f vals).2 <;> simp_all
        rw [round_unchanged stoppedFalse]
        exact round_total_of_unchanged ordered known seeded stoppedFalse

theorem valueTypes_reconstructs {m : GIR.Module} {f : Func} {types : ValueId → VTy}
    (ordered : OrderedReconstruction m f types) :
    ReconstructionPrefix types (f.valueTypes m) f.numValues := by
  rw [valueTypes_eq_reconstruction]
  apply go_reconstructs ordered _ (start_known ordered)
    (fun v bound parameter => start_parameter ordered bound parameter)
    (k := 0) (by intro v h; omega)
  omega

end Goose.Lower.Validation
