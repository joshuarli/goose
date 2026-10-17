import Goose.Lower.Validation.ShrinkGenerated

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ReplacementSafe (types : Array (Option VTy)) (valid : Array Bool)
    (facts : List ValueId) (inst : Inst) : Prop :=
  ∀ owner run origin, inst = .eff (.replace owner run origin) →
    (∃ element, ownerTy types owner = some (.grow element) ∨
      ownerTy types owner = some (.growshrink element)) ∧
    valid[run]? = some true ∧ owner ∈ facts

inductive ReplacementTrace (module : GIR.Module) (types : Array (Option VTy))
    (provenance : Prov) (valid : Array Bool) : List ValueId → List Inst → Prop
  | nil (facts) : ReplacementTrace module types provenance valid facts []
  | cons {facts inst rest} (safe : ReplacementSafe types valid facts inst)
      (tail : ReplacementTrace module types provenance valid
        (transferEmptyInst module types provenance facts inst) rest) :
      ReplacementTrace module types provenance valid facts (inst :: rest)

theorem checkReplace_of_safe (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : Prov) (valid : Array Bool)
    (label : String) (facts : List ValueId) (inst : Inst)
    (safe : ReplacementSafe types valid facts inst) :
    checkReplace module func types provenance valid label facts inst = .ok () := by
  cases inst with
  | «def» result op => simp [checkReplace, pure, Except.pure]
  | term term => simp [checkReplace, pure, Except.pure]
  | eff effect =>
    cases effect <;> try rfl
    rename_i owner run origin
    obtain ⟨⟨element, ownerType | ownerType⟩, fresh, cleared⟩ := safe owner run origin rfl <;>
      simp [checkReplace, ownerType, fresh, cleared,
        pure, Except.pure]

theorem replacementTrace_scan (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : Prov) (valid : Array Bool)
    (label : String) {facts : List ValueId} {insts : List Inst}
    (trace : ReplacementTrace module types provenance valid facts insts) :
    (forIn insts facts fun inst current => do
      checkReplace module func types provenance valid label current inst
      pure (.yield (transferEmptyInst module types provenance current inst))) =
        (Except.ok (insts.foldl (transferEmptyInst module types provenance) facts) :
          Check (List ValueId)) := by
  induction trace with
  | nil => rfl
  | cons safe tail ih =>
    rw [List.forIn_cons, checkReplace_of_safe module func types provenance valid label _ _ safe]
    exact ih

private theorem list_forIn'_checked {items : List α}
    {body : (item : α) → item ∈ items → PUnit → Check (ForInStep PUnit)}
    (checked : ∀ item member, body item member PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn' items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn'_cons, checked item (by simp)]
    exact ih (fun next member => checked next (by simp [member]))

def ReplacementBlocksSafe (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : Prov) : Prop :=
  ∀ (index : Nat) (block : GIR.Block), func.blocks[index]? = some block →
    ∃ facts, (emptyFactsAtBlocks module func types (replacementProvenance func provenance))[index]? = some (some facts) ∧
      ReplacementTrace module types (replacementProvenance func provenance)
        (freshRuns func types) facts block.insts

theorem checkShrinkReplace_of_blocks (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : Prov) (label : String)
    (safe : ReplacementBlocksSafe module func types provenance) :
    checkShrinkReplace module label func types provenance = .ok () := by
  unfold checkShrinkReplace
  split
  · dsimp only
    apply Eq.trans (congrArg (fun result : Check PUnit => result >>= fun _ => pure ()) (a₂ := .ok PUnit.unit) ?_) rfl
    rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
    apply list_forIn'_checked
    intro index member
    have bounded : index < func.blocks.size := by
      have bounds := List.mem_range'.mp member
      simp [Std.Legacy.Range.size] at bounds
      nat_omega
    let block := func.blocks[index]
    have row : func.blocks[index]? = some block := by simp [block, bounded]
    obtain ⟨facts, state, trace⟩ := safe index block row
    simp only [row, state, Option.join_some]
    rw [replacementTrace_scan module func types (replacementProvenance func provenance)
      (freshRuns func types) label trace]
    rfl
  · rfl

def NoReplacements (func : Func) : Prop :=
  ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts, ∀ owner run origin,
    inst ≠ .eff (.replace owner run origin)

theorem replacementTrace_of_no_replacements (module : GIR.Module)
    (types : Array (Option VTy)) (provenance : Prov) (valid : Array Bool)
    (insts : List Inst) (absent : ∀ inst ∈ insts, ∀ owner run origin,
      inst ≠ .eff (.replace owner run origin)) (facts : List ValueId) :
    ReplacementTrace module types provenance valid facts insts := by
  induction insts generalizing facts with
  | nil => exact .nil facts
  | cons inst rest ih =>
    apply ReplacementTrace.cons
    · intro owner run origin equal
      exact False.elim (absent inst (by simp) owner run origin equal)
    · exact ih (by intro next member; exact absent next (by simp [member])) _

theorem lowerImpl_checkShrinkReplace_without_replacements (module : Core.Module)
    (impl : Core.Impl) (types : Array (Option VTy)) (provenance : Prov) (label : String)
    (absent : NoReplacements (lowerImpl module impl)) :
    checkShrinkReplace (lower module) label (lowerImpl module impl) types provenance = .ok () := by
  apply checkShrinkReplace_of_blocks
  intro index block row
  obtain ⟨facts, state⟩ := lowerImpl_emptyFacts_known module impl types (replacementProvenance (lowerImpl module impl) provenance)
    ((Array.getElem?_eq_some_iff.mp row).1)
  exact ⟨facts, state, replacementTrace_of_no_replacements _ _ _ _ _
    (absent block (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row))) facts⟩

theorem lowerContextAt_checkShrinkReplace_without_replacements (module : Core.Module)
    (context : Core.Context) (impl : Core.Impl) (types : Array (Option VTy))
    (provenance : Prov) (label : String) (absent : NoReplacements (lowerContextAt module context impl)) :
    checkShrinkReplace (lower module) label (lowerContextAt module context impl) types provenance = .ok () := by
  apply checkShrinkReplace_of_blocks
  intro index block row
  obtain ⟨facts, state⟩ := lowerContextAt_emptyFacts_known module context impl types
    (replacementProvenance (lowerContextAt module context impl) provenance)
    ((Array.getElem?_eq_some_iff.mp row).1)
  exact ⟨facts, state, replacementTrace_of_no_replacements _ _ _ _ _
    (absent block (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row))) facts⟩

theorem lowerGlobal_checkShrinkReplace_without_replacements (module : Core.Module)
    (global : Core.Global) (types : Array (Option VTy)) (provenance : Prov) (label : String)
    (absent : NoReplacements (lowerGlobal module global).init) :
    checkShrinkReplace (lower module) label (lowerGlobal module global).init types provenance = .ok () := by
  apply checkShrinkReplace_of_blocks
  intro index block row
  obtain ⟨facts, state⟩ := lowerGlobal_emptyFacts_known module global types (replacementProvenance (lowerGlobal module global).init provenance)
    ((Array.getElem?_eq_some_iff.mp row).1)
  exact ⟨facts, state, replacementTrace_of_no_replacements _ _ _ _ _
    (absent block (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row))) facts⟩

end Goose.Lower.Validation
