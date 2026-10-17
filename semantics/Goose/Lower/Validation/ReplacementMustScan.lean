import Goose.Lower.Validation.ReplacementMustFacts

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReplacementSafe.mono {types : Array (Option VTy)} {valid : Array Bool}
    {before after : List ValueId} {inst : Inst} (safe : ReplacementSafe types valid before inst)
    (subset : before ⊆ after) : ReplacementSafe types valid after inst := by
  intro owner run origin same
  obtain ⟨ty, fresh, cleared⟩ := safe owner run origin same
  exact ⟨ty, fresh, subset cleared⟩

theorem ReplacementTrace.mono {module : GIR.Module} {types : Array (Option VTy)}
    {queries : ReplacementQueries} {valid : Array Bool} {before after : List ValueId} {insts : List Inst}
    (trace : ReplacementTrace module types queries valid before insts) (subset : before ⊆ after) :
    ReplacementTrace module types queries valid after insts := by
  induction trace generalizing after with
  | nil => exact .nil after
  | cons safe tail ih =>
    exact .cons (safe.mono subset) (ih (transferEmptyInst_mono module types queries _ subset))

theorem lowerContextAt_checkShrinkReplace_of_required (module : Core.Module) (context : Core.Context)
    (impl : Core.Impl) (types : Array (Option VTy)) (label : String)
    (required : BlockId → List ValueId)
    (closed : EmptyFactsClosed (lower module) (lowerContextAt module context impl) types
      (replacementQueries (lower module) (lowerContextAt module context impl) types) required)
    (entry : required 0 = [])
    (traces : ∀ (index : Nat) (block : GIR.Block),
      (lowerContextAt module context impl).blocks[index]? = some block →
        ReplacementTrace (lower module) types (replacementQueries (lower module) (lowerContextAt module context impl) types)
          (freshRuns (lowerContextAt module context impl) types) (required index) block.insts) :
    checkShrinkReplace (lower module) label (lowerContextAt module context impl) types = .ok () := by
  apply checkShrinkReplace_of_blocks
  intro index block row
  obtain ⟨facts, state, contains⟩ := lowerContextAt_required_emptyFacts module context impl types
    required closed entry ((Array.getElem?_eq_some_iff.mp row).1)
  exact ⟨facts, state, (traces index block row).mono contains⟩

theorem lowerGlobal_checkShrinkReplace_of_required (module : Core.Module) (global : Core.Global)
    (types : Array (Option VTy)) (label : String) (required : BlockId → List ValueId)
    (closed : EmptyFactsClosed (lower module) (lowerGlobal module global).init types
      (replacementQueries (lower module) (lowerGlobal module global).init types) required)
    (entry : required 0 = [])
    (traces : ∀ (index : Nat) (block : GIR.Block),
      (lowerGlobal module global).init.blocks[index]? = some block →
        ReplacementTrace (lower module) types (replacementQueries (lower module) (lowerGlobal module global).init types)
          (freshRuns (lowerGlobal module global).init types) (required index) block.insts) :
    checkShrinkReplace (lower module) label (lowerGlobal module global).init types = .ok () := by
  apply checkShrinkReplace_of_blocks
  intro index block row
  obtain ⟨facts, state, contains⟩ := lowerGlobal_required_emptyFacts module global types
    required closed entry ((Array.getElem?_eq_some_iff.mp row).1)
  exact ⟨facts, state, (traces index block row).mono contains⟩

end Goose.Lower.Validation
