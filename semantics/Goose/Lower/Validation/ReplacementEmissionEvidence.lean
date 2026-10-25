import Goose.Lower.CoreToGir

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure EmitsOnly (property : Inst → Prop) (before after : LS) : Prop where
  blocks : before.blocks.size ≤ after.blocks.size
  old : ∀ (index : BlockId) (body : BlockB), before.blocks[index]? = some body →
    ∃ next, after.blocks[index]? = some next ∧ next.params = body.params ∧
      ∃ tail, next.insts.toList = body.insts.toList ++ tail ∧ ∀ inst ∈ tail, property inst
  fresh : ∀ (index : BlockId) (body : BlockB), after.blocks[index]? = some body →
    before.blocks.size ≤ index → ∀ inst ∈ body.insts.toList, property inst

end Goose.Lower.Validation
