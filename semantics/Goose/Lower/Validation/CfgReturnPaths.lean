import Goose.Lower.Validation.CfgReturnBits

namespace Goose.Lower.Validation

open Goose.GIR

def ReturnFlowLE (left right : ReturnFlow) : Prop :=
  left = .stops ∨ left = right

theorem blockReturnFlow_monotone {left right : Array Bool} (order : ReturnBitsLE left right)
    (code : List Inst) : ReturnFlowLE (blockReturnFlow left code) (blockReturnFlow right code) := by
  induction code with
  | nil => exact Or.inr rfl
  | cons inst rest ih =>
    cases inst with
    | «def» value op =>
      cases op <;> try exact ih
      rename_i callee args origin
      simp only [blockReturnFlow]
      by_cases returns : left[callee]?.getD true = true
      · have next := order.getD callee returns
        simpa only [returns, next, ite_true] using ih
      · simp only [returns]
        exact Or.inl rfl
    | eff effect => exact ih
    | term term =>
      cases term <;> exact Or.inr rfl

inductive ReturnPath (mayReturn : Array Bool) (func : Func) : BlockId → Prop
  | missing {block : BlockId} (row : func.blocks[block]? = none) : ReturnPath mayReturn func block
  | returns {block : BlockId} {body : Block} (row : func.blocks[block]? = some body)
      (flow : blockReturnFlow mayReturn body.insts = .returns) : ReturnPath mayReturn func block
  | branch {block target : BlockId} {body : Block} {targets : List BlockId}
      (row : func.blocks[block]? = some body)
      (flow : blockReturnFlow mayReturn body.insts = .branches targets)
      (member : target ∈ targets) (next : ReturnPath mayReturn func target) : ReturnPath mayReturn func block

def ReturnClosed (mayReturn : Array Bool) (func : Func) (closed : BlockId → Prop) : Prop :=
  ∀ block, closed block → ∃ body, func.blocks[block]? = some body ∧
    (blockReturnFlow mayReturn body.insts = .stops ∨
      ∃ targets, blockReturnFlow mayReturn body.insts = .branches targets ∧
        ∀ target ∈ targets, closed target)

theorem ReturnClosed.excludes {mayReturn : Array Bool} {func : Func} {closed : BlockId → Prop}
    (safe : ReturnClosed mayReturn func closed) {block : BlockId}
    (path : ReturnPath mayReturn func block) : ¬ closed block := by
  induction path with
  | missing row =>
    intro member
    obtain ⟨body, found, _⟩ := safe _ member
    rw [row] at found
    cases found
  | returns row flow =>
    intro member
    obtain ⟨body, found, stops | ⟨targets, branches, _⟩⟩ := safe _ member
    · have same := Option.some.inj (row.symm.trans found)
      subst body
      rw [flow] at stops
      cases stops
    · have same := Option.some.inj (row.symm.trans found)
      subst body
      rw [flow] at branches
      cases branches
  | branch row flow member next ih =>
    intro present
    obtain ⟨body, found, stops | ⟨targets, branches, contains⟩⟩ := safe _ present
    · have same := Option.some.inj (row.symm.trans found)
      subst body
      rw [flow] at stops
      cases stops
    · have same := Option.some.inj (row.symm.trans found)
      subst body
      rw [flow] at branches
      cases branches
      exact ih (contains _ member)

theorem ReturnClosed.antitone {left right : Array Bool} (order : ReturnBitsLE left right)
    {func : Func} {closed : BlockId → Prop} (safe : ReturnClosed right func closed) :
    ReturnClosed left func closed := by
  intro block present
  obtain ⟨body, row, flow⟩ := safe block present
  refine ⟨body, row, ?_⟩
  rcases blockReturnFlow_monotone order body.insts with stops | same
  · exact Or.inl stops
  · rw [same]
    exact flow

end Goose.Lower.Validation
