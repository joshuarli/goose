import Goose.Lower.Validation.CfgSourceDominanceStatementIf
import Goose.Lower.Validation.CfgSourceDominanceShortCircuit

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def continuationTarget : ContKind → BlockId
  | .jump header | .next header _ _ => header

def continuationValues : ContKind → List ValueId
  | .jump _ => []
  | .next _ _ counter => [counter]

structure HeaderSSA (continuation : ContKind) (state : LS) (imports : ImportedValues) : Prop where
  bound : continuationTarget continuation < state.blocks.size
  incoming : AvailableValues state imports (imports (continuationTarget continuation))
  counter : AvailableValues state imports (continuationValues continuation)

theorem HeaderSSA.move {continuation : ContKind} {before after : LS}
    {beforeImports afterImports : ImportedValues} {values : List ValueId}
    (header : HeaderSSA continuation before beforeImports)
    (result : SSAResult before after beforeImports afterImports values) :
    HeaderSSA continuation after afterImports := by
  refine ⟨Nat.lt_of_lt_of_le header.bound result.advance.ext.1, ?_, result.frame _ header.counter⟩
  rw [result.imports _ header.bound]
  exact result.frame _ header.incoming

theorem header_imports_current {state : LS} {imports : ImportedValues}
    (checked : ImportedState state imports) {header : BlockId} (current : state.cur = some header) :
    AvailableValues state imports (imports header) := by
  intro block live value member
  have same : block = header := Option.some.inj (live.symm.trans current)
  subst block
  obtain ⟨body, row, _⟩ := checked.opened header current
  exact ⟨body, row, Or.inl member⟩

theorem HeaderSSA.jump_current {state : LS} {imports : ImportedValues}
    (checked : ImportedState state imports) {header : BlockId} (current : state.cur = some header) :
    HeaderSSA (.jump header) state imports :=
  ⟨checked.opened.bound header current, header_imports_current checked current, by simp [AvailableValues, continuationValues]⟩

theorem HeaderSSA.next_current {state : LS} {imports : ImportedValues}
    (checked : ImportedState state imports) {header : BlockId} (current : state.cur = some header)
    (type : IntTy) (counter : ValueId) (available : AvailableValues state imports [counter]) :
    HeaderSSA (.next header type counter) state imports :=
  ⟨checked.opened.bound header current, header_imports_current checked current, available⟩

theorem HeaderSSA.loopReady {continuation : ContKind} {state : LS} {imports : ImportedValues}
    (header : HeaderSSA continuation state imports) (depth : Nat) (exit : BlockId)
    (exitBound : exit < state.blocks.size) (available : AvailableValues state imports (imports exit)) :
    LoopImportsReady (some ⟨depth, exit, continuation⟩) state imports := by
  refine ⟨?_, ?_, ?_⟩
  · intro target member
    have choice : target = exit ∨ target = continuationTarget continuation := by
      cases continuation <;> simpa [loopTargets, continuationTarget] using member
    rcases choice with rfl | rfl
    · exact exitBound
    · exact header.bound
  · intro target member
    have choice : target = exit ∨ target = continuationTarget continuation := by
      cases continuation <;> simpa [loopTargets, continuationTarget] using member
    rcases choice with rfl | rfl
    · exact available
    · exact header.incoming
  · cases continuation <;> exact header.counter

theorem ssa_counter (depth : Nat) (exit header : BlockId) (type : IntTy) (counter : ValueId) :
    SSARun (some ⟨depth, exit, .next header type counter⟩) [] (fun value => [value]) (pure counter) := by
  intro env before result after run imports checked ready _
  obtain ⟨rfl, rfl⟩ := pure_eq.mp run
  exact ⟨imports, checked, .refl before, fun _ _ => rfl, fun _ available => available, ready.counters⟩

theorem ssa_rangeBack (depth : Nat) (exit header : BlockId) (type : IntTy) (counter : ValueId) :
    SSARun (some ⟨depth, exit, .next header type counter⟩) [] (fun _ => []) (rangeBack type counter header) := by
  unfold rangeBack
  refine SSARun.bind (ssa_isLive _) fun live => ?_
  cases live with
  | false => exact ssa_pure _ _
  | true =>
    let context : Option LoopCtx := some ⟨depth, exit, .next header type counter⟩
    have back := SSARun.bind (ssa_counter depth exit header type counter) fun value =>
      SSARun.bind (ssa_emitDef context (.next type value)) fun advanced =>
        ssa_emitTerm context (.br header [advanced]) (by simp [Term.successors, loopTargets, context])
    exact back

end Goose.Lower.Validation
