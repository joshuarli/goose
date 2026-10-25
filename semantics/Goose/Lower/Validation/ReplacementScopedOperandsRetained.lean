import Goose.Lower.Validation.ReplacementScopedOperandsLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem RhsValueFresh.coerceTo {floor : Nat} {env : LEnv} {before after : LS}
    {target : Ty} {value result : ValueId} {origin : OriginId}
    (bound : floor ≤ before.vals.size) (fresh : RhsValueFresh floor before value)
    (run : coerceTo target value origin env before = (result, after)) :
    RhsValueFresh floor after result := by
  rcases coerceTo_cases run with ⟨rfl, rfl⟩ | ⟨_, _, emitted⟩ | ⟨_, view, middle, _, first, last⟩
  · exact fresh
  · exact RhsValueFresh.output bound (freshValue_emitDef _) emitted
  · exact RhsValueFresh.output (Nat.le_trans bound (advB_emitDef _ env before view middle first).vals)
      (freshValue_emitDef _) last

theorem RhsValueFresh.coerceSlot {floor : Nat} {env : LEnv} {before after : LS}
    {slot : SlotId} {value result : ValueId} {origin : OriginId}
    (bound : floor ≤ before.vals.size) (fresh : RhsValueFresh floor before value)
    (run : coerceSlot slot value origin env before = (result, after)) :
    RhsValueFresh floor after result := by
  unfold Goose.Lower.coerceSlot at run
  simp only [bind_run, read_apply] at run
  cases lookup : env.slots[slot]? with
  | some destination =>
    simp only [lookup] at run
    exact RhsValueFresh.coerceTo bound fresh run
  | none =>
    simp only [lookup] at run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    exact fresh

theorem RhsValueFresh.coerceResult {floor : Nat} {env : LEnv} {before after : LS}
    {value result : ValueId} {origin : OriginId}
    (bound : floor ≤ before.vals.size) (fresh : RhsValueFresh floor before value)
    (run : coerceResult value origin env before = (result, after)) :
    RhsValueFresh floor after result := by
  unfold Goose.Lower.coerceResult at run
  simp only [bind_run, read_apply] at run
  cases lookup : env.results.head? with
  | some destination =>
    simp only [lookup] at run
    exact RhsValueFresh.coerceTo bound fresh run
  | none =>
    simp only [lookup] at run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    exact fresh

theorem RhsValueFresh.borrowTo {floor : Nat} {env : LEnv} {before after : LS}
    {mu : Mutability} {value result : ValueId}
    (bound : floor ≤ before.vals.size) (fresh : RhsValueFresh floor before value)
    (run : borrowTo mu value env before = (result, after)) : RhsValueFresh floor after result := by
  rcases borrowTo_cases run with frozen | emitted
  · rcases freezeTo_cases frozen with ⟨rfl, rfl⟩ | emitted
    · exact fresh
    · exact RhsValueFresh.output bound (freshValue_emitDef _) emitted
  · exact RhsValueFresh.output bound (freshValue_emitDef _) emitted

theorem rhsOperands_eachElemValue (floor : Nat) (env : LEnv) (before : LS)
    (slot : VarId) (byRef : Bool) (element : ValueId)
    (fresh : RhsValueFresh floor before element) :
    RhsOperandsAt floor env before (eachElemValue slot byRef element) := by
  unfold eachElemValue
  split
  · apply (RhsOperandsAt.read _ _ _).bind
    simp only [read_apply]
    split
    · split
      · exact RhsOperandsAt.borrowTo _ _ _ _ _ fresh
      · exact RhsOperandsAt.pure _ _ _ _
    · exact RhsOperandsAt.pure _ _ _ _
  · exact RhsOperandsAt.emitDef _ _ _ _ (by simpa only [Op.uses, List.mem_singleton] using
      fun live value equal => equal ▸ (fresh live))

theorem RhsValueFresh.eachElemValue {floor : Nat} {env : LEnv} {before after : LS}
    {slot : VarId} {byRef : Bool} {element result : ValueId}
    (bound : floor ≤ before.vals.size) (fresh : RhsValueFresh floor before element)
    (run : eachElemValue slot byRef element env before = (result, after)) :
    RhsValueFresh floor after result := by
  unfold Goose.Lower.eachElemValue at run
  cases byRef
  · exact RhsValueFresh.output bound (freshValue_emitDef _) run
  · simp only [↓reduceIte, bind_run, read_apply] at run
    cases lookup : env.vars[slot]? with
    | none =>
      simp only [lookup] at run
      obtain ⟨rfl, rfl⟩ := pure_eq.mp run
      exact fresh
    | some localVar =>
      simp only [lookup] at run
      cases type : localVar.ty <;> simp only [type] at run <;> first
        | exact RhsValueFresh.borrowTo bound fresh run
        | (obtain ⟨rfl, rfl⟩ := pure_eq.mp run; exact fresh)

end Goose.Lower.Validation
