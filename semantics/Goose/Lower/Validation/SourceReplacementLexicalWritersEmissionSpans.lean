import Goose.Lower.Validation.SourceReplacementWriterLedgerEmissions

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.GIR SourceReplacementWriterLedger

private theorem effectEmission_span {env : LEnv} {before current after : LS} {effect : Effect}
    {emission : Emission} (initial : before.Ext current)
    (final : (emitEffect effect env current).2.Ext after)
    (member : emission ∈ effectEmission env current effect) :
    before.Ext emission.before ∧ emission.after.Ext after := by
  unfold effectEmission at member
  split at member
  · have same := List.mem_singleton.mp member
    subst emission
    exact ⟨initial,final⟩
  · contradiction

private theorem definitionEmission_span {env : LEnv} {before current after : LS} {op : Op}
    {emission : Emission} (initial : before.Ext current)
    (final : (emitDef op env current).2.Ext after)
    (member : emission ∈ definitionEmission env current op) :
    before.Ext emission.before ∧ emission.after.Ext after := by
  unfold definitionEmission at member
  split at member
  · have same := List.mem_singleton.mp member
    subst emission
    exact ⟨initial,final⟩
  · contradiction

theorem initializationEmissions_span {env : LEnv} {bindings : List (SlotId × ValueId × OriginId)}
    {before : LS} {emission : Emission}
    (member : emission ∈ initializationEmissions env bindings before) :
    before.Ext emission.before ∧ emission.after.Ext (initSlots bindings env before).2 := by
  induction bindings generalizing before with
  | nil => contradiction
  | cons binding rest ih =>
    rcases binding with ⟨slot,value,origin⟩
    rcases List.mem_append.mp member with head | tail
    · have suffix := (advB_initSlots rest env (emitEffect (.slotInit slot value (some origin)) env before).2 _ _ rfl).ext
      have bounded := effectEmission_span (.refl before) suffix head
      simpa only [initSlots,bind_run] using bounded
    · have bounded := ih tail
      have initial := (advB_emitEffect (.slotInit slot value (some origin)) env before _ _ rfl).ext
      exact ⟨initial.trans bounded.1,by simpa only [initSlots,bind_run] using bounded.2⟩

theorem fragment_emission_span {fragment : Fragment} {env : LEnv} {before : LS} {emission : Emission}
    (member : emission ∈ fragment.emissions env before) :
    before.Ext emission.before ∧ emission.after.Ext (fragment.finish env before) := by
  cases fragment with
  | expression expression =>
    cases expression <;> simp only [Fragment.emissions] at member <;> try contradiction
    case call callee arguments origin =>
      apply definitionEmission_span (advB_lowerArgs arguments env before _ _ rfl).ext _ member
      have suffix (result : ValueId) : AdvB (do
          if (← read).mod.noReturn callee then emitTerm .unreachable
          pure result : B ValueId) := by
        apply AdvB.bind advB_read
        intro le
        cases returns : le.mod.noReturn callee
        · simp only [Bool.false_eq_true,reduceIte]
          exact AdvB.bind (AdvB.pure ()) (fun _ => AdvB.pure result)
        · simp only [reduceIte]
          exact AdvB.bind (advB_emitTerm .unreachable) (fun _ => AdvB.pure result)
      exact (suffix _ env _ _ _ rfl).ext

  | statement loop statement =>
    cases statement <;> simp only [Fragment.emissions] at member <;> try contradiction
    case letS slot expression origin =>
      have initial := (advB_lowerExpr expression env before _ _ rfl).ext.trans
        (advB_coerceSlot slot (lowerExpr expression env before).1 origin env _ _ _ rfl).ext
      exact effectEmission_span initial (.refl _) member
    case assign place expression origin =>
      have initial := (advB_lowerPlace place env before _ _ rfl).ext.trans
        (advB_lowerExpr expression env (lowerPlace place env before).2 _ _ rfl).ext
      exact effectEmission_span initial (.refl _) member
    case assignOp operation place expression origin =>
      let addressed := lowerPlace place env before
      let loaded := emitDef (.load addressed.1) env addressed.2
      let lowered := lowerExpr expression env loaded.2
      let integer := intTyOf loaded.1 env lowered.2
      let combined := emitDef (.bin operation integer.1 loaded.1 lowered.1 (some origin)) env integer.2
      have initial := (advB_lowerPlace place env before _ _ rfl).ext.trans
        ((advB_emitDef (.load addressed.1) env addressed.2 _ _ rfl).ext.trans
          ((advB_lowerExpr expression env loaded.2 _ _ rfl).ext.trans
            ((advB_intTyOf loaded.1 env lowered.2 _ _ rfl).ext.trans
              (advB_emitDef (.bin operation integer.1 loaded.1 lowered.1 (some origin)) env integer.2 _ _ rfl).ext)))
      exact effectEmission_span initial (.refl _) member
    case rebind slot expression origin =>
      let lowered := lowerExpr expression env before
      let coerced := coerceSlot slot lowered.1 origin env lowered.2
      have initial := (advB_lowerExpr expression env before _ _ rfl).ext.trans
        ((advB_coerceSlot slot lowered.1 origin env lowered.2 _ _ rfl).ext.trans
          (advB_emitDef (.slotAddr slot) env coerced.2 _ _ rfl).ext)
      exact effectEmission_span initial (.refl _) member
    case assignWhole place expression origin =>
      let addressed := lowerPlace place env before
      let cleared := emitEffect (.clear addressed.1 (some origin)) env addressed.2
      have initial := (advB_lowerPlace place env before _ _ rfl).ext.trans
        ((advB_emitEffect (.clear addressed.1 (some origin)) env addressed.2 _ _ rfl).ext.trans
          (advB_lowerExpr expression env cleared.2 _ _ rfl).ext)
      exact effectEmission_span initial (.refl _) member
  | block loop bindings want block =>
    cases block with
    | mk scope statements value =>
      let entered := (emitEffect (.enter scope) env before).2
      let inside := (pushScope scope env entered).2
      let initialized := (initSlots bindings env inside).2
      let stated := (lowerStmts loop statements env initialized).2
      let valued := (lowerBlockValue want value env stated).2
      have bounded := initializationEmissions_span member
      have initial : before.Ext inside := (advB_emitEffect (.enter scope) env before _ _ rfl).ext
      have final := (advB_lowerStmts loop statements env initialized _ _ rfl).ext.trans
        ((advB_lowerBlockValue want value env stated _ _ rfl).ext.trans
          (advB_emitEffect (.leave scope) env valued _ _ rfl).ext)
      refine ⟨initial.trans bounded.1,?_⟩
      exact bounded.2.trans final
  | _ => simp [Fragment.emissions] at member

private theorem effectEmission_liveBound {env : LEnv} {before : LS} {effect : Effect}
    {emission : Emission} (bounded : LiveBound before)
    (member : emission ∈ effectEmission env before effect) : LiveBound emission.before := by
  unfold effectEmission at member
  split at member
  · have same := List.mem_singleton.mp member
    subst emission
    exact bounded
  · contradiction

private theorem definitionEmission_liveBound {env : LEnv} {before : LS} {op : Op}
    {emission : Emission} (bounded : LiveBound before)
    (member : emission ∈ definitionEmission env before op) : LiveBound emission.before := by
  unfold definitionEmission at member
  split at member
  · have same := List.mem_singleton.mp member
    subst emission
    exact bounded
  · contradiction

theorem initializationEmissions_liveBound {env : LEnv} {bindings : List (SlotId × ValueId × OriginId)}
    {before : LS} {emission : Emission} (bounded : LiveBound before)
    (member : emission ∈ initializationEmissions env bindings before) : LiveBound emission.before := by
  induction bindings generalizing before with
  | nil => contradiction
  | cons binding rest ih =>
    rcases binding with ⟨slot,value,origin⟩
    rcases List.mem_append.mp member with head | tail
    · exact effectEmission_liveBound bounded head
    · exact ih (liveBound_of_adv (advB_emitEffect (.slotInit slot value (some origin)) env before _ _ rfl) bounded) tail

theorem fragment_emission_liveBound {fragment : Fragment} {env : LEnv} {before : LS} {emission : Emission}
    (bounded : LiveBound before) (member : emission ∈ fragment.emissions env before) : LiveBound emission.before := by
  cases fragment with
  | expression expression =>
    cases expression <;> simp only [Fragment.emissions] at member <;> try contradiction
    case call callee arguments origin =>
      exact definitionEmission_liveBound
        (liveBound_of_adv (advB_lowerArgs arguments env before _ _ rfl) bounded) member
  | statement loop statement =>
    cases statement <;> simp only [Fragment.emissions] at member <;> try contradiction
    case letS slot expression origin =>
      have initial := (advB_lowerExpr expression env before _ _ rfl).trans
        (advB_coerceSlot slot (lowerExpr expression env before).1 origin env _ _ _ rfl)
      exact effectEmission_liveBound (liveBound_of_adv initial bounded) member
    case assign place expression origin =>
      have initial := (advB_lowerPlace place env before _ _ rfl).trans
        (advB_lowerExpr expression env (lowerPlace place env before).2 _ _ rfl)
      exact effectEmission_liveBound (liveBound_of_adv initial bounded) member
    case assignOp operation place expression origin =>
      let addressed := lowerPlace place env before
      let loaded := emitDef (.load addressed.1) env addressed.2
      let lowered := lowerExpr expression env loaded.2
      let integer := intTyOf loaded.1 env lowered.2
      have initial := (advB_lowerPlace place env before _ _ rfl).trans
        ((advB_emitDef (.load addressed.1) env addressed.2 _ _ rfl).trans
          ((advB_lowerExpr expression env loaded.2 _ _ rfl).trans
            ((advB_intTyOf loaded.1 env lowered.2 _ _ rfl).trans
              (advB_emitDef (.bin operation integer.1 loaded.1 lowered.1 (some origin)) env integer.2 _ _ rfl))))
      exact effectEmission_liveBound (liveBound_of_adv initial bounded) member
    case rebind slot expression origin =>
      let lowered := lowerExpr expression env before
      let coerced := coerceSlot slot lowered.1 origin env lowered.2
      have initial := (advB_lowerExpr expression env before _ _ rfl).trans
        ((advB_coerceSlot slot lowered.1 origin env lowered.2 _ _ rfl).trans
          (advB_emitDef (.slotAddr slot) env coerced.2 _ _ rfl))
      exact effectEmission_liveBound (liveBound_of_adv initial bounded) member
    case assignWhole place expression origin =>
      let addressed := lowerPlace place env before
      let cleared := emitEffect (.clear addressed.1 (some origin)) env addressed.2
      have initial := (advB_lowerPlace place env before _ _ rfl).trans
        ((advB_emitEffect (.clear addressed.1 (some origin)) env addressed.2 _ _ rfl).trans
          (advB_lowerExpr expression env cleared.2 _ _ rfl))
      exact effectEmission_liveBound (liveBound_of_adv initial bounded) member
  | block loop bindings want block =>
    cases block with
    | mk scope statements value =>
      have entered := liveBound_of_adv (advB_emitEffect (.enter scope) env before _ _ rfl) bounded
      exact initializationEmissions_liveBound
        (before := (pushScope scope env (emitEffect (.enter scope) env before).2).2) entered member
  | _ => simp [Fragment.emissions] at member

#print axioms initializationEmissions_span
#print axioms fragment_emission_span
#print axioms initializationEmissions_liveBound
#print axioms fragment_emission_liveBound

end Goose.Lower.Validation.SourceReplacementLexicalWriters
