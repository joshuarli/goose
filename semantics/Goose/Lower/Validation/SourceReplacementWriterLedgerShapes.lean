import Goose.Lower.Validation.SourceReplacementWriterLedgerEmissions

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

theorem effectEmission_eq {env : LEnv} {before : LS} {effect : Effect} {emission : Emission}
    (member : emission ∈ effectEmission env before effect) :
    emission = ⟨before,(emitEffect effect env before).2,.eff effect⟩ ∧ before.cur.isSome = true := by
  unfold effectEmission at member
  split at member
  · exact ⟨List.mem_singleton.mp member,by assumption⟩
  · contradiction

theorem definitionEmission_eq {env : LEnv} {before : LS} {op : Op} {emission : Emission}
    (member : emission ∈ definitionEmission env before op) :
    emission = ⟨before,(emitDef op env before).2,.def before.vals.size op⟩ ∧ before.cur.isSome = true := by
  unfold definitionEmission at member
  split at member
  · exact ⟨List.mem_singleton.mp member,by assumption⟩
  · contradiction

theorem initializationEmissions_shape {env : LEnv} {before : LS} {bindings : List (SlotId × ValueId × OriginId)}
    {emission : Emission} (member : emission ∈ initializationEmissions env bindings before) :
    ∃ slot value origin, (slot,value,origin) ∈ bindings ∧ emission.instruction = .eff (.slotInit slot value (some origin)) := by
  induction bindings generalizing before with
  | nil => contradiction
  | cons binding rest ih =>
    rcases binding with ⟨slot,value,origin⟩
    rcases List.mem_append.mp member with head | tail
    · obtain ⟨same,_⟩ := effectEmission_eq head
      exact ⟨slot,value,origin,List.mem_cons_self,congrArg Emission.instruction same⟩
    · obtain ⟨slot,value,origin,member,same⟩ := ih tail
      exact ⟨slot,value,origin,List.mem_cons_of_mem _ member,same⟩

theorem Fragment.call_emission_shape {fragment : Fragment} {env : LEnv} {before : LS} {emission : Emission}
    {result callee : Nat} {arguments : List ValueId} {origin : Option OriginId}
    (member : emission ∈ fragment.emissions env before)
    (same : emission.instruction = .def result (.call callee arguments origin)) :
    ∃ syntaxArgs sourceOrigin,
      fragment = .expression (.call callee syntaxArgs sourceOrigin) ∧ origin = some sourceOrigin ∧
      lowerArgs syntaxArgs env before = (arguments,emission.before) ∧
      emitDef (.call callee arguments origin) env emission.before = (result,emission.after) := by
  cases fragment with
  | expression expression =>
    cases expression <;> simp only [Fragment.emissions] at member <;> try contradiction
    case call sourceCallee syntaxArgs sourceOrigin =>
      obtain ⟨identity,live⟩ := definitionEmission_eq member
      subst emission
      obtain ⟨rfl,rfl,rfl,rfl⟩ := by simpa using same
      refine ⟨syntaxArgs,sourceOrigin,rfl,rfl,?_,?_⟩
      · exact Prod.ext rfl rfl
      · exact (definitionEmission_run member).2
  | statement loop statement =>
    cases statement <;> simp only [Fragment.emissions] at member <;> try contradiction
    all_goals
      obtain ⟨identity,live⟩ := effectEmission_eq member
      rw [identity] at same
      contradiction
  | block loop bindings want block =>
    cases block
    obtain ⟨slot,value,origin,_,identity⟩ := initializationEmissions_shape member
    rw [identity] at same
    contradiction
  | _ => simp [Fragment.emissions] at member

theorem Fragment.replacement_emission_shape {fragment : Fragment} {env : LEnv} {before : LS} {emission : Emission}
    {owner value : Nat} {origin : Option OriginId}
    (member : emission ∈ fragment.emissions env before)
    (same : emission.instruction = .eff (.replace owner value origin)) :
    ∃ loop place expression sourceOrigin,
      fragment = .statement loop (.assignWhole place expression sourceOrigin) ∧ origin = some sourceOrigin ∧
      let addressed := lowerPlace place env before
      let cleared := emitEffect (.clear addressed.1 (some sourceOrigin)) env addressed.2
      let lowered := lowerExpr expression env cleared.2
      owner = addressed.1 ∧ value = lowered.1 ∧ emission.before = lowered.2 ∧
      emitEffect (.replace owner value origin) env emission.before = ((),emission.after) := by
  cases fragment with
  | expression expression =>
    cases expression <;> simp only [Fragment.emissions] at member <;> try contradiction
    obtain ⟨identity,_⟩ := definitionEmission_eq member
    rw [identity] at same
    contradiction
  | statement loop statement =>
    cases statement <;> simp only [Fragment.emissions] at member <;> try contradiction
    all_goals
      obtain ⟨identity,live⟩ := effectEmission_eq member
      subst emission
    all_goals try (simp at same)
    case assignWhole place expression sourceOrigin =>
      obtain ⟨rfl,rfl,rfl⟩ := by simpa using same
      refine ⟨loop,place,expression,sourceOrigin,rfl,rfl,rfl,rfl,rfl,?_⟩
      exact (effectEmission_run member).2
  | block loop bindings want block =>
    cases block
    obtain ⟨slot,value,origin,_,identity⟩ := initializationEmissions_shape member
    rw [identity] at same
    cases (Inst.eff.inj same)
  | _ => simp [Fragment.emissions] at member

theorem Fragment.slot_initialization_emission_shape {fragment : Fragment} {env : LEnv} {before : LS}
    {emission : Emission} {slot value : Nat} {origin : Option OriginId}
    (member : emission ∈ fragment.emissions env before)
    (same : emission.instruction = .eff (.slotInit slot value origin)) :
    (∃ loop expression sourceOrigin,
      fragment = .statement loop (.letS slot expression sourceOrigin) ∧ origin = some sourceOrigin) ∨
    (∃ loop bindings want block sourceOrigin,
      fragment = .block loop bindings want block ∧ (slot,value,sourceOrigin) ∈ bindings ∧ origin = some sourceOrigin) := by
  cases fragment with
  | expression expression =>
    cases expression <;> simp only [Fragment.emissions] at member <;> try contradiction
    obtain ⟨identity,_⟩ := definitionEmission_eq member
    rw [identity] at same
    contradiction
  | statement loop statement =>
    cases statement <;> simp only [Fragment.emissions] at member <;> try contradiction
    all_goals
      obtain ⟨identity,live⟩ := effectEmission_eq member
      subst emission
    all_goals try (simp at same)
    case letS slotId expression sourceOrigin =>
      obtain ⟨rfl,_,rfl⟩ := by simpa using same
      exact Or.inl ⟨loop,expression,sourceOrigin,rfl,rfl⟩
  | block loop bindings want block =>
    cases block
    obtain ⟨bindingSlot,bindingValue,bindingOrigin,bindingMember,identity⟩ := initializationEmissions_shape member
    rw [identity] at same
    obtain ⟨rfl,rfl,rfl⟩ := by simpa using same
    exact Or.inr ⟨loop,bindings,want,_,bindingOrigin,rfl,bindingMember,rfl⟩
  | _ => simp [Fragment.emissions] at member

theorem Fragment.store_emission_shape {fragment : Fragment} {env : LEnv} {before : LS}
    {emission : Emission} {address value : Nat} {origin : Option OriginId}
    (member : emission ∈ fragment.emissions env before)
    (same : emission.instruction = .eff (.store address value origin)) :
    (∃ loop place expression sourceOrigin,
      fragment = .statement loop (.assign place expression sourceOrigin) ∧ origin = some sourceOrigin) ∨
    (∃ loop operation place expression sourceOrigin,
      fragment = .statement loop (.assignOp operation place expression sourceOrigin) ∧ origin = some sourceOrigin) ∨
    (∃ loop slotId expression sourceOrigin,
      fragment = .statement loop (.rebind slotId expression sourceOrigin) ∧ origin = some sourceOrigin) := by
  cases fragment with
  | expression expression =>
    cases expression <;> simp only [Fragment.emissions] at member <;> try contradiction
    obtain ⟨identity,_⟩ := definitionEmission_eq member
    rw [identity] at same
    contradiction
  | statement loop statement =>
    cases statement <;> simp only [Fragment.emissions] at member <;> try contradiction
    all_goals
      obtain ⟨identity,live⟩ := effectEmission_eq member
      subst emission
    all_goals try (simp at same)
    case assign place expression sourceOrigin =>
      obtain ⟨_,_,rfl⟩ := by simpa using same
      exact Or.inl ⟨loop,place,expression,sourceOrigin,rfl,rfl⟩
    case assignOp operation place expression sourceOrigin =>
      obtain ⟨_,_,rfl⟩ := by simpa using same
      exact Or.inr (Or.inl ⟨loop,operation,place,expression,sourceOrigin,rfl,rfl⟩)
    case rebind slotId expression sourceOrigin =>
      obtain ⟨_,_,rfl⟩ := by simpa using same
      exact Or.inr (Or.inr ⟨loop,slotId,expression,sourceOrigin,rfl,rfl⟩)
  | block loop bindings want block =>
    cases block
    obtain ⟨slot,value,origin,_,identity⟩ := initializationEmissions_shape member
    rw [identity] at same
    cases (Inst.eff.inj same)
  | _ => simp [Fragment.emissions] at member

theorem SourceLoweringAt.replacement_rhs {root : Fragment} {env : LEnv} {initial before : LS}
    {path : List Nat} {loop : Option LoopCtx} {place : Place} {expression : Expr} {sourceOrigin : OriginId}
    (located : SourceLoweringAt root env initial path (.statement loop (.assignWhole place expression sourceOrigin)) before) :
    SourceLoweringAt root env initial (path ++ [1]) (.expression expression)
      (emitEffect (.clear (lowerPlace place env before).1 (some sourceOrigin)) env (lowerPlace place env before).2).2 := by
  apply located.child
  rfl

#print axioms Fragment.call_emission_shape
#print axioms Fragment.replacement_emission_shape
#print axioms Fragment.slot_initialization_emission_shape
#print axioms Fragment.store_emission_shape
#print axioms SourceLoweringAt.replacement_rhs

end Goose.Lower.Validation.SourceReplacementWriterLedger
