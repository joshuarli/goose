import Goose.Lower.Validation.ScopeBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ScopeMapAdvance (before : LS) (entry exit nextEntry nextExit : BlockId → List ScopeId) : Prop :=
  ∀ block, block < before.blocks.size → nextEntry block = entry block ∧
    (before.cur ≠ some block → nextExit block = exit block)

theorem ScopeMapAdvance.refl (before : LS) (entry exit : BlockId → List ScopeId) :
    ScopeMapAdvance before entry exit entry exit := fun _ _ => ⟨rfl, fun _ => rfl⟩

theorem LS_Adv.otherCurrent {before after : LS} (advance : before.Adv after)
    {block : BlockId} (old : block < before.blocks.size) (other : before.cur ≠ some block) :
    after.cur ≠ some block := by
  rcases advance.cur with closed | unchanged | ⟨current, live, fresh, bound⟩
  · rw [closed]
    simp
  · rw [unchanged]
    exact other
  · rw [live]
    intro same
    cases same
    nat_omega

theorem ScopeMapAdvance.trans {before middle : LS}
    {entry exit middleEntry middleExit afterEntry afterExit : BlockId → List ScopeId}
    (advance : before.Adv middle)
    (first : ScopeMapAdvance before entry exit middleEntry middleExit)
    (second : ScopeMapAdvance middle middleEntry middleExit afterEntry afterExit) :
    ScopeMapAdvance before entry exit afterEntry afterExit := by
  intro block old
  have middleOld := Nat.lt_of_lt_of_le old advance.ext.1
  have left := first block old
  have right := second block middleOld
  refine ⟨right.1.trans left.1, ?_⟩
  intro other
  exact (right.2 (LS_Adv.otherCurrent advance old other)).trans (left.2 other)

def ScopeLiveBound (state : LS) : Prop :=
  ∀ block, state.cur = some block → block < state.blocks.size

theorem ScopeLiveBound.advance {before after : LS}
    (bound : ScopeLiveBound before) (advance : before.Adv after) : ScopeLiveBound after := by
  intro block current
  rcases advance.cur with closed | unchanged | ⟨new, live, fresh, allocated⟩
  · rw [closed] at current
    cases current
  · exact Nat.lt_of_lt_of_le (bound block (unchanged.symm.trans current)) advance.ext.1
  · have same : new = block := Option.some.inj (live.symm.trans current)
    simpa [same] using allocated

structure ScopeAction (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (action : B α) : Prop where
  advance : AdvB action
  preserves : ∀ (env : LEnv) (before : LS) (entry exit : BlockId → List ScopeId),
    ScopeBuilder parents entry exit before → ScopeLiveBound before → before.stack.head? = parent →
    ∃ nextEntry nextExit,
      ScopeBuilder parents nextEntry nextExit (action env before).2 ∧
      ScopeMapAdvance before entry exit nextEntry nextExit

theorem ScopeAction.pure (parents : Array (Option ScopeId)) (parent : Option ScopeId) (value : α) :
    ScopeAction parents parent (pure value : B α) := by
  refine ⟨AdvB.pure _, ?_⟩
  intro env before entry exit valid bound head
  exact ⟨entry, exit, valid, ScopeMapAdvance.refl _ _ _⟩

theorem ScopeAction.bind {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    {action : B α} {next : α → B β} (first : ScopeAction parents parent action)
    (rest : ∀ value, ScopeAction parents parent (next value)) :
    ScopeAction parents parent (action >>= next) := by
  refine ⟨AdvB.bind first.advance (fun value => (rest value).advance), ?_⟩
  intro env before entry exit valid bound head
  obtain ⟨middleEntry, middleExit, middleValid, firstMaps⟩ :=
    first.preserves env before entry exit valid bound head
  have advance := first.advance env before _ _ rfl
  have middleHead : (action env before).2.stack.head? = parent := by
    rw [advance.stack]
    exact head
  obtain ⟨afterEntry, afterExit, afterValid, secondMaps⟩ :=
    (rest (action env before).1).preserves env (action env before).2 middleEntry middleExit
      middleValid (bound.advance advance) middleHead
  exact ⟨afterEntry, afterExit, afterValid, firstMaps.trans advance secondMaps⟩

theorem ScopeAction.emitDef (parents : Array (Option ScopeId)) (parent : Option ScopeId) (op : Op) :
    ScopeAction parents parent (emitDef op) := by
  refine ⟨advB_emitDef _, ?_⟩
  intro env before entry exit valid bound head
  exact ⟨entry, exit, valid.emitDef op env, ScopeMapAdvance.refl _ _ _⟩

theorem ScopeAction.emitNeutralEffect (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (effect : Effect) (neutral : scopeNeutral (.eff effect) = true) :
    ScopeAction parents parent (emitEffect effect) := by
  refine ⟨advB_emitEffect _, ?_⟩
  intro env before entry exit valid bound head
  exact ⟨entry, exit, valid.emitNeutralEffect effect neutral env, ScopeMapAdvance.refl _ _ _⟩

theorem ScopeAction.emitNeutralTerm (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (term : Term) (neutral : scopeNeutral (.term term) = true) :
    ScopeAction parents parent (emitTerm term) := by
  refine ⟨advB_emitTerm _, ?_⟩
  intro env before entry exit valid bound head
  exact ⟨entry, exit, valid.emitNeutralTerm term neutral env, ScopeMapAdvance.refl _ _ _⟩

theorem ScopeAction.get (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ScopeAction parents parent (get : B LS) := by
  refine ⟨advB_get, ?_⟩
  intro env before entry exit valid bound head
  exact ⟨entry, exit, valid, ScopeMapAdvance.refl _ _ _⟩

theorem ScopeAction.read (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ScopeAction parents parent (read : B LEnv) := by
  refine ⟨advB_read, ?_⟩
  intro env before entry exit valid bound head
  exact ⟨entry, exit, valid, ScopeMapAdvance.refl _ _ _⟩

theorem ScopeAction.observe (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (action : B α) (advance : AdvB action)
    (same : ∀ env before, (action env before).2 = before) : ScopeAction parents parent action := by
  refine ⟨advance, ?_⟩
  intro env before entry exit valid bound head
  refine ⟨entry, exit, ?_, ScopeMapAdvance.refl _ _ _⟩
  rw [same]
  exact valid

theorem ScopeAction.curBlock (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ScopeAction parents parent Goose.Lower.curBlock := by
  unfold Goose.Lower.curBlock
  exact (ScopeAction.get parents parent).bind fun state => ScopeAction.pure parents parent _

theorem ScopeAction.isLive (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ScopeAction parents parent Goose.Lower.isLive := by
  unfold Goose.Lower.isLive
  exact (ScopeAction.curBlock parents parent).bind fun current => ScopeAction.pure parents parent _

theorem ScopeAction.valTy (parents : Array (Option ScopeId)) (parent : Option ScopeId) (value : ValueId) :
    ScopeAction parents parent (Goose.Lower.valTy value) :=
  .observe parents parent _ (advB_valTy value) (valTy_run value)

theorem ScopeAction.intTyOf (parents : Array (Option ScopeId)) (parent : Option ScopeId) (value : ValueId) :
    ScopeAction parents parent (Goose.Lower.intTyOf value) := by
  unfold Goose.Lower.intTyOf
  refine (ScopeAction.valTy parents parent value).bind fun type => ?_
  cases type with
  | data type => cases type <;> exact ScopeAction.pure parents parent _
  | view _ _ => exact ScopeAction.pure parents parent _

theorem ScopeAction.freezeTo (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (mutability : Mutability) (value : ValueId) : ScopeAction parents parent (Goose.Lower.freezeTo mutability value) := by
  unfold Goose.Lower.freezeTo
  refine (ScopeAction.valTy parents parent value).bind fun type => ?_
  cases mutability <;> cases type <;> first
    | exact ScopeAction.pure parents parent _
    | (rename_i type; cases type <;> first
      | exact ScopeAction.pure parents parent _
      | (rename_i mutability type; cases mutability <;> first
        | exact ScopeAction.pure parents parent _
        | exact ScopeAction.emitDef parents parent _))

theorem ScopeAction.coerceTo (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (target : Ty) (value : ValueId) (origin : OriginId) :
    ScopeAction parents parent (Goose.Lower.coerceTo target value origin) := by
  unfold Goose.Lower.coerceTo
  refine (ScopeAction.valTy parents parent value).bind fun source => ?_
  split
  · exact ScopeAction.emitDef parents parent _
  · exact (ScopeAction.emitDef parents parent _).bind fun _ => ScopeAction.emitDef parents parent _
  · exact ScopeAction.pure parents parent _

theorem ScopeAction.coerceSlot (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (slot : SlotId) (value : ValueId) (origin : OriginId) :
    ScopeAction parents parent (Goose.Lower.coerceSlot slot value origin) := by
  unfold Goose.Lower.coerceSlot
  refine (ScopeAction.read parents parent).bind fun env => ?_
  cases env.slots[slot]? with
  | none => exact ScopeAction.pure parents parent _
  | some destination => exact ScopeAction.coerceTo parents parent _ _ _

theorem ScopeAction.coerceResult (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (value : ValueId) (origin : OriginId) : ScopeAction parents parent (Goose.Lower.coerceResult value origin) := by
  unfold Goose.Lower.coerceResult
  refine (ScopeAction.read parents parent).bind fun env => ?_
  cases env.results.head? with
  | none => exact ScopeAction.pure parents parent _
  | some destination => exact ScopeAction.coerceTo parents parent _ _ _

theorem ScopeAction.growOwner (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (value : ValueId) : ScopeAction parents parent (Goose.Lower.growOwner value) := by
  unfold Goose.Lower.growOwner
  refine (ScopeAction.valTy parents parent value).bind fun type => ?_
  cases type with
  | data type => cases type <;> first
    | exact ScopeAction.pure parents parent _
    | (rename_i mutability target; cases target <;> exact ScopeAction.pure parents parent _)
  | view _ _ => exact ScopeAction.pure parents parent _

theorem ScopeAction.initSlots (parents : Array (Option ScopeId)) (parent : Option ScopeId) :
    ∀ slots, ScopeAction parents parent (Goose.Lower.initSlots slots)
  | [] => ScopeAction.pure parents parent _
  | (slot, value, origin) :: rest =>
    (ScopeAction.emitNeutralEffect parents parent (.slotInit slot value (some origin)) rfl).bind
      fun _ => ScopeAction.initSlots parents parent rest

end Goose.Lower.Validation
