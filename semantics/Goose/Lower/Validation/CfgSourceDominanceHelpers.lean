import Goose.Lower.Validation.CfgSourceDominancePrimitives

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ssa_pure (loop : Option LoopCtx) (value : α) :
    SSARun loop [] (fun _ => []) (pure value) :=
  SSARun.pure loop value [] (fun _ => []) (by simp)

theorem ssa_value (loop : Option LoopCtx) (value : ValueId) :
    SSARun loop [value] (fun result => [result]) (pure value) :=
  SSARun.pure loop value [value] (fun result => [result]) (fun _ member => member)

theorem ssa_intTyOf (loop : Option LoopCtx) (value : ValueId) :
    SSARun loop [] (fun _ => []) (intTyOf value) := by
  unfold intTyOf
  refine SSARun.bind (ssa_valTy loop value) fun type => ?_
  cases type with
  | data type => cases type <;> exact ssa_pure loop _
  | view _ _ => exact ssa_pure loop _

theorem ssa_freezeTo (loop : Option LoopCtx) (mu : Mutability) (value : ValueId) :
    SSARun loop [value] (fun result => [result]) (freezeTo mu value) := by
  unfold freezeTo
  refine SSARun.bind ((ssa_valTy loop value).keep [value]) fun type => ?_
  cases mu <;> cases type <;> first
    | exact ssa_value loop value
    | (rename_i type; cases type <;> first
      | exact ssa_value loop value
      | (rename_i mu _; cases mu <;> first | exact ssa_value loop value | exact ssa_emitDef loop _))

theorem ssa_coerceTo (loop : Option LoopCtx) (target : Ty) (value : ValueId) (origin : OriginId) :
    SSARun loop [value] (fun result => [result]) (coerceTo target value origin) := by
  unfold coerceTo
  refine SSARun.bind ((ssa_valTy loop value).keep [value]) fun type => ?_
  split
  · exact ssa_emitDef loop _
  · exact SSARun.bind (ssa_emitDef loop _) fun view => ssa_emitDef loop _
  · exact ssa_value loop value

theorem ssa_coerceSlot (loop : Option LoopCtx) (slot value : Nat) (origin : OriginId) :
    SSARun loop [value] (fun result => [result]) (coerceSlot slot value origin) := by
  unfold coerceSlot
  refine SSARun.bind ((ssa_read loop).keep [value]) fun env => ?_
  cases env.slots[slot]? with
  | none => exact ssa_value loop value
  | some destination => exact ssa_coerceTo loop destination.ty value origin

theorem ssa_coerceResult (loop : Option LoopCtx) (value : ValueId) (origin : OriginId) :
    SSARun loop [value] (fun result => [result]) (coerceResult value origin) := by
  unfold coerceResult
  refine SSARun.bind ((ssa_read loop).keep [value]) fun env => ?_
  cases env.results.head? with
  | none => exact ssa_value loop value
  | some destination => exact ssa_coerceTo loop destination value origin

theorem ssa_growOwner (loop : Option LoopCtx) (value : ValueId) :
    SSARun loop [] (fun _ => []) (growOwner value) := by
  unfold growOwner
  refine SSARun.bind (ssa_valTy loop value) fun type => ?_
  cases type with
  | data type => cases type <;> first
    | exact ssa_pure loop _
    | (rename_i mu type; cases type <;> exact ssa_pure loop _)
  | view _ _ => exact ssa_pure loop _

theorem ssa_regrowOf (loop : Option LoopCtx) (owner : Option ValueId) :
    SSARun loop [] (fun _ => []) (regrowOf owner) := by
  cases owner with
  | none => exact ssa_pure loop _
  | some value => exact ssa_growOwner loop value

theorem ssa_leaveAll (loop : Option LoopCtx) : ∀ scopes,
    SSARun loop [] (fun _ => []) (leaveAll scopes)
  | [] => ssa_pure loop _
  | scope :: rest => by
    unfold leaveAll
    exact SSARun.bind (ssa_emitEffect loop _) fun _ => ssa_leaveAll loop rest

theorem ssa_leaveTo (loop : Option LoopCtx) (depth : Nat) :
    SSARun loop [] (fun _ => []) (leaveTo depth) := by
  unfold leaveTo
  exact SSARun.bind (ssa_get loop) fun _ => ssa_leaveAll loop _

theorem ssa_initSlots (loop : Option LoopCtx) : ∀ pre,
    SSARun loop (pre.map fun entry => entry.2.1) (fun _ => []) (initSlots pre)
  | [] => ssa_pure loop _
  | (slot, value, origin) :: rest => by
    unfold initSlots
    apply SSARun.weaken
      (SSARun.bind ((ssa_emitEffect loop (.slotInit slot value (some origin))).keep
        (rest.map fun entry => entry.2.1)) fun _ => by
          simpa only [List.append_nil] using ssa_initSlots loop rest)
    intro used member
    simpa [Effect.uses, List.mem_cons, or_comm] using member

theorem ssa_eachElemValue (loop : Option LoopCtx) (var : VarId) (byRef : Bool) (elem : ValueId) :
    SSARun loop [elem] (fun result => [result]) (eachElemValue var byRef elem) := by
  unfold eachElemValue
  cases byRef with
  | false => exact ssa_emitDef loop _
  | true =>
    refine SSARun.bind ((ssa_read loop).keep [elem]) fun env => ?_
    cases env.vars[var]? with
    | none => exact ssa_value loop elem
    | some localVar =>
      dsimp only
      cases localVar.ty with
      | ref mu type => exact ssa_freezeTo loop mu elem
      | _ => exact ssa_value loop elem

theorem ssa_whenLive (loop : Option LoopCtx) (default : α) (inputs : List ValueId)
    (outputs : α → List ValueId) {action : BlockId → B α}
    (body : ∀ block, SSARun loop inputs outputs (action block)) :
    SSARun loop inputs outputs (whenLive default action) := by
  intro env before result after run imports checked ready arguments
  cases current : before.cur with
  | none =>
    simp only [whenLive, bind_run, curBlock_run, current] at run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    exact ⟨imports, SSAResult.of_current checked (.refl before) (Or.inr rfl)
      (by simp [AvailableValues, current])⟩
  | some block =>
    simp only [whenLive, bind_run, curBlock_run, current] at run
    exact body block env before result after run imports checked ready arguments

end Goose.Lower.Validation
