import Goose.Lower.Validation.EmittedMetadataStaticResolved

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

section
variable {module : Core.Module} {le : LEnv} (tables : EmittedStaticTables module le)
include tables

theorem resolved_inScope (scope : ScopeId) {action : B α} (typed : EmittedResolvedRun module le action) :
    EmittedResolvedRun module le (inScope scope action) := by
  unfold inScope
  exact EmittedResolvedRun.bind (resolved_pushScope module le _) fun _ =>
    EmittedResolvedRun.bind typed fun _ => EmittedResolvedRun.bind (resolved_popScope module le) fun _ => EmittedResolvedRun.pure module le _

theorem resolved_whenLive (default : α) {action : BlockId → B α}
    (typed : ∀ block, EmittedResolvedRun module le (action block)) : EmittedResolvedRun module le (whenLive default action) := by
  unfold whenLive
  refine EmittedResolvedRun.bind (resolved_curBlock module le) fun current => ?_
  cases current
  · exact EmittedResolvedRun.pure module le _
  · exact typed _

theorem resolved_intTyOf (v : ValueId) : EmittedResolvedRun module le (intTyOf v) := by
  unfold intTyOf
  refine EmittedResolvedRun.bind (resolved_valTy module le v) fun t => ?_
  cases t with
  | data t => cases t <;> exact EmittedResolvedRun.pure module le _
  | view _ _ => exact EmittedResolvedRun.pure module le _

theorem resolved_freezeTo (m : Mutability) (r : ValueId) : EmittedResolvedRun module le (freezeTo m r) := by
  unfold freezeTo
  refine EmittedResolvedRun.bind (resolved_valTy module le r) fun t => ?_
  cases m <;> cases t <;> first
    | exact EmittedResolvedRun.pure module le _
    | (rename_i t; cases t <;> first | exact EmittedResolvedRun.pure module le _ | (rename_i m' _; cases m' <;> first | exact EmittedResolvedRun.pure module le _ | exact resolved_emitDef tables _ (fun _ => trivial)))

theorem resolved_borrowTo (m : Mutability) (r : ValueId) : EmittedResolvedRun module le (borrowTo m r) := by
  intro before result after run checked
  rcases borrowTo_cases run with frozen | borrowed
  · exact resolved_freezeTo tables m r before result after frozen checked
  · exact resolved_emitDef tables (.ownerBorrow r) (fun _ => trivial) before result after borrowed checked

theorem resolved_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : EmittedResolvedRun module le (coerceTo target r org) := by
  unfold coerceTo
  refine EmittedResolvedRun.bind (resolved_valTy module le r) fun source => ?_
  split
  · exact resolved_emitDef tables _ (fun _ => trivial)
  · exact EmittedResolvedRun.bind (resolved_emitDef tables _ (fun _ => trivial)) (fun _ => resolved_emitDef tables _ (fun _ => trivial))
  · exact EmittedResolvedRun.pure module le _

theorem resolved_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    EmittedResolvedRun module le (coerceSlot slot value org) := by
  unfold coerceSlot
  refine EmittedResolvedRun.bind (resolved_read module le) fun readEnv => ?_
  cases readEnv.slots[slot]? with
  | none => exact EmittedResolvedRun.pure module le _
  | some destination => exact resolved_coerceTo tables destination.ty value org

theorem resolved_coerceResult (value : ValueId) (org : OriginId) :
    EmittedResolvedRun module le (coerceResult value org) := by
  unfold coerceResult
  refine EmittedResolvedRun.bind (resolved_read module le) fun readEnv => ?_
  cases readEnv.results.head? with
  | none => exact EmittedResolvedRun.pure module le _
  | some destination => exact resolved_coerceTo tables destination value org

theorem resolved_growOwner (r : ValueId) : EmittedResolvedRun module le (growOwner r) := by
  unfold growOwner
  refine EmittedResolvedRun.bind (resolved_valTy module le r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact EmittedResolvedRun.pure module le _ | (rename_i m' t'; cases t' <;> exact EmittedResolvedRun.pure module le _)
  | view _ _ => exact EmittedResolvedRun.pure module le _

theorem resolved_leaveAll : ∀ scs, EmittedResolvedRun module le (leaveAll scs)
  | [] => EmittedResolvedRun.pure module le _
  | sc :: rest => by
    unfold leaveAll
    exact EmittedResolvedRun.bind (resolved_emitEffect _) fun _ => resolved_leaveAll rest

theorem resolved_leaveTo (d : Nat) : EmittedResolvedRun module le (leaveTo d) := by
  unfold leaveTo
  exact EmittedResolvedRun.bind (resolved_get module le) fun _ => resolved_leaveAll tables _

theorem resolved_initSlots : ∀ ps, EmittedResolvedRun module le (initSlots ps)
  | [] => EmittedResolvedRun.pure module le _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact EmittedResolvedRun.bind (resolved_emitEffect _) fun _ => resolved_initSlots rest

theorem resolved_isLive : EmittedResolvedRun module le isLive := by
  unfold isLive
  exact EmittedResolvedRun.bind (resolved_curBlock module le) fun _ => EmittedResolvedRun.pure module le _

theorem resolved_eachElemValue (x : VarId) (byRef : Bool) (elem : ValueId) :
    EmittedResolvedRun module le (eachElemValue x byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact resolved_emitDef tables _ (fun _ => trivial)
  · refine EmittedResolvedRun.bind (resolved_read module le) fun readEnv => ?_
    cases readEnv.vars[x]? with
    | none => exact EmittedResolvedRun.pure module le _
    | some lv =>
      dsimp only
      cases lv.ty with
      | ref m t => exact resolved_borrowTo tables m elem
      | _ => exact EmittedResolvedRun.pure module le _

theorem resolved_regrowOf (o : Option ValueId) : EmittedResolvedRun module le (regrowOf o) := by
  cases o with
  | none => exact EmittedResolvedRun.pure module le _
  | some r => exact resolved_growOwner tables r

theorem resolved_eachSampled (regrow : Bool) (vw : ValueId) : EmittedResolvedRun module le (eachSampled regrow vw) := by
  unfold eachSampled
  cases regrow
  · exact resolved_emitDef tables _ (fun _ => trivial)
  · exact EmittedResolvedRun.pure module le _

theorem resolved_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    EmittedResolvedRun module le (eachLen regrow owner sampled) := by
  unfold eachLen
  cases regrow
  · exact EmittedResolvedRun.pure module le _
  · exact resolved_emitDef tables _ (fun _ => trivial)

theorem resolved_fork (condition : ValueId) : EmittedResolvedRun module le (fork condition) := by
  unfold fork
  exact EmittedResolvedRun.bind (resolved_newBlock _ (by simp [EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure])) fun ⟨thenBlock, _⟩ =>
    EmittedResolvedRun.bind (resolved_newBlock _ (by simp [EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure])) fun ⟨elseBlock, _⟩ =>
    EmittedResolvedRun.bind (resolved_emitTerm _) fun _ => EmittedResolvedRun.pure module le _

theorem resolved_patchBrs (target : BlockId) : ∀ incoming, EmittedResolvedRun module le (patchBrs target incoming)
  | [] => EmittedResolvedRun.pure module le _
  | (block, value) :: rest => by
    unfold patchBrs
    exact EmittedResolvedRun.bind (resolved_patchTerm _ _) fun _ => resolved_patchBrs target rest

theorem resolved_patchBrs0 (target : BlockId) : ∀ incoming, EmittedResolvedRun module le (patchBrs0 target incoming)
  | [] => EmittedResolvedRun.pure module le _
  | block :: rest => by
    unfold patchBrs0
    exact EmittedResolvedRun.bind (resolved_patchTerm _ _) fun _ => resolved_patchBrs0 target rest

theorem resolved_joinValue (endT : Option BlockId) (vt : ValueId)
    (endF : Option BlockId) (vf : ValueId) :
    EmittedResolvedRun module le (joinValue endT vt endF vf) := by
  unfold joinValue
  cases endT <;> cases endF
  · exact EmittedResolvedRun.bind (resolved_setCur module le _) fun _ =>
      EmittedResolvedRun.pure module le _
  all_goals
    intro before result after run checked
    obtain ⟨type, middle, typeRun, tail⟩ := bind_eq.mp run
    have same := congrArg Prod.snd typeRun
    simp only [valTy_run] at same
    subst middle
    have valid : EmittedVTyResolved module type := by
      have sameType := congrArg Prod.fst typeRun
      dsimp only at sameType
      exact sameType ▸ checked.valTy le _
    exact (EmittedResolvedRun.bind (resolved_newBlock [type] (by simpa using valid)) fun ⟨_, _⟩ =>
      EmittedResolvedRun.bind (resolved_patchBrs tables _ _) fun _ =>
      EmittedResolvedRun.bind (resolved_setCur module le _) fun _ =>
      EmittedResolvedRun.pure module le _) _ _ _ tail checked

theorem resolved_joinArms (endT endF : Option BlockId) : EmittedResolvedRun module le (joinArms endT endF) := by
  unfold joinArms
  cases endT <;> cases endF
  · exact resolved_setCur module le _
  all_goals
    exact EmittedResolvedRun.bind (resolved_newBlock _ (by simp [EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure])) fun ⟨_, _⟩ =>
      EmittedResolvedRun.bind (resolved_patchBrs0 tables _ _) fun _ => resolved_setCur module le _

theorem resolved_scFork (isAnd : Bool) (value : ValueId) : EmittedResolvedRun module le (scFork isAnd value) := by
  unfold scFork
  refine EmittedResolvedRun.bind (resolved_newBlock _ (by simp [EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure])) fun ⟨_, _⟩ =>
    EmittedResolvedRun.bind (resolved_newBlock _ (by simp [EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure])) fun ⟨_, _⟩ => ?_
  cases isAnd <;> exact EmittedResolvedRun.bind (resolved_emitTerm _) fun _ => EmittedResolvedRun.pure module le _

theorem resolved_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (typed : EmittedResolvedRun module le rhs) : EmittedResolvedRun module le (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  exact resolved_whenLive tables _ fun _ =>
    EmittedResolvedRun.bind (resolved_scFork tables _ _) fun ⟨_, _, _⟩ =>
    EmittedResolvedRun.bind (resolved_setCur module le _) fun _ => EmittedResolvedRun.bind typed fun _ =>
    EmittedResolvedRun.bind (resolved_emitTerm _) fun _ =>
    EmittedResolvedRun.bind (resolved_setCur module le _) fun _ => EmittedResolvedRun.pure module le _

theorem resolved_loopBody (cv : ValueId) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (hbody : ∀ depth exitBlock, EmittedResolvedRun module le (body depth exitBlock)) (hback : EmittedResolvedRun module le back) :
    EmittedResolvedRun module le (loopBody cv body back) := by
  unfold loopBody
  exact EmittedResolvedRun.bind (resolved_get module le) fun _ =>
    EmittedResolvedRun.bind (resolved_fork tables _) fun ⟨_, _⟩ =>
    EmittedResolvedRun.bind (resolved_setCur module le _) fun _ => EmittedResolvedRun.bind (hbody _ _) fun _ =>
    EmittedResolvedRun.bind hback fun _ => resolved_setCur module le _

theorem resolved_rangeBack (t : IntTy) (i : ValueId) (hb : BlockId) : EmittedResolvedRun module le (rangeBack t i hb) := by
  unfold rangeBack
  refine EmittedResolvedRun.bind (resolved_isLive tables) fun live => ?_
  cases live
  · exact EmittedResolvedRun.pure module le _
  · exact EmittedResolvedRun.bind (resolved_emitDef tables _ (fun _ => trivial)) fun _ => resolved_emitTerm _


theorem resolved_lowerWhile (hb : BlockId) {cond : B ValueId} {body : Nat → BlockId → B ValueId}
    (hc : EmittedResolvedRun module le cond) (hbody : ∀ d xb, EmittedResolvedRun module le (body d xb)) : EmittedResolvedRun module le (lowerWhile hb cond body) := by
  unfold lowerWhile
  exact EmittedResolvedRun.bind hc fun cv => resolved_whenLive tables _ fun _ =>
    resolved_loopBody tables cv hbody (resolved_emitTerm _)

theorem resolved_lowerRange (t : IntTy) (i b : ValueId) (hb : BlockId) {body : Nat → BlockId → B ValueId}
    (hbody : ∀ d xb, EmittedResolvedRun module le (body d xb)) : EmittedResolvedRun module le (lowerRange t i b hb body) := by
  unfold lowerRange
  exact EmittedResolvedRun.bind (resolved_emitDef tables _ (fun _ => trivial)) fun c => resolved_loopBody tables c hbody (resolved_rangeBack tables _ _ _)

theorem resolved_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (hb : BlockId)
    (i : ValueId) {body : Nat → BlockId → B ValueId} (hbody : ∀ d xb, EmittedResolvedRun module le (body d xb)) :
    EmittedResolvedRun module le (lowerEach regrow owner sampled hb i body) := by
  unfold lowerEach
  exact EmittedResolvedRun.bind (resolved_eachLen tables _ _ _) fun n => EmittedResolvedRun.bind (resolved_emitDef tables _ (fun _ => trivial)) fun c =>
    resolved_loopBody tables c hbody (resolved_rangeBack tables _ _ _)

omit tables in
theorem resolved_recordValueRootRecipe (value : ValueId) (sourceScope : ScopeId) :
    EmittedResolvedRun module le (recordValueRootRecipe value sourceScope) := by
  apply EmittedResolvedRun.of_unchanged
  all_goals intro before; rw [recordValueRootRecipe_run]

omit tables in
theorem resolved_recordReadValueRootRecipe (value : ValueId) (place : Place) :
    EmittedResolvedRun module le (recordReadValueRootRecipe value place) := by
  apply EmittedResolvedRun.of_unchanged
  all_goals
    intro before
    cases place <;> simp only [recordReadValueRootRecipe_run]
    split <;> simp [recordValueRootSource_run]

theorem resolved_ifE_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : EmittedResolvedRun module le a1) (h2 : EmittedResolvedRun module le a2) :
    EmittedResolvedRun module le (whenLive 0 fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let vt ← a1
      let endT ← curBlock
      setCur (some eb)
      let vf ← a2
      let endF ← curBlock
      joinValue endT vt endF vf) := by
  exact resolved_whenLive tables _ fun _ =>
    EmittedResolvedRun.bind (resolved_fork tables _) fun ⟨_, _⟩ =>
    EmittedResolvedRun.bind (resolved_setCur module le _) fun _ => EmittedResolvedRun.bind h1 fun _ =>
    EmittedResolvedRun.bind (resolved_curBlock module le) fun _ => EmittedResolvedRun.bind (resolved_setCur module le _) fun _ =>
    EmittedResolvedRun.bind h2 fun _ => EmittedResolvedRun.bind (resolved_curBlock module le) fun _ => resolved_joinValue tables _ _ _ _

theorem resolved_ifE_recorded_core (cv : ValueId) (sourceScope : ScopeId) {a1 a2 : B ValueId} (h1 : EmittedResolvedRun module le a1) (h2 : EmittedResolvedRun module le a2) :
    EmittedResolvedRun module le (whenLive 0 fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let vt ← a1
      let endT ← curBlock
      setCur (some eb)
      let vf ← a2
      let endF ← curBlock
      let value ← joinValue endT vt endF vf
      recordValueRootRecipe value sourceScope
      Pure.pure value) := by
  exact resolved_whenLive tables _ fun _ =>
    EmittedResolvedRun.bind (resolved_fork tables _) fun ⟨_, _⟩ =>
    EmittedResolvedRun.bind (resolved_setCur module le _) fun _ => EmittedResolvedRun.bind h1 fun _ =>
    EmittedResolvedRun.bind (resolved_curBlock module le) fun _ => EmittedResolvedRun.bind (resolved_setCur module le _) fun _ =>
    EmittedResolvedRun.bind h2 fun _ => EmittedResolvedRun.bind (resolved_curBlock module le) fun _ =>
      EmittedResolvedRun.bind (resolved_joinValue tables _ _ _ _) fun value =>
      EmittedResolvedRun.bind (resolved_recordValueRootRecipe (module := module) (le := le) value sourceScope) fun _ =>
      EmittedResolvedRun.pure module le value

theorem resolved_ifS_some_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : EmittedResolvedRun module le a1) (h2 : EmittedResolvedRun module le a2) :
    EmittedResolvedRun module le (whenLive () fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let _ ← a1
      let endT ← curBlock
      setCur (some eb)
      let _ ← a2
      let endF ← curBlock
      joinArms endT endF) := by
  exact resolved_whenLive tables _ fun _ =>
    EmittedResolvedRun.bind (resolved_fork tables _) fun ⟨_, _⟩ =>
    EmittedResolvedRun.bind (resolved_setCur module le _) fun _ => EmittedResolvedRun.bind h1 fun _ =>
    EmittedResolvedRun.bind (resolved_curBlock module le) fun _ => EmittedResolvedRun.bind (resolved_setCur module le _) fun _ =>
    EmittedResolvedRun.bind h2 fun _ => EmittedResolvedRun.bind (resolved_curBlock module le) fun _ => resolved_joinArms tables _ _

theorem resolved_ifS_none_core (cv : ValueId) {a1 : B ValueId} (h1 : EmittedResolvedRun module le a1) :
    EmittedResolvedRun module le (whenLive () fun _ => do
      let (tb, jb) ← fork cv
      setCur (some tb)
      let _ ← a1
      emitTerm (.br jb [])
      setCur (some jb)) := by
  exact resolved_whenLive tables _ fun _ =>
    EmittedResolvedRun.bind (resolved_fork tables _) fun ⟨_, _⟩ =>
    EmittedResolvedRun.bind (resolved_setCur module le _) fun _ => EmittedResolvedRun.bind h1 fun _ =>
    EmittedResolvedRun.bind (resolved_emitTerm _) fun _ => resolved_setCur module le _

theorem resolved_assert_core (cv : ValueId) (org : OriginId) :
    EmittedResolvedRun module le (whenLive () fun _ => do
      let (pb, fb) ← fork cv
      setCur (some fb)
      emitTerm (.abort .assert (some org))
      setCur (some pb)) := by
  exact resolved_whenLive tables _ fun _ =>
    EmittedResolvedRun.bind (resolved_fork tables _) fun ⟨_, _⟩ =>
    EmittedResolvedRun.bind (resolved_setCur module le _) fun _ => EmittedResolvedRun.bind (resolved_emitTerm _) fun _ => resolved_setCur module le _

theorem resolved_header0 {tail : BlockId → B Unit} (ht : ∀ h, EmittedResolvedRun module le (tail h)) :
    EmittedResolvedRun module le (do
      let (hb, _) ← newBlock []
      emitTerm (.br hb [])
      setCur (some hb)
      tail hb) := by
  exact EmittedResolvedRun.bind (resolved_newBlock _ (by simp [EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure])) fun ⟨_, _⟩ =>
    EmittedResolvedRun.bind (resolved_emitTerm _) fun _ => EmittedResolvedRun.bind (resolved_setCur module le _) fun _ => ht _


theorem resolved_header1 (type : VTy) (value : ValueId)
    (resolved : EmittedVTyResolved module type) {tail : BlockId → ValueId → B Unit}
    (typed : ∀ header counter, EmittedResolvedRun module le (tail header counter)) :
    EmittedResolvedRun module le (do
      let (header, parameters) ← newBlock [type]
      let counter := parameters.headD 0
      emitTerm (.br header [value])
      setCur (some header)
      tail header counter) := by
  exact EmittedResolvedRun.bind (resolved_newBlock [type] (by simpa using resolved)) fun ⟨_, _⟩ =>
    EmittedResolvedRun.bind (resolved_emitTerm _) fun _ =>
    EmittedResolvedRun.bind (resolved_setCur module le _) fun _ => typed _ _

end

end Goose.Lower.Validation
