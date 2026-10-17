import Goose.Lower.Validation.EmittedMetadataStaticState

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

section
variable {module : Core.Module} {le : LEnv} (tables : EmittedStaticTables module le)
include tables

theorem staticState_inScope (scope : ScopeId) {action : B α} (typed : EmittedStaticStateRun module le action) :
    EmittedStaticStateRun module le (inScope scope action) := by
  unfold inScope
  exact EmittedStaticStateRun.bind (staticState_pushScope module le _) fun _ =>
    EmittedStaticStateRun.bind typed fun _ => EmittedStaticStateRun.bind (staticState_popScope module le) fun _ => EmittedStaticStateRun.pure module le _

theorem staticState_whenLive (default : α) {action : BlockId → B α}
    (typed : ∀ block, EmittedStaticStateRun module le (action block)) : EmittedStaticStateRun module le (whenLive default action) := by
  unfold whenLive
  refine EmittedStaticStateRun.bind (staticState_curBlock module le) fun current => ?_
  cases current
  · exact EmittedStaticStateRun.pure module le _
  · exact typed _

theorem staticState_intTyOf (v : ValueId) : EmittedStaticStateRun module le (intTyOf v) := by
  unfold intTyOf
  refine EmittedStaticStateRun.bind (staticState_valTy module le v) fun t => ?_
  cases t with
  | data t => cases t <;> exact EmittedStaticStateRun.pure module le _
  | view _ _ => exact EmittedStaticStateRun.pure module le _

theorem staticState_freezeTo (m : Mutability) (r : ValueId) : EmittedStaticStateRun module le (freezeTo m r) := by
  unfold freezeTo
  refine EmittedStaticStateRun.bind (staticState_valTy module le r) fun t => ?_
  cases m <;> cases t <;> first
    | exact EmittedStaticStateRun.pure module le _
    | (rename_i t; cases t <;> first | exact EmittedStaticStateRun.pure module le _ | (rename_i m' _; cases m' <;> first | exact EmittedStaticStateRun.pure module le _ | exact staticState_emitDef tables _ (fun _ => trivial) (fun _ => trivial)))

theorem staticState_borrowTo (m : Mutability) (r : ValueId) : EmittedStaticStateRun module le (borrowTo m r) := by
  intro before result after run checked
  rcases borrowTo_cases run with frozen | borrowed
  · exact staticState_freezeTo tables m r before result after frozen checked
  · exact staticState_emitDef tables (.ownerBorrow r) (fun _ => trivial) (fun _ => trivial) before result after borrowed checked

theorem staticState_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : EmittedStaticStateRun module le (coerceTo target r org) := by
  unfold coerceTo
  refine EmittedStaticStateRun.bind (staticState_valTy module le r) fun source => ?_
  split
  · exact staticState_emitDef tables _ (fun _ => trivial) (fun _ => trivial)
  · exact EmittedStaticStateRun.bind (staticState_emitDef tables _ (fun _ => trivial) (fun _ => trivial)) (fun _ => staticState_emitDef tables _ (fun _ => trivial) (fun _ => trivial))
  · exact EmittedStaticStateRun.pure module le _

theorem staticState_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    EmittedStaticStateRun module le (coerceSlot slot value org) := by
  unfold coerceSlot
  refine EmittedStaticStateRun.bind (staticState_read module le) fun readEnv => ?_
  cases readEnv.slots[slot]? with
  | none => exact EmittedStaticStateRun.pure module le _
  | some destination => exact staticState_coerceTo tables destination.ty value org

theorem staticState_coerceResult (value : ValueId) (org : OriginId) :
    EmittedStaticStateRun module le (coerceResult value org) := by
  unfold coerceResult
  refine EmittedStaticStateRun.bind (staticState_read module le) fun readEnv => ?_
  cases readEnv.results.head? with
  | none => exact EmittedStaticStateRun.pure module le _
  | some destination => exact staticState_coerceTo tables destination value org

theorem staticState_growOwner (r : ValueId) : EmittedStaticStateRun module le (growOwner r) := by
  unfold growOwner
  refine EmittedStaticStateRun.bind (staticState_valTy module le r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact EmittedStaticStateRun.pure module le _ | (rename_i m' t'; cases t' <;> exact EmittedStaticStateRun.pure module le _)
  | view _ _ => exact EmittedStaticStateRun.pure module le _

theorem staticState_leaveAll : ∀ scs, EmittedStaticStateRun module le (leaveAll scs)
  | [] => EmittedStaticStateRun.pure module le _
  | sc :: rest => by
    unfold leaveAll
    exact EmittedStaticStateRun.bind (staticState_emitEffect _ trivial) fun _ => staticState_leaveAll rest

theorem staticState_leaveTo (d : Nat) : EmittedStaticStateRun module le (leaveTo d) := by
  unfold leaveTo
  exact EmittedStaticStateRun.bind (staticState_get module le) fun _ => staticState_leaveAll tables _

theorem staticState_initSlots : ∀ ps, EmittedStaticStateRun module le (initSlots ps)
  | [] => EmittedStaticStateRun.pure module le _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact EmittedStaticStateRun.bind (staticState_emitEffect _ trivial) fun _ => staticState_initSlots rest

theorem staticState_isLive : EmittedStaticStateRun module le isLive := by
  unfold isLive
  exact EmittedStaticStateRun.bind (staticState_curBlock module le) fun _ => EmittedStaticStateRun.pure module le _

theorem staticState_eachElemValue (x : VarId) (byRef : Bool) (elem : ValueId) :
    EmittedStaticStateRun module le (eachElemValue x byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact staticState_emitDef tables _ (fun _ => trivial) (fun _ => trivial)
  · refine EmittedStaticStateRun.bind (staticState_read module le) fun readEnv => ?_
    cases readEnv.vars[x]? with
    | none => exact EmittedStaticStateRun.pure module le _
    | some lv =>
      dsimp only
      cases lv.ty with
      | ref m t => exact staticState_borrowTo tables m elem
      | _ => exact EmittedStaticStateRun.pure module le _

theorem staticState_regrowOf (o : Option ValueId) : EmittedStaticStateRun module le (regrowOf o) := by
  cases o with
  | none => exact EmittedStaticStateRun.pure module le _
  | some r => exact staticState_growOwner tables r

theorem staticState_eachSampled (regrow : Bool) (vw : ValueId) : EmittedStaticStateRun module le (eachSampled regrow vw) := by
  unfold eachSampled
  cases regrow
  · exact staticState_emitDef tables _ (fun _ => trivial) (fun _ => trivial)
  · exact EmittedStaticStateRun.pure module le _

theorem staticState_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    EmittedStaticStateRun module le (eachLen regrow owner sampled) := by
  unfold eachLen
  cases regrow
  · exact EmittedStaticStateRun.pure module le _
  · exact staticState_emitDef tables _ (fun _ => trivial) (fun _ => trivial)

theorem staticState_fork (condition : ValueId) : EmittedStaticStateRun module le (fork condition) := by
  unfold fork
  exact EmittedStaticStateRun.bind (staticState_newBlock _ (by simp [EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure])) fun ⟨thenBlock, _⟩ =>
    EmittedStaticStateRun.bind (staticState_newBlock _ (by simp [EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure])) fun ⟨elseBlock, _⟩ =>
    EmittedStaticStateRun.bind (staticState_emitTerm _ (by simp [EmittedProfileInst])) fun _ => EmittedStaticStateRun.pure module le _

theorem staticState_patchBrs (target : BlockId) : ∀ incoming, EmittedStaticStateRun module le (patchBrs target incoming)
  | [] => EmittedStaticStateRun.pure module le _
  | (block, value) :: rest => by
    unfold patchBrs
    exact EmittedStaticStateRun.bind (staticState_patchTerm _ _ (by simp [EmittedProfileInst])) fun _ => staticState_patchBrs target rest

theorem staticState_patchBrs0 (target : BlockId) : ∀ incoming, EmittedStaticStateRun module le (patchBrs0 target incoming)
  | [] => EmittedStaticStateRun.pure module le _
  | block :: rest => by
    unfold patchBrs0
    exact EmittedStaticStateRun.bind (staticState_patchTerm _ _ (by simp [EmittedProfileInst])) fun _ => staticState_patchBrs0 target rest

theorem staticState_joinValue (endT : Option BlockId) (vt : ValueId)
    (endF : Option BlockId) (vf : ValueId) :
    EmittedStaticStateRun module le (joinValue endT vt endF vf) := by
  unfold joinValue
  cases endT <;> cases endF
  · exact EmittedStaticStateRun.bind (staticState_setCur module le _) fun _ =>
      EmittedStaticStateRun.pure module le _
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
    exact (EmittedStaticStateRun.bind (staticState_newBlock [type] (by simpa using valid)) fun ⟨_, _⟩ =>
      EmittedStaticStateRun.bind (staticState_patchBrs tables _ _) fun _ =>
      EmittedStaticStateRun.bind (staticState_setCur module le _) fun _ =>
      EmittedStaticStateRun.pure module le _) _ _ _ tail checked

theorem staticState_joinArms (endT endF : Option BlockId) : EmittedStaticStateRun module le (joinArms endT endF) := by
  unfold joinArms
  cases endT <;> cases endF
  · exact staticState_setCur module le _
  all_goals
    exact EmittedStaticStateRun.bind (staticState_newBlock _ (by simp [EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure])) fun ⟨_, _⟩ =>
      EmittedStaticStateRun.bind (staticState_patchBrs0 tables _ _) fun _ => staticState_setCur module le _

theorem staticState_scFork (isAnd : Bool) (value : ValueId) : EmittedStaticStateRun module le (scFork isAnd value) := by
  unfold scFork
  refine EmittedStaticStateRun.bind (staticState_newBlock _ (by simp [EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure])) fun ⟨_, _⟩ =>
    EmittedStaticStateRun.bind (staticState_newBlock _ (by simp [EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure])) fun ⟨_, _⟩ => ?_
  cases isAnd <;> exact EmittedStaticStateRun.bind (staticState_emitTerm _ (by simp [EmittedProfileInst])) fun _ => EmittedStaticStateRun.pure module le _

theorem staticState_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (typed : EmittedStaticStateRun module le rhs) : EmittedStaticStateRun module le (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  exact staticState_whenLive tables _ fun _ =>
    EmittedStaticStateRun.bind (staticState_scFork tables _ _) fun ⟨_, _, _⟩ =>
    EmittedStaticStateRun.bind (staticState_setCur module le _) fun _ => EmittedStaticStateRun.bind typed fun _ =>
    EmittedStaticStateRun.bind (staticState_emitTerm _ (by simp [EmittedProfileInst])) fun _ =>
    EmittedStaticStateRun.bind (staticState_setCur module le _) fun _ => EmittedStaticStateRun.pure module le _

theorem staticState_loopBody (cv : ValueId) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (hbody : ∀ depth exitBlock, EmittedStaticStateRun module le (body depth exitBlock)) (hback : EmittedStaticStateRun module le back) :
    EmittedStaticStateRun module le (loopBody cv body back) := by
  unfold loopBody
  exact EmittedStaticStateRun.bind (staticState_get module le) fun _ =>
    EmittedStaticStateRun.bind (staticState_fork tables _) fun ⟨_, _⟩ =>
    EmittedStaticStateRun.bind (staticState_setCur module le _) fun _ => EmittedStaticStateRun.bind (hbody _ _) fun _ =>
    EmittedStaticStateRun.bind hback fun _ => staticState_setCur module le _

theorem staticState_rangeBack (t : IntTy) (i : ValueId) (hb : BlockId) : EmittedStaticStateRun module le (rangeBack t i hb) := by
  unfold rangeBack
  refine EmittedStaticStateRun.bind (staticState_isLive tables) fun live => ?_
  cases live
  · exact EmittedStaticStateRun.pure module le _
  · exact EmittedStaticStateRun.bind (staticState_emitDef tables _ (fun _ => trivial) (fun _ => trivial)) fun _ => staticState_emitTerm _ (by simp [EmittedProfileInst])


theorem staticState_lowerWhile (hb : BlockId) {cond : B ValueId} {body : Nat → BlockId → B ValueId}
    (hc : EmittedStaticStateRun module le cond) (hbody : ∀ d xb, EmittedStaticStateRun module le (body d xb)) : EmittedStaticStateRun module le (lowerWhile hb cond body) := by
  unfold lowerWhile
  exact EmittedStaticStateRun.bind hc fun cv => staticState_whenLive tables _ fun _ =>
    staticState_loopBody tables cv hbody (staticState_emitTerm _ (by simp [EmittedProfileInst]))

theorem staticState_lowerRange (t : IntTy) (i b : ValueId) (hb : BlockId) {body : Nat → BlockId → B ValueId}
    (hbody : ∀ d xb, EmittedStaticStateRun module le (body d xb)) : EmittedStaticStateRun module le (lowerRange t i b hb body) := by
  unfold lowerRange
  exact EmittedStaticStateRun.bind (staticState_emitDef tables _ (fun _ => trivial) (fun _ => trivial)) fun c => staticState_loopBody tables c hbody (staticState_rangeBack tables _ _ _)

theorem staticState_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (hb : BlockId)
    (i : ValueId) {body : Nat → BlockId → B ValueId} (hbody : ∀ d xb, EmittedStaticStateRun module le (body d xb)) :
    EmittedStaticStateRun module le (lowerEach regrow owner sampled hb i body) := by
  unfold lowerEach
  exact EmittedStaticStateRun.bind (staticState_eachLen tables _ _ _) fun n => EmittedStaticStateRun.bind (staticState_emitDef tables _ (fun _ => trivial) (fun _ => trivial)) fun c =>
    staticState_loopBody tables c hbody (staticState_rangeBack tables _ _ _)

theorem staticState_ifE_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : EmittedStaticStateRun module le a1) (h2 : EmittedStaticStateRun module le a2) :
    EmittedStaticStateRun module le (whenLive 0 fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let vt ← a1
      let endT ← curBlock
      setCur (some eb)
      let vf ← a2
      let endF ← curBlock
      joinValue endT vt endF vf) := by
  exact staticState_whenLive tables _ fun _ =>
    EmittedStaticStateRun.bind (staticState_fork tables _) fun ⟨_, _⟩ =>
    EmittedStaticStateRun.bind (staticState_setCur module le _) fun _ => EmittedStaticStateRun.bind h1 fun _ =>
    EmittedStaticStateRun.bind (staticState_curBlock module le) fun _ => EmittedStaticStateRun.bind (staticState_setCur module le _) fun _ =>
    EmittedStaticStateRun.bind h2 fun _ => EmittedStaticStateRun.bind (staticState_curBlock module le) fun _ => staticState_joinValue tables _ _ _ _

theorem staticState_ifS_some_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : EmittedStaticStateRun module le a1) (h2 : EmittedStaticStateRun module le a2) :
    EmittedStaticStateRun module le (whenLive () fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let _ ← a1
      let endT ← curBlock
      setCur (some eb)
      let _ ← a2
      let endF ← curBlock
      joinArms endT endF) := by
  exact staticState_whenLive tables _ fun _ =>
    EmittedStaticStateRun.bind (staticState_fork tables _) fun ⟨_, _⟩ =>
    EmittedStaticStateRun.bind (staticState_setCur module le _) fun _ => EmittedStaticStateRun.bind h1 fun _ =>
    EmittedStaticStateRun.bind (staticState_curBlock module le) fun _ => EmittedStaticStateRun.bind (staticState_setCur module le _) fun _ =>
    EmittedStaticStateRun.bind h2 fun _ => EmittedStaticStateRun.bind (staticState_curBlock module le) fun _ => staticState_joinArms tables _ _

theorem staticState_ifS_none_core (cv : ValueId) {a1 : B ValueId} (h1 : EmittedStaticStateRun module le a1) :
    EmittedStaticStateRun module le (whenLive () fun _ => do
      let (tb, jb) ← fork cv
      setCur (some tb)
      let _ ← a1
      emitTerm (.br jb [])
      setCur (some jb)) := by
  exact staticState_whenLive tables _ fun _ =>
    EmittedStaticStateRun.bind (staticState_fork tables _) fun ⟨_, _⟩ =>
    EmittedStaticStateRun.bind (staticState_setCur module le _) fun _ => EmittedStaticStateRun.bind h1 fun _ =>
    EmittedStaticStateRun.bind (staticState_emitTerm _ (by simp [EmittedProfileInst])) fun _ => staticState_setCur module le _

theorem staticState_assert_core (cv : ValueId) (org : OriginId) :
    EmittedStaticStateRun module le (whenLive () fun _ => do
      let (pb, fb) ← fork cv
      setCur (some fb)
      emitTerm (.abort .assert (some org))
      setCur (some pb)) := by
  exact staticState_whenLive tables _ fun _ =>
    EmittedStaticStateRun.bind (staticState_fork tables _) fun ⟨_, _⟩ =>
    EmittedStaticStateRun.bind (staticState_setCur module le _) fun _ => EmittedStaticStateRun.bind (staticState_emitTerm _ (by simp [EmittedProfileInst])) fun _ => staticState_setCur module le _

theorem staticState_header0 {tail : BlockId → B Unit} (ht : ∀ h, EmittedStaticStateRun module le (tail h)) :
    EmittedStaticStateRun module le (do
      let (hb, _) ← newBlock []
      emitTerm (.br hb [])
      setCur (some hb)
      tail hb) := by
  exact EmittedStaticStateRun.bind (staticState_newBlock _ (by simp [EmittedVTyResolved, Core.checkResolvedType, pure, Except.pure])) fun ⟨_, _⟩ =>
    EmittedStaticStateRun.bind (staticState_emitTerm _ (by simp [EmittedProfileInst])) fun _ => EmittedStaticStateRun.bind (staticState_setCur module le _) fun _ => ht _


theorem staticState_header1 (type : VTy) (value : ValueId)
    (resolved : EmittedVTyResolved module type) {tail : BlockId → ValueId → B Unit}
    (typed : ∀ header counter, EmittedStaticStateRun module le (tail header counter)) :
    EmittedStaticStateRun module le (do
      let (header, parameters) ← newBlock [type]
      let counter := parameters.headD 0
      emitTerm (.br header [value])
      setCur (some header)
      tail header counter) := by
  exact EmittedStaticStateRun.bind (staticState_newBlock [type] (by simpa using resolved)) fun ⟨_, _⟩ =>
    EmittedStaticStateRun.bind (staticState_emitTerm _ trivial) fun _ =>
    EmittedStaticStateRun.bind (staticState_setCur module le _) fun _ => typed _ _

end

end Goose.Lower.Validation
