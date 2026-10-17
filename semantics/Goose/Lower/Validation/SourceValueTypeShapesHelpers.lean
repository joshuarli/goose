import Goose.Lower.Validation.SourceValueTypeShapesState

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

section
variable {module : Core.Module} {le : LEnv} (tables : ShapeTables module le)
include tables

theorem shaped_inScope (scope : ScopeId) {action : B α} (typed : EmittedShapeRun module le action) :
    EmittedShapeRun module le (inScope scope action) := by
  unfold inScope
  exact EmittedShapeRun.bind (shaped_pushScope module le _) fun _ =>
    EmittedShapeRun.bind typed fun _ => EmittedShapeRun.bind (shaped_popScope module le) fun _ => EmittedShapeRun.pure module le _

theorem shaped_whenLive (default : α) {action : BlockId → B α}
    (typed : ∀ block, EmittedShapeRun module le (action block)) : EmittedShapeRun module le (whenLive default action) := by
  unfold whenLive
  refine EmittedShapeRun.bind (shaped_curBlock module le) fun current => ?_
  cases current
  · exact EmittedShapeRun.pure module le _
  · exact typed _

theorem shaped_intTyOf (v : ValueId) : EmittedShapeRun module le (intTyOf v) := by
  unfold intTyOf
  refine EmittedShapeRun.bind (shaped_valTy module le v) fun t => ?_
  cases t with
  | data t => cases t <;> exact EmittedShapeRun.pure module le _
  | view _ _ => exact EmittedShapeRun.pure module le _

theorem shaped_freezeTo (m : Mutability) (r : ValueId) : EmittedShapeRun module le (freezeTo m r) := by
  unfold freezeTo
  refine EmittedShapeRun.bind (shaped_valTy module le r) fun t => ?_
  cases m <;> cases t <;> first
    | exact EmittedShapeRun.pure module le _
    | (rename_i t; cases t <;> first | exact EmittedShapeRun.pure module le _ | (rename_i m' _; cases m' <;> first | exact EmittedShapeRun.pure module le _ | exact shaped_emitDef tables _ (fun _ => trivial)))

theorem shaped_borrowTo (m : Mutability) (r : ValueId) : EmittedShapeRun module le (borrowTo m r) := by
  intro before result after run checked
  rcases borrowTo_cases run with frozen | borrowed
  · exact shaped_freezeTo tables m r before result after frozen checked
  · exact shaped_emitDef tables (.ownerBorrow r) (fun _ => trivial) before result after borrowed checked

theorem shaped_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : EmittedShapeRun module le (coerceTo target r org) := by
  unfold coerceTo
  refine EmittedShapeRun.bind (shaped_valTy module le r) fun source => ?_
  split
  · exact shaped_emitDef tables _ (fun _ => trivial)
  · exact EmittedShapeRun.bind (shaped_emitDef tables _ (fun _ => trivial)) (fun _ => shaped_emitDef tables _ (fun _ => trivial))
  · exact EmittedShapeRun.pure module le _

theorem shaped_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    EmittedShapeRun module le (coerceSlot slot value org) := by
  unfold coerceSlot
  refine EmittedShapeRun.bind (shaped_read module le) fun readEnv => ?_
  cases readEnv.slots[slot]? with
  | none => exact EmittedShapeRun.pure module le _
  | some destination => exact shaped_coerceTo tables destination.ty value org

theorem shaped_coerceResult (value : ValueId) (org : OriginId) :
    EmittedShapeRun module le (coerceResult value org) := by
  unfold coerceResult
  refine EmittedShapeRun.bind (shaped_read module le) fun readEnv => ?_
  cases readEnv.results.head? with
  | none => exact EmittedShapeRun.pure module le _
  | some destination => exact shaped_coerceTo tables destination value org

theorem shaped_growOwner (r : ValueId) : EmittedShapeRun module le (growOwner r) := by
  unfold growOwner
  refine EmittedShapeRun.bind (shaped_valTy module le r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact EmittedShapeRun.pure module le _ | (rename_i m' t'; cases t' <;> exact EmittedShapeRun.pure module le _)
  | view _ _ => exact EmittedShapeRun.pure module le _

theorem shaped_leaveAll : ∀ scs, EmittedShapeRun module le (leaveAll scs)
  | [] => EmittedShapeRun.pure module le _
  | sc :: rest => by
    unfold leaveAll
    exact EmittedShapeRun.bind (shaped_emitEffect _) fun _ => shaped_leaveAll rest

theorem shaped_leaveTo (d : Nat) : EmittedShapeRun module le (leaveTo d) := by
  unfold leaveTo
  exact EmittedShapeRun.bind (shaped_get module le) fun _ => shaped_leaveAll tables _

theorem shaped_initSlots : ∀ ps, EmittedShapeRun module le (initSlots ps)
  | [] => EmittedShapeRun.pure module le _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact EmittedShapeRun.bind (shaped_emitEffect _) fun _ => shaped_initSlots rest

theorem shaped_isLive : EmittedShapeRun module le isLive := by
  unfold isLive
  exact EmittedShapeRun.bind (shaped_curBlock module le) fun _ => EmittedShapeRun.pure module le _

theorem shaped_eachElemValue (x : VarId) (byRef : Bool) (elem : ValueId) :
    EmittedShapeRun module le (eachElemValue x byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact shaped_emitDef tables _ (fun _ => trivial)
  · refine EmittedShapeRun.bind (shaped_read module le) fun readEnv => ?_
    cases readEnv.vars[x]? with
    | none => exact EmittedShapeRun.pure module le _
    | some lv =>
      dsimp only
      cases lv.ty with
      | ref m t => exact shaped_borrowTo tables m elem
      | _ => exact EmittedShapeRun.pure module le _

theorem shaped_regrowOf (o : Option ValueId) : EmittedShapeRun module le (regrowOf o) := by
  cases o with
  | none => exact EmittedShapeRun.pure module le _
  | some r => exact shaped_growOwner tables r

theorem shaped_eachSampled (regrow : Bool) (vw : ValueId) : EmittedShapeRun module le (eachSampled regrow vw) := by
  unfold eachSampled
  cases regrow
  · exact shaped_emitDef tables _ (fun _ => trivial)
  · exact EmittedShapeRun.pure module le _

theorem shaped_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    EmittedShapeRun module le (eachLen regrow owner sampled) := by
  unfold eachLen
  cases regrow
  · exact EmittedShapeRun.pure module le _
  · exact shaped_emitDef tables _ (fun _ => trivial)

theorem shaped_fork (condition : ValueId) : EmittedShapeRun module le (fork condition) := by
  unfold fork
  exact EmittedShapeRun.bind (shaped_newBlock _ (by simp [ValueTypeShape, DataTypeShape, Ty.storable, pure, Except.pure])) fun ⟨thenBlock, _⟩ =>
    EmittedShapeRun.bind (shaped_newBlock _ (by simp [ValueTypeShape, DataTypeShape, Ty.storable, pure, Except.pure])) fun ⟨elseBlock, _⟩ =>
    EmittedShapeRun.bind (shaped_emitTerm _) fun _ => EmittedShapeRun.pure module le _

theorem shaped_patchBrs (target : BlockId) : ∀ incoming, EmittedShapeRun module le (patchBrs target incoming)
  | [] => EmittedShapeRun.pure module le _
  | (block, value) :: rest => by
    unfold patchBrs
    exact EmittedShapeRun.bind (shaped_patchTerm _ _) fun _ => shaped_patchBrs target rest

theorem shaped_patchBrs0 (target : BlockId) : ∀ incoming, EmittedShapeRun module le (patchBrs0 target incoming)
  | [] => EmittedShapeRun.pure module le _
  | block :: rest => by
    unfold patchBrs0
    exact EmittedShapeRun.bind (shaped_patchTerm _ _) fun _ => shaped_patchBrs0 target rest

theorem shaped_joinValue (endT : Option BlockId) (vt : ValueId)
    (endF : Option BlockId) (vf : ValueId) :
    EmittedShapeRun module le (joinValue endT vt endF vf) := by
  unfold joinValue
  cases endT <;> cases endF
  · exact EmittedShapeRun.bind (shaped_setCur module le _) fun _ =>
      EmittedShapeRun.pure module le _
  all_goals
    intro before result after run checked
    obtain ⟨type, middle, typeRun, tail⟩ := bind_eq.mp run
    have same := congrArg Prod.snd typeRun
    simp only [valTy_run] at same
    subst middle
    have valid : ValueTypeShape type := by
      have sameType := congrArg Prod.fst typeRun
      dsimp only at sameType
      exact sameType ▸ checked.valTy le _
    exact (EmittedShapeRun.bind (shaped_newBlock [type] (by simpa using valid)) fun ⟨_, _⟩ =>
      EmittedShapeRun.bind (shaped_patchBrs tables _ _) fun _ =>
      EmittedShapeRun.bind (shaped_setCur module le _) fun _ =>
      EmittedShapeRun.pure module le _) _ _ _ tail checked

theorem shaped_joinArms (endT endF : Option BlockId) : EmittedShapeRun module le (joinArms endT endF) := by
  unfold joinArms
  cases endT <;> cases endF
  · exact shaped_setCur module le _
  all_goals
    exact EmittedShapeRun.bind (shaped_newBlock _ (by simp [ValueTypeShape, DataTypeShape, Ty.storable, pure, Except.pure])) fun ⟨_, _⟩ =>
      EmittedShapeRun.bind (shaped_patchBrs0 tables _ _) fun _ => shaped_setCur module le _

theorem shaped_scFork (isAnd : Bool) (value : ValueId) : EmittedShapeRun module le (scFork isAnd value) := by
  unfold scFork
  refine EmittedShapeRun.bind (shaped_newBlock _ (by simp [ValueTypeShape, DataTypeShape, Ty.storable, pure, Except.pure])) fun ⟨_, _⟩ =>
    EmittedShapeRun.bind (shaped_newBlock _ (by simp [ValueTypeShape, DataTypeShape, Ty.storable, pure, Except.pure])) fun ⟨_, _⟩ => ?_
  cases isAnd <;> exact EmittedShapeRun.bind (shaped_emitTerm _) fun _ => EmittedShapeRun.pure module le _

theorem shaped_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (typed : EmittedShapeRun module le rhs) : EmittedShapeRun module le (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  exact shaped_whenLive tables _ fun _ =>
    EmittedShapeRun.bind (shaped_scFork tables _ _) fun ⟨_, _, _⟩ =>
    EmittedShapeRun.bind (shaped_setCur module le _) fun _ => EmittedShapeRun.bind typed fun _ =>
    EmittedShapeRun.bind (shaped_emitTerm _) fun _ =>
    EmittedShapeRun.bind (shaped_setCur module le _) fun _ => EmittedShapeRun.pure module le _

theorem shaped_loopBody (cv : ValueId) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (hbody : ∀ depth exitBlock, EmittedShapeRun module le (body depth exitBlock)) (hback : EmittedShapeRun module le back) :
    EmittedShapeRun module le (loopBody cv body back) := by
  unfold loopBody
  exact EmittedShapeRun.bind (shaped_get module le) fun _ =>
    EmittedShapeRun.bind (shaped_fork tables _) fun ⟨_, _⟩ =>
    EmittedShapeRun.bind (shaped_setCur module le _) fun _ => EmittedShapeRun.bind (hbody _ _) fun _ =>
    EmittedShapeRun.bind hback fun _ => shaped_setCur module le _

theorem shaped_rangeBack (t : IntTy) (i : ValueId) (hb : BlockId) : EmittedShapeRun module le (rangeBack t i hb) := by
  unfold rangeBack
  refine EmittedShapeRun.bind (shaped_isLive tables) fun live => ?_
  cases live
  · exact EmittedShapeRun.pure module le _
  · exact EmittedShapeRun.bind (shaped_emitDef tables _ (fun _ => trivial)) fun _ => shaped_emitTerm _


theorem shaped_lowerWhile (hb : BlockId) {cond : B ValueId} {body : Nat → BlockId → B ValueId}
    (hc : EmittedShapeRun module le cond) (hbody : ∀ d xb, EmittedShapeRun module le (body d xb)) : EmittedShapeRun module le (lowerWhile hb cond body) := by
  unfold lowerWhile
  exact EmittedShapeRun.bind hc fun cv => shaped_whenLive tables _ fun _ =>
    shaped_loopBody tables cv hbody (shaped_emitTerm _)

theorem shaped_lowerRange (t : IntTy) (i b : ValueId) (hb : BlockId) {body : Nat → BlockId → B ValueId}
    (hbody : ∀ d xb, EmittedShapeRun module le (body d xb)) : EmittedShapeRun module le (lowerRange t i b hb body) := by
  unfold lowerRange
  exact EmittedShapeRun.bind (shaped_emitDef tables _ (fun _ => trivial)) fun c => shaped_loopBody tables c hbody (shaped_rangeBack tables _ _ _)

theorem shaped_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (hb : BlockId)
    (i : ValueId) {body : Nat → BlockId → B ValueId} (hbody : ∀ d xb, EmittedShapeRun module le (body d xb)) :
    EmittedShapeRun module le (lowerEach regrow owner sampled hb i body) := by
  unfold lowerEach
  exact EmittedShapeRun.bind (shaped_eachLen tables _ _ _) fun n => EmittedShapeRun.bind (shaped_emitDef tables _ (fun _ => trivial)) fun c =>
    shaped_loopBody tables c hbody (shaped_rangeBack tables _ _ _)

theorem shaped_ifE_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : EmittedShapeRun module le a1) (h2 : EmittedShapeRun module le a2) :
    EmittedShapeRun module le (whenLive 0 fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let vt ← a1
      let endT ← curBlock
      setCur (some eb)
      let vf ← a2
      let endF ← curBlock
      joinValue endT vt endF vf) := by
  exact shaped_whenLive tables _ fun _ =>
    EmittedShapeRun.bind (shaped_fork tables _) fun ⟨_, _⟩ =>
    EmittedShapeRun.bind (shaped_setCur module le _) fun _ => EmittedShapeRun.bind h1 fun _ =>
    EmittedShapeRun.bind (shaped_curBlock module le) fun _ => EmittedShapeRun.bind (shaped_setCur module le _) fun _ =>
    EmittedShapeRun.bind h2 fun _ => EmittedShapeRun.bind (shaped_curBlock module le) fun _ => shaped_joinValue tables _ _ _ _

theorem shaped_ifS_some_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : EmittedShapeRun module le a1) (h2 : EmittedShapeRun module le a2) :
    EmittedShapeRun module le (whenLive () fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let _ ← a1
      let endT ← curBlock
      setCur (some eb)
      let _ ← a2
      let endF ← curBlock
      joinArms endT endF) := by
  exact shaped_whenLive tables _ fun _ =>
    EmittedShapeRun.bind (shaped_fork tables _) fun ⟨_, _⟩ =>
    EmittedShapeRun.bind (shaped_setCur module le _) fun _ => EmittedShapeRun.bind h1 fun _ =>
    EmittedShapeRun.bind (shaped_curBlock module le) fun _ => EmittedShapeRun.bind (shaped_setCur module le _) fun _ =>
    EmittedShapeRun.bind h2 fun _ => EmittedShapeRun.bind (shaped_curBlock module le) fun _ => shaped_joinArms tables _ _

theorem shaped_ifS_none_core (cv : ValueId) {a1 : B ValueId} (h1 : EmittedShapeRun module le a1) :
    EmittedShapeRun module le (whenLive () fun _ => do
      let (tb, jb) ← fork cv
      setCur (some tb)
      let _ ← a1
      emitTerm (.br jb [])
      setCur (some jb)) := by
  exact shaped_whenLive tables _ fun _ =>
    EmittedShapeRun.bind (shaped_fork tables _) fun ⟨_, _⟩ =>
    EmittedShapeRun.bind (shaped_setCur module le _) fun _ => EmittedShapeRun.bind h1 fun _ =>
    EmittedShapeRun.bind (shaped_emitTerm _) fun _ => shaped_setCur module le _

theorem shaped_assert_core (cv : ValueId) (org : OriginId) :
    EmittedShapeRun module le (whenLive () fun _ => do
      let (pb, fb) ← fork cv
      setCur (some fb)
      emitTerm (.abort .assert (some org))
      setCur (some pb)) := by
  exact shaped_whenLive tables _ fun _ =>
    EmittedShapeRun.bind (shaped_fork tables _) fun ⟨_, _⟩ =>
    EmittedShapeRun.bind (shaped_setCur module le _) fun _ => EmittedShapeRun.bind (shaped_emitTerm _) fun _ => shaped_setCur module le _

theorem shaped_header0 {tail : BlockId → B Unit} (ht : ∀ h, EmittedShapeRun module le (tail h)) :
    EmittedShapeRun module le (do
      let (hb, _) ← newBlock []
      emitTerm (.br hb [])
      setCur (some hb)
      tail hb) := by
  exact EmittedShapeRun.bind (shaped_newBlock _ (by simp [ValueTypeShape, DataTypeShape, Ty.storable, pure, Except.pure])) fun ⟨_, _⟩ =>
    EmittedShapeRun.bind (shaped_emitTerm _) fun _ => EmittedShapeRun.bind (shaped_setCur module le _) fun _ => ht _


theorem shaped_header1 (type : VTy) (value : ValueId)
    (resolved : ValueTypeShape type) {tail : BlockId → ValueId → B Unit}
    (typed : ∀ header counter, EmittedShapeRun module le (tail header counter)) :
    EmittedShapeRun module le (do
      let (header, parameters) ← newBlock [type]
      let counter := parameters.headD 0
      emitTerm (.br header [value])
      setCur (some header)
      tail header counter) := by
  exact EmittedShapeRun.bind (shaped_newBlock [type] (by simpa using resolved)) fun ⟨_, _⟩ =>
    EmittedShapeRun.bind (shaped_emitTerm _) fun _ =>
    EmittedShapeRun.bind (shaped_setCur module le _) fun _ => typed _ _

end

end Goose.Lower.Validation
