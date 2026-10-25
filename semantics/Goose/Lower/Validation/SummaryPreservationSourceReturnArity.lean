import Goose.Lower.Validation.SummaryPreservationReturnFramesLoops
import Goose.Lower.Validation.CfgBuilderFunctions
import Goose.Lower.Validate

namespace Goose.Lower.Validation.SummaryPreservation.SourceReturnArity

open ReturnFrames

open Goose.Core Goose.GIR Goose.Lower.Validation

variable {avoid : List ValueId × Option OriginId}

private theorem emitTerm_absent (term : Term) (different : term ≠ .ret avoid.1 avoid.2) :
    ReturnAbsentRun (avoid := avoid) (Goose.Lower.emitTerm term) := by
  intro le before result after run checked
  cases current : before.cur with
  | none => rw [emitTerm_none _ _ current] at run; cases run; exact checked
  | some block =>
    have pushed : BuilderReturnAbsent (avoid := avoid)
        (pushInst block (.term term) le before).2 := by
      apply checked.modify
      intro body row member
      have entries : Inst.term (.ret avoid.1 avoid.2) ∈ body.insts.toList ++ [.term term] := by
        simpa only [Array.toList_push] using member
      rcases List.mem_append.mp entries with old | fresh
      · exact checked block body row old
      · exact different (Inst.term.inj (List.mem_singleton.mp fresh)).symm
    rw [emitTerm_run _ _ current] at run
    cases run
    exact pushed.of_blocks rfl

mutual

theorem invalidReturnAbsent_lowerExpr (invalid : 1 < avoid.1.length) : ∀ e : Expr, ReturnAbsentRun (avoid := avoid) (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExprs invalid es) fun _ => returnAbsent_emitDef _
  | .lit t n => by simp only [lowerExpr]; exact returnAbsent_emitDef _
  | .bool b => by simp only [lowerExpr]; exact returnAbsent_emitDef _
  | .read p => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid p) fun address =>
      ReturnAbsentRun.bind (returnAbsent_emitDef (.load address)) fun value =>
      ReturnAbsentRun.bind (returnAbsent_recordReadValueRootRecipe value p) fun _ => returnAbsent_pure value
  | .ref m p => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid p) fun r => returnAbsent_borrowTo m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerView invalid v) fun _ => ReturnAbsentRun.bind (invalidReturnAbsent_lowerBound invalid lo) fun _ =>
      ReturnAbsentRun.bind (invalidReturnAbsent_lowerBound invalid hi) fun _ => returnAbsent_emitDef _
  | .len v => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerView invalid v) fun _ => returnAbsent_emitDef _
  | .un op e org => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun a => ReturnAbsentRun.bind (returnAbsent_intTyOf a) fun _ => returnAbsent_emitDef _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid a) fun x => ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid b) fun y =>
      ReturnAbsentRun.bind (returnAbsent_intTyOf x) fun _ => returnAbsent_emitDef _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid a) fun x => ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid b) fun y =>
      ReturnAbsentRun.bind (returnAbsent_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact returnAbsent_emitDef _
    | view _ _ => exact returnAbsent_emitDef _
  | .and a b => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid a) fun x => returnAbsent_shortCircuit true x (invalidReturnAbsent_lowerExpr invalid b) (advB_lowerExpr b)
  | .or a b => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid a) fun x => returnAbsent_shortCircuit false x (invalidReturnAbsent_lowerExpr invalid b) (advB_lowerExpr b)
  | .not e => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun _ => returnAbsent_emitDef _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun a => ReturnAbsentRun.bind (returnAbsent_intTyOf a) fun _ => returnAbsent_emitDef _
  | .call c args org => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerArgs invalid args) fun values => returnAbsent_call c values (some org)
  | .push owner e org => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid owner) fun r => ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun v =>
      returnAbsent_emitDef (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid owner) fun _ => returnAbsent_emitDef _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid c) fun cv =>
      returnAbsent_ifE_recorded_core cv (sourceBlockScope t) (invalidReturnAbsent_lowerBlock invalid none [] true t) (invalidReturnAbsent_lowerBlock invalid none [] true f)
  | .blockE b => by
    simp only [lowerExpr]
    exact invalidReturnAbsent_lowerBlock invalid none [] true b
  | .arrLit t es => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExprs invalid es) fun _ => returnAbsent_emitDef _
  | .fill t e => by
    simp only [lowerExpr]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun _ => returnAbsent_emitDef _

theorem invalidReturnAbsent_lowerExprs (invalid : 1 < avoid.1.length) : ∀ es : List Expr, ReturnAbsentRun (avoid := avoid) (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact returnAbsent_pure _
  | e :: rest => by
    simp only [lowerExprs]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun _ => ReturnAbsentRun.bind (invalidReturnAbsent_lowerExprs invalid rest) fun _ => returnAbsent_pure _

theorem invalidReturnAbsent_lowerArg (invalid : 1 < avoid.1.length) : ∀ a : Arg, ReturnAbsentRun (avoid := avoid) (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact invalidReturnAbsent_lowerExpr invalid e
  | .byRef m p => by
    simp only [lowerArg]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid p) fun r => returnAbsent_borrowTo m r

theorem invalidReturnAbsent_lowerArgs (invalid : 1 < avoid.1.length) : ∀ as : List Arg, ReturnAbsentRun (avoid := avoid) (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact returnAbsent_pure _
  | a :: rest => by
    simp only [lowerArgs]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerArg invalid a) fun _ => ReturnAbsentRun.bind (invalidReturnAbsent_lowerArgs invalid rest) fun _ => returnAbsent_pure _

theorem invalidReturnAbsent_lowerPlace (invalid : 1 < avoid.1.length) : ∀ p : Place, ReturnAbsentRun (avoid := avoid) (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid owner) fun _ => returnAbsent_emitDef _
  | .var x => by simp only [lowerPlace]; exact returnAbsent_emitDef _
  | .global g => by simp only [lowerPlace]; exact returnAbsent_emitDef _
  | .deref e => by simp only [lowerPlace]; exact invalidReturnAbsent_lowerExpr invalid e
  | .elem v i org => by
    simp only [lowerPlace]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerView invalid v) fun _ => ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid i) fun _ => returnAbsent_emitDef _

theorem invalidReturnAbsent_lowerView (invalid : 1 < avoid.1.length) : ∀ v : View, ReturnAbsentRun (avoid := avoid) (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid p) fun _ => returnAbsent_emitDef _
  | .val e => by
    simp only [lowerView]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun _ => returnAbsent_emitDef _

theorem invalidReturnAbsent_lowerBound (invalid : 1 < avoid.1.length) : ∀ b : Bound, ReturnAbsentRun (avoid := avoid) (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact returnAbsent_pure _
  | .expr e => by
    simp only [lowerBound]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun _ => returnAbsent_pure _
  | .fromEnd e => by
    simp only [lowerBound]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun _ => returnAbsent_pure _

theorem invalidReturnAbsent_lowerEachSource (invalid : 1 < avoid.1.length) : ∀ v : View, ReturnAbsentRun (avoid := avoid) (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid p) fun _ => ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ => returnAbsent_pure _
  | .val e => by
    simp only [lowerEachSource]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun _ => ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ => returnAbsent_pure _

theorem invalidReturnAbsent_lowerBlockValue (invalid : 1 < avoid.1.length) (want : Bool) : ∀ v : Option Expr, ReturnAbsentRun (avoid := avoid) (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact invalidReturnAbsent_lowerExpr invalid e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact returnAbsent_pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact returnAbsent_emitDef _

theorem invalidReturnAbsent_lowerBlock (invalid : 1 < avoid.1.length) (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, ReturnAbsentRun (avoid := avoid) (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact ReturnAbsentRun.bind (returnAbsent_emitEffect _) fun _ => returnAbsent_inScope sc
      (ReturnAbsentRun.bind (returnAbsent_initSlots _) fun _ => ReturnAbsentRun.bind (invalidReturnAbsent_lowerStmts invalid lc stmts) fun _ =>
        ReturnAbsentRun.bind (invalidReturnAbsent_lowerBlockValue invalid want value) fun _ => ReturnAbsentRun.bind (returnAbsent_emitEffect _) fun _ =>
        returnAbsent_pure _)

theorem invalidReturnAbsent_lowerStmts (invalid : 1 < avoid.1.length) (lc : Option LoopCtx) : ∀ ss : List Stmt, ReturnAbsentRun (avoid := avoid) (lowerStmts lc ss)
  | [] => by simp only [lowerStmts]; exact returnAbsent_pure _
  | s :: rest => by
    simp only [lowerStmts]
    refine ReturnAbsentRun.bind (returnAbsent_isLive) fun live => ?_
    cases live
    · exact returnAbsent_pure _
    · exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerStmt invalid lc s) fun _ => invalidReturnAbsent_lowerStmts invalid lc rest

theorem invalidReturnAbsent_lowerPrintArgs (invalid : 1 < avoid.1.length) : ∀ as : List PrintArg, ReturnAbsentRun (avoid := avoid) (lowerPrintArgs as)
  | [] => by simp only [lowerPrintArgs]; exact returnAbsent_pure _
  | .text s :: rest => by
    simp only [lowerPrintArgs]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPrintArgs invalid rest) fun _ => returnAbsent_pure _
  | .expr e :: rest => by
    simp only [lowerPrintArgs]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun _ => ReturnAbsentRun.bind (invalidReturnAbsent_lowerPrintArgs invalid rest) fun _ => returnAbsent_pure _

theorem invalidReturnAbsent_lowerStmt (invalid : 1 < avoid.1.length) (lc : Option LoopCtx) : ∀ s : Stmt, ReturnAbsentRun (avoid := avoid) (lowerStmt lc s)
  | .letS x e org => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun v =>
      ReturnAbsentRun.bind (returnAbsent_coerceSlot x v org) fun _ => returnAbsent_emitEffect _
  | .assign p e org => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid p) fun _ => ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun _ => returnAbsent_emitEffect _
  | .assignOp op p e org => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid p) fun _ => ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ =>
      ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun _ => ReturnAbsentRun.bind (returnAbsent_intTyOf _) fun _ =>
      ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ => returnAbsent_emitEffect _
  | .rebind x e org => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun v =>
      ReturnAbsentRun.bind (returnAbsent_coerceSlot x v org) fun _ =>
        ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ => returnAbsent_emitEffect _
  | .expr e _ => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun _ => returnAbsent_pure _
  | .append owner src org => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid owner) fun _ => ReturnAbsentRun.bind (invalidReturnAbsent_lowerView invalid src) fun _ =>
      returnAbsent_emitEffect _
  | .popN owner count org => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid owner) fun r => ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid count) fun n =>
      returnAbsent_emitEffect (.popN r n (some org))
  | .resize owner size none org => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid owner) fun r => ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid size) fun n =>
      ReturnAbsentRun.bind (returnAbsent_pure _) fun fill => returnAbsent_emitEffect (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid owner) fun r => ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid size) fun n =>
      ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid fill) fun v =>
        returnAbsent_emitEffect (.resize r n (some v) (some org))
  | .clear owner org => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid owner) fun r => returnAbsent_emitEffect (.clear r (some org))
  | .assignWhole owner replacement org => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPlace invalid owner) fun r =>
      ReturnAbsentRun.bind (returnAbsent_emitEffect (.clear r (some org))) fun _ =>
      ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid replacement) fun run =>
        returnAbsent_emitEffect (.replace r run (some org))
  | .ifS c t f _ => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid c) fun cv => returnAbsent_ifS_none_core cv (invalidReturnAbsent_lowerBlock invalid lc [] false t) (advB_lowerBlock lc [] false t)
    | some fb =>
      simp only [lowerStmt]
      exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid c) fun cv =>
        returnAbsent_ifS_some_core cv (invalidReturnAbsent_lowerBlock invalid lc [] false t) (invalidReturnAbsent_lowerBlock invalid lc [] false fb)
  | .while c body _ => by
    simp only [lowerStmt]
    apply returnAbsent_header0 (tail := fun header => lowerWhile header (lowerExpr c)
      (fun depth exit => lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body))
    intro header
    exact returnAbsent_lowerWhile header (invalidReturnAbsent_lowerExpr invalid c)
      (fun depth exit => invalidReturnAbsent_lowerBlock invalid (some ⟨depth, exit, .jump header⟩) [] false body)
  | .forRange x lo hi body org => by
    simp only [lowerStmt]
    refine ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid lo) fun first =>
      ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid hi) fun bound =>
      returnAbsent_whenLive _ fun _ => ReturnAbsentRun.bind (returnAbsent_intTyOf first) fun ty => ?_
    apply returnAbsent_header1 (.data (.int ty)) first
      (tail := fun header counter => lowerRange ty counter bound header
        (fun depth exit => lowerBlock (some ⟨depth, exit, .next header ty counter⟩) [(x, counter, org)] false body))
    intro header counter
    exact returnAbsent_lowerRange ty counter bound header
      (fun depth exit => invalidReturnAbsent_lowerBlock invalid (some ⟨depth, exit, .next header ty counter⟩) [(x, counter, org)] false body)
  | .forEach x none v byRef body org => by
    simp only [lowerStmt]
    refine ReturnAbsentRun.bind (invalidReturnAbsent_lowerEachSource invalid v) fun ownerView =>
      ReturnAbsentRun.bind (returnAbsent_regrowOf _) fun regrow =>
      ReturnAbsentRun.bind (returnAbsent_eachSampled _ _) fun sampled =>
      ReturnAbsentRun.bind (returnAbsent_emitDef _) fun first =>
      returnAbsent_whenLive _ fun _ => ?_
    apply returnAbsent_header1 (.data (.int .i64)) first
      (tail := fun header counter => lowerEach regrow ownerView.1 sampled header counter (fun depth exit => do
        let element ← emitDef (.refElem ownerView.2 counter)
        let value ← eachElemValue x byRef element
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((x, value, org) :: []) false body))
    intro header counter
    apply returnAbsent_lowerEach regrow ownerView.1 sampled header counter
    intro depth exit
    refine ReturnAbsentRun.bind (returnAbsent_emitDef _) fun element =>
      ReturnAbsentRun.bind (returnAbsent_eachElemValue _ _ _) fun value => ?_
    exact invalidReturnAbsent_lowerBlock invalid (some ⟨depth, exit, .next header .i64 counter⟩) _ false body
  | .forEach x (some index) v byRef body org => by
    simp only [lowerStmt]
    refine ReturnAbsentRun.bind (invalidReturnAbsent_lowerEachSource invalid v) fun ownerView =>
      ReturnAbsentRun.bind (returnAbsent_regrowOf _) fun regrow =>
      ReturnAbsentRun.bind (returnAbsent_eachSampled _ _) fun sampled =>
      ReturnAbsentRun.bind (returnAbsent_emitDef _) fun first =>
      returnAbsent_whenLive _ fun _ => ?_
    apply returnAbsent_header1 (.data (.int .i64)) first
      (tail := fun header counter => lowerEach regrow ownerView.1 sampled header counter (fun depth exit => do
        let element ← emitDef (.refElem ownerView.2 counter)
        let value ← eachElemValue x byRef element
        lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((x, value, org) :: [(index, counter, org)]) false body))
    intro header counter
    apply returnAbsent_lowerEach regrow ownerView.1 sampled header counter
    intro depth exit
    refine ReturnAbsentRun.bind (returnAbsent_emitDef _) fun element =>
      ReturnAbsentRun.bind (returnAbsent_eachElemValue _ _ _) fun value => ?_
    exact invalidReturnAbsent_lowerBlock invalid (some ⟨depth, exit, .next header .i64 counter⟩) _ false body
  | .ret e org => by
    cases e with
    | none =>
      change ReturnAbsentRun (do
        Goose.Lower.leaveTo 0
        Goose.Lower.emitTerm (.ret [] (some org)))
      exact ReturnAbsentRun.bind (returnAbsent_leaveTo 0) fun _ =>
        emitTerm_absent _ (by intro same; have eq := congrArg List.length (Term.ret.inj same).1; simp at eq; omega)
    | some expression =>
      change ReturnAbsentRun (do
        let value ← lowerExpr expression
        let returned ← Goose.Lower.coerceResult value org
        Goose.Lower.leaveTo 0
        Goose.Lower.emitTerm (.ret [returned] (some org)))
      exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid expression) fun value =>
        ReturnAbsentRun.bind (returnAbsent_coerceResult value org) fun returned =>
          ReturnAbsentRun.bind (returnAbsent_leaveTo 0) fun _ =>
            emitTerm_absent _ (by intro same; have eq := congrArg List.length (Term.ret.inj same).1; simp at eq; omega)
  | .brk _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact returnAbsent_pure _
    | some context =>
      simp only [lowerStmt]
      exact ReturnAbsentRun.bind (returnAbsent_leaveTo _) fun _ =>
        returnAbsent_emitTerm _ (by intro values origin h; cases h)
  | .cont _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact returnAbsent_pure _
    | some context =>
      cases kind : context.cont with
      | jump header =>
        simp only [lowerStmt, kind]
        exact ReturnAbsentRun.bind (returnAbsent_leaveTo _) fun _ =>
          returnAbsent_emitTerm _ (by intro values origin h; cases h)
      | next header ty counter =>
        simp only [lowerStmt, kind]
        exact ReturnAbsentRun.bind (returnAbsent_leaveTo _) fun _ =>
          ReturnAbsentRun.bind (returnAbsent_emitDef _) fun _ =>
            returnAbsent_emitTerm _ (by intro values origin h; cases h)
  | .print args org => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerPrintArgs invalid args) fun _ => returnAbsent_emitEffect _
  | .assertS e org => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun cv => returnAbsent_assert_core cv org
  | .abort _ org => by
    simp only [lowerStmt]
    exact returnAbsent_emitTerm _ (by intro values origin h; cases h)
  | .exit e org => by
    simp only [lowerStmt]
    exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid e) fun _ => returnAbsent_emitTerm _ (by intro values origin h; cases h)

end

theorem invalidReturnAbsent_finishFunction (invalid : 1 < avoid.1.length) (impl : Impl) (value : ValueId) :
    ReturnAbsentRun (avoid := avoid) (Goose.Lower.finishFunction impl value) := by
  simp only [Goose.Lower.finishFunction]
  refine ReturnAbsentRun.bind returnAbsent_read fun env => ?_
  refine ReturnAbsentRun.bind returnAbsent_isLive fun live => ?_
  cases live <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact returnAbsent_pure _
  · split
    · refine ReturnAbsentRun.bind (returnAbsent_newBlock []) fun pair => ?_
      refine ReturnAbsentRun.bind (returnAbsent_emitTerm _ (by intro values origin same; cases same)) fun _ => ?_
      exact ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ =>
        returnAbsent_emitTerm _ (by intro values origin same; cases same)
    · apply emitTerm_absent
      intro same
      have lengths := congrArg List.length (Term.ret.inj same).1
      cases condition : impl.body.value.isSome <;> simp [condition] at lengths <;> omega

theorem invalidReturnAbsent_impl (invalid : 1 < avoid.1.length) (impl : Impl) :
    ReturnAbsentRun (avoid := avoid) (cfg_implAction impl) := by
  unfold cfg_implAction
  refine ReturnAbsentRun.bind (returnAbsent_newBlock _) fun pair => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  exact ReturnAbsentRun.bind (invalidReturnAbsent_lowerBlock invalid none _ false impl.body)
    fun value => invalidReturnAbsent_finishFunction invalid impl value

theorem invalidReturnAbsent_global (invalid : 1 < avoid.1.length) (global : Core.Global) :
    ReturnAbsentRun (avoid := avoid) (cfg_globalAction global) := by
  unfold cfg_globalAction
  refine ReturnAbsentRun.bind (returnAbsent_newBlock _) fun pair => ?_
  refine ReturnAbsentRun.bind (returnAbsent_setCur _) fun _ => ?_
  refine ReturnAbsentRun.bind (invalidReturnAbsent_lowerExpr invalid global.init) fun value => ?_
  apply emitTerm_absent
  intro same
  have lengths := congrArg List.length (Term.ret.inj same).1
  simp at lengths
  omega

theorem return_arity_of_absence {action : B α}
    (absent : ∀ avoid : List ValueId × Option OriginId, 1 < avoid.1.length →
      ReturnAbsentRun (avoid := avoid) action)
    (le : LEnv) (values : List ValueId) (origin : Option OriginId)
    (member : Inst.term (.ret values origin) ∈ (action le initState).2.insts) :
    values.length ≤ 1 := by
  apply Classical.byContradiction
  intro invalid
  have missing : BuilderReturnAbsent (avoid := (values, origin)) initState := by
    intro index body row
    simp [initState] at row
  have checked := absent (values, origin) (by change 1 < values.length; omega) le initState _ _ rfl missing
  obtain ⟨body, bodyMember, instruction⟩ := List.mem_flatMap.mp member
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp bodyMember)
  exact checked index body row instruction

theorem implementation_return_arity (module : Core.Module) (impl : Impl)
    (values : List ValueId) (origin : Option OriginId)
    (member : Inst.term (.ret values origin) ∈ (cfg_implState module impl).insts) :
    values.length ≤ 1 :=
  return_arity_of_absence (fun _ invalid => invalidReturnAbsent_impl invalid impl)
    _ values origin member

theorem global_return_arity (module : Core.Module) (global : Core.Global)
    (values : List ValueId) (origin : Option OriginId)
    (member : Inst.term (.ret values origin) ∈ (cfg_globalState module global).insts) :
    values.length ≤ 1 :=
  return_arity_of_absence (fun _ invalid => invalidReturnAbsent_global invalid global)
    _ values origin member

#print axioms implementation_return_arity
#print axioms global_return_arity

end Goose.Lower.Validation.SummaryPreservation.SourceReturnArity
