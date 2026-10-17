import Goose.Lower.Validation.CfgSourceDominanceLoopStatements
import Goose.Lower.Validation.CfgSourceDominanceSourceBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

mutual

theorem ssa_sourceExpr (loop : Option LoopCtx) : ∀ expr : Expr,
    SSARun loop [] (fun result => [result]) (lowerExpr expr)
  | .structLit type expressions => ssa_structLit loop type (ssa_sourceExprs loop expressions)
  | .lit _ _ => ssa_emitDef loop _
  | .bool _ => ssa_emitDef loop _
  | .read place => ssa_readPlace loop (ssa_sourcePlace loop place)
  | .ref mu place => ssa_refPlace loop mu (ssa_sourcePlace loop place)
  | .slice mu view lo hi origin => ssa_slice loop mu origin (ssa_sourceView loop view)
      (ssa_sourceBound loop lo) (ssa_sourceBound loop hi)
  | .len view => (ssa_sourceView loop view).bind fun _ => ssa_emitDef loop _
  | .un op expr origin => ssa_unary loop op origin (ssa_sourceExpr loop expr)
  | .bin op left right origin => ssa_binary loop op origin (ssa_sourceExpr loop left) (ssa_sourceExpr loop right)
  | .cmp op left right => ssa_compare loop op (ssa_sourceExpr loop left) (ssa_sourceExpr loop right)
  | .and left right => (ssa_sourceExpr loop left).bind fun value =>
      ssa_shortCircuit loop true value (ssa_sourceExpr loop right)
  | .or left right => (ssa_sourceExpr loop left).bind fun value =>
      ssa_shortCircuit loop false value (ssa_sourceExpr loop right)
  | .not expr => (ssa_sourceExpr loop expr).bind fun _ => ssa_emitDef loop _
  | .conv kind target expr origin => ssa_convert loop kind target origin (ssa_sourceExpr loop expr)
  | .call context args origin => ssa_call loop context origin (ssa_sourceArgs loop args)
  | .push place expr origin => ssa_push loop origin (ssa_sourcePlace loop place) (ssa_sourceExpr loop expr)
  | .pop place _ => (ssa_sourcePlace loop place).bind fun _ => ssa_emitDef loop _
  | .ifE condition thenBlock elseBlock => ssa_ifExpr loop (ssa_sourceExpr loop condition)
      ((ssa_sourceBlock none thenBlock [] true).withLoop loop |>.congr_outputs (fun _ => by simp [blockValues]) |>.weaken (by simp))
      ((ssa_sourceBlock none elseBlock [] true).withLoop loop |>.congr_outputs (fun _ => by simp [blockValues]) |>.weaken (by simp))
  | .blockE body => by
    change SSARun loop [] (fun result => [result]) (lowerBlock none [] true body)
    exact ((ssa_sourceBlock none body [] true).withLoop loop).congr_outputs (fun _ => by simp [blockValues])
  | .arrLit type expressions => ssa_arrLit loop type (ssa_sourceExprs loop expressions)
  | .fill _ expr => (ssa_sourceExpr loop expr).bind fun _ => ssa_emitDef loop _

termination_by expr => sizeOf expr
decreasing_by all_goals simp_wf; all_goals omega

theorem ssa_sourceExprs (loop : Option LoopCtx) : ∀ expressions : List Expr,
    SSARun loop [] id (lowerExprs expressions)
  | [] => SSARun.pure loop [] [] id (by simp)
  | expr :: rest => ssa_exprs_cons loop (ssa_sourceExpr loop expr) (ssa_sourceExprs loop rest)

termination_by expressions => sizeOf expressions
decreasing_by all_goals simp_wf; all_goals omega

theorem ssa_sourceArg (loop : Option LoopCtx) : ∀ arg : Arg,
    SSARun loop [] (fun result => [result]) (lowerArg arg)
  | .byVal expr => ssa_sourceExpr loop expr
  | .byRef mu place => (ssa_sourcePlace loop place).bind fun value => ssa_borrowTo loop mu value

termination_by arg => sizeOf arg
decreasing_by all_goals simp_wf; all_goals omega

theorem ssa_sourceArgs (loop : Option LoopCtx) : ∀ args : List Arg,
    SSARun loop [] id (lowerArgs args)
  | [] => SSARun.pure loop [] [] id (by simp)
  | arg :: rest => ssa_args_cons loop (ssa_sourceArg loop arg) (ssa_sourceArgs loop rest)

termination_by args => sizeOf args
decreasing_by all_goals simp_wf; all_goals omega

theorem ssa_sourcePlace (loop : Option LoopCtx) : ∀ place : Place,
    SSARun loop [] (fun result => [result]) (lowerPlace place)
  | .var _ => ssa_emitDef loop _
  | .global _ => ssa_emitDef loop _
  | .field place _ => (ssa_sourcePlace loop place).bind fun _ => ssa_emitDef loop _
  | .deref expr => ssa_sourceExpr loop expr
  | .elem view index origin => ssa_place_elem loop origin (ssa_sourceView loop view) (ssa_sourceExpr loop index)

termination_by place => sizeOf place
decreasing_by all_goals simp_wf; all_goals omega

theorem ssa_sourceView (loop : Option LoopCtx) : ∀ view : View,
    SSARun loop [] (fun result => [result]) (lowerView view)
  | .of place => by
    cases place <;> exact (ssa_sourcePlace loop _).bind fun _ => ssa_emitDef loop _
  | .val expr => (ssa_sourceExpr loop expr).bind fun _ => ssa_emitDef loop _

termination_by view => sizeOf view
decreasing_by all_goals simp_wf; all_goals omega

theorem ssa_sourceBound (loop : Option LoopCtx) : ∀ bound : Bound,
    SSARun loop [] Bnd.uses (lowerBound bound)
  | .omitted => SSARun.pure loop .omitted [] Bnd.uses (by simp [Bnd.uses])
  | .expr expr => (ssa_sourceExpr loop expr).bind fun value =>
      SSARun.pure loop (.val value) [value] Bnd.uses (by simp [Bnd.uses])
  | .fromEnd expr => (ssa_sourceExpr loop expr).bind fun value =>
      SSARun.pure loop (.fromEnd value) [value] Bnd.uses (by simp [Bnd.uses])

termination_by bound => sizeOf bound
decreasing_by all_goals simp_wf; all_goals omega

theorem ssa_sourceEachSource (loop : Option LoopCtx) : ∀ view : View,
    SSARun loop [] (fun result => result.1.toList ++ [result.2]) (lowerEachSource view)
  | .of place => ssa_eachSource_of loop (ssa_sourcePlace loop place)
  | .val expr => ssa_eachSource_val loop (ssa_sourceExpr loop expr)

termination_by view => sizeOf view
decreasing_by all_goals simp_wf; all_goals omega

theorem ssa_sourceBlockValue (loop : Option LoopCtx) (want : Bool) : ∀ tail : Option Expr,
    SSARun loop [] (blockValues want tail) (lowerBlockValue want tail)
  | none => by
    cases want with
    | false => exact ssa_pure loop 0
    | true => exact ssa_emitDef loop _
  | some expr => by
    change SSARun loop [] (blockValues want (some expr)) (lowerExpr expr)
    exact (ssa_sourceExpr loop expr).congr_outputs (fun _ => by simp [blockValues])

termination_by tail => sizeOf tail
decreasing_by all_goals simp_wf; all_goals omega

theorem ssa_sourceBlock (loop : Option LoopCtx) : ∀ body : Core.Block,
    ∀ (pre : List (SlotId × ValueId × OriginId)) (want : Bool),
    SSARun loop (pre.map fun entry => entry.2.1) (blockValues want body.value) (lowerBlock loop pre want body)
  | .mk scope statements tail, pre, want => ssa_block loop pre want scope statements tail
      (ssa_sourceStmts loop statements) (ssa_sourceBlockValue loop want tail)

termination_by body _pre _want => sizeOf body
decreasing_by all_goals simp_wf; all_goals omega

theorem ssa_sourceStmts (loop : Option LoopCtx) : ∀ statements : List Stmt,
    SSARun loop [] (fun _ => []) (lowerStmts loop statements)
  | [] => ssa_pure loop ()
  | stmt :: rest => ssa_stmts_cons loop stmt rest (ssa_sourceStmt loop stmt) (ssa_sourceStmts loop rest)

termination_by statements => sizeOf statements
decreasing_by all_goals simp_wf; all_goals omega

theorem ssa_sourcePrintArgs (loop : Option LoopCtx) : ∀ args : List PrintArg,
    SSARun loop [] (fun parts => parts.flatMap PrintPart.uses) (lowerPrintArgs args)
  | [] => SSARun.pure loop [] [] (fun parts => parts.flatMap PrintPart.uses) (by simp)
  | .text text :: rest => by
    refine (ssa_sourcePrintArgs loop rest).bind fun parts => ?_
    exact SSARun.pure loop (.text text :: parts) (parts.flatMap PrintPart.uses)
      (fun parts => parts.flatMap PrintPart.uses) (by simp [PrintPart.uses])
  | .expr expr :: rest => by
    refine (ssa_sourceExpr loop expr).bind fun value => ?_
    refine ((ssa_sourcePrintArgs loop rest).keep [value]).bind fun parts => ?_
    exact SSARun.pure loop (.val value :: parts) ([value] ++ parts.flatMap PrintPart.uses)
      (fun parts => parts.flatMap PrintPart.uses) (by simp [PrintPart.uses])

termination_by args => sizeOf args
decreasing_by all_goals simp_wf; all_goals omega

theorem ssa_sourceStmt (loop : Option LoopCtx) : ∀ stmt : Stmt,
    LiveSSARun loop [] (fun _ => []) (lowerStmt loop stmt)
  | .letS slot expr origin => (ssa_letStmt loop slot origin (ssa_sourceExpr loop expr)).live
  | .assign place expr origin => (ssa_assignStmt loop origin (ssa_sourcePlace loop place) (ssa_sourceExpr loop expr)).live
  | .assignOp op place expr origin => (ssa_assignOpStmt loop op origin (ssa_sourcePlace loop place) (ssa_sourceExpr loop expr)).live
  | .rebind slot expr origin => (ssa_rebindStmt loop slot origin (ssa_sourceExpr loop expr)).live
  | .expr expr _ => ((ssa_sourceExpr loop expr).bind fun _ => (ssa_pure loop ()).weaken (by simp)).live
  | .append place view origin => (ssa_twoEffectStmt loop (fun a b => .append a b (some origin))
      (ssa_sourcePlace loop place) (ssa_sourceView loop view) (by simp [Effect.uses])).live
  | .popN place expr origin => (ssa_twoEffectStmt loop (fun a b => .popN a b (some origin))
      (ssa_sourcePlace loop place) (ssa_sourceExpr loop expr) (by simp [Effect.uses])).live
  | .resize place size none origin => (ssa_resizeStmt loop origin (ssa_sourcePlace loop place)
      (ssa_sourceExpr loop size) (by intro expr equal; cases equal)).live
  | .resize place size (some fill) origin => (ssa_resizeStmt loop origin (ssa_sourcePlace loop place)
      (ssa_sourceExpr loop size) (by intro expr equal; cases equal; exact ssa_sourceExpr loop fill)).live
  | .clear place origin => ((ssa_sourcePlace loop place).bind fun address => ssa_emitEffect loop (.clear address (some origin))).live
  | .assignWhole place expr origin => (ssa_assignWholeStmt loop origin (ssa_sourcePlace loop place) (ssa_sourceExpr loop expr)).live
  | .ifS condition thenBlock none _ =>
      ((ssa_sourceExpr loop condition).bind fun value =>
        ssa_ifS_none_core loop value (ssa_sourceBlock loop thenBlock [] false).discard).live
  | .ifS condition thenBlock (some elseBlock) _ =>
      ((ssa_sourceExpr loop condition).bind fun value =>
        ssa_ifS_some_core loop value (ssa_sourceBlock loop thenBlock [] false).discard
          (ssa_sourceBlock loop elseBlock [] false).discard).live
  | .while condition body origin => ssa_whileStmt loop origin (ssa_sourceExpr loop condition)
      (fun depth exit header => (ssa_sourceBlock (some ⟨depth, exit, .jump header⟩) body [] false).discard)
  | .forRange slot lo hi body origin => (ssa_rangeStmt loop slot origin (ssa_sourceExpr loop lo) (ssa_sourceExpr loop hi)
      (fun depth exit header type counter =>
        (ssa_sourceBlock (some ⟨depth, exit, .next header type counter⟩) body [(slot, counter, origin)] false).discard)).live
  | .forEach slot none view byRef body origin => (ssa_eachStmt loop slot none byRef origin
      (ssa_sourceEachSource loop view) (fun depth exit header counter value =>
        (ssa_sourceBlock (some ⟨depth, exit, .next header .i64 counter⟩) body
          ((slot, value, origin) :: []) false).discard)).live
  | .forEach slot (some index) view byRef body origin => (ssa_eachStmt loop slot (some index) byRef origin
      (ssa_sourceEachSource loop view) (fun depth exit header counter value =>
        (ssa_sourceBlock (some ⟨depth, exit, .next header .i64 counter⟩) body
          ((slot, value, origin) :: [(index, counter, origin)]) false).discard)).live
  | .ret none origin => (ssa_returnStmt loop origin (by intro value equal; cases equal)).live
  | .ret (some expr) origin => (ssa_returnStmt loop origin (by intro value equal; cases equal; exact ssa_sourceExpr loop expr)).live
  | .brk origin => (ssa_breakStmt loop origin).live
  | .cont origin => (ssa_continueStmt loop origin).live
  | .print args origin => ((ssa_sourcePrintArgs loop args).bind fun parts => ssa_emitEffect loop (.print parts (some origin))).live
  | .assertS expr origin => ((ssa_sourceExpr loop expr).bind fun value => ssa_assert_core loop value origin).live
  | .abort _ origin => (ssa_emitTerm loop (.abort .userAbort (some origin)) (by simp [Term.successors])).live
  | .exit expr origin => ((ssa_sourceExpr loop expr).bind fun value => ssa_emitTerm loop (.exit value (some origin)) (by simp [Term.successors])).live

termination_by stmt => sizeOf stmt
decreasing_by all_goals simp_wf; all_goals omega

end

end Goose.Lower.Validation
