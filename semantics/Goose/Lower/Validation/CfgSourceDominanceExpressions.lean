import Goose.Lower.Validation.CfgSourceDominanceStart
import Goose.Lower.Validation.CfgSourceDominanceValueIf
import Goose.Lower.Validation.CfgSourceDominanceStatementIf
import Goose.Lower.Validation.CfgSourceDominanceControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ssa_structLit (loop : Option LoopCtx) (type : Ty) {expressions : List Expr}
    (source : SSARun loop [] id (lowerExprs expressions)) :
    SSARun loop [] (fun result => [result]) (lowerExpr (.structLit type expressions)) := by
  exact source.bind fun values => ssa_emitDef loop _

theorem ssa_arrLit (loop : Option LoopCtx) (type : Ty) {expressions : List Expr}
    (source : SSARun loop [] id (lowerExprs expressions)) :
    SSARun loop [] (fun result => [result]) (lowerExpr (.arrLit type expressions)) := by
  exact source.bind fun values => ssa_emitDef loop _

theorem ssa_readPlace (loop : Option LoopCtx) {place : Place}
    (source : SSARun loop [] (fun result => [result]) (lowerPlace place)) :
    SSARun loop [] (fun result => [result]) (lowerExpr (.read place)) :=
  source.bind fun _value => ssa_emitDef loop _

theorem ssa_refPlace (loop : Option LoopCtx) (mu : Mutability) {place : Place}
    (source : SSARun loop [] (fun result => [result]) (lowerPlace place)) :
    SSARun loop [] (fun result => [result]) (lowerExpr (.ref mu place)) :=
  source.bind fun value => ssa_borrowTo loop mu value

theorem ssa_slice (loop : Option LoopCtx) (mu : Mutability) (origin : OriginId)
    {view : View} {lo hi : Bound}
    (viewSource : SSARun loop [] (fun result => [result]) (lowerView view))
    (loSource : SSARun loop [] Bnd.uses (lowerBound lo))
    (hiSource : SSARun loop [] Bnd.uses (lowerBound hi)) :
    SSARun loop [] (fun result => [result]) (lowerExpr (.slice mu view lo hi origin)) := by
  refine viewSource.bind fun value => ?_
  refine (loSource.keep [value]).bind fun lower => ?_
  refine (show SSARun loop ([value] ++ lower.uses) (fun upper => ([value] ++ lower.uses) ++ upper.uses) (lowerBound hi) from by simpa only [List.append_nil] using hiSource.keep ([value] ++ lower.uses)).bind fun upper => ?_
  exact ssa_emitDef loop _

theorem ssa_unary (loop : Option LoopCtx) (op : UnOp) (origin : OriginId) {expr : Expr}
    (source : SSARun loop [] (fun result => [result]) (lowerExpr expr)) :
    SSARun loop [] (fun result => [result]) (lowerExpr (.un op expr origin)) := by
  refine source.bind fun value => ?_
  exact ((ssa_intTyOf loop value).keep [value]).bind fun type => ssa_emitDef loop _

theorem ssa_binary (loop : Option LoopCtx) (op : BinOp) (origin : OriginId) {left right : Expr}
    (leftSource : SSARun loop [] (fun result => [result]) (lowerExpr left))
    (rightSource : SSARun loop [] (fun result => [result]) (lowerExpr right)) :
    SSARun loop [] (fun result => [result]) (lowerExpr (.bin op left right origin)) := by
  refine leftSource.bind fun one => ?_
  refine (rightSource.keep [one]).bind fun two => ?_
  exact ((ssa_intTyOf loop one).keep [one, two]).bind fun type => ssa_emitDef loop _

theorem ssa_compare (loop : Option LoopCtx) (op : CmpOp) {left right : Expr}
    (leftSource : SSARun loop [] (fun result => [result]) (lowerExpr left))
    (rightSource : SSARun loop [] (fun result => [result]) (lowerExpr right)) :
    SSARun loop [] (fun result => [result]) (lowerExpr (.cmp op left right)) := by
  refine leftSource.bind fun one => ?_
  refine (rightSource.keep [one]).bind fun two => ?_
  refine ((ssa_valTy loop one).keep [one, two]).bind fun type => ?_
  cases type with
  | data type => cases type <;> exact ssa_emitDef loop _
  | view _ _ => exact ssa_emitDef loop _

theorem ssa_convert (loop : Option LoopCtx) (kind : ConvKind) (target : Ty) (origin : OriginId) {expr : Expr}
    (source : SSARun loop [] (fun result => [result]) (lowerExpr expr)) :
    SSARun loop [] (fun result => [result]) (lowerExpr (.conv kind target expr origin)) := by
  refine source.bind fun value => ?_
  exact ((ssa_intTyOf loop value).keep [value]).bind fun type => ssa_emitDef loop _

theorem ssa_call (loop : Option LoopCtx) (context : ContextId) (origin : OriginId) {args : List Arg}
    (source : SSARun loop [] id (lowerArgs args)) :
    SSARun loop [] (fun result => [result]) (lowerExpr (.call context args origin)) := by
  refine source.bind fun values => ?_
  refine (ssa_emitDef loop (.call context values (some origin))).bind fun value => ?_
  refine ((ssa_read loop).keep [value]).bind fun env => ?_
  split
  · exact ((ssa_emitTerm loop .unreachable (by simp [Term.successors])).keep [value]).bind fun _ => ssa_value loop value
  · exact ssa_value loop value

theorem ssa_push (loop : Option LoopCtx) (origin : Option OriginId) {place : Place} {expr : Expr}
    (placeSource : SSARun loop [] (fun result => [result]) (lowerPlace place))
    (exprSource : SSARun loop [] (fun result => [result]) (lowerExpr expr)) :
    SSARun loop [] (fun result => [result]) (lowerExpr (.push place expr origin)) := by
  exact placeSource.bind fun address => (exprSource.keep [address]).bind fun value => ssa_emitDef loop _

theorem ssa_ifExpr (loop : Option LoopCtx) {condition : Expr} {thenBlock elseBlock : Core.Block}
    (conditionSource : SSARun loop [] (fun result => [result]) (lowerExpr condition))
    (thenSource : SSARun loop [] (fun result => [result]) (lowerBlock none [] true thenBlock))
    (elseSource : SSARun loop [] (fun result => [result]) (lowerBlock none [] true elseBlock)) :
    SSARun loop [] (fun result => [result]) (lowerExpr (.ifE condition thenBlock elseBlock)) :=
  conditionSource.bind fun value => ssa_ifE_core loop value (sourceBlockScope thenBlock) thenSource elseSource

theorem ssa_exprs_cons (loop : Option LoopCtx) {expr : Expr} {rest : List Expr}
    (source : SSARun loop [] (fun result => [result]) (lowerExpr expr))
    (restSource : SSARun loop [] id (lowerExprs rest)) :
    SSARun loop [] id (lowerExprs (expr :: rest)) := by
  refine source.bind fun value => ?_
  exact (restSource.keep [value]).bind fun values =>
    SSARun.pure loop (value :: values) (value :: values) id (by simp)

theorem ssa_args_cons (loop : Option LoopCtx) {arg : Arg} {rest : List Arg}
    (source : SSARun loop [] (fun result => [result]) (lowerArg arg))
    (restSource : SSARun loop [] id (lowerArgs rest)) :
    SSARun loop [] id (lowerArgs (arg :: rest)) := by
  refine source.bind fun value => ?_
  exact (restSource.keep [value]).bind fun values =>
    SSARun.pure loop (value :: values) (value :: values) id (by simp)

theorem ssa_place_elem (loop : Option LoopCtx) (origin : OriginId) {view : View} {index : Expr}
    (viewSource : SSARun loop [] (fun result => [result]) (lowerView view))
    (indexSource : SSARun loop [] (fun result => [result]) (lowerExpr index)) :
    SSARun loop [] (fun result => [result]) (lowerPlace (.elem view index origin)) := by
  exact viewSource.bind fun value => (indexSource.keep [value]).bind fun ix => ssa_emitDef loop _

theorem ssa_eachSource_of (loop : Option LoopCtx) {place : Place}
    (source : SSARun loop [] (fun result => [result]) (lowerPlace place)) :
    SSARun loop [] (fun result => result.1.toList ++ [result.2]) (lowerEachSource (.of place)) := by
  cases place <;>
    (refine source.bind fun address => ?_
     refine (((ssa_emitDef loop (.snapshot _ address)).keep [address]).weaken (more := [address]) (by simp [Op.uses])).bind fun view => ?_
     exact SSARun.pure loop (some address, view) [address, view] (fun result => result.1.toList ++ [result.2]) (by simp))

theorem ssa_eachSource_val (loop : Option LoopCtx) {expr : Expr}
    (source : SSARun loop [] (fun result => [result]) (lowerExpr expr)) :
    SSARun loop [] (fun result => result.1.toList ++ [result.2]) (lowerEachSource (.val expr)) := by
  refine source.bind fun value => ?_
  refine (ssa_emitDef loop (.sliceView value)).bind fun view => ?_
  exact SSARun.pure loop (none, view) [view] (fun result => result.1.toList ++ [result.2]) (by simp)

end Goose.Lower.Validation
