import Goose.Lower.Validation.OperandEach

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem values_lowerPrintArgs : ∀ args le before parts after,
    lowerPrintArgs args le before = (parts, after) → after.cur.isSome = true →
      ∀ value ∈ parts.flatMap PrintPart.uses, value < after.vals.size
  | [], le, before, parts, after, run, _, value, member => by
    obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    simp at member
  | .text text :: rest, le, before, parts, after, run, live, value, member => by
    obtain ⟨parts, mid, restRun, pureRun⟩ := bind_eq.mp run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
    exact values_lowerPrintArgs rest _ _ _ _ restRun live value (by simpa [PrintPart.uses] using member)
  | .expr expr :: rest, le, before, parts, after, run, live, value, member => by
    obtain ⟨input, evaluated, exprRun, parts, prepared, partsRun, pureRun⟩ :=
      (by simpa only [lowerPrintArgs, bind_eq] using run)
    obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
    have either : value = input ∨ value ∈ parts.flatMap PrintPart.uses := by
      simpa [PrintPart.uses] using member
    rcases either with rfl | member
    · exact live_value_through (advB_lowerPrintArgs rest) (dead_lowerPrintArgs rest) partsRun
        (value_lowerExpr expr _ _ _ _ exprRun) live
    · exact values_lowerPrintArgs rest _ _ _ _ partsRun live value member

mutual

theorem operands_source_lowerExpr : ∀ expr : Expr, OperandRun (lowerExpr expr)
  | .structLit ty exprs => operands_lowerExpr_structLit ty exprs (operands_source_lowerExprs exprs)
  | .lit ty number => operands_lowerExpr_lit ty number
  | .bool value => operands_lowerExpr_bool value
  | .read place => operands_lowerExpr_read place (operands_source_lowerPlace place)
  | .ref mu place => operands_lowerExpr_ref mu place (operands_source_lowerPlace place)
  | .slice mu view lo hi origin => operands_lowerExpr_slice mu view lo hi origin
      (operands_source_lowerView view) (operands_source_lowerBound lo) (operands_source_lowerBound hi)
  | .len view => operands_lowerExpr_len view (operands_source_lowerView view)
  | .un op expr origin => operands_lowerExpr_un op expr origin (operands_source_lowerExpr expr)
  | .bin op left right origin => operands_lowerExpr_bin op left right origin
      (operands_source_lowerExpr left) (operands_source_lowerExpr right)
  | .cmp op left right => operands_lowerExpr_cmp op left right
      (operands_source_lowerExpr left) (operands_source_lowerExpr right)
  | .and left right => operands_lowerExpr_shortCircuit true left right
      (operands_source_lowerExpr left) (operands_source_lowerExpr right)
  | .or left right => operands_lowerExpr_shortCircuit false left right
      (operands_source_lowerExpr left) (operands_source_lowerExpr right)
  | .not expr => operands_lowerExpr_not expr (operands_source_lowerExpr expr)
  | .conv kind target expr origin => operands_lowerExpr_conv kind target expr origin (operands_source_lowerExpr expr)
  | .call context args origin => operands_lowerExpr_call context args origin (operands_source_lowerArgs args)
  | .push place expr origin => operands_lowerExpr_push place expr origin
      (operands_source_lowerPlace place) (operands_source_lowerExpr expr)
  | .pop place origin => operands_lowerExpr_pop place origin (operands_source_lowerPlace place)
  | .ifE condition trueArm falseArm => operands_lowerExpr_ifE condition trueArm falseArm
      (operands_source_lowerExpr condition)
      (fun le before result after run checked => operands_source_lowerBlock none trueArm [] true le before result after run checked trivial (by simp [PreOperandBounds]))
      (fun le before result after run checked => operands_source_lowerBlock none falseArm [] true le before result after run checked trivial (by simp [PreOperandBounds]))
  | .blockE body => fun le before result after run checked =>
      operands_source_lowerBlock none body [] true le before result after run checked trivial (by simp [PreOperandBounds])
  | .arrLit ty exprs => operands_lowerExpr_arrLit ty exprs (operands_source_lowerExprs exprs)
  | .fill ty expr => operands_lowerExpr_fill ty expr (operands_source_lowerExpr expr)

theorem operands_source_lowerExprs : ∀ exprs : List Expr, OperandRun (lowerExprs exprs)
  | [] => OperandRun.pure _
  | expr :: rest => OperandRun.bind (operands_source_lowerExpr expr) fun _ =>
      OperandRun.bind (operands_source_lowerExprs rest) fun _ => OperandRun.pure _

theorem operands_source_lowerArg : ∀ arg : Arg, OperandRun (lowerArg arg)
  | .byVal expr => operands_source_lowerExpr expr
  | .byRef mu place => operands_lowerExpr_ref mu place (operands_source_lowerPlace place)

theorem operands_source_lowerArgs : ∀ args : List Arg, OperandRun (lowerArgs args)
  | [] => OperandRun.pure _
  | arg :: rest => OperandRun.bind (operands_source_lowerArg arg) fun _ =>
      OperandRun.bind (operands_source_lowerArgs rest) fun _ => OperandRun.pure _

theorem operands_source_lowerPlace : ∀ place : Place, OperandRun (lowerPlace place)
  | .var slot => operands_lowerPlace_var slot
  | .global global => operands_lowerPlace_global global
  | .field place index => operands_lowerPlace_field place index (operands_source_lowerPlace place)
  | .deref expr => operands_source_lowerExpr expr
  | .elem view expr origin => operands_lowerPlace_elem view expr origin
      (operands_source_lowerView view) (operands_source_lowerExpr expr)

theorem operands_source_lowerView : ∀ view : View, OperandRun (lowerView view)
  | .of place => operands_lowerView (.of place) (operands_source_lowerPlace place)
  | .val expr => operands_lowerView (.val expr) (operands_source_lowerExpr expr)

theorem operands_source_lowerBound : ∀ bound : Bound, OperandRun (lowerBound bound)
  | .omitted => OperandRun.pure _
  | .expr expr | .fromEnd expr => OperandRun.bind (operands_source_lowerExpr expr) fun _ => OperandRun.pure _

theorem operands_source_lowerBlock (context : Option LoopCtx) : ∀ body : Core.Block, OperandBlock context body
  | .mk scope stmts tail => by
    intro pre want le before result after run checked counter preBounds
    exact operands_lowerBlock context pre want scope stmts tail
      (operands_source_lowerStmts context stmts)
      (by intro expr equal; cases equal; exact operands_source_lowerExpr expr)
      run checked counter preBounds

theorem operands_source_lowerStmts (context : Option LoopCtx) : ∀ stmts le before result after,
    lowerStmts context stmts le before = (result, after) → OperandBounds before →
      LoopOperandBounds context before → OperandBounds after
  | [], le, before, result, after, run, checked, _ => by
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact checked
  | stmt :: rest, le, before, result, after, run, checked, counter => by
    simp only [lowerStmts, bind_run, isLive, curBlock_run, pure_run] at run
    cases live : before.cur.isSome
    · simp only [live, Bool.false_eq_true, ↓reduceIte] at run
      obtain ⟨_, rfl⟩ := pure_eq.mp run
      exact checked
    · simp only [live, ↓reduceIte] at run
      obtain ⟨_, mid, first, remaining⟩ := bind_eq.mp run
      exact operands_source_lowerStmts context rest _ _ _ _ remaining
        (operands_source_lowerStmt context stmt _ _ _ _ first checked counter)
        (counter.mono (advB_lowerStmt context stmt _ _ _ _ first).vals)

theorem operands_source_lowerPrintArgs : ∀ args : List PrintArg, OperandRun (lowerPrintArgs args)
  | [] => OperandRun.pure _
  | .text text :: rest => OperandRun.bind (operands_source_lowerPrintArgs rest) fun _ => OperandRun.pure _
  | .expr expr :: rest => OperandRun.bind (operands_source_lowerExpr expr) fun _ =>
      OperandRun.bind (operands_source_lowerPrintArgs rest) fun _ => OperandRun.pure _

theorem operands_source_lowerStmt (context : Option LoopCtx) : ∀ stmt le before result after,
    lowerStmt context stmt le before = (result, after) → OperandBounds before →
      LoopOperandBounds context before → OperandBounds after
  | .letS slot expr origin => fun _ _ _ _ run checked _ =>
      operands_lowerStmt_letS context slot expr origin (operands_source_lowerExpr expr) _ _ _ _ run checked
  | .assign place expr origin => fun _ _ _ _ run checked _ =>
      operands_lowerStmt_assign context place expr origin (operands_source_lowerPlace place)
        (operands_source_lowerExpr expr) _ _ _ _ run checked
  | .assignOp op place expr origin => fun _ _ _ _ run checked _ =>
      operands_lowerStmt_assignOp context op place expr origin (operands_source_lowerPlace place)
        (operands_source_lowerExpr expr) _ _ _ _ run checked
  | .rebind slot expr origin => fun _ _ _ _ run checked _ =>
      operands_lowerStmt_rebind context slot expr origin (operands_source_lowerExpr expr) _ _ _ _ run checked
  | .expr expr origin => fun _ _ _ _ run checked _ =>
      operands_lowerStmt_expr context expr origin (operands_source_lowerExpr expr) _ _ _ _ run checked
  | .append place view origin => fun _ _ _ _ run checked _ =>
      operands_lowerStmt_append context place view origin (operands_source_lowerPlace place)
        (operands_source_lowerView view) _ _ _ _ run checked
  | .popN place expr origin => fun _ _ _ _ run checked _ =>
      operands_lowerStmt_popN context place expr origin (operands_source_lowerPlace place)
        (operands_source_lowerExpr expr) _ _ _ _ run checked
  | .resize place size fill origin => by
      intro le before result after run checked _
      exact operands_lowerStmt_resize context place size fill origin (operands_source_lowerPlace place)
        (operands_source_lowerExpr size) (by intro expr equal; cases equal; exact operands_source_lowerExpr expr)
        _ _ _ _ run checked
  | .clear place origin => fun _ _ _ _ run checked _ =>
      operands_lowerStmt_clear context place origin (operands_source_lowerPlace place) _ _ _ _ run checked
  | .assignWhole place expr origin => fun _ _ _ _ run checked _ =>
      operands_lowerStmt_assignWhole context place expr origin (operands_source_lowerPlace place)
        (operands_source_lowerExpr expr) _ _ _ _ run checked
  | .ifS condition trueArm falseArm origin => by
      intro le before result after run checked counter
      exact operands_lowerStmt_ifS context condition trueArm falseArm origin
        (operands_source_lowerExpr condition) (operands_source_lowerBlock context trueArm)
        (by intro body equal; cases equal; exact operands_source_lowerBlock context body) run checked counter
  | .while condition body origin => fun _ _ _ _ run checked _ =>
      operands_lowerStmt_while context condition body origin (operands_source_lowerExpr condition)
        (fun _ _ _ => operands_source_lowerBlock _ body) _ _ _ _ run checked
  | .forRange slot lo hi body origin => fun _ _ _ _ run checked _ =>
      operands_lowerStmt_forRange context slot lo hi body origin (operands_source_lowerExpr lo)
        (operands_source_lowerExpr hi) (fun _ _ _ _ _ => operands_source_lowerBlock _ body) _ _ _ _ run checked
  | .forEach slot index view byRef body origin => by
      intro le before result after run checked _
      apply operands_lowerStmt_forEach context slot index view byRef body origin ?_
        (fun _ _ _ _ => operands_source_lowerBlock _ body) _ _ _ _ run checked
      cases view with
      | of place => exact operands_source_lowerPlace place
      | val expr => exact operands_source_lowerExpr expr
  | .ret expr origin => by
      intro le before result after run checked _
      exact operands_lowerStmt_ret context expr origin
        (by intro value equal; cases equal; exact operands_source_lowerExpr value) _ _ _ _ run checked
  | .brk origin => fun _ _ _ _ run checked _ => operands_lowerStmt_brk context origin _ _ _ _ run checked
  | .cont origin => fun _ _ _ _ run checked counter => operands_lowerStmt_cont context origin run checked counter
  | .print args origin => by
      intro le before result after run checked _
      obtain ⟨parts, mid, argsRun, emission⟩ := bind_eq.mp run
      exact operands_emitEffect emission (operands_source_lowerPrintArgs args _ _ _ _ argsRun checked)
        (by simpa [Effect.uses] using values_lowerPrintArgs args _ _ _ _ argsRun)
  | .assertS condition origin => fun _ _ _ _ run checked _ =>
      operands_lowerStmt_assert context condition origin (operands_source_lowerExpr condition) _ _ _ _ run checked
  | .abort message origin => by
      intro le before result after run checked _
      exact operands_emitTerm run checked (by simp [Term.uses])
  | .exit expr origin => fun _ _ _ _ run checked _ =>
      operands_lowerStmt_exit context expr origin (operands_source_lowerExpr expr) _ _ _ _ run checked

end

end Goose.Lower.Validation
