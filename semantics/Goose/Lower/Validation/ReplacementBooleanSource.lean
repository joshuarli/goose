import Goose.Lower.Validation.ReplacementScalarSource

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ScalarControlInstruction (inst : Inst) : Prop := ScalarInstruction inst ∨ ReplacementControlInst inst

inductive ScalarBooleanExpr : Expr → Prop
  | scalar {expr} : ScalarSourceExpr expr → ScalarBooleanExpr expr
  | and {left right} : ScalarBooleanExpr left → ScalarBooleanExpr right → ScalarBooleanExpr (.and left right)
  | or {left right} : ScalarBooleanExpr left → ScalarBooleanExpr right → ScalarBooleanExpr (.or left right)
  | not {expr} : ScalarBooleanExpr expr → ScalarBooleanExpr (.not expr)
  | cmp (op) {left right} : ScalarBooleanExpr left → ScalarBooleanExpr right → ScalarBooleanExpr (.cmp op left right)

theorem EmitsOnlyRun.weaken {property next : Inst → Prop} {action : B α}
    (emitted : EmitsOnlyRun property action) (transform : ∀ inst, property inst → next inst) :
    EmitsOnlyRun next action := by
  intro env before value after run
  exact (emitted env before value after run).map (fun inst _ valid => transform inst valid)

theorem scalarBoolean_lowerExpr {expr : Expr} (source : ScalarBooleanExpr expr) :
    EmitsOnlyRun ScalarControlInstruction (lowerExpr expr) := by
  induction source with
  | scalar source => exact (scalarSource_lowerExpr source).weaken (fun _ => Or.inl)
  | and left right leftIH rightIH =>
    simp only [lowerExpr]
    apply EmitsOnlyRun.bind leftIH
    intro value
    exact emitsOnly_shortCircuit (fun term => Or.inr (.term term)) true value rightIH
  | or left right leftIH rightIH =>
    simp only [lowerExpr]
    apply EmitsOnlyRun.bind leftIH
    intro value
    exact emitsOnly_shortCircuit (fun term => Or.inr (.term term)) false value rightIH
  | not child ih =>
    simp only [lowerExpr]
    apply EmitsOnlyRun.bind ih
    intro value
    exact (emitsOnly_scalar _ (.boolNot value)).weaken (fun _ => Or.inl)
  | cmp op left right leftIH rightIH =>
    simp only [lowerExpr]
    apply EmitsOnlyRun.bind leftIH
    intro x
    apply EmitsOnlyRun.bind rightIH
    intro y
    apply EmitsOnlyRun.bind (emitsOnly_valTy _ x)
    intro type
    split
    · exact (emitsOnly_scalar _ (.cmp _ _ _ _)).weaken (fun _ => Or.inl)
    · exact (emitsOnly_scalar _ (.boolCmp _ _ _)).weaken (fun _ => Or.inl)

theorem scalarBoolean_lowerExprs {exprs : List Expr}
    (source : ∀ expr ∈ exprs, ScalarBooleanExpr expr) : EmitsOnlyRun ScalarControlInstruction (lowerExprs exprs) := by
  induction exprs with
  | nil => exact .pure _ []
  | cons expr rest ih =>
    simp only [lowerExprs]
    apply EmitsOnlyRun.bind (scalarBoolean_lowerExpr (source expr (by simp)))
    intro value
    apply EmitsOnlyRun.bind (ih (fun expr member => source expr (by simp [member])))
    intro values
    exact .pure _ _

theorem lowerExpr_scalar_boolean_apart
    {module : GIR.Module} {func : Func} {le env : LEnv} {state before captured : LS}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
    (structs : module.structs = le.mod.structs)
    (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state)
    {queries : ReplacementQueries} {owner value : ValueId} {expr : Expr}
    (source : ScalarBooleanExpr expr) (run : lowerExpr expr env before = (value, captured))
    (extension : captured.Ext state) :
    EmitsOnly (ReplacementInstApart module (func.valueTypes module) queries owner) before captured := by
  apply (scalarBoolean_lowerExpr source env before value captured run).map
  intro inst member pureInst
  rcases pureInst with scalar | control
  · obtain ⟨value, op, rfl, scalar⟩ := scalar
    exact replacementScalarApart_of_source_graphs builder blocks slots globals sigs structs profile graphs
      (extension_inst_member extension member) scalar
  · exact .control control

inductive ScalarControlStmt : Stmt → Prop
  | expr (origin) {expr} : ScalarBooleanExpr expr → ScalarControlStmt (.expr expr origin)
  | assert (origin) {expr} : ScalarBooleanExpr expr → ScalarControlStmt (.assertS expr origin)
  | abort (message origin) : ScalarControlStmt (.abort message origin)
  | exit (origin) {expr} : ScalarBooleanExpr expr → ScalarControlStmt (.exit expr origin)

theorem scalarControl_lowerStmt {stmt : Stmt} (source : ScalarControlStmt stmt) (loop : Option LoopCtx) :
    EmitsOnlyRun ScalarControlInstruction (lowerStmt loop stmt) := by
  cases source with
  | expr origin scalar =>
    apply EmitsOnlyRun.bind (scalarBoolean_lowerExpr scalar)
    intro _
    exact .pure _ _
  | assert origin scalar =>
    apply EmitsOnlyRun.bind (scalarBoolean_lowerExpr scalar)
    intro value
    apply EmitsOnlyRun.whenLive
    intro index
    apply EmitsOnlyRun.bind (emitsOnly_fork _ (fun term => Or.inr (.term term)) value)
    rintro ⟨pass, fail⟩
    apply EmitsOnlyRun.bind (emitsOnly_setCur _ (some fail))
    intro _
    apply EmitsOnlyRun.bind (emitsOnly_emitTerm _ (Or.inr (.term _)))
    intro _
    exact emitsOnly_setCur _ (some pass)
  | abort message origin => exact emitsOnly_emitTerm _ (Or.inr (.term _))
  | exit origin scalar =>
    apply EmitsOnlyRun.bind (scalarBoolean_lowerExpr scalar)
    intro value
    exact emitsOnly_emitTerm _ (Or.inr (.term _))

theorem scalarControl_lowerStmts {stmts : List Stmt} (source : ∀ stmt ∈ stmts, ScalarControlStmt stmt)
    (loop : Option LoopCtx) : EmitsOnlyRun ScalarControlInstruction (lowerStmts loop stmts) := by
  induction stmts with
  | nil => exact .pure _ _
  | cons stmt rest ih =>
    simp only [lowerStmts]
    apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (fun _ _ => rfl))
    intro live
    split
    · apply EmitsOnlyRun.bind (scalarControl_lowerStmt (source stmt (by simp)) loop)
      intro _
      exact ih (fun stmt member => source stmt (by simp [member]))
    · exact .pure _ _

end Goose.Lower.Validation
