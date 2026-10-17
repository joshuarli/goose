import Goose.Lower.Validation.ReplacementReconstructed
import Goose.Lower.Validation.ReplacementControl
import Goose.Lower.Validation.ReplacementEmissionMap

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ScalarInstruction (inst : Inst) : Prop :=
  ∃ value op, inst = .def value op ∧ ScalarOp op

inductive ScalarSourceExpr : Expr → Prop
  | int (type value) : ScalarSourceExpr (.lit type value)
  | bool (value) : ScalarSourceExpr (.bool value)
  | un (op origin) {expr} : ScalarSourceExpr expr → ScalarSourceExpr (.un op expr origin)
  | bin (op origin) {left right} : ScalarSourceExpr left → ScalarSourceExpr right →
      ScalarSourceExpr (.bin op left right origin)
  | cmp (op) {left right} : ScalarSourceExpr left → ScalarSourceExpr right →
      ScalarSourceExpr (.cmp op left right)
  | not {expr} : ScalarSourceExpr expr → ScalarSourceExpr (.not expr)
  | conv (kind target origin) {expr} : ScalarSourceExpr expr → ScalarSourceExpr (.conv kind target expr origin)

theorem emitsOnly_scalar (op : Op) (scalar : ScalarOp op) : EmitsOnlyRun ScalarInstruction (emitDef op) := by
  intro env before value after run
  exact emitsOnly_emitDef run ⟨before.vals.size, op, rfl, scalar⟩

theorem emitsOnly_valTy (property : Inst → Prop) (value : ValueId) :
    EmitsOnlyRun property (valTy value) :=
  .unchanged (fun env state => congrArg LS.blocks (valTy_run value env state))

theorem emitsOnly_intTyOf (property : Inst → Prop) (value : ValueId) :
    EmitsOnlyRun property (intTyOf value) := by
  unfold intTyOf
  apply EmitsOnlyRun.bind (emitsOnly_valTy property value)
  intro type
  split <;> exact .pure _ _

theorem scalarSource_lowerExpr {expr : Expr} (source : ScalarSourceExpr expr) :
    EmitsOnlyRun ScalarInstruction (lowerExpr expr) := by
  induction source with
  | int type value => exact emitsOnly_scalar _ (.constInt type value)
  | bool value => exact emitsOnly_scalar _ (.constBool value)
  | un op origin child ih =>
    simp only [lowerExpr]
    apply EmitsOnlyRun.bind ih
    intro value
    apply EmitsOnlyRun.bind (emitsOnly_intTyOf _ value)
    intro type
    exact emitsOnly_scalar _ (.un op type value (some origin))
  | bin op origin left right leftIH rightIH =>
    simp only [lowerExpr]
    apply EmitsOnlyRun.bind leftIH
    intro x
    apply EmitsOnlyRun.bind rightIH
    intro y
    apply EmitsOnlyRun.bind (emitsOnly_intTyOf _ x)
    intro type
    exact emitsOnly_scalar _ (.bin op type x y (some origin))
  | cmp op left right leftIH rightIH =>
    simp only [lowerExpr]
    apply EmitsOnlyRun.bind leftIH
    intro x
    apply EmitsOnlyRun.bind rightIH
    intro y
    apply EmitsOnlyRun.bind (emitsOnly_valTy _ x)
    intro type
    split
    · exact emitsOnly_scalar _ (.cmp _ _ _ _)
    · exact emitsOnly_scalar _ (.boolCmp _ _ _)
  | not child ih =>
    simp only [lowerExpr]
    apply EmitsOnlyRun.bind ih
    intro value
    exact emitsOnly_scalar _ (.boolNot value)
  | conv kind target origin child ih =>
    simp only [lowerExpr]
    apply EmitsOnlyRun.bind ih
    intro value
    apply EmitsOnlyRun.bind (emitsOnly_intTyOf _ value)
    intro type
    exact emitsOnly_scalar _ (.conv _ _ _ _ _)

theorem scalarSource_lowerExprs {exprs : List Expr}
    (source : ∀ expr ∈ exprs, ScalarSourceExpr expr) : EmitsOnlyRun ScalarInstruction (lowerExprs exprs) := by
  induction exprs with
  | nil => exact .pure _ []
  | cons expr rest ih =>
    simp only [lowerExprs]
    apply EmitsOnlyRun.bind (scalarSource_lowerExpr (source expr (by simp)))
    intro value
    apply EmitsOnlyRun.bind (ih (fun expr member => source expr (by simp [member])))
    intro values
    exact .pure _ _

theorem lowerExpr_scalar_source_apart
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
    (source : ScalarSourceExpr expr) (run : lowerExpr expr env before = (value, captured))
    (extension : captured.Ext state) :
    EmitsOnly (ReplacementInstApart module (func.valueTypes module) queries owner) before captured := by
  apply (scalarSource_lowerExpr source env before value captured run).map
  intro inst member scalar
  obtain ⟨value, op, rfl, scalar⟩ := scalar
  exact replacementScalarApart_of_source_graphs builder blocks slots globals sigs structs profile graphs
    (extension_inst_member extension member) scalar

end Goose.Lower.Validation
