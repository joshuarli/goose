import Goose.Lower.Validation.ReplacementBooleanSource
import Goose.Lower.Validation.SourceStatementTypingBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def IndependentOwnerInstruction (inst : Inst) : Prop :=
  ScalarControlInstruction inst ∨ ∃ value ty values, inst = .def value (.arrLit ty values) ∧
    ∀ element, arrayElem? ty = some element → element.flat = true

mutual
inductive IndependentOwnerExpr : Expr → Prop
  | literal (ty values) (scalars : ∀ expr ∈ values, ScalarBooleanExpr expr)
      (flat : ∀ element, arrayElem? ty = some element → element.flat = true) :
      IndependentOwnerExpr (.arrLit ty values)
  | conditional (condition) {yes no} (scalar : ScalarBooleanExpr condition)
      (yesIndependent : IndependentOwnerBlock yes) (noIndependent : IndependentOwnerBlock no) :
      IndependentOwnerExpr (.ifE condition yes no)
  | block {body} : IndependentOwnerBlock body → IndependentOwnerExpr (.blockE body)
inductive IndependentOwnerBlock : Core.Block → Prop
  | result (scope) {expr} : IndependentOwnerExpr expr → IndependentOwnerBlock (.mk scope [] (some expr))
  | prefixResult (scope statements) {expr} : (∀ stmt ∈ statements, ScalarControlStmt stmt) →
      IndependentOwnerExpr expr → IndependentOwnerBlock (.mk scope statements (some expr))
end

mutual
theorem independentOwner_lowerExpr {expr : Expr} (source : IndependentOwnerExpr expr) :
    EmitsOnlyRun IndependentOwnerInstruction (lowerExpr expr) := by
  cases source with
  | literal ty values scalars flat =>
    simp only [lowerExpr]
    apply EmitsOnlyRun.bind ((scalarBoolean_lowerExprs scalars).weaken (fun _ => Or.inl))
    intro args
    intro env before value after run
    exact emitsOnly_emitDef run (Or.inr ⟨before.vals.size, ty, args, rfl, flat⟩)
  | conditional condition scalar yes no =>
    simp only [lowerExpr]
    apply EmitsOnlyRun.bind ((scalarBoolean_lowerExpr scalar).weaken (fun _ => Or.inl))
    intro conditionValue
    apply EmitsOnlyRun.whenLive
    intro index
    apply EmitsOnlyRun.bind (emitsOnly_fork _ (fun term => Or.inl (Or.inr (.term term))) conditionValue)
    rintro ⟨yesBlock, noBlock⟩
    apply EmitsOnlyRun.bind (emitsOnly_setCur _ (some yesBlock))
    intro _
    apply EmitsOnlyRun.bind (independentOwner_lowerBlock yes)
    intro yesValue
    apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (fun _ _ => rfl))
    intro yesEnd
    apply EmitsOnlyRun.bind (emitsOnly_setCur _ (some noBlock))
    intro _
    apply EmitsOnlyRun.bind (independentOwner_lowerBlock no)
    intro noValue
    apply EmitsOnlyRun.bind (EmitsOnlyRun.unchanged (fun _ _ => rfl))
    intro noEnd
    apply EmitsOnlyRun.bind (emitsOnly_joinValue IndependentOwnerInstruction
      (fun (term : Term) => Or.inl (Or.inr (ReplacementControlInst.term term)))
      yesEnd noEnd yesValue noValue)
    intro result
    apply EmitsOnlyRun.bind
      (EmitsOnlyRun.unchanged
        (action := recordValueRootRecipe result _)
        (by
          intro env state
          rw [recordValueRootRecipe_run]))
    intro _
    exact .pure _ _
  | block body => exact independentOwner_lowerBlock body

theorem independentOwner_lowerBlock {body : Core.Block} (source : IndependentOwnerBlock body) :
    EmitsOnlyRun IndependentOwnerInstruction (lowerBlock none [] true body) := by
  cases source with
  | result scope expr =>
    simp only [lowerBlock]
    apply EmitsOnlyRun.bind (emitsOnly_emitEffect _ (Or.inl (Or.inr (.enter scope))))
    intro _
    apply EmitsOnlyRun.inScope
    simp only [initSlots, lowerStmts, lowerBlockValue]
    apply EmitsOnlyRun.bind (EmitsOnlyRun.pure _ ())
    intro _
    apply EmitsOnlyRun.bind (EmitsOnlyRun.pure _ ())
    intro _
    apply EmitsOnlyRun.bind (independentOwner_lowerExpr expr)
    intro value
    apply EmitsOnlyRun.bind (emitsOnly_emitEffect _ (Or.inl (Or.inr (.leave scope))))
    intro _
    exact .pure _ _
  | prefixResult scope statements prefixIndependent expr =>
    simp only [lowerBlock]
    apply EmitsOnlyRun.bind (emitsOnly_emitEffect _ (Or.inl (Or.inr (.enter scope))))
    intro _
    apply EmitsOnlyRun.inScope
    simp only [initSlots, lowerBlockValue]
    apply EmitsOnlyRun.bind (EmitsOnlyRun.pure _ ())
    intro _
    apply EmitsOnlyRun.bind ((scalarControl_lowerStmts prefixIndependent none).weaken (fun _ => Or.inl))
    intro _
    apply EmitsOnlyRun.bind (independentOwner_lowerExpr expr)
    intro value
    apply EmitsOnlyRun.bind (emitsOnly_emitEffect _ (Or.inl (Or.inr (.leave scope))))
    intro _
    exact .pure _ _

end

theorem independentOwner_literal_of_source {ty : Ty} {values : List Expr}
    {env : Core.TEnv} {result : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.arrLit ty values) start = .ok (result, finish))
    (scalars : ∀ expr ∈ values, ScalarBooleanExpr expr) : IndependentOwnerExpr (.arrLit ty values) :=
  .literal ty values scalars (fun _ shape => source_arrLit_element_flat source shape)

mutual
inductive IndependentOwnerShape : Expr → Prop
  | literal (ty values) : (∀ expr ∈ values, ScalarBooleanExpr expr) → IndependentOwnerShape (.arrLit ty values)
  | conditional (condition) {yes no} : ScalarBooleanExpr condition →
      IndependentOwnerBlockShape yes → IndependentOwnerBlockShape no → IndependentOwnerShape (.ifE condition yes no)
  | block {body} : IndependentOwnerBlockShape body → IndependentOwnerShape (.blockE body)
inductive IndependentOwnerBlockShape : Core.Block → Prop
  | result (scope) {expr} : IndependentOwnerShape expr → IndependentOwnerBlockShape (.mk scope [] (some expr))
  | prefixResult (scope statements) {expr} : (∀ stmt ∈ statements, ScalarControlStmt stmt) →
      IndependentOwnerShape expr → IndependentOwnerBlockShape (.mk scope statements (some expr))
end

mutual
theorem IndependentOwnerShape.fresh {expr : Expr} (shape : IndependentOwnerShape expr) : expr.freshOwner = true := by
  cases shape with
  | literal => rfl
  | conditional condition scalar yes no =>
    simp only [Core.Expr.freshOwner, IndependentOwnerBlockShape.fresh yes, IndependentOwnerBlockShape.fresh no,
      Bool.and_self]
  | block body => exact IndependentOwnerBlockShape.fresh body

theorem IndependentOwnerBlockShape.fresh {body : Core.Block} (shape : IndependentOwnerBlockShape body) :
    body.freshOwner = true := by
  cases shape with
  | result scope expr => exact IndependentOwnerShape.fresh expr
  | prefixResult scope statements prefixIndependent expr => exact IndependentOwnerShape.fresh expr
end

mutual
theorem independentOwner_of_source {expr : Expr} (shape : IndependentOwnerShape expr)
    {env : Core.TEnv} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env expr start = .ok (ty, finish)) : IndependentOwnerExpr expr := by
  cases shape with
  | literal ty values scalars => exact independentOwner_literal_of_source source scalars
  | conditional condition scalar yes no =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, yesSource, source⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, noSource, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp source
    exact .conditional condition scalar (independentOwnerBlock_of_source yes yesSource)
      (independentOwnerBlock_of_source no noSource)
  | block body => exact .block (independentOwnerBlock_of_source body source)

theorem independentOwnerBlock_of_source {body : Core.Block} (shape : IndependentOwnerBlockShape body)
    {env : Core.TEnv} {ty : Ty} {start finish : Nat}
    (source : Core.tyBlock env [] body start = .ok (ty, finish)) : IndependentOwnerBlock body := by
  cases shape with
  | result scope expr =>
    obtain ⟨_, _, _, _, _, _, _, child⟩ := tyBlock_checked_children source
    exact .result scope (independentOwner_of_source expr child)
  | prefixResult scope statements prefixIndependent expr =>
    obtain ⟨_, _, _, _, _, _, _, child⟩ := tyBlock_checked_children source
    exact .prefixResult scope statements prefixIndependent (independentOwner_of_source expr child)

end

theorem lowerExpr_independent_owner_apart
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
    (source : IndependentOwnerExpr expr) (run : lowerExpr expr env before = (value, captured))
    (extension : captured.Ext state) :
    EmitsOnly (ReplacementInstApart module (func.valueTypes module) queries owner) before captured := by
  apply (independentOwner_lowerExpr source env before value captured run).map
  intro inst member independent
  have retained := extension_inst_member extension member
  rcases independent with (scalar | control) | literal
  · obtain ⟨value, op, rfl, scalar⟩ := scalar
    exact replacementScalarApart_of_source_graphs builder blocks slots globals sigs structs profile graphs retained scalar
  · exact .control control
  · obtain ⟨value, ty, values, rfl, flat⟩ := literal
    exact replacementFlatLiteralApart_of_source_graphs builder blocks slots globals sigs structs profile graphs retained flat

theorem lowerExpr_owner_shape_apart
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
    {sourceEnv : Core.TEnv} {result : Ty} {start finish : Nat}
    (source : Core.tyExpr sourceEnv expr start = .ok (result, finish))
    (shape : IndependentOwnerShape expr) (run : lowerExpr expr env before = (value, captured))
    (extension : captured.Ext state) :
    EmitsOnly (ReplacementInstApart module (func.valueTypes module) queries owner) before captured :=
  lowerExpr_independent_owner_apart builder blocks slots globals sigs structs profile graphs
    (independentOwner_of_source shape source) run extension

end Goose.Lower.Validation
