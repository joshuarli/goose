import Goose.Lower.DemandGeneratedConstruction
import Goose.Lower.DemandRuntimePrefix

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive ScalarExpression : Expr → Type where
  | literal (type : IntTy) (number : Int) : ScalarExpression (.lit type number)
  | boolean (value : Bool) : ScalarExpression (.bool value)
  | negate (child : Expr) : ScalarExpression (.not child)
  | unary (operation : UnOp) (child : Expr) (origin : OriginId) : ScalarExpression (.un operation child origin)
  | convert (kind : ConvKind) (target : IntTy) (child : Expr) (origin : OriginId) :
      ScalarExpression (.conv kind (.int target) child origin)
  | binary (operation : BinOp) (left right : Expr) (origin : OriginId) : ScalarExpression (.bin operation left right origin)
  | compare (operation : CmpOp) (left right : Expr) : ScalarExpression (.cmp operation left right)

def ScalarExpression.prefix {expression : Expr} (form : ScalarExpression expression) (le : LEnv) (before : LS) : LS :=
  match form with
  | .literal .. | .boolean .. => before
  | .negate child | .unary _ child _ | .convert _ _ child _ => (lowerExpr child le before).2
  | .binary _ left right _ | .compare _ left right => (lowerExpr right le (lowerExpr left le before).2).2

def ScalarExpression.operation {expression : Expr} (form : ScalarExpression expression) (le : LEnv) (before : LS) : Op :=
  match form with
  | .literal type number => .constInt type number
  | .boolean value => .constBool value
  | .negate child => .boolNot (lowerExpr child le before).1
  | .unary operation child origin =>
      .un operation (intTyOf (lowerExpr child le before).1 le (form.prefix le before)).1
        (lowerExpr child le before).1 (some origin)
  | .convert kind target child origin =>
      .conv kind (intTyOf (lowerExpr child le before).1 le (form.prefix le before)).1 target
        (lowerExpr child le before).1 (some origin)
  | .binary operation left right origin =>
      .bin operation (intTyOf (lowerExpr left le before).1 le (form.prefix le before)).1
        (lowerExpr left le before).1 (lowerExpr right le (lowerExpr left le before).2).1 (some origin)
  | .compare operation left right =>
      match (valTy (lowerExpr left le before).1 le (form.prefix le before)).1 with
      | .data (.int type) => .cmp operation type (lowerExpr left le before).1 (lowerExpr right le (lowerExpr left le before).2).1
      | _ => .boolCmp operation (lowerExpr left le before).1 (lowerExpr right le (lowerExpr left le before).2).1

theorem ScalarExpression.lower {expression : Expr} (form : ScalarExpression expression) (le : LEnv) (before : LS) :
    lowerExpr expression le before = emitDef (form.operation le before) le (form.prefix le before) := by
  cases form <;> simp only [operation, ScalarExpression.prefix, lowerExpr, bind_run, intTyOf_state, valTy_run]
  all_goals first | rfl | (split <;> simp_all)

def ScalarExpression.ownerExpression {expression : Expr} : ScalarExpression expression → Expr
  | .literal type number => .lit type number
  | .boolean value => .bool value
  | .negate child | .unary _ child _ | .convert _ _ child _ => child
  | .binary _ _ right _ | .compare _ _ right => right

def ScalarExpression.ownerPath {expression : Expr} (form : ScalarExpression expression) (path : List Nat) : List Nat :=
  match form with
  | .literal .. | .boolean .. => path
  | .negate .. | .unary .. | .convert .. => path ++ [0]
  | .binary .. | .compare .. => path ++ [1]

def ScalarExpression.boundary {expression : Expr} : ScalarExpression expression → DemandBoundary
  | .literal .. | .boolean .. => .entry
  | _ => .exit

def ScalarExpression.ownerBefore {expression : Expr} (form : ScalarExpression expression) (le : LEnv) (before : LS) : LS :=
  match form with
  | .binary _ left _ _ | .compare _ left _ => (lowerExpr left le before).2
  | _ => before

theorem ScalarExpression.ownerOccurrence {expression : Expr} (form : ScalarExpression expression)
    {m : Core.Module} {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
    (occurrence : GeneratedDemandOccurrence m function le root path (.expression expression) before) :
    GeneratedDemandOccurrence m function le root (form.ownerPath path) (.expression form.ownerExpression)
      (form.ownerBefore le before) := by
  cases form with
  | literal | boolean => exact occurrence
  | negate | unary | convert => exact .first occurrence (.expression rfl)
  | binary => exact .binaryRight occurrence
  | compare => exact .comparisonRight occurrence

structure GeneratedScalarSite {expression : Expr} (form : ScalarExpression expression)
    (m : Core.Module) (access : AccessEnv) (function : Func) (le : LEnv) (root : DemandNode)
    (path : List Nat) (before : LS) (required : RetainedSsaMap) (point : Pt) : Prop where
  occurrence : GeneratedDemandOccurrence m function le root path (.expression expression) before
  rows : GeneratedDemandRows m access (form.ownerOccurrence occurrence) required
  atPoint : (form.prefix le before).pp = some point
  extended : ExtT (lowerExpr expression le before).2 function.blocks

theorem GeneratedScalarSite.instruction {expression : Expr} {form : ScalarExpression expression}
    {m : Core.Module} {access : AccessEnv} {function : Func} {le : LEnv} {root : DemandNode}
    {path : List Nat} {before : LS} {required : RetainedSsaMap} {point : Pt}
    (site : GeneratedScalarSite form m access function le root path before required point) :
    instAt function point = some (.def (lowerExpr expression le before).1 (form.operation le before)) := by
  have extended : ExtT (emitDef (form.operation le before) le (form.prefix le before)).2 function.blocks := by
    simpa only [form.lower] using site.extended
  have emitted : emitDef (form.operation le before) le (form.prefix le before) =
      ((emitDef (form.operation le before) le (form.prefix le before)).1,
        (emitDef (form.operation le before) le (form.prefix le before)).2) := rfl
  have instruction := (emitDef_facts emitted site.atPoint extended).2.2.2.2
  simpa only [form.lower, instAt_eq] using instruction

def ScalarExpression.label {expression : Expr} (form : ScalarExpression expression) (path : List Nat) : DemandSourceLabel :=
  ⟨form.ownerPath path, .expression, form.boundary⟩

inductive GeneratedScalarInstruction (m : Core.Module) (access : AccessEnv) :
    Func → RetainedSsaMap → DemandSourceLabel → Pt → Inst → Prop where
  | scalar {expression : Expr} (form : ScalarExpression expression)
      {function : Func} {le : LEnv} {root : DemandNode} {path : List Nat} {before : LS}
      {required : RetainedSsaMap} {point : Pt}
      (site : GeneratedScalarSite form m access function le root path before required point) :
      GeneratedScalarInstruction m access function required (form.label path) point
        (.def (lowerExpr expression le before).1 (form.operation le before))

theorem GeneratedScalarInstruction.instruction {m : Core.Module} {access : AccessEnv} {function : Func}
    {required : RetainedSsaMap} {label : DemandSourceLabel} {point : Pt} {instruction : Inst}
    (site : GeneratedScalarInstruction m access function required label point instruction) :
    instAt function point = some instruction := by
  cases site with
  | scalar form generated => exact generated.instruction

theorem GeneratedScalarInstruction.requiredRows {m : Core.Module} {access : AccessEnv} {function : Func}
    {required : RetainedSsaMap} {label : DemandSourceLabel} {point : Pt} {instruction : Inst}
    (site : GeneratedScalarInstruction m access function required label point instruction) :
    ∃ (le : LEnv) (root : DemandNode) (expression : Expr) (before : LS)
      (occurrence : GeneratedDemandOccurrence m function le root label.path (.expression expression) before),
      GeneratedDemandRows m access occurrence required ∧ label.phase = .expression := by
  cases site with
  | scalar form generated => exact ⟨_, _, _, _, form.ownerOccurrence generated.occurrence, generated.rows, rfl⟩

end Goose.Lower
