import Goose.Lower.TypedExpressions
import Goose.Lower.SourceContexts
import Goose.GIR.Validate

namespace Goose.Lower.TypedExpressionChecks

open Goose.Core Goose.GIR Goose.Core.Sound

def sourceImpl : Impl :=
  { initImpl with body := .mk 0 [.expr (.not (.bool true)) 0,
    .expr (.call 1 [.byVal (.bool true), .byVal (.bool false)] 0) 0] none }

def boolCallee : Impl :=
  { name := "bools", params := #[⟨0, .byValue⟩, ⟨1, .byValue⟩], results := #[],
    vars := #[⟨"first", .bool, .immutable, 0, 0⟩, ⟨"second", .bool, .immutable, 0, 0⟩],
    body := .mk 0 [] none, summary := .unknown }

def sourceModule : Core.Module :=
  { files := #["typed.goose"], types := #[.bool], globals := #[], impls := #[sourceImpl, boolCallee],
    contexts := #[initContext, ⟨1, "bools", [], [], []⟩], entry := 0, origins := #[⟨0, 1, "expr"⟩] }

def enteredState : St := { St.initial with nextAct := 1, nextScope := 1 }

def sourceEnv : Env := ⟨#[], 0, [(0, 0)], 1⟩

def typingEnv : TEnv :=
  { mod := sourceModule, impl := some sourceImpl, vars := #[], visible := [], loops := 0,
    inExpr := false, scopes := [0], globalLimit := 0, initializing := none }

def rootsEnv : PEnv := ⟨sourceModule, sourceImpl, initContext, [0]⟩

def sourceWorld : World := ⟨0, fun _ _ => False, fun _ _ => False, {}, 0,
  fun _ _ => False, fun _ _ => False⟩

theorem initial_store (demanded : RootInst → Prop) : StoreInv sourceModule 0 enteredState demanded := by
  constructor
  · simp [enteredState, St.initial, Store.empty]
  · simp [enteredState, St.initial, Store.empty]
  · simp [enteredState, St.initial, Store.empty]
  · simp
  · simp [enteredState, St.initial, Store.empty]
  · simp [enteredState, St.initial, Store.empty]

theorem initial_frame : Core.Sound.Frame sourceModule sourceWorld typingEnv rootsEnv sourceEnv
    enteredState [] := by
  constructor
  all_goals first
    | rfl
    | exact initial_store _
    | simp [sourceWorld, typingEnv, rootsEnv, sourceEnv, sourceImpl, initImpl, initContext,
        OwnerParameterShape, PEnv.cont, PRef, enteredState, St.initial, Store.empty]

theorem call_frame : Core.Sound.Frame sourceModule { sourceWorld with E := { unknown := true } } typingEnv rootsEnv sourceEnv
    enteredState [] := by
  constructor
  all_goals first
    | rfl
    | exact initial_store _
    | simp [sourceWorld, typingEnv, rootsEnv, sourceEnv, sourceImpl, initImpl, initContext,
        OwnerParameterShape, PEnv.cont, PRef, enteredState, St.initial, Store.empty]

def boolSource (profile : NumProfile) : ExprSource ⟨profile, sourceModule⟩ sourceEnv (.bool true)
    enteredState :=
  { accepted := (by cbv), plans := #[], path := [], context := .pilot rfl [],
    observation := .empty, world := sourceWorld, typingEnv := typingEnv, rootsEnv := rootsEnv,
    typingStart := 0, typingEnd := 0, ty := .bool, rootsStart := ⟨0, {}⟩,
    rootsEnd := ⟨0, {}⟩, roots := [], active := by simp [typingEnv, EvaluationContext.ActiveMatches], access := trivial,
    protection := by simp [ShrinkProtected, sourceWorld],
    observed := ObservedSafe.empty _ _ _ _, classified := (by intro h; cases h),
    permission := Or.inl (by exact Nat.le_refl 0),
    frame := (by simpa [EvaluationContext.inputFuture, DemandNode.variables, Expr.variables, Arg.variables] using initial_frame), typed := rfl, rooted := rfl,
    effects := EffLe.refl _ }

def callSource (profile : NumProfile) : ExprSource ⟨profile, sourceModule⟩ sourceEnv
    (.call 1 [.byVal (.bool true), .byVal (.bool false)] 0)
    enteredState :=
  { accepted := (by cbv), plans := #[], path := [], context := .pilot rfl [],
    observation := .empty, world := { sourceWorld with E := { unknown := true } }, typingEnv := typingEnv, rootsEnv := rootsEnv,
    typingStart := 0, typingEnd := 0, ty := .unit, rootsStart := ⟨0, {}⟩,
    rootsEnd := ⟨0, { unknown := true }⟩, roots := [], active := by simp [typingEnv, EvaluationContext.ActiveMatches], access := trivial,
    protection := by simp [ShrinkProtected, sourceWorld],
    observed := ObservedSafe.empty _ _ _ _, classified := (by intro h; cases h),
    permission := Or.inl (by exact Nat.le_refl 0),
    frame := (by simpa [EvaluationContext.inputFuture, DemandNode.variables, Expr.variables, Arg.variables] using call_frame), typed := (by cbv), rooted := (by cbv),
    effects := EffLe.refl _ }

def notSource (profile : NumProfile) : ExprSource ⟨profile, sourceModule⟩ sourceEnv (.not (.bool true))
    enteredState :=
  { accepted := (by cbv), plans := #[], path := [], context := .pilot rfl [],
    observation := .empty, world := sourceWorld, typingEnv := typingEnv, rootsEnv := rootsEnv,
    typingStart := 0, typingEnd := 0, ty := .bool, rootsStart := ⟨0, {}⟩,
    rootsEnd := ⟨0, {}⟩, roots := [], active := by simp [typingEnv, EvaluationContext.ActiveMatches], access := trivial,
    protection := by simp [ShrinkProtected, sourceWorld],
    observed := ObservedSafe.empty _ _ _ _, classified := (by intro h; cases h),
    permission := Or.inl (by exact Nat.le_refl 0),
    frame := (by simpa [EvaluationContext.inputFuture, DemandNode.variables, Expr.variables, Arg.variables] using initial_frame), typed := rfl, rooted := rfl,
    effects := EffLe.refl _ }

theorem not_source_result (profile : NumProfile) :
    ExprResult (notSource profile) (.bool false) enteredState :=
  (notSource profile).result 2 (.bool false)
    (by simp [evalExpr, expectBool, pure_bind, pure_apply])

theorem not_child_source (profile : NumProfile) :
    ∃ child : ExprSource ⟨profile, sourceModule⟩ sourceEnv (.bool true) enteredState,
      child.typingEnv = typingEnv ∧ child.rootsEnv = rootsEnv ∧ child.ty = .bool ∧
      child.path = (notSource profile).path ++ [0] ∧ child.world = (notSource profile).world := by
  obtain ⟨child, typing, roots, type, metadata⟩ := (notSource profile).notChild
  exact ⟨child, typing, roots, type, metadata.path, metadata.world⟩

theorem bool_source_result (profile : NumProfile) :
    ExprResult (boolSource profile) (.bool true) enteredState :=
  (boolSource profile).result 1 (.bool true) (by simp [evalExpr, pure_apply])

theorem bool_source_metadata (profile : NumProfile) :
    SourceResults (boolSource profile).typingEnv (boolSource profile).rootsEnv [] := by
  intro impl hi
  change some sourceImpl = some impl at hi
  cases hi
  exact ⟨rfl, rfl⟩

theorem call_source_args (profile : NumProfile) :
    ∃ source : ArgsSource 3 ⟨profile, sourceModule⟩ sourceEnv
      [.byVal (.bool true), .byVal (.bool false)] enteredState, source.resultsMatch [] := by
  apply (callSource profile).callArgs
  intro impl hi
  change some sourceImpl = some impl at hi
  cases hi
  exact ⟨rfl, rfl⟩

#guard [NumProfile.release, .debug].all fun profile =>
  match Core.eval 80 profile sourceModule, GIR.run 160 profile (lower sourceModule) with
  | .done .returned "", .done .returned "" => true
  | _, _ => false

theorem reject_wrong_source_results : ¬ SourceResults typingEnv rootsEnv [.bool] := by
  intro h
  have := (h sourceImpl rfl).2
  cases this

#guard match Core.validate sourceModule, GIR.validate (lower sourceModule) with
  | .ok _, .ok _ => true
  | _, _ => false

def sliceHeaderModule : Core.Module :=
  let main : Impl :=
    { name := "main", params := #[], results := #[],
      vars := #[⟨"owner", .arr .bool 2, .immutable, 0, 0⟩,
        ⟨"slice", .slice .readOnly .bool, .mutable, 0, 0⟩],
      body := .mk 0 [.letS 0 (.arrLit (.arr .bool 2) [.bool true, .bool false]) 0,
        .letS 1 (.slice .readOnly (.of (.var 0)) .omitted .omitted 0) 0,
        .expr (.call 1 [.byRef .readOnly (.var 1), .byRef .readOnly (.var 0)] 0) 0] none,
      summary := .unknown }
  let callee : Impl :=
    { name := "header", params := #[⟨0, .byRef⟩, ⟨1, .byRef⟩], results := #[],
      vars := #[⟨"header", .ref .readOnly (.slice .readOnly .bool), .immutable, 0, 0⟩,
        ⟨"owner", .ref .readOnly (.arr .bool 2), .immutable, 0, 0⟩],
      body := .mk 0 [.expr (.read (.deref (.read (.var 0)))) 0] none,
      summary := .unknown }
  { files := #["slice-header.goose"],
    types := #[.bool, .arr .bool 2, .slice .readOnly .bool, .ref .readOnly (.slice .readOnly .bool), .ref .readOnly (.arr .bool 2)],
    globals := #[], impls := #[main, callee],
    contexts := #[⟨0, "main", [(1, [.local 0])], [], []⟩,
      ⟨1, "header", [(0, [.param 0]), (1, [.param 1])], [], [(0, [.param 1])]⟩],
    entry := 0, origins := #[⟨0, 1, "expr"⟩] }

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := { sliceHeaderModule with profile := artifact }
  match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := { sliceHeaderModule with profile := artifact }
  [NumProfile.release, .debug].all fun profile =>
    match Core.eval 120 profile source, GIR.run 240 profile (lower source) with
    | .done .returned "", .done .returned "" => true
    | _, _ => false

def unaryModule : Core.Module :=
  let main : Impl :=
    { initImpl with body := .mk 0 [
      .expr (.conv .as (.int .i8) (.lit .i64 7) 0) 0,
      .expr (.un .neg (.lit .i64 (-9223372036854775808)) 0) 0] none }
  { files := #["unary.goose"], types := #[.int .i64, .int .i8], globals := #[],
    impls := #[main], contexts := #[initContext], entry := 0,
    origins := #[⟨0, 1, "unary"⟩] }

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := { unaryModule with profile := artifact }
  match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := { unaryModule with profile := artifact }
  match Core.eval 80 .release source, GIR.run 160 .release (lower source),
      Core.eval 80 .debug source, GIR.run 160 .debug (lower source) with
  | .done .returned "", .done .returned "",
      .done (.aborted coreKind coreOrigin) "", .done (.aborted girKind girOrigin) "" =>
    coreKind == girKind && coreOrigin == girOrigin
  | _, _, _, _ => false

def binaryExpression : Expr := .bin .add (.lit .i64 9223372036854775807) (.lit .i64 1) 0

def binaryModule (artifact : ArtifactProfile) : Core.Module :=
  { files := #["binary.goose"], types := #[.int .i64],
    globals := #[⟨"sum", .int .i64, .mutable, binaryExpression, 0⟩],
    impls := #[initImpl], contexts := #[initContext], entry := 0,
    origins := #[⟨0, 1, "binary"⟩], profile := artifact }

theorem binary_claim (artifact : ArtifactProfile) (profile : NumProfile) :
    TypedExprClaim 5 ⟨profile, binaryModule artifact⟩ [.int .i64] binaryExpression :=
  typedExprClaim_bin (typedExprClaim_lit 4 _ _ .i64 9223372036854775807)
    (typedExprClaim_lit 4 _ _ .i64 1) .add 0

theorem binary_children_source (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (binaryModule artifact) = .ok ()) :
    ∃ left : ExprSource ⟨profile, binaryModule artifact⟩ ⟨#[], 0, [], 0⟩
        (.lit .i64 9223372036854775807) { St.initial with nextAct := 1 },
      ∃ right : ExprSource ⟨profile, binaryModule artifact⟩ ⟨#[], 0, [], 0⟩
        (.lit .i64 1) { St.initial with nextAct := 1 },
        left.typingEnv = right.typingEnv ∧ left.rootsEnv = right.rootsEnv := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, binaryModule artifact⟩) (state := St.initial) (g := 0)
    (global := ⟨"sum", .int .i64, .mutable, binaryExpression, 0⟩)
    accepted rfl (InitializedGlobals.initial _).invariant
  obtain ⟨intTy, left, hltyping, hlroots, hltype, _, next⟩ := source.binChildren .add 0
  obtain ⟨right, hrtyping, hrroots, hrtype, _⟩ := next 4 (.int .i64 9223372036854775807)
    { St.initial with nextAct := 1 } (by simp [evalExpr, pure_apply, St.initial])
  exact ⟨left, right, hltyping.trans hrtyping.symm, hlroots.trans hrroots.symm⟩

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := binaryModule artifact
  match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := binaryModule artifact
  match Core.eval 80 .release source, GIR.run 160 .release (lower source),
      Core.eval 80 .debug source, GIR.run 160 .debug (lower source) with
  | .done .returned "", .done .returned "",
      .done (.aborted .intOverflow 0) "", .done (.aborted .intOverflow 0) "" => true
  | _, _, _, _ => false

def comparisonArguments (booleans : Bool) : Expr × Expr :=
  if booleans then (.bool true, .bool true) else (.lit .i64 1, .lit .i64 1)

def comparisonModule (artifact : ArtifactProfile) (booleans : Bool) : Core.Module :=
  let arguments := comparisonArguments booleans
  { files := #["comparison.goose"], types := #[.bool, .int .i64],
    globals := #[⟨"equal", .bool, .mutable, .cmp .eq arguments.1 arguments.2, 0⟩],
    impls := #[{ initImpl with body := .mk 0 [.assertS (.read (.global 0)) 0] none }],
    contexts := #[initContext], entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := artifact }

theorem comparison_claim (artifact : ArtifactProfile) (profile : NumProfile) (booleans : Bool) :
    TypedExprClaim 5 ⟨profile, comparisonModule artifact booleans⟩ [.bool]
      (.cmp .eq (comparisonArguments booleans).1 (comparisonArguments booleans).2) := by
  cases booleans
  · exact typedExprClaim_cmp (typedExprClaim_lit 4 _ _ .i64 1) (typedExprClaim_lit 4 _ _ .i64 1) .eq
  · exact typedExprClaim_cmp (typedExprClaim_bool 4 _ _ true) (typedExprClaim_bool 4 _ _ true) .eq

theorem comparison_children_source (artifact : ArtifactProfile) (profile : NumProfile) (booleans : Bool)
    (accepted : Core.validate (comparisonModule artifact booleans) = .ok ()) :
    ∃ left : ExprSource ⟨profile, comparisonModule artifact booleans⟩ ⟨#[], 0, [], 0⟩
        (comparisonArguments booleans).1 { St.initial with nextAct := 1 },
      ∃ right : ExprSource ⟨profile, comparisonModule artifact booleans⟩ ⟨#[], 0, [], 0⟩
        (comparisonArguments booleans).2 { St.initial with nextAct := 1 },
        left.typingEnv = right.typingEnv ∧ left.rootsEnv = right.rootsEnv := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, comparisonModule artifact booleans⟩) (state := St.initial) (g := 0)
    (global := ⟨"equal", .bool, .mutable,
      .cmp .eq (comparisonArguments booleans).1 (comparisonArguments booleans).2, 0⟩)
    accepted rfl (InitializedGlobals.initial _).invariant
  obtain ⟨left, hltyping, hlroots, _, next⟩ := source.cmpChildren .eq
  obtain ⟨right, hrtyping, hrroots, _⟩ := next 4 (if booleans then .bool true else .int .i64 1)
    { St.initial with nextAct := 1 } (by cases booleans <;>
      simp [comparisonArguments, evalExpr, pure_apply, St.initial])
  exact ⟨left, right, hltyping.trans hrtyping.symm, hlroots.trans hrroots.symm⟩

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  [false, true].all fun booleans =>
    let source := comparisonModule artifact booleans
    match Core.validate source, GIR.validate (lower source) with
    | .ok _, .ok _ => true
    | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  [false, true].all fun booleans =>
    let source := comparisonModule artifact booleans
    [NumProfile.release, .debug].all fun profile =>
      match Core.eval 80 profile source, GIR.run 160 profile (lower source) with
      | .done .returned "", .done .returned "" => true
      | _, _ => false

def shortCircuitRight : Expr := .cmp .eq (.bin .div (.lit .i64 1) (.lit .i64 0) 0) (.lit .i64 0)

def shortCircuitExpression (isAnd boolean : Bool) : Expr :=
  if isAnd then .and (.bool boolean) shortCircuitRight else .or (.bool boolean) shortCircuitRight

def shortCircuitModule (artifact : ArtifactProfile) (isAnd boolean : Bool) : Core.Module :=
  { files := #["short-circuit.goose"], types := #[.bool, .int .i64],
    globals := #[⟨"result", .bool, .mutable, shortCircuitExpression isAnd boolean, 0⟩],
    impls := #[{ initImpl with body := .mk 0 [
      .assertS (if isAnd then .not (.read (.global 0)) else .read (.global 0)) 0] none }],
    contexts := #[initContext], entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := artifact }

theorem shortCircuit_claim (artifact : ArtifactProfile) (profile : NumProfile) (isAnd boolean : Bool) :
    TypedExprClaim 5 ⟨profile, shortCircuitModule artifact isAnd boolean⟩ [.bool]
      (shortCircuitExpression isAnd boolean) := by
  have right : TypedExprClaim 4 ⟨profile, shortCircuitModule artifact isAnd boolean⟩ [.bool]
      shortCircuitRight := typedExprClaim_cmp
    (typedExprClaim_bin (typedExprClaim_lit 2 _ _ .i64 1) (typedExprClaim_lit 2 _ _ .i64 0) .div 0)
    (typedExprClaim_lit 3 _ _ .i64 0) .eq
  cases isAnd
  · exact typedExprClaim_or (typedExprClaim_bool 4 _ _ boolean) right
  · exact typedExprClaim_and (typedExprClaim_bool 4 _ _ boolean) right

theorem shortCircuit_children_source (artifact : ArtifactProfile) (profile : NumProfile)
    (isAnd boolean : Bool) (accepted : Core.validate (shortCircuitModule artifact isAnd boolean) = .ok ()) :
    ∃ left : ExprSource ⟨profile, shortCircuitModule artifact isAnd boolean⟩ ⟨#[], 0, [], 0⟩
        (.bool boolean) { St.initial with nextAct := 1 },
      ∃ right : ExprSource ⟨profile, shortCircuitModule artifact isAnd boolean⟩ ⟨#[], 0, [], 0⟩
        shortCircuitRight { St.initial with nextAct := 1 },
        left.ty = .bool ∧ right.ty = .bool := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, shortCircuitModule artifact isAnd boolean⟩) (state := St.initial) (g := 0)
    (global := ⟨"result", .bool, .mutable, shortCircuitExpression isAnd boolean, 0⟩)
    accepted rfl (InitializedGlobals.initial _).invariant
  obtain ⟨left, hltyping, hlroots, hltype, next⟩ := source.shortCircuitChildren isAnd
  obtain ⟨right, hrtyping, hrroots, hrtype⟩ := next 4 (.bool boolean)
    { St.initial with nextAct := 1 } (by simp [evalExpr, pure_apply, St.initial])
  exact ⟨left, right, hltype, hrtype⟩

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  [false, true].all fun isAnd => [false, true].all fun boolean =>
    let source := shortCircuitModule artifact isAnd boolean
    match Core.validate source, GIR.validate (lower source) with
    | .ok _, .ok _ => true
    | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  [false, true].all fun isAnd => [false, true].all fun boolean =>
    let source := shortCircuitModule artifact isAnd boolean
    [NumProfile.release, .debug].all fun profile =>
      if isAnd == boolean then
        match Core.eval 80 profile source, GIR.run 160 profile (lower source) with
        | .done (.aborted .divZero 0) "", .done (.aborted .divZero 0) "" => true
        | _, _ => false
      else
        match Core.eval 80 profile source, GIR.run 160 profile (lower source) with
        | .done .returned "", .done .returned "" => true
        | _, _ => false

def fillModule (artifact : ArtifactProfile) : Core.Module :=
  { files := #["fill.goose"], types := #[.bool, .int .i64, .arr .bool 3],
    globals := #[⟨"filled", .arr .bool 3, .mutable, .fill (.arr .bool 3) (.bool true), 0⟩],
    impls := #[{ initImpl with body := .mk 0 [
      .assertS (.read (.elem (.of (.global 0)) (.lit .i64 0) 0)) 0,
      .assertS (.read (.elem (.of (.global 0)) (.lit .i64 2) 0)) 0] none }],
    contexts := #[initContext], entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := artifact }

theorem fill_claim (artifact : ArtifactProfile) (profile : NumProfile) :
    TypedExprClaim 3 ⟨profile, fillModule artifact⟩ [.arr .bool 3]
      (.fill (.arr .bool 3) (.bool true)) :=
  typedExprClaim_fill (typedExprClaim_bool 2 _ _ true) (.arr .bool 3)

theorem fill_child_source (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (fillModule artifact) = .ok ()) :
    ∃ child : ExprSource ⟨profile, fillModule artifact⟩ ⟨#[], 0, [], 0⟩ (.bool true)
      { St.initial with nextAct := 1 }, child.ty = .bool := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, fillModule artifact⟩) (state := St.initial) (g := 0)
    (global := ⟨"filled", .arr .bool 3, .mutable, .fill (.arr .bool 3) (.bool true), 0⟩)
    accepted rfl (InitializedGlobals.initial _).invariant
  obtain ⟨element, count, targetEq, child, hchildTyping, hchildRoots, childTy, _⟩ := source.fillChild _
  cases targetEq
  exact ⟨child, childTy⟩

def fieldType : Ty := .structT 0 (.cons .bool .nil)

def fieldModule (artifact : ArtifactProfile) : Core.Module :=
  { files := #["field.goose"], types := #[.bool, fieldType],
    structs := #[⟨1, #[⟨.bool, .mutable, .mutable, 0⟩]⟩],
    globals := #[⟨"owner", fieldType, .mutable, .structLit fieldType [.bool true], 0⟩,
      ⟨"field", .bool, .mutable, .read (.field (.global 0) 0), 0⟩],
    impls := #[{ initImpl with body := .mk 0 [.assertS (.read (.global 1)) 0] none }],
    contexts := #[initContext], entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := artifact }

def fieldPrefixState : St :=
  { St.initial with nextAct := 1, store := Store.empty.introduce (.global 0) (.record 0 #[.bool true]) }

theorem field_prefix (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (fieldModule artifact) = .ok ()) :
    InitializedGlobals (fieldModule artifact) 1 fieldPrefixState :=
  InitializedGlobals.afterInitializer (cfg := ⟨profile, fieldModule artifact⟩)
    (before := St.initial) (after := { St.initial with nextAct := 1 })
    (value := .record 0 #[.bool true]) (g := 0)
    (global := ⟨"owner", fieldType, .mutable, .structLit fieldType [.bool true], 0⟩)
    accepted rfl (InitializedGlobals.initial _) 2
    (by simp [evalExpr, fieldType, mapList, pure_apply, bind_apply, St.initial])

theorem field_owner_source (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (fieldModule artifact) = .ok ()) :
    ∃ child : PlaceSource ⟨profile, fieldModule artifact⟩ ⟨#[], 1, [], 0⟩ (.global 0)
      { fieldPrefixState with nextAct := 2 }, child.ty = fieldType := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, fieldModule artifact⟩) (state := fieldPrefixState) (g := 1)
    (global := ⟨"field", .bool, .mutable, .read (.field (.global 0) 0), 0⟩)
    accepted rfl (field_prefix artifact profile accepted).invariant
  obtain ⟨field, hfieldTyping, hfieldRoots⟩ := source.readChild
  obtain ⟨owner, hownerTyping, hownerRoots⟩ := field.fieldChild 0
  have ht := owner.typed
  rw [hownerTyping, hfieldTyping, htyping] at ht
  simp only [tyPlace] at ht
  inv at ht
  obtain ⟨_, ht⟩ := ht
  simp only [initEnv, fieldModule] at ht
  have ht' := (Core.Sound.st_pure_ok _ _ _).1 ht
  exact ⟨owner, congrArg (fun p => p.1.ty) ht'⟩

theorem field_claim (artifact : ArtifactProfile) (profile : NumProfile) :
    TypedExprClaim 4 ⟨profile, fieldModule artifact⟩ [.bool] (.read (.field (.global 0) 0)) :=
  typedExprClaim_read (typedPlaceClaim_field (typedPlaceClaim_global 2 _ _ 0) 0)

example : ∃ child : ExprSource ⟨.release, fillModule .pilot⟩ ⟨#[], 0, [], 0⟩ (.bool true)
    { St.initial with nextAct := 1 }, child.ty = .bool := fill_child_source .pilot .release (by cbv)

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := fillModule artifact
  match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard match Core.validate (fieldModule .shrink), GIR.validate (lower (fieldModule .shrink)) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard match Core.validate (fieldModule .pilot), GIR.validate (lower (fieldModule .pilot)) with
  | .error _, .error _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := fillModule artifact
  [NumProfile.release, .debug].all fun profile =>
    match Core.eval 100 profile source, GIR.run 200 profile (lower source) with
    | .done .returned "", .done .returned "" => true
    | _, _ => false

#guard [NumProfile.release, .debug].all fun profile =>
  let source := fieldModule .shrink
  match Core.eval 100 profile source, GIR.run 200 profile (lower source) with
  | .done .returned "", .done .returned "" => true
  | _, _ => false

def viewLengthModule (artifact : ArtifactProfile) : Core.Module :=
  { files := #["view-length.goose"], types := #[.bool, .int .i64, .arr .bool 3, .slice .readOnly .bool],
    globals := #[⟨"owner", .arr .bool 3, .mutable, .fill (.arr .bool 3) (.bool true), 0⟩,
      ⟨"sliceLength", .int .i64, .mutable,
        .len (.val (.slice .readOnly (.of (.global 0)) .omitted .omitted 0)), 0⟩,
      ⟨"ownerLength", .int .i64, .mutable, .len (.of (.global 0)), 0⟩],
    impls := #[{ initImpl with body := .mk 0 [
      .assertS (.cmp .eq (.read (.global 1)) (.lit .i64 3)) 0,
      .assertS (.cmp .eq (.read (.global 2)) (.lit .i64 3)) 0] none }],
    contexts := #[initContext], entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := artifact }

def viewOwnerState : St :=
  { St.initial with nextAct := 1, store := Store.empty.introduce (.global 0) (.fixed (Array.replicate 3 (.bool true))) }

theorem view_owner_prefix (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (viewLengthModule artifact) = .ok ()) :
    InitializedGlobals (viewLengthModule artifact) 1 viewOwnerState :=
  InitializedGlobals.afterInitializer (cfg := ⟨profile, viewLengthModule artifact⟩)
    (before := St.initial) (after := { St.initial with nextAct := 1 })
    (value := .fixed (Array.replicate 3 (.bool true))) (g := 0)
    (global := ⟨"owner", .arr .bool 3, .mutable, .fill (.arr .bool 3) (.bool true), 0⟩)
    accepted rfl (InitializedGlobals.initial _) 3
    (by simp [evalExpr, Core.expectFixedCount, pure_apply, bind_apply, St.initial])

theorem view_val_source (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (viewLengthModule artifact) = .ok ()) :
    Nonempty (ViewSource ⟨profile, viewLengthModule artifact⟩ ⟨#[], 1, [], 0⟩
      (.val (.slice .readOnly (.of (.global 0)) .omitted .omitted 0))
      { viewOwnerState with nextAct := 2 }) := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, viewLengthModule artifact⟩) (state := viewOwnerState) (g := 1)
    (global := ⟨"sliceLength", .int .i64, .mutable,
      .len (.val (.slice .readOnly (.of (.global 0)) .omitted .omitted 0)), 0⟩)
    accepted rfl (view_owner_prefix artifact profile accepted).invariant
  obtain ⟨view, hviewTyping, hviewRoots⟩ := source.lenChild
  exact ⟨view⟩

theorem view_of_claim (artifact : ArtifactProfile) (profile : NumProfile) :
    TypedExprClaim 4 ⟨profile, viewLengthModule artifact⟩ [.int .i64] (.len (.of (.global 0))) :=
  typedExprClaim_len (typedViewClaim_of (typedPlaceClaim_global 2 _ _ 0))

theorem view_val_child_source (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (viewLengthModule artifact) = .ok ()) :
    Nonempty (ExprSource ⟨profile, viewLengthModule artifact⟩ ⟨#[], 1, [], 0⟩
      (.slice .readOnly (.of (.global 0)) .omitted .omitted 0)
      { viewOwnerState with nextAct := 2 }) := by
  obtain ⟨source⟩ := view_val_source artifact profile accepted
  obtain ⟨child, htyping, hroots, mutability, htype⟩ := source.valChild
  exact ⟨child⟩

theorem view_val_result (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (viewLengthModule artifact) = .ok ()) :
    ∃ source : ViewSource ⟨profile, viewLengthModule artifact⟩ ⟨#[], 1, [], 0⟩
      (.val (.slice .readOnly (.of (.global 0)) .omitted .omitted 0))
      { viewOwnerState with nextAct := 2 },
      ViewResult source ⟨⟨.global 0, []⟩, 0, 3, false⟩ { viewOwnerState with nextAct := 2 } := by
  obtain ⟨source⟩ := view_val_source artifact profile accepted
  exact ⟨source, source.result 5 _ (by cbv)⟩

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := viewLengthModule artifact
  match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := viewLengthModule artifact
  [NumProfile.release, .debug].all fun profile =>
    match Core.eval 160 profile source, GIR.run 320 profile (lower source) with
    | .done .returned "", .done .returned "" => true
    | _, _ => false

def indexedModule (artifact : ArtifactProfile) (index : Int) : Core.Module :=
  { files := #["indexed.goose"], types := #[.bool, .int .i64, .arr .bool 3],
    globals := #[⟨"owner", .arr .bool 3, .mutable, .fill (.arr .bool 3) (.bool true), 0⟩,
      ⟨"selected", .bool, .mutable, .read (.elem (.of (.global 0)) (.lit .i64 index) 0), 0⟩],
    impls := #[{ initImpl with body := .mk 0 [.assertS (.read (.global 1)) 0] none }],
    contexts := #[initContext], entry := 0, origins := #[⟨0, 1, "index"⟩], profile := artifact }

theorem indexed_prefix (artifact : ArtifactProfile) (profile : NumProfile) (index : Int)
    (accepted : Core.validate (indexedModule artifact index) = .ok ()) :
    InitializedGlobals (indexedModule artifact index) 1 viewOwnerState :=
  InitializedGlobals.afterInitializer (cfg := ⟨profile, indexedModule artifact index⟩)
    (before := St.initial) (after := { St.initial with nextAct := 1 })
    (value := .fixed (Array.replicate 3 (.bool true))) (g := 0)
    (global := ⟨"owner", .arr .bool 3, .mutable, .fill (.arr .bool 3) (.bool true), 0⟩)
    accepted rfl (InitializedGlobals.initial _) 3
    (by simp [evalExpr, Core.expectFixedCount, pure_apply, bind_apply, St.initial])

theorem indexed_children_source (artifact : ArtifactProfile) (profile : NumProfile) (index : Int)
    (accepted : Core.validate (indexedModule artifact index) = .ok ()) :
    ∃ view : ViewSource ⟨profile, indexedModule artifact index⟩ ⟨#[], 1, [], 0⟩ (.of (.global 0))
      { viewOwnerState with nextAct := 2 },
      ∃ operand : ExprSource ⟨profile, indexedModule artifact index⟩ ⟨#[], 1, [], 0⟩ (.lit .i64 index)
        { viewOwnerState with nextAct := 2 }, view.typingEnv = operand.typingEnv := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, indexedModule artifact index⟩) (state := viewOwnerState) (g := 1)
    (global := ⟨"selected", .bool, .mutable, .read (.elem (.of (.global 0)) (.lit .i64 index) 0), 0⟩)
    accepted rfl (indexed_prefix artifact profile index accepted).invariant
  obtain ⟨place, hplaceTyping, hplaceRoots⟩ := source.readChild
  obtain ⟨intTy, view, hviewTyping, hviewRoots, next⟩ := place.elemChildren 0
  obtain ⟨operand, hoperandTyping, hoperandRoots, hoperandType⟩ := next 3
    ⟨⟨.global 0, []⟩, 0, 3, false⟩ { viewOwnerState with nextAct := 2 } (by cbv)
  exact ⟨view, operand, hviewTyping.trans hoperandTyping.symm⟩

theorem indexed_claim (artifact : ArtifactProfile) (profile : NumProfile) (index : Int) :
    TypedExprClaim 5 ⟨profile, indexedModule artifact index⟩ [.bool]
      (.read (.elem (.of (.global 0)) (.lit .i64 index) 0)) :=
  typedExprClaim_read (typedPlaceClaim_elem
    (typedViewClaim_of (typedPlaceClaim_global 2 _ _ 0)) (typedExprClaim_lit 3 _ _ .i64 index) 0)

#guard [ArtifactProfile.pilot, .shrink].all fun artifact => [2, 3].all fun index =>
  let source := indexedModule artifact index
  match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact => [NumProfile.release, .debug].all fun profile =>
  let within := indexedModule artifact 2
  let outside := indexedModule artifact 3
  match Core.eval 160 profile within, GIR.run 320 profile (lower within),
      Core.eval 160 profile outside, GIR.run 320 profile (lower outside) with
  | .done .returned "", .done .returned "",
      .done (.aborted .indexOob 0) "", .done (.aborted .indexOob 0) "" => true
  | _, _, _, _ => false

theorem view_val_claim (artifact : ArtifactProfile) (profile : NumProfile) :
    TypedExprClaim 7 ⟨profile, viewLengthModule artifact⟩ [.int .i64]
      (.len (.val (.slice .readOnly (.of (.global 0)) .omitted .omitted 0))) :=
  typedExprClaim_len (typedViewClaim_val (typedExprClaim_slice
    (typedViewClaim_of (typedPlaceClaim_global 3 _ _ 0)) (typedBoundClaim_omitted 4 _ _)
    (typedBoundClaim_omitted 4 _ _) .readOnly 0))

def boundedSlice (low : Int) : Expr :=
  .slice .readOnly (.of (.global 0)) (.expr (.lit .i64 low)) (.fromEnd (.lit .i64 1)) 0

def boundedSliceModule (artifact : ArtifactProfile) (low : Int) : Core.Module :=
  { files := #["bounded-slice.goose"], types := #[.bool, .int .i64, .arr .bool 3, .slice .readOnly .bool],
    globals := #[⟨"owner", .arr .bool 3, .mutable, .fill (.arr .bool 3) (.bool true), 0⟩,
      ⟨"length", .int .i64, .mutable, .len (.val (boundedSlice low)), 0⟩],
    impls := #[{ initImpl with body := .mk 0 [.assertS (.cmp .eq (.read (.global 1)) (.lit .i64 1)) 0] none }],
    contexts := #[initContext], entry := 0, origins := #[⟨0, 1, "slice"⟩], profile := artifact }

theorem bounded_slice_prefix (artifact : ArtifactProfile) (profile : NumProfile) (low : Int)
    (accepted : Core.validate (boundedSliceModule artifact low) = .ok ()) :
    InitializedGlobals (boundedSliceModule artifact low) 1 viewOwnerState :=
  InitializedGlobals.afterInitializer (cfg := ⟨profile, boundedSliceModule artifact low⟩)
    (before := St.initial) (after := { St.initial with nextAct := 1 })
    (value := .fixed (Array.replicate 3 (.bool true))) (g := 0)
    (global := ⟨"owner", .arr .bool 3, .mutable, .fill (.arr .bool 3) (.bool true), 0⟩)
    accepted rfl (InitializedGlobals.initial _) 3
    (by simp [evalExpr, Core.expectFixedCount, pure_apply, bind_apply, St.initial])

theorem bounded_slice_sources (artifact : ArtifactProfile) (profile : NumProfile) (low : Int)
    (accepted : Core.validate (boundedSliceModule artifact low) = .ok ()) :
    ∃ lower : BoundSource ⟨profile, boundedSliceModule artifact low⟩ ⟨#[], 1, [], 0⟩
        (.expr (.lit .i64 low)) { viewOwnerState with nextAct := 2 },
      ∃ upper : BoundSource ⟨profile, boundedSliceModule artifact low⟩ ⟨#[], 1, [], 0⟩
        (.fromEnd (.lit .i64 1)) { viewOwnerState with nextAct := 2 },
        lower.typingEnv = upper.typingEnv := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, boundedSliceModule artifact low⟩) (state := viewOwnerState) (g := 1)
    (global := ⟨"length", .int .i64, .mutable, .len (.val (boundedSlice low)), 0⟩)
    accepted rfl (bounded_slice_prefix artifact profile low accepted).invariant
  obtain ⟨view, hviewTyping, hviewRoots⟩ := source.lenChild
  obtain ⟨slice, hsliceTyping, hsliceRoots, mutable, hsliceType⟩ := view.valChild
  obtain ⟨sampled, hsampledTyping, hsampledRoots, next⟩ := slice.sliceChildren .readOnly 0
  obtain ⟨lower, hltyping, hlroots, nextLow⟩ := next 4 ⟨⟨.global 0, []⟩, 0, 3, false⟩
    { viewOwnerState with nextAct := 2 } (by cbv)
  obtain ⟨upper, hhtyping, hhroots⟩ := nextLow 4 low { viewOwnerState with nextAct := 2 }
    (by simp [evalBound, evalExpr, Core.expectInt, bind_apply, pure_apply])
  exact ⟨lower, upper, hltyping.trans hhtyping.symm⟩

theorem bounded_slice_claim (artifact : ArtifactProfile) (profile : NumProfile) (low : Int) :
    TypedExprClaim 7 ⟨profile, boundedSliceModule artifact low⟩ [.int .i64]
      (.len (.val (boundedSlice low))) :=
  typedExprClaim_len (typedViewClaim_val (typedExprClaim_slice
    (typedViewClaim_of (typedPlaceClaim_global 3 _ _ 0))
    (typedBoundClaim_expr (typedExprClaim_lit 3 _ _ .i64 low))
    (typedBoundClaim_fromEnd (typedExprClaim_lit 3 _ _ .i64 1)) .readOnly 0))

#guard [ArtifactProfile.pilot, .shrink].all fun artifact => [1, 3].all fun low =>
  let source := boundedSliceModule artifact low
  match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact => [NumProfile.release, .debug].all fun profile =>
  let within := boundedSliceModule artifact 1
  let outside := boundedSliceModule artifact 3
  match Core.eval 200 profile within, GIR.run 400 profile (lower within),
      Core.eval 200 profile outside, GIR.run 400 profile (lower outside) with
  | .done .returned "", .done .returned "",
      .done (.aborted .sliceOob 0) "", .done (.aborted .sliceOob 0) "" => true
  | _, _, _, _ => false

def popValues (nonempty : Bool) : List Expr := if nonempty then [.bool true] else []

def popModule (artifact : ArtifactProfile) (nonempty : Bool) : Core.Module :=
  { files := #["pop.goose"], types := #[.bool, .int .i64, .growshrink .bool],
    globals := #[⟨"owner", .growshrink .bool, .mutable, .arrLit (.growshrink .bool) (popValues nonempty), 0⟩,
      ⟨"popped", .bool, .mutable, .pop (.global 0) 0, 0⟩],
    impls := #[{ initImpl with body := .mk 0 [.assertS (.read (.global 1)) 0,
      .assertS (.cmp .eq (.len (.of (.global 0))) (.lit .i64 0)) 0] none }],
    contexts := #[initContext], entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := artifact }

def popPrefixState (nonempty : Bool) : St :=
  { St.initial with nextAct := 1, store := Store.empty.introduce (.global 0) (.resizable .bool (if nonempty then #[.bool true] else #[])) }

theorem pop_prefix (artifact : ArtifactProfile) (profile : NumProfile) (nonempty : Bool)
    (accepted : Core.validate (popModule artifact nonempty) = .ok ()) :
    InitializedGlobals (popModule artifact nonempty) 1 (popPrefixState nonempty) := by
  exact InitializedGlobals.afterInitializer (cfg := ⟨profile, popModule artifact nonempty⟩)
    (before := St.initial) (after := { St.initial with nextAct := 1 })
    (value := .resizable .bool (if nonempty then #[.bool true] else #[])) (g := 0)
    (global := ⟨"owner", .growshrink .bool, .mutable, .arrLit (.growshrink .bool) (popValues nonempty), 0⟩)
    accepted rfl (InitializedGlobals.initial _) 3
    (by cases nonempty <;> simp [evalExpr, popValues, mapList, Core.expectArrayLit,
      bind_apply, pure_apply, St.initial])

theorem pop_owner_source (artifact : ArtifactProfile) (profile : NumProfile) (nonempty : Bool)
    (accepted : Core.validate (popModule artifact nonempty) = .ok ()) :
    Nonempty (PlaceSource ⟨profile, popModule artifact nonempty⟩ ⟨#[], 1, [], 0⟩ (.global 0)
      { popPrefixState nonempty with nextAct := 2 }) := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, popModule artifact nonempty⟩) (state := popPrefixState nonempty) (g := 1)
    (global := ⟨"popped", .bool, .mutable, .pop (.global 0) 0, 0⟩)
    accepted rfl (pop_prefix artifact profile nonempty accepted).invariant
  obtain ⟨owner, hownerTyping, hownerRoots⟩ := source.popChild 0
  exact ⟨owner⟩

theorem pop_claim (artifact : ArtifactProfile) (profile : NumProfile) :
    TypedExprClaim 4 ⟨profile, popModule artifact true⟩ [.bool] (.pop (.global 0) 0) :=
  typedExprClaim_pop (typedPlaceClaim_global 3 _ _ 0) 0

#guard [false, true].all fun nonempty =>
  let source := popModule .shrink nonempty
  match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [false, true].all fun nonempty =>
  match Core.validate (popModule .pilot nonempty) with
  | .error _ => true
  | .ok _ => false

#guard [NumProfile.release, .debug].all fun profile =>
  let within := popModule .shrink true
  let empty := popModule .shrink false
  match Core.eval 160 profile within, GIR.run 320 profile (lower within),
      Core.eval 160 profile empty, GIR.run 320 profile (lower empty) with
  | .done .returned "", .done .returned "",
      .done (.aborted .popEmpty 0) "", .done (.aborted .popEmpty 0) "" => true
  | _, _, _, _ => false

def pushOwnerType : ArtifactProfile → Nat → Ty
  | .pilot, _ => .grow .bool
  | .shrink, capacity => .limited .bool capacity

def pushOrigin : ArtifactProfile → Option OriginId
  | .pilot => none
  | .shrink => some 0

def pushOwnerValue : ArtifactProfile → Nat → Val
  | .pilot, _ => .resizable .bool #[]
  | .shrink, capacity => .limited .bool capacity #[] 0

def pushModule (artifact : ArtifactProfile) (capacity : Nat) : Core.Module :=
  let ownerTy := pushOwnerType artifact capacity
  { files := #["push.goose"], types := #[.bool, .int .i64, ownerTy, .ref .mutable .bool],
    globals := #[⟨"owner", ownerTy, .mutable, .arrLit ownerTy [], 0⟩,
      ⟨"pushed", .bool, .mutable, .read (.deref (.push (.global 0) (.bool true) (pushOrigin artifact))), 0⟩],
    impls := #[{ initImpl with body := .mk 0 [.assertS (.read (.global 1)) 0,
      .assertS (.cmp .eq (.len (.of (.global 0))) (.lit .i64 1)) 0] none }],
    contexts := #[initContext], entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := artifact }

def pushPrefixState (artifact : ArtifactProfile) (capacity : Nat) : St :=
  { St.initial with nextAct := 1, store := Store.empty.introduce (.global 0) (pushOwnerValue artifact capacity) }

theorem push_prefix (artifact : ArtifactProfile) (profile : NumProfile) (capacity : Nat)
    (accepted : Core.validate (pushModule artifact capacity) = .ok ()) :
    InitializedGlobals (pushModule artifact capacity) 1 (pushPrefixState artifact capacity) := by
  exact InitializedGlobals.afterInitializer (cfg := ⟨profile, pushModule artifact capacity⟩)
    (before := St.initial) (after := { St.initial with nextAct := 1 })
    (value := pushOwnerValue artifact capacity) (g := 0)
    (global := ⟨"owner", pushOwnerType artifact capacity, .mutable,
      .arrLit (pushOwnerType artifact capacity) [], 0⟩)
    accepted rfl (InitializedGlobals.initial _) 3 (by cases artifact <;>
      simp [evalExpr, pushOwnerType, pushOwnerValue, mapList, Core.expectArrayLit,
        bind_apply, pure_apply, St.initial])

theorem push_children_source (artifact : ArtifactProfile) (profile : NumProfile) (capacity : Nat)
    (accepted : Core.validate (pushModule artifact capacity) = .ok ()) :
    ∃ owner : PlaceSource ⟨profile, pushModule artifact capacity⟩ ⟨#[], 1, [], 0⟩ (.global 0)
        { pushPrefixState artifact capacity with nextAct := 2 },
      ∃ value : ExprSource ⟨profile, pushModule artifact capacity⟩ ⟨#[], 1, [], 0⟩ (.bool true)
        { pushPrefixState artifact capacity with nextAct := 2 }, owner.typingEnv = value.typingEnv := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, pushModule artifact capacity⟩) (state := pushPrefixState artifact capacity) (g := 1)
    (global := ⟨"pushed", .bool, .mutable,
      .read (.deref (.push (.global 0) (.bool true) (pushOrigin artifact))), 0⟩)
    accepted rfl (push_prefix artifact profile capacity accepted).invariant
  obtain ⟨place, hplaceTyping, hplaceRoots⟩ := source.readChild
  obtain ⟨push, hpushTyping, hpushRoots, mutability, target, hpushType⟩ := place.derefChild (by rfl)
  obtain ⟨owner, hownerTyping, hownerRoots, next⟩ := push.pushChildren (pushOrigin artifact)
  obtain ⟨value, hvalueTyping, hvalueRoots⟩ := next 2 ⟨.global 0, []⟩
    { pushPrefixState artifact capacity with nextAct := 2 } (by simp [evalPlace, pure_apply, pushPrefixState])
  exact ⟨owner, value, hownerTyping.trans hvalueTyping.symm⟩

theorem push_claim (artifact : ArtifactProfile) (profile : NumProfile) (capacity : Nat) :
    TypedExprClaim 5 ⟨profile, pushModule artifact capacity⟩ [.bool]
      (.read (.deref (.push (.global 0) (.bool true) (pushOrigin artifact)))) :=
  typedExprClaim_read (typedPlaceClaim_deref
    (typedExprClaim_push (typedPlaceClaim_global 2 _ _ 0) (typedExprClaim_bool 2 _ _ true)
      (pushOrigin artifact)))

def fullPushModule : Core.Module :=
  let source := pushModule .shrink 1
  { source with globals := source.globals.modify 0 fun owner =>
      { owner with init := .arrLit owner.ty [.bool false] } }

def fullPushPrefixState : St :=
  { St.initial with nextAct := 1, store := Store.empty.introduce (.global 0) (.limited .bool 1 #[.bool false] 1) }

theorem full_push_prefix (profile : NumProfile) (accepted : Core.validate fullPushModule = .ok ()) :
    InitializedGlobals fullPushModule 1 fullPushPrefixState :=
  InitializedGlobals.afterInitializer (cfg := ⟨profile, fullPushModule⟩)
    (before := St.initial) (after := { St.initial with nextAct := 1 })
    (value := .limited .bool 1 #[.bool false] 1) (g := 0)
    (global := ⟨"owner", .limited .bool 1, .mutable, .arrLit (.limited .bool 1) [.bool false], 0⟩)
    accepted rfl (InitializedGlobals.initial _) 3
    (by simp [evalExpr, mapList, Core.expectArrayLit, bind_apply, pure_apply, St.initial])

theorem full_push_source (profile : NumProfile) (accepted : Core.validate fullPushModule = .ok ()) :
    Nonempty (ExprSource ⟨profile, fullPushModule⟩ ⟨#[], 1, [], 0⟩
      (.push (.global 0) (.bool true) (some 0)) { fullPushPrefixState with nextAct := 2 }) := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, fullPushModule⟩) (state := fullPushPrefixState) (g := 1)
    (global := ⟨"pushed", .bool, .mutable, .read (.deref (.push (.global 0) (.bool true) (some 0))), 0⟩)
    accepted rfl (full_push_prefix profile accepted).invariant
  obtain ⟨place, hplaceTyping, hplaceRoots⟩ := source.readChild
  obtain ⟨push, hpushTyping, hpushRoots, mutability, target, hpushType⟩ := place.derefChild (by rfl)
  exact ⟨push⟩

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := pushModule artifact 1
  match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard match Core.validate fullPushModule, GIR.validate (lower fullPushModule) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact => [NumProfile.release, .debug].all fun profile =>
  let source := pushModule artifact 1
  match Core.eval 160 profile source, GIR.run 320 profile (lower source) with
  | .done .returned "", .done .returned "" => true
  | _, _ => false

#guard [NumProfile.release, .debug].all fun profile =>
  let source := fullPushModule
  match Core.eval 160 profile source, GIR.run 320 profile (lower source) with
  | .done (.aborted .capacity 0) "", .done (.aborted .capacity 0) "" => true
  | _, _ => false

def aggregateModule (artifact : ArtifactProfile) : Core.Module :=
  { files := #["aggregate.goose"], types := #[.bool, .int .i64, .arr .bool 2],
    globals := #[⟨"owner", .arr .bool 2, .mutable,
      .arrLit (.arr .bool 2) [.bool true, .bool false], 0⟩],
    impls := #[{ initImpl with body := .mk 0 [
      .assertS (.read (.elem (.of (.global 0)) (.lit .i64 0) 0)) 0,
      .assertS (.not (.read (.elem (.of (.global 0)) (.lit .i64 1) 0))) 0] none }],
    contexts := #[initContext], entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := artifact }

theorem aggregate_claim (artifact : ArtifactProfile) (profile : NumProfile) :
    TypedExprClaim 3 ⟨profile, aggregateModule artifact⟩ [.arr .bool 2]
      (.arrLit (.arr .bool 2) [.bool true, .bool false]) := by
  apply typedExprClaim_arrLit
  apply typedExprsClaim
  intro expr h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact typedExprClaim_bool 2 _ _ _

theorem aggregate_sources (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (aggregateModule artifact) = .ok ()) :
    ∃ children : ExprsSource 2 ⟨profile, aggregateModule artifact⟩ ⟨#[], 0, [], 0⟩
      [.bool true, .bool false] { St.initial with nextAct := 1 },
      children.resultsMatch [.arr .bool 2] := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, aggregateModule artifact⟩) (state := St.initial) (g := 0)
    (global := ⟨"owner", .arr .bool 2, .mutable,
      .arrLit (.arr .bool 2) [.bool true, .bool false], 0⟩)
    accepted rfl (InitializedGlobals.initial _).invariant
  exact source.arrLitChildren 2 [.arr .bool 2] (by
    intro impl himpl
    rw [htyping] at himpl
    cases himpl)

theorem aggregate_second_source (artifact : ArtifactProfile) (profile : NumProfile)
    (accepted : Core.validate (aggregateModule artifact) = .ok ()) :
    ∃ child : ExprSource ⟨profile, aggregateModule artifact⟩ ⟨#[], 0, [], 0⟩
      (.bool false) { St.initial with nextAct := 1 },
      SourceResults child.typingEnv child.rootsEnv [.arr .bool 2] := by
  obtain ⟨children, metadata⟩ := aggregate_sources artifact profile accepted
  cases children with
  | cons first next =>
    have hdone : evalExpr 2 ⟨profile, aggregateModule artifact⟩ ⟨#[], 0, [], 0⟩
        (.bool true) { St.initial with nextAct := 1 } =
        .ok (.bool true) { St.initial with nextAct := 1 } := by simp [evalExpr, pure_apply]
    have hrest := metadata.2 (.bool true) _ hdone
    cases hnext : next (.bool true) _ hdone with
    | cons second nextSecond =>
      rw [hnext] at hrest
      exact ⟨second, hrest.1⟩

theorem struct_aggregate_claim (profile : NumProfile) :
    TypedExprClaim 3 ⟨profile, fieldModule .shrink⟩ [fieldType]
      (.structLit fieldType [.bool true]) := by
  apply typedExprClaim_structLit
  apply typedExprsClaim
  intro expr h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  subst expr
  exact typedExprClaim_bool 2 _ _ true

theorem struct_aggregate_source (profile : NumProfile)
    (accepted : Core.validate (fieldModule .shrink) = .ok ()) :
    ∃ children : ExprsSource 2 ⟨profile, fieldModule .shrink⟩ ⟨#[], 0, [], 0⟩
      [.bool true] { St.initial with nextAct := 1 }, children.resultsMatch [fieldType] := by
  obtain ⟨source, htyping, hroots, htype, hcount⟩ := acceptedGlobalActivation
    (cfg := ⟨profile, fieldModule .shrink⟩) (state := St.initial) (g := 0)
    (global := ⟨"owner", fieldType, .mutable, .structLit fieldType [.bool true], 0⟩)
    accepted rfl (InitializedGlobals.initial _).invariant
  exact source.structLitChildren 2 [fieldType] (by
    intro impl himpl
    rw [htyping] at himpl
    cases himpl)

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  let source := aggregateModule artifact
  match Core.validate source, GIR.validate (lower source) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact => [NumProfile.release, .debug].all fun profile =>
  let source := aggregateModule artifact
  match Core.eval 100 profile source, GIR.run 200 profile (lower source) with
  | .done .returned "", .done .returned "" => true
  | _, _ => false

#guard match (lowerGlobal (aggregateModule .pilot)
  ⟨"owner", .arr .bool 2, .mutable, .arrLit (.arr .bool 2) [.bool true, .bool false], 0⟩).init.blocks[0]?.map (·.insts) with
  | some [Inst.def 0 (.constBool true), Inst.def 1 (.constBool false),
      Inst.def 2 (.arrLit (.arr .bool 2) [0, 1]), Inst.term (.ret [2] (some 0))] => true
  | _ => false

end Goose.Lower.TypedExpressionChecks
