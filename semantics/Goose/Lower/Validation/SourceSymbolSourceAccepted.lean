import Goose.Lower.Validation.SourceSymbolSourceFacts
import Goose.Lower.Validation.SourceEnvironment

namespace Goose.Lower.Validation.SourceSymbolSource

open Goose.Core Goose.Core.Sound

private theorem lookup_bound {array : Array α} {index : Nat} {value : α}
    (lookup : array[index]? = some value) : index < array.size :=
  (Array.getElem?_eq_some_iff.mp lookup).1

private theorem declare_bound {env : TEnv} {slot scope start finish : Nat} {localVar : LocalVar}
    (typed : declare env slot scope start = .ok (localVar, finish)) : slot < env.vars.size :=
  lookup_bound (declare_ok _ _ _ _ _ typed).2.1

private theorem declareIndex_bound {env : TEnv} {slot scope start finish : Nat}
    (typed : declareIndex env scope (some slot) start = .ok ((), finish)) : slot < env.vars.size := by
  have facts := (declareIndex_ok _ _ _ _ _ typed).2 slot rfl
  obtain ⟨_, localVar, row, _, _⟩ := facts
  exact lookup_bound row

private theorem sliceRefTy_some_within {env : TEnv} {expr : Expr} {ty : Ty}
    (lookup : sliceRefTy env expr = some ty) : Within env.mod env.vars (exprReferences expr) := by
  cases expr with
  | read place =>
    cases place with
    | var slot =>
      by_cases visible : env.visible.contains slot = true
      · simp only [sliceRefTy, visible, ite_true] at lookup
        cases row : env.vars[slot]? with
        | none => simp [row] at lookup
        | some localVar =>
          simpa [exprReferences, placeReferences, Reference.Within] using lookup_bound row
      · simp only [sliceRefTy, visible, ite_false, reduceCtorEq] at lookup
    | _ => simp [sliceRefTy] at lookup
  | _ => simp [sliceRefTy] at lookup

set_option maxHeartbeats 1600000 in
mutual

theorem fromExpr {env : TEnv} (expr : Expr) {ty : Ty} {start finish : Nat}
    (typed : tyExpr env expr start = .ok (ty, finish))
 : Within env.mod env.vars (exprReferences expr) := by
  cases expr with
  | read place =>
    simp only [tyExpr] at typed
    obtain ⟨info, next, placeTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
    simpa only [exprReferences] using fromPlace place placeTyped
  | blockE body =>
    simp only [tyExpr] at typed
    simpa only [exprReferences, exprEnv] using fromBlock body [] typed
  | ifE condition yes no =>
    simp only [tyExpr] at typed
    obtain ⟨conditionTy, first, conditionTyped, rest⟩ := (st_bind_ok _ _ _ _).mp typed
    obtain ⟨_, second, _, rest⟩ := (st_bind_ok _ _ _ _).mp rest
    obtain ⟨yesTy, third, yesTyped, rest⟩ := (st_bind_ok _ _ _ _).mp rest
    obtain ⟨noTy, fourth, noTyped, _⟩ := (st_bind_ok _ _ _ _).mp rest
    simp only [exprReferences, within_append]
    exact ⟨⟨fromExpr condition conditionTyped,
      by simpa only [exprEnv] using fromBlock yes [] yesTyped⟩,
      by simpa only [exprEnv] using fromBlock no [] noTyped⟩
  | call context args origin =>
    have originBound := Core.tyExpr_call_success_origin_bound typed
    have contextBound := Core.tyExpr_call_success_context_bound typed
    simp only [exprReferences, within_cons, Reference.Within]
    refine ⟨originBound, contextBound, ?_⟩
    cases contextRow : env.mod.contexts[context]? with
    | none => simp [tyExpr, contextRow, chk] at typed
    | some contextInfo =>
      cases implRow : env.mod.impls[contextInfo.impl]? with
      | none => simp [tyExpr, contextRow, implRow, chk] at typed
      | some callee =>
        simp only [tyExpr, contextRow, implRow] at typed
        try inv at typed
        repeat' first
          | contradiction
          | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
          | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
          | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
        all_goals
          exact fromArgs args callee.params.toList (by assumption)
            (by simpa using (show callee.params.size = args.length from by assumption))
  | push owner value origin =>
    cases origin <;> cases profile : env.mod.profile
    all_goals simp only [exprReferences, within_append, within_cons, within_nil, Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append, Reference.Within, true_and, and_true]
    all_goals repeat' apply And.intro
    all_goals simp only [tyExpr, profile] at typed
    all_goals try inv at typed
    all_goals repeat' first
      | assumption
      | (apply fromPlace <;> assumption)
      | assumption
      | (apply lookup_bound <;> assumption)
      | (apply declare_bound <;> assumption)
      | (apply declareIndex_bound <;> assumption)
      | (apply fromExpr <;> assumption)
      | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
      | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
      | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
      | (split at typed <;> try inv at typed)
      | contradiction
  | _ =>
    all_goals try simp only [exprReferences, within_append, within_cons, within_nil, Reference.Within, Option.toList, List.map_cons, List.map_nil, List.nil_append, List.singleton_append, true_and, and_true]
    all_goals repeat' apply And.intro
    all_goals
      try simp only [tyExpr] at typed
      try inv at typed
      repeat' first
      | contradiction
      | rfl
      | exact within_nil
      | trivial
      | assumption
      | (apply lookup_bound <;> assumption)
      | (apply declare_bound <;> assumption)
      | (apply declareIndex_bound <;> assumption)
      | (apply fromExpr <;> assumption)
      | (apply fromPlace <;> assumption)
      | (apply fromView <;> assumption)
      | (apply fromBound <;> assumption)
      | (apply fromBlock <;> assumption)
      | (apply fromExprsAs <;> assumption)
      | (apply fromStructExprs <;> assumption)
      | (apply fromPrintArgs <;> assumption)
      | (solve | simp_all only [])
      | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
      | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
      | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
      | (split at typed <;> try inv at typed)
termination_by sizeOf expr

theorem fromPlace {env : TEnv} (place : Place) {info : PlaceInfo} {start finish : Nat}
    (typed : tyPlace env place start = .ok (info, finish))
 : Within env.mod env.vars (placeReferences place) := by
  cases place with
  | deref expr =>
    simp only [tyPlace] at typed
    obtain ⟨source, next, sourceTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
    cases special : sliceRefTy env expr with
    | some ty =>
      simpa only [placeReferences] using sliceRefTy_some_within special
    | none =>
      simp only [special] at sourceTyped
      obtain ⟨ty, final, expressionTyped, _⟩ := (st_bind_ok _ _ _ _).mp sourceTyped
      simpa only [placeReferences] using fromExpr expr expressionTyped
  | global global =>
    by_cases initialized : global < env.globalLimit
    · simp only [tyPlace, initialized, ite_true] at typed
      cases row : env.mod.globals[global]? with
      | none => simp [row, chk] at typed
      | some localVar =>
        simpa [placeReferences, Reference.Within] using lookup_bound row
    · simp [tyPlace, initialized, chk] at typed
  | _ =>
    all_goals try simp only [placeReferences, within_append, within_cons, within_nil, Reference.Within, and_true]
    all_goals repeat' apply And.intro
    all_goals
      try simp only [tyPlace] at typed
      try inv at typed
      repeat' first
      | contradiction
      | rfl
      | exact within_nil
      | trivial
      | assumption
      | (apply lookup_bound <;> assumption)
      | (apply declare_bound <;> assumption)
      | (apply declareIndex_bound <;> assumption)
      | (apply fromExpr <;> assumption)
      | (apply fromPlace <;> assumption)
      | (apply fromView <;> assumption)
      | (apply fromBound <;> assumption)
      | (apply fromBlock <;> assumption)
      | (apply fromExprsAs <;> assumption)
      | (apply fromStructExprs <;> assumption)
      | (apply fromPrintArgs <;> assumption)
      | (solve | simp_all only [])
      | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
      | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
      | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
      | (split at typed <;> try inv at typed)
termination_by sizeOf place

theorem fromView {env : TEnv} (view : View) {info : Ty × Bool} {start finish : Nat}
    (typed : tyView env view start = .ok (info, finish))
 : Within env.mod env.vars (viewReferences view) := by
  cases view with
  | of place =>
    simp only [tyView] at typed
    obtain ⟨placeInfo, next, placeTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
    simpa only [viewReferences] using fromPlace place placeTyped
  | val expr =>
    simp only [tyView] at typed
    obtain ⟨ty, next, expressionTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
    simpa only [viewReferences] using fromExpr expr expressionTyped
termination_by sizeOf view

theorem fromBound {env : TEnv} (bound : Bound) {start finish : Nat}
    (typed : tyBound env bound start = .ok ((), finish))
 : Within env.mod env.vars (boundReferences bound) := by
  cases bound <;> simp only [boundReferences]
  all_goals
    try simp only [tyBound] at typed
    try inv at typed
    repeat' first
    | contradiction
    | rfl
    | exact within_nil
    | trivial
    | assumption
    | (apply lookup_bound <;> assumption)
    | (apply declare_bound <;> assumption)
    | (apply declareIndex_bound <;> assumption)
    | (apply fromExpr <;> assumption)
    | (apply fromPlace <;> assumption)
    | (apply fromView <;> assumption)
    | (apply fromBound <;> assumption)
    | (apply fromBlock <;> assumption)
    | (apply fromExprsAs <;> assumption)
    | (apply fromStructExprs <;> assumption)
    | (apply fromPrintArgs <;> assumption)
    | (solve | simp_all only [])
    | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
    | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
    | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
    | (split at typed <;> try inv at typed)

termination_by sizeOf bound

theorem fromExprsAs {env : TEnv} (exprs : List Expr) {element : Ty} {start finish : Nat}
    (typed : tyExprsAs env element exprs start = .ok ((), finish))
 : Within env.mod env.vars (exprs.flatMap exprReferences) := by
  cases exprs with
  | nil => exact within_nil
  | cons expr rest =>
    simp only [List.flatMap_cons, within_append]
    constructor
    all_goals
      simp only [tyExprsAs] at typed
      try inv at typed
      repeat' first
      | contradiction
      | rfl
      | exact within_nil
      | trivial
      | assumption
      | (apply lookup_bound <;> assumption)
      | (apply declare_bound <;> assumption)
      | (apply declareIndex_bound <;> assumption)
      | (apply fromExpr <;> assumption)
      | (apply fromPlace <;> assumption)
      | (apply fromView <;> assumption)
      | (apply fromBound <;> assumption)
      | (apply fromBlock <;> assumption)
      | (apply fromExprsAs <;> assumption)
      | (apply fromStructExprs <;> assumption)
      | (apply fromPrintArgs <;> assumption)
      | (solve | simp_all only [])
      | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
      | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
      | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
      | (split at typed <;> try inv at typed)
termination_by sizeOf exprs

theorem fromStructExprs {env : TEnv} (exprs : List Expr) (types : List Ty) {start finish : Nat}
    (typed : tyStructExprs env types exprs start = .ok ((), finish))
 : Within env.mod env.vars (exprs.flatMap exprReferences) := by
  cases exprs with
  | nil => exact within_nil
  | cons expr rest =>
    cases types with
    | nil => simp [tyStructExprs, chk] at typed
    | cons ty types =>
      simp only [List.flatMap_cons, within_append]
      constructor
      all_goals
        simp only [tyStructExprs] at typed
        try inv at typed
        repeat' first
        | contradiction
        | rfl
        | exact within_nil
        | trivial
        | assumption
        | (apply lookup_bound <;> assumption)
        | (apply declare_bound <;> assumption)
        | (apply declareIndex_bound <;> assumption)
        | (apply fromExpr <;> assumption)
        | (apply fromPlace <;> assumption)
        | (apply fromView <;> assumption)
        | (apply fromBound <;> assumption)
        | (apply fromBlock <;> assumption)
        | (apply fromExprsAs <;> assumption)
        | (apply fromStructExprs <;> assumption)
        | (apply fromPrintArgs <;> assumption)
        | (solve | simp_all only [])
        | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
        | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
        | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
        | (split at typed <;> try inv at typed)
termination_by sizeOf exprs

theorem fromArgs {env : TEnv} (args : List Arg) (params : List Param) {callee : Impl}
    {start finish : Nat} (typed : tyArgs env callee params args start = .ok ((), finish))
    (shape : params.length = args.length) :
    Within env.mod env.vars (args.flatMap argReferences) := by
  cases args with
  | nil => exact within_nil
  | cons arg rest =>
    cases params with
    | nil => simp at shape
    | cons param params =>
      have tailShape : params.length = rest.length := by simpa using shape
      cases row : callee.vars[param.var]? with
      | none =>
        cases arg <;> simp only [tyArgs, row] at typed
        all_goals try inv at typed
        all_goals contradiction
      | some localVar =>
        cases arg with
        | byVal expr =>
          simp only [List.flatMap_cons, argReferences, within_append]
          constructor
          · simp only [tyArgs, row] at typed
            try inv at typed
            repeat' first
            | contradiction
            | rfl
            | exact within_nil
            | trivial
            | assumption
            | (apply lookup_bound <;> assumption)
            | (apply declare_bound <;> assumption)
            | (apply declareIndex_bound <;> assumption)
            | (apply fromExpr <;> assumption)
            | (apply fromPlace <;> assumption)
            | (apply fromView <;> assumption)
            | (apply fromBound <;> assumption)
            | (apply fromBlock <;> assumption)
            | (apply fromExprsAs <;> assumption)
            | (apply fromStructExprs <;> assumption)
            | (apply fromPrintArgs <;> assumption)
            | (solve | simp_all only [])
            | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
            | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
            | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
            | (split at typed <;> try inv at typed)
          · simp only [tyArgs, row] at typed
            try inv at typed
            repeat' first
              | contradiction
              | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
              | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
              | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
            all_goals exact fromArgs rest params (by assumption) tailShape
        | byRef mutability place =>
          simp only [List.flatMap_cons, argReferences, within_append]
          constructor
          · simp only [tyArgs, row] at typed
            try inv at typed
            repeat' first
            | contradiction
            | rfl
            | exact within_nil
            | trivial
            | assumption
            | (apply lookup_bound <;> assumption)
            | (apply declare_bound <;> assumption)
            | (apply declareIndex_bound <;> assumption)
            | (apply fromExpr <;> assumption)
            | (apply fromPlace <;> assumption)
            | (apply fromView <;> assumption)
            | (apply fromBound <;> assumption)
            | (apply fromBlock <;> assumption)
            | (apply fromExprsAs <;> assumption)
            | (apply fromStructExprs <;> assumption)
            | (apply fromPrintArgs <;> assumption)
            | (solve | simp_all only [])
            | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
            | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
            | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
            | (split at typed <;> try inv at typed)
          · simp only [tyArgs, row] at typed
            try inv at typed
            repeat' first
              | contradiction
              | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
              | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
              | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
            all_goals exact fromArgs rest params (by assumption) tailShape
termination_by sizeOf args

theorem fromBlock {env : TEnv} (block : Block) (pre : List (VarId × Ty)) {ty : Ty}
    {start finish : Nat} (typed : tyBlock env pre block start = .ok (ty, finish))
 : Within env.mod env.vars (blockReferences block) := by
  cases block with
  | mk scope stmts value =>
    obtain ⟨_, initial, initialNext, after, afterNext, declared, body, result⟩ :=
      tyBlock_ok _ _ _ _ _ _ _ _ typed
    have initialTables := declarePre_tables pre declared
    have afterTables := tyStmts_tables stmts body
    have statements := fromStmts stmts body
    rw [initialTables.1, initialTables.2.1] at statements
    cases value with
    | none => simpa [blockReferences] using statements
    | some expr =>
      have tail := fromExpr expr result
      rw [afterTables.1, afterTables.2.1, initialTables.1, initialTables.2.1] at tail
      simpa only [blockReferences] using within_append.mpr ⟨statements, tail⟩
termination_by sizeOf block

theorem fromStmts {env after : TEnv} (stmts : List Stmt) {scope start finish : Nat}
    (typed : tyStmts env scope stmts start = .ok (after, finish)) :
    Within env.mod env.vars (stmts.flatMap stmtReferences) := by
  cases stmts with
  | nil => exact within_nil
  | cons stmt rest =>
    simp only [tyStmts] at typed
    obtain ⟨mid, next, first, restTyped⟩ := (st_bind_ok _ _ _ _).mp typed
    have head := fromStmt stmt first
    have tail := fromStmts rest restTyped
    have tables := tyStmt_tables stmt first
    rw [tables.1, tables.2.1] at tail
    exact within_append.mpr ⟨head, tail⟩
termination_by sizeOf stmts

theorem fromPrintArgs {env : TEnv} (args : List PrintArg) {start finish : Nat}
    (typed : tyPrintArgs env args start = .ok ((), finish))
 : Within env.mod env.vars (args.flatMap printReferences) := by
  cases args with
  | nil => exact within_nil
  | cons arg rest =>
    cases arg with
    | text text =>
      simpa only [List.flatMap_cons, printReferences, List.nil_append] using
        fromPrintArgs rest typed
    | expr expr =>
      simp only [List.flatMap_cons, printReferences, within_append]
      constructor
      all_goals
        simp only [tyPrintArgs] at typed
        try inv at typed
        repeat' first
        | contradiction
        | rfl
        | exact within_nil
        | trivial
        | assumption
        | (apply lookup_bound <;> assumption)
        | (apply declare_bound <;> assumption)
        | (apply declareIndex_bound <;> assumption)
        | (apply fromExpr <;> assumption)
        | (apply fromPlace <;> assumption)
        | (apply fromView <;> assumption)
        | (apply fromBound <;> assumption)
        | (apply fromBlock <;> assumption)
        | (apply fromExprsAs <;> assumption)
        | (apply fromStructExprs <;> assumption)
        | (apply fromPrintArgs <;> assumption)
        | (solve | simp_all only [])
        | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
        | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
        | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
        | (split at typed <;> try inv at typed)
termination_by sizeOf args

theorem fromStmt {env after : TEnv} (stmt : Stmt) {scope start finish : Nat}
    (typed : tyStmt env scope stmt start = .ok (after, finish))
 :
    Within env.mod env.vars (stmtReferences stmt) := by
  have originBound := Core.tyStmt_success_origin_bound typed
  cases stmt
  case «while» condition body origin =>
    all_goals try simp only [stmtReferences, within_cons, within_append, within_nil, Reference.Within, Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append, stmtSourceOrigin, and_true, true_and]
    all_goals simp only [stmtSourceOrigin] at originBound
    all_goals repeat' apply And.intro
    all_goals
      try simp only [tyStmt] at typed
      try inv at typed
      repeat' first
      | contradiction
      | rfl
      | exact within_nil
      | trivial
      | assumption
      | (apply lookup_bound <;> assumption)
      | (apply declare_bound <;> assumption)
      | (apply declareIndex_bound <;> assumption)
      | (apply fromExpr <;> assumption)
      | (apply fromPlace <;> assumption)
      | (apply fromView <;> assumption)
      | (apply fromBound <;> assumption)
      | (apply fromBlock (env := { env with loops := env.loops + 1 }) <;> assumption)
      | (apply fromBlock <;> assumption)
      | (apply fromExprsAs <;> assumption)
      | (apply fromStructExprs <;> assumption)
      | (apply fromPrintArgs <;> assumption)
      | (subst after; rfl)
      | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
      | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
      | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
      | (split at typed <;> try inv at typed)
  case forRange slot lo hi body origin =>
    all_goals try simp only [stmtReferences, within_cons, within_append, within_nil, Reference.Within, Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append, stmtSourceOrigin, and_true, true_and]
    all_goals simp only [stmtSourceOrigin] at originBound
    all_goals repeat' apply And.intro
    all_goals
      try simp only [tyStmt] at typed
      try inv at typed
      repeat' first
      | contradiction
      | rfl
      | exact within_nil
      | trivial
      | assumption
      | (apply lookup_bound <;> assumption)
      | (apply declare_bound <;> assumption)
      | (apply declareIndex_bound <;> assumption)
      | (apply fromExpr <;> assumption)
      | (apply fromPlace <;> assumption)
      | (apply fromView <;> assumption)
      | (apply fromBound <;> assumption)
      | (apply fromBlock (env := { env with loops := env.loops + 1, visible := slot :: env.visible }) <;> assumption)
      | (apply fromBlock <;> assumption)
      | (apply fromExprsAs <;> assumption)
      | (apply fromStructExprs <;> assumption)
      | (apply fromPrintArgs <;> assumption)
      | (subst after; rfl)
      | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
      | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
      | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
      | (split at typed <;> try inv at typed)
  case forEach slot index view byRef body origin =>
    cases index with
    | none =>
      all_goals try simp only [stmtReferences, within_cons, within_append, within_nil, Reference.Within, Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append, stmtSourceOrigin, and_true, true_and]
      all_goals simp only [stmtSourceOrigin] at originBound
      all_goals repeat' apply And.intro
      all_goals
        try simp only [tyStmt] at typed
        try inv at typed
        repeat' first
        | contradiction
        | rfl
        | exact within_nil
        | trivial
        | assumption
        | (apply lookup_bound <;> assumption)
        | (apply declare_bound <;> assumption)
        | (apply declareIndex_bound <;> assumption)
        | (apply fromExpr <;> assumption)
        | (apply fromPlace <;> assumption)
        | (apply fromView <;> assumption)
        | (apply fromBound <;> assumption)
        | (apply fromBlock (env := { env with loops := env.loops + 1, visible := slot :: env.visible }) <;> assumption)
        | (apply fromBlock <;> assumption)
        | (apply fromExprsAs <;> assumption)
        | (apply fromStructExprs <;> assumption)
        | (apply fromPrintArgs <;> assumption)
        | (subst after; rfl)
        | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
        | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
        | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
        | (split at typed <;> try inv at typed)
    | some index =>
      all_goals try simp only [stmtReferences, within_cons, within_append, within_nil, Reference.Within, Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append, stmtSourceOrigin, and_true, true_and]
      all_goals simp only [stmtSourceOrigin] at originBound
      all_goals repeat' apply And.intro
      all_goals
        try simp only [tyStmt] at typed
        try inv at typed
        repeat' first
        | contradiction
        | rfl
        | exact within_nil
        | trivial
        | assumption
        | (apply lookup_bound <;> assumption)
        | (apply declare_bound <;> assumption)
        | (apply declareIndex_bound <;> assumption)
        | (apply fromExpr <;> assumption)
        | (apply fromPlace <;> assumption)
        | (apply fromView <;> assumption)
        | (apply fromBound <;> assumption)
        | (apply fromBlock (env := { env with loops := env.loops + 1, visible := slot :: [index] ++ env.visible }) <;> assumption)
        | (apply fromBlock <;> assumption)
        | (apply fromExprsAs <;> assumption)
        | (apply fromStructExprs <;> assumption)
        | (apply fromPrintArgs <;> assumption)
        | (subst after; rfl)
        | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
        | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
        | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
        | (split at typed <;> try inv at typed)
  case' resize owner size fill origin => cases fill
  case' ifS condition thenBlock otherwise origin => cases otherwise
  case' ret value origin => cases value
  all_goals try simp only [stmtReferences, within_cons, within_append, within_nil, Reference.Within, Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append, stmtSourceOrigin, and_true, true_and]
  all_goals simp only [stmtSourceOrigin] at originBound
  all_goals repeat' apply And.intro
  all_goals
    try simp only [tyStmt] at typed
    try inv at typed
    repeat' first
    | contradiction
    | rfl
    | exact within_nil
    | trivial
    | assumption
    | (apply lookup_bound <;> assumption)
    | (apply declare_bound <;> assumption)
    | (apply declareIndex_bound <;> assumption)
    | (apply fromExpr <;> assumption)
    | (apply fromPlace <;> assumption)
    | (apply fromView <;> assumption)
    | (apply fromBound <;> assumption)
    | (apply fromBlock <;> assumption)
    | (apply fromExprsAs <;> assumption)
    | (apply fromStructExprs <;> assumption)
    | (apply fromPrintArgs <;> assumption)
    | (subst after; rfl)
    | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
    | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
    | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
    | (split at typed <;> try inv at typed)
termination_by sizeOf stmt

end

theorem implementation_references {module : Module} (accepted : validate module = .ok ())
    {index : Nat} {impl : Impl} (lookup : module.impls[index]? = some impl) :
    Within module impl.vars (blockReferences impl.body) := by
  obtain ⟨ty, finish, typed, _⟩ := (validate_modOk module accepted).impl index impl lookup |>.body
  exact fromBlock impl.body [] typed

theorem initializer_references {module : Module} (accepted : validate module = .ok ())
    {index : Nat} {global : Global} (lookup : module.globals[index]? = some global) :
    Within module #[] (exprReferences global.init) := by
  obtain ⟨finish, typed⟩ := (validate_modOk module accepted).glob index global lookup |>.init
  exact fromExpr global.init typed

end Goose.Lower.Validation.SourceSymbolSource
