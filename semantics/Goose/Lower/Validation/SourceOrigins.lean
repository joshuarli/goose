import Goose.Lower.Validation.PushOrigins

namespace Goose.Lower.Validation.SourceOrigins

open Goose.Core Goose.Core.Sound Goose.Lower.Validation.PushOrigins


theorem sliceRefTy_some_empty {env : TEnv} {expr : Expr} {ty : Ty}
    (lookup : sliceRefTy env expr = some ty) : expr.pushOrigins = [] := by
  cases expr with
  | read place =>
    cases place <;> simp_all [sliceRefTy, Expr.pushOrigins, Place.pushOrigins]
  | _ => simp [sliceRefTy] at lookup

set_option maxHeartbeats 1600000 in
mutual

theorem fromExpr {env : TEnv} (expr : Expr) {ty : Ty} {start finish : Nat}
    (typed : tyExpr env expr start = .ok (ty, finish))
    (profile : env.mod.profile = .shrink) : Present expr.pushOrigins := by
  cases expr with
  | read place =>
    simp only [tyExpr] at typed
    obtain ⟨info, next, placeTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
    simpa only [Expr.pushOrigins] using fromPlace place placeTyped profile
  | push owner arg origin =>
    have present := pushOrigin_present_of_typed typed profile
    cases origin with
    | none => simp at present
    | some origin =>
      simp only [Expr.pushOrigins, present_cons, present_append, Option.isSome_some, true_and]
      constructor
      all_goals
        simp only [tyExpr, profile] at typed
        try inv at typed
        repeat' first
        | contradiction
        | rfl
        | exact present_nil
        | trivial
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
  | call context args origin =>
    simp only [Expr.pushOrigins]
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
            (by simpa using (show callee.params.size = args.length from by assumption)) profile
  | _ =>
    all_goals try simp only [Expr.pushOrigins, present_append]
    all_goals repeat' apply And.intro
    all_goals
      try simp only [tyExpr] at typed
      try inv at typed
      repeat' first
      | contradiction
      | rfl
      | exact present_nil
      | trivial
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
    (profile : env.mod.profile = .shrink) : Present place.pushOrigins := by
  cases place with
  | deref expr =>
    simp only [tyPlace] at typed
    obtain ⟨source, next, sourceTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
    cases special : sliceRefTy env expr with
    | some ty =>
      have empty := sliceRefTy_some_empty special
      simpa [Place.pushOrigins, empty] using present_nil
    | none =>
      simp only [special] at sourceTyped
      obtain ⟨ty, final, expressionTyped, _⟩ := (st_bind_ok _ _ _ _).mp sourceTyped
      simpa only [Place.pushOrigins] using fromExpr expr expressionTyped profile
  | _ =>
    all_goals try simp only [Place.pushOrigins, present_append]
    all_goals repeat' apply And.intro
    all_goals
      try simp only [tyPlace] at typed
      try inv at typed
      repeat' first
      | contradiction
      | rfl
      | exact present_nil
      | trivial
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
    (profile : env.mod.profile = .shrink) : Present view.pushOrigins := by
  cases view with
  | of place =>
    simp only [tyView] at typed
    obtain ⟨placeInfo, next, placeTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
    simpa only [View.pushOrigins] using fromPlace place placeTyped profile
  | val expr =>
    simp only [tyView] at typed
    obtain ⟨ty, next, expressionTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
    simpa only [View.pushOrigins] using fromExpr expr expressionTyped profile
termination_by sizeOf view

theorem fromBound {env : TEnv} (bound : Bound) {start finish : Nat}
    (typed : tyBound env bound start = .ok ((), finish))
    (profile : env.mod.profile = .shrink) : Present bound.pushOrigins := by
  cases bound <;> simp only [Bound.pushOrigins]
  all_goals
    try simp only [tyBound] at typed
    try inv at typed
    repeat' first
    | contradiction
    | rfl
    | exact present_nil
    | trivial
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
    (profile : env.mod.profile = .shrink) : Present (exprs.flatMap Expr.pushOrigins) := by
  cases exprs with
  | nil => exact present_nil
  | cons expr rest =>
    simp only [List.flatMap_cons, present_append]
    constructor
    all_goals
      simp only [tyExprsAs] at typed
      try inv at typed
      repeat' first
      | contradiction
      | rfl
      | exact present_nil
      | trivial
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
    (profile : env.mod.profile = .shrink) : Present (exprs.flatMap Expr.pushOrigins) := by
  cases exprs with
  | nil => exact present_nil
  | cons expr rest =>
    cases types with
    | nil => simp [tyStructExprs, chk] at typed
    | cons ty types =>
      simp only [List.flatMap_cons, present_append]
      constructor
      all_goals
        simp only [tyStructExprs] at typed
        try inv at typed
        repeat' first
        | contradiction
        | rfl
        | exact present_nil
        | trivial
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
    (shape : params.length = args.length) (profile : env.mod.profile = .shrink) :
    Present (args.flatMap Arg.pushOrigins) := by
  cases args with
  | nil => exact present_nil
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
          simp only [List.flatMap_cons, Arg.pushOrigins, present_append]
          constructor
          · simp only [tyArgs, row] at typed
            try inv at typed
            repeat' first
            | contradiction
            | rfl
            | exact present_nil
            | trivial
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
            all_goals exact fromArgs rest params (by assumption) tailShape profile
        | byRef mutability place =>
          simp only [List.flatMap_cons, Arg.pushOrigins, present_append]
          constructor
          · simp only [tyArgs, row] at typed
            try inv at typed
            repeat' first
            | contradiction
            | rfl
            | exact present_nil
            | trivial
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
            all_goals exact fromArgs rest params (by assumption) tailShape profile
termination_by sizeOf args

theorem fromBlock {env : TEnv} (block : Block) (pre : List (VarId × Ty)) {ty : Ty}
    {start finish : Nat} (typed : tyBlock env pre block start = .ok (ty, finish))
    (profile : env.mod.profile = .shrink) : Present block.pushOrigins := by
  cases block with
  | mk scope stmts value =>
    obtain ⟨_, initial, initialNext, after, afterNext, declared, body, result⟩ :=
      tyBlock_ok _ _ _ _ _ _ _ _ typed
    have initialMod := (declarePre_ok _ _ _ _ _ _ declared).1.mod
    have initialProfile : initial.mod.profile = .shrink := by rw [initialMod]; exact profile
    have statements := fromStmts stmts body initialProfile
    have afterProfile : after.mod.profile = .shrink := by rw [statements.2]; exact initialProfile
    cases value with
    | none => simpa [Block.pushOrigins] using statements.1
    | some expr =>
      simp only [Block.pushOrigins, present_append]
      exact ⟨statements.1, fromExpr expr result afterProfile⟩
termination_by sizeOf block

theorem fromStmts {env after : TEnv} (stmts : List Stmt) {scope start finish : Nat}
    (typed : tyStmts env scope stmts start = .ok (after, finish))
    (profile : env.mod.profile = .shrink) :
    Present (stmts.flatMap Stmt.pushOrigins) ∧ after.mod = env.mod := by
  cases stmts with
  | nil =>
    have equality := (st_pure_ok _ _ _).mp typed
    cases equality
    exact ⟨present_nil, rfl⟩
  | cons stmt rest =>
    simp only [tyStmts] at typed
    obtain ⟨mid, next, first, restTyped⟩ := (st_bind_ok _ _ _ _).mp typed
    have firstOrigins := fromStmt stmt first profile
    have midProfile : mid.mod.profile = .shrink := by rw [firstOrigins.2]; exact profile
    have remaining := fromStmts rest restTyped midProfile
    exact ⟨present_append _ _ |>.mpr ⟨firstOrigins.1, remaining.1⟩,
      remaining.2.trans firstOrigins.2⟩
termination_by sizeOf stmts

theorem fromPrintArgs {env : TEnv} (args : List PrintArg) {start finish : Nat}
    (typed : tyPrintArgs env args start = .ok ((), finish))
    (profile : env.mod.profile = .shrink) : Present (args.flatMap PrintArg.pushOrigins) := by
  cases args with
  | nil => exact present_nil
  | cons arg rest =>
    cases arg with
    | text text =>
      simpa only [List.flatMap_cons, PrintArg.pushOrigins, List.nil_append] using
        fromPrintArgs rest typed profile
    | expr expr =>
      simp only [List.flatMap_cons, PrintArg.pushOrigins, present_append]
      constructor
      all_goals
        simp only [tyPrintArgs] at typed
        try inv at typed
        repeat' first
        | contradiction
        | rfl
        | exact present_nil
        | trivial
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
    (profile : env.mod.profile = .shrink) :
    Present stmt.pushOrigins ∧ after.mod = env.mod := by
  cases stmt
  case' resize owner size fill origin => cases fill
  case' ifS condition thenBlock otherwise origin => cases otherwise
  case' ret value origin => cases value
  all_goals try simp only [Stmt.pushOrigins, present_append, present_nil, true_and]
  all_goals repeat' apply And.intro
  all_goals
    try simp only [tyStmt] at typed
    try inv at typed
    repeat' first
    | contradiction
    | rfl
    | exact present_nil
    | trivial
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

theorem implementations_present {module : Module} (accepted : validate module = .ok ())
    (profile : module.profile = .shrink) :
    ∀ impl ∈ module.impls.toList, Present impl.body.pushOrigins := by
  intro impl member
  obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  obtain ⟨ty, finish, typed, _⟩ := (validate_modOk module accepted).impl index impl lookup |>.body
  exact fromBlock impl.body [] typed profile

theorem initializers_present {module : Module} (accepted : validate module = .ok ())
    (profile : module.profile = .shrink) :
    ∀ global ∈ module.globals.toList, Present global.init.pushOrigins := by
  intro global member
  obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  obtain ⟨finish, typed⟩ := (validate_modOk module accepted).glob index global lookup |>.init
  exact fromExpr global.init typed profile

end Goose.Lower.Validation.SourceOrigins
