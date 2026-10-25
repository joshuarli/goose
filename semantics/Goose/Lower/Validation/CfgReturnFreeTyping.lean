import Goose.Lower.Validation.CfgReturnFreeSyntax
import Goose.Core.Sound.Invert

set_option Elab.async false

namespace Goose.Lower.Validation
open Goose.Core Goose.Core.Sound

private theorem tyStmt_inExpr {env after : TEnv} (stmt : Stmt) {scope start finish : Nat}
    (typed : tyStmt env scope stmt start = .ok (after, finish)) :
    after.inExpr = env.inExpr := by
  cases stmt
  case' resize owner size fill origin => cases fill
  case' ifS condition yes no origin => cases no
  case' ret value origin => cases value
  all_goals simp only [tyStmt] at typed
  all_goals try inv at typed
  all_goals
    repeat' first
      | contradiction
      | rfl
      | (subst after; rfl)
      | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
      | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
      | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
      | (split at typed <;> try inv at typed)

private theorem sliceRefTy_returnFree {env : TEnv} {expr : Expr} {ty : Ty}
    (lookup : sliceRefTy env expr = some ty) : ReturnFreeExpr expr := by
  cases expr with
  | read place =>
      cases place <;> simp_all [sliceRefTy, ReturnFreeExpr, ReturnFreePlace]
  | _ => simp [sliceRefTy] at lookup

set_option maxHeartbeats 1600000 in
mutual

theorem tyExpr_returnFree {env : TEnv} (expr : Expr) {ty : Ty} {start finish : Nat}
    (typed : tyExpr env expr start = .ok (ty, finish)) : ReturnFreeExpr expr := by
  cases expr with
  | push owner arg origin =>
      cases profile : env.mod.profile <;> cases origin
      all_goals simp only [ReturnFreeExpr]
      all_goals constructor
      all_goals
        simp only [tyExpr, profile] at typed
        try inv at typed
        repeat' first
          | contradiction
          | (apply tyExpr_returnFree <;> assumption)
          | (apply tyPlace_returnFree <;> assumption)
          | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
          | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
          | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
          | (split at typed <;> try inv at typed)
  | call context args origin =>
      simp only [ReturnFreeExpr]
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
                exact tyArgs_returnFree args callee.params.toList (by assumption)
                  (by simpa using (show callee.params.size = args.length from by assumption))
  | _ =>
      all_goals try simp only [ReturnFreeExpr]
      all_goals repeat' apply And.intro
      all_goals
        try simp only [tyExpr] at typed
        try inv at typed
        repeat' first
          | contradiction
          | rfl
          | trivial
          | (apply tyExpr_returnFree <;> assumption)
          | (apply tyPlace_returnFree <;> assumption)
          | (apply tyView_returnFree <;> assumption)
          | (apply tyBound_returnFree <;> assumption)
          | (apply tyBlock_returnFree <;> first | assumption | rfl)
          | (apply tyExprsAs_returnFree <;> assumption)
          | (apply tyStructExprs_returnFree <;> assumption)
          | (apply tyPrintArgs_returnFree <;> assumption)
          | (solve | simp_all only [])
          | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
          | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
          | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
          | (split at typed <;> try inv at typed)
termination_by sizeOf expr

theorem tyPlace_returnFree {env : TEnv} (place : Place) {info : PlaceInfo} {start finish : Nat}
    (typed : tyPlace env place start = .ok (info, finish)) : ReturnFreePlace place := by
  cases place with
  | deref expr =>
      simp only [tyPlace] at typed
      obtain ⟨source, next, sourceTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
      cases special : sliceRefTy env expr with
      | some ty => exact sliceRefTy_returnFree special
      | none =>
          simp only [special] at sourceTyped
          obtain ⟨ty, final, expressionTyped, _⟩ := (st_bind_ok _ _ _ _).mp sourceTyped
          exact tyExpr_returnFree expr expressionTyped
  | _ =>
      all_goals try simp only [ReturnFreePlace]
      all_goals repeat' apply And.intro
      all_goals
        try simp only [tyPlace] at typed
        try inv at typed
        repeat' first
          | contradiction
          | rfl
          | trivial
          | (apply tyExpr_returnFree <;> assumption)
          | (apply tyPlace_returnFree <;> assumption)
          | (apply tyView_returnFree <;> assumption)
          | (apply tyBound_returnFree <;> assumption)
          | (apply tyBlock_returnFree <;> first | assumption | rfl)
          | (apply tyExprsAs_returnFree <;> assumption)
          | (apply tyStructExprs_returnFree <;> assumption)
          | (apply tyPrintArgs_returnFree <;> assumption)
          | (solve | simp_all only [])
          | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
          | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
          | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
          | (split at typed <;> try inv at typed)
termination_by sizeOf place

theorem tyView_returnFree {env : TEnv} (view : View) {info : Ty × Bool} {start finish : Nat}
    (typed : tyView env view start = .ok (info, finish)) : ReturnFreeView view := by
  cases view with
  | of place =>
      simp only [tyView] at typed
      obtain ⟨placeInfo, next, placeTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
      exact tyPlace_returnFree place placeTyped
  | val expr =>
      simp only [tyView] at typed
      obtain ⟨ty, next, expressionTyped, _⟩ := (st_bind_ok _ _ _ _).mp typed
      exact tyExpr_returnFree expr expressionTyped
termination_by sizeOf view

theorem tyBound_returnFree {env : TEnv} (bound : Bound) {start finish : Nat}
    (typed : tyBound env bound start = .ok ((), finish)) : ReturnFreeBound bound := by
  cases bound <;> simp only [ReturnFreeBound]
  all_goals
    try simp only [tyBound] at typed
    try inv at typed
    repeat' first
      | contradiction
      | rfl
      | trivial
      | (apply tyExpr_returnFree <;> assumption)
      | (apply tyPlace_returnFree <;> assumption)
      | (apply tyView_returnFree <;> assumption)
      | (apply tyBound_returnFree <;> assumption)
      | (apply tyBlock_returnFree <;> first | assumption | rfl)
      | (apply tyExprsAs_returnFree <;> assumption)
      | (apply tyStructExprs_returnFree <;> assumption)
      | (apply tyPrintArgs_returnFree <;> assumption)
      | (solve | simp_all only [])
      | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
      | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
      | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
      | (split at typed <;> try inv at typed)
termination_by sizeOf bound

theorem tyExprsAs_returnFree {env : TEnv} (exprs : List Expr) {element : Ty} {start finish : Nat}
    (typed : tyExprsAs env element exprs start = .ok ((), finish)) : ReturnFreeExprs exprs := by
  cases exprs with
  | nil => trivial
  | cons expr rest =>
      constructor
      all_goals
        simp only [tyExprsAs] at typed
        try inv at typed
        repeat' first
          | contradiction
          | rfl
          | trivial
          | (apply tyExpr_returnFree <;> assumption)
          | (apply tyPlace_returnFree <;> assumption)
          | (apply tyView_returnFree <;> assumption)
          | (apply tyBound_returnFree <;> assumption)
          | (apply tyBlock_returnFree <;> first | assumption | rfl)
          | (apply tyExprsAs_returnFree <;> assumption)
          | (apply tyStructExprs_returnFree <;> assumption)
          | (apply tyPrintArgs_returnFree <;> assumption)
          | (solve | simp_all only [])
          | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
          | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
          | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
          | (split at typed <;> try inv at typed)
termination_by sizeOf exprs

theorem tyStructExprs_returnFree {env : TEnv} (exprs : List Expr) (types : List Ty) {start finish : Nat}
    (typed : tyStructExprs env types exprs start = .ok ((), finish)) : ReturnFreeExprs exprs := by
  cases exprs with
  | nil => trivial
  | cons expr rest =>
      cases types with
      | nil => simp [tyStructExprs, chk] at typed
      | cons ty types =>
          constructor
          all_goals
            simp only [tyStructExprs] at typed
            try inv at typed
            repeat' first
              | contradiction
              | rfl
              | trivial
              | (apply tyExpr_returnFree <;> assumption)
              | (apply tyPlace_returnFree <;> assumption)
              | (apply tyView_returnFree <;> assumption)
              | (apply tyBound_returnFree <;> assumption)
              | (apply tyBlock_returnFree <;> first | assumption | rfl)
              | (apply tyExprsAs_returnFree <;> assumption)
              | (apply tyStructExprs_returnFree <;> assumption)
              | (apply tyPrintArgs_returnFree <;> assumption)
              | (solve | simp_all only [])
              | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
              | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
              | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
              | (split at typed <;> try inv at typed)
termination_by sizeOf exprs

theorem tyArgs_returnFree {env : TEnv} (args : List Arg) (params : List Param) {callee : Impl}
    {start finish : Nat} (typed : tyArgs env callee params args start = .ok ((), finish))
    (shape : params.length = args.length) : ReturnFreeArgs args := by
  cases args with
  | nil => trivial
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
              cases arg
              all_goals constructor
              all_goals
                simp only [tyArgs, row] at typed
                try inv at typed
                repeat' first
                  | contradiction
                  | (apply tyExpr_returnFree <;> assumption)
                  | (apply tyPlace_returnFree <;> assumption)
                  | (solve | exact tyArgs_returnFree rest params (by assumption) tailShape)
                  | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
                  | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
                  | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
                  | (split at typed <;> try inv at typed)
termination_by sizeOf args

theorem tyBlock_returnFree {env : TEnv} (block : Block) (pre : List (VarId × Ty)) {ty : Ty}
    {start finish : Nat} (typed : tyBlock env pre block start = .ok (ty, finish))
    (inside : env.inExpr = true) : ReturnFreeBlock block := by
  cases block with
  | mk scope stmts value =>
      obtain ⟨_, initial, initialNext, after, afterNext, declared, body, result⟩ :=
        tyBlock_ok _ _ _ _ _ _ _ _ typed
      have initialInside : initial.inExpr = true := (declarePre_ok _ _ _ _ _ _ declared).1.inExpr.trans inside
      have statements := tyStmts_returnFree stmts body initialInside
      cases value with
      | none => exact ⟨statements, trivial⟩
      | some expr => exact ⟨statements, tyExpr_returnFree expr result⟩
termination_by sizeOf block

theorem tyStmts_returnFree {env after : TEnv} (stmts : List Stmt) {scope start finish : Nat}
    (typed : tyStmts env scope stmts start = .ok (after, finish))
    (inside : env.inExpr = true) : ReturnFreeStmts stmts := by
  cases stmts with
  | nil => trivial
  | cons stmt rest =>
      simp only [tyStmts] at typed
      obtain ⟨middle, next, first, tail⟩ := (st_bind_ok _ _ _ _).mp typed
      exact ⟨tyStmt_returnFree_of_plain_or_inExpr stmt first (Or.inl inside),
        tyStmts_returnFree rest tail ((tyStmt_inExpr stmt first).trans inside)⟩
termination_by sizeOf stmts

theorem tyPrintArgs_returnFree {env : TEnv} (args : List PrintArg) {start finish : Nat}
    (typed : tyPrintArgs env args start = .ok ((), finish)) : ReturnFreePrintArgs args := by
  cases args with
  | nil => trivial
  | cons arg rest =>
      cases arg with
      | text text => exact tyPrintArgs_returnFree rest typed
      | expr expr =>
          constructor
          all_goals
            simp only [tyPrintArgs] at typed
            try inv at typed
            repeat' first
              | contradiction
              | rfl
              | trivial
              | (apply tyExpr_returnFree <;> assumption)
              | (apply tyPlace_returnFree <;> assumption)
              | (apply tyView_returnFree <;> assumption)
              | (apply tyBound_returnFree <;> assumption)
              | (apply tyBlock_returnFree <;> first | assumption | rfl)
              | (apply tyExprsAs_returnFree <;> assumption)
              | (apply tyStructExprs_returnFree <;> assumption)
              | (apply tyPrintArgs_returnFree <;> assumption)
              | (solve | simp_all only [])
              | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
              | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
              | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
              | (split at typed <;> try inv at typed)
termination_by sizeOf args

theorem tyStmt_returnFree_of_plain_or_inExpr {env after : TEnv} (stmt : Stmt)
    {scope start finish : Nat} (typed : tyStmt env scope stmt start = .ok (after, finish))
    (allowed : env.inExpr = true ∨ stmt.isPlain = true) : ReturnFreeStmt stmt := by
  cases stmt
  case' resize owner size fill origin => cases fill
  case' ifS condition yes no origin => cases no
  case ret value origin =>
    have inside : env.inExpr = true := by simpa only [Stmt.isPlain, Bool.false_eq_true, or_false] using allowed
    cases value with
    | none =>
        simp only [tyStmt] at typed
        obtain ⟨_, next, _, remainder⟩ := (st_bind_ok _ _ _ _).mp typed
        obtain ⟨_, last, returned, _⟩ := (st_bind_ok _ _ _ _).mp remainder
        have outside := (retUnit_ok _ _ _ returned).2.1
        simp [inside] at outside
    | some expr =>
        simp only [tyStmt] at typed
        obtain ⟨_, next, _, remainder⟩ := (st_bind_ok _ _ _ _).mp typed
        obtain ⟨_, last, returned, _⟩ := (st_bind_ok _ _ _ _).mp remainder
        have outside := (retTy_ok _ _ _ returned).2.1
        simp [inside] at outside
  all_goals try simp only [Stmt.isPlain, Bool.false_eq_true, or_false, or_true] at allowed
  all_goals try simp only [ReturnFreeStmt, ReturnFreeValue]
  all_goals repeat' apply And.intro
  all_goals
    try simp only [tyStmt] at typed
    try inv at typed
    repeat' first
      | contradiction
      | rfl
      | trivial
      | (apply tyExpr_returnFree <;> assumption)
      | (apply tyPlace_returnFree <;> assumption)
      | (apply tyView_returnFree <;> assumption)
      | (apply tyBlock_returnFree <;> first | assumption | rfl)
      | (apply tyPrintArgs_returnFree <;> assumption)
      | (solve | simp_all only [])
      | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
      | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
      | (guard_hyp typed : _ ∨ _; rcases typed with typed | typed)
      | (split at typed <;> try inv at typed)
termination_by sizeOf stmt

end

theorem tyStmt_returnFree {env after : TEnv} (stmt : Stmt) {scope start finish : Nat}
    (typed : tyStmt env scope stmt start = .ok (after, finish))
    (inside : env.inExpr = true) : ReturnFreeStmt stmt :=
  tyStmt_returnFree_of_plain_or_inExpr stmt typed (Or.inl inside)

mutual

theorem tyBlock_returnFreeStopping {env : TEnv} (noReturn : ContextId → Bool)
    (block : Block) (pre : List (VarId × Ty)) {ty : Ty} {start finish : Nat}
    (typed : tyBlock env pre block start = .ok (ty, finish))
    (stopping : block.stops noReturn = true) : ReturnFreeStoppingBlock noReturn block := by
  cases block with
  | mk scope stmts value =>
      obtain ⟨_, initial, initialNext, after, afterNext, declared, body, result⟩ :=
        tyBlock_ok _ _ _ _ _ _ _ _ typed
      have statements := tyStmts_returnFreeStopping noReturn stmts body stopping
      cases value with
      | none => exact ⟨statements, trivial⟩
      | some expr => exact ⟨statements, tyExpr_returnFree expr result⟩
termination_by sizeOf block

theorem tyStmts_returnFreeStopping {env after : TEnv} (noReturn : ContextId → Bool)
    (stmts : List Stmt) {scope start finish : Nat}
    (typed : tyStmts env scope stmts start = .ok (after, finish))
    (stopping : stmtsStop noReturn stmts = true) : ReturnFreeStoppingStmts noReturn stmts := by
  cases stmts with
  | nil => simp [stmtsStop] at stopping
  | cons stmt rest =>
      simp only [tyStmts] at typed
      obtain ⟨middle, next, first, tail⟩ := (st_bind_ok _ _ _ _).mp typed
      by_cases front : stmt.stops noReturn = true
      · simp only [ReturnFreeStoppingStmts, front, ↓reduceIte]
        exact tyStmt_returnFreeStopping noReturn stmt first front
      · have conditions : stmt.isPlain = true ∧ stmtsStop noReturn rest = true := by
          simpa only [stmtsStop, Bool.or_eq_true, front, Bool.false_eq_true, false_or, Bool.and_eq_true] using stopping
        simp only [ReturnFreeStoppingStmts, front, ↓reduceIte]
        exact ⟨tyStmt_returnFree_of_plain_or_inExpr stmt first (Or.inr conditions.1),
          tyStmts_returnFreeStopping noReturn rest tail conditions.2⟩
termination_by sizeOf stmts

theorem tyStmt_returnFreeStopping {env after : TEnv} (noReturn : ContextId → Bool)
    (stmt : Stmt) {scope start finish : Nat}
    (typed : tyStmt env scope stmt start = .ok (after, finish))
    (stopping : stmt.stops noReturn = true) : ReturnFreeStoppingStmt noReturn stmt := by
  cases stmt with
  | abort code origin => trivial
  | exit expr origin =>
      simp only [ReturnFreeStoppingStmt]
      simp only [tyStmt] at typed
      try inv at typed
      repeat' first
        | (apply tyExpr_returnFree <;> assumption)
        | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
        | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
  | expr expr origin =>
      cases expr <;> try simp [Stmt.stops] at stopping
      rename_i context args callOrigin
      simp only [tyStmt] at typed
      obtain ⟨_, next, _, remainder⟩ := (st_bind_ok _ _ _ _).mp typed
      obtain ⟨ty, last, expressionTyped, _⟩ := (st_bind_ok _ _ _ _).mp remainder
      exact tyExpr_returnFree (.call context args callOrigin) expressionTyped
  | ifS condition yes no origin =>
      cases no with
      | none => simp [Stmt.stops] at stopping
      | some no =>
          have branches : yes.stops noReturn = true ∧ no.stops noReturn = true := by
            simpa only [Stmt.stops, Bool.and_eq_true] using stopping
          simp only [ReturnFreeStoppingStmt]
          repeat' apply And.intro
          all_goals
            simp only [tyStmt] at typed
            try inv at typed
            repeat' first
              | (apply tyExpr_returnFree <;> assumption)
              | (apply tyBlock_returnFreeStopping <;> first | assumption | exact branches.1 | exact branches.2)
              | (guard_hyp typed : _ ∧ _; obtain ⟨fact, typed⟩ := typed)
              | (guard_hyp typed : ∃ _, _; obtain ⟨value, typed⟩ := typed)
              | (split at typed <;> try inv at typed)
  | _ => simp [Stmt.stops] at stopping
termination_by sizeOf stmt

end

end Goose.Lower.Validation
