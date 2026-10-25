import Goose.Lower.Validation.SourceCanonicalRootFloorsTables

set_option Elab.async false

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core

mutual

theorem exprScopes_keys_parent (node : Expr) (first second : Option Nat) :
    (exprScopes first node).map Prod.fst = (exprScopes second node).map Prod.fst := by
  cases node
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil]
  all_goals repeat' first
    | rfl
    | exact exprScopes_keys_parent _ _ _
    | exact placeScopes_keys_parent _ _ _
    | exact viewScopes_keys_parent _ _ _
    | exact boundScopes_keys_parent _ _ _
    | exact argsScopes_keys_parent _ _ _
    | exact exprsScopes_keys_parent _ _ _
    | exact blockScopes_keys_parent _ _ _
    | exact stmtsScopes_keys_parent _ _ _
    | exact printScopes_keys_parent _ _ _
    | exact stmtScopes_keys_parent _ _ _
    | split
    | congr 1
termination_by sizeOf node

theorem placeScopes_keys_parent (node : Place) (first second : Option Nat) :
    (placeScopes first node).map Prod.fst = (placeScopes second node).map Prod.fst := by
  cases node
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil]
  all_goals repeat' first
    | rfl
    | exact exprScopes_keys_parent _ _ _
    | exact placeScopes_keys_parent _ _ _
    | exact viewScopes_keys_parent _ _ _
    | exact boundScopes_keys_parent _ _ _
    | exact argsScopes_keys_parent _ _ _
    | exact exprsScopes_keys_parent _ _ _
    | exact blockScopes_keys_parent _ _ _
    | exact stmtsScopes_keys_parent _ _ _
    | exact printScopes_keys_parent _ _ _
    | exact stmtScopes_keys_parent _ _ _
    | split
    | congr 1
termination_by sizeOf node

theorem viewScopes_keys_parent (node : View) (first second : Option Nat) :
    (viewScopes first node).map Prod.fst = (viewScopes second node).map Prod.fst := by
  cases node
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil]
  all_goals repeat' first
    | rfl
    | exact exprScopes_keys_parent _ _ _
    | exact placeScopes_keys_parent _ _ _
    | exact viewScopes_keys_parent _ _ _
    | exact boundScopes_keys_parent _ _ _
    | exact argsScopes_keys_parent _ _ _
    | exact exprsScopes_keys_parent _ _ _
    | exact blockScopes_keys_parent _ _ _
    | exact stmtsScopes_keys_parent _ _ _
    | exact printScopes_keys_parent _ _ _
    | exact stmtScopes_keys_parent _ _ _
    | split
    | congr 1
termination_by sizeOf node

theorem boundScopes_keys_parent (node : Bound) (first second : Option Nat) :
    (boundScopes first node).map Prod.fst = (boundScopes second node).map Prod.fst := by
  cases node
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil]
  all_goals repeat' first
    | rfl
    | exact exprScopes_keys_parent _ _ _
    | exact placeScopes_keys_parent _ _ _
    | exact viewScopes_keys_parent _ _ _
    | exact boundScopes_keys_parent _ _ _
    | exact argsScopes_keys_parent _ _ _
    | exact exprsScopes_keys_parent _ _ _
    | exact blockScopes_keys_parent _ _ _
    | exact stmtsScopes_keys_parent _ _ _
    | exact printScopes_keys_parent _ _ _
    | exact stmtScopes_keys_parent _ _ _
    | split
    | congr 1
termination_by sizeOf node

theorem argsScopes_keys_parent (node : List Arg) (first second : Option Nat) :
    (argsScopes first node).map Prod.fst = (argsScopes second node).map Prod.fst := by
  cases node
  all_goals try (rename_i head rest; cases head)
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil]
  all_goals repeat' first
    | rfl
    | exact exprScopes_keys_parent _ _ _
    | exact placeScopes_keys_parent _ _ _
    | exact viewScopes_keys_parent _ _ _
    | exact boundScopes_keys_parent _ _ _
    | exact argsScopes_keys_parent _ _ _
    | exact exprsScopes_keys_parent _ _ _
    | exact blockScopes_keys_parent _ _ _
    | exact stmtsScopes_keys_parent _ _ _
    | exact printScopes_keys_parent _ _ _
    | exact stmtScopes_keys_parent _ _ _
    | split
    | congr 1
termination_by sizeOf node

theorem exprsScopes_keys_parent (node : List Expr) (first second : Option Nat) :
    (exprsScopes first node).map Prod.fst = (exprsScopes second node).map Prod.fst := by
  cases node
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil]
  all_goals repeat' first
    | rfl
    | exact exprScopes_keys_parent _ _ _
    | exact placeScopes_keys_parent _ _ _
    | exact viewScopes_keys_parent _ _ _
    | exact boundScopes_keys_parent _ _ _
    | exact argsScopes_keys_parent _ _ _
    | exact exprsScopes_keys_parent _ _ _
    | exact blockScopes_keys_parent _ _ _
    | exact stmtsScopes_keys_parent _ _ _
    | exact printScopes_keys_parent _ _ _
    | exact stmtScopes_keys_parent _ _ _
    | split
    | congr 1
termination_by sizeOf node

theorem blockScopes_keys_parent (node : Block) (first second : Option Nat) :
    (blockScopes first node).map Prod.fst = (blockScopes second node).map Prod.fst := by
  cases node
  all_goals try (rename_i scope statements value; cases value)
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil]
  all_goals repeat' first
    | rfl
    | exact exprScopes_keys_parent _ _ _
    | exact placeScopes_keys_parent _ _ _
    | exact viewScopes_keys_parent _ _ _
    | exact boundScopes_keys_parent _ _ _
    | exact argsScopes_keys_parent _ _ _
    | exact exprsScopes_keys_parent _ _ _
    | exact blockScopes_keys_parent _ _ _
    | exact stmtsScopes_keys_parent _ _ _
    | exact printScopes_keys_parent _ _ _
    | exact stmtScopes_keys_parent _ _ _
    | split
    | congr 1
termination_by sizeOf node

theorem stmtsScopes_keys_parent (node : List Stmt) (first second : Option Nat) :
    (stmtsScopes first node).map Prod.fst = (stmtsScopes second node).map Prod.fst := by
  cases node
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil]
  all_goals repeat' first
    | rfl
    | exact exprScopes_keys_parent _ _ _
    | exact placeScopes_keys_parent _ _ _
    | exact viewScopes_keys_parent _ _ _
    | exact boundScopes_keys_parent _ _ _
    | exact argsScopes_keys_parent _ _ _
    | exact exprsScopes_keys_parent _ _ _
    | exact blockScopes_keys_parent _ _ _
    | exact stmtsScopes_keys_parent _ _ _
    | exact printScopes_keys_parent _ _ _
    | exact stmtScopes_keys_parent _ _ _
    | split
    | congr 1
termination_by sizeOf node

theorem printScopes_keys_parent (node : List PrintArg) (first second : Option Nat) :
    (printScopes first node).map Prod.fst = (printScopes second node).map Prod.fst := by
  cases node
  all_goals try (rename_i head rest; cases head)
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil]
  all_goals repeat' first
    | rfl
    | exact exprScopes_keys_parent _ _ _
    | exact placeScopes_keys_parent _ _ _
    | exact viewScopes_keys_parent _ _ _
    | exact boundScopes_keys_parent _ _ _
    | exact argsScopes_keys_parent _ _ _
    | exact exprsScopes_keys_parent _ _ _
    | exact blockScopes_keys_parent _ _ _
    | exact stmtsScopes_keys_parent _ _ _
    | exact printScopes_keys_parent _ _ _
    | exact stmtScopes_keys_parent _ _ _
    | split
    | congr 1
termination_by sizeOf node

theorem stmtScopes_keys_parent (node : Stmt) (first second : Option Nat) :
    (stmtScopes first node).map Prod.fst = (stmtScopes second node).map Prod.fst := by
  cases node
  case ret value origin =>
    cases value with
    | none => rfl
    | some expression => exact exprScopes_keys_parent expression first second
  case resize owner count fill origin =>
    cases fill
    all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil]
    all_goals repeat' first
      | rfl
      | exact exprScopes_keys_parent _ _ _
      | exact placeScopes_keys_parent _ _ _
      | exact viewScopes_keys_parent _ _ _
      | exact boundScopes_keys_parent _ _ _
      | exact argsScopes_keys_parent _ _ _
      | exact exprsScopes_keys_parent _ _ _
      | exact blockScopes_keys_parent _ _ _
      | exact stmtsScopes_keys_parent _ _ _
      | exact printScopes_keys_parent _ _ _
      | exact stmtScopes_keys_parent _ _ _
      | split
      | congr 1
  case ifS condition yes no origin =>
    cases no
    all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil]
    all_goals repeat' first
      | rfl
      | exact exprScopes_keys_parent _ _ _
      | exact placeScopes_keys_parent _ _ _
      | exact viewScopes_keys_parent _ _ _
      | exact boundScopes_keys_parent _ _ _
      | exact argsScopes_keys_parent _ _ _
      | exact exprsScopes_keys_parent _ _ _
      | exact blockScopes_keys_parent _ _ _
      | exact stmtsScopes_keys_parent _ _ _
      | exact printScopes_keys_parent _ _ _
      | exact stmtScopes_keys_parent _ _ _
      | split
      | congr 1
  all_goals simp only [exprScopes, placeScopes, viewScopes, boundScopes, argsScopes, exprsScopes, blockScopes, stmtsScopes, printScopes, stmtScopes, List.map_append, List.map_cons, List.map_nil]
  all_goals repeat' first
    | rfl
    | exact exprScopes_keys_parent _ _ _
    | exact placeScopes_keys_parent _ _ _
    | exact viewScopes_keys_parent _ _ _
    | exact boundScopes_keys_parent _ _ _
    | exact argsScopes_keys_parent _ _ _
    | exact exprsScopes_keys_parent _ _ _
    | exact blockScopes_keys_parent _ _ _
    | exact stmtsScopes_keys_parent _ _ _
    | exact printScopes_keys_parent _ _ _
    | exact stmtScopes_keys_parent _ _ _
    | split
    | congr 1
termination_by sizeOf node

end

theorem exprScopes_keys_none (node : Expr) (parent : Option Nat) :
    (exprScopes parent node).map Prod.fst = (exprScopes none node).map Prod.fst :=
  exprScopes_keys_parent node parent none

theorem placeScopes_keys_none (node : Place) (parent : Option Nat) :
    (placeScopes parent node).map Prod.fst = (placeScopes none node).map Prod.fst :=
  placeScopes_keys_parent node parent none

theorem viewScopes_keys_none (node : View) (parent : Option Nat) :
    (viewScopes parent node).map Prod.fst = (viewScopes none node).map Prod.fst :=
  viewScopes_keys_parent node parent none

theorem boundScopes_keys_none (node : Bound) (parent : Option Nat) :
    (boundScopes parent node).map Prod.fst = (boundScopes none node).map Prod.fst :=
  boundScopes_keys_parent node parent none

theorem argsScopes_keys_none (node : List Arg) (parent : Option Nat) :
    (argsScopes parent node).map Prod.fst = (argsScopes none node).map Prod.fst :=
  argsScopes_keys_parent node parent none

theorem exprsScopes_keys_none (node : List Expr) (parent : Option Nat) :
    (exprsScopes parent node).map Prod.fst = (exprsScopes none node).map Prod.fst :=
  exprsScopes_keys_parent node parent none

theorem blockScopes_keys_none (node : Block) (parent : Option Nat) :
    (blockScopes parent node).map Prod.fst = (blockScopes none node).map Prod.fst :=
  blockScopes_keys_parent node parent none

theorem stmtsScopes_keys_none (node : List Stmt) (parent : Option Nat) :
    (stmtsScopes parent node).map Prod.fst = (stmtsScopes none node).map Prod.fst :=
  stmtsScopes_keys_parent node parent none

theorem printScopes_keys_none (node : List PrintArg) (parent : Option Nat) :
    (printScopes parent node).map Prod.fst = (printScopes none node).map Prod.fst :=
  printScopes_keys_parent node parent none

theorem stmtScopes_keys_none (node : Stmt) (parent : Option Nat) :
    (stmtScopes parent node).map Prod.fst = (stmtScopes none node).map Prod.fst :=
  stmtScopes_keys_parent node parent none

end Goose.Lower.Validation.SourceCanonicalRootFloors
