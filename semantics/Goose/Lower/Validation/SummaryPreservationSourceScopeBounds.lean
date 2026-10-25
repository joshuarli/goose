import Goose.Core.Scopes

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core

def SourceScopesWithin (count : Nat) (scopes : List (Nat × Option Nat)) : Prop :=
  ∀ entry ∈ scopes, entry.1 < count

theorem SourceScopesWithin.nil (count : Nat) : SourceScopesWithin count [] := by
  intro entry member
  cases member

theorem SourceScopesWithin.cons {count : Nat} {entry : Nat × Option Nat}
    {rest : List (Nat × Option Nat)} :
    SourceScopesWithin count (entry :: rest) ↔ entry.1 < count ∧ SourceScopesWithin count rest := by
  simp only [SourceScopesWithin, List.mem_cons, forall_eq_or_imp]

theorem SourceScopesWithin.append {count : Nat} {left right : List (Nat × Option Nat)} :
    SourceScopesWithin count (left ++ right) ↔
      SourceScopesWithin count left ∧ SourceScopesWithin count right := by
  constructor
  · intro bounds
    exact ⟨fun entry member => bounds entry (List.mem_append_left right member),
      fun entry member => bounds entry (List.mem_append_right left member)⟩
  · rintro ⟨leftBounds, rightBounds⟩ entry member
    rcases List.mem_append.mp member with member | member
    · exact leftBounds entry member
    · exact rightBounds entry member

theorem SourceScopesWithin.member {count : Nat} {scopes : List (Nat × Option Nat)}
    (bounds : SourceScopesWithin count scopes) {scope : Nat} {parent : Option Nat}
    (member : (scope, parent) ∈ scopes) : scope < count :=
  bounds (scope, parent) member

theorem SourceScopesWithin.of_subset {count : Nat} {left right : List (Nat × Option Nat)}
    (bounds : SourceScopesWithin count right) (subset : ∀ entry ∈ left, entry ∈ right) :
    SourceScopesWithin count left :=
  fun entry member => bounds entry (subset entry member)

theorem SourceScopesWithin.iff_indices {count : Nat} {scopes : List (Nat × Option Nat)} :
    SourceScopesWithin count scopes ↔ ∀ scope ∈ scopes.map Prod.fst, scope < count := by
  constructor
  · intro bounds scope member
    obtain ⟨entry, entryMember, equal⟩ := List.mem_map.mp member
    subst scope
    exact bounds entry entryMember
  · intro bounds entry member
    exact bounds entry.1 (List.mem_map.mpr ⟨entry, member, rfl⟩)

theorem blockScopes_indices_parent (body : Core.Block) (parent other : Option Nat) :
    (blockScopes parent body).map Prod.fst = (blockScopes other body).map Prod.fst := by
  cases body
  rfl

mutual

theorem exprScopes_indices_parent (parent other : Option Nat) (expression : Expr) :
    (exprScopes parent expression).map Prod.fst = (exprScopes other expression).map Prod.fst := by
  cases expression with
  | lit | bool => rfl
  | read p | ref _ p | pop p _ => exact placeScopes_indices_parent parent other p
  | slice _ v lo hi _ =>
    simp only [exprScopes, List.map_append, viewScopes_indices_parent parent other v,
      boundScopes_indices_parent parent other lo, boundScopes_indices_parent parent other hi]
  | len v => exact viewScopes_indices_parent parent other v
  | un _ e _ | not e | conv _ _ e _ | fill _ e => exact exprScopes_indices_parent parent other e
  | bin _ a b _ | cmp _ a b | and a b | or a b =>
    simp only [exprScopes, List.map_append, exprScopes_indices_parent parent other a,
      exprScopes_indices_parent parent other b]
  | call _ args _ => exact argsScopes_indices_parent parent other args
  | push p e _ =>
    simp only [exprScopes, List.map_append, placeScopes_indices_parent parent other p,
      exprScopes_indices_parent parent other e]
  | ifE c t f =>
    simp only [exprScopes, List.map_append, exprScopes_indices_parent parent other c,
      blockScopes_indices_parent t parent other, blockScopes_indices_parent f parent other]
  | blockE body => exact blockScopes_indices_parent body parent other
  | arrLit _ es | structLit _ es => exact exprsScopes_indices_parent parent other es
termination_by sizeOf expression

theorem exprsScopes_indices_parent (parent other : Option Nat) (expressions : List Expr) :
    (exprsScopes parent expressions).map Prod.fst = (exprsScopes other expressions).map Prod.fst := by
  cases expressions with
  | nil => rfl
  | cons e rest =>
    simp only [exprsScopes, List.map_append, exprScopes_indices_parent parent other e,
      exprsScopes_indices_parent parent other rest]
termination_by sizeOf expressions

theorem argsScopes_indices_parent (parent other : Option Nat) (args : List Arg) :
    (argsScopes parent args).map Prod.fst = (argsScopes other args).map Prod.fst := by
  cases args with
  | nil => rfl
  | cons arg rest =>
    cases arg with
    | byVal e =>
      simp only [argsScopes, List.map_append, exprScopes_indices_parent parent other e,
        argsScopes_indices_parent parent other rest]
    | byRef _ p =>
      simp only [argsScopes, List.map_append, placeScopes_indices_parent parent other p,
        argsScopes_indices_parent parent other rest]
termination_by sizeOf args

theorem placeScopes_indices_parent (parent other : Option Nat) (place : Place) :
    (placeScopes parent place).map Prod.fst = (placeScopes other place).map Prod.fst := by
  cases place with
  | var | global => rfl
  | deref e => exact exprScopes_indices_parent parent other e
  | field p _ => exact placeScopes_indices_parent parent other p
  | elem v i _ =>
    simp only [placeScopes, List.map_append, viewScopes_indices_parent parent other v,
      exprScopes_indices_parent parent other i]
termination_by sizeOf place

theorem viewScopes_indices_parent (parent other : Option Nat) (view : View) :
    (viewScopes parent view).map Prod.fst = (viewScopes other view).map Prod.fst := by
  cases view with
  | of p => exact placeScopes_indices_parent parent other p
  | val e => exact exprScopes_indices_parent parent other e
termination_by sizeOf view

theorem boundScopes_indices_parent (parent other : Option Nat) (bound : Bound) :
    (boundScopes parent bound).map Prod.fst = (boundScopes other bound).map Prod.fst := by
  cases bound with
  | omitted => rfl
  | expr e | fromEnd e => exact exprScopes_indices_parent parent other e
termination_by sizeOf bound

end

theorem printScopes_indices_parent (args : List PrintArg) (parent other : Option Nat) :
    (printScopes parent args).map Prod.fst = (printScopes other args).map Prod.fst := by
  induction args with
  | nil => rfl
  | cons arg rest ih =>
    cases arg <;> simp only [printScopes, List.map_append, exprScopes_indices_parent parent other, ih]

theorem stmtScopes_indices_parent (statement : Stmt) (parent other : Option Nat) :
    (stmtScopes parent statement).map Prod.fst = (stmtScopes other statement).map Prod.fst := by
  cases statement with
  | letS _ e _ | rebind _ e _ | expr e _ | assertS e _ | exit e _ =>
    exact exprScopes_indices_parent parent other e
  | assign p e _ | assignOp _ p e _ | popN p e _ | assignWhole p e _ =>
    simp only [stmtScopes, List.map_append, placeScopes_indices_parent parent other p,
      exprScopes_indices_parent parent other e]
  | append p v _ =>
    simp only [stmtScopes, List.map_append, placeScopes_indices_parent parent other p,
      viewScopes_indices_parent parent other v]
  | resize p n fill _ =>
    cases fill with
    | none =>
      simp only [stmtScopes, List.map_append, List.map_nil,
        placeScopes_indices_parent parent other p, exprScopes_indices_parent parent other n]
    | some e =>
      simp only [stmtScopes, List.map_append, placeScopes_indices_parent parent other p,
        exprScopes_indices_parent parent other n, exprScopes_indices_parent parent other e]
  | clear p _ => exact placeScopes_indices_parent parent other p
  | ifS c t f _ =>
    cases f with
    | none =>
      simp only [stmtScopes, List.map_append, List.map_nil,
        exprScopes_indices_parent parent other c, blockScopes_indices_parent t parent other]
    | some f =>
      simp only [stmtScopes, List.map_append, exprScopes_indices_parent parent other c,
        blockScopes_indices_parent t parent other, blockScopes_indices_parent f parent other]
  | «while» c b _ =>
    simp only [stmtScopes, List.map_append, exprScopes_indices_parent parent other c,
      blockScopes_indices_parent b parent other]
  | forRange _ lo hi b _ =>
    simp only [stmtScopes, List.map_append, exprScopes_indices_parent parent other lo,
      exprScopes_indices_parent parent other hi, blockScopes_indices_parent b parent other]
  | forEach _ _ v _ b _ =>
    simp only [stmtScopes, List.map_append, viewScopes_indices_parent parent other v,
      blockScopes_indices_parent b parent other]
  | ret e _ =>
    cases e with
    | none => rfl
    | some e => exact exprScopes_indices_parent parent other e
  | brk | cont | abort => rfl
  | print args _ => exact printScopes_indices_parent args parent other

theorem stmtsScopes_indices_parent (statements : List Stmt) (parent other : Option Nat) :
    (stmtsScopes parent statements).map Prod.fst = (stmtsScopes other statements).map Prod.fst := by
  induction statements with
  | nil => rfl
  | cons statement rest ih =>
    simp only [stmtsScopes, List.map_append, stmtScopes_indices_parent _ parent other, ih]

theorem SourceScopesWithin.stmts_member {count : Nat} {parent : Option Nat}
    {statements : List Stmt} {statement : Stmt} :
    SourceScopesWithin count (stmtsScopes parent statements) → statement ∈ statements →
      SourceScopesWithin count (stmtScopes parent statement) := by
  induction statements with
  | nil => intro _ member; cases member
  | cons head rest ih =>
    intro bounds member
    have parts := SourceScopesWithin.append.mp bounds
    rcases List.mem_cons.mp member with rfl | member
    · exact parts.1
    · exact ih parts.2 member

theorem SourceScopesWithin.exprs_member {count : Nat} {parent : Option Nat}
    {expressions : List Expr} {expression : Expr} :
    SourceScopesWithin count (exprsScopes parent expressions) → expression ∈ expressions →
      SourceScopesWithin count (exprScopes parent expression) := by
  induction expressions with
  | nil => intro _ member; cases member
  | cons head rest ih =>
    intro bounds member
    have parts := SourceScopesWithin.append.mp bounds
    rcases List.mem_cons.mp member with rfl | member
    · exact parts.1
    · exact ih parts.2 member

theorem SourceScopesWithin.args_value_member {count : Nat} {parent : Option Nat}
    {args : List Arg} {expression : Expr} :
    SourceScopesWithin count (argsScopes parent args) → .byVal expression ∈ args →
      SourceScopesWithin count (exprScopes parent expression) := by
  induction args with
  | nil => intro _ member; cases member
  | cons head rest ih =>
    intro bounds member
    cases head with
    | byVal head =>
      have parts := SourceScopesWithin.append.mp bounds
      rcases List.mem_cons.mp member with equal | member
      · cases equal; exact parts.1
      · exact ih parts.2 member
    | byRef _ head =>
      have parts := SourceScopesWithin.append.mp bounds
      rcases List.mem_cons.mp member with equal | member
      · cases equal
      · exact ih parts.2 member

theorem SourceScopesWithin.args_ref_member {count : Nat} {parent : Option Nat}
    {args : List Arg} {mutability : Mutability} {place : Place} :
    SourceScopesWithin count (argsScopes parent args) → .byRef mutability place ∈ args →
      SourceScopesWithin count (placeScopes parent place) := by
  induction args with
  | nil => intro _ member; cases member
  | cons head rest ih =>
    intro bounds member
    cases head with
    | byVal head =>
      have parts := SourceScopesWithin.append.mp bounds
      rcases List.mem_cons.mp member with equal | member
      · cases equal
      · exact ih parts.2 member
    | byRef _ head =>
      have parts := SourceScopesWithin.append.mp bounds
      rcases List.mem_cons.mp member with equal | member
      · cases equal; exact parts.1
      · exact ih parts.2 member

theorem SourceScopesWithin.block_parts {count scope : Nat} {parent : Option Nat}
    {statements : List Stmt} {value : Option Expr}
    (bounds : SourceScopesWithin count (blockScopes parent (.mk scope statements value))) :
    scope < count ∧ SourceScopesWithin count (stmtsScopes (some scope) statements) ∧
      SourceScopesWithin count (match value with
        | some expression => exprScopes (some scope) expression
        | none => []) := by
  cases value with
  | none =>
    change SourceScopesWithin count ((scope, parent) :: (stmtsScopes (some scope) statements ++ [])) at bounds
    have parts := SourceScopesWithin.cons.mp bounds
    exact ⟨parts.1, SourceScopesWithin.append.mp parts.2⟩
  | some expression =>
    change SourceScopesWithin count
      ((scope, parent) :: (stmtsScopes (some scope) statements ++ exprScopes (some scope) expression)) at bounds
    have parts := SourceScopesWithin.cons.mp bounds
    exact ⟨parts.1, SourceScopesWithin.append.mp parts.2⟩

theorem SourceScopesWithin.block_parent {count : Nat} (body : Core.Block) (parent other : Option Nat) :
    SourceScopesWithin count (blockScopes parent body) ↔
      SourceScopesWithin count (blockScopes other body) := by
  simp only [SourceScopesWithin.iff_indices, blockScopes_indices_parent body parent other]

theorem SourceScopesWithin.expression_parent {count : Nat} (expression : Expr) (parent other : Option Nat) :
    SourceScopesWithin count (exprScopes parent expression) ↔
      SourceScopesWithin count (exprScopes other expression) := by
  simp only [SourceScopesWithin.iff_indices, exprScopes_indices_parent parent other expression]

theorem SourceScopesWithin.expressions_parent {count : Nat} (expressions : List Expr) (parent other : Option Nat) :
    SourceScopesWithin count (exprsScopes parent expressions) ↔
      SourceScopesWithin count (exprsScopes other expressions) := by
  simp only [SourceScopesWithin.iff_indices, exprsScopes_indices_parent parent other expressions]

theorem SourceScopesWithin.args_parent {count : Nat} (args : List Arg) (parent other : Option Nat) :
    SourceScopesWithin count (argsScopes parent args) ↔
      SourceScopesWithin count (argsScopes other args) := by
  simp only [SourceScopesWithin.iff_indices, argsScopes_indices_parent parent other args]

theorem SourceScopesWithin.place_parent {count : Nat} (place : Place) (parent other : Option Nat) :
    SourceScopesWithin count (placeScopes parent place) ↔
      SourceScopesWithin count (placeScopes other place) := by
  simp only [SourceScopesWithin.iff_indices, placeScopes_indices_parent parent other place]

theorem SourceScopesWithin.view_parent {count : Nat} (view : View) (parent other : Option Nat) :
    SourceScopesWithin count (viewScopes parent view) ↔
      SourceScopesWithin count (viewScopes other view) := by
  simp only [SourceScopesWithin.iff_indices, viewScopes_indices_parent parent other view]

theorem SourceScopesWithin.bound_parent {count : Nat} (bound : Bound) (parent other : Option Nat) :
    SourceScopesWithin count (boundScopes parent bound) ↔
      SourceScopesWithin count (boundScopes other bound) := by
  simp only [SourceScopesWithin.iff_indices, boundScopes_indices_parent parent other bound]

theorem SourceScopesWithin.print_parent {count : Nat} (args : List PrintArg) (parent other : Option Nat) :
    SourceScopesWithin count (printScopes parent args) ↔
      SourceScopesWithin count (printScopes other args) := by
  simp only [SourceScopesWithin.iff_indices, printScopes_indices_parent args parent other]

theorem SourceScopesWithin.statement_parent {count : Nat} (statement : Stmt) (parent other : Option Nat) :
    SourceScopesWithin count (stmtScopes parent statement) ↔
      SourceScopesWithin count (stmtScopes other statement) := by
  simp only [SourceScopesWithin.iff_indices, stmtScopes_indices_parent statement parent other]

theorem SourceScopesWithin.statements_parent {count : Nat} (statements : List Stmt) (parent other : Option Nat) :
    SourceScopesWithin count (stmtsScopes parent statements) ↔
      SourceScopesWithin count (stmtsScopes other statements) := by
  simp only [SourceScopesWithin.iff_indices, stmtsScopes_indices_parent statements parent other]

end Goose.Lower.Validation.SummaryPreservation
