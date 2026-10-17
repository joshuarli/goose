import Goose.Lower.Validation.SourceSymbolSourceFacts

namespace Goose.Lower.Validation.SourceSymbolSource

open Goose.Core Goose.GIR

def Reference.LoweredWithin (le : LEnv) : Reference → Prop
  | .slot index => index < le.slots.size
  | .global index => index < le.globals.size
  | .context index => index < le.sigs.size
  | .origin index => index < le.mod.origins.size

def LoweredWithin (le : LEnv) (references : List Reference) : Prop :=
  ∀ reference ∈ references, reference.LoweredWithin le

@[simp] theorem loweredWithin_nil : LoweredWithin le [] := by simp [LoweredWithin]
@[simp] theorem loweredWithin_append : LoweredWithin le (first ++ second) ↔
    LoweredWithin le first ∧ LoweredWithin le second := by
  simp [LoweredWithin, List.mem_append, or_imp, forall_and]
@[simp] theorem loweredWithin_cons : LoweredWithin le (first :: rest) ↔
    first.LoweredWithin le ∧ LoweredWithin le rest := by
  simp [LoweredWithin, List.mem_cons, forall_eq_or_imp]

theorem Within.lowered {module : Core.Module} {vars : Array LocalVar} {le : LEnv}
    (checked : Within module vars references)
    (slots : vars.size = le.slots.size)
    (globals : module.globals.size = le.globals.size)
    (contexts : module.contexts.size = le.sigs.size)
    (origins : module.origins.size = le.mod.origins.size) :
    LoweredWithin le references := by
  intro reference member
  have bound := checked reference member
  cases reference <;> simpa only [Reference.Within, Reference.LoweredWithin,
    slots, globals, contexts, origins] using bound

def ScopeBounds (scopeCount : Nat) (pairs : List (Nat × Option Nat)) : Prop :=
  ∀ scope parent, (scope, parent) ∈ pairs → scope < scopeCount

@[simp] theorem scopeBounds_nil : ScopeBounds scopeCount [] := by simp [ScopeBounds]
@[simp] theorem scopeBounds_append : ScopeBounds scopeCount (first ++ second) ↔
    ScopeBounds scopeCount first ∧ ScopeBounds scopeCount second := by
  simp [ScopeBounds, List.mem_append, or_imp, forall_and]
@[simp] theorem scopeBounds_cons : ScopeBounds scopeCount ((scope, parent) :: rest) ↔
    scope < scopeCount ∧ ScopeBounds scopeCount rest := by
  constructor
  · intro checked
    exact ⟨checked scope parent (by simp), fun next outer member => checked next outer (by simp [member])⟩
  · rintro ⟨head, tail⟩ next outer member
    rcases List.mem_cons.mp member with equal | member
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact head
    · exact tail next outer member

theorem ScopeTableContains.bounds {parents : Array (Option Nat)}
    (checked : ScopeTableContains parents pairs) : ScopeBounds parents.size pairs := by
  intro scope parent member
  exact (Array.getElem?_eq_some_iff.mp (checked scope parent member)).1


set_option maxHeartbeats 1600000 in
mutual

theorem lowerExpr_references (le : LEnv) (count : Nat) (parent : Option Nat)
    (expr : Core.Expr) (refs : LoweredWithin le (exprReferences expr))
    (scopes : ScopeBounds count (exprScopes parent expr)) :
    LS.SourceSymbolsRun le count (Goose.Lower.lowerExpr expr) := by
  cases expr with
  | lit type value =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_lit type value
  | bool value =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_bool value
  | read place =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_read (lowerPlace_references le count parent place refs scopes)
  | ref mu place =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_ref (lowerPlace_references le count parent place refs scopes)
  | len view =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_len (lowerView_references le count parent view refs scopes)
  | un op expr origin =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_un (lowerExpr_references le count parent expr refs.2 scopes) refs.1
  | conv kind target expr origin =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_conv (lowerExpr_references le count parent expr refs.2 scopes) refs.1
  | bin op left right origin =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_bin (lowerExpr_references le count parent left refs.2.1 scopes.1) (lowerExpr_references le count parent right refs.2.2 scopes.2) refs.1
  | cmp op left right =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_cmp (lowerExpr_references le count parent left refs.1 scopes.1) (lowerExpr_references le count parent right refs.2 scopes.2)
  | «and» left right =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_and (lowerExpr_references le count parent left refs.1 scopes.1) (lowerExpr_references le count parent right refs.2 scopes.2)
  | «or» left right =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_or (lowerExpr_references le count parent left refs.1 scopes.1) (lowerExpr_references le count parent right refs.2 scopes.2)
  | «not» expr =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_not (lowerExpr_references le count parent expr refs scopes)
  | pop place origin =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_pop (lowerPlace_references le count parent place refs.2 scopes) refs.1
  | fill type expr =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_fill (lowerExpr_references le count parent expr refs scopes)
  | arrLit type exprs =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_arrLit (lowerExprs_references le count parent exprs refs scopes)
  | structLit type exprs =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_structLit (lowerExprs_references le count parent exprs refs scopes)
  | slice mu view lo hi origin =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_slice
      (lowerView_references le count parent view refs.2.1.1 scopes.1.1)
      (lowerBound_references le count parent lo refs.2.1.2 scopes.1.2)
      (lowerBound_references le count parent hi refs.2.2 scopes.2) refs.1
  | call context args origin =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    exact LS.SourceSymbolsRun.lowerExpr_call
      (lowerArgs_references le count parent args refs.2.2 scopes) refs.1
      (by simpa only [Op.SymbolRefsValid] using refs.2.1)
  | push place expr origin =>
    cases origin with
    | none =>
      simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
        Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
        Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
        and_true, true_and] at refs scopes
      exact LS.SourceSymbolsRun.lowerExpr_push
        (lowerPlace_references le count parent place refs.1 scopes.1)
        (lowerExpr_references le count parent expr refs.2 scopes.2)
        (by intro origin equal; cases equal)
    | some origin =>
      simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
        Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
        Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
        and_true, true_and] at refs scopes
      exact LS.SourceSymbolsRun.lowerExpr_push
        (lowerPlace_references le count parent place refs.1.2 scopes.1)
        (lowerExpr_references le count parent expr refs.2 scopes.2)
        (by intro emitted equal; cases equal; exact refs.1.1)
  | blockE body =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    simpa only [Goose.Lower.lowerExpr] using
      lowerBlock_references le count parent none [] true body refs scopes (by simp)
  | ifE condition yes no =>
    simp only [exprReferences, loweredWithin_cons, loweredWithin_append, loweredWithin_nil,
      Reference.LoweredWithin, exprScopes, scopeBounds_append, scopeBounds_nil,
      Option.toList, List.map_nil, List.map_cons, List.nil_append, List.singleton_append,
      and_true, true_and] at refs scopes
    simp only [Goose.Lower.lowerExpr]
    exact (lowerExpr_references le count parent condition refs.1.1 scopes.1.1).bind fun value =>
      LS.SourceSymbolsRun.ifValue value
        (lowerBlock_references le count parent none [] true yes refs.1.2 scopes.1.2 (by simp))
        (lowerBlock_references le count parent none [] true no refs.2 scopes.2 (by simp))
termination_by sizeOf expr

theorem lowerExprs_references (le : LEnv) (count : Nat) (parent : Option Nat) :
    ∀ exprs : List Core.Expr, LoweredWithin le (exprs.flatMap exprReferences) →
      ScopeBounds count (exprsScopes parent exprs) →
      LS.SourceSymbolsRun le count (Goose.Lower.lowerExprs exprs)
  | [], _, _ => LS.SourceSymbolsRun.pure []
  | expr :: rest, refs, scopes => by
    simp only [List.flatMap_cons, loweredWithin_append] at refs
    simp only [exprsScopes, scopeBounds_append] at scopes
    simp only [Goose.Lower.lowerExprs]
    exact (lowerExpr_references le count parent expr refs.1 scopes.1).bind fun _ =>
      (lowerExprs_references le count parent rest refs.2 scopes.2).bind fun _ =>
        LS.SourceSymbolsRun.pure _

termination_by exprs _ _ => sizeOf exprs

theorem lowerArgs_references (le : LEnv) (count : Nat) (parent : Option Nat) :
    ∀ args : List Core.Arg, LoweredWithin le (args.flatMap argReferences) →
      ScopeBounds count (argsScopes parent args) →
      LS.SourceSymbolsRun le count (Goose.Lower.lowerArgs args)
  | [], _, _ => LS.SourceSymbolsRun.pure []
  | .byVal expr :: rest, refs, scopes => by
    simp only [List.flatMap_cons, argReferences, loweredWithin_append] at refs
    simp only [argsScopes, scopeBounds_append] at scopes
    simp only [Goose.Lower.lowerArgs, Goose.Lower.lowerArg]
    exact (lowerExpr_references le count parent expr refs.1 scopes.1).bind fun _ =>
      (lowerArgs_references le count parent rest refs.2 scopes.2).bind fun _ =>
        LS.SourceSymbolsRun.pure _
  | .byRef mu place :: rest, refs, scopes => by
    simp only [List.flatMap_cons, argReferences, loweredWithin_append] at refs
    simp only [argsScopes, scopeBounds_append] at scopes
    simp only [Goose.Lower.lowerArgs]
    exact (LS.SourceSymbolsRun.lowerArg_byRef
      (lowerPlace_references le count parent place refs.1 scopes.1)).bind fun _ =>
      (lowerArgs_references le count parent rest refs.2 scopes.2).bind fun _ =>
        LS.SourceSymbolsRun.pure _

termination_by args _ _ => sizeOf args

theorem lowerPlace_references (le : LEnv) (count : Nat) (parent : Option Nat) :
    ∀ place : Core.Place, LoweredWithin le (placeReferences place) →
      ScopeBounds count (placeScopes parent place) →
      LS.SourceSymbolsRun le count (Goose.Lower.lowerPlace place)
  | .var slot, refs, _ => by
    apply LS.SourceSymbolsRun.emitDef
    · simp [Op.origin]
    · simpa [Op.SymbolRefsValid, placeReferences, Reference.LoweredWithin] using refs
  | .global global, refs, _ => by
    apply LS.SourceSymbolsRun.emitDef
    · simp [Op.origin]
    · simpa [Op.SymbolRefsValid, placeReferences, Reference.LoweredWithin] using refs
  | .deref expr, refs, scopes => by
    simp only [placeReferences, placeScopes] at refs scopes
    simpa only [Goose.Lower.lowerPlace] using lowerExpr_references le count parent expr refs scopes
  | .field place index, refs, scopes => by
    simp only [placeReferences, placeScopes] at refs scopes
    exact LS.SourceSymbolsRun.lowerPlace_field (lowerPlace_references le count parent place refs scopes)
  | .elem view index origin, refs, scopes => by
    simp only [placeReferences, loweredWithin_cons, loweredWithin_append, Reference.LoweredWithin] at refs
    simp only [placeScopes, scopeBounds_append] at scopes
    exact LS.SourceSymbolsRun.lowerPlace_elem
      (lowerView_references le count parent view refs.2.1 scopes.1)
      (lowerExpr_references le count parent index refs.2.2 scopes.2) refs.1

termination_by place _ _ => sizeOf place

theorem lowerView_references (le : LEnv) (count : Nat) (parent : Option Nat) :
    ∀ view : Core.View, LoweredWithin le (viewReferences view) →
      ScopeBounds count (viewScopes parent view) →
      LS.SourceSymbolsRun le count (Goose.Lower.lowerView view)
  | .of place, refs, scopes => by
    simp only [viewReferences, viewScopes] at refs scopes
    exact LS.SourceSymbolsRun.lowerView_of (lowerPlace_references le count parent place refs scopes)
  | .val expr, refs, scopes => by
    simp only [viewReferences, viewScopes] at refs scopes
    exact LS.SourceSymbolsRun.lowerView_val (lowerExpr_references le count parent expr refs scopes)

termination_by view _ _ => sizeOf view

theorem lowerEachSource_references (le : LEnv) (count : Nat) (parent : Option Nat) :
    ∀ view : Core.View, LoweredWithin le (viewReferences view) →
      ScopeBounds count (viewScopes parent view) →
      LS.SourceSymbolsRun le count (Goose.Lower.lowerEachSource view)
  | .of place, refs, scopes => by
    simp only [viewReferences, viewScopes] at refs scopes
    simp only [Goose.Lower.lowerEachSource]
    apply LS.SourceSymbolsRun.bind (lowerPlace_references le count parent place refs scopes)
    intro address
    apply LS.SourceSymbolsRun.bind
      (LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]))
    intro _
    exact LS.SourceSymbolsRun.pure _
  | .val expr, refs, scopes => by
    simp only [viewReferences, viewScopes] at refs scopes
    simp only [Goose.Lower.lowerEachSource]
    apply LS.SourceSymbolsRun.bind (lowerExpr_references le count parent expr refs scopes)
    intro value
    apply LS.SourceSymbolsRun.bind
      (LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]))
    intro _
    exact LS.SourceSymbolsRun.pure _

termination_by view _ _ => sizeOf view

theorem lowerBound_references (le : LEnv) (count : Nat) (parent : Option Nat) :
    ∀ bound : Core.Bound, LoweredWithin le (boundReferences bound) →
      ScopeBounds count (boundScopes parent bound) →
      LS.SourceSymbolsRun le count (Goose.Lower.lowerBound bound)
  | .omitted, _, _ => LS.SourceSymbolsRun.pure Bnd.omitted
  | .expr expr, refs, scopes => by
    simp only [boundReferences, boundScopes] at refs scopes
    exact LS.SourceSymbolsRun.lowerBound_expr (lowerExpr_references le count parent expr refs scopes)
  | .fromEnd expr, refs, scopes => by
    simp only [boundReferences, boundScopes] at refs scopes
    exact LS.SourceSymbolsRun.lowerBound_fromEnd (lowerExpr_references le count parent expr refs scopes)

termination_by bound _ _ => sizeOf bound

theorem lowerBlock_references (le : LEnv) (count : Nat) (parent : Option Nat)
    (loop : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ body : Core.Block, LoweredWithin le (blockReferences body) →
      ScopeBounds count (blockScopes parent body) →
      (∀ entry ∈ pre, entry.1 < le.slots.size ∧ entry.2.2 < le.mod.origins.size) →
      LS.SourceSymbolsRun le count (Goose.Lower.lowerBlock loop pre want body)
  | .mk scope stmts none, refs, scopes, preBounds => by
    simp only [blockReferences, loweredWithin_append] at refs
    simp only [blockScopes, scopeBounds_cons, scopeBounds_append] at scopes
    apply LS.SourceSymbolsRun.lowerBlock scope pre want stmts _ loop scopes.1 preBounds
    · exact lowerStmts_references le count (some scope) loop stmts refs.1 scopes.2.1
    · apply LS.SourceSymbolsRun.lowerBlockValue
      intro value equal
      cases equal
  | .mk scope stmts (some expr), refs, scopes, preBounds => by
    simp only [blockReferences, loweredWithin_append] at refs
    simp only [blockScopes, scopeBounds_cons, scopeBounds_append] at scopes
    apply LS.SourceSymbolsRun.lowerBlock scope pre want stmts _ loop scopes.1 preBounds
    · exact lowerStmts_references le count (some scope) loop stmts refs.1 scopes.2.1
    · apply LS.SourceSymbolsRun.lowerBlockValue
      intro value equal
      cases equal
      exact lowerExpr_references le count (some scope) expr refs.2 scopes.2.2

termination_by body _ _ _ => sizeOf body

theorem lowerStmts_references (le : LEnv) (count : Nat) (parent : Option Nat)
    (loop : Option LoopCtx) : ∀ stmts : List Core.Stmt,
      LoweredWithin le (stmts.flatMap stmtReferences) → ScopeBounds count (stmtsScopes parent stmts) →
      LS.SourceSymbolsRun le count (Goose.Lower.lowerStmts loop stmts)
  | [], _, _ => LS.SourceSymbolsRun.pure ()
  | stmt :: rest, refs, scopes => by
    simp only [List.flatMap_cons, loweredWithin_append] at refs
    simp only [stmtsScopes, scopeBounds_append] at scopes
    simp only [Goose.Lower.lowerStmts]
    apply LS.SourceSymbolsRun.bind LS.SourceSymbolsRun.isLive
    intro live
    cases live with
    | false => exact LS.SourceSymbolsRun.pure ()
    | true =>
      exact (lowerStmt_references le count parent loop stmt refs.1 scopes.1).bind fun _ =>
        lowerStmts_references le count parent loop rest refs.2 scopes.2

termination_by stmts _ _ => sizeOf stmts

theorem lowerPrint_references (le : LEnv) (count : Nat) (parent : Option Nat) :
    ∀ args : List Core.PrintArg, LoweredWithin le (args.flatMap printReferences) →
      ScopeBounds count (printScopes parent args) →
      LS.SourceSymbolsRun le count (Goose.Lower.lowerPrintArgs args)
  | [], _, _ => LS.SourceSymbolsRun.pure []
  | .text text :: rest, refs, scopes => by
    simp only [List.flatMap_cons, printReferences, List.nil_append] at refs
    simp only [printScopes] at scopes
    simp only [Goose.Lower.lowerPrintArgs]
    exact (lowerPrint_references le count parent rest refs scopes).bind fun _ => LS.SourceSymbolsRun.pure _
  | .expr expr :: rest, refs, scopes => by
    simp only [List.flatMap_cons, printReferences, loweredWithin_append] at refs
    simp only [printScopes, scopeBounds_append] at scopes
    simp only [Goose.Lower.lowerPrintArgs]
    exact (lowerExpr_references le count parent expr refs.1 scopes.1).bind fun _ =>
      (lowerPrint_references le count parent rest refs.2 scopes.2).bind fun _ => LS.SourceSymbolsRun.pure _

termination_by args _ _ => sizeOf args

theorem lowerStmt_references (le : LEnv) (count : Nat) (parent : Option Nat)
    (loop : Option LoopCtx) (stmt : Core.Stmt) (refs : LoweredWithin le (stmtReferences stmt))
    (scopes : ScopeBounds count (stmtScopes parent stmt)) :
    LS.SourceSymbolsRun le count (Goose.Lower.lowerStmt loop stmt) := by
  cases stmt with
  | «while» condition body origin =>
    try simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      Reference.LoweredWithin] at refs
    simp only [stmtScopes, scopeBounds_append] at scopes
    simp only [Goose.Lower.lowerStmt]
    apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.newBlock [])
    intro allocated
    apply LS.SourceSymbolsRun.bind
      (LS.SourceSymbolsRun.emitTerm (.br allocated.1 []) (by simp [Term.origin]))
    intro _
    apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.setCur (some allocated.1))
    intro _
    let header := allocated.1
    let params := allocated.2
    apply LS.SourceSymbolsRun.lowerWhile header
    · exact lowerExpr_references le count parent condition refs.2.1 scopes.1
    · intro depth exit
      exact lowerBlock_references le count parent _ [] false body refs.2.2 scopes.2 (by simp)
  | forRange slot lo hi body origin =>
    try simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      Reference.LoweredWithin] at refs
    simp only [stmtScopes, scopeBounds_append] at scopes
    simp only [Goose.Lower.lowerStmt]
    apply LS.SourceSymbolsRun.bind (lowerExpr_references le count parent lo refs.2.2.1.1 scopes.1.1)
    intro loValue
    apply LS.SourceSymbolsRun.bind (lowerExpr_references le count parent hi refs.2.2.1.2 scopes.1.2)
    intro hiValue
    apply LS.SourceSymbolsRun.whenLive ()
    intro _
    apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.intTyOf loValue)
    intro type
    apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.newBlock [.data (.int type)])
    intro allocated
    apply LS.SourceSymbolsRun.bind
      (LS.SourceSymbolsRun.emitTerm (.br allocated.1 [loValue]) (by simp [Term.origin]))
    intro _
    apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.setCur (some allocated.1))
    intro _
    let header := allocated.1
    let params := allocated.2
    apply LS.SourceSymbolsRun.lowerRange
    intro depth exit
    apply lowerBlock_references le count parent _ _ false body refs.2.2.2 scopes.2
    intro entry member
    simp only [List.mem_singleton] at member
    subst entry
    exact ⟨refs.2.1, refs.1⟩
  | forEach slot index view byRef body origin =>
    try simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      Reference.LoweredWithin] at refs
    simp only [stmtScopes, scopeBounds_append] at scopes
    simp only [Goose.Lower.lowerStmt]
    apply LS.SourceSymbolsRun.bind
    · exact lowerEachSource_references le count parent view refs.2.2.1.2 scopes.1
    · intro ownerView
      apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.regrowOf ownerView.1)
      intro regrow
      apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.eachSampled regrow ownerView.2)
      intro sampled
      apply LS.SourceSymbolsRun.bind
        (LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]))
      intro start
      apply LS.SourceSymbolsRun.whenLive ()
      intro _
      apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.newBlock [.data (.int .i64)])
      intro allocated
      apply LS.SourceSymbolsRun.bind
        (LS.SourceSymbolsRun.emitTerm (.br allocated.1 [start]) (by simp [Term.origin]))
      intro _
      apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.setCur (some allocated.1))
      intro _
      let header := allocated.1
      let params := allocated.2
      apply LS.SourceSymbolsRun.lowerEach
      intro depth exit
      apply LS.SourceSymbolsRun.bind
        (LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]))
      intro element
      apply LS.SourceSymbolsRun.bind (LS.SourceSymbolsRun.eachElemValue slot byRef element)
      intro elementValue
      apply lowerBlock_references le count parent _ _ false body refs.2.2.2 scopes.2
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨refs.2.1, refs.1⟩
      · cases index with
        | none => simp at member
        | some index =>
          simp only [List.mem_singleton] at member
          subst entry
          constructor
          · simpa [Option.toList, Reference.LoweredWithin] using refs.2.2.1.1
          · exact refs.1
  | ifS condition yes no origin =>
    cases no with
    | none =>
      simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
        Reference.LoweredWithin] at refs
      simp only [stmtScopes, scopeBounds_append] at scopes
      simp only [Goose.Lower.lowerStmt]
      apply LS.SourceSymbolsRun.bind (lowerExpr_references le count parent condition refs.2.1.1 scopes.1.1)
      intro value
      apply LS.SourceSymbolsRun.lowerStmt_ifS_none
      exact lowerBlock_references le count parent loop [] false yes refs.2.1.2 scopes.1.2 (by simp)
    | some no =>
      simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
        Reference.LoweredWithin] at refs
      simp only [stmtScopes, scopeBounds_append] at scopes
      simp only [Goose.Lower.lowerStmt]
      apply LS.SourceSymbolsRun.bind (lowerExpr_references le count parent condition refs.2.1.1 scopes.1.1)
      intro value
      apply LS.SourceSymbolsRun.lowerStmt_ifS_some
      · exact lowerBlock_references le count parent loop [] false yes refs.2.1.2 scopes.1.2 (by simp)
      · exact lowerBlock_references le count parent loop [] false no refs.2.2 scopes.2 (by simp)
  | ret expr origin =>
    cases expr with
    | none =>
      apply LS.SourceSymbolsRun.lowerStmt_ret_none
      simpa [stmtReferences, stmtSourceOrigin, Reference.LoweredWithin] using refs
    | some expr =>
      simp only [stmtScopes] at scopes
      simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, Reference.LoweredWithin] at refs
      exact LS.SourceSymbolsRun.lowerStmt_ret_some expr origin
        (lowerExpr_references le count parent expr refs.2 scopes) refs.1
  | print args origin =>
    simp only [stmtScopes] at scopes
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, Reference.LoweredWithin] at refs
    exact LS.SourceSymbolsRun.lowerStmt_print args origin
      (lowerPrint_references le count parent args refs.2 scopes) refs.1
  | resize place size fill origin =>
    cases fill with
    | none =>
      simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
        Reference.LoweredWithin] at refs
      simp only [stmtScopes, scopeBounds_append] at scopes
      apply LS.SourceSymbolsRun.lowerStmt_resize
      · exact lowerPlace_references le count parent place refs.2.1.1 scopes.1.1
      · exact lowerExpr_references le count parent size refs.2.1.2 scopes.1.2
      · intro expr equal
        cases equal
      · exact refs.1
    | some fill =>
      simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
        Reference.LoweredWithin] at refs
      simp only [stmtScopes, scopeBounds_append] at scopes
      apply LS.SourceSymbolsRun.lowerStmt_resize
      · exact lowerPlace_references le count parent place refs.2.1.1 scopes.1.1
      · exact lowerExpr_references le count parent size refs.2.1.2 scopes.1.2
      · intro expr equal
        cases equal
        exact lowerExpr_references le count parent fill refs.2.2 scopes.2
      · exact refs.1
  | letS slot expr origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_let (lowerExpr_references le count parent expr refs.2.2 scopes) refs.2.1 refs.1
  | rebind slot expr origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_rebind (lowerExpr_references le count parent expr refs.2.2 scopes) refs.2.1 refs.1
  | expr expr origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_expr (lowerExpr_references le count parent expr refs.2 scopes)
  | assign place expr origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_assign (lowerPlace_references le count parent place refs.2.1 scopes.1) (lowerExpr_references le count parent expr refs.2.2 scopes.2) refs.1
  | assignOp op place expr origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_assignOp (lowerPlace_references le count parent place refs.2.1 scopes.1) (lowerExpr_references le count parent expr refs.2.2 scopes.2) refs.1
  | popN place expr origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_popN (lowerPlace_references le count parent place refs.2.1 scopes.1) (lowerExpr_references le count parent expr refs.2.2 scopes.2) refs.1
  | assignWhole place expr origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_assignWhole (lowerPlace_references le count parent place refs.2.1 scopes.1) (lowerExpr_references le count parent expr refs.2.2 scopes.2) refs.1
  | append place view origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_append (lowerPlace_references le count parent place refs.2.1 scopes.1) (lowerView_references le count parent view refs.2.2 scopes.2) refs.1
  | clear place origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_clear (lowerPlace_references le count parent place refs.2 scopes) refs.1
  | assertS expr origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_assert expr origin (lowerExpr_references le count parent expr refs.2 scopes) refs.1
  | exit expr origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_exit expr origin (lowerExpr_references le count parent expr refs.2 scopes) refs.1
  | abort message origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_abort message origin refs
  | brk origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_brk origin loop refs
  | cont origin =>
    simp only [stmtReferences, stmtSourceOrigin, loweredWithin_cons, loweredWithin_append,
      loweredWithin_nil, Reference.LoweredWithin, and_true, stmtScopes, scopeBounds_append,
      scopeBounds_nil] at refs scopes
    exact LS.SourceSymbolsRun.lowerStmt_cont origin loop refs
termination_by sizeOf stmt

end

end Goose.Lower.Validation.SourceSymbolSource
