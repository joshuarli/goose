import Lean.Meta.Tactic.Cases
import Goose.Lower.Validation.SourceCanonicalRootFloorsProjection
import Goose.Lower.Validation.SourceRootBounds
import Goose.Lower.Validation.SourceCanonicalRootFloorsMetadata

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

local syntax "source_split_ands" : tactic
elab_rules : tactic
  | `(tactic| source_split_ands) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      return [← goal.casesAnd]

open Goose.Core Goose.Core.Sound SourceSymbolSource

def SourceAnnotationBounds (env : PEnv) : Prop :=
  (∀ varId roots, (varId, roots) ∈ env.ctx.varRoots → SourceRootsWithin env.mod env.impl roots) ∧
  (∀ varId roots, (varId, roots) ∈ env.ctx.contentRoots → SourceRootsWithin env.mod env.impl roots)

def SourceTableBounds (module : Core.Module) (impl : Impl) (table : SourceRootTable) : Prop :=
  ∀ (scope : Nat) roots, table[scope]?.join = some roots → SourceRootsWithin module impl roots

private theorem bounded_empty (module : Core.Module) (impl : Impl) :
    SourceRootsWithin module impl [] := by intro root member; cases member

theorem SourceTableBounds.getD {module : Core.Module} {impl : Impl} {table : SourceRootTable}
    (valid : SourceTableBounds module impl table) (scope : Nat) :
    SourceRootsWithin module impl (table[scope]?.join.getD []) := by
  cases found : table[scope]?.join with
  | none => exact bounded_empty _ _
  | some roots => exact valid scope roots found

private theorem bounded_union {module : Core.Module} {impl : Impl} {left right : List RootRef}
    (first : SourceRootsWithin module impl left) (second : SourceRootsWithin module impl right) :
    SourceRootsWithin module impl (unionRoots left right) := by
  intro root member
  exact (unionRoots_mem left right root member).elim (first root) (second root)

theorem sourceReadRoots_bounded (env : PEnv) (place : Place) (bounds : SourceAnnotationBounds env) :
    SourceRootsWithin env.mod env.impl (sourceReadRoots env place) := by
  have annotation : ∀ varId, SourceRootsWithin env.mod env.impl ((env.ann varId).getD []) := by
    intro varId
    unfold PEnv.ann
    cases found : env.ctx.varRoots.find? (·.1 == varId) with
    | none => exact bounded_empty _ _
    | some row => exact bounds.1 row.1 row.2 (List.mem_of_find?_eq_some found)
  have contents : ∀ varId, SourceRootsWithin env.mod env.impl ((env.cont varId).getD []) := by
    intro varId
    unfold PEnv.cont
    cases found : env.ctx.contentRoots.find? (·.1 == varId) with
    | none => exact bounded_empty _ _
    | some row => exact bounds.2 row.1 row.2 (List.mem_of_find?_eq_some found)
  cases place with
  | var varId => simp only [sourceReadRoots]; split <;> first | exact annotation varId | exact bounded_empty _ _
  | deref expression =>
      cases expression <;> try exact bounded_empty _ _
      case read owner =>
        cases owner <;> try exact bounded_empty _ _
        case var varId => simp only [sourceReadRoots]; split <;> first | exact contents varId | exact bounded_empty _ _
  | _ => exact bounded_empty _ _

private theorem sourceMappedRoots_bounded (module : Core.Module) (impl : Impl)
    (arguments : List (List RootRef)) (declared : List RootRef)
    (inputs : ∀ roots ∈ arguments, SourceRootsWithin module impl roots)
    (globals : ∀ root ∈ declared, ∀ index, root = .global index → index < module.globals.size) :
    SourceRootsWithin module impl (sourceMappedRoots arguments declared) := by
  unfold sourceMappedRoots
  suffices ∀ initial, SourceRootsWithin module impl initial →
      SourceRootsWithin module impl (declared.foldl (fun roots root =>
        unionRoots roots (match root with
          | .param parameter => arguments[parameter]?.getD []
          | .global global => [.global global]
          | .local _ => [])) initial) from this [] (bounded_empty _ _)
  induction declared with
  | nil => intro initial bounds; exact bounds
  | cons head rest ih =>
      intro initial bounds
      apply ih (fun root member => globals root (by simp [member]))
      apply bounded_union bounds
      cases head with
      | param index =>
          change SourceRootsWithin module impl (arguments[index]?.getD [])
          cases found : arguments[index]? with
          | none => exact bounded_empty _ _
          | some roots => exact inputs roots (List.mem_of_getElem? found)
      | global index =>
          intro root member
          have same := List.mem_singleton.mp member
          subst root
          exact globals (.global index) (by simp) index rfl
      | «local» index => exact bounded_empty _ _

theorem sourceCallRoots_bounded (env : PEnv) (context : ContextId)
    (arguments : List (List RootRef)) (accepted : Core.validate env.mod = .ok ())
    (inputs : ∀ roots ∈ arguments, SourceRootsWithin env.mod env.impl roots) :
    SourceRootsWithin env.mod env.impl (sourceCallRoots env context arguments) := by
  unfold sourceCallRoots
  cases contextAt : env.mod.contexts[context]? with
  | none => exact bounded_empty _ _
  | some called =>
      dsimp only
      cases implAt : env.mod.impls[called.impl]? with
      | none => exact bounded_empty _ _
      | some impl =>
          dsimp only
          have resultsBounds := (accepted_context_root_bounds accepted contextAt implAt).2.2
          cases results : impl.results.toList with
          | nil => simp only [results]; exact bounded_empty _ _
          | cons type rest =>
              cases rest with
              | cons other rest => simp only [results]; exact bounded_empty _ _
              | nil =>
                  cases declared : called.resultRoots with
                  | nil => simp only [results, declared]; exact bounded_empty _ _
                  | cons roots rest =>
                      cases rest with
                      | cons other rest => simp only [results, declared]; exact bounded_empty _ _
                      | nil =>
                          simp only [results, declared]
                          split
                          · apply sourceMappedRoots_bounded env.mod env.impl arguments roots inputs
                            intro root member index same
                            have bounded := resultsBounds roots (by simp [declared]) root member
                            simpa only [same, SourceRootIndexWithin] using bounded
                          · exact bounded_empty _ _

abbrev SourceCollectorBounds (env : PEnv) (action : SourceRootsM α) (result : α → Prop) : Prop :=
  ∀ table, SourceTableBounds env.mod env.impl table →
    result (action table).1 ∧ SourceTableBounds env.mod env.impl (action table).2

local syntax "source_intro_callback" : tactic
elab_rules : tactic
  | `(tactic| source_intro_callback) => do
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      let .forallE _ _ (.forallE _ _ body _) _ := target
        | Lean.throwError "expected source collector continuation"
      unless body.getAppFn.isConstOf ``SourceCollectorBounds do
        Lean.throwError "expected source collector continuation"
      Lean.Elab.Tactic.evalTactic (← `(tactic| intro value valueBound))

local syntax "source_action " ident : tactic
elab_rules : tactic
  | `(tactic| source_action $expected:ident) => Lean.Elab.Tactic.withMainContext do
      let target ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
      unless target.getAppFn.isConstOf ``SourceCollectorBounds do
        Lean.throwError "expected source collector bounds"
      let arguments := target.getAppArgs
      let mut action := arguments[arguments.size - 2]!
      repeat
        action := action.headBeta
        if let .letE _ _ value body _ := action then
          action := body.instantiate1 value
        else if let .reduced reduced ← Lean.Meta.reduceMatcher? action then
          action := reduced
        else
          break
      let .const actual _ := action.getAppFn
        | Lean.throwError "expected source collector action"
      unless actual.getString! == expected.getId.getString! do
        Lean.throwError "different source collector action"

private theorem collector_bounds_pure (env : PEnv) (value : α) (result : α → Prop)
    (bounded : result value) : SourceCollectorBounds env (pure value) result := by
  intro table valid
  exact ⟨bounded, valid⟩

private theorem collector_bounds_bind (env : PEnv) (action : SourceRootsM α)
    (next : α → SourceRootsM β) (middle : α → Prop) (result : β → Prop)
    (first : SourceCollectorBounds env action middle)
    (rest : ∀ value, middle value → SourceCollectorBounds env (next value) result) :
    SourceCollectorBounds env (action >>= next) result := by
  intro table valid
  exact rest (action table).1 (first table valid).1 (action table).2 (first table valid).2

private theorem collector_bounds_discard (env : PEnv) (action : SourceRootsM α)
    (next : SourceRootsM β) (middle : α → Prop) (result : β → Prop)
    (first : SourceCollectorBounds env action middle)
    (rest : SourceCollectorBounds env next result) :
    SourceCollectorBounds env (do let _ ← action; next) result :=
  collector_bounds_bind env action (fun _ => next) middle result first (fun _ _ => rest)

private theorem collector_bounds_write (env : PEnv) (scope : Nat) (roots : List RootRef)
    (bounded : SourceRootsWithin env.mod env.impl roots) :
    SourceCollectorBounds env
      (modify fun table => if scope < table.size then table.set! scope (some roots) else table)
      (fun _ : Unit => True) := by
  intro table valid
  refine ⟨True.intro, ?_⟩
  change SourceTableBounds env.mod env.impl
    (if scope < table.size then table.set! scope (some roots) else table)
  split
  · intro index found present
    by_cases same : index = scope
    · subst index
      simp_all
    · have unchanged : (table.set! scope (some roots))[index]? = table[index]? := by
        simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne, same, Ne.symm same]
      rw [unchanged] at present
      exact valid index found present
  · exact valid

private theorem bounded_local (module : Core.Module) (impl : Impl) (index : Nat)
    (bounded : index < impl.vars.size) : SourceRootsWithin module impl [.local index] := by
  intro root member
  cases List.mem_singleton.mp member
  exact bounded

private theorem bounded_global (module : Core.Module) (impl : Impl) (index : Nat)
    (bounded : index < module.globals.size) : SourceRootsWithin module impl [.global index] := by
  intro root member
  cases List.mem_singleton.mp member
  exact bounded

private theorem bounded_rows_cons {module : Core.Module} {impl : Impl}
    {head : List RootRef} {tail : List (List RootRef)}
    (first : SourceRootsWithin module impl head)
    (rest : ∀ roots ∈ tail, SourceRootsWithin module impl roots) :
    ∀ roots ∈ head :: tail, SourceRootsWithin module impl roots := by
  intro roots member
  rcases List.mem_cons.mp member with rfl | member
  · exact first
  · exact rest roots member

mutual

theorem collectSourceExprRoots_bounded (env : PEnv) (expression : Expr)
    (accepted : Core.validate env.mod = .ok ()) (annotations : SourceAnnotationBounds env)
    (references : Within env.mod env.impl.vars (exprReferences expression)) :
    SourceCollectorBounds env (collectSourceExprRoots env expression) (SourceRootsWithin env.mod env.impl) := by
  cases expression
  all_goals simp only [exprReferences, placeReferences, viewReferences, boundReferences, argReferences, blockReferences, stmtReferences, printReferences, List.flatMap_cons, List.flatMap_nil, within_append, within_cons, within_nil] at references
  all_goals source_split_ands
  all_goals try rw [collectSourceExprRoots.eq_def]
  all_goals repeat' first
    | assumption
    | exact True.intro
    | exact bounded_empty _ _
    | (solve | intro roots member; cases member)
    | (apply bounded_rows_cons <;> assumption)
    | (apply bounded_union <;> assumption)
    | (solve | exact sourceReadRoots_bounded env _ annotations)
    | (solve | apply sourceCallRoots_bounded env _ _ accepted <;> assumption)
    | (apply bounded_local <;> assumption)
    | (apply bounded_global <;> assumption)
    | (solve | source_action collectSourceExprRoots; apply collectSourceExprRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePlaceRoots; apply collectSourcePlaceRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceViewRoots; apply collectSourceViewRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBoundRoots; apply collectSourceBoundRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceArgumentRoots; apply collectSourceArgumentRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceExprListRoots; apply collectSourceExprListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBlockRoots; apply collectSourceBlockRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtListRoots; apply collectSourceStmtListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePrintRoots; apply collectSourcePrintRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtRoots; apply collectSourceStmtRoots_bounded _ _ accepted annotations <;> assumption)
    | (source_action pure; apply collector_bounds_pure)
    | (source_action bind; apply collector_bounds_bind)
    | (source_action modify; apply collector_bounds_write; apply bounded_union <;> assumption)
    | source_intro_callback
termination_by sizeOf expression

theorem collectSourcePlaceRoots_bounded (env : PEnv) (place : Place)
    (accepted : Core.validate env.mod = .ok ()) (annotations : SourceAnnotationBounds env)
    (references : Within env.mod env.impl.vars (placeReferences place)) :
    SourceCollectorBounds env (collectSourcePlaceRoots env place) (SourceRootsWithin env.mod env.impl) := by
  cases place
  all_goals simp only [exprReferences, placeReferences, viewReferences, boundReferences, argReferences, blockReferences, stmtReferences, printReferences, List.flatMap_cons, List.flatMap_nil, within_append, within_cons, within_nil] at references
  all_goals source_split_ands
  all_goals try rw [collectSourcePlaceRoots.eq_def]
  all_goals repeat' first
    | assumption
    | exact True.intro
    | exact bounded_empty _ _
    | (solve | intro roots member; cases member)
    | (apply bounded_rows_cons <;> assumption)
    | (apply bounded_union <;> assumption)
    | (solve | exact sourceReadRoots_bounded env _ annotations)
    | (solve | apply sourceCallRoots_bounded env _ _ accepted <;> assumption)
    | (apply bounded_local <;> assumption)
    | (apply bounded_global <;> assumption)
    | (solve | source_action collectSourceExprRoots; apply collectSourceExprRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePlaceRoots; apply collectSourcePlaceRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceViewRoots; apply collectSourceViewRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBoundRoots; apply collectSourceBoundRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceArgumentRoots; apply collectSourceArgumentRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceExprListRoots; apply collectSourceExprListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBlockRoots; apply collectSourceBlockRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtListRoots; apply collectSourceStmtListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePrintRoots; apply collectSourcePrintRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtRoots; apply collectSourceStmtRoots_bounded _ _ accepted annotations <;> assumption)
    | (source_action pure; apply collector_bounds_pure)
    | (source_action bind; apply collector_bounds_bind)
    | (source_action modify; apply collector_bounds_write; apply bounded_union <;> assumption)
    | source_intro_callback
termination_by sizeOf place

theorem collectSourceViewRoots_bounded (env : PEnv) (view : View)
    (accepted : Core.validate env.mod = .ok ()) (annotations : SourceAnnotationBounds env)
    (references : Within env.mod env.impl.vars (viewReferences view)) :
    SourceCollectorBounds env (collectSourceViewRoots env view) (SourceRootsWithin env.mod env.impl) := by
  cases view
  all_goals simp only [exprReferences, placeReferences, viewReferences, boundReferences, argReferences, blockReferences, stmtReferences, printReferences, List.flatMap_cons, List.flatMap_nil, within_append, within_cons, within_nil] at references
  all_goals source_split_ands
  all_goals try rw [collectSourceViewRoots.eq_def]
  all_goals repeat' first
    | assumption
    | exact True.intro
    | exact bounded_empty _ _
    | (solve | intro roots member; cases member)
    | (apply bounded_rows_cons <;> assumption)
    | (apply bounded_union <;> assumption)
    | (solve | exact sourceReadRoots_bounded env _ annotations)
    | (solve | apply sourceCallRoots_bounded env _ _ accepted <;> assumption)
    | (apply bounded_local <;> assumption)
    | (apply bounded_global <;> assumption)
    | (solve | source_action collectSourceExprRoots; apply collectSourceExprRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePlaceRoots; apply collectSourcePlaceRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceViewRoots; apply collectSourceViewRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBoundRoots; apply collectSourceBoundRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceArgumentRoots; apply collectSourceArgumentRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceExprListRoots; apply collectSourceExprListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBlockRoots; apply collectSourceBlockRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtListRoots; apply collectSourceStmtListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePrintRoots; apply collectSourcePrintRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtRoots; apply collectSourceStmtRoots_bounded _ _ accepted annotations <;> assumption)
    | (source_action pure; apply collector_bounds_pure)
    | (source_action bind; apply collector_bounds_bind)
    | (source_action modify; apply collector_bounds_write; apply bounded_union <;> assumption)
    | source_intro_callback
termination_by sizeOf view

theorem collectSourceBoundRoots_bounded (env : PEnv) (bound : Bound)
    (accepted : Core.validate env.mod = .ok ()) (annotations : SourceAnnotationBounds env)
    (references : Within env.mod env.impl.vars (boundReferences bound)) :
    SourceCollectorBounds env (collectSourceBoundRoots env bound) (fun _ => True) := by
  cases bound
  all_goals simp only [exprReferences, placeReferences, viewReferences, boundReferences, argReferences, blockReferences, stmtReferences, printReferences, List.flatMap_cons, List.flatMap_nil, within_append, within_cons, within_nil] at references
  all_goals source_split_ands
  all_goals try rw [collectSourceBoundRoots.eq_def]
  all_goals repeat' first
    | exact True.intro
    | (source_action pure; apply collector_bounds_pure)
    | (solve | source_action collectSourceExprRoots; apply collectSourceExprRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePlaceRoots; apply collectSourcePlaceRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceViewRoots; apply collectSourceViewRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBoundRoots; apply collectSourceBoundRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceArgumentRoots; apply collectSourceArgumentRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceExprListRoots; apply collectSourceExprListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBlockRoots; apply collectSourceBlockRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtListRoots; apply collectSourceStmtListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePrintRoots; apply collectSourcePrintRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtRoots; apply collectSourceStmtRoots_bounded _ _ accepted annotations <;> assumption)
    | (source_action bind; apply collector_bounds_discard)
termination_by sizeOf bound

theorem collectSourceArgumentRoots_bounded (env : PEnv) (arguments : List Arg)
    (accepted : Core.validate env.mod = .ok ()) (annotations : SourceAnnotationBounds env)
    (references : Within env.mod env.impl.vars (arguments.flatMap argReferences)) :
    SourceCollectorBounds env (collectSourceArgumentRoots env arguments) (fun rows => ∀ roots ∈ rows, SourceRootsWithin env.mod env.impl roots) := by
  cases arguments
  all_goals try (rename_i head rest; cases head)
  all_goals simp only [exprReferences, placeReferences, viewReferences, boundReferences, argReferences, blockReferences, stmtReferences, printReferences, List.flatMap_cons, List.flatMap_nil, within_append, within_cons, within_nil] at references
  all_goals source_split_ands
  all_goals try rw [collectSourceArgumentRoots.eq_def]
  all_goals repeat' first
    | assumption
    | exact True.intro
    | exact bounded_empty _ _
    | (solve | intro roots member; cases member)
    | (apply bounded_rows_cons <;> assumption)
    | (apply bounded_union <;> assumption)
    | (solve | exact sourceReadRoots_bounded env _ annotations)
    | (solve | apply sourceCallRoots_bounded env _ _ accepted <;> assumption)
    | (apply bounded_local <;> assumption)
    | (apply bounded_global <;> assumption)
    | (solve | source_action collectSourceExprRoots; apply collectSourceExprRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePlaceRoots; apply collectSourcePlaceRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceViewRoots; apply collectSourceViewRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBoundRoots; apply collectSourceBoundRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceArgumentRoots; apply collectSourceArgumentRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceExprListRoots; apply collectSourceExprListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBlockRoots; apply collectSourceBlockRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtListRoots; apply collectSourceStmtListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePrintRoots; apply collectSourcePrintRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtRoots; apply collectSourceStmtRoots_bounded _ _ accepted annotations <;> assumption)
    | (source_action pure; apply collector_bounds_pure)
    | (source_action bind; apply collector_bounds_bind)
    | (source_action modify; apply collector_bounds_write; apply bounded_union <;> assumption)
    | source_intro_callback
termination_by sizeOf arguments

theorem collectSourceExprListRoots_bounded (env : PEnv) (expressions : List Expr)
    (accepted : Core.validate env.mod = .ok ()) (annotations : SourceAnnotationBounds env)
    (references : Within env.mod env.impl.vars (expressions.flatMap exprReferences)) :
    SourceCollectorBounds env (collectSourceExprListRoots env expressions) (fun _ => True) := by
  cases expressions
  all_goals simp only [exprReferences, placeReferences, viewReferences, boundReferences, argReferences, blockReferences, stmtReferences, printReferences, List.flatMap_cons, List.flatMap_nil, within_append, within_cons, within_nil] at references
  all_goals source_split_ands
  all_goals try rw [collectSourceExprListRoots.eq_def]
  all_goals repeat' first
    | exact True.intro
    | (source_action pure; apply collector_bounds_pure)
    | (solve | source_action collectSourceExprRoots; apply collectSourceExprRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePlaceRoots; apply collectSourcePlaceRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceViewRoots; apply collectSourceViewRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBoundRoots; apply collectSourceBoundRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceArgumentRoots; apply collectSourceArgumentRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceExprListRoots; apply collectSourceExprListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBlockRoots; apply collectSourceBlockRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtListRoots; apply collectSourceStmtListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePrintRoots; apply collectSourcePrintRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtRoots; apply collectSourceStmtRoots_bounded _ _ accepted annotations <;> assumption)
    | (source_action bind; apply collector_bounds_discard)
termination_by sizeOf expressions

theorem collectSourceBlockRoots_bounded (env : PEnv) (body : Block)
    (accepted : Core.validate env.mod = .ok ()) (annotations : SourceAnnotationBounds env)
    (references : Within env.mod env.impl.vars (blockReferences body)) :
    SourceCollectorBounds env (collectSourceBlockRoots env body) (SourceRootsWithin env.mod env.impl) := by
  cases body with
  | mk scope statements value =>
      let inner := { env with scopes := scope :: env.scopes }
      cases value with
      | none =>
          have source : Within env.mod env.impl.vars (statements.flatMap stmtReferences) := by
            simpa only [blockReferences, List.append_nil] using references
          have first : SourceCollectorBounds env (collectSourceStmtListRoots inner statements)
              (fun _ => True) :=
            collectSourceStmtListRoots_bounded inner statements accepted annotations source
          rw [collectSourceBlockRoots.eq_def]
          exact collector_bounds_discard env _ _ (fun _ => True) _ first
            (collector_bounds_pure env [] _ (bounded_empty _ _))
      | some expression =>
          have source : Within env.mod env.impl.vars (statements.flatMap stmtReferences) ∧
              Within env.mod env.impl.vars (exprReferences expression) := by
            simpa only [blockReferences, within_append] using references
          have first : SourceCollectorBounds env (collectSourceStmtListRoots inner statements)
              (fun _ => True) :=
            collectSourceStmtListRoots_bounded inner statements accepted annotations source.1
          have last : SourceCollectorBounds env (collectSourceExprRoots inner expression)
              (SourceRootsWithin env.mod env.impl) :=
            collectSourceExprRoots_bounded inner expression accepted annotations source.2
          rw [collectSourceBlockRoots.eq_def]
          exact collector_bounds_discard env _ _ (fun _ => True) _ first last
termination_by sizeOf body

theorem collectSourceStmtListRoots_bounded (env : PEnv) (statements : List Stmt)
    (accepted : Core.validate env.mod = .ok ()) (annotations : SourceAnnotationBounds env)
    (references : Within env.mod env.impl.vars (statements.flatMap stmtReferences)) :
    SourceCollectorBounds env (collectSourceStmtListRoots env statements) (fun _ => True) := by
  cases statements
  all_goals simp only [exprReferences, placeReferences, viewReferences, boundReferences, argReferences, blockReferences, stmtReferences, printReferences, List.flatMap_cons, List.flatMap_nil, within_append, within_cons, within_nil] at references
  all_goals source_split_ands
  all_goals try rw [collectSourceStmtListRoots.eq_def]
  all_goals repeat' first
    | exact True.intro
    | (source_action pure; apply collector_bounds_pure)
    | (solve | source_action collectSourceExprRoots; apply collectSourceExprRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePlaceRoots; apply collectSourcePlaceRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceViewRoots; apply collectSourceViewRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBoundRoots; apply collectSourceBoundRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceArgumentRoots; apply collectSourceArgumentRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceExprListRoots; apply collectSourceExprListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBlockRoots; apply collectSourceBlockRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtListRoots; apply collectSourceStmtListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePrintRoots; apply collectSourcePrintRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtRoots; apply collectSourceStmtRoots_bounded _ _ accepted annotations <;> assumption)
    | (source_action bind; apply collector_bounds_discard)
termination_by sizeOf statements

theorem collectSourcePrintRoots_bounded (env : PEnv) (arguments : List PrintArg)
    (accepted : Core.validate env.mod = .ok ()) (annotations : SourceAnnotationBounds env)
    (references : Within env.mod env.impl.vars (arguments.flatMap printReferences)) :
    SourceCollectorBounds env (collectSourcePrintRoots env arguments) (fun _ => True) := by
  cases arguments
  all_goals try (rename_i head rest; cases head)
  all_goals simp only [exprReferences, placeReferences, viewReferences, boundReferences, argReferences, blockReferences, stmtReferences, printReferences, List.flatMap_cons, List.flatMap_nil, within_append, within_cons, within_nil] at references
  all_goals source_split_ands
  all_goals try rw [collectSourcePrintRoots.eq_def]
  all_goals repeat' first
    | exact True.intro
    | (source_action pure; apply collector_bounds_pure)
    | (solve | source_action collectSourceExprRoots; apply collectSourceExprRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePlaceRoots; apply collectSourcePlaceRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceViewRoots; apply collectSourceViewRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBoundRoots; apply collectSourceBoundRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceArgumentRoots; apply collectSourceArgumentRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceExprListRoots; apply collectSourceExprListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBlockRoots; apply collectSourceBlockRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtListRoots; apply collectSourceStmtListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePrintRoots; apply collectSourcePrintRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtRoots; apply collectSourceStmtRoots_bounded _ _ accepted annotations <;> assumption)
    | (source_action bind; apply collector_bounds_discard)
termination_by sizeOf arguments

theorem collectSourceStmtRoots_bounded (env : PEnv) (statement : Stmt)
    (accepted : Core.validate env.mod = .ok ()) (annotations : SourceAnnotationBounds env)
    (references : Within env.mod env.impl.vars (stmtReferences statement)) :
    SourceCollectorBounds env (collectSourceStmtRoots env statement) (fun _ => True) := by
  cases statement
  case ret value origin =>
    cases value
    all_goals simp only [exprReferences, placeReferences, viewReferences, boundReferences, argReferences, blockReferences, stmtReferences, printReferences, List.flatMap_cons, List.flatMap_nil, within_append, within_cons, within_nil] at references
    all_goals source_split_ands
    all_goals try rw [collectSourceStmtRoots.eq_def]
    all_goals repeat' first
      | exact True.intro
      | (source_action pure; apply collector_bounds_pure)
      | (solve | source_action collectSourceExprRoots; apply collectSourceExprRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourcePlaceRoots; apply collectSourcePlaceRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceViewRoots; apply collectSourceViewRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceBoundRoots; apply collectSourceBoundRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceArgumentRoots; apply collectSourceArgumentRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceExprListRoots; apply collectSourceExprListRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceBlockRoots; apply collectSourceBlockRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceStmtListRoots; apply collectSourceStmtListRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourcePrintRoots; apply collectSourcePrintRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceStmtRoots; apply collectSourceStmtRoots_bounded _ _ accepted annotations <;> assumption)
      | (source_action bind; apply collector_bounds_discard)
  case resize owner count fill origin =>
    cases fill
    all_goals simp only [exprReferences, placeReferences, viewReferences, boundReferences, argReferences, blockReferences, stmtReferences, printReferences, List.flatMap_cons, List.flatMap_nil, within_append, within_cons, within_nil] at references
    all_goals source_split_ands
    all_goals try rw [collectSourceStmtRoots.eq_def]
    all_goals repeat' first
      | exact True.intro
      | (source_action pure; apply collector_bounds_pure)
      | (solve | source_action collectSourceExprRoots; apply collectSourceExprRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourcePlaceRoots; apply collectSourcePlaceRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceViewRoots; apply collectSourceViewRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceBoundRoots; apply collectSourceBoundRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceArgumentRoots; apply collectSourceArgumentRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceExprListRoots; apply collectSourceExprListRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceBlockRoots; apply collectSourceBlockRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceStmtListRoots; apply collectSourceStmtListRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourcePrintRoots; apply collectSourcePrintRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceStmtRoots; apply collectSourceStmtRoots_bounded _ _ accepted annotations <;> assumption)
      | (source_action bind; apply collector_bounds_discard)
  case ifS condition yes no origin =>
    cases no
    all_goals simp only [exprReferences, placeReferences, viewReferences, boundReferences, argReferences, blockReferences, stmtReferences, printReferences, List.flatMap_cons, List.flatMap_nil, within_append, within_cons, within_nil] at references
    all_goals source_split_ands
    all_goals try rw [collectSourceStmtRoots.eq_def]
    all_goals repeat' first
      | exact True.intro
      | (source_action pure; apply collector_bounds_pure)
      | (solve | source_action collectSourceExprRoots; apply collectSourceExprRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourcePlaceRoots; apply collectSourcePlaceRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceViewRoots; apply collectSourceViewRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceBoundRoots; apply collectSourceBoundRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceArgumentRoots; apply collectSourceArgumentRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceExprListRoots; apply collectSourceExprListRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceBlockRoots; apply collectSourceBlockRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceStmtListRoots; apply collectSourceStmtListRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourcePrintRoots; apply collectSourcePrintRoots_bounded _ _ accepted annotations <;> assumption)
      | (solve | source_action collectSourceStmtRoots; apply collectSourceStmtRoots_bounded _ _ accepted annotations <;> assumption)
      | (source_action bind; apply collector_bounds_discard)
  all_goals simp only [exprReferences, placeReferences, viewReferences, boundReferences, argReferences, blockReferences, stmtReferences, printReferences, List.flatMap_cons, List.flatMap_nil, within_append, within_cons, within_nil] at references
  all_goals source_split_ands
  all_goals try rw [collectSourceStmtRoots.eq_def]
  all_goals repeat' first
    | exact True.intro
    | (source_action pure; apply collector_bounds_pure)
    | (solve | source_action collectSourceExprRoots; apply collectSourceExprRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePlaceRoots; apply collectSourcePlaceRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceViewRoots; apply collectSourceViewRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBoundRoots; apply collectSourceBoundRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceArgumentRoots; apply collectSourceArgumentRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceExprListRoots; apply collectSourceExprListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceBlockRoots; apply collectSourceBlockRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtListRoots; apply collectSourceStmtListRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourcePrintRoots; apply collectSourcePrintRoots_bounded _ _ accepted annotations <;> assumption)
    | (solve | source_action collectSourceStmtRoots; apply collectSourceStmtRoots_bounded _ _ accepted annotations <;> assumption)
    | (source_action bind; apply collector_bounds_discard)
termination_by sizeOf statement

end

private theorem sourceTableBounds_empty (module : Core.Module) (impl : Impl) (count : Nat) :
    SourceTableBounds module impl (Array.replicate count none) := by
  intro scope roots present
  simp only [Array.getElem?_replicate] at present
  split at present <;> simp_all

theorem lowerContext_source_table_bounds {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {contextIndex : ContextId} {ctx : Context} {impl : Impl}
    (contextAt : module.contexts[contextIndex]? = some ctx)
    (implAt : module.impls[ctx.impl]? = some impl) :
    SourceTableBounds module impl
      (sourceNodeRootTable ⟨module, impl, ctx, []⟩ (.block impl.body)) := by
  obtain ⟨_, _, typed, _⟩ := (validate_modOk module accepted).impl ctx.impl impl implAt |>.body
  have declared := accepted_context_root_bounds accepted contextAt implAt
  have annotations : SourceAnnotationBounds ⟨module, impl, ctx, []⟩ := ⟨declared.1, declared.2.1⟩
  have references : Within module impl.vars (blockReferences impl.body) :=
    fromBlock impl.body [] typed
  exact (collectSourceBlockRoots_bounded ⟨module, impl, ctx, []⟩ impl.body accepted annotations
    references _ (sourceTableBounds_empty module impl _)).2

theorem lowerGlobal_source_table_bounds {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (globalAt : module.globals[index]? = some global) :
    SourceTableBounds module initImpl
      (sourceNodeRootTable ⟨module, initImpl, initContext, []⟩ (.expression global.init)) := by
  obtain ⟨_, typed⟩ := (validate_modOk module accepted).glob index global globalAt |>.init
  have annotations : SourceAnnotationBounds ⟨module, initImpl, initContext, []⟩ := by
    simp [SourceAnnotationBounds, initContext]
  have references : Within module initImpl.vars (exprReferences global.init) :=
    fromExpr global.init typed
  exact (collectSourceExprRoots_bounded ⟨module, initImpl, initContext, []⟩ global.init accepted
    annotations references _ (sourceTableBounds_empty module initImpl _)).2

end Goose.Lower.Validation.SourceCanonicalRootFloors
