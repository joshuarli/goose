import Goose.Core.DeclarativeRoots
import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.SourceSymbolSourceAccepted

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound
open SourceSymbolSource

def SourceRootIndexWithin (module : Core.Module) (impl : Impl) : RootRef → Prop
  | .local index => index < impl.vars.size
  | .global index => index < module.globals.size
  | .param index => index < impl.params.size

def SourceRootsWithin (module : Core.Module) (impl : Impl) (roots : List RootRef) : Prop :=
  ∀ root ∈ roots, SourceRootIndexWithin module impl root

private theorem roots_empty (module : Core.Module) (impl : Impl) : SourceRootsWithin module impl [] := by
  intro root member
  cases member

private theorem roots_union {module : Core.Module} {impl : Impl} {left right : List RootRef}
    (first : SourceRootsWithin module impl left) (second : SourceRootsWithin module impl right) :
    SourceRootsWithin module impl (unionRoots left right) := by
  intro root member
  exact (unionRoots_mem _ _ root member).elim (first root) (second root)

private theorem annotation_row_bounds {module : Core.Module} {impl : Impl} {ctx : Context}
    (context : CtxOk module impl ctx) {varId : VarId} {roots : List RootRef}
    (row : (varId, roots) ∈ ctx.varRoots) : SourceRootsWithin module impl roots := by
  obtain ⟨_, _, _, declared⟩ := (Core.Declarative.annotations_sound module impl ctx
    context.annotationShape).1 varId roots row
  intro root member
  have bound := declared root member
  cases root with
  | «local» index =>
    obtain ⟨localVar, lookup, _⟩ := bound
    exact (Array.getElem?_eq_some_iff.mp lookup).1
  | global index => exact bound
  | param index => exact bound

private theorem content_row_bounds {module : Core.Module} {impl : Impl} {ctx : Context}
    (context : CtxOk module impl ctx) {varId : VarId} {roots : List RootRef}
    (row : (varId, roots) ∈ ctx.contentRoots) : SourceRootsWithin module impl roots := by
  obtain ⟨_, _, _, _, _, declared⟩ := Core.Declarative.declaredContents_sound module impl ctx
    context.contentShape varId roots row
  intro root member
  have bound := declared root member
  cases root with
  | «local» index => exact bound.elim
  | global index => exact bound
  | param index => exact bound

private theorem result_row_bounds {module : Core.Module} {impl : Impl} {ctx : Context}
    (context : CtxOk module impl ctx) {roots : List RootRef} (row : roots ∈ ctx.resultRoots) :
    SourceRootsWithin module impl roots := by
  have declarations := Core.Declarative.declaredResults_sound module impl ctx context.resultShape
  have index := List.getElem_of_mem row
  obtain ⟨index, bounded, equal⟩ := index
  have resultBound : index < impl.results.toList.length := by
    simpa only [declarations.1, Array.length_toList] using bounded
  have paired : (impl.results.toList[index], roots) ∈ impl.results.toList.zip ctx.resultRoots := by
    apply List.mem_of_getElem?
    apply List.getElem?_zip_eq_some.mpr
    exact ⟨List.getElem?_eq_getElem resultBound, by simpa only [equal] using List.getElem?_eq_getElem bounded⟩
  intro root member
  have bound := (declarations.2 _ roots paired).2 root member
  cases root with
  | «local» index => exact bound.elim
  | global index => exact bound
  | param index => exact bound.1

private theorem read_bounds {env : PEnv} (context : CtxOk env.mod env.impl env.ctx)
    {place : Place} {before after : RState} {roots : List RootRef}
    (replayed : readRoots env place before = .ok (roots, after)) :
    SourceRootsWithin env.mod env.impl roots := by
  rcases (readRoots_ok env place before (roots, after) replayed).2 with
    ⟨varId, _, _, _, _, row⟩ | ⟨varId, _, _, row⟩ | empty
  · unfold PEnv.ann at row
    cases found : env.ctx.varRoots.find? (·.1 == varId) with
    | none => simp [found] at row
    | some pair =>
      simp only [found, Option.map_some, Option.some.injEq] at row
      rw [← row]
      exact annotation_row_bounds context (List.mem_of_find?_eq_some found)
  · unfold PEnv.cont at row
    cases found : env.ctx.contentRoots.find? (·.1 == varId) with
    | none => simp [found] at row
    | some pair =>
      simp only [found, Option.map_some, Option.some.injEq] at row
      rw [← row]
      exact content_row_bounds context (List.mem_of_find?_eq_some found)
  · have emptyRoots : roots = [] := empty.1
    rw [emptyRoots]
    exact roots_empty _ _

private theorem map_callee_bounds {module : Core.Module} {impl : Impl}
    {arguments : List (List RootRef)} (bounded : ∀ roots ∈ arguments, SourceRootsWithin module impl roots)
    {root : RootRef} {mapped : List RootRef}
    (globalBound : ∀ index, root = .global index → index < module.globals.size)
    (replayed : mapCalleeRoots arguments root = .ok mapped) : SourceRootsWithin module impl mapped := by
  cases root with
  | «local» index => simp [mapCalleeRoots, reject] at replayed
  | global index =>
    have equal : mapped = [.global index] := (ex_pure_ok _ _).mp replayed
    rw [equal]
    intro root member
    have same := List.mem_singleton.mp member
    subst root
    exact globalBound index rfl
  | param index =>
    cases row : arguments[index]? with
    | none => simp [mapCalleeRoots, row, reject] at replayed
    | some roots =>
      have equal : mapped = roots := by simpa [mapCalleeRoots, row, ex_pure_ok] using replayed
      rw [equal]
      exact bounded roots (List.mem_of_getElem? row)

private theorem map_result_bounds {module : Core.Module} {impl : Impl}
    {arguments : List (List RootRef)} (bounded : ∀ roots ∈ arguments, SourceRootsWithin module impl roots)
    (declared : List RootRef) {initial actual : List RootRef}
    (initialBounds : SourceRootsWithin module impl initial)
    (globals : ∀ root ∈ declared, ∀ index, root = .global index → index < module.globals.size)
    (replayed : mapResultRoots arguments initial declared = .ok actual) : SourceRootsWithin module impl actual := by
  induction declared generalizing initial with
  | nil =>
    have same : actual = initial := (ex_pure_ok _ _).mp replayed
    simpa only [same] using initialBounds
  | cons root rest ih =>
    simp only [mapResultRoots] at replayed
    obtain ⟨mapped, mapping, replayed⟩ := (ex_bind_ok _ _ _).mp replayed
    exact ih (roots_union initialBounds (map_callee_bounds bounded
      (globals root (by simp)) mapping)) (fun root member => globals root (by simp [member])) replayed

private theorem call_result_bounds {module : Core.Module} {impl callee : Impl} {ctx : Context}
    (context : CtxOk module callee ctx) {arguments : List (List RootRef)}
    (bounded : ∀ roots ∈ arguments, SourceRootsWithin module impl roots) {roots : List RootRef}
    (replayed : callResultRoots callee ctx arguments = .ok roots) : SourceRootsWithin module impl roots := by
  unfold callResultRoots at replayed
  split at replayed
  · rename_i result declared results contexts
    split at replayed
    · apply map_result_bounds bounded _ (roots_empty _ _) ?_ replayed
      intro root member index same
      have row : declared ∈ ctx.resultRoots := by simp [contexts]
      have bounds := result_row_bounds context row root member
      simpa only [same, SourceRootIndexWithin] using bounds
    · have same : roots = [] := (ex_pure_ok _ _).mp replayed
      rw [same]
      exact roots_empty _ _
  · have same : roots = [] := (ex_pure_ok _ _).mp replayed
    rw [same]
    exact roots_empty _ _

mutual

private theorem replay_expr_bounds (expression : Expr) {env : PEnv}
    (context : CtxOk env.mod env.impl env.ctx) (module : ModOk env.mod)
    (references : Within env.mod env.impl.vars (exprReferences expression))
    {before after : RState} {roots : List RootRef}
    (replayed : rpExpr env expression before = .ok (roots, after)) :
    SourceRootsWithin env.mod env.impl roots := by
  cases expression with
  | lit _ _ | bool _ | len _ | un _ _ _ | bin _ _ _ _ | cmp _ _ _ | and _ _ | or _ _
      | not _ | conv _ _ _ _ | pop _ _ | arrLit _ _ | structLit _ _ | fill _ _ =>
    simp only [rpExpr] at replayed
    repeat' first
    | (have emptyRoots : roots = [] := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
       rw [emptyRoots]
       exact roots_empty _ _)
    | (obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed)
    | (split at replayed)
  | read place =>
    simp only [rpExpr] at replayed
    obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    exact read_bounds context replayed
  | ref _ place =>
    exact replay_place_bounds place context module
      (by simpa only [exprReferences] using references) replayed
  | slice _ view low high _ =>
    simp only [rpExpr] at replayed
    obtain ⟨viewRoots, _, viewReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    have same : roots = viewRoots := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
    rw [same]
    exact replay_view_bounds view context module
      (fun reference member => references reference (by simp [exprReferences, member])) viewReplay
  | push owner value origin =>
    simp only [rpExpr] at replayed
    obtain ⟨ownerRoots, _, ownerReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    have same : roots = ownerRoots := by
      repeat' first
      | (exact congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed))
      | (obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed)
      | (split at replayed)
    rw [same]
    exact replay_place_bounds owner context module
      (fun reference member => references reference (by simp [exprReferences, member])) ownerReplay
  | call contextId arguments _ =>
    simp only [rpExpr] at replayed
    obtain ⟨argumentRoots, callStart, argumentsReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨_, callReady, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨calleeContext, callee, contextAt, calleeAt, _, _, resultReplay⟩ :=
      rpCall_ok env contextId argumentRoots callReady roots after replayed
    obtain ⟨found, foundAt, foundContext⟩ := module.ctx contextId calleeContext contextAt
    rw [calleeAt] at foundAt
    cases Option.some.inj foundAt
    apply call_result_bounds foundContext ?_ resultReplay
    exact replay_args_bounds arguments context module
      (fun reference member => references reference (by simp [exprReferences, member])) argumentsReplay
  | ifE condition yes no =>
    simp only [rpExpr] at replayed
    obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨⟨yesRoots, yesRange⟩, _, yesReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨⟨noRoots, noRange⟩, _, noReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    have same : roots = unionRoots yesRoots noRoots := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
    rw [same]
    exact roots_union
      (replay_block_bounds yes context module
        (fun reference member => references reference (by simp [exprReferences, member])) yesReplay)
      (replay_block_bounds no context module
        (fun reference member => references reference (by simp [exprReferences, member])) noReplay)
  | blockE body =>
    simp only [rpExpr] at replayed
    obtain ⟨⟨bodyRoots, bodyRange⟩, _, bodyReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    have same : roots = bodyRoots := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
    rw [same]
    exact replay_block_bounds body context module
      (by simpa only [exprReferences] using references) bodyReplay
termination_by sizeOf expression

private theorem replay_place_bounds (place : Place) {env : PEnv}
    (context : CtxOk env.mod env.impl env.ctx) (module : ModOk env.mod)
    (references : Within env.mod env.impl.vars (placeReferences place))
    {before after : RState} {roots : List RootRef}
    (replayed : rpPlace env place before = .ok (roots, after)) :
    SourceRootsWithin env.mod env.impl roots := by
  cases place with
  | var index =>
    have same : roots = [.local index] := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
    rw [same]
    intro root member
    cases List.mem_singleton.mp member
    exact references (.slot index) (by simp [placeReferences])
  | global index =>
    have same : roots = [.global index] := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
    rw [same]
    intro root member
    cases List.mem_singleton.mp member
    exact references (.global index) (by simp [placeReferences])
  | deref expression =>
    exact replay_expr_bounds expression context module
      (by simpa only [placeReferences] using references) replayed
  | field owner _ =>
    exact replay_place_bounds owner context module
      (by simpa only [placeReferences] using references) replayed
  | elem view index _ =>
    simp only [rpPlace] at replayed
    obtain ⟨viewRoots, _, viewReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    have same : roots = viewRoots := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
    rw [same]
    exact replay_view_bounds view context module
      (fun reference member => references reference (by simp [placeReferences, member])) viewReplay
termination_by sizeOf place

private theorem replay_view_bounds (view : View) {env : PEnv}
    (context : CtxOk env.mod env.impl env.ctx) (module : ModOk env.mod)
    (references : Within env.mod env.impl.vars (viewReferences view))
    {before after : RState} {roots : List RootRef}
    (replayed : rpView env view before = .ok (roots, after)) :
    SourceRootsWithin env.mod env.impl roots := by
  cases view with
  | val expression =>
    exact replay_expr_bounds expression context module
      (by simpa only [viewReferences] using references) replayed
  | of place =>
    simp only [rpView] at replayed
    obtain ⟨placeRoots, _, placeReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    obtain ⟨_, _, _, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
    have same : roots = placeRoots := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
    rw [same]
    exact replay_place_bounds place context module
      (by simpa only [viewReferences] using references) placeReplay
termination_by sizeOf view

private theorem replay_args_bounds (arguments : List Arg) {env : PEnv}
    (context : CtxOk env.mod env.impl env.ctx) (module : ModOk env.mod)
    (references : Within env.mod env.impl.vars (arguments.flatMap argReferences))
    {before after : RState} {rows : List (List RootRef)}
    (replayed : rpArgs env arguments before = .ok (rows, after)) :
    ∀ roots ∈ rows, SourceRootsWithin env.mod env.impl roots := by
  cases arguments with
  | nil =>
    have same : rows = [] := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
    simp [same]
  | cons argument rest =>
    have restReferences : Within env.mod env.impl.vars (rest.flatMap argReferences) := by
      intro reference member
      exact references reference (by simp [member])
    cases argument with
    | byVal expression =>
      simp only [rpArgs] at replayed
      obtain ⟨head, _, headReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
      obtain ⟨tail, _, tailReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
      have same : rows = head :: tail := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
      rw [same]
      intro roots member
      rcases List.mem_cons.mp member with rfl | member
      · exact replay_expr_bounds expression context module
          (fun reference member => references reference (by simp [argReferences, member])) headReplay
      · exact replay_args_bounds rest context module restReferences tailReplay roots member
    | byRef mode place =>
      simp only [rpArgs] at replayed
      obtain ⟨head, _, headReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
      obtain ⟨tail, _, tailReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
      have same : rows = head :: tail := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
      rw [same]
      intro roots member
      rcases List.mem_cons.mp member with rfl | member
      · exact replay_place_bounds place context module
          (fun reference member => references reference (by simp [argReferences, member])) headReplay
      · exact replay_args_bounds rest context module restReferences tailReplay roots member
termination_by sizeOf arguments

private theorem replay_block_bounds (body : Core.Block) {env : PEnv}
    (context : CtxOk env.mod env.impl env.ctx) (module : ModOk env.mod)
    (references : Within env.mod env.impl.vars (blockReferences body))
    {pre : List VarId} {before after : RState} {roots : List RootRef} {range : Nat × Nat}
    (replayed : rpBlockValue env pre body before = .ok ((roots, range), after)) :
    SourceRootsWithin env.mod env.impl roots := by
  cases body with
  | mk scope statements expression =>
    obtain ⟨rootState, _, valueReplay, _⟩ :=
      (rpBlockValue_ok env pre scope statements expression before roots range after replayed).2
    cases expression with
    | none =>
      rw [valueReplay.1]
      exact roots_empty _ _
    | some expression =>
      exact replay_expr_bounds expression (env := { env with scopes := scope :: env.scopes }) context module
        (fun reference member => references reference (by simp [blockReferences, member])) valueReplay
termination_by sizeOf body

end

private theorem accepted_context_bounds_source {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {contextIndex : ContextId} {ctx : Context} {impl : Impl}
    (contextAt : module.contexts[contextIndex]? = some ctx)
    (implAt : module.impls[ctx.impl]? = some impl) : CtxOk module impl ctx := by
  obtain ⟨found, foundAt, context⟩ := (validate_modOk module accepted).ctx contextIndex ctx contextAt
  rw [implAt] at foundAt
  cases Option.some.inj foundAt
  exact context

theorem accepted_context_root_bounds {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {contextIndex : ContextId} {ctx : Context} {impl : Impl}
    (contextAt : module.contexts[contextIndex]? = some ctx)
    (implAt : module.impls[ctx.impl]? = some impl) :
    (∀ varId roots, (varId, roots) ∈ ctx.varRoots → SourceRootsWithin module impl roots) ∧
    (∀ varId roots, (varId, roots) ∈ ctx.contentRoots → SourceRootsWithin module impl roots) ∧
    (∀ roots ∈ ctx.resultRoots, SourceRootsWithin module impl roots) := by
  have context := accepted_context_bounds_source accepted contextAt implAt
  exact ⟨fun _ _ row => annotation_row_bounds context row,
    fun _ _ row => content_row_bounds context row, fun _ row => result_row_bounds context row⟩

theorem source_expr_root_bounds (expression : Expr) {env : TEnv} {penv : PEnv}
    (tables : SourceRootTables env penv) (accepted : Core.validate penv.mod = .ok ())
    {contextIndex : ContextId} (contextAt : penv.mod.contexts[contextIndex]? = some penv.ctx)
    (implAt : penv.mod.impls[penv.ctx.impl]? = some penv.impl)
    {type : Ty} {start finish : Nat} (source : tyExpr env expression start = .ok (type, finish))
    {before after : RState} {roots : List RootRef}
    (replayed : rpExpr penv expression before = .ok (roots, after)) :
    SourceRootsWithin penv.mod penv.impl roots := by
  apply replay_expr_bounds expression (accepted_context_bounds_source accepted contextAt implAt)
    (validate_modOk penv.mod accepted) ?_ replayed
  simpa only [← tables.moduleEq, ← tables.variablesEq] using SourceSymbolSource.fromExpr expression source

theorem source_place_root_bounds (place : Place) {env : TEnv} {penv : PEnv}
    (tables : SourceRootTables env penv) (accepted : Core.validate penv.mod = .ok ())
    {contextIndex : ContextId} (contextAt : penv.mod.contexts[contextIndex]? = some penv.ctx)
    (implAt : penv.mod.impls[penv.ctx.impl]? = some penv.impl)
    {info : PlaceInfo} {start finish : Nat} (source : tyPlace env place start = .ok (info, finish))
    {before after : RState} {roots : List RootRef}
    (replayed : rpPlace penv place before = .ok (roots, after)) :
    SourceRootsWithin penv.mod penv.impl roots := by
  apply replay_place_bounds place (accepted_context_bounds_source accepted contextAt implAt)
    (validate_modOk penv.mod accepted) ?_ replayed
  simpa only [← tables.moduleEq, ← tables.variablesEq] using SourceSymbolSource.fromPlace place source

theorem source_view_root_bounds (view : View) {env : TEnv} {penv : PEnv}
    (tables : SourceRootTables env penv) (accepted : Core.validate penv.mod = .ok ())
    {contextIndex : ContextId} (contextAt : penv.mod.contexts[contextIndex]? = some penv.ctx)
    (implAt : penv.mod.impls[penv.ctx.impl]? = some penv.impl)
    {info : Ty × Bool} {start finish : Nat} (source : tyView env view start = .ok (info, finish))
    {before after : RState} {roots : List RootRef}
    (replayed : rpView penv view before = .ok (roots, after)) :
    SourceRootsWithin penv.mod penv.impl roots := by
  apply replay_view_bounds view (accepted_context_bounds_source accepted contextAt implAt)
    (validate_modOk penv.mod accepted) ?_ replayed
  simpa only [← tables.moduleEq, ← tables.variablesEq] using SourceSymbolSource.fromView view source

theorem source_expr_param_bounds (expression : Expr) {env : TEnv} {penv : PEnv}
    (tables : SourceRootTables env penv) (accepted : Core.validate penv.mod = .ok ())
    {contextIndex : ContextId} (contextAt : penv.mod.contexts[contextIndex]? = some penv.ctx)
    (implAt : penv.mod.impls[penv.ctx.impl]? = some penv.impl)
    {type : Ty} {start finish : Nat} (source : tyExpr env expression start = .ok (type, finish))
    {before after : RState} {roots : List RootRef}
    (replayed : rpExpr penv expression before = .ok (roots, after)) :
    ∀ index, RootRef.param index ∈ roots → index < penv.impl.params.size := by
  intro index member
  exact source_expr_root_bounds expression tables accepted contextAt implAt source replayed (.param index) member

theorem source_place_param_bounds (place : Place) {env : TEnv} {penv : PEnv}
    (tables : SourceRootTables env penv) (accepted : Core.validate penv.mod = .ok ())
    {contextIndex : ContextId} (contextAt : penv.mod.contexts[contextIndex]? = some penv.ctx)
    (implAt : penv.mod.impls[penv.ctx.impl]? = some penv.impl)
    {info : PlaceInfo} {start finish : Nat} (source : tyPlace env place start = .ok (info, finish))
    {before after : RState} {roots : List RootRef}
    (replayed : rpPlace penv place before = .ok (roots, after)) :
    ∀ index, RootRef.param index ∈ roots → index < penv.impl.params.size := by
  intro index member
  exact source_place_root_bounds place tables accepted contextAt implAt source replayed (.param index) member

theorem source_view_param_bounds (view : View) {env : TEnv} {penv : PEnv}
    (tables : SourceRootTables env penv) (accepted : Core.validate penv.mod = .ok ())
    {contextIndex : ContextId} (contextAt : penv.mod.contexts[contextIndex]? = some penv.ctx)
    (implAt : penv.mod.impls[penv.ctx.impl]? = some penv.impl)
    {info : Ty × Bool} {start finish : Nat} (source : tyView env view start = .ok (info, finish))
    {before after : RState} {roots : List RootRef}
    (replayed : rpView penv view before = .ok (roots, after)) :
    ∀ index, RootRef.param index ∈ roots → index < penv.impl.params.size := by
  intro index member
  exact source_view_root_bounds view tables accepted contextAt implAt source replayed (.param index) member

end Goose.Lower.Validation
