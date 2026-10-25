import Goose.Lower.Validation.SourceCanonicalRootFloorsContracts

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource

private theorem generated_push {before after : LS} (generated : GeneratedBuilderState before)
    {scope : ScopeId} {le : LEnv} {result : Unit}
    (run : pushScope scope le before = (result, after)) : GeneratedBuilderState after := by
  rw [pushScope_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨generated.dense, generated.live, generated.targets⟩

private theorem popped_extension {before after : LS} {le : LEnv} {result : Unit}
    (run : popScope le before = (result, after)) : before.Ext after := by
  rw [popScope_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact LS.Ext.refl before

private theorem popped_projects {env : PEnv} {root : DemandNode} {func : Func}
    {before after : LS} {le : LEnv} {result : Unit}
    (projects : RecipeMetadataProjects env root func after)
    (run : popScope le before = (result, after)) : RecipeMetadataProjects env root func before := by
  apply projects.restrict
  have same := recipesUnchangedB_popScope le before
  rw [run] at same
  dsimp only at same
  intro recipe member
  rwa [same]

theorem block_floor (scope : ScopeId) (statements : List Stmt) (tail : Option Expr)
    (child : match tail with | none => True | some expression => ExpressionFloor expression) :
    BlockFloor (.mk scope statements tail) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots range replayed returnTypes before after value run generated live continuation projects
  have replayShape := rpBlockValue_ok env [] scope statements tail rootsBefore sourceRoots range rootsAfter replayed
  obtain ⟨_, _, valueReplay, _⟩ := replayShape.2
  unfold tyBlock at source
  by_cases nested : scope ∈ typing.scopes
  · simp [nested, chk] at source
  · simp only [List.contains_iff_mem, nested, ite_false] at source
    obtain ⟨declared, declaredFinish, declaration, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨finalEnv, valueStart, statementsTyped, source⟩ := (st_bind_ok _ _ _ _).mp source
    have declaredEnv := declarePre_lowerEnv declaration returnTypes
    have finalLower := tyStmts_lowerEnv statementsTyped returnTypes
    have sameEnv : lowerEnv finalEnv.mod finalEnv.vars returnTypes = lowerEnv typing.mod typing.vars returnTypes :=
      finalLower.trans declaredEnv
    have declarationTables := declarePre_tables [] declaration
    have finalTables := tyStmts_tables statements statementsTyped
    have childTables : SourceRootTables finalEnv {env with scopes := scope :: env.scopes} := by
      constructor
      · exact sourceTables.moduleEq.trans (finalTables.1.trans declarationTables.1).symm
      · exact sourceTables.variablesEq.trans (finalTables.2.1.trans declarationTables.2.1).symm
    simp only [lowerBlock, inScope] at run
    obtain ⟨_, entered, enterRun, run⟩ := bind_eq.mp run
    obtain ⟨_, pushed, pushRun, run⟩ := bind_eq.mp run
    obtain ⟨result, bodyAfter, bodyRun, run⟩ := bind_eq.mp run
    obtain ⟨_, popped, popRun, run⟩ := bind_eq.mp run
    obtain ⟨resultEq, stateEq⟩ := pure_eq.mp run
    subst after
    subst value
    obtain ⟨_, initialized, initRun, bodyRun⟩ := bind_eq.mp bodyRun
    obtain ⟨_, statementsAfter, statementsRun, bodyRun⟩ := bind_eq.mp bodyRun
    obtain ⟨result, valueAfter, valueRun, bodyRun⟩ := bind_eq.mp bodyRun
    obtain ⟨_, left, leaveRun, bodyRun⟩ := bind_eq.mp bodyRun
    obtain ⟨rfl, rfl⟩ := pure_eq.mp bodyRun
    have leftLive := dead_popScope.live_before popRun live
    have valueLive := (dead_emitEffect (.leave scope)).live_before leaveRun leftLive
    have enteredGenerated := generated.emitEffect (.enter scope) enterRun
    have pushedGenerated := generated_push enteredGenerated pushRun
    have initializedGenerated := pushedGenerated.initSlots [] initRun
    have statementsGenerated := initializedGenerated.lowerStmts none statements trivial statementsRun
    cases tail with
    | none => rw [valueReplay.1]; exact List.nil_subset _
    | some expression =>
        have tailLocation : DemandNodeAt root (path ++ [statements.length]) (.expression expression) := by
          apply location.snoc statements.length
          simp [DemandNode.child?, DemandNode.children]
        have valueContinuation := (continuation.of_extension (popped_extension popRun)).of_advance
          (advB_emitEffect _ _ _ _ _ leaveRun)
        have valueProjects := (popped_projects projects popRun).of_advance (advB_emitEffect _ _ _ _ _ leaveRun)
        have contextualProjects : RecipeMetadataProjects {env with scopes := scope :: env.scopes} root func valueAfter :=
          RecipeMetadataProjects.access (left := env) (right := {env with scopes := scope :: env.scopes}) rfl valueProjects
        simp only [lowerBlockValue] at valueRun
        rw [← sameEnv] at valueRun
        exact child (tables.scopes (scope :: env.scopes)) childTables valid tailLocation source valueReplay
          valueRun statementsGenerated valueLive valueContinuation contextualProjects

theorem block_expression_floor (body : Core.Block) (child : BlockFloor body) : ExpressionFloor (.blockE body) := by
  intro env typing func root tables sourceTables valid path location info start finish source
    rootsBefore rootsAfter sourceRoots replayed returnTypes before after value run generated live continuation projects
  simp only [rpExpr] at replayed
  obtain ⟨blockResult, _, blockReplay, replayed⟩ := (st_bind_ok _ _ _ _).mp replayed
  have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp replayed)
  dsimp only at shape
  rw [shape]
  exact child tables sourceTables.exprEnv valid (location.snoc 0 rfl) source blockReplay
    run generated live continuation projects

end Goose.Lower.Validation.SourceCanonicalRootFloors
