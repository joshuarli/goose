import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceBranches

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem profile_source_while {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (condition : Expr) (body : Core.Block) (origin : OriginId)
    (conditionChild : EmittedProfileSourceExpression env results condition)
    (bodyChild : ∀ env, EmittedProfileSourceBlock env results body) :
    EmittedProfileSourceStatement env results scope (.while condition body origin) := by
  intro output start finish source loop
  obtain ⟨conditionFinish, bodyType, conditionSource, bodySource, _⟩ := tyStmt_while_children source
  exact (EmittedProfileRun.newBlock []).bind fun header =>
    (EmittedProfileRun.emitTerm (.br header.1 []) trivial).bind fun _ =>
      (EmittedProfileRun.setCur _).bind fun _ =>
        EmittedProfileRun.lowerWhile header.1 (conditionChild conditionSource)
          (fun depth target => bodyChild { env with loops := env.loops + 1 } bodySource _ [] false)

theorem profile_source_forRange {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : VarId) (lo hi : Expr) (body : Core.Block) (origin : OriginId)
    (lowChild : EmittedProfileSourceExpression env results lo) (highChild : EmittedProfileSourceExpression env results hi)
    (bodyChild : ∀ env, EmittedProfileSourceBlock env results body) :
    EmittedProfileSourceStatement env results scope (.forRange slot lo hi body origin) := by
  intro output start finish source loop
  obtain ⟨localVar, integer, lowerStart, lowerFinish, upperFinish, bodyType,
    declared, lowSource, highSource, binderType, bodySource, _⟩ := tyStmt_forRange_children source
  refine (lowChild lowSource).bind fun low => (highChild highSource).bind fun high => ?_
  apply EmittedProfileRun.whenLive
  intro current
  exact (EmittedProfileRun.intTyOf low).bind fun hint =>
    (EmittedProfileRun.newBlock [.data (.int hint)]).bind fun header =>
      (EmittedProfileRun.emitTerm (.br header.1 [low]) trivial).bind fun _ =>
        (EmittedProfileRun.setCur _).bind fun _ =>
          EmittedProfileRun.lowerRange hint (header.2.headD 0) high header.1
            (fun depth target => bodyChild { env with loops := env.loops + 1, visible := slot :: env.visible }
              bodySource _ [(slot, header.2.headD 0, origin)] false)

theorem profile_source_eachSource {env : Core.TEnv} {results : List Ty} (view : View)
    (child : EmittedProfileSourceView env results view) {element : Ty} {writable : Bool} {start finish : Nat}
    (typed : Core.tyView env view start = .ok ((element, writable), finish)) :
    EmittedProfileRun env.mod.profile (lowerEnv env.mod env.vars results) (lowerEachSource view) := by
  have checked := child typed
  intro before result after run profile
  apply checked before result.2 after ?_ profile
  cases view <;> simp only [lowerEachSource, lowerView, bind_eq] at run ⊢
  all_goals
    obtain ⟨value, first, childRun, snapshot, emitted, emitRun, pureRun⟩ := run
    obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
    exact ⟨value, first, childRun, emitRun⟩

theorem profile_source_forEach {env : Core.TEnv} {results : List Ty} (scope : ScopeId)
    (slot : VarId) (index : Option VarId) (view : View) (byRef : Bool) (body : Core.Block) (origin : OriginId)
    (viewChild : EmittedProfileSourceView env results view)
    (bodyChild : ∀ env, EmittedProfileSourceBlock env results body) :
    EmittedProfileSourceStatement env results scope (.forEach slot index view byRef body origin) := by
  intro output start finish source loop
  obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
    declared, indexDeclared, viewSource, binderTyped, bodySource, _⟩ := tyStmt_forEach_children source
  refine (profile_source_eachSource view viewChild viewSource).bind fun sampledSource =>
    (EmittedProfileRun.regrowOf sampledSource.1).bind fun regrow =>
      (EmittedProfileRun.eachSampled regrow sampledSource.2).bind fun sampled =>
        (EmittedProfileRun.emitDef (.constInt .i64 0) (fun _ => trivial)).bind fun startAt => ?_
  apply EmittedProfileRun.whenLive
  intro current
  exact (EmittedProfileRun.newBlock [.data (.int .i64)]).bind fun header =>
    (EmittedProfileRun.emitTerm (.br header.1 [startAt]) trivial).bind fun _ =>
      (EmittedProfileRun.setCur _).bind fun _ =>
        EmittedProfileRun.lowerEach regrow sampledSource.1 sampled header.1 (header.2.headD 0)
          (fun depth target => (EmittedProfileRun.emitDef (.refElem sampledSource.2 (header.2.headD 0)) (fun _ => trivial)).bind fun elem =>
            (EmittedProfileRun.eachElemValue slot byRef elem).bind fun value =>
              bodyChild { env with loops := env.loops + 1, visible := slot :: index.toList ++ env.visible }
                bodySource _ _ false)

end Goose.Lower.Validation
