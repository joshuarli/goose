import Goose.Lower.Validation.ReplacementSourceSitesHeaders
import Goose.Lower.Validation.ReplacementSourceSitesEachValue
import Goose.Lower.Validation.OperandEach
import Goose.Lower.Validation.SourceStatementTypingControl
import Goose.Lower.Validation.SourceReadable

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {root : DemandNode} {targets : List BlockId}

attribute [local irreducible] ReplacementSitesAt

theorem replacementSites_forEach_source {env output : Core.TEnv} {results : List Ty}
    (sourceTypes : SourceReadableEnvironment env)
    {slot : VarId} {index : Option VarId} {view : View} {byReference : Bool}
    {body : Core.Block} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.forEach slot index view byReference body origin) start = .ok (output, finish))
    (viewChild : ReplacementSitesViewChild (root := root) (targets := targets) env results view)
    (bodyChild : ∀ {childTargets : List BlockId} {type : Ty} {first last : Nat},
      Core.tyBlock { env with loops := env.loops + 1, visible := slot :: index.toList ++ env.visible }
        [] body first = .ok (type, last) →
      ∀ (loop : Option LoopCtx) (pre : List (VarId × ValueId × OriginId)) {state : LS},
        GeneratedBuilderState state → LoopBuilderTargets loop state →
        ReplacementLoopTargetsIncluded loop childTargets →
        ReplacementSitesAt (root := root) (targets := childTargets) (lowerEnv env.mod env.vars results) state (lowerBlock loop pre false body))
    {before : LS} (generated : GeneratedBuilderState before) (loop : Option LoopCtx) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before
      (lowerStmt loop (.forEach slot index view byReference body origin)) := by
  obtain ⟨localVar, element, writable, indexStart, viewStart, viewFinish, bodyType,
    _, _, viewSource, _, bodySource, _⟩ := tyStmt_forEach_children source
  let le := lowerEnv env.mod env.vars results
  let sourced := lowerEachSource view le before
  let regrown := regrowOf sourced.1.1 le sourced.2
  let sampled := eachSampled regrown.1 sourced.1.2 le regrown.2
  let started := emitDef (.constInt .i64 0) le sampled.2
  have sourceSites : ReplacementSitesAt (root := root) (targets := targets) le before (lowerEachSource view) := by
    unfold ReplacementSitesAt ReplacementSitesFree
    intro bounded checked
    have viewed := viewChild viewSource generated
    unfold ReplacementSitesAt ReplacementSitesFree at viewed
    have viewed := viewed bounded checked
    cases view <;> exact viewed
  have sourcedGenerated : GeneratedBuilderState sourced.2 := generated.lowerEachSource view
    (show lowerEachSource view le before = sourced from rfl)
  have regrownGenerated : GeneratedBuilderState regrown.2 := sourcedGenerated.regrowOf sourced.1.1
    (show regrowOf sourced.1.1 le sourced.2 = regrown from rfl)
  have sampledGenerated : GeneratedBuilderState sampled.2 := regrownGenerated.eachSampled regrown.1 sourced.1.2
    (show eachSampled regrown.1 sourced.1.2 le regrown.2 = sampled from rfl)
  have startedGenerated : GeneratedBuilderState started.2 := sampledGenerated.emitDef (.constInt .i64 0)
    (show emitDef _ le sampled.2 = started from rfl)
  apply sourceSites.bind
  apply (ReplacementSitesAt.regrowOf _ _ _).bind
  apply (ReplacementSitesAt.eachSampled _ _ _ _).bind
  apply (ReplacementSitesAt.emitDef _ (by intros; trivial)).bind
  apply ReplacementSitesAt.whenLive
  intro block live
  refine ReplacementSitesAt.header_generated (α := Unit) (le := le) (before := started.2)
    (tail := fun header parameters => lowerEach regrown.1 sourced.1.1 sampled.1 header (parameters.headD 0) (fun depth exit => do
      let reference ← emitDef (.refElem sourced.1.2 (parameters.headD 0))
      let value ← eachElemValue slot byReference reference
      let pre := (slot, value, origin) :: (match (generalizing := false) index with
        | some slot => [(slot, parameters.headD 0, origin)] | none => [])
      lowerBlock (some ⟨depth, exit, .next header .i64 (parameters.headD 0)⟩) pre false body))
    [.data (.int .i64)] [started.1] startedGenerated ?_
  intro header parameters state current headerBound
  refine ReplacementSitesAt.lowerEach_generated regrown.1 sourced.1.1 sampled.1 header (parameters.headD 0) (by simp) current ?_
  intro depth exit bodyState bodyGenerated exitBound grows
  let reference := emitDef (.refElem sourced.1.2 (parameters.headD 0)) le bodyState
  let value := eachElemValue slot byReference reference.1 le reference.2
  have referenceGenerated := bodyGenerated.emitDef (.refElem sourced.1.2 (parameters.headD 0))
    (show emitDef _ le bodyState = reference from rfl)
  have valueGenerated := referenceGenerated.eachElemValue slot byReference reference.1
    (show eachElemValue slot byReference reference.1 le reference.2 = value from rfl)
  let measured := eachLen regrown.1 sourced.1.1 sampled.1 le state
  let compared := emitDef (.cmp .lt .i64 (parameters.headD 0) measured.1) le measured.2
  have measuredDense := dense_eachLen regrown.1 sourced.1.1 sampled.1 le state measured.1 measured.2 rfl current.dense current.live
  have comparedDense := dense_emitDef (.cmp .lt .i64 (parameters.headD 0) measured.1) le measured.2 compared.1 compared.2 rfl measuredDense.1 measuredDense.2.1
  have headerAtBody := Nat.lt_of_lt_of_le headerBound (Nat.le_trans measuredDense.2.2 (Nat.le_trans comparedDense.2.2 grows))
  have referenceDense := dense_emitDef (.refElem sourced.1.2 (parameters.headD 0)) le bodyState reference.1 reference.2 rfl bodyGenerated.dense bodyGenerated.live
  have valueDense := dense_eachElemValue slot byReference reference.1 le reference.2 value.1 value.2 rfl referenceDense.1 referenceDense.2.1
  have valueBounds : LoopBuilderTargets (some ⟨depth, exit, .next header .i64 (parameters.headD 0)⟩) value.2 :=
    (show LoopBuilderTargets (some ⟨depth, exit, .next header .i64 (parameters.headD 0)⟩) bodyState from ⟨exitBound, headerAtBody⟩).mono
      (Nat.le_trans referenceDense.2.2 valueDense.2.2)
  apply (ReplacementSitesAt.emitDef _ (by intros; trivial)).bind
  apply ReplacementSitesAt.bind
  · exact ReplacementSitesAt.eachElemValue _ _ _ _ _ (by intros; trivial)
  · exact bodyChild bodySource (some ⟨depth, exit, .next header .i64 (parameters.headD 0)⟩)
      ((slot, value.1, origin) :: (match (generalizing := false) index with | some slot => [(slot, parameters.headD 0, origin)] | none => []))
      valueGenerated valueBounds
      (by simp [ReplacementLoopTargetsIncluded, LoopBuilderFrameTargets])

end Goose.Lower.Validation
