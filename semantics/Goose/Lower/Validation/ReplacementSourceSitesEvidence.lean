import Goose.Lower.Validation.ReplacementEmissionSite
import Goose.Lower.Validation.ReplacementEmissionMap
import Goose.Lower.GeneratedBuilder
import Goose.Lower.Validation.ValueTypes
import Goose.Lower.GeneratedIntervalFramesBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

variable {targets : List BlockId}

structure AcceptedReplacementSite (le : LEnv) (finalState : LS)
    (owner value : ValueId) (origin : OriginId) where
  sourceEnv : Core.TEnv
  results : List Ty
  environment : lowerEnv sourceEnv.mod sourceEnv.vars results = le
  place : Place
  rhs : Expr
  scope : ScopeId
  start : Nat
  finish : Nat
  output : Core.TEnv
  accepted : Core.tyStmt sourceEnv scope (.assignWhole place rhs origin) start = .ok (output, finish)
  initial : LS
  finished : LS
  site : ReplacementEmissionSite le initial finished place rhs origin
  owner_eq : site.owner = owner
  value_eq : site.value = value
  generated : GeneratedBuilderState initial
  live : site.captured.cur.isSome = true
  extension : finished.Ext finalState
  types : TypePrefix site.addressed finalState
  framed : IntervalEdgesFramed site.cleared site.captured finalState

def AcceptedReplacementSite.retained {le : LEnv} {before after : LS}
    {owner value : ValueId} {origin : OriginId}
    (site : AcceptedReplacementSite le before owner value origin)
    (extension : before.Ext after) (types : TypePrefix before after)
    (framed : IntervalEdgesFramed site.site.cleared site.site.captured after) :
    AcceptedReplacementSite le after owner value origin :=
  { site with extension := site.extension.trans extension, types := site.types.trans types, framed := framed }

theorem AcceptedReplacementSite.occurrence {le : LEnv} {finalState : LS}
    {owner value : ValueId} {origin : OriginId}
    (witness : AcceptedReplacementSite le finalState owner value origin) :
    ∃ index capturedBody finalBody tail,
      witness.site.captured.cur = some index ∧
      witness.site.captured.blocks[index]? = some capturedBody ∧
      finalState.blocks[index]? = some finalBody ∧
      finalBody.params = capturedBody.params ∧
      finalBody.insts.toList = capturedBody.insts.toList ++
        (.eff (.replace owner value (some origin)) :: tail) := by
  have addressedGenerated := witness.generated.lowerPlace witness.place witness.site.addressRun
  have clearedGenerated := addressedGenerated.emitEffect _ witness.site.clearRun
  have capturedGenerated := clearedGenerated.lowerExpr witness.rhs witness.site.rhsRun
  cases current : witness.site.captured.cur with
  | none => have active := witness.live; simp [current] at active
  | some index =>
    have bound := capturedGenerated.live index current
    let body := witness.site.captured.blocks[index]
    have row : witness.site.captured.blocks[index]? = some body := by simp [body, bound]
    have publish := witness.site.publishRun
    rw [emitEffect_run _ _ current] at publish
    have publishedRow : witness.finished.blocks[index]? =
        some { body with insts := body.insts.push (.eff (.replace owner value (some origin))) } := by
      obtain ⟨_, state⟩ := Prod.mk.inj publish
      rw [← state, Array.getElem?_modify, row]
      simp [witness.owner_eq, witness.value_eq]
    obtain ⟨finalBody, finalRow, params, tail, append⟩ := witness.extension.2 index _ publishedRow
    exact ⟨index, body, finalBody, tail, rfl, row, finalRow, params,
      by simpa [Array.toList_push, List.append_assoc] using append⟩

structure ReplacementSiteAt (le : LEnv) (state : LS) (block position : Nat)
    (owner value : ValueId) (origin : OriginId) where
  source : AcceptedReplacementSite le state owner value origin
  capturedBody : BlockB
  current : source.site.captured.cur = some block
  row : source.site.captured.blocks[block]? = some capturedBody
  position_eq : capturedBody.insts.size = position

def ReplacementSiteAt.retained {le : LEnv} {before after : LS}
    {block position owner value : Nat} {origin : OriginId}
    (site : ReplacementSiteAt le before block position owner value origin)
    (extension : before.Ext after) (types : TypePrefix before after)
    (framed : IntervalEdgesFramed site.source.site.cleared site.source.site.captured after) :
    ReplacementSiteAt le after block position owner value origin :=
  { site with source := site.source.retained extension types framed }

theorem ReplacementSiteAt.occurrence {le : LEnv} {state : LS}
    {block position owner value : Nat} {origin : OriginId}
    (witness : ReplacementSiteAt le state block position owner value origin) :
    ∃ finalBody tail, state.blocks[block]? = some finalBody ∧
      finalBody.params = witness.capturedBody.params ∧
      finalBody.insts.toList = witness.capturedBody.insts.toList ++
        (.eff (.replace owner value (some origin)) :: tail) := by
  have publish := witness.source.site.publishRun
  rw [emitEffect_run _ _ witness.current] at publish
  have publishedRow : witness.source.finished.blocks[block]? =
      some { witness.capturedBody with insts := witness.capturedBody.insts.push (.eff (.replace owner value (some origin))) } := by
    obtain ⟨_, stateEq⟩ := Prod.mk.inj publish
    rw [← stateEq, Array.getElem?_modify, witness.row]
    simp [witness.source.owner_eq, witness.source.value_eq]
  obtain ⟨finalBody, row, params, tail, append⟩ := witness.source.extension.2 block _ publishedRow
  exact ⟨finalBody, tail, row, params,
    by simpa [Array.toList_push, List.append_assoc] using append⟩

theorem AcceptedReplacementSite.captured_extension {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (witness : AcceptedReplacementSite le state owner value origin) :
    witness.site.captured.Ext state :=
  ((advB_emitEffect _ le witness.site.captured () witness.finished witness.site.publishRun).ext).trans witness.extension

theorem AcceptedReplacementSite.addressed_liveBound {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (witness : AcceptedReplacementSite le state owner value origin) : LiveBound witness.site.addressed :=
  (witness.generated.lowerPlace witness.place witness.site.addressRun).live

theorem AcceptedReplacementSite.cleared_generated {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (witness : AcceptedReplacementSite le state owner value origin) :
    GeneratedBuilderState witness.site.cleared :=
  (witness.generated.lowerPlace witness.place witness.site.addressRun).emitEffect _ witness.site.clearRun

theorem AcceptedReplacementSite.captured_generated {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (witness : AcceptedReplacementSite le state owner value origin) :
    GeneratedBuilderState witness.site.captured :=
  witness.cleared_generated.lowerExpr witness.rhs witness.site.rhsRun

def ReplacementLoopTargetsIncluded (loop : Option LoopCtx) (targets : List BlockId) : Prop :=
  ∀ target ∈ LoopBuilderFrameTargets loop, target ∈ targets

def ReplacementTargetsBound (targets : List BlockId) (state : LS) : Prop :=
  ∀ target ∈ targets, target < state.blocks.size

theorem ReplacementTargetsBound.mono {before after : LS}
    (bounded : ReplacementTargetsBound targets before) (extension : before.Ext after) :
    ReplacementTargetsBound targets after :=
  fun target member => Nat.lt_of_lt_of_le (bounded target member) extension.1

def ReplacementIntervalsPreserved (targets : List BlockId) (before after : LS) : Prop :=
  ∀ cleared captured, captured.Ext before → IntervalTargetsAvoid cleared captured targets →
    IntervalEdgesFramed cleared captured before → IntervalEdgesFramed cleared captured after

theorem ReplacementIntervalsPreserved.of_frames {before after : LS}
    (framed : TermEdgesFramed none before after) : ReplacementIntervalsPreserved targets before after := by
  intro cleared captured extension _ previous
  exact previous.after_frames extension framed (.nil _ _)

theorem ReplacementIntervalsPreserved.of_blocks {before after : LS}
    (same : after.blocks = before.blocks) : ReplacementIntervalsPreserved targets before after := by
  intro cleared captured _ _ previous
  exact previous.of_blocks same

theorem ReplacementIntervalsPreserved.of_run {action : B α} {le : LEnv}
    {before after : LS} {result : α} (frames : GeneratedTargetFrameRun none action)
    (run : action le before = (result, after)) : ReplacementIntervalsPreserved targets before after := by
  obtain ⟨framed, _⟩ := frames before le before result after (.refl _) trivial
    (TermEdgesFramed.refl none before) run
  exact .of_frames framed

theorem ReplacementIntervalsPreserved.emitTerm {le : LEnv} {before after : LS}
    {term : Term} {result : Unit} (run : Goose.Lower.emitTerm term le before = (result, after))
    (allowed : ∀ target ∈ term.successors, target ∈ targets ∨ before.blocks.size ≤ target) :
    ReplacementIntervalsPreserved targets before after := by
  intro cleared captured extension avoids framed
  apply framed.emitTermAt run
  intro target member
  rcases allowed target member with inherited | fresh
  · exact avoids target inherited
  · exact Or.inr (Nat.le_trans extension.1 fresh)

theorem ReplacementIntervalsPreserved.patchTerm {le : LEnv} {before after : LS}
    {term : Term} {block : BlockId} {result : Unit} (run : Goose.Lower.patchTerm block term le before = (result, after))
    (allowed : ∀ target ∈ term.successors, target ∈ targets ∨ before.blocks.size ≤ target) :
    ReplacementIntervalsPreserved targets before after := by
  intro cleared captured extension avoids framed
  apply framed.patchTermAt run
  intro target member
  rcases allowed target member with inherited | fresh
  · exact avoids target inherited
  · exact Or.inr (Nat.le_trans extension.1 fresh)

structure ReservedReplacementSiteAt (targets : List BlockId) (le : LEnv) (state : LS)
    (block position owner value : Nat) (origin : OriginId) where
  site : ReplacementSiteAt le state block position owner value origin
  avoids : IntervalTargetsAvoid site.source.site.cleared site.source.site.captured targets

def ReservedReplacementSiteAt.retained {le : LEnv} {before after : LS}
    {block position owner value : Nat} {origin : OriginId}
    (witness : ReservedReplacementSiteAt targets le before block position owner value origin)
    (extension : before.Ext after) (types : TypePrefix before after)
    (preserved : ReplacementIntervalsPreserved targets before after) :
    ReservedReplacementSiteAt targets le after block position owner value origin :=
  { site := witness.site.retained extension types
      (preserved _ _ witness.site.source.captured_extension witness.avoids witness.site.source.framed)
    avoids := witness.avoids }

def ReservedReplacementSiteAt.weaken {le : LEnv} {state : LS} {first second : List BlockId}
    {block position owner value : Nat} {origin : OriginId}
    (witness : ReservedReplacementSiteAt first le state block position owner value origin)
    (included : ∀ target ∈ second, target ∈ first) :
    ReservedReplacementSiteAt second le state block position owner value origin :=
  { witness with avoids := witness.avoids.mono included }

def ReservedReplacementSiteAt.reserve {le : LEnv} {state : LS}
    {block position owner value : Nat} {origin : OriginId}
    (witness : ReservedReplacementSiteAt targets le state block position owner value origin)
    (target : BlockId) (fresh : state.blocks.size ≤ target) :
    ReservedReplacementSiteAt (target :: targets) le state block position owner value origin :=
  { witness with avoids := witness.avoids.cons (Or.inr (Nat.le_trans witness.site.source.captured_extension.1 fresh)) }

def ReplacementSourceAuthority (le : LEnv) (state : LS) (block position : Nat) : Inst → Prop
  | .eff (.replace owner value (some origin)) => Nonempty (ReservedReplacementSiteAt targets le state block position owner value origin)
  | .eff (.replace _ _ none) => False
  | _ => True

def ReplacementSitesBuilder (le : LEnv) (state : LS) : Prop :=
  ∀ block body, state.blocks[block]? = some body → ∀ position instruction,
    body.insts[position]? = some instruction → ReplacementSourceAuthority (targets := targets) le state block position instruction

theorem ReplacementSourceAuthority.retained {le : LEnv} {before after : LS}
    {block position : Nat} {inst : Inst}
    (valid : ReplacementSourceAuthority (targets := targets) le before block position inst)
    (extension : before.Ext after) (types : TypePrefix before after)
    (preserved : ReplacementIntervalsPreserved targets before after) :
    ReplacementSourceAuthority (targets := targets) le after block position inst := by
  cases inst with
  | eff effect =>
    cases effect <;> try exact valid
    case replace owner value origin =>
      cases origin with
      | none => exact valid
      | some origin => obtain ⟨site⟩ := valid; exact ⟨site.retained extension types preserved⟩
  | _ => exact valid

theorem ReplacementSourceAuthority.weaken {le : LEnv} {state : LS} {first second : List BlockId}
    {block position : Nat} {inst : Inst}
    (valid : ReplacementSourceAuthority (targets := first) le state block position inst)
    (included : ∀ target ∈ second, target ∈ first) :
    ReplacementSourceAuthority (targets := second) le state block position inst := by
  cases inst with
  | eff effect =>
    cases effect <;> try exact valid
    case replace owner value origin =>
      cases origin with
      | none => exact valid
      | some origin => obtain ⟨site⟩ := valid; exact ⟨site.weaken included⟩
  | _ => exact valid

theorem ReplacementSitesBuilder.weaken {le : LEnv} {state : LS} {first second : List BlockId}
    (checked : ReplacementSitesBuilder (targets := first) le state)
    (included : ∀ target ∈ second, target ∈ first) :
    ReplacementSitesBuilder (targets := second) le state :=
  fun block body row position inst lookup => (checked block body row position inst lookup).weaken included

theorem ReplacementSitesBuilder.reserve {le : LEnv} {state : LS}
    (checked : ReplacementSitesBuilder (targets := targets) le state) (target : BlockId)
    (fresh : state.blocks.size ≤ target) : ReplacementSitesBuilder (targets := target :: targets) le state := by
  intro block body row position inst lookup
  have valid := checked block body row position inst lookup
  cases inst with
  | eff effect =>
    cases effect <;> try exact valid
    case replace owner value origin =>
      cases origin with
      | none => exact valid
      | some origin => obtain ⟨site⟩ := valid; exact ⟨site.reserve target fresh⟩
  | _ => exact valid

theorem ReplacementSitesBuilder.reserveMany {le : LEnv} {state : LS}
    (checked : ReplacementSitesBuilder (targets := targets) le state) (extra : List BlockId)
    (fresh : ∀ target ∈ extra, state.blocks.size ≤ target) :
    ReplacementSitesBuilder (targets := extra ++ targets) le state := by
  induction extra with
  | nil => exact checked
  | cons target rest ih =>
    exact (ih (fun next member => fresh next (List.mem_cons_of_mem target member))).reserve target
      (fresh target (by simp))

end Goose.Lower.Validation
