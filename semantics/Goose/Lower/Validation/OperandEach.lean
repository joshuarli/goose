import Goose.Lower.Validation.OperandControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def EachSourceBounds (source : Option ValueId × ValueId) (state : LS) : Prop :=
  source.2 < state.vals.size ∧ ∀ owner ∈ source.1.toList, owner < state.vals.size

theorem operands_lowerEachSource (view : View)
    (child : match view with
      | .of place => OperandRun (lowerPlace place)
      | .val expr => OperandRun (lowerExpr expr)) :
    OperandRun (lowerEachSource view) ∧
      (∀ le before result after, lowerEachSource view le before = (result, after) →
        after.cur.isSome = true → EachSourceBounds result after) := by
  cases view with
  | of place =>
    constructor
    · intro le before result after run checked
      obtain ⟨owner, addressed, placeRun, value, emitted, emission, remaining⟩ :=
        (by simpa only [lowerEachSource, bind_eq] using run)
      obtain ⟨_, rfl⟩ := pure_eq.mp remaining
      exact operands_emitDef emission (child _ _ _ _ placeRun checked)
        (by simpa [Op.uses] using value_lowerPlace place _ _ _ _ placeRun)
    · intro le before result after run live
      obtain ⟨owner, addressed, placeRun, value, emitted, emission, remaining⟩ :=
        (by simpa only [lowerEachSource, bind_eq] using run)
      obtain ⟨rfl, rfl⟩ := pure_eq.mp remaining
      exact ⟨value_emitDef _ _ _ _ _ emission live, by
        intro candidate member
        have equal : candidate = owner := by simpa using member
        subst candidate
        exact live_value_through (advB_emitDef _) (dead_emitDef _) emission
          (value_lowerPlace place _ _ _ _ placeRun) live⟩
  | val expr =>
    constructor
    · intro le before result after run checked
      obtain ⟨input, evaluated, exprRun, value, emitted, emission, remaining⟩ :=
        (by simpa only [lowerEachSource, bind_eq] using run)
      obtain ⟨_, rfl⟩ := pure_eq.mp remaining
      exact operands_emitDef emission (child _ _ _ _ exprRun checked)
        (by simpa [Op.uses] using value_lowerExpr expr _ _ _ _ exprRun)
    · intro le before result after run live
      obtain ⟨input, evaluated, exprRun, value, emitted, emission, remaining⟩ :=
        (by simpa only [lowerEachSource, bind_eq] using run)
      obtain ⟨rfl, rfl⟩ := pure_eq.mp remaining
      exact ⟨value_emitDef _ _ _ _ _ emission live, by simp⟩

theorem regrowOf_state (owner : Option ValueId) (le : LEnv) (before : LS) :
    (regrowOf owner le before).2 = before := by
  cases owner with
  | none => rfl
  | some value =>
    simp only [regrowOf, growOwner, bind_run, valTy_run]
    cases valueType : (valTy value le before).1 with
    | view _ _ => rfl
    | data source => cases source <;> rfl

theorem regrowOf_owner {owner : Option ValueId} {le before result after}
    (run : regrowOf owner le before = (result, after)) (regrows : result = true) : owner.isSome = true := by
  cases owner with
  | none =>
    obtain ⟨rfl, _⟩ := pure_eq.mp run
    contradiction
  | some value => rfl

theorem operands_regrowOf (owner : Option ValueId) : OperandRun (regrowOf owner) := by
  apply OperandRun.of_unchanged
  · intro le state; rw [regrowOf_state]
  · intro le state; rw [regrowOf_state]; exact Nat.le_refl _

theorem dead_regrowOf (owner : Option ValueId) : DeadRun (regrowOf owner) :=
  DeadRun.of_cur_unchanged (by intro le state; rw [regrowOf_state])

theorem operands_eachSampled {regrow : Bool} {view : ValueId} {le before result after}
    (run : eachSampled regrow view le before = (result, after)) (checked : OperandBounds before)
    (bounded : before.cur.isSome = true → view < before.vals.size) : OperandBounds after := by
  cases regrow
  · exact operands_emitDef run checked (by simpa [Op.uses] using bounded)
  · obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact checked

theorem value_eachSampled {regrow : Bool} {view : ValueId} {le before result after}
    (run : eachSampled regrow view le before = (result, after)) (sampled : regrow = false)
    (live : after.cur.isSome = true) : result < after.vals.size := by
  subst regrow
  exact value_emitDef _ _ _ _ _ run live

theorem dead_eachSampled (regrow : Bool) (view : ValueId) : DeadRun (eachSampled regrow view) := by
  cases regrow
  · exact dead_emitDef _
  · exact DeadRun.pure _

theorem value_emitDef_of_nonempty {op : Op} {le before result after}
    (run : emitDef op le before = (result, after)) (nonempty : 0 < before.vals.size) :
    result < after.vals.size := by
  cases current : before.cur with
  | none =>
    rw [emitDef_none _ _ current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact nonempty
  | some block =>
    rw [emitDef_run _ _ current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    simp

theorem value_eachElemValue_of_bounded {slot : VarId} {byRef : Bool} {input : ValueId}
    {le before result after} (run : eachElemValue slot byRef input le before = (result, after))
    (bounded : input < before.vals.size) : result < after.vals.size := by
  have nonempty : 0 < before.vals.size := Nat.lt_of_le_of_lt (Nat.zero_le input) bounded
  rcases eachElemValue_cases run with ⟨rfl, rfl⟩ | ⟨mu, freeze⟩ | load
  · exact bounded
  · rcases borrowTo_cases freeze with frozen | borrowed
    · rcases freezeTo_cases frozen with ⟨rfl, rfl⟩ | fresh
      · exact bounded
      · exact value_emitDef_of_nonempty fresh nonempty
    · exact value_emitDef_of_nonempty borrowed nonempty
  · exact value_emitDef_of_nonempty load nonempty

theorem operands_eachBody (slot : VarId) (index : Option VarId) (view counter : ValueId)
    (byRef : Bool) (depth : Nat) (exit header : BlockId) (body : Core.Block) (origin : OriginId)
    (child : OperandBlock (some ⟨depth, exit, .next header .i64 counter⟩) body)
    {le : LEnv} {before after : LS} {result : ValueId}
    (run : (do
      let elem ← emitDef (.refElem view counter)
      let value ← eachElemValue slot byRef elem
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
        ((slot, value, origin) :: (match index with | some other => [(other, counter, origin)] | none => [])) false body)
      le before = (result, after))
    (checked : OperandBounds before) (viewBound : view < before.vals.size)
    (counterBound : counter < before.vals.size) : OperandBounds after := by
  obtain ⟨elem, addressed, address, value, evaluated, evaluate, remaining⟩ :=
    (by simpa only [bind_eq] using run)
  have addressedBounds := operands_emitDef address checked (by
    intro _ used member
    have either : used = view ∨ used = counter := by simpa [Op.uses] using member
    rcases either with rfl | rfl
    · exact viewBound
    · exact counterBound)
  have elemBound := value_emitDef_of_nonempty address
    (Nat.lt_of_le_of_lt (Nat.zero_le counter) counterBound)
  have evaluatedBounds := operands_eachElemValue evaluate addressedBounds (fun _ => elemBound)
  have valueBound := value_eachElemValue_of_bounded evaluate elemBound
  have counterGrowth := Nat.le_trans (advB_emitDef _ _ _ _ _ address).vals
    (advB_eachElemValue _ _ _ _ _ _ _ evaluate).vals
  have counterAtBody := Nat.lt_of_lt_of_le counterBound counterGrowth
  apply child _ false _ _ _ _ remaining evaluatedBounds counterAtBody
  intro binding member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact valueBound
  · cases index with
    | none => simp at member
    | some other =>
      have equal : binding = (other, counter, origin) := by simpa using member
      subst binding
      exact counterAtBody

theorem operands_lowerStmt_forEach (context : Option LoopCtx) (slot : VarId) (index : Option VarId)
    (view : View) (byRef : Bool) (body : Core.Block) (origin : OriginId)
    (sourceRun : match view with
      | .of place => OperandRun (lowerPlace place)
      | .val expr => OperandRun (lowerExpr expr))
    (bodyRun : ∀ depth exit header counter,
      OperandBlock (some ⟨depth, exit, .next header .i64 counter⟩) body) :
    OperandRun (lowerStmt context (.forEach slot index view byRef body origin)) := by
  intro le before result after run checked
  obtain ⟨⟨owner, sampledView⟩, sourced, source, regrow, classified, classify,
    sampled, measured, measure, startAt, started, start, remaining⟩ :=
    (by simpa only [lowerStmt, bind_eq] using run)
  have sourceFacts := operands_lowerEachSource view sourceRun
  have sourcedBounds := sourceFacts.1 _ _ _ _ source checked
  have unchanged := regrowOf_state owner le sourced
  rw [classify] at unchanged
  simp only at unchanged
  subst classified
  have measuredBounds := operands_eachSampled measure sourcedBounds
    (fun live => (sourceFacts.2 _ _ _ _ source live).1)
  have startedBounds := operands_emitDef start measuredBounds (by simp [Op.uses])
  cases current : started.cur with
  | none =>
    rw [whenLive_none _ _ le current] at remaining
    obtain ⟨_, rfl⟩ := Prod.mk.inj remaining
    exact startedBounds
  | some block =>
    rw [whenLive_some _ _ le current] at remaining
    have live : started.cur.isSome = true := by simp [current]
    have measuredLive := live_before (dead_emitDef _) start live
    have sourcedLive := live_before (dead_eachSampled regrow sampledView) measure measuredLive
    have sourceBounds := sourceFacts.2 _ _ _ _ source sourcedLive
    have sourceGrowth := Nat.le_trans (advB_eachSampled _ _ _ _ _ _ measure).vals
      (advB_emitDef _ _ _ _ _ start).vals
    have viewBound := Nat.lt_of_lt_of_le sourceBounds.1 sourceGrowth
    have ownerBound : regrow = true → owner.getD 0 < started.vals.size := by
      intro regrows
      have present := regrowOf_owner classify regrows
      cases owner with
      | none => contradiction
      | some owner =>
        exact Nat.lt_of_lt_of_le (sourceBounds.2 owner (by simp)) sourceGrowth
    have sampleBound : regrow = false → sampled < started.vals.size := by
      intro samples
      exact Nat.lt_of_lt_of_le (value_eachSampled measure samples measuredLive)
        (advB_emitDef _ _ _ _ _ start).vals
    obtain ⟨⟨header, params⟩, allocated, allocation, _, closed, close,
      _, selected, select, eachRun⟩ := (by simpa only [bind_eq] using remaining)
    have allocatedBounds := operands_newBlock _ _ _ _ _ allocation startedBounds
    have allocationGrowth := (adv_newBlock1 allocation).vals
    have closedBounds := operands_emitTerm close allocatedBounds (by
      intro liveAllocated used member
      have equal : used = startAt := by simpa [Term.uses] using member
      subst used
      exact Nat.lt_of_lt_of_le (value_emitDef _ _ _ _ _ start live) allocationGrowth)
    have selectedBounds := operands_setCur _ _ _ _ _ select closedBounds
    have counterBound := Nat.lt_of_lt_of_le (newBlock1_value_bound allocation)
      (advB_emitTerm _ _ _ _ _ close).vals
    have headerGrowth := Nat.le_trans allocationGrowth (advB_emitTerm _ _ _ _ _ close).vals
    rw [setCur_run] at select
    obtain ⟨_, rfl⟩ := Prod.mk.inj select
    apply operands_lowerEach eachRun selectedBounds counterBound
      (fun regrows => Nat.lt_of_lt_of_le (ownerBound regrows) headerGrowth)
      (fun samples => Nat.lt_of_lt_of_le (sampleBound samples) headerGrowth)
    · intro depth exit bodyStart value finish actual bounds growth
      exact operands_eachBody slot index sampledView (params.headD 0) byRef depth exit header body origin
        (bodyRun depth exit header (params.headD 0)) actual bounds
        (Nat.lt_of_lt_of_le viewBound (Nat.le_trans headerGrowth growth))
        (Nat.lt_of_lt_of_le counterBound growth)
    · intro depth exit
      exact AdvB.bind (advB_emitDef _) fun elem =>
        AdvB.bind (advB_eachElemValue _ _ _) fun value => advB_lowerBlock _ _ _ _

end Goose.Lower.Validation
