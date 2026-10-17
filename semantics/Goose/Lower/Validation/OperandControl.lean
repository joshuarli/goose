import Goose.Lower.Validation.OperandStatements

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem operands_whenLive (fallback : α) {action : BlockId → B α}
    (children : ∀ block, OperandRun (action block)) : OperandRun (whenLive fallback action) := by
  intro le before result after run checked
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [whenLive_some _ _ le current] at run
    exact children block _ _ _ _ run checked

theorem operands_patchBrs0 (target : BlockId) : ∀ incoming, OperandRun (patchBrs0 target incoming)
  | [] => OperandRun.pure _
  | block :: rest => by
    apply OperandRun.bind (action := patchTerm block (.br target []))
    · intro le before result after run checked
      exact operands_patchTerm run checked (by simp [Term.uses])
    · intro _; exact operands_patchBrs0 target rest

theorem operands_joinArms (trueEnd falseEnd : Option BlockId) :
    OperandRun (joinArms trueEnd falseEnd) := by
  unfold joinArms
  cases trueEnd <;> cases falseEnd
  · exact operands_setCur _
  all_goals
    exact OperandRun.bind (operands_newBlock _) fun ⟨_, _⟩ =>
      OperandRun.bind (operands_patchBrs0 _ _) fun _ => operands_setCur _

theorem operands_loopBody {condition : ValueId} {body : Nat → BlockId → B ValueId} {back : B Unit}
    {le before result after} (run : loopBody condition body back le before = (result, after))
    (checked : OperandBounds before)
    (conditionBound : before.cur.isSome = true → condition < before.vals.size)
    (bodyRun : ∀ depth exit start value finish, body depth exit le start = (value, finish) →
      OperandBounds start → before.vals.size ≤ start.vals.size → OperandBounds finish)
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (backRun : ∀ start value finish, back le start = (value, finish) →
      OperandBounds start → before.vals.size ≤ start.vals.size → OperandBounds finish) :
    OperandBounds after := by
  obtain ⟨state, saved, save, ⟨entry, exit⟩, forked, forkRun, _, selected, select,
    value, executed, execute, _, backed, backRunActual, resume⟩ :=
    (by simpa only [loopBody, bind_eq] using run)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj save
  have forkedBounds := operands_fork forkRun checked conditionBound
  have selectedBounds := operands_setCur _ _ _ _ _ select forkedBounds
  have forkGrowth := (advB_fork condition _ _ _ _ forkRun).vals
  have selectedGrowth : before.vals.size ≤ selected.vals.size := by
    rw [setCur_run] at select
    obtain ⟨_, rfl⟩ := Prod.mk.inj select
    exact forkGrowth
  have executedBounds := bodyRun _ _ _ _ _ execute selectedBounds selectedGrowth
  have executedGrowth := Nat.le_trans selectedGrowth ((bodyAdvance _ _ _ _ _ _ execute).vals)
  have backedBounds := backRun _ _ _ backRunActual executedBounds executedGrowth
  exact operands_setCur _ _ _ _ _ resume backedBounds

def OperandBlock (context : Option LoopCtx) (body : Core.Block) : Prop :=
  ∀ pre want le before result after,
    lowerBlock context pre want body le before = (result, after) →
      OperandBounds before → LoopOperandBounds context before → PreOperandBounds pre before →
        OperandBounds after

theorem operands_lowerWhile (header : BlockId) (condition : Expr) {body : Nat → BlockId → B ValueId}
    (conditionRun : OperandRun (lowerExpr condition))
    (children : ∀ depth exit, OperandRun (body depth exit))
    (advances : ∀ depth exit, AdvB (body depth exit)) :
    OperandRun (lowerWhile header (lowerExpr condition) body) := by
  intro le before result after run checked
  obtain ⟨cv, tested, testRun, remaining⟩ := bind_eq.mp run
  have testedBounds := conditionRun _ _ _ _ testRun checked
  cases current : tested.cur with
  | none =>
    rw [whenLive_none _ _ le current] at remaining
    obtain ⟨_, rfl⟩ := Prod.mk.inj remaining
    exact testedBounds
  | some block =>
    rw [whenLive_some _ _ le current] at remaining
    exact operands_loopBody remaining testedBounds (value_lowerExpr condition _ _ _ _ testRun)
      (by intro depth exit start value finish bodyRun bounds _; exact children depth exit _ _ _ _ bodyRun bounds)
      advances
      (by
        intro start value finish backRun bounds _
        exact operands_emitTerm backRun bounds (by simp [Term.uses]))

theorem operands_lowerStmt_while (context : Option LoopCtx) (condition : Expr) (body : Core.Block)
    (origin : OriginId) (conditionRun : OperandRun (lowerExpr condition))
    (bodyRun : ∀ depth exit header, OperandBlock (some ⟨depth, exit, .jump header⟩) body) :
    OperandRun (lowerStmt context (.while condition body origin)) := by
  simp only [lowerStmt]
  apply OperandRun.bind (operands_newBlock _)
  intro ⟨header, _⟩
  apply OperandRun.bind (action := emitTerm (.br header []))
  · intro le before result after run checked
    exact operands_emitTerm run checked (by simp [Term.uses])
  · intro _
    exact OperandRun.bind (operands_setCur _) fun _ =>
      operands_lowerWhile _ _ conditionRun
        (fun depth exit le before result after run checked =>
          bodyRun depth exit header [] false le before result after run checked trivial (by simp [PreOperandBounds]))
        (fun _ _ => advB_lowerBlock _ _ _ _)

theorem operands_rangeBack {ty : IntTy} {counter : ValueId} {header : BlockId}
    {le before result after} (run : rangeBack ty counter header le before = (result, after))
    (checked : OperandBounds before) (bounded : counter < before.vals.size) : OperandBounds after := by
  unfold rangeBack at run
  simp only [bind_run, isLive, curBlock_run, pure_run] at run
  cases live : before.cur.isSome
  · simp only [live, Bool.false_eq_true, ↓reduceIte] at run
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact checked
  · simp only [live, ↓reduceIte] at run
    obtain ⟨next, emitted, emission, term⟩ := bind_eq.mp run
    exact operands_emitTerm term
      (operands_emitDef emission checked (by simpa [Op.uses] using (fun _ => bounded)))
      (by simpa [Term.uses] using value_emitDef _ _ _ _ _ emission)

theorem operands_lowerRange {ty : IntTy} {counter bound : ValueId} {header : BlockId}
    {body : Nat → BlockId → B ValueId} {le before result after}
    (run : lowerRange ty counter bound header body le before = (result, after))
    (checked : OperandBounds before) (counterBound : counter < before.vals.size)
    (boundBound : bound < before.vals.size)
    (bodyRun : ∀ depth exit start value finish, body depth exit le start = (value, finish) →
      OperandBounds start → before.vals.size ≤ start.vals.size → OperandBounds finish)
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit)) : OperandBounds after := by
  obtain ⟨cv, tested, testRun, remaining⟩ := bind_eq.mp run
  have testedBounds := operands_emitDef testRun checked (by
    intro _ value member
    have either : value = counter ∨ value = bound := by simpa [Op.uses] using member
    rcases either with rfl | rfl
    · exact counterBound
    · exact boundBound)
  have growth := (advB_emitDef _ _ _ _ _ testRun).vals
  apply operands_loopBody remaining testedBounds (value_emitDef _ _ _ _ _ testRun)
  · intro depth exit start value finish bodyActual bounds grows
    exact bodyRun depth exit start value finish bodyActual bounds (Nat.le_trans growth grows)
  · exact bodyAdvance
  · intro start value finish backRun bounds grows
    exact operands_rangeBack backRun bounds (Nat.lt_of_lt_of_le counterBound (Nat.le_trans growth grows))

theorem newBlock1_value_bound {ty : VTy} {le before block params after}
    (run : newBlock [ty] le before = ((block, params), after)) : params.headD 0 < after.vals.size := by
  rw [newBlock1_run] at run
  obtain ⟨pair, rfl⟩ := Prod.mk.inj run
  obtain ⟨_, rfl⟩ := Prod.mk.inj pair
  simp

theorem operands_lowerStmt_forRange (context : Option LoopCtx) (slot : VarId) (lo hi : Expr)
    (body : Core.Block) (origin : OriginId)
    (lowRun : OperandRun (lowerExpr lo)) (highRun : OperandRun (lowerExpr hi))
    (bodyRun : ∀ depth exit header ty counter,
      OperandBlock (some ⟨depth, exit, .next header ty counter⟩) body) :
    OperandRun (lowerStmt context (.forRange slot lo hi body origin)) := by
  intro le before result after run checked
  obtain ⟨a, lowed, lowRunActual, b, highed, highRunActual, remaining⟩ :=
    (by simpa only [lowerStmt, bind_eq] using run)
  have highBounds := highRun _ _ _ _ highRunActual (lowRun _ _ _ _ lowRunActual checked)
  cases current : highed.cur with
  | none =>
    rw [whenLive_none _ _ le current] at remaining
    obtain ⟨_, rfl⟩ := Prod.mk.inj remaining
    exact highBounds
  | some block =>
    rw [whenLive_some _ _ le current] at remaining
    obtain ⟨ty, inspected, inspection, ⟨header, params⟩, allocated, allocation,
      _, closed, close, _, selected, select, rangeRun⟩ :=
      (by simpa only [bind_eq] using remaining)
    have same : inspected = highed := by
      have equality := intTyOf_state a le highed
      rw [inspection] at equality
      exact equality
    subst inspected
    have allocatedBounds := operands_newBlock _ _ _ _ _ allocation highBounds
    have aBound := live_value_through (advB_lowerExpr hi) (dead_lowerExpr hi) highRunActual
      (value_lowerExpr lo _ _ _ _ lowRunActual)
    have closedBounds := operands_emitTerm close allocatedBounds (by
      intro live value member
      have equality : value = a := by simpa [Term.uses] using member
      subst value
      have growth := (adv_newBlock1 allocation).vals
      rw [newBlock1_run] at allocation
      obtain ⟨_, rfl⟩ := Prod.mk.inj allocation
      exact Nat.lt_of_lt_of_le (aBound live) growth)
    have selectedBounds := operands_setCur _ _ _ _ _ select closedBounds
    have counterBound := newBlock1_value_bound allocation
    have afterClose := (advB_emitTerm _ _ _ _ _ close).vals
    have bBound := Nat.lt_of_lt_of_le
      (value_lowerExpr hi _ _ _ _ highRunActual (by simp [current]))
      (adv_newBlock1 allocation).vals
    rw [setCur_run] at select
    obtain ⟨_, rfl⟩ := Prod.mk.inj select
    have counterAtHeader := Nat.lt_of_lt_of_le counterBound afterClose
    apply operands_lowerRange rangeRun selectedBounds counterAtHeader
      (Nat.lt_of_lt_of_le bBound afterClose)
    · intro depth exit start value finish actual bounds growth
      have counterAtBody := Nat.lt_of_lt_of_le counterAtHeader growth
      exact bodyRun depth exit header ty (params.headD 0) _ _ _ _ _ _ actual bounds
        counterAtBody (by simpa [PreOperandBounds] using counterAtBody)
    · intro depth exit
      exact advB_lowerBlock _ _ _ _

theorem operands_lowerStmt_ifS (context : Option LoopCtx) (condition : Expr)
    (trueArm : Core.Block) (falseArm : Option Core.Block) (origin : OriginId)
    (conditionRun : OperandRun (lowerExpr condition)) (trueRun : OperandBlock context trueArm)
    (falseRun : ∀ body, falseArm = some body → OperandBlock context body)
    {le before result after} (run : lowerStmt context (.ifS condition trueArm falseArm origin) le before = (result, after))
    (checked : OperandBounds before) (counter : LoopOperandBounds context before) : OperandBounds after := by
  cases falseArm with
  | none =>
    obtain ⟨cv, tested, testRun, remaining⟩ := bind_eq.mp run
    have testedBounds := conditionRun _ _ _ _ testRun checked
    have testedCounter := counter.mono (advB_lowerExpr condition _ _ _ _ testRun).vals
    cases current : tested.cur with
    | none =>
      rw [whenLive_none _ _ le current] at remaining
      obtain ⟨_, rfl⟩ := Prod.mk.inj remaining
      exact testedBounds
    | some block =>
      rw [whenLive_some _ _ le current] at remaining
      obtain ⟨⟨left, join⟩, forked, forkRun, _, selected, select,
        value, executed, execute, _, closed, close, resume⟩ :=
        (by simpa only [bind_eq] using remaining)
      have forkedBounds := operands_fork forkRun testedBounds (value_lowerExpr condition _ _ _ _ testRun)
      have selectedBounds := operands_setCur _ _ _ _ _ select forkedBounds
      have forkedCounter := testedCounter.mono (advB_fork _ _ _ _ _ forkRun).vals
      have selectedCounter : LoopOperandBounds context selected := by
        rw [setCur_run] at select
        obtain ⟨_, rfl⟩ := Prod.mk.inj select
        exact forkedCounter
      have executedBounds := trueRun [] false _ _ _ _ execute selectedBounds selectedCounter (by simp [PreOperandBounds])
      have closedBounds := operands_emitTerm close executedBounds (by simp [Term.uses])
      exact operands_setCur _ _ _ _ _ resume closedBounds
  | some falseBody =>
    obtain ⟨cv, tested, testRun, remaining⟩ := bind_eq.mp run
    have testedBounds := conditionRun _ _ _ _ testRun checked
    have testedCounter := counter.mono (advB_lowerExpr condition _ _ _ _ testRun).vals
    cases current : tested.cur with
    | none =>
      rw [whenLive_none _ _ le current] at remaining
      obtain ⟨_, rfl⟩ := Prod.mk.inj remaining
      exact testedBounds
    | some block =>
      rw [whenLive_some _ _ le current] at remaining
      obtain ⟨⟨left, right⟩, forked, forkRun, _, selectedT, selectT,
        valueT, executedT, executeT, endT, savedT, saveT, _, selectedF, selectF,
        valueF, executedF, executeF, endF, savedF, saveF, joinRun⟩ :=
        (by simpa only [bind_eq] using remaining)
      have forkedBounds := operands_fork forkRun testedBounds (value_lowerExpr condition _ _ _ _ testRun)
      have selectedTBounds := operands_setCur _ _ _ _ _ selectT forkedBounds
      have forkedCounter := testedCounter.mono (advB_fork _ _ _ _ _ forkRun).vals
      have selectedTCounter : LoopOperandBounds context selectedT := by
        rw [setCur_run] at selectT
        obtain ⟨_, rfl⟩ := Prod.mk.inj selectT
        exact forkedCounter
      have executedTBounds := trueRun [] false _ _ _ _ executeT selectedTBounds selectedTCounter (by simp [PreOperandBounds])
      have executedTCounter := selectedTCounter.mono (advB_lowerBlock _ _ _ _ _ _ _ _ executeT).vals
      rw [curBlock_run] at saveT saveF
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj saveT
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj saveF
      have selectedFBounds := operands_setCur _ _ _ _ _ selectF executedTBounds
      have selectedFCounter : LoopOperandBounds context selectedF := by
        rw [setCur_run] at selectF
        obtain ⟨_, rfl⟩ := Prod.mk.inj selectF
        exact executedTCounter
      have executedFBounds := falseRun falseBody rfl [] false _ _ _ _ executeF selectedFBounds selectedFCounter (by simp [PreOperandBounds])
      exact operands_joinArms _ _ _ _ _ _ joinRun executedFBounds

theorem operands_lowerStmt_assert (context : Option LoopCtx) (condition : Expr) (origin : OriginId)
    (child : OperandRun (lowerExpr condition)) : OperandRun (lowerStmt context (.assertS condition origin)) := by
  intro le before result after run checked
  obtain ⟨cv, tested, testRun, remaining⟩ := bind_eq.mp run
  have testedBounds := child _ _ _ _ testRun checked
  cases current : tested.cur with
  | none =>
    rw [whenLive_none _ _ le current] at remaining
    obtain ⟨_, rfl⟩ := Prod.mk.inj remaining
    exact testedBounds
  | some block =>
    rw [whenLive_some _ _ le current] at remaining
    obtain ⟨⟨pass, fail⟩, forked, forkRun, _, selected, select,
      _, closed, close, resume⟩ := (by simpa only [bind_eq] using remaining)
    have forkedBounds := operands_fork forkRun testedBounds (value_lowerExpr condition _ _ _ _ testRun)
    have selectedBounds := operands_setCur _ _ _ _ _ select forkedBounds
    have closedBounds := operands_emitTerm close selectedBounds (by simp [Term.uses])
    exact operands_setCur _ _ _ _ _ resume closedBounds

theorem eachElemValue_cases {slot : VarId} {byRef : Bool} {input : ValueId} {le before result after}
    (run : eachElemValue slot byRef input le before = (result, after)) :
    (result = input ∧ after = before) ∨
      (∃ mu, freezeTo mu input le before = (result, after)) ∨
      emitDef (.load input) le before = (result, after) := by
  unfold eachElemValue at run
  cases byRef
  · exact Or.inr (Or.inr run)
  · simp only [↓reduceIte, bind_run, read_apply] at run
    cases lookup : le.vars[slot]? with
    | none =>
      simp only [lookup] at run
      exact Or.inl ⟨(pure_eq.mp run).1.symm, (pure_eq.mp run).2.symm⟩
    | some var =>
      simp only [lookup] at run
      cases ty : var.ty <;> simp only [ty] at run <;>
        first
        | exact Or.inl ⟨(pure_eq.mp run).1.symm, (pure_eq.mp run).2.symm⟩
        | exact Or.inr (Or.inl ⟨_, run⟩)

theorem operands_eachElemValue {slot : VarId} {byRef : Bool} {input : ValueId} {le before result after}
    (run : eachElemValue slot byRef input le before = (result, after)) (checked : OperandBounds before)
    (bounded : before.cur.isSome = true → input < before.vals.size) : OperandBounds after := by
  rcases eachElemValue_cases run with ⟨rfl, rfl⟩ | ⟨mu, freeze⟩ | load
  · exact checked
  · exact operands_freezeTo freeze checked bounded
  · exact operands_emitDef load checked (by simpa [Op.uses] using bounded)

theorem value_eachElemValue {slot : VarId} {byRef : Bool} {input : ValueId} {le before result after}
    (run : eachElemValue slot byRef input le before = (result, after))
    (bounded : before.cur.isSome = true → input < before.vals.size)
    (live : after.cur.isSome = true) : result < after.vals.size := by
  rcases eachElemValue_cases run with ⟨rfl, rfl⟩ | ⟨mu, freeze⟩ | load
  · exact bounded live
  · rcases freezeTo_cases freeze with ⟨rfl, rfl⟩ | fresh
    · exact bounded live
    · exact value_emitDef _ _ _ _ _ fresh live
  · exact value_emitDef _ _ _ _ _ load live

theorem operands_eachLen {regrow : Bool} {owner : Option ValueId} {sampled : ValueId}
    {le before result after} (run : eachLen regrow owner sampled le before = (result, after))
    (checked : OperandBounds before)
    (ownerBound : regrow = true → owner.getD 0 < before.vals.size) : OperandBounds after := by
  cases regrow
  · obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact checked
  · exact operands_emitDef run checked (by simpa [Op.uses] using (fun _ => ownerBound rfl))

theorem value_eachLen {regrow : Bool} {owner : Option ValueId} {sampled : ValueId}
    {le before result after} (run : eachLen regrow owner sampled le before = (result, after))
    (sampleBound : regrow = false → sampled < before.vals.size)
    (live : after.cur.isSome = true) : result < after.vals.size := by
  cases regrow
  · obtain ⟨rfl, rfl⟩ := pure_eq.mp run
    exact sampleBound rfl
  · exact value_emitDef _ _ _ _ _ run live

theorem operands_lowerEach {regrow : Bool} {owner : Option ValueId} {sampled : ValueId}
    {header : BlockId} {counter : ValueId} {body : Nat → BlockId → B ValueId}
    {le before result after} (run : lowerEach regrow owner sampled header counter body le before = (result, after))
    (checked : OperandBounds before) (counterBound : counter < before.vals.size)
    (ownerBound : regrow = true → owner.getD 0 < before.vals.size)
    (sampleBound : regrow = false → sampled < before.vals.size)
    (bodyRun : ∀ depth exit start value finish, body depth exit le start = (value, finish) →
      OperandBounds start → before.vals.size ≤ start.vals.size → OperandBounds finish)
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit)) : OperandBounds after := by
  obtain ⟨length, measured, measure, cv, tested, testRun, remaining⟩ :=
    (by simpa only [lowerEach, bind_eq] using run)
  have measuredBounds := operands_eachLen measure checked ownerBound
  have measureGrowth := (advB_eachLen regrow owner sampled _ _ _ _ measure).vals
  have testedBounds := operands_emitDef testRun measuredBounds (by
    intro live value member
    have either : value = counter ∨ value = length := by simpa [Op.uses] using member
    rcases either with rfl | rfl
    · exact Nat.lt_of_lt_of_le counterBound measureGrowth
    · exact value_eachLen measure sampleBound live)
  have growth := Nat.le_trans measureGrowth (advB_emitDef _ _ _ _ _ testRun).vals
  apply operands_loopBody remaining testedBounds (value_emitDef _ _ _ _ _ testRun)
  · intro depth exit start value finish bodyActual bounds grows
    exact bodyRun depth exit start value finish bodyActual bounds (Nat.le_trans growth grows)
  · exact bodyAdvance
  · intro start value finish backRun bounds grows
    exact operands_rangeBack backRun bounds (Nat.lt_of_lt_of_le counterBound (Nat.le_trans growth grows))

end Goose.Lower.Validation
