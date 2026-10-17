import Goose.Lower.Validation.SourceReplacementWriterLedgerChildSpansBlocks
import Goose.Lower.Validation.CfgFrontier

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.GIR

def ChildrenLiveBound : List Child → Prop
  | [] => True
  | none :: rest => ChildrenLiveBound rest
  | some (_, before) :: rest => LiveBound before ∧ ChildrenLiveBound rest

theorem ChildrenLiveBound.append {left right : List Child}
    (first : ChildrenLiveBound left) (second : ChildrenLiveBound right) : ChildrenLiveBound (left ++ right) := by
  induction left with
  | nil => exact second
  | cons entry rest ih =>
    cases entry with
    | none => exact ih first
    | some pair => exact ⟨first.1, ih first.2⟩

theorem ChildrenLiveBound.member {children : List Child} (bounded : ChildrenLiveBound children)
    {child : Fragment} {before : LS} (member : some (child, before) ∈ children) : LiveBound before := by
  induction children with
  | nil => simp at member
  | cons entry rest ih =>
    cases entry with
    | none => exact ih bounded (by simpa using member)
    | some pair =>
      rcases List.mem_cons.mp member with same | member
      · cases Option.some.inj same
        exact bounded.1
      · exact ih bounded.2 member

theorem expressionChildren_liveBound (env : LEnv) (expressions : List Expr) (before : LS)
    (bounded : LiveBound before) : ChildrenLiveBound (expressionChildren env expressions before) := by
  induction expressions generalizing before with
  | nil => trivial
  | cons expression rest ih => exact ⟨bounded, ih _ (liveBound_lowerExpr expression env before bounded)⟩

theorem argumentChildren_liveBound (env : LEnv) (arguments : List Arg) (before : LS)
    (bounded : LiveBound before) : ChildrenLiveBound (argumentChildren env arguments before) := by
  induction arguments generalizing before with
  | nil => trivial
  | cons argument rest ih =>
    cases argument <;> exact ⟨bounded, ih _ (liveBound_of_advB (advB_lowerArg _) env before bounded)⟩

theorem printChildren_liveBound (env : LEnv) (arguments : List PrintArg) (before : LS)
    (bounded : LiveBound before) : ChildrenLiveBound (printChildren env arguments before) := by
  induction arguments generalizing before with
  | nil => trivial
  | cons argument rest ih =>
    cases argument with
    | text text => exact ih _ bounded
    | expr expression => exact ⟨bounded, ih _ (liveBound_lowerExpr expression env before bounded)⟩

theorem statementChildren_liveBound (env : LEnv) (loop : Option LoopCtx) (statements : List Stmt) (before : LS)
    (bounded : LiveBound before) : ChildrenLiveBound (statementChildren env loop statements before) := by
  induction statements generalizing before with
  | nil => trivial
  | cons statement rest ih =>
    simp only [statementChildren]
    split
    · exact ⟨bounded, ih _ (liveBound_lowerStmt loop statement env before bounded)⟩
    · exact ih _ bounded

theorem fork_entry_liveBound (condition : ValueId) (env : LEnv) (before : LS) :
    LiveBound (setCur (some (fork condition env before).1.1) env (fork condition env before).2).2 ∧
      (fork condition env before).1.2 < (fork condition env before).2.blocks.size := by
  obtain ⟨_, _, _, yesBound, noBound⟩ := adv_fork_step (.refl before)
    (rfl : fork condition env before = ((fork condition env before).1, (fork condition env before).2))
  exact ⟨liveBound_setCur yesBound env, noBound⟩

theorem shortCircuitChild_liveBound (env : LEnv) (before : LS) (isAnd : Bool) (left : ValueId) (right : Expr) :
    ChildrenLiveBound [shortCircuitChild env before isAnd left right] := by
  unfold shortCircuitChild
  split
  · rename_i live
    obtain ⟨current, currentAt⟩ := Option.isSome_iff_exists.mp live
    refine ⟨liveBound_setCur ?_ env, trivial⟩
    simp only [scFork_run _ _ _ currentAt]
    simp
    exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
  · trivial

theorem branchChildren_liveBound (env : LEnv) (before : LS) (condition : ValueId)
    (loop : Option LoopCtx) (want : Bool) (yes : Core.Block) (no : Option Core.Block) :
    ChildrenLiveBound (branchChildren env before condition loop want yes no) := by
  unfold branchChildren
  split
  · have bounds := fork_entry_liveBound condition env before
    refine ⟨bounds.1, ?_⟩
    cases no with
    | none => trivial
    | some no =>
      refine ⟨liveBound_setCur ?_ env, trivial⟩
      have extension := (advB_lowerBlock loop [] want yes env
        (setCur (some (fork condition env before).1.1) env (fork condition env before).2).2 _ _ rfl).ext
      exact Nat.lt_of_lt_of_le bounds.2 (by simpa only [setCur_run] using extension.1)
  · trivial

theorem whileChildren_liveBound (env : LEnv) (before : LS) (condition : Expr) (body : Core.Block) :
    ChildrenLiveBound (whileChildren env before condition body) := by
  let header := newBlock [] env before
  let jumped := (emitTerm (.br header.1.1 []) env header.2).2
  let conditionBefore := (setCur (some header.1.1) env jumped).2
  let tested := lowerExpr condition env conditionBefore
  have headerBound : header.1.1 < jumped.blocks.size := by
    have bound : header.1.1 < header.2.blocks.size := by simp [header, newBlock0_run]
    exact Nat.lt_of_lt_of_le bound (advB_emitTerm _ env header.2 _ _ rfl).ext.1
  change LiveBound conditionBefore ∧ ChildrenLiveBound [if tested.2.cur.isSome then
    let split := fork tested.1 env tested.2
    let bodyBefore := (setCur (some split.1.1) env split.2).2
    some (.block (some ⟨tested.2.stack.length, split.1.2, .jump header.1.1⟩) [] false body, bodyBefore)
    else none]
  refine ⟨liveBound_setCur headerBound env, ?_⟩
  split
  · exact ⟨(fork_entry_liveBound tested.1 env tested.2).1, trivial⟩
  · trivial

theorem rangeChild_liveBound (env : LEnv) (before : LS) (varId : VarId) (low high : ValueId)
    (body : Core.Block) (origin : OriginId) :
    ChildrenLiveBound [rangeChild env before varId low high body origin] := by
  unfold rangeChild
  split
  · exact ⟨(fork_entry_liveBound _ _ _).1, trivial⟩
  · trivial

theorem eachChild_liveBound (env : LEnv) (before : LS) (varId : VarId) (index : Option VarId)
    (view : View) (byRef : Bool) (body : Core.Block) (origin : OriginId) :
    ChildrenLiveBound [eachChild env before varId index view byRef body origin] := by
  unfold eachChild
  dsimp only
  split
  · refine ⟨?_, trivial⟩
    apply liveBound_of_advB (advB_eachElemValue _ _ _) env _
    apply liveBound_of_advB (advB_emitDef _) env _
    exact (fork_entry_liveBound _ _ _).1
  · trivial

#print axioms fork_entry_liveBound
#print axioms branchChildren_liveBound
#print axioms whileChildren_liveBound
#print axioms rangeChild_liveBound
#print axioms eachChild_liveBound

end Goose.Lower.Validation.SourceReplacementWriterLedger
