import Goose.Lower.Validation.PermissionPreservationNewEmit
import Goose.Lower.GeneratedTargetFramesSource
import Goose.Lower.GeneratedBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem FreshPermissionInstruction.of_framed_run {α : Type} {action : B α}
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat}
    {before after : LS} {instruction : Inst} {result : α} {loop : Option LoopCtx}
    (permitted : FreshPermissionInstruction module func le first before instruction)
    (run : action le before = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (frameRun : GeneratedTargetFrameRun loop action)
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before) :
    FreshPermissionInstruction module func le first after instruction := by
  have afterDense := (dense le before result after run generated.dense generated.live).1
  have advanced := advances le before result after run
  have framed := (frameRun before le before result after (.refl _) frames (.refl loop before) run).1
  exact permitted.retained generated.dense afterDense advanced.ext advanced.vals
    (typed le before result after run) frames framed

theorem NewPermissionInstructions.compose_framed {α : Type} {action : B α}
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat}
    {before middle after : LS} {result : α} {loop : Option LoopCtx}
    (head : NewPermissionInstructions module func le first before middle)
    (tail : NewPermissionInstructions module func le first middle after)
    (run : action le middle = (result, after))
    (dense : DenseRun action) (advances : AdvB action) (typed : TypeRun action)
    (frameRun : GeneratedTargetFrameRun loop action)
    (generated : GeneratedBuilderState middle) (frames : LoopBuilderFrames loop middle) :
    NewPermissionInstructions module func le first before after := by
  apply head.compose tail
  intro instruction member permitted
  exact permitted.of_framed_run run dense advances typed frameRun generated frames

theorem FreshPermissionInstruction.branch (module : GIR.Module) (func : Func) (le : LEnv)
    (first : Nat) (state : LS) (target : BlockId) (arguments : List ValueId) :
    FreshPermissionInstruction module func le first state (.term (.br target arguments)) := by
  constructor
  · constructor
    · intro owner value origin same; cases same
    · intro owner value origin mu ty same; cases same
    · intro owner mutation; cases mutation
    · intro value owner same; cases same
    · intro owner value origin same; cases same
    · intro value mode owner ty same; cases same
    · intro value callee args origin descriptor same; cases same
    · intro slot value origin descriptor same; cases same
    · intro values origin same; cases same
  · constructor
    · intro owner value origin same; cases same
    · intro value mode owner same; cases same

theorem FreshPermissionInstruction.conditional (module : GIR.Module) (func : Func) (le : LEnv)
    (first : Nat) (state : LS) (condition : ValueId) (yes : BlockId) (yesArgs : List ValueId)
    (no : BlockId) (noArgs : List ValueId) :
    FreshPermissionInstruction module func le first state
      (.term (.condbr condition yes yesArgs no noArgs)) := by
  constructor
  · constructor
    · intro owner value origin same; cases same
    · intro owner value origin mu ty same; cases same
    · intro owner mutation; cases mutation
    · intro value owner same; cases same
    · intro owner value origin same; cases same
    · intro value mode owner ty same; cases same
    · intro value callee args origin descriptor same; cases same
    · intro slot value origin descriptor same; cases same
    · intro values origin same; cases same
  · constructor
    · intro owner value origin same; cases same
    · intro value mode owner same; cases same

theorem NewPermissionInstructions.setCur {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {current : Option BlockId}
    (run : Goose.Lower.setCur current le before = (result, after)) :
    NewPermissionInstructions module func le first before after := by
  rw [setCur_run] at run
  obtain ⟨_,rfl⟩ := Prod.mk.inj run
  exact .of_blocks_eq rfl

theorem NewPermissionInstructions.branch {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {target : BlockId} {arguments : List ValueId}
    (run : Goose.Lower.emitTerm (.br target arguments) le before = (result, after)) :
    NewPermissionInstructions module func le first before after :=
  .emitTerm run (fun _ => FreshPermissionInstruction.branch module func le first after target arguments)

theorem NewPermissionInstructions.conditional {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {condition : ValueId}
    {yes no : BlockId} {yesArgs noArgs : List ValueId}
    (run : Goose.Lower.emitTerm (.condbr condition yes yesArgs no noArgs) le before = (result, after)) :
    NewPermissionInstructions module func le first before after :=
  .emitTerm run (fun _ => FreshPermissionInstruction.conditional module func le first after condition yes yesArgs no noArgs)

theorem FreshPermissionInstruction.setCur {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {current : Option BlockId} {instruction : Inst}
    (permitted : FreshPermissionInstruction module func le first before instruction)
    (run : Goose.Lower.setCur current le before = (result, after)) :
    FreshPermissionInstruction module func le first after instruction := by
  rw [setCur_run] at run
  obtain ⟨_,rfl⟩ := Prod.mk.inj run
  exact permitted

private theorem newBlock_insts {le : LEnv} {before after : LS} {types : List VTy}
    {result : BlockId × List ValueId} (run : Goose.Lower.newBlock types le before = (result,after)) :
    after.insts = before.insts := by
  rw [newBlock_run_general] at run
  obtain ⟨_,rfl⟩ := Prod.mk.inj run
  simp [LS.insts]

theorem NewPermissionInstructions.prepend_newBlock {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS} {result : BlockId × List ValueId} {types : List VTy}
    (run : Goose.Lower.newBlock types le before = (result,middle))
    (tail : NewPermissionInstructions module func le first middle after) :
    NewPermissionInstructions module func le first before after := by
  intro instruction member
  rcases tail instruction member with old | issued
  · exact Or.inl (by simpa only [newBlock_insts run] using old)
  · exact Or.inr issued

theorem NewPermissionInstructions.prepend_setCur {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS} {result : Unit} {current : Option BlockId}
    (run : Goose.Lower.setCur current le before = (result,middle))
    (tail : NewPermissionInstructions module func le first middle after) :
    NewPermissionInstructions module func le first before after := by
  rw [setCur_run] at run
  obtain ⟨_,rfl⟩ := Prod.mk.inj run
  exact tail

theorem NewPermissionInstructions.append_setCur {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS} {result : Unit} {current : Option BlockId}
    (head : NewPermissionInstructions module func le first before middle)
    (run : Goose.Lower.setCur current le middle = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  intro instruction member
  have oldMember : instruction ∈ middle.insts := by
    rw [setCur_run] at run
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    exact member
  exact (head instruction oldMember).imp id (fun permitted => permitted.setCur run)

theorem NewPermissionInstructions.fork {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : BlockId × BlockId} {condition : ValueId}
    (run : Goose.Lower.fork condition le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [Goose.Lower.fork,bind_eq] at run
  obtain ⟨yes,one,yesRun,no,two,noRun,ignored,three,branchRun,finish⟩ := run
  rw [pure_run] at finish
  obtain ⟨_,rfl⟩ := Prod.mk.inj finish
  intro instruction member
  rcases NewPermissionInstructions.conditional branchRun instruction member with old | fresh
  · exact Or.inl (by simpa only [newBlock_insts noRun,newBlock_insts yesRun] using old)
  · exact Or.inr fresh

theorem NewPermissionInstructions.scFork {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : BlockId × BlockId × ValueId} {condition : ValueId}
    {isAnd : Bool} (run : Goose.Lower.scFork isAnd condition le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  cases isAnd <;> simp only [Goose.Lower.scFork,Bool.false_eq_true,ite_false,ite_true,bind_eq] at run
  all_goals
    obtain ⟨rhs,one,rhsRun,join,two,joinRun,ignored,three,branchRun,finish⟩ := run
    rw [pure_run] at finish
    obtain ⟨_,rfl⟩ := Prod.mk.inj finish
    intro instruction member
    rcases NewPermissionInstructions.conditional branchRun instruction member with old | fresh
    · exact Or.inl (by simpa only [newBlock_insts joinRun,newBlock_insts rhsRun] using old)
    · exact Or.inr fresh

theorem NewPermissionInstructions.patchBranch {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {block target : BlockId} {arguments : List ValueId}
    (run : Goose.Lower.patchTerm block (.br target arguments) le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  rw [patchTerm_run] at run
  obtain ⟨_,rfl⟩ := Prod.mk.inj run
  intro instruction member
  rcases permission_appendInst_membership (before := before) (block := block)
      (added := .term (.br target arguments)) member with old | rfl
  · exact Or.inl old
  · exact Or.inr (FreshPermissionInstruction.branch module func le first _ target arguments)

end Goose.Lower.Validation
