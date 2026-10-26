import Goose.Proofs.ConstructionAcceptedCursor
import Goose.Proofs.ConstructionRootCorrespondenceCursors

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

inductive SourceAction
  | expression (value : Expr)
  | statement (value : Stmt)
  | statements (values : List Stmt)
  | block (value : Block)

def SourceActionChecks (frame : ConstructionSourceFrame) : SourceAction → Prop
  | .expression expression => ∃ types typingAfter roots rootsAfter,
      typeExpr frame.typingFuel frame.typing expression frame.typingCounter = .ok (types, typingAfter) ∧
      rpExpr frame.source expression frame.rootCursor = .ok (roots, rootsAfter)
  | .statement statement => ∃ next typingAfter rootsAfter,
      typeStatement frame.typingFuel frame.typing statement frame.typingCounter = .ok (next, typingAfter) ∧
      rpStmt frame.source statement frame.rootCursor = .ok ((), rootsAfter)
  | .statements statements => ∃ next typingAfter rootsAfter,
      typeStatements frame.typingFuel frame.typing statements frame.typingCounter = .ok (next, typingAfter) ∧
      rpStmts frame.source statements frame.rootCursor = .ok ((), rootsAfter)
  | .block block => ∃ types typingAfter roots rootsAfter,
      typeBlock frame.typingFuel frame.typing block frame.typingCounter = .ok (types, typingAfter) ∧
      rpBlockValue frame.source [] block frame.rootCursor = .ok (roots, rootsAfter)

def implementationBodyFrame (config : EvalConfig) (frame : ConstructionSourceFrame) : ConstructionSourceFrame :=
  { frame with
    typing := {
      module := config.module
      implementation := some frame.source.impl
      variables := frame.source.impl.vars
      visible := List.range frame.source.impl.params.size
      scope := frame.source.impl.body.scope
      loops := 0
      use := if frame.source.impl.results.isEmpty then .ordinary else .result
      request := .value
      resultRequests := frame.source.impl.results.toList.map (·.request)
      globalLimit := config.module.globals.size }
    source := { frame.source with scopes := [], valueBlock := none, initializing := [] }
    typingFuel := 4096
    typingCounter := frame.source.impl.params.size
    rootCursor := ⟨frame.source.impl.params.size, {}, []⟩ }

theorem implementationBodyFrame_checks (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (context : Nat) (phase : frame.phase = .implementation context)
    (compatible : SourceFrameCompatible accepted frame) :
    SourceActionChecks (implementationBodyFrame config frame) (.block frame.source.impl.body) := by
  have origin := compatible.origin
  simp only [SourceOrigin, phase] at origin
  obtain ⟨original, calls, _, implementationAt, _, _, _, _, _, _, _, roots, rootsAfter, rootChecked⟩ := origin
  obtain ⟨types, typingAfter, typeChecked⟩ := validated_implementation_typing config.module original.impl
    frame.source.impl accepted.accepted implementationAt
  exact ⟨types, typingAfter, roots, rootsAfter, typeChecked, rootChecked⟩

def blockStatementsFrame (frame : ConstructionSourceFrame) (scope fuel : Nat) : ConstructionSourceFrame :=
  { frame with
    typing := { frame.typing with scope := scope }
    source := { frame.source with scopes := scope :: frame.source.scopes }
    typingFuel := fuel }

def letInitializerFrame (frame : ConstructionSourceFrame) (id fuel : Nat) : ConstructionSourceFrame :=
  { ordinaryOperandFrame frame fuel with
    typingCounter := frame.typingCounter + 1
    source := { frame.source with initializing := id :: frame.source.initializing }
    rootCursor := { frame.rootCursor with nextVar := frame.rootCursor.nextVar + 1 } }

inductive DirectSourceChild : ConstructionSourceFrame → SourceAction → ConstructionSourceFrame → SourceAction → Prop
  | notOperand (frame : ConstructionSourceFrame) (expression : Expr) (fuel : Nat)
      (nesting : frame.typingFuel = fuel + 1) :
      DirectSourceChild frame (.expression (.not expression)) (ordinaryOperandFrame frame fuel) (.expression expression)
  | blockStatements (frame : ConstructionSourceFrame) (scope fuel : Nat) (statements : List Stmt) (tail : Option Expr)
      (nesting : frame.typingFuel = fuel + 1) :
      DirectSourceChild frame (.block (.mk scope statements tail))
        (blockStatementsFrame frame scope fuel) (.statements statements)
  | statementsHead (frame : ConstructionSourceFrame) (statement : Stmt) (rest : List Stmt) (fuel : Nat)
      (nesting : frame.typingFuel = fuel + 1) :
      DirectSourceChild frame (.statements (statement :: rest)) { frame with typingFuel := fuel } (.statement statement)
  | statementsTail (frame : ConstructionSourceFrame) (statement : Stmt) (rest : List Stmt) (fuel : Nat)
      (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState)
      (nesting : frame.typingFuel = fuel + 1)
      (typed : typeStatement fuel frame.typing statement frame.typingCounter = .ok (next, typingAfter))
      (rooted : rpStmt frame.source statement frame.rootCursor = .ok ((), rootsAfter)) :
      DirectSourceChild frame (.statements (statement :: rest))
        { frame with typingFuel := fuel, typing := next, typingCounter := typingAfter, rootCursor := rootsAfter }
        (.statements rest)
  | letInitializer (frame : ConstructionSourceFrame) (id origin fuel : Nat) (expression : Expr)
      (nesting : frame.typingFuel = fuel + 1)
      (typedOrder : id = frame.typingCounter) (rootOrder : id = frame.rootCursor.nextVar) :
      DirectSourceChild frame (.statement (.letS id expression origin)) (letInitializerFrame frame id fuel)
        (.expression expression)
  | statementExpression (frame : ConstructionSourceFrame) (expression : Expr) (origin fuel : Nat)
      (nesting : frame.typingFuel = fuel + 1) :
      DirectSourceChild frame (.statement (.expr expression origin)) (ordinaryOperandFrame frame fuel) (.expression expression)

inductive SourcePosition {config : EvalConfig} (accepted : AcceptedModule config) :
    ConstructionSourceFrame → SourceAction → Prop
  | implementationBody (frame : ConstructionSourceFrame) (context : Nat)
      (phase : frame.phase = .implementation context) (compatible : SourceFrameCompatible accepted frame) :
      SourcePosition accepted (implementationBodyFrame config frame) (.block frame.source.impl.body)
  | child {parent child : ConstructionSourceFrame} {parentAction childAction : SourceAction}
      (ancestry : SourcePosition accepted parent parentAction)
      (edge : DirectSourceChild parent parentAction child childAction) (checked : SourceActionChecks child childAction) :
      SourcePosition accepted child childAction
  | instantiate {frame : ConstructionSourceFrame} {action : SourceAction}
      (ancestry : SourcePosition accepted frame action) (interpretation : RootInterpretation) (initialized : Nat) :
      SourcePosition accepted { frame with interpretation := interpretation, initialized := initialized } action

theorem SourcePosition.checked {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (action : SourceAction) (position : SourcePosition accepted frame action) :
    SourceActionChecks frame action := by
  induction position with
  | implementationBody frame context phase compatible => exact implementationBodyFrame_checks config accepted frame context phase compatible
  | child ancestry edge checked ih => exact checked
  | instantiate ancestry interpretation initialized ih => cases action <;> exact ih

theorem SourcePosition.not_operand {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (expression : Expr) (fuel : Nat)
    (position : SourcePosition accepted frame (.expression (.not expression)))
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (nesting : frame.typingFuel = fuel + 1)
    (checked : CheckedValue frame (.not expression) ty roots typingAfter rootsAfter) :
    ∃ operandRoots, SourcePosition accepted (ordinaryOperandFrame frame fuel) (.expression expression) ∧
      CheckedValue (ordinaryOperandFrame frame fuel) expression .bool operandRoots typingAfter rootsAfter := by
  obtain ⟨_, _, operandRoots, operand⟩ := checkedValue_not_operand frame fuel expression ty roots typingAfter rootsAfter nesting checked
  exact ⟨operandRoots, .child position (.notOperand frame expression fuel nesting)
    ⟨[.bool], typingAfter, operandRoots, rootsAfter, operand.typing, operand.provenance⟩, operand⟩

theorem SourcePosition.block_statements {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (scope fuel : Nat) (statements : List Stmt) (tail : Option Expr)
    (position : SourcePosition accepted frame (.block (.mk scope statements tail)))
    (nesting : frame.typingFuel = fuel + 1) :
    SourcePosition accepted (blockStatementsFrame frame scope fuel) (.statements statements) := by
  obtain ⟨types, typingAfter, roots, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  rw [nesting] at typed
  simp only [typeBlock, bind, StateT.bind] at typed
  obtain ⟨_, rootMiddle, _, rootedStatements, _, _⟩ := rpBlockValue_body rooted
  simp only [List.length_nil, Nat.add_zero] at rootedStatements
  cases checkedStatements : typeStatements fuel { frame.typing with scope := scope } statements frame.typingCounter with
  | error failure =>
    rw [checkedStatements] at typed
    change Except.error _ = Except.ok _ at typed
    cases typed
  | ok result =>
    obtain ⟨next, nextCounter⟩ := result
    exact .child position (.blockStatements frame scope fuel statements tail nesting)
      ⟨next, nextCounter, rootMiddle, checkedStatements, rootedStatements⟩

theorem SourcePosition.statements_head {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (statement : Stmt) (rest : List Stmt) (fuel : Nat)
    (position : SourcePosition accepted frame (.statements (statement :: rest)))
    (nesting : frame.typingFuel = fuel + 1) :
    SourcePosition accepted { frame with typingFuel := fuel } (.statement statement) := by
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  rw [nesting] at typed
  simp only [typeStatements, bind, StateT.bind] at typed
  obtain ⟨rootMiddle, rootedStatement, _⟩ := rpStmts_cons rooted
  cases checkedStatement : typeStatement fuel frame.typing statement frame.typingCounter with
  | error failure =>
    rw [checkedStatement] at typed
    change Except.error _ = Except.ok _ at typed
    cases typed
  | ok result =>
    obtain ⟨middle, nextCounter⟩ := result
    exact .child position (.statementsHead frame statement rest fuel nesting)
      ⟨middle, nextCounter, rootMiddle, checkedStatement, rootedStatement⟩

#print axioms implementationBodyFrame_checks
#print axioms SourcePosition.not_operand
#print axioms SourcePosition.block_statements
#print axioms SourcePosition.statements_head

end Goose.Proofs.ConstructionAcceptedExecution
