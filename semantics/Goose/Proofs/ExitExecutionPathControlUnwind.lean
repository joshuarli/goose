import Goose.Proofs.ExitExecutionPathExitChannelsUnwind

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem returnOperands_escape_after_child (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (operands : List Expr) (origin : Goose.Core.OriginId)
    (initial prepared before : ExecutionState) (channels : List Channel)
    (address : ExitAddress) (carriers : List Carrier)
    (selected : enclosingActivation environment initial = .ok activation initial)
    (setup : exitChannels environment activation operands origin initial = .ok channels prepared)
    (escaped : evalOperands fuel config environment channels operands prepared = .escape address carriers before) :
    (∃ final changes,
      execStmt (fuel + 1) config environment (.retValues operands origin) initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) ∨
    (∃ reason final changes,
      execStmt (fuel + 1) config environment (.retValues operands origin) initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) := by
  have result := withExitChannels_escape_after_action environment activation operands origin
    (fun channels => evalOperands fuel config environment channels operands) initial prepared before channels address carriers setup escaped
  rcases result with ⟨final, changes, returned, stdout, objects, storage⟩ | ⟨reason, final, changes, stopped, stdout, objects, storage⟩
  · refine Or.inl ⟨final, changes, ?_, stdout, objects, storage⟩
    simp only [execStmt, bind, selected, returned]
  · refine Or.inr ⟨reason, final, changes, ?_, stdout, objects, storage⟩
    simp only [execStmt, bind, selected, stopped]

#print axioms returnOperands_escape_after_child

theorem returnForwardProduce_escape_after_child (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial prepared before : ExecutionState) (channels : List Channel)
    (address : ExitAddress) (carriers : List Carrier)
    (selected : enclosingActivation environment initial = .ok activation initial)
    (setup : exitChannels environment activation (List.replicate activation.channels.length producer) origin initial = .ok channels prepared)
    (escaped : evalProduce fuel config environment channels producer prepared = .escape address carriers before) :
    (∃ final changes,
      execStmt (fuel + 1) config environment (.retForward producer origin) initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) ∨
    (∃ reason final changes,
      execStmt (fuel + 1) config environment (.retForward producer origin) initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) := by
  have result := withExitChannels_escape_after_action environment activation (List.replicate activation.channels.length producer) origin
    (fun channels => evalProduce fuel config environment channels producer) initial prepared before channels address carriers setup escaped
  rcases result with ⟨final, changes, returned, stdout, objects, storage⟩ | ⟨reason, final, changes, stopped, stdout, objects, storage⟩
  · refine Or.inl ⟨final, changes, ?_, stdout, objects, storage⟩
    simp only [execStmt, bind, selected, returned]
  · refine Or.inr ⟨reason, final, changes, ?_, stdout, objects, storage⟩
    simp only [execStmt, bind, selected, stopped]

#print axioms returnForwardProduce_escape_after_child

theorem returnProduce_escape_after_child (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial prepared before : ExecutionState) (channels : List Channel)
    (address : ExitAddress) (carriers : List Carrier)
    (selected : enclosingActivation environment initial = .ok activation initial)
    (setup : exitChannels environment activation (match producer with | .values operands => operands | _ => List.replicate activation.channels.length producer) origin initial = .ok channels prepared)
    (escaped : evalProduce fuel config environment channels producer prepared = .escape address carriers before) :
    (∃ final changes,
      execStmt (fuel + 1) config environment (.ret (some producer) origin) initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) ∨
    (∃ reason final changes,
      execStmt (fuel + 1) config environment (.ret (some producer) origin) initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) := by
  have result := withExitChannels_escape_after_action environment activation (match (generalizing := false) producer with | .values operands => operands | _ => List.replicate activation.channels.length producer) origin
    (fun channels => evalProduce fuel config environment channels producer) initial prepared before channels address carriers setup escaped
  rcases result with ⟨final, changes, returned, stdout, objects, storage⟩ | ⟨reason, final, changes, stopped, stdout, objects, storage⟩
  · refine Or.inl ⟨final, changes, ?_, stdout, objects, storage⟩
    cases producer <;> simp_all only [execStmt, bind]
  · refine Or.inr ⟨reason, final, changes, ?_, stdout, objects, storage⟩
    cases producer <;> simp_all only [execStmt, bind]

#print axioms returnProduce_escape_after_child

theorem returnFromOperands_escape_after_child (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (target : Nat) (operands : List Expr) (origin : Goose.Core.OriginId)
    (initial prepared before : ExecutionState) (channels : List Channel)
    (address : ExitAddress) (carriers : List Carrier)
    (selected : targetActivation config target initial = .ok activation initial)
    (setup : exitChannels environment activation operands origin initial = .ok channels prepared)
    (escaped : evalOperands fuel config environment channels operands prepared = .escape address carriers before) :
    (∃ final changes,
      execStmt (fuel + 1) config environment (.returnFrom target operands origin) initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) ∨
    (∃ reason final changes,
      execStmt (fuel + 1) config environment (.returnFrom target operands origin) initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) := by
  have result := withExitChannels_escape_after_action environment activation operands origin
    (fun channels => evalOperands fuel config environment channels operands) initial prepared before channels address carriers setup escaped
  rcases result with ⟨final, changes, returned, stdout, objects, storage⟩ | ⟨reason, final, changes, stopped, stdout, objects, storage⟩
  · refine Or.inl ⟨final, changes, ?_, stdout, objects, storage⟩
    simp only [execStmt, bind, selected, returned]
  · refine Or.inr ⟨reason, final, changes, ?_, stdout, objects, storage⟩
    simp only [execStmt, bind, selected, stopped]

#print axioms returnFromOperands_escape_after_child

theorem returnFromForwardProduce_escape_after_child (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (target : Nat) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial prepared before : ExecutionState) (channels : List Channel)
    (address : ExitAddress) (carriers : List Carrier)
    (selected : targetActivation config target initial = .ok activation initial)
    (setup : exitChannels environment activation (List.replicate activation.channels.length producer) origin initial = .ok channels prepared)
    (escaped : evalProduce fuel config environment channels producer prepared = .escape address carriers before) :
    (∃ final changes,
      execStmt (fuel + 1) config environment (.returnFromForward target producer origin) initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) ∨
    (∃ reason final changes,
      execStmt (fuel + 1) config environment (.returnFromForward target producer origin) initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) := by
  have result := withExitChannels_escape_after_action environment activation (List.replicate activation.channels.length producer) origin
    (fun channels => evalProduce fuel config environment channels producer) initial prepared before channels address carriers setup escaped
  rcases result with ⟨final, changes, returned, stdout, objects, storage⟩ | ⟨reason, final, changes, stopped, stdout, objects, storage⟩
  · refine Or.inl ⟨final, changes, ?_, stdout, objects, storage⟩
    simp only [execStmt, bind, selected, returned]
  · refine Or.inr ⟨reason, final, changes, ?_, stdout, objects, storage⟩
    simp only [execStmt, bind, selected, stopped]

#print axioms returnFromForwardProduce_escape_after_child


theorem breakProduce_escape_after_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (target : BreakTarget) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial prepared before : ExecutionState) (channels : List Channel)
    (address : ExitAddress) (carriers : List Carrier)
    (selected : currentBreak environment.act (some .block) initial = .ok target initial)
    (setup : exitChannels environment { environment with channels := target.channels }
      (match producer with | .values operands => operands | _ => List.replicate target.channels.length producer)
      origin initial = .ok channels prepared)
    (escaped : evalProduce fuel config environment channels producer prepared = .escape address carriers before) :
    (∃ final changes,
      execStmt (fuel + 1) config environment (.breakValue producer origin) initial = .escape address carriers final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) ∨
    (∃ reason final changes,
      execStmt (fuel + 1) config environment (.breakValue producer origin) initial = .stop reason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage) := by
  have result := withExitChannels_escape_after_action environment { environment with channels := target.channels }
    (match (generalizing := false) producer with | .values operands => operands | _ => List.replicate target.channels.length producer)
    origin (fun channels => evalProduce fuel config environment channels producer)
    initial prepared before channels address carriers setup escaped
  rcases result with ⟨final, changes, returned, stdout, objects, storage⟩ | ⟨reason, final, changes, stopped, stdout, objects, storage⟩
  · refine Or.inl ⟨final, changes, ?_, stdout, objects, storage⟩
    cases producer <;> simp_all only [execStmt, bind]
  · refine Or.inr ⟨reason, final, changes, ?_, stdout, objects, storage⟩
    cases producer <;> simp_all only [execStmt, bind]

#print axioms breakProduce_escape_after_child

theorem returnOperands_stop_after_child (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (operands : List Expr) (origin : Goose.Core.OriginId)
    (initial prepared before : ExecutionState) (channels : List Channel) (reason : Goose.Core.Stop)
    (selected : enclosingActivation environment initial = .ok activation initial)
    (setup : exitChannels environment activation operands origin initial = .ok channels prepared)
    (stopped : evalOperands fuel config environment channels operands prepared = .stop reason before) :
    ∃ finalReason final changes,
      execStmt (fuel + 1) config environment (.retValues operands origin) initial = .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage := by
  obtain ⟨finalReason, final, changes, returned, stdout, objects, storage⟩ :=
    withExitChannels_stop_after_action environment activation operands origin
      (fun channels => evalOperands fuel config environment channels operands) initial prepared before channels reason setup stopped
  refine ⟨finalReason, final, changes, ?_, stdout, objects, storage⟩
  simp only [execStmt, bind, selected, returned]

#print axioms returnOperands_stop_after_child

theorem returnForwardProduce_stop_after_child (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial prepared before : ExecutionState) (channels : List Channel) (reason : Goose.Core.Stop)
    (selected : enclosingActivation environment initial = .ok activation initial)
    (setup : exitChannels environment activation (List.replicate activation.channels.length producer) origin initial = .ok channels prepared)
    (stopped : evalProduce fuel config environment channels producer prepared = .stop reason before) :
    ∃ finalReason final changes,
      execStmt (fuel + 1) config environment (.retForward producer origin) initial = .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage := by
  obtain ⟨finalReason, final, changes, returned, stdout, objects, storage⟩ :=
    withExitChannels_stop_after_action environment activation (List.replicate activation.channels.length producer) origin
      (fun channels => evalProduce fuel config environment channels producer) initial prepared before channels reason setup stopped
  refine ⟨finalReason, final, changes, ?_, stdout, objects, storage⟩
  simp only [execStmt, bind, selected, returned]

#print axioms returnForwardProduce_stop_after_child

theorem returnProduce_stop_after_child (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial prepared before : ExecutionState) (channels : List Channel) (reason : Goose.Core.Stop)
    (selected : enclosingActivation environment initial = .ok activation initial)
    (setup : exitChannels environment activation (match producer with | .values operands => operands | _ => List.replicate activation.channels.length producer) origin initial = .ok channels prepared)
    (stopped : evalProduce fuel config environment channels producer prepared = .stop reason before) :
    ∃ finalReason final changes,
      execStmt (fuel + 1) config environment (.ret (some producer) origin) initial = .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage := by
  obtain ⟨finalReason, final, changes, returned, stdout, objects, storage⟩ :=
    withExitChannels_stop_after_action environment activation (match (generalizing := false) producer with | .values operands => operands | _ => List.replicate activation.channels.length producer) origin
      (fun channels => evalProduce fuel config environment channels producer) initial prepared before channels reason setup stopped
  refine ⟨finalReason, final, changes, ?_, stdout, objects, storage⟩
  cases producer <;> simp_all only [execStmt, bind]

#print axioms returnProduce_stop_after_child

theorem returnFromOperands_stop_after_child (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (target : Nat) (operands : List Expr) (origin : Goose.Core.OriginId)
    (initial prepared before : ExecutionState) (channels : List Channel) (reason : Goose.Core.Stop)
    (selected : targetActivation config target initial = .ok activation initial)
    (setup : exitChannels environment activation operands origin initial = .ok channels prepared)
    (stopped : evalOperands fuel config environment channels operands prepared = .stop reason before) :
    ∃ finalReason final changes,
      execStmt (fuel + 1) config environment (.returnFrom target operands origin) initial = .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage := by
  obtain ⟨finalReason, final, changes, returned, stdout, objects, storage⟩ :=
    withExitChannels_stop_after_action environment activation operands origin
      (fun channels => evalOperands fuel config environment channels operands) initial prepared before channels reason setup stopped
  refine ⟨finalReason, final, changes, ?_, stdout, objects, storage⟩
  simp only [execStmt, bind, selected, returned]

#print axioms returnFromOperands_stop_after_child

theorem returnFromForwardProduce_stop_after_child (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation) (target : Nat) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial prepared before : ExecutionState) (channels : List Channel) (reason : Goose.Core.Stop)
    (selected : targetActivation config target initial = .ok activation initial)
    (setup : exitChannels environment activation (List.replicate activation.channels.length producer) origin initial = .ok channels prepared)
    (stopped : evalProduce fuel config environment channels producer prepared = .stop reason before) :
    ∃ finalReason final changes,
      execStmt (fuel + 1) config environment (.returnFromForward target producer origin) initial = .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage := by
  obtain ⟨finalReason, final, changes, returned, stdout, objects, storage⟩ :=
    withExitChannels_stop_after_action environment activation (List.replicate activation.channels.length producer) origin
      (fun channels => evalProduce fuel config environment channels producer) initial prepared before channels reason setup stopped
  refine ⟨finalReason, final, changes, ?_, stdout, objects, storage⟩
  simp only [execStmt, bind, selected, returned]

#print axioms returnFromForwardProduce_stop_after_child

theorem breakProduce_stop_after_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (target : BreakTarget) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial prepared before : ExecutionState) (channels : List Channel) (reason : Goose.Core.Stop)
    (selected : currentBreak environment.act (some .block) initial = .ok target initial)
    (setup : exitChannels environment { environment with channels := target.channels } (match producer with | .values operands => operands | _ => List.replicate target.channels.length producer) origin initial = .ok channels prepared)
    (stopped : evalProduce fuel config environment channels producer prepared = .stop reason before) :
    ∃ finalReason final changes,
      execStmt (fuel + 1) config environment (.breakValue producer origin) initial = .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧ final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage := by
  obtain ⟨finalReason, final, changes, returned, stdout, objects, storage⟩ :=
    withExitChannels_stop_after_action environment { environment with channels := target.channels } (match (generalizing := false) producer with | .values operands => operands | _ => List.replicate target.channels.length producer) origin
      (fun channels => evalProduce fuel config environment channels producer) initial prepared before channels reason setup stopped
  refine ⟨finalReason, final, changes, ?_, stdout, objects, storage⟩
  cases producer <;> simp_all only [execStmt, bind]

#print axioms breakProduce_stop_after_child

end Goose.Proofs.ExitExecution
