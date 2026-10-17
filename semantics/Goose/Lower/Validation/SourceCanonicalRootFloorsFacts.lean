import Goose.Lower.Validation.SourceCanonicalRootFloorsNativeFlow
import Goose.Lower.Validation.SourceCanonicalRootFloorsResults

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.GIR ProvenanceConvergence

structure SourceCanonicalTables (env : PEnv) (func : Func) : Prop where
  rootUniverse : RootUniverse (resultRoots (lower env.mod) (lower env.mod).implTypes) func
    (finiteRootUniverse (lower env.mod).globals.size func)
  rootCount : (finiteRootUniverse (lower env.mod).globals.size func).length ≤ (lower env.mod).rootCount
  native : ∀ block ∈ func.blocks.toList, ∀ value op,
    Inst.def value op ∈ block.insts →
      checkInstTypes func { (lower env.mod).tyEnv func with vals := func.valueTypes (lower env.mod) }
        (func.valueTypes (lower env.mod)) (.def value op) = .ok ()
  definitions : ∀ block ∈ func.blocks.toList, ∀ value op,
    Inst.def value op ∈ block.insts → value < func.numValues
  valueRows : ∀ value roots, (value, roots) ∈ func.roots.values.getD #[] → value < func.numValues
  variables : ∀ (slot : VarId) (localVar : LocalVar), env.impl.vars[slot]? = some localVar →
    ∃ nativeSlot : GIR.Slot, func.slots[slot]? = some nativeSlot ∧ nativeSlot.ty = localVar.ty
  annotations : ∀ (slot : VarId) (localVar : LocalVar), env.impl.vars[slot]? = some localVar →
    localVar.ty.isRefLike = true → localVar.ty.isRefSlice = false →
      ((env.ann slot).getD []) ⊆ rootsAt func.slotRootSeeds slot
  contents : ∀ slot roots, env.cont slot = some roots →
    ∃ formal : Ty, func.params[slot]? = some formal ∧ formal.isRefSlice = true ∧
      RootRef.param slot ∈ rootsAt func.slotRootSeeds slot ∧
      roots ⊆ ((func.roots.contents.find? (·.1 == slot)).map (·.2)).getD []
  callees : ∀ callee context impl, env.mod.contexts[callee]? = some context →
    env.mod.impls[context.impl]? = some impl → ∀ type, impl.results.toList = [type] →
      type.isRefLike = true → (context.resultRoots[0]?.getD []) ⊆
        rootsAt (resultRoots (lower env.mod) (lower env.mod).implTypes) callee

theorem SourceCanonicalTables.scopes {env : PEnv} {func : Func}
    (tables : SourceCanonicalTables env func) (scopes : List ScopeId) :
    SourceCanonicalTables { env with scopes := scopes } func :=
  ⟨tables.rootUniverse, tables.rootCount, tables.native, tables.definitions, tables.valueRows, tables.variables,
    tables.annotations, tables.contents, tables.callees⟩

theorem SourceCanonicalTables.access {left right : PEnv} {func : Func}
    (same : left.access = right.access) (tables : SourceCanonicalTables left func) :
    SourceCanonicalTables right func := by
  cases left with
  | mk leftMod leftImpl leftCtx leftScopes =>
      cases right with
      | mk rightMod rightImpl rightCtx rightScopes =>
          have fields : leftMod = rightMod ∧ leftImpl = rightImpl ∧ leftCtx = rightCtx := by
            simpa only [PEnv.access, AccessEnv.mk.injEq] using same
          rcases fields with ⟨rfl, rfl, rfl⟩
          exact tables.scopes rightScopes

end Goose.Lower.Validation.SourceCanonicalRootFloors
