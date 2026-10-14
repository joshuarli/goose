#ifdef NDEBUG
#undef NDEBUG
#endif
#include "../src/includes.h"
#include "../src/utils.h"
#include "../src/ident/sha256.h"
#include "../src/units/contract.h"

using namespace goose;

static UnitContractValues ContractValues() {
    UnitContractValues values;
    values.goose_digest = string(64, 'a');
    values.runtime_version = "runtime-a";
    values.args = { "-O2", "-DX=1" };
    values.c_compiler_digest = string(64, 'b');
    values.c_compiler_version = "17.1";
    values.c_compiler_name = "gcc";
    values.c_compiler_style = "cc";
    values.c_flags = { "-O2" };
    values.system_libs = { "-lm", "-pthread" };
    values.target = { "x86_64", "unix", 8 };
    values.environment = { { "GOOSE_STDLIB", "" }, { "GOOSE_CC", "" },
                           { "GOOSE_RUNTIME", "" } };
    return values;
}

static void TestContractDimensionsSelectStores() {
    const auto builddir = string("/build/program");
    const auto original = MakeContract(ContractValues());
    const auto original_store = UnitStoreDirectory(builddir, original);
    assert(original.digest == "7eb67bee685107f02796d89b7927fb0c3e751460b2e7b590914a2b01634f5d5d");
    assert(MakeContract(ContractValues()).digest == original.digest);
    assert(UnitStoreDirectory(builddir, original) == original_store);

    auto c_flags = ContractValues();
    c_flags.c_flags.push_back("-fno-omit-frame-pointer");
    auto with_c_flags = MakeContract(c_flags);
    assert(with_c_flags.digest != original.digest);
    assert(UnitStoreDirectory(builddir, with_c_flags) != original_store);

    auto target = ContractValues();
    target.target.arch = "aarch64";
    auto with_target = MakeContract(target);
    assert(with_target.digest != original.digest);
    assert(UnitStoreDirectory(builddir, with_target) != original_store);

    auto runtime = ContractValues();
    runtime.runtime_version = "runtime-b";
    auto with_runtime = MakeContract(runtime);
    assert(with_runtime.digest != original.digest);
    assert(UnitStoreDirectory(builddir, with_runtime) != original_store);

    assert(UnitStoreDirectory(builddir, MakeContract(ContractValues())) == original_store);
}

int main() {
    TestContractDimensionsSelectStores();
}
