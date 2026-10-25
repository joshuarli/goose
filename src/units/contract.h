#pragma once

namespace goose {

struct UnitContractTarget {
    string arch, os;
    size_t pointer_bytes = 0;
};

struct UnitContractValues {
    string goose_digest, runtime_version;
    vector<string> args;
    string c_compiler_digest, c_compiler_version, c_compiler_name, c_compiler_style;
    vector<string> c_flags, system_libs;
    UnitContractTarget target;
    vector<pair<string, string>> environment;
};

struct UnitContract {
    string text, digest;
    vector<string> c_flags, system_libs;
};

inline UnitContract MakeContract(const UnitContractValues &values) {
    UnitContract contract;
    contract.c_flags = values.c_flags;
    contract.system_libs = values.system_libs;
    string args_text;
    for (auto &arg : values.args) args_text += arg + "\x1f";
    contract.text = cat("goose-contract/1\ngoose ", values.goose_digest,
                        "\nruntime ", values.runtime_version, "\nargs ", args_text,
                        "\ncc-digest ", values.c_compiler_digest,
                        "\ncc-version ", values.c_compiler_version,
                        "\ncc-name ", values.c_compiler_name, " ", values.c_compiler_style, "\n");
    for (auto &flag : values.c_flags) contract.text += "cflag " + flag + "\n";
    for (auto &library : values.system_libs) contract.text += "lib " + library + "\n";
    contract.text += cat("arch ", values.target.arch, "\nos ", values.target.os,
                         "\npointer ", values.target.pointer_bytes, "\n");
    for (auto &[name, value] : values.environment)
        contract.text += cat("env ", name, "=", value, "\n");
    contract.digest = Sha256::Of(contract.text).Hex();
    return contract;
}

inline string UnitStoreDirectory(const string &builddir, const UnitContract &contract) {
    return cat(builddir, "/store/", contract.digest.substr(0, 16));
}

}
