#!/bin/sh
# Check every line of INDEX against the reference tool.
#
#   check.sh [TOOL]
#
# A line is NAME, the Core module (a path from the repository root), and the
# line `agree` prints for it with --numeric release and with --numeric debug.
# For each, the golden NAME.gir-h.json must be the bytes `lower` prints (twice,
# identically), pass `gir-validate`, survive `gir-reencode` unchanged, and agree
# with the Core module in both profiles. Every Core statement and expression
# tag must occur in some module. Exit status 0 means every check held.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
tool=${1:-$root/semantics/.lake/build/bin/goose-semantics}
work=$root/.work/tmp/gir-golden
mkdir -p "$work"
status=0

fail() {
    echo "FAIL $1" >&2
    status=1
}

while IFS='	' read -r name core release debug; do
    gir=$here/$name.gir-h.json
    "$tool" lower "$root/$core" > "$work/$name.1" || fail "$name: lower failed"
    "$tool" lower "$root/$core" > "$work/$name.2" || fail "$name: lower failed"
    cmp -s "$work/$name.1" "$work/$name.2" || fail "$name: lower is not deterministic"
    cmp -s "$work/$name.1" "$gir" || fail "$name: lower differs from the golden"
    [ "$("$tool" gir-validate "$gir")" = '["ok"]' ] || fail "$name: gir-validate"
    "$tool" gir-reencode "$gir" | cmp -s - "$gir" || fail "$name: gir-reencode changes the bytes"
    [ "$("$tool" agree "$root/$core" "$gir" --numeric release)" = "$release" ] || fail "$name: agree release"
    [ "$("$tool" agree "$root/$core" "$gir" --numeric debug)" = "$debug" ] || fail "$name: agree debug"
done < "$here/INDEX"

tags='e_lit e_bool e_read e_ref e_slice e_len e_un e_bin e_cmp e_and e_or e_not e_conv e_call e_push e_if e_block e_arr e_fill p_local p_global p_deref p_elem v_of v_val b_expr b_end b_none a_val a_ref s_let s_assign s_assign_op s_rebind s_expr s_append s_if s_while s_for_range s_for_each s_ret s_break s_continue s_print s_assert s_abort s_exit pa_text pa_expr'
cores=$(cut -f2 "$here/INDEX" | sed "s|^|$root/|")
for tag in $tags; do
    # shellcheck disable=SC2086
    grep -q "\"$tag\"" $cores || fail "no module uses $tag"
done

# Every instruction, terminator and operand tag of the profile must occur in a golden.
gir_tags='i_int i_bool i_unit i_bin i_un i_cmp i_bcmp i_not i_conv i_next i_slot i_global i_elem i_freeze i_load i_snap i_sview i_vlen i_vslice i_alen i_index i_push i_call i_arr i_fill x_init x_store x_append x_enter x_leave x_print t_br t_condbr t_ret t_abort t_exit pp_text pp_val bd_none bd_val bd_end'
for tag in $gir_tags; do
    # shellcheck disable=SC2046
    grep -q "\"$tag\"" $(cut -f1 "$here/INDEX" | sed "s|\$|.gir-h.json|; s|^|$here/|") || fail "no golden uses $tag"
done

[ "$status" -eq 0 ] && echo "golden: $(wc -l < "$here/INDEX") modules ok"
exit "$status"
