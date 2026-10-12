#!/bin/sh
# Check every case of INDEX against goose-semantics. See INDEX for the format.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
tool=${1:-$root/semantics/.lake/build/bin/goose-semantics}
work=$root/.work/tmp/share-index
mkdir -p "$work"
cd "$here"
failures=0
fail() { echo "FAIL $*"; failures=$((failures + 1)); }
tab=$(printf '\t')
while IFS=$tab read -r kind a b c d; do
  case $kind in ''|'#'*) continue ;; esac
  case $kind in
    propose)
      out=$work/$(basename "$a").shared.json
      if ! "$tool" share --propose "$a" > "$out"; then fail "propose $a: exit $?"; continue; fi
      got=$("$tool" share "$a" "$out") || { fail "propose $a: checker said $got"; continue; }
      [ "$got" = "[\"ok\",$b]" ] || { fail "propose $a: expected [\"ok\",$b], got $got"; continue; }
      if [ "$c" = unchanged ]; then
        cmp -s "$a" "$out" || { fail "propose $a: output differs from the input"; continue; }
      else
        ! cmp -s "$a" "$out" || { fail "propose $a: nothing was merged"; continue; }
      fi
      before=$("$tool" run "$a"); after=$("$tool" run "$out")
      case $before in '["done"'*) ;; *) fail "propose $a: unshared run gave $before"; continue ;; esac
      [ "$before" = "$after" ] || { fail "propose $a: run differs: $before / $after"; continue; }
      echo "ok   propose $a ($b implementations, $c)"
      ;;
    check)
      got=$("$tool" share "$a" "$b"); status=$?
      if [ "$status" = "$c" ] && [ "$got" = "$d" ]; then echo "ok   check $a $b"
      else fail "check $a $b: expected $c $d, got $status $got"; fi
      ;;
    differs)
      x=$("$tool" run "$a"); y=$("$tool" run "$b")
      case $x in '["done"'*) ;; *) fail "differs $a: gave $x"; continue ;; esac
      case $y in '["done"'*) ;; *) fail "differs $b: gave $y"; continue ;; esac
      if [ "$x" != "$y" ]; then echo "ok   differs $a $b"; else fail "differs $a $b: same output $x"; fi
      ;;
    *) fail "unknown kind $kind" ;;
  esac
done < INDEX
[ "$failures" = 0 ] && echo "all cases passed"
exit "$failures"
