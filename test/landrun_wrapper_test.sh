#!/usr/bin/env bash
set -euo pipefail

# Exercises scripts/landrun-wrapper.sh against a stub Landrun that records the
# argument vector it receives. The wrapper stands between Comparator and the
# real sandbox, so the properties pinned here are the sandbox's own contract:
# the flags Comparator actually sends survive unchanged, and any flag that
# would switch off a Landlock restriction stops the run instead.

repository_root=$(cd "$(dirname "$0")/.." && pwd)
wrapper="$repository_root/scripts/landrun-wrapper.sh"
work_dir=$(mktemp -d)
trap 'rm -rf "$work_dir"' EXIT

stub="$work_dir/landrun-stub.sh"
cat >"$stub" <<'STUB'
#!/usr/bin/env bash
if [ -s "$PALOMAR_TEST_ARGV" ]; then
  printf '%s\n' '---' >>"$PALOMAR_TEST_ARGV"
fi
printf '%s\n' "$@" >>"$PALOMAR_TEST_ARGV"
if [ -n "${PALOMAR_TEST_FAIL_TARGET:-}" ] && \
    [ "${!#}" = "$PALOMAR_TEST_FAIL_TARGET" ]; then
  exit 7
fi
STUB
chmod +x "$stub"

failures=0
export PALOMAR_LANDRUN_BIN="$stub"
export PALOMAR_TEST_ARGV="$work_dir/argv"

report_failure() {
  echo "FAIL: $1" >&2
  failures=$((failures + 1))
}

# Runs the wrapper, capturing status, stderr and the stub's argument vector.
run_wrapper() {
  : >"$PALOMAR_TEST_ARGV"
  set +e
  wrapper_stderr=$("$wrapper" "$@" 2>&1 >/dev/null)
  wrapper_status=$?
  set -e
  wrapper_argv=$(cat "$PALOMAR_TEST_ARGV")
}

assert_passthrough() {
  local description=$1 expected=$2
  shift 2
  run_wrapper "$@"
  if [ "$wrapper_status" -ne 0 ]; then
    report_failure "$description: wrapper exited $wrapper_status: $wrapper_stderr"
  elif [ "$wrapper_argv" != "$expected" ]; then
    report_failure "$description: Landrun received
$wrapper_argv
but expected
$expected"
  fi
}

assert_refused() {
  local description=$1 flag=$2
  shift 2
  run_wrapper "$@"
  if [ "$wrapper_status" -ne 2 ]; then
    report_failure "$description: wrapper exited $wrapper_status, expected 2"
  elif [ -s "$PALOMAR_TEST_ARGV" ]; then
    report_failure "$description: Landrun ran anyway with
$wrapper_argv"
  elif [ "${wrapper_stderr#*"$flag"}" = "$wrapper_stderr" ]; then
    report_failure "$description: refusal does not name $flag: $wrapper_stderr"
  fi
}

# The Solution build isolates both measured peaks, then repeats the identical
# sandbox vector for Comparator's untouched command.
assert_passthrough "Solution peaks are isolated before Comparator's build" \
  '--best-effort
--ro
/
--rw
/dev
-ldd
-add-exec
--env
PATH
--ro
/workspace
--rwx
/workspace/.lake
--rox
/toolchain
--
lake
build
+WPPCompactSyntaxFVExplicitPart001
---
--best-effort
--ro
/
--rw
/dev
-ldd
-add-exec
--env
PATH
--ro
/workspace
--rwx
/workspace/.lake
--rox
/toolchain
--
lake
build
+NFStandard.HailperinAlgebra
---
--best-effort
--ro
/
--rw
/dev
-ldd
-add-exec
--env
PATH
--ro
/workspace
--rwx
/workspace/.lake
--rox
/toolchain
--
lake
build
Solution' \
  --best-effort --ro / --rw /dev -ldd -add-exec --env PATH \
  --ro /workspace --rwx /workspace/.lake --rox /toolchain \
  lake build Solution

# Failure at either isolated build prevents every later invocation.
assert_prebuild_failure() {
  local target=$1 expected=$2
  export PALOMAR_TEST_FAIL_TARGET=$target
  run_wrapper --best-effort lake build Solution
  unset PALOMAR_TEST_FAIL_TARGET
  if [ "$wrapper_status" -ne 7 ]; then
    report_failure "$target failure exits 7, got $wrapper_status: $wrapper_stderr"
  elif [ "$wrapper_argv" != "$expected" ]; then
    report_failure "$target failure reached a later command:
$wrapper_argv"
  fi
}

assert_prebuild_failure +WPPCompactSyntaxFVExplicitPart001 '--best-effort
--
lake
build
+WPPCompactSyntaxFVExplicitPart001'

assert_prebuild_failure +NFStandard.HailperinAlgebra '--best-effort
--
lake
build
+WPPCompactSyntaxFVExplicitPart001
---
--best-effort
--
lake
build
+NFStandard.HailperinAlgebra'

# Commands other than the exact Solution build remain single-pass.
assert_passthrough "Challenge remains a single sandbox invocation" \
  '--best-effort
--
lake
build
Challenge' \
  --best-effort lake build Challenge

assert_passthrough "a near-match Solution command remains single-pass" \
  '--best-effort
--
lake
build
Solution
extra' \
  --best-effort lake build Solution extra

# Landrun uses -add-exec to add the sandboxed binary to --rox. It narrows the
# executable set rather than lifting a restriction, and Comparator sends it on
# every run, so both spellings stay allowed.
assert_passthrough "-add-exec stays allowed" \
  '-add-exec
--
true' \
  -add-exec true
assert_passthrough "--add-exec stays allowed" \
  '--add-exec
--
true' \
  --add-exec true

for flag in --unrestricted-filesystem --unrestricted-network --unrestricted-scoped \
  -unrestricted-filesystem -unrestricted-network -unrestricted-scoped \
  --unrestricted-filesystem=true; do
  assert_refused "$flag is refused" "$flag" --best-effort "$flag" --ro / true
done

assert_refused "an unknown flag is refused" "--brand-new-flag" --brand-new-flag true
assert_refused "a flag missing its value is refused" "--ro" --ro
run_wrapper --best-effort
if [ "$wrapper_status" -ne 2 ]; then
  report_failure "a missing command is refused: wrapper exited $wrapper_status, expected 2"
fi

# Only Landrun's own options are inspected. Everything after the sandboxed
# command belongs to that command and passes through untouched.
assert_passthrough "the sandboxed command keeps its own arguments" \
  '--best-effort
--
solver
--unrestricted-filesystem' \
  --best-effort solver --unrestricted-filesystem

# The Comparator subprocess receives the same explicit Lake worker bound as
# the outer CI job, even though Comparator itself does not forward it.
export LEAN_NUM_THREADS=2
assert_passthrough "the Lake worker bound crosses the sandbox boundary" \
  '--env
LEAN_NUM_THREADS
--best-effort
--
true' \
  --best-effort true
unset LEAN_NUM_THREADS

if [ "$failures" -ne 0 ]; then
  echo "$failures landrun-wrapper.sh check(s) failed" >&2
  exit 1
fi

echo "landrun-wrapper.sh checks passed"
