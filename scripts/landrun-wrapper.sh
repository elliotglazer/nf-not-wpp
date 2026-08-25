#!/usr/bin/env bash
set -euo pipefail

# Landrun's current CLI needs an explicit outer `--` before the sandboxed
# command. Comparator constructs Landrun's options itself but does not add that
# delimiter. Without it, Landrun consumes lean4export's own `--` separator.
landrun_binary=${PALOMAR_LANDRUN_BIN:?PALOMAR_LANDRUN_BIN must name the pinned Landrun binary}
landrun_options=()

# Comparator deliberately forwards only a small allowlist into Landrun. Carry
# the repository's explicit Lake worker bound through that boundary so its
# internal `lake build Solution` cannot fan out beyond the audited setting.
if [ -n "${LEAN_NUM_THREADS:-}" ]; then
  landrun_options+=(--env LEAN_NUM_THREADS)
fi

# Landrun's --unrestricted-* flags each switch off a whole class of Landlock
# restriction. Refuse them so a dependency change cannot silently widen the
# sandbox.
while [ "$#" -gt 0 ]; do
  case "$1" in
    -unrestricted-*|--unrestricted-*)
      echo "error: Landrun option $1 switches off part of the sandbox" >&2
      echo "Comparator must not request it; refusing to run $landrun_binary" >&2
      exit 2
      ;;
    --best-effort|-ldd|--ldd|-add-exec|--add-exec|--ignore-missing|--log-disable-originating|--log-enable-subprocesses|--log-disable-subdomains)
      landrun_options+=("$1")
      shift
      ;;
    --log-level|--ro|--rox|--rw|--rwx|--unix|--bind-tcp|--connect-tcp|--env)
      if [ "$#" -lt 2 ]; then
        echo "error: Landrun option $1 is missing its value" >&2
        exit 2
      fi
      landrun_options+=("$1" "$2")
      shift 2
      ;;
    -*)
      echo "error: unrecognized Landrun option $1; update scripts/landrun-wrapper.sh" >&2
      exit 2
      ;;
    *)
      break
      ;;
  esac
done

if [ "$#" -eq 0 ]; then
  echo "error: Comparator supplied no sandboxed command" >&2
  exit 2
fi

# Isolate the two measured memory peaks before Lake schedules the full Solution
# graph.  Both use the same sandbox and must succeed before the original build.
if [ "$#" -eq 3 ] && [ "$1" = lake ] && [ "$2" = build ] && [ "$3" = Solution ]; then
  for prebuild_target in \
    +WPPCompactSyntaxFVExplicitPart001 \
    +NFStandard.HailperinAlgebra \
    +NFStandard.Equivalence; do
    "$landrun_binary" "${landrun_options[@]}" -- \
      lake build "$prebuild_target"
  done
fi

exec "$landrun_binary" "${landrun_options[@]}" -- "$@"
