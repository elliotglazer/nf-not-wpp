#!/usr/bin/env bash
set -euo pipefail

# Based on PalomarTemplate main at
# 128a6c5ce5f48622e69927ccd639cbff401022e8.
# The lean4export pin is the exact v4.30.0-rc2 tag commit, matching this
# candidate's lean-toolchain rather than the template's v4.32.0 toolchain.

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cache_root=${PALOMAR_COMPARATOR_CACHE:-"$repository_root/.cache/palomar-comparator"}
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"
comparator_commit=68a064109f01c08f47c8edc9f51d6a2bbffaa188
lean4export_commit=12581a6b680d8478175596338eb2d53383a323e3
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

for required_command in cargo git go lake python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run Comparator" >&2
    exit 1
  fi
done

python3 - "$repository_root/comparator.json" <<'PY'
import json
import pathlib
import sys

config_path = pathlib.Path(sys.argv[1])
try:
    config = json.loads(config_path.read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {config_path}: {error}", file=sys.stderr)
    raise SystemExit(1)
if not isinstance(config, dict) or config.get("enable_nanoda") is not True:
    print(
        f"error: {config_path}: enable_nanoda must be exactly true; "
        "the NanoDa replay is required",
        file=sys.stderr,
    )
    raise SystemExit(1)
PY

mkdir -p "$cache_root" "$bin_dir"
checkout_exact() {
  local repository=$1
  local destination=$2
  local commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none "$repository" "$destination"
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
}

checkout_exact https://github.com/leanprover/lean4export.git "$lean4export_dir" "$lean4export_commit"
if [ ! -f "$lean4export_dir/lean-toolchain" ]; then
  echo "error: pinned lean4export revision $lean4export_commit has no lean-toolchain file" >&2
  echo "select a lean4export revision that declares its Lean toolchain" >&2
  exit 1
fi
project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
lean4export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "$lean4export_toolchain" ]; then
  echo "error: project toolchain $project_toolchain does not match" >&2
  echo "the pinned lean4export toolchain $lean4export_toolchain" >&2
  echo "update lean4export_commit when changing lean-toolchain, then review" >&2
  echo "Comparator and NanoDa compatibility with the export format" >&2
  exit 1
fi

checkout_exact https://github.com/leanprover/comparator.git "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"

GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"

(cd "$comparator_dir" && lake build comparator)
(cd "$lean4export_dir" && lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)
cd "$repository_root"
lake exe cache get

telemetry_file_value() {
  local path=$1
  local value=
  if [ -r "$path" ] && IFS= read -r value < "$path" 2>/dev/null; then
    printf '%s' "${value:-na}"
  else
    printf 'na'
  fi
}

telemetry_snapshot() {
  local phase=${1:-interval}
  local timestamp=na
  local mem_available_kib=na
  local swap_total_kib=na
  local swap_free_kib=na
  local cgroup_dir=
  local cgroup_memory_current=na
  local cgroup_memory_max=na
  local cgroup_swap_current=na
  local cgroup_swap_max=na
  local cgroup_oom=na
  local cgroup_oom_kill=na
  local repository_available_kib=na
  local filesystem_output=
  local filesystem_line=
  local process_status=
  local process_name=
  local process_rss=0
  local lean_process_count=0
  local lean_rss_kib=0
  local top_process_name=na
  local top_process_rss_kib=0
  local key=
  local value=

  if command -v date >/dev/null 2>&1; then
    timestamp=$(date -u '+%Y-%m-%dT%H:%M:%SZ' 2>/dev/null || true)
    timestamp=${timestamp:-na}
  fi

  if [ -r /proc/meminfo ]; then
    while read -r key value _; do
      case "$key" in
        MemAvailable:)
          case "$value" in
            ''|*[!0-9]*) ;;
            *) mem_available_kib=$value ;;
          esac
          ;;
        SwapTotal:)
          case "$value" in
            ''|*[!0-9]*) ;;
            *) swap_total_kib=$value ;;
          esac
          ;;
        SwapFree:)
          case "$value" in
            ''|*[!0-9]*) ;;
            *) swap_free_kib=$value ;;
          esac
          ;;
      esac
    done < /proc/meminfo 2>/dev/null || true
  fi

  if [ -r /proc/self/cgroup ]; then
    while IFS=: read -r key value process_status; do
      if [ "$key" = 0 ] && [ -z "$value" ]; then
        cgroup_dir="/sys/fs/cgroup${process_status}"
        break
      fi
    done < /proc/self/cgroup 2>/dev/null || true
  fi
  if [ -n "$cgroup_dir" ]; then
    cgroup_memory_current=$(telemetry_file_value "$cgroup_dir/memory.current")
    cgroup_memory_max=$(telemetry_file_value "$cgroup_dir/memory.max")
    cgroup_swap_current=$(telemetry_file_value "$cgroup_dir/memory.swap.current")
    cgroup_swap_max=$(telemetry_file_value "$cgroup_dir/memory.swap.max")
    if [ -r "$cgroup_dir/memory.events" ]; then
      while read -r key value _; do
        case "$key" in
          oom) cgroup_oom=$value ;;
          oom_kill) cgroup_oom_kill=$value ;;
        esac
      done < "$cgroup_dir/memory.events" 2>/dev/null || true
    fi
  fi

  if command -v df >/dev/null 2>&1; then
    filesystem_output=$(df -Pk "$repository_root" 2>/dev/null || true)
    while IFS= read -r filesystem_line; do
      case "$filesystem_line" in
        Filesystem*) continue ;;
      esac
      read -r _ _ _ repository_available_kib _ <<< "$filesystem_line" || true
    done <<< "$filesystem_output"
    case "$repository_available_kib" in
      ''|*[!0-9]*) repository_available_kib=na ;;
    esac
  fi

  for process_status in /proc/[0-9]*/status; do
    [ -r "$process_status" ] || continue
    process_name=unknown
    process_rss=0
    while read -r key value _; do
      case "$key" in
        Name:) process_name=${value:-unknown} ;;
        VmRSS:)
          case "$value" in
            ''|*[!0-9]*) process_rss=0 ;;
            *) process_rss=$value ;;
          esac
          ;;
      esac
    done < "$process_status" 2>/dev/null || true
    if [ "$process_rss" -gt "$top_process_rss_kib" ]; then
      top_process_name=$process_name
      top_process_rss_kib=$process_rss
    fi
    case "$process_name" in
      lean|lean.exe)
        lean_process_count=$((lean_process_count + 1))
        lean_rss_kib=$((lean_rss_kib + process_rss))
        ;;
    esac
  done

  printf '%s\n' \
    "PALOMAR_RESOURCE timestamp=$timestamp phase=$phase mem_available_kib=$mem_available_kib swap_total_kib=$swap_total_kib swap_free_kib=$swap_free_kib cgroup_memory_current_bytes=$cgroup_memory_current cgroup_memory_max_bytes=$cgroup_memory_max cgroup_swap_current_bytes=$cgroup_swap_current cgroup_swap_max_bytes=$cgroup_swap_max cgroup_oom=$cgroup_oom cgroup_oom_kill=$cgroup_oom_kill repository_available_kib=$repository_available_kib lean_processes=$lean_process_count lean_rss_kib=$lean_rss_kib top_process=$top_process_name top_rss_kib=$top_process_rss_kib"
}

telemetry_monitor() {
  local sleeper_pid=
  if ! command -v sleep >/dev/null 2>&1; then
    telemetry_snapshot interval || true
    return 0
  fi
  trap 'trap - TERM USR1; if [ -n "${sleeper_pid:-}" ]; then kill "$sleeper_pid" 2>/dev/null || true; wait "$sleeper_pid" 2>/dev/null || true; fi; exit 0' USR1
  trap 'telemetry_snapshot term || true; trap - TERM USR1; if [ -n "${sleeper_pid:-}" ]; then kill "$sleeper_pid" 2>/dev/null || true; wait "$sleeper_pid" 2>/dev/null || true; fi; exit 143' TERM
  while true; do
    telemetry_snapshot interval || true
    sleep 15 &
    sleeper_pid=$!
    wait "$sleeper_pid" || true
    sleeper_pid=
  done
}

telemetry_pid=
stop_telemetry() {
  if [ -n "${telemetry_pid:-}" ]; then
    kill -USR1 "$telemetry_pid" 2>/dev/null || true
    wait "$telemetry_pid" 2>/dev/null || true
    telemetry_pid=
  fi
}

on_comparator_term() {
  telemetry_snapshot term || true
  exit 143
}

telemetry_monitor &
telemetry_pid=$!
trap stop_telemetry EXIT
trap on_comparator_term TERM

if PALOMAR_LANDRUN_BIN="$bin_dir/landrun" \
  COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
  COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
  COMPARATOR_LANDRUN="$repository_root/scripts/landrun-wrapper.sh" \
    lake env "$comparator_dir/.lake/build/bin/comparator" comparator.json; then
  comparator_status=0
else
  comparator_status=$?
fi

trap - TERM
if [ "$comparator_status" -eq 143 ]; then
  telemetry_snapshot exit-143 || true
fi
stop_telemetry
trap - EXIT
exit "$comparator_status"
