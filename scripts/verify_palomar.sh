#!/usr/bin/env bash
# Verify every prepared Palomar Registry entry in this repository locally.
#
# This is not Palomar's verification and it never contacts the registry.
# It mirrors the important local stages: static readiness, exact Challenge/
# Solution builds, Comparator export, NanoDa replay, and Lean kernel replay.
#
# Usage:
#   scripts/verify_palomar.sh
#   scripts/verify_palomar.sh yws-symmetric
#   scripts/verify_palomar.sh yws-rectangular
#   scripts/verify_palomar.sh --static-only
#   scripts/verify_palomar.sh --fake-landrun
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

add_cached_palomar_tools_to_path() {
    local candidate
    local cache_parent="${PALOMAR_TOOLS_CACHE_PARENT:-$HOME/.cache}"
    local -a candidates=()
    local -a dated=()

    [[ -n "${PALOMAR_TOOLS_BIN:-}" ]] && candidates+=("$PALOMAR_TOOLS_BIN")
    candidates+=("$cache_parent/palomar-tools-latest/bin")

    shopt -s nullglob
    dated=("$cache_parent"/palomar-tools-[0-9]*/bin)
    shopt -u nullglob
    if [[ ${#dated[@]} -gt 0 ]]; then
        while IFS= read -r candidate; do
            candidates+=("$candidate")
        done < <(printf '%s\n' "${dated[@]}" | sort -r)
    fi

    for candidate in "${candidates[@]}"; do
        [[ -d "$candidate" ]] || continue
        if [[ -x "$candidate/comparator" && -x "$candidate/lean4export" \
            && -x "$candidate/nanoda_bin" && -x "$candidate/landrun" ]]; then
            PATH="$PATH:$candidate"
            export PATH
            echo "    added cached Palomar tools to PATH: $candidate"
            return 0
        fi
    done
    return 1
}

ENTRIES=()
STATIC_ONLY=0
FAKE_LANDRUN=0

while [[ $# -gt 0 ]]; do
    case "$1" in
        --all) ;;
        --static-only) STATIC_ONLY=1 ;;
        --fake-landrun) FAKE_LANDRUN=1 ;;
        -h|--help)
            sed -n '2,22p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        -*) echo "unknown option: $1" >&2; exit 2 ;;
        *) ENTRIES+=("$1") ;;
    esac
    shift
done

config_for() {
    case "$1" in
        root) echo "comparator.json" ;;
        *) echo "registry/$1/comparator.json" ;;
    esac
}

if [[ ${#ENTRIES[@]} -eq 0 ]]; then
    [[ -f comparator.json ]] && ENTRIES+=("root")
    if [[ -d registry ]]; then
        while IFS= read -r cfg; do
            ENTRIES+=("$(basename "$(dirname "$cfg")")")
        done < <(find registry -mindepth 2 -maxdepth 2 -name comparator.json | sort)
    fi
fi

if [[ ${#ENTRIES[@]} -eq 0 ]]; then
    echo "no comparator.json at root and none under registry/*/" >&2
    exit 2
fi

# Comparator compares every non-target constant transitively. These preludes
# deliberately elaborate the Challenge vocabulary under Mathlib alone before
# Solution imports the proof development. Keep them source-identical.
PRELUDE_OK=1
if [[ -f scripts/check_solution_preludes.py ]]; then
    echo "======================================================================"
    echo "Comparator vocabulary prelude check"
    echo "======================================================================"
    python3 scripts/check_solution_preludes.py || PRELUDE_OK=0
fi

# Build the exact modules selected by the requested Comparator configurations.
BUILD_TARGETS=()
for entry in "${ENTRIES[@]}"; do
    cfg="$(config_for "$entry")"
    if [[ ! -f "$cfg" ]]; then
        continue
    fi
    while IFS= read -r module; do
        [[ -n "$module" ]] && BUILD_TARGETS+=("$module")
    done < <(python3 - "$cfg" <<'PY'
import json
import pathlib
import sys
cfg = json.loads(pathlib.Path(sys.argv[1]).read_text())
for key in ("challenge_module", "solution_module"):
    value = cfg.get(key)
    if isinstance(value, str) and value:
        print(value)
PY
    )
done

# Deduplicate while preserving order.
if [[ ${#BUILD_TARGETS[@]} -gt 0 ]]; then
    mapfile -t BUILD_TARGETS < <(printf '%s\n' "${BUILD_TARGETS[@]}" | awk '!seen[$0]++')
fi

echo "======================================================================"
echo "build: ${BUILD_TARGETS[*]:-<none selected>}"
echo "======================================================================"
BUILD_OK=$PRELUDE_OK
if [[ ${#BUILD_TARGETS[@]} -eq 0 ]]; then
    echo "no Challenge/Solution modules selected by requested comparator configs" >&2
    BUILD_OK=0
else
    lake build "${BUILD_TARGETS[@]}" || BUILD_OK=0
fi

FAILED=()
for entry in "${ENTRIES[@]}"; do
    cfg="$(config_for "$entry")"
    echo "======================================================================"
    echo "palomar entry: $entry  ($cfg)"
    echo "======================================================================"
    if [[ ! -f "$cfg" ]]; then
        echo "  no such entry: $cfg" >&2
        FAILED+=("$entry (missing config)")
        continue
    fi

    ok=$BUILD_OK
    [[ $BUILD_OK -eq 1 ]] || echo "--- build/prelude FAILED above; later stages are not meaningful"

    echo "--- 1/3 static preflight"
    if [[ "$entry" == "root" ]]; then
        python3 scripts/check_palomar_readiness.py --entry root || ok=0
    else
        python3 scripts/check_palomar_readiness.py --entry "$entry" || ok=0
    fi

    echo "--- 2/3 build: done above"

    if [[ $STATIC_ONLY -eq 1 ]]; then
        echo "--- 3/3 comparator: skipped (--static-only)"
        echo "    Not a pass. The exporter is ground truth and did not run."
    else
        echo "--- 3/3 comparator + NanoDa"
        if ! command -v comparator >/dev/null 2>&1 \
            || ! command -v lean4export >/dev/null 2>&1 \
            || ! command -v nanoda_bin >/dev/null 2>&1 \
            || { [[ $FAKE_LANDRUN -eq 0 && -z "${COMPARATOR_LANDRUN:-}" ]] \
                && ! command -v landrun >/dev/null 2>&1; }; then
            add_cached_palomar_tools_to_path || true
        fi

        if ! command -v comparator >/dev/null 2>&1; then
            echo "    comparator was not found on PATH or in a cached Palomar tool bundle."
            echo "    Run scripts/build_verification_tools.sh."
            ok=0
        elif ! command -v lean4export >/dev/null 2>&1; then
            echo "    lean4export was not found on PATH or in a cached Palomar tool bundle."
            echo "    Run scripts/build_verification_tools.sh."
            ok=0
        elif ! command -v nanoda_bin >/dev/null 2>&1; then
            echo "    nanoda_bin was not found on PATH or in a cached Palomar tool bundle."
            echo "    NanoDa is the independent second kernel; refusing to report a pass without it."
            echo "    Run scripts/build_verification_tools.sh."
            ok=0
        elif [[ $FAKE_LANDRUN -eq 0 && -z "${COMPARATOR_LANDRUN:-}" ]] \
            && ! command -v landrun >/dev/null 2>&1; then
            echo "    landrun was not found on PATH or in a cached Palomar tool bundle."
            echo "    Run scripts/build_verification_tools.sh or pass --fake-landrun."
            ok=0
        else
            if [[ $FAKE_LANDRUN -eq 1 && -z "${COMPARATOR_LANDRUN:-}" ]]; then
                echo "    landrun is bypassed (--fake-landrun): the exporter runs unsandboxed."
                SHIM="$(mktemp)"
                cat > "$SHIM" <<'SHIM_EOF'
#!/usr/bin/env bash
set -euo pipefail
value_flags=(--ro --rox --rw --rwx --bind-tcp --connect-tcp --log-level --env)
while [[ $# -gt 0 ]]; do
  case "$1" in
    --) shift; break ;;
    -*)
      for vf in "${value_flags[@]}"; do
        if [[ "$1" == "$vf" ]]; then
          shift
          break
        fi
      done
      shift
      ;;
    *) break ;;
  esac
done
[[ $# -gt 0 ]] || { echo "landrun shim: no command given" >&2; exit 2; }
echo "NOT LANDRUN: running unsandboxed: $*" >&2
exec "$@"
SHIM_EOF
                chmod +x "$SHIM"
                export COMPARATOR_LANDRUN="$SHIM"
                trap 'rm -f "$SHIM"' EXIT
            fi
            lake env comparator "$cfg" || ok=0
        fi
    fi

    [[ $ok -eq 1 ]] || FAILED+=("$entry")
    echo
done

echo "======================================================================"
if [[ ${#FAILED[@]} -eq 0 ]]; then
    echo "palomar verify: OK for ${#ENTRIES[@]} entry/entries"
    echo
    echo "  Locally verified only. This is not Palomar verification, acceptance,"
    echo "  or registration. The maintainer reviews the prepared commit and submits."
    exit 0
fi

echo "palomar verify: FAILED for ${#FAILED[@]} of ${#ENTRIES[@]}: ${FAILED[*]}"
exit 1
