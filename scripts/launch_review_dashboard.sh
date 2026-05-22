#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
DEFAULT_HOST="127.0.0.1"
DEFAULT_PORT="8765"

PAPER=""
SLICE=""
CHECK_ONLY="false"
HOST="${REVIEW_DASHBOARD_HOST:-$DEFAULT_HOST}"
PORT="${REVIEW_DASHBOARD_PORT:-$DEFAULT_PORT}"

if [ -z "${REVIEW_DASHBOARD_HOST:-}" ] && { [ -n "${WSL_DISTRO_NAME:-}" ] || [ -n "${WSL_INTEROP:-}" ] || grep -qi "microsoft" /proc/version >/dev/null 2>&1; }; then
  HOST="0.0.0.0"
fi

is_wsl() {
  [ -n "${WSL_DISTRO_NAME:-}" ] || [ -n "${WSL_INTEROP:-}" ] || grep -qi "microsoft" /proc/version >/dev/null 2>&1
}

get_wsl_host() {
  awk '/^nameserver / { print $2; exit }' /etc/resolv.conf 2>/dev/null || true
}

get_wsl_guest_host() {
  local candidate

  if command -v hostname >/dev/null 2>&1; then
    for candidate in $(hostname -I 2>/dev/null || true); do
      case "$candidate" in
        *:* | 127.* | 169.254.* | 0.0.0.0)
          continue
          ;;
        *)
          printf "%s" "$candidate"
          return 0
          ;;
      esac
    done
  fi

  if command -v ip >/dev/null 2>&1; then
    ip -4 -o addr show scope global 2>/dev/null \
      | awk '{ split($4, a, "/"); if (a[1] !~ /^(127\.|169\.254\.|0\.0\.0\.0)/) { print a[1]; exit } }'
  fi
}

is_unusable_wsl_host() {
  local host="$1"
  case "$host" in
    "" | "10.255.255.254" | 127.* | 169.254.* | "0.0.0.0")
      return 0
      ;;
  esac
  return 1
}

normalize_wsl_host_url() {
  local host="$1"
  printf "%s" "${host// /}"
}

open_windows_url() {
  local url="$1"
  local _out

  if command -v cmd.exe >/dev/null 2>&1; then
    if _out=$(cmd.exe /c start "" "$url" 2>&1); then
      return 0
    fi
    echo "cmd.exe could not open $url"
    if [ -n "$_out" ]; then
      printf '  stderr: %s\n' "$_out"
    fi
  fi

  if command -v powershell.exe >/dev/null 2>&1; then
    if _out=$(powershell.exe -NoProfile -Command "Start-Process '$url'" 2>&1); then
      return 0
    fi
    echo "powershell.exe could not open $url"
    if [ -n "$_out" ]; then
      printf '  stderr: %s\n' "$_out"
    fi
  fi

  if command -v explorer.exe >/dev/null 2>&1; then
    if _out=$(explorer.exe "$url" 2>&1); then
      return 0
    fi
    echo "explorer.exe could not open $url"
    if [ -n "$_out" ]; then
      printf '  stderr: %s\n' "$_out"
    fi
  fi

  return 1
}

open_in_browser() {
  local urls=("$@")
  local url
  local first_url=""
  local opened_any=0

  for url in "${urls[@]}"; do
    [ -n "$url" ] || continue
    first_url="${first_url:-$url}"
    if is_wsl; then
      if open_windows_url "$url"; then
        opened_any=1
      fi
    else
      if command -v xdg-open >/dev/null 2>&1; then
        if xdg-open "$url" >/dev/null 2>&1; then
          return
        fi
      fi
    fi
  done

  if is_wsl && [ "$opened_any" -eq 1 ]; then
    return
  fi

  if [ -n "$first_url" ] && command -v python3 >/dev/null 2>&1; then
    if python3 - "$first_url" <<'PY' >/dev/null 2>&1
import sys
import webbrowser

try:
    if webbrowser.open(sys.argv[1], new=2):
        pass
except Exception:
    pass
PY
    then
      return
    fi
  fi

  echo "Could not auto-open any browser. Open one of these URLs manually:"
  for url in "${urls[@]}"; do
    [ -n "$url" ] && echo "  - ${url}"
  done
}

check_bind_capability() {
  local host="$1"
  local port="$2"
  python3 - "$host" "$port" <<'PY'
import sys
import socket

host = sys.argv[1]
port = int(sys.argv[2])
sock = None
try:
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        sock.bind((host, port))
    except OSError as exc:
        print(f"Cannot bind to {host}:{port}: {exc}")
        sys.exit(1)
except Exception as exc:
    print(f"Cannot create socket for {host}:{port}: {exc}")
    sys.exit(1)
finally:
    try:
        if sock is not None:
            sock.close()
    except Exception:
        pass
PY
  return $?
}

dashboard_run() {
  local -n args_ref=$1
  if [ -x "$DASHBOARD_SCRIPT" ]; then
    "$DASHBOARD_SCRIPT" "${args_ref[@]}"
  else
    python3 "$DASHBOARD_SCRIPT" "${args_ref[@]}"
  fi
}

wait_for_local_http() {
  local target="$1"
  local attempts="${2:-${REVIEW_DASHBOARD_READY_ATTEMPTS:-90}}"
  local delay="${3:-${REVIEW_DASHBOARD_READY_DELAY:-0.5}}"
  local i=0

  command -v curl >/dev/null 2>&1 || return 0
  while [ "$i" -lt "$attempts" ]; do
    if curl -fsS --max-time 2 "$target" >/dev/null 2>&1; then
      return 0
    fi
    sleep "$delay"
    i=$((i + 1))
  done
  return 1
}

append_unique_url() {
  local -n urls_ref=$1
  local new_url="$2"
  local existing

  [ -n "$new_url" ] || return 0
  for existing in "${urls_ref[@]}"; do
    if [ "$existing" = "$new_url" ]; then
      return 0
    fi
  done
  urls_ref+=("$new_url")
}

show_help() {
  cat <<'EOF'
Usage: launch_review_dashboard.sh [--paper PAPER] [--slice SLICE] [--host HOST] [--port PORT] [--check]

Start the review dashboard for one paper and open it in a browser tab when possible.
If --paper is omitted, the script infers the paper from the current directory.
Use --slice to review one slice from review_slices.json.
Set --check to run launch-time validation only and exit with status 1 when any
theorem needs an initial review or a refresh.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --paper)
      PAPER="$2"
      shift 2
      ;;
    --slice)
      SLICE="$2"
      shift 2
      ;;
    --host)
      HOST="$2"
      shift 2
      ;;
    --port)
      PORT="$2"
      shift 2
      ;;
    --check)
      CHECK_ONLY="true"
      shift
      ;;
    -h|--help)
      show_help
      exit 0
      ;;
    *)
      echo "Unknown option: $1" >&2
      show_help
      exit 1
      ;;
  esac
done

if [ -z "$PAPER" ]; then
  if [ -f "PaperInterface.lean" ]; then
    PAPER="$(basename "$(cd -P "." && pwd)")"
  else
    echo "Could not infer paper folder. Run from a paper folder or pass --paper." >&2
    exit 1
  fi
fi

PAPER_PATH="${ROOT_DIR}/papers/${PAPER}"
LOG_FILE="${PAPER_PATH}/.review_traces/review-dashboard.log"

if [ ! -d "$PAPER_PATH" ] || [ ! -f "${PAPER_PATH}/PaperInterface.lean" ]; then
  echo "No PaperInterface.lean found for paper '${PAPER}' under papers/." >&2
  exit 1
fi

mkdir -p "$(dirname "$LOG_FILE")"

DASHBOARD_SCRIPT="${ROOT_DIR}/scripts/review_dashboard.py"
if [ ! -f "$DASHBOARD_SCRIPT" ]; then
  echo "Missing script: $DASHBOARD_SCRIPT" >&2
  exit 1
fi
if [ ! -x "$DASHBOARD_SCRIPT" ] && [ -w "$DASHBOARD_SCRIPT" ]; then
  chmod +x "$DASHBOARD_SCRIPT" || true
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo "Could not find python3 in PATH; required to launch the dashboard." >&2
  exit 1
fi

if [ "$HOST" = "0.0.0.0" ]; then
  URL_HOST="127.0.0.1"
else
  URL_HOST="$HOST"
fi
URL="http://${URL_HOST}:${PORT}/"
OPEN_URLS=("$URL")
if is_wsl; then
  WSL_GUEST_HOST="$(normalize_wsl_host_url "$(get_wsl_guest_host)")"
  if ! is_unusable_wsl_host "$WSL_GUEST_HOST"; then
    append_unique_url OPEN_URLS "http://${WSL_GUEST_HOST}:${PORT}/"
  fi
  WSL_DNS_HOST="$(normalize_wsl_host_url "$(get_wsl_host)")"
  if ! is_unusable_wsl_host "$WSL_DNS_HOST"; then
    append_unique_url OPEN_URLS "http://${WSL_DNS_HOST}:${PORT}/"
  fi
fi
ARGS=(--paper "$PAPER" --host "$HOST" --port "$PORT" --serve)
if [ -n "$SLICE" ]; then
  ARGS+=(--slice "$SLICE")
fi

if [ "$CHECK_ONLY" = "true" ]; then
  CHECK_ARGS=(--paper "$PAPER" --check)
  if [ -n "$SLICE" ]; then
    CHECK_ARGS+=(--slice "$SLICE")
  fi
  dashboard_run CHECK_ARGS
  exit $?
fi

printf 'Starting dashboard for %s...\n' "$PAPER"
if [ -n "$SLICE" ]; then
  printf 'Review slice: %s\n' "$SLICE"
fi
printf 'Local URL: %s\n' "$URL"
if is_wsl; then
  printf 'Windows browser URLs to try:\n'
  for i in "${!OPEN_URLS[@]}"; do
    printf '  - %s\n' "${OPEN_URLS[$i]}"
  done
else
  printf 'URL: %s\n' "$URL"
fi
printf 'Logs: %s\n' "$LOG_FILE"

if ! check_bind_capability "$HOST" "$PORT"; then
  echo "Dashboard server cannot bind to ${HOST}:${PORT}." >&2
  echo "Try a different --port or run with --check for precheck-only mode." >&2
  echo "Inspect startup logs at: $LOG_FILE" >&2
  exit 1
fi

(
  dashboard_run ARGS
) >>"$LOG_FILE" 2>&1 &
PID=$!

cleanup() {
  if kill -0 "$PID" >/dev/null 2>&1; then
    kill "$PID" >/dev/null 2>&1 || true
    wait "$PID" >/dev/null 2>&1 || true
  fi
}
trap cleanup EXIT INT TERM

sleep 1

if ! kill -0 "$PID" >/dev/null 2>&1; then
  echo "Failed to start the dashboard server." >&2
  echo "Inspect startup logs at: $LOG_FILE" >&2
  if [ -f "$LOG_FILE" ]; then
    tail -n 40 "$LOG_FILE" >&2
  fi
  exit 1
fi

if ! wait_for_local_http "$URL"; then
  echo "Warning: dashboard process is running, but the local endpoint did not respond on ${URL}."
  echo "Large paper interfaces can take longer to initialize; inspect startup logs at: $LOG_FILE"
  if is_wsl; then
    echo "If the page is not loading from Windows, try each printed Windows browser URL."
  fi
fi

open_in_browser "${OPEN_URLS[@]}"

echo "Keep this terminal open to keep the dashboard running. Press Ctrl-C to stop."
wait "$PID"
