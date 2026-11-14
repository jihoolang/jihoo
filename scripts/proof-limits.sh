#!/usr/bin/env bash
# Keep proof/compiler process trees away from the terminal's cgroup. All local
# checkouts share the lock and aggregate slice, including sub-agent checkouts.
set -euo pipefail

if [[ $# -eq 0 ]]; then
  printf 'usage: %s COMMAND [ARGUMENT ...]\n' "$0" >&2
  exit 2
fi

export LEAN_NUM_THREADS=1
export JIHOO_CODEGEN_UNITS=1

# Nested checks already belong to the limited job and must not acquire its lock.
if [[ -r /proc/self/cgroup ]] &&
    [[ $(< /proc/self/cgroup) == *'/jihoo-proof-jobs.slice/'* ]]; then
  exec "$@"
fi

for dependency in flock systemd-run systemctl; do
  if ! command -v "$dependency" >/dev/null; then
    printf 'Cannot enforce proof job memory limits: missing %s.\n' "$dependency" >&2
    exit 75
  fi
done

if ! systemctl --user show-environment >/dev/null 2>&1; then
  printf 'Cannot enforce proof job memory limits: user systemd is unavailable.\n' >&2
  exit 75
fi

# Runtime properties disappear on reboot. Reapply the aggregate cap before
# admitting work; initializing an absent slice runs only the harmless true job.
if ! systemctl --user set-property --runtime jihoo-proof-jobs.slice \
    MemoryHigh=6G MemoryMax=8G MemorySwapMax=512M TasksMax=64 2>/dev/null; then
  systemd-run --user --scope --quiet --slice=jihoo-proof-jobs.slice \
    -p MemoryMax=6G -p MemorySwapMax=512M -- true
  systemctl --user set-property --runtime jihoo-proof-jobs.slice \
    MemoryHigh=6G MemoryMax=8G MemorySwapMax=512M TasksMax=64
fi

proof_lock="${XDG_RUNTIME_DIR:-/tmp}/jihoo-proof-jobs-$(id -u).lock"
exec flock "$proof_lock" systemd-run --user --scope --quiet \
  --slice=jihoo-proof-jobs.slice \
  -p MemoryHigh=4G -p MemoryMax=6G -p MemorySwapMax=512M -p TasksMax=64 \
  -- "$@"
