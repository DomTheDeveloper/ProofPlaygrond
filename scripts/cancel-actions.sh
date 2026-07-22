#!/usr/bin/env bash
set -euo pipefail

# Cancel queued/running GitHub Actions runs from outside GitHub Actions.
# Usage:
#   bash scripts/cancel-actions.sh OWNER/REPO
#   bash scripts/cancel-actions.sh --owner OWNER

usage() {
  cat <<'EOF'
Usage:
  cancel-actions.sh OWNER/REPO
  cancel-actions.sh --owner OWNER

Requires an authenticated GitHub CLI (`gh auth status`) with Actions: write
permission for the target repositories.
EOF
}

list_active_run_ids() {
  local repo=$1
  local status
  for status in queued in_progress waiting requested pending; do
    gh api --paginate \
      "/repos/${repo}/actions/runs?status=${status}&per_page=100" \
      --jq '.workflow_runs[].id'
  done | sort -u
}

cancel_repo() {
  local repo=$1
  local run_id
  echo "==> ${repo}"

  while IFS= read -r run_id; do
    [[ -z "$run_id" ]] && continue
    echo "Stopping run ${run_id}"

    if gh api -X POST "/repos/${repo}/actions/runs/${run_id}/cancel" >/dev/null 2>&1; then
      continue
    fi

    gh api -X POST "/repos/${repo}/actions/runs/${run_id}/force-cancel" >/dev/null 2>&1 || {
      echo "Warning: unable to cancel ${repo} run ${run_id}" >&2
    }
  done < <(list_active_run_ids "$repo")
}

command -v gh >/dev/null 2>&1 || {
  echo 'GitHub CLI (`gh`) is required.' >&2
  exit 127
}

gh auth status >/dev/null

case ${1:-} in
  --owner)
    owner=${2:-}
    [[ -n "$owner" ]] || { usage >&2; exit 2; }
    while IFS= read -r repo; do
      cancel_repo "$repo"
    done < <(
      gh repo list "$owner" --limit 1000 \
        --json nameWithOwner --jq '.[].nameWithOwner'
    )
    ;;
  */*)
    cancel_repo "$1"
    ;;
  *)
    usage >&2
    exit 2
    ;;
esac
