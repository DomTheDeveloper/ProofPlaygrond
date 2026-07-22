# Formal Conjectures CI v2

## Diagnosis

The current fork correctly cancels superseded commits **inside one PR**, but its concurrency key is per PR. Ten draft audit PRs therefore still create ten independent full Lean builds. The build workflow executes `lake --wfail build`, so a proof-development PR validates the entire repository instead of the theorem being edited.

The fork must distinguish development, promotion, and integration.

## Recommended trigger and gate

Keep the existing main/webtest/manual behavior, but replace the bare `pull_request:` trigger with explicit lifecycle events:

```yaml
on:
  push:
    branches:
      - main
      - '*-webtest'
  pull_request:
    types:
      - opened
      - synchronize
      - reopened
      - ready_for_review
      - converted_to_draft
      - labeled
      - unlabeled
  merge_group:
    types: [checks_requested]
  workflow_dispatch:
    inputs:
      website_only:
        description: Skip Lean build and use live site data
        type: boolean
        default: false
```

Retain the per-PR concurrency group:

```yaml
concurrency:
  group: build-and-docs-${{ github.event.pull_request.number || github.ref }}
  cancel-in-progress: true
```

Gate the expensive build job:

```yaml
jobs:
  build:
    if: >-
      github.event_name != 'pull_request' ||
      github.event.pull_request.draft == false ||
      contains(github.event.pull_request.labels.*.name, 'ci:full')
    runs-on: ubuntu-latest
```

Effects:

- opening or updating a draft PR creates no expensive runner job;
- converting a running PR back to draft triggers a same-group skipped run, canceling its obsolete build;
- marking the PR ready starts the full build exactly once;
- a deliberate `ci:full` label allows an exceptional full build while still draft;
- merge queue checks receive a full build through `merge_group`;
- main and explicit manual runs keep their current behavior.

## Lightweight copyright check

The copyright workflow is tiny but currently uses a standard Ubuntu VM and lacks concurrency. Change it to:

```yaml
concurrency:
  group: copyright-${{ github.event.pull_request.number || github.ref }}
  cancel-in-progress: true

jobs:
  check-copyright:
    runs-on: ubuntu-slim
```

This keeps one cheap metadata check per PR while canceling superseded copies.

## Targeted promotion check

A later improvement should add a targeted Lean job before the full integration build:

1. determine changed `.lean` files;
2. reject placeholders and trust shortcuts in those files;
3. run `lake env lean <changed-file>` for problem files or `lake --wfail build <module>` for an explicitly declared module;
4. reserve `lake --wfail build` for ready-for-review, merge-group, manual full audit, and main.

Do not make a path-filtered workflow itself a required check unless a separate always-reporting gate job exists; GitHub can leave required path-filtered checks pending when the workflow does not run.

## Repository boundary

`DomTheDeveloper/formal-conjectures` is a promotion/integration repository, not a proof scratchpad.

Allowed there:

- one stable branch per proof;
- one draft promotion PR per theorem;
- a full build only when ready or explicitly labeled.

Not allowed there:

- one-shot audit workflow files;
- operating-system hedge PRs;
- PRs created only to trigger Actions;
- repeated commits whose sole purpose is restarting CI.

All iterative work and one-off audit harnesses belong in `ProofPlaygrond`, using AXLE/local Lean first and the generic manual kernel audit once the source is stable.
