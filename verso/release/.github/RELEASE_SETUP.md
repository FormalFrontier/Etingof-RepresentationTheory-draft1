# Maintainer setup

This repository must remain private and GitHub Pages must remain disabled.
Configure strict branch protection on `main` so that `Private Verso CI / build`
is a required check. Select **Require branches to be up to date before merging**.
In **Settings → Actions → General → Workflow permissions**, allow read and
write permissions and allow GitHub Actions to create and approve pull requests.
The updater requests only the `actions: write`, `contents: write`, and
`pull-requests: write` permissions it needs.

The public repository sends `repository_dispatch` events containing its exact
tested commit SHA. The `Update formalization dependency` workflow opens a pull
request that changes the Git pin and deterministic formalization panels
exported from that exact public revision. It regenerates the ignored Lake
manifest only to resolve and build the dependency; the manifest is not included
in the pull request, and the workflow never copies the public repository into
this one. Because GitHub suppresses recursive workflow events created by
`GITHUB_TOKEN`, the updater explicitly dispatches `ci.yml` on the new branch
and waits for the exact head commit to pass. It then rechecks both public and
private `main` and requests an immediate head-bound squash merge. The strict
up-to-date branch rule closes the remaining race if private `main` advances
between that final check and GitHub's merge operation. Rendered HTML is retained
only as a private Actions artifact unless the American Mathematical Society
separately authorizes publication.
