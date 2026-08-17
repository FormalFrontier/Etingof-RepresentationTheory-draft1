# Maintainer setup

This repository must remain private and GitHub Pages must remain disabled.
Configure branch protection on `main` so that `Private Verso CI / build` is a
required check, and enable auto-merge for dependency-update pull requests.

The public repository sends `repository_dispatch` events containing its exact
tested commit SHA. The `Update formalization dependency` workflow opens a pull
request that changes the Git pin and deterministic formalization panels
exported from that exact public revision. It regenerates the ignored Lake
manifest only to resolve and build the dependency; the manifest is not included
in the pull request, and the workflow never copies the public repository into
this one. Because GitHub suppresses recursive workflow events created by
`GITHUB_TOKEN`, the updater explicitly dispatches `ci.yml` on the new branch
before enabling auto-merge. Rendered HTML is retained only as a private Actions
artifact unless the American Mathematical Society separately authorizes
publication.
