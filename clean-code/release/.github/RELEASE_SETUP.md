# Maintainer setup

The repository is public. Configure branch protection on `main` so that the
`Lean CI / build` check is required.

Configure the Actions secret `VERSO_REPO_DISPATCH_TOKEN` with a fine-grained
token (or GitHub App installation token supplied by equivalent automation) that
has access only to the private
`mathlib-initiative/EtingofRepresentationTheory-verso` repository and permission to
send repository dispatch events. A push to `main` then sends the exact commit
SHA to the private repository. Do not put the token in either repository.
