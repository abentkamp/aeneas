#!/usr/bin/env bash
set -eo pipefail

# The lakefile disables precompilation of the `AeneasMeta` modules whenever the
# `CI` environment variable is set, because precompilation breaks the Nix-based
# test CI. For *releases*, however, we want precompilation ON:
#   * it produces the shared libraries needed for plugin loading, and
#   * it makes the uploaded oleans match a default downstream `lake build`, so
#     that consumers using `preferReleaseBuild` reuse them instead of
#     recompiling Aeneas from source.
#
# Two subtleties make this easy to get wrong:
#   * `CI=` / `CI=""` does NOT disable the guard: `IO.getEnv "CI"` still returns
#     `some ""` (the variable is set, just empty), so `notCI` stays false. The
#     variable must be fully `unset`.
#   * Lake bakes the precompilation decision into the compiled config
#     (`.lake/config/.../lakefile.olean`) the first time it elaborates the
#     lakefile, and reuses that OLean on subsequent runs regardless of the
#     environment (the config trace tracks the lakefile source and toolchain,
#     not env vars). A config restored from the CI build cache may have been
#     elaborated while `CI` was set, so we pass `--reconfigure` to force
#     re-elaboration now that `CI` is unset.
unset CI

elan default "$(cat lean-toolchain)"

# Fetch pre-compiled Mathlib binaries.
if ! lake exe cache get; then
  echo "::warning::Mathlib cache extraction failed; continuing with source build"
fi

lake build --reconfigure

# Pack prebuilt oleans into an archive for Lake's automatic olean download.
# Users who pin to a release tag get these instead of compiling from source.
lake pack

# Delete heavy dependency sources to keep the release archive small.
rm -rf .lake/packages
