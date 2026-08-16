# `just vv` is the normative acceptance gate (SPEC.md §9.2). Everything else is
# a slice of it, in the order the specification fixes.

default: vv

# The whole gate, in the normative order.
vv: fmt-check model spec-links lint test features bdd examples golden repro deny
    @echo "vv: the acceptance gate passed"

fmt:
    cargo fmt --all

fmt-check:
    cargo fmt --all -- --check

# R1, R4, R5: the model is the single source; nothing is deferred; every public
# failure is registered. Includes the repository audits (§27.5).
model:
    cargo xtask validate-model

# RP-07: the SPEC.md §31 table and model/ids.toml are bijective and
# text-consistent (§27.6).
spec-links:
    cargo xtask validate-spec-links

lint:
    cargo clippy --workspace --all-targets --all-features -- -D warnings

test:
    cargo test --workspace --all-features

# A feature only its author has built is a feature that does not work: every
# optional feature compiles, with its tests.
features:
    cargo check --workspace --all-features --all-targets

# R3: every capability begins as a Gherkin scenario, and every scenario has a
# test named `conformance_<id>` (§27.8).
bdd:
    cargo test -p repo-conformance

# §28.6: every example directory formats, locks, checks, builds, and verifies.
examples:
    cargo xtask verify-examples

# §28.3: golden output changes only through the explicit write recipe below.
golden:
    cargo xtask check-golden

# §28.4: two clean builds in distinct absolute directories are byte-identical
# for every platform-independent artifact.
repro:
    cargo xtask check-reproducibility

# R6: advisories, bans, licences and sources, over the dependency graph.
deny:
    cargo deny --all-features check

# Regenerate everything the model owns: CONFORMANCE.md and ERRORS.md (§27.5).
model-write:
    cargo xtask validate-model --write

# The only path that rewrites golden files (§28.3). Never part of `vv`.
golden-write:
    cargo xtask check-golden --write

# RP-12: a release is refused unless the complete §30 criterion holds. The
# gate itself must pass first; refusal is expected until 1.0.0.
release: vv
    cargo xtask release-check
