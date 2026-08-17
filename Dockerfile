# The published container image (GitHub Packages, `ghcr.io/afflom/lexlean`).
#
# The image carries the compiler *and* the exact toolchain its `verify`
# command requires. LexLean's central claim is that a document was checked by
# Lean 4.32.1 and replayed by that toolchain's `leanchecker` (§22, R9); an
# image with the binary alone could `check` and `build` but never `verify`,
# which is the part worth distributing. Both versions are read from the files
# that pin them --- `rust-toolchain.toml` and `lean-toolchain` --- so the image
# cannot drift from the repository (R1).

# ---- build: the compiler, from the pinned Rust toolchain ----
FROM docker.io/library/debian:bookworm-slim AS build

ENV RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    PATH=/usr/local/cargo/bin:$PATH

RUN apt-get update \
    && apt-get install --no-install-recommends --yes \
        build-essential ca-certificates curl \
    && rm -rf /var/lib/apt/lists/*

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
    | sh -s -- -y --no-modify-path --profile minimal --default-toolchain none

WORKDIR /src
# The whole tree: `crates/lexlean/{language,schemas}` and
# `crates/lexlean/model/errors.toml` are links into the repository root that
# `build.rs` reads to embed the normative language data, and the
# compiler-semantics ID is a digest over exactly those bytes (§21.2).
COPY . .

# `rustup toolchain install` with no argument installs the toolchain, profile,
# and components `rust-toolchain.toml` names, so the version lives in one file.
RUN rustup toolchain install \
    && cargo build --locked --release -p lexlean \
    && strip target/release/lexlean

# ---- runtime: the compiler plus the pinned Lean toolchain ----
FROM docker.io/library/debian:bookworm-slim

# `git` is what Lake uses to resolve a workspace dependency; `libgmp10` is
# what the Lean runtime links against.
RUN apt-get update \
    && apt-get install --no-install-recommends --yes \
        ca-certificates curl git libgmp10 \
    && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/usr/local/elan \
    PATH=/usr/local/elan/bin:$PATH

COPY --from=build /src/lean-toolchain /tmp/lean-toolchain
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf \
        | sh -s -- -y --no-modify-path --default-toolchain none \
    && elan toolchain install "$(cat /tmp/lean-toolchain)" \
    && elan default "$(cat /tmp/lean-toolchain)" \
    && rm /tmp/lean-toolchain

COPY --from=build /src/target/release/lexlean /usr/local/bin/lexlean
COPY --from=build /src/LICENSE-APACHE /src/LICENSE-MIT /usr/share/doc/lexlean/

# A project is mounted here; every path LexLean touches stays inside it
# (§25.1), so the image needs no other writable location.
WORKDIR /work

# The image is the tool, not a shell: the default entry point is the compiler
# itself, and `--version` is the identity it reports (§30.3).
ENTRYPOINT ["/usr/local/bin/lexlean"]
CMD ["--version"]

LABEL org.opencontainers.image.title="LexLean" \
      org.opencontainers.image.description="A closed-lexicon LaTeX-to-Lean 4 compiler whose canonical document and prose-free Lean program are generated from one semantic representation." \
      org.opencontainers.image.source="https://github.com/afflom/lexlean" \
      org.opencontainers.image.licenses="MIT OR Apache-2.0"
