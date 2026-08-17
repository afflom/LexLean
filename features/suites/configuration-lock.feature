Feature: configuration-lock

  Project configuration, selection, lexicon sources, and the canonical lock file (§10, §11, §23).

  @CF-01 @build
  Scenario: Project configuration accepts exactly the project/1 schema and rejects unknown or missing fields.
    Given three copies of the example project with `surprise = 1` added, the name field removed, and spec set to `lexlean/project/2`
    When Engine::load is called on each lexlean.toml
    Then the unknown-field copy fails with LLC0101
    And the missing-name copy fails with LLC0101
    And the wrong-schema-tag copy fails with LLC0103

  @CF-02 @build
  Scenario: Every operational limit is explicit, positive, parsed with checked arithmetic, and has no hidden default.
    Given one example copy with `max_file_bytes = 0` and another with the max_file_bytes row deleted
    When Engine::load is called on each lexlean.toml
    Then the zero limit fails with LLC0101
    And the omitted limit fails with LLC0101 instead of taking a default

  @CF-03 @build
  Scenario: Configured paths resolve within the project under the specified UTF-8 and nonsymlink rules.
    Given one example copy with `source_roots = ["../src"]` and another with `entrypoints = ["/etc/passwd"]`
    When Engine::load is called on each lexlean.toml
    Then the parent-escaping source root fails with LLC0101
    And the absolute entrypoint fails with LLC0101

  @CF-04 @build
  Scenario: Project discovery selects the nearest valid regular lexlean.toml and stops at the filesystem root.
    Given the example project with a nested src/deeper directory, then a directory named lexlean.toml inside it, and a second copy whose src/inner/lexlean.toml is a symlink to the real config
    When `lexlean check` runs from src/deeper and then from src/inner
    Then discovery walks upward from src/deeper and exits 0
    And the directory candidate is skipped and check still exits 0
    But the symlinked candidate makes check exit nonzero

  @CF-05 @build
  Scenario: Entrypoint, explicit-file, and all-module selections are mutually exclusive and canonicalized as specified.
    Given the example project
    When `lexlean check --all src/Main.lex.tex` runs, then the engine checks Selection::Files with the absolute Main.lex.tex path, then with an empty file set
    Then the mixed CLI invocation exits 2
    And the explicit-file selection yields the same unit keys as the entrypoint selection
    And the empty explicit selection fails with LLC0002

  @CF-06 @build
  Scenario: Builtin, path, and exact-commit HTTPS Git lexicon sources obey their disjoint schemas.
    Given one example copy whose builtin lexlean.std.nat source gains `path = "somewhere"` and another with a git source for test.remote that has a url but no revision
    When Engine::load is called on each lexlean.toml
    Then the builtin source carrying a path fails with LLC0101
    And the git source without an exact commit fails with LLC0101

  @CF-07 @build
  Scenario: The lock file is canonical, comment-free, sorted, generated, and exact-byte checkable.
    Given the example project's committed lexlean.lock
    When the lock text is inspected, the engine relocks without check_only, and then `1.0.0` is replaced by `1.0.1` before a lock --check
    Then the lock has no `#` character, ends with one LF, and its `id = ` rows are sorted
    And the relock reports written = false and leaves the bytes unchanged
    And the edited lock fails lock --check with LLC0102

  @CF-08 @build
  Scenario: The lock contains the complete exact transitive lexicon package closure including lexlean.core.
    Given the example project whose lexlean.toml configures only lexlean.std.nat
    When lexlean.lock is read
    Then it contains `id = "lexlean.core"` and `id = "lexlean.std.nat"`
    And at least two tree_sha256 rows are present

  @CF-09 @build
  Scenario: Package tree digests use the specified length-framed sorted-file algorithm and reject special files.
    Given the example project with a path package test.extra at lexicons/test-extra locked
    When the section 11.5 digest is recomputed by hand over lexicon.toml and entries/nzz.toml with the `lexlean-tree-v1` prefix and length framing, and then a symlink entries/link.toml is added and lock reruns
    Then the manual hex digest equals the locked tree_sha256 for test.extra
    And the relock with the symlink fails with LLS8001

  @CF-10 @build
  Scenario: A changed config, package, workspace pin, or digest makes lock checking fail rather than silently refresh.
    Given one example copy with `max_scope_depth = 1024` changed to 512 and a test.extra path package copy whose entries/nzz.toml gains a trailing newline
    When lock --check and `lexlean check` run on the config drift and lock --check runs on the package drift
    Then the config drift fails lock --check and check with LLC0102
    And the lexlean.lock bytes are unchanged after the failed check
    And the package drift fails lock --check with LLC0102

  @CF-11 @build
  Scenario: Check, build, format, and verify resolve only locked locally available dependencies.
    Given the example project with path package test.extra locked and its lexicons/test-extra directory then deleted
    When `lexlean check` runs
    Then check fails with LLR3001 or LLC0102

  @CF-12 @build
  Scenario: Network package acquisition occurs only through lock --allow-network and only for an exact configured commit.
    Given the example project with a git lexicon source test.remote at an exact 40-hex revision under subdirectory pkg
    When the engine locks with allow_network = false and then `lexlean lock --check --allow-network` runs
    Then the uncached git package fails with LLS8003
    And the combined --check and --allow-network invocation exits 2

  @CF-13 @build
  Scenario: The Lake workspace contains exactly one supported Lake configuration and the recorded workspace files match.
    Given one example copy whose lakefile.toml gains `defaultTargets = []` and another that also gets a lakefile.lean
    When lock --check runs on the first and a full lock runs on the second
    Then the drifted lakefile fails lock --check with LLC0102
    And the twin Lake configuration fails with LLC0101 or LLV7007

  @CF-14 @build
  Scenario: Language 1.0 accepts only leanprover/lean4:v4.32.1 for verification.
    Given one example copy with `lean_toolchain = "leanprover/lean4:v4.31.0"` in lexlean.toml and another whose lean-toolchain file reads leanprover/lean4:v4.31.0
    When Engine::load runs on the first and lock --check runs on the second
    Then the foreign toolchain string fails configuration with LLC0101
    And the drifted lean-toolchain pin fails lock --check with LLC0102

  @CF-15 @build
  Scenario: Duplicate logical modules and case-folded path or module collisions are rejected.
    Given the example project with src/Main.lex.tex copied to src/MAin.lex.tex and both listed as entrypoints
    When the project is relocked and `lexlean check` runs
    Then check fails with LLC0104
