Feature: configuration-lock

  Project configuration, selection, lexicon sources, and the canonical lock file (§10, §11, §23).

  @CF-01 @build
  Scenario: Project configuration accepts exactly the project/1 schema and rejects unknown or missing fields.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_01 exercises CF-01
    Then the observed behavior matches the registered statement exactly

  @CF-02 @build
  Scenario: Every operational limit is explicit, positive, parsed with checked arithmetic, and has no hidden default.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_02 exercises CF-02
    Then the observed behavior matches the registered statement exactly

  @CF-03 @build
  Scenario: Configured paths resolve within the project under the specified UTF-8 and nonsymlink rules.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_03 exercises CF-03
    Then the observed behavior matches the registered statement exactly

  @CF-04 @build
  Scenario: Project discovery selects the nearest valid regular lexlean.toml and stops at the filesystem root.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_04 exercises CF-04
    Then the observed behavior matches the registered statement exactly

  @CF-05 @build
  Scenario: Entrypoint, explicit-file, and all-module selections are mutually exclusive and canonicalized as specified.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_05 exercises CF-05
    Then the observed behavior matches the registered statement exactly

  @CF-06 @build
  Scenario: Builtin, path, and exact-commit HTTPS Git lexicon sources obey their disjoint schemas.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_06 exercises CF-06
    Then the observed behavior matches the registered statement exactly

  @CF-07 @build
  Scenario: The lock file is canonical, comment-free, sorted, generated, and exact-byte checkable.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_07 exercises CF-07
    Then the observed behavior matches the registered statement exactly

  @CF-08 @build
  Scenario: The lock contains the complete exact transitive lexicon package closure including lexlean.core.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_08 exercises CF-08
    Then the observed behavior matches the registered statement exactly

  @CF-09 @build
  Scenario: Package tree digests use the specified length-framed sorted-file algorithm and reject special files.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_09 exercises CF-09
    Then the observed behavior matches the registered statement exactly

  @CF-10 @build
  Scenario: A changed config, package, workspace pin, or digest makes lock checking fail rather than silently refresh.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_10 exercises CF-10
    Then the observed behavior matches the registered statement exactly

  @CF-11 @build
  Scenario: Check, build, format, and verify resolve only locked locally available dependencies.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_11 exercises CF-11
    Then the observed behavior matches the registered statement exactly

  @CF-12 @build
  Scenario: Network package acquisition occurs only through lock --allow-network and only for an exact configured commit.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_12 exercises CF-12
    Then the observed behavior matches the registered statement exactly

  @CF-13 @build
  Scenario: The Lake workspace contains exactly one supported Lake configuration and the recorded workspace files match.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_13 exercises CF-13
    Then the observed behavior matches the registered statement exactly

  @CF-14 @build
  Scenario: Language 1.0 accepts only leanprover/lean4:v4.32.1 for verification.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_14 exercises CF-14
    Then the observed behavior matches the registered statement exactly

  @CF-15 @build
  Scenario: Duplicate logical modules and case-folded path or module collisions are rejected.
    Given the LexLean repository with its committed language data and fixtures
    When conformance test conformance_cf_15 exercises CF-15
    Then the observed behavior matches the registered statement exactly
