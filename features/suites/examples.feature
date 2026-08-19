Feature: examples

  The literal example, its required mutations, and the negative fixture suite (§28, §29).

  @EX-01 @build
  Scenario: The committed nat-add-zero example formats, locks, checks, builds, and verifies with an empty axiom set.
    Given the committed nat-add-zero example project verified against the pinned Lean 4.32.1 toolchain
    When lexlean fmt --check, lexlean lock --check and lexlean check run on it
    Then all three succeed with the committed lock current
    And the attestation declarations row for LexLeanExample.Main.add_zero records an empty observed axiom set

  @EX-02 @build
  Scenario: Changing the example proposition while retaining the old proof causes remapped Lean verification failure.
    Given the example project with `\(n + 0 = n\)` changed to `\(n + 0 = 0\)` while keeping the reflexivity proof
    When lexlean verify runs against the pinned Lean 4.32.1 toolchain
    Then it fails with LLV7002 remapped from the Lean elaboration error
    And .lexlean/verified is absent or empty

  @EX-03 @build
  Scenario: Replacing a title concept with an undeclared word causes lexical-closure failure.
    Given the example project with \title{Natural number addition} changed to \title{Natural number banana}
    When lexlean check runs
    Then it fails with LLL1004 at the undeclared word

  @EX-04 @build
  Scenario: Adding an indistinguishable same-surface entry causes ambiguity rather than priority selection.
    Given the nzz module using one local package test.dupa whose nzz entry denotes Nat.le_refl
    When lexlean check runs after relocking
    Then it succeeds
    And with a second package test.dupb adding an nzz entry of the same surface denoting Nat.ge_refl and both glossaries used
    Then lexlean check fails with LLP2002 rather than picking either entry by priority

  @EX-05 @build
  Scenario: An axiom-dependent fixture fails an insufficient declaration policy and records the observed excess.
    Given the em fixture proved by `Classical.em` under \allowaxioms{Classical.choice}
    When lexlean verify runs against the pinned Lean 4.32.1 toolchain
    Then it fails with LLV7005
    And the rendered diagnostic records the observed excess propext or Quot.sound

  @EX-06 @build
  Scenario: Two clean example builds in distinct paths have byte-identical platform-independent artifacts.
    Given two fresh copies of the example project in distinct temporary directories
    When each is rendered by lexlean build
    Then both builds share the same build_id
    And every artifact path and its bytes are identical between the two builds

  @EX-07 @build
  Scenario: The negative fixture suite covers every required rejection class and prescribed diagnostic family.
    Given the negative fixture suite under tests/negative/<class>/, each with a project/, expected/{command.json,diagnostics.json,artifacts.json,hashes.toml} and case.toml
    When the class set is compared with the 28 prescribed rejection classes from unknown-word through pdf-hash-mismatch
    Then every required class has a fixture directory
    And each mutation fixture applies its overlay and edits to the example, relocks when asked, and its check, lock or lock-check run fails with exactly the one prescribed diagnostic code of its class
    And each delegated fixture names a test that exists in the workspace

  @EX-08 @build
  Scenario: Every example directory is discovered automatically and must satisfy the full example gate.
    Given every directory under examples/
    When each is loaded as a project
    Then it has lexlean.toml, lexlean.lock and an expected/build directory and the engine loads it
    And at least one example directory is discovered
