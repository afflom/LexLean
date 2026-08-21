Feature: verification

  The fixed verification pipeline, replay, axiom audit, and attestations (§22).

  @VR-01 @build
  Scenario: Verification runs every specified stage in order and exposes no stage-suppression option.
    Given the committed nat-add-zero example project verified against the pinned Lean 4.32.1 toolchain
    When the published verified directory is inspected
    Then it holds probe/process.json, audit/process.json, audit/output.txt, build-manifest.json and attestation.json
    And process/lean/ and process/leanchecker/ each hold at least one process record
    But lexlean verify --skip-audit, verify --no-replay and verify --output each exit 2 as unknown options

  @VR-02 @build
  Scenario: Lean, Lake, and leanchecker versions and executable hashes are checked and recorded before use.
    Given the attestation of the verified nat-add-zero example
    When the toolchain records for lean, lake and leanchecker are read
    Then each carries a 64-hex executable_sha256 and lean and lake record a version_output containing 4.32.1
    And with ELAN_HOME pointing at a fake toolchain whose lean prints version 4.31.0
    Then lexlean verify fails preflight with LLV7001 before any module is compiled

  @VR-03 @build
  Scenario: Lean execution uses the pinned Lake environment and never updates or fetches workspace dependencies.
    Given the process/lean/ records of the verified nat-add-zero example
    When each recorded argv is examined
    Then the first argument is `env` and the argv contains `lean`, so compilation runs through `lake env lean`
    And no argv contains `update`, `build` or `fetch`

  @VR-04 @build
  Scenario: Every used external interface is elaborated in the unique reserved probe module.
    Given the verified nat-add-zero example and its semantic ID
    When the reserved probe and audit module names are derived from that semantic ID
    Then the probe/ directory contains exactly one .lean file named after the reserved probe module
    And the probe module name differs from the audit module name

  @VR-05 @build
  Scenario: Generated modules compile in topological order and produce one required olean each.
    Given the verified nat-add-zero example
    When the oleans/ directory is compared with the verified units
    Then every unit's Lean module `A.B` has its olean at oleans/A/B.olean

  @VR-06 @build
  Scenario: Verification neither requests nor includes ilean artifacts.
    Given the verified nat-add-zero example
    When every file under the verified directory is listed
    Then no file name ends with .ilean

  @VR-07 @build
  Scenario: A Lean warning, unknown informational message, overflow, or missing output fails verification.
    Given the process/lean/ records of the verified nat-add-zero example
    When each record's stdout and stderr are trimmed
    Then both are empty for every successful compilation
    And the verifier source in crates/lexlean/src/verify/mod.rs wires the LLV7006 rejection for warnings, unknown informational messages and unexpected output

  @VR-08 @build
  Scenario: Every generated module is replayed by a separate leanchecker process and every replay must succeed.
    Given the process/leanchecker/ records of the verified nat-add-zero example
    When their count and exit codes are examined
    Then there is exactly one replay record per generated module and every exit_code is 0
    And with ELAN_HOME pointing at a fake toolchain whose leanchecker script exits 1
    Then lexlean verify fails with LLV7003

  @VR-09 @build
  Scenario: The unique reserved audit module prints axioms for every generated declaration exactly once.
    Given the audit/ directory of the verified nat-add-zero example
    When the reserved audit .lean module is read
    Then it contains exactly one `#print axioms` directive
    And that directive names LexLeanExample.Main.add_zero

  @VR-10 @build
  Scenario: The axiom parser accepts only the pinned exact output forms and rejects missing, duplicate, extra, or malformed records.
    Given the committed vectors tests/golden/axiom-parser/accepted.txt and rejected.txt
    When each non-empty line is fed to the audit-output parser expecting the single quoted declaration name
    Then every accepted vector parses
    And every rejected vector, covering missing, duplicate, extra and malformed records, is refused

  @VR-11 @build
  Scenario: None, allow-subset, and exact axiom policies are enforced exactly and recorded per declaration.
    Given the attestation of the verified nat-add-zero example under \noaxioms
    When the declarations row for LexLeanExample.Main.add_zero is read
    Then its policy kind is `none` and its observed set is empty
    And the em fixture verified under \allowaxioms{Classical.choice;Quot.sound;propext} records the sorted observed set Classical.choice, Quot.sound, propext
    And the same em fixture under \allowaxioms{Classical.choice} fails with LLV7005 naming the excess propext and Quot.sound
    And an exact policy passes only when the observed set matches and fails with LLV7005 on any mismatch

  @VR-12 @build
  Scenario: Child process output is normalized with the exact path and line rules before hashing.
    Given a child-output Normalizer built from distinct staging, project, lake and toolchain root directories
    When raw output with a CRLF line, those root prefixes before audit/A.lean, src and bin/lean, trailing spaces and three blank tail lines is normalized
    Then the prefixes become $STAGING/audit/A.lean, $PROJECT/src and $TOOLCHAIN/bin/lean
    And no carriage return survives, `trailing   ` becomes `trailing`, and the blank tail collapses to a single newline

  @VR-13 @build
  Scenario: A verified directory contains the complete fixed source, map, coverage, olean, probe, audit, and process artifact set.
    Given the verified nat-add-zero example
    When every file under the verified directory is matched against the fixed artifact slots
    Then each file falls into attestation.json, build-manifest.json, modules/*.lean, modules/*.tex, maps/*.map.json, coverage/*.coverage.json, lexicons/*.closure.json, oleans/*, probe/*.lean, probe/process.json, audit/*.lean, audit/output.txt, audit/process.json, process/lean/*.json or process/leanchecker/*.json
    And every one of those slots is populated by at least one file

  @VR-14 @build
  Scenario: The attestation ID is computed over the canonical body with its ID field removed.
    Given the attestation.json of the verified nat-add-zero example parsed as canonical JSON
    When the attestation_id field is removed and the remaining object is re-serialized canonically
    Then the attestation ID recomputed over that body equals the recorded hex
    And the verified directory name equals that attestation ID
    And the hashed body contains no timestamp

  @VR-15 @build
  Scenario: Any failed verification stage removes staging and produces no verified artifact or verified status.
    Given the example project with `\(n + 0 = n\)` changed to `\(n + 0 = 0\)` while keeping the reflexivity proof
    When lexlean verify runs against the pinned Lean 4.32.1 toolchain and fails
    Then .lexlean/verified is absent or empty with no staging leftovers
    And for each of probe, module, replay, audit and policy failures the staging directory is removed and no verified artifact or verified status is produced

  @VR-16 @build
  Scenario: Axioms flowing from imported theorems remain subject to the generated declaration's policy.
    Given the em fixture whose theorem is proved by the imported `Classical.em` under \allowaxioms{Classical.choice}
    When lexlean verify runs the axiom audit against the pinned Lean 4.32.1 toolchain
    Then it fails with LLV7005
    And the rendered diagnostic reports the excess axioms propext and Quot.sound that flow from the imported theorem

  @VR-17 @build
  Scenario: Lean workspace configuration and manifest hashes must match the lock and all dependencies must be locally available.
    Given the example project with lakefile.toml renamed from `nat_add_zero_host` to `renamed_host` without relocking
    When lexlean verify runs its workspace preflight
    Then it fails with LLV7007 because the lakefile hash no longer matches the lock
    And no verified directory is published

  @VR-18 @build
  Scenario: Check and build results never claim verified or kernel-checked status.
    Given the committed nat-add-zero example project
    When lexlean --diagnostic-format json check and lexlean --diagnostic-format json build each run
    Then both exit 0
    And neither JSON status is `verified` and neither stdout contains `kernel-checked`

  @VR-19 @build
  Scenario: The native Atlas source is the byte-exact semantic and proof export of the completed migration oracle and does not import that oracle.
    Given the completed Atlas migration oracle and the committed native Atlas source
    When the oracle is semantically exported with the pinned toolchain
    Then the exported source equals the committed source byte for byte
    And the native core module does not import the migration oracle
