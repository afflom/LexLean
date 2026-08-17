Feature: artifacts

  Diagnostics, source maps, coverage, hashing, manifests, and atomic publication (§20, §21).

  @AR-01 @build
  Scenario: Diagnostics use the canonical schema, exact spans, stable sorting, and registered codes.
    Given the nat-add-zero example with `banana` and `kumquat` inserted into the theorem statement
    When `lexlean --diagnostic-format json check` runs
    Then the exit code is nonzero and stderr is empty
    And stdout is one canonical JSON object whose `diagnostics` array is nonempty
    And every diagnostic `code` is registered in the model and the `primary.byte_start` offsets are in ascending order

  @AR-02 @build
  Scenario: Source maps contain complete module, source, artifact, node, and range records.
    Given the nat-add-zero example project rendered with its source map
    When the `Main` module map is inspected
    Then its artifact, node, mapping, and source record lists are all nonempty
    And every mapping names an existing node ID and artifact ID
    And every mapping has `gen_start` no greater than `gen_end`

  @AR-03 @build
  Scenario: Lean diagnostics remap by the specified smallest-enclosing mapping algorithm.
    Given the nat-add-zero example project rendered with its source map
    When the byte offset of `rfl` in the `.lean` artifact is remapped to source
    Then a mapping is returned
    And its generated range length equals the smallest range among all mappings enclosing that offset
    And the mapping role is not synthetic

  @AR-04 @build
  Scenario: Coverage files record every required source and output token with no gap or overlap.
    Given the nat-add-zero example project
    When lexlean build runs and the project is also rendered with coverage rows
    Then the build directory contains `coverage/LexLeanExample/Main.coverage.json`
    And the Lean and LaTeX coverage rows are each sorted with no overlapping byte ranges
    And the source coverage rows are nonempty

  @AR-05 @build
  Scenario: All compound hashes use the specified length-prefixed frame function.
    Given a `FramedHasher` with tag `t` fed the frames `a` = `xy` and `b` = empty
    When the digest is recomputed by hand as sha256 of `t\0`, a 4-byte big-endian label length, the label, an 8-byte big-endian payload length, and the payload per frame
    Then the hasher's result equals the hand-computed digest

  @AR-06 @build
  Scenario: Compiler-semantics identity is recomputed from the exact normative language, schema, backend, and parser inputs.
    Given the embedded normative file set of the compiler
    When the tree digest of the file set is computed and again with the first file's bytes replaced by `tampered`
    Then the untampered digest equals the compiler semantics ID
    And the tampered digest differs from it

  @AR-07 @build
  Scenario: Source IDs are independent of absolute checkout location and include exact normalized inputs.
    Given two fresh copies of the nat-add-zero example in distinct temporary directories
    When both are checked, and then the second has its theorem label changed from `{add-zero}` to `{add-zeros}` and is checked again
    Then the two unmodified copies share one source ID
    And the modified copy's source ID differs

  @AR-08 @build
  Scenario: Semantic IDs are platform independent and include linked IR, lexicon closure, language semantics, and toolchain ID.
    Given two fresh copies of the nat-add-zero example and the test.defs definitions fixture
    When each project is checked and its semantic ID read
    Then the two example copies share one semantic ID
    And the definitions fixture's semantic ID differs from it

  @AR-09 @build
  Scenario: Successful builds publish only the fixed content-addressed build-ID layout.
    Given the nat-add-zero example project
    When lexlean build runs and every file under the build directory is listed
    Then the set is exactly `manifest.json`, `modules/LexLeanExample/Main.lean`, `modules/LexLeanExample/Main.tex`, `maps/LexLeanExample/Main.map.json`, `coverage/LexLeanExample/Main.coverage.json`, and `lexicons/Main.closure.json`

  @AR-10 @build
  Scenario: Build manifests enumerate every input and output with stable paths, sizes, and hashes.
    Given the nat-add-zero example project
    When lexlean build runs and `manifest.json` in the build directory is parsed
    Then it has the fields `spec`, `compiler`, `language`, `project`, `source_id`, `semantic_id`, `build_id`, `lean_toolchain`, `selection`, `modules`, `inputs`, and `outputs`
    And the inputs enumerate `src/Main.lex.tex`, `lexlean.toml`, and `lexlean.lock`
    And every output row's `byte_length` and `sha256` match the published file exactly

  @AR-11 @build
  Scenario: Normative JSON obeys the restricted canonical JSON format and hash/file newline distinction.
    Given the restricted canonical JSON implementation
    When `1.5` and `null` are parsed and an object with keys `zebra` and `alpha` is serialized
    Then both parses are rejected
    And the canonical string is `{"alpha":2,"zebra":1}` with sorted keys and no spaces
    And the file form is the same bytes plus exactly one final LF

  @AR-12 @build
  Scenario: Concurrent and failed builds preserve atomic content-addressed artifacts and never overwrite unexplained bytes.
    Given a built nat-add-zero example project
    When two builds run concurrently on separate threads, then the first byte of the published `modules/LexLeanExample/Main.lean` is flipped and build runs again
    Then both concurrent builds succeed and the build directory exists
    And the rebuild over the corrupted byte fails with LLB6003
    And no `.staging` entry remains anywhere under `.lexlean`

  @AR-13 @build
  Scenario: Two clean builds in different absolute directories produce byte-identical platform-independent artifacts.
    Given two fresh copies of the nat-add-zero example in distinct temporary directories
    When each copy is rendered to a build
    Then both builds have the same build ID
    And their artifact lists have equal length with matching paths
    And every artifact's bytes are identical between the two

  @AR-14 @build
  Scenario: Platform-independent build evidence is distinguished from platform-bound oleans, process records, PDF bytes, and attestations.
    Given the shared verified run of the nat-add-zero example
    When the verified root and the content-addressed build directory are each listed
    Then the verified set contains a `.olean` file, `attestation.json`, and a `process/lean/` record
    And the build set contains no `.olean`, no `process/` entry, no `attestation.json`, and no `.pdf`
