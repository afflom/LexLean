Feature: security

  Filesystem confinement, process policy, limits, and internal invariants (§25).

  @SE-01 @build
  Scenario: Source, package, workspace, resource, and output paths are confined and symlinks are rejected.
    Given the example project with build_root set to `../elsewhere`
    When the engine loads lexlean.toml
    Then it fails with LLC0101
    And with src/Evil.lex.tex a symlink to the system hostname file added to entrypoints and the project relocked
    Then lexlean check fails with LLS8001

  @SE-02 @build
  Scenario: Special files, duplicate filesystem identities, and case-fold collisions are rejected before processing.
    Given the example project with a local package test.fifo whose entries/pipe.toml is a FIFO created by mkfifo
    When lexlean lock runs offline
    Then it fails with LLS8001
    And with src/MAin.lex.tex copied from src/Main.lex.tex and both listed as entrypoints after relocking
    Then lexlean check fails with LLC0104

  @SE-03 @build
  Scenario: All child processes use direct executable and argv invocation with no shell.
    Given the process/lean/ and process/leanchecker/ records of the verified nat-add-zero example
    When each recorded argv is examined
    Then every argv is non-empty
    And no argument is `sh`, `bash` or `-c`

  @SE-04 @build
  Scenario: No command except lock --allow-network may perform package network acquisition.
    Given the example project with a git lexicon_source for test.remote at https://example.invalid/repo.git pinned to a 40-hex revision
    When lexlean check, build and verify each run
    Then each exits non-zero with LLS8003 or LLC0102 on stderr because the package is never acquired
    And lexlean build --allow-network exits 2 as an unknown option

  @SE-05 @build
  Scenario: Child environments use the specified deterministic allow-list and recorded normalization.
    Given the child spawner in crates/lexlean/src/verify/child.rs
    When its source is inspected
    Then it calls .env_clear() and pins NO_COLOR, C.UTF-8 and GIT_TERMINAL_PROMPT
    And no JSON record under process/lean/, process/leanchecker/, probe/ or audit/ of the verified example contains the quoted HOME prefix

  @SE-06 @build
  Scenario: Every configured parser, graph, IR, diagnostic, child-output, and timeout limit is enforced with checked arithmetic.
    Given the example project with max_primitive_atoms lowered from 2000000 to 10 and relocked
    When lexlean check runs
    Then it fails with LLS8002
    And with max_file_bytes set to 99999999999999999999999999
    Then loading lexlean.toml fails with LLC0101 instead of overflowing

  @SE-07 @build
  Scenario: Temporary data uses confined owner-only staging and is removed after atomic publication or failure.
    Given one example project that builds successfully and another with `natural number` changed to `banana number` whose check fails
    When every entry under each project's .lexlean directory is walked
    Then no name starts with .tmp or contains .staging

  @SE-08 @build
  Scenario: External executables and PDF resources are hash-checked before use.
    Given the attestation of the verified nat-add-zero example
    When the toolchain entries for lean, lake and leanchecker are read
    Then each executable_sha256 is a full 64-hex SHA-256
    And every process/lean/ record carries the 64-hex executable_sha256 of the binary it ran

  @SE-09 @build
  Scenario: PDF execution receives only canonical TeX and declared resources in an isolated working directory.
    Given the example project with assets/logo.txt and a tools/fakepdf script that writes a listing of its working directory into the output PDF
    When the PDF provider runs with compile_argv --outdir {out_dir} {input} and resources assets/logo.txt on the rendered LexLeanExample.Main module
    Then the sorted listing is exactly LexLeanExample.Main.tex and logo.txt

  @SE-10 @build
  Scenario: Internal invariant failures use LLI9001 and exit 70 without misclassifying user input.
    Given the diagnostic code LLI9001
    When its class exit code is computed
    Then it is 70
    And with src/Main.lex.tex replaced by `}{}{` the check error has an exit code other than 70 and no LLI9001 diagnostic

  @SE-11 @build
  Scenario: Diagnostics and process records do not expose secret environment values or arbitrary unrelated file contents.
    Given the environment variable LEXLEAN_TEST_SECRET set to hunter2-marker and the example with `natural number` changed to `banana number`
    When lexlean --diagnostic-format json check runs
    Then neither stdout nor stderr contains hunter2-marker
    And with entrypoints set to the system passwd file the load error is rendered without any `root:` line from that file

  @SE-12 @build
  Scenario: Git lexicon acquisition accepts only an exact 40-hex commit over HTTPS and rejects submodules and LFS indirection.
    Given git lexicon_source entries with a short revision `abc123`, a plain http URL, a file:// URL and an ssh:// URL
    When the engine loads each lexlean.toml
    Then each fails with LLC0101
    And a local git fixture served through a url.insteadOf rewrite at an exact 40-hex commit acquires under lock --allow-network and then checks offline from the cache
    But a fixture committing .gitmodules or an LFS .gitattributes filter fails lock --allow-network with LLR3001
