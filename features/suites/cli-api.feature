Feature: cli-api

  The command-line interface and the stable public Rust API (§23, §24).

  @CL-01 @build
  Scenario: Global options and upward project discovery obey the exact CLI contract.
    Given the nat-add-zero example project and an unrelated empty working directory
    When `lexlean --project <config> check` runs from the empty directory, then bare `check`, then `--frobnicate check`, then `--help`
    Then the `--project` run exits 0
    And the bare `check` and the `--frobnicate` runs both exit 2
    And `--help` exits 0 and mentions `--project` and `--diagnostic-format`

  @CL-02 @build
  Scenario: Init creates the complete canonical skeleton only in an absent or empty destination and never overwrites.
    Given an empty temporary directory
    When `lexlean init . --name fresh --module-prefix Fresh` runs and then `init . --name again --module-prefix Again` runs in the same directory
    Then the first init exits 0 and writes `lexlean.toml`, `lexlean.lock`, `lean-toolchain`, `src/Main.lex.tex`, and `.gitignore`
    And the generated skeleton loads and checks successfully
    And the second init exits 2 without overwriting

  @CL-03 @build
  Scenario: Lock check, local update, and explicit network acquisition obey their exact mutually exclusive behavior.
    Given the nat-add-zero example project with a current lock
    When `lock --check --allow-network`, `lock --check`, and after changing `max_diagnostics` from 256 to 128 `lock --check`, `lock`, and `lock --check` run in turn
    Then the combined `--check --allow-network` invocation exits 2
    And the initial `lock --check` exits 0 while the drifted `lock --check` exits nonzero
    And plain `lock` exits 0 and the following `lock --check` exits 0

  @CL-04 @build
  Scenario: Check runs through linked IR and emits no build artifacts.
    Given the nat-add-zero example project with no `.lexlean/build` directory
    When `lexlean check` runs
    Then the exit code is 0
    And `.lexlean/build` still does not exist

  @CL-05 @build
  Scenario: Build emits the fixed build-ID artifact set without running Lean or claiming verification.
    Given the nat-add-zero example project with `ELAN_HOME` pointed at an empty directory
    When lexlean build runs through the engine
    Then the build succeeds and reports a build ID
    And no Lean toolchain was required

  @CL-06 @build
  Scenario: Verify runs the complete fixed verification pipeline and accepts no output or suppression option.
    Given the nat-add-zero example project
    When `verify --output elsewhere`, `verify --skip-probe`, and `verify --fast` each run
    Then every invocation exits 2

  @CL-07 @build
  Scenario: Format and format-check are idempotent and preserve linked IR.
    Given the already-canonical nat-add-zero example with its `src/Main.lex.tex` bytes and semantic ID recorded
    When `lexlean fmt` runs and then `lexlean fmt --check` runs
    Then both exit 0
    And `src/Main.lex.tex` is byte-identical to the recorded bytes
    And the semantic ID after formatting equals the recorded one

  @CL-08 @build
  Scenario: Clean removes only the validated configured build root and no source or external cache.
    Given a built nat-add-zero example project with an extra `src/keep.txt` file
    When `lexlean clean` runs, then `.lexlean` is replaced by a symlink to a directory holding `precious.txt` and `clean` runs again
    Then the first clean exits 0, removes `.lexlean`, and leaves `src/keep.txt` in place
    And the second clean exits nonzero
    And `precious.txt` in the symlink target survives

  @CL-09 @build
  Scenario: Explain prints exactly one registered diagnostic entry and rejects unknown codes.
    Given the nat-add-zero example project
    When `lexlean explain LLL1004` runs and then `lexlean explain` runs with an unregistered code
    Then the first exits 0 and prints `LLL1004` with `Unknown non-whitespace primitive atom`
    And the first output does not mention LLL1005
    And the second exits 2

  @CL-10 @build
  Scenario: All, explicit-files, and entrypoint selections return sorted project result sets including import closure.
    Given the nat-add-zero example extended with `src/Helper.lex.tex` and `\importmodule{Helper}` in `Main`
    When `--diagnostic-format json check` runs with no selection, with `--all`, and with `src/Main.lex.tex`
    Then every run exits 0
    And each JSON `modules` list is exactly `Helper` then `Main`

  @CL-11 @build
  Scenario: Every command maps failures to the exact documented exit code.
    Given four example copies mutated for a config error, a language error, an empty `ELAN_HOME`, and a git lexicon source at `https://example.invalid/repo.git`
    When `check`, `check`, `verify`, and `lock` run over the respective copies
    Then the unknown `mystery` key in `lexlean.toml` exits 2
    And the `banana number` statement exits 1, the empty toolchain verify exits 3, and the network lock exits 4
    And the internal error class maps to exit code 70

  @CL-12 @build
  Scenario: Human and canonical-JSON output modes obey exact stream, color, and cardinality rules.
    Given the nat-add-zero example with `natural number` changed to `banana number`
    When `--diagnostic-format json check` runs and then `--color never check` runs
    Then the JSON run leaves stderr empty and prints exactly one JSON object on stdout
    And the human run writes diagnostics to stderr
    And neither human stream contains an ANSI escape byte

  @CL-13 @build
  Scenario: The public Engine exposes exactly the stable load, lock, check, build, verify, and format entry points.
    Given the source of `crates/lexlean/src/api.rs`
    When the `pub fn` names inside `impl Engine` are collected and sorted
    Then the list is exactly `build`, `check`, `format`, `load`, `lock`, and `verify`

  @CL-14 @build
  Scenario: Every public multi-module operation returns a ProjectResultSet or VerifiedProject rather than a singular unit.
    Given the nat-add-zero example project with its single `Main` module
    When the engine checks and then builds the entrypoints
    Then the check result set has exactly one unit keyed `Main`
    And the build result set also has a unit keyed `Main`

  @CL-15 @build
  Scenario: Public requests cannot override backends, toolchain, verification stages, limits, policies, or fixed artifact sets.
    Given the source of `crates/lexlean/src/api.rs`
    When the `pub` fields of each request struct are read
    Then `CheckRequest`, `BuildRequest`, and `VerifyRequest` have exactly `selection`
    And `FormatRequest` has exactly `selection` and `check_only`
    And `LockRequest` has exactly `check_only` and `allow_network`

  @CL-16 @build
  Scenario: Every public failure is a LexLeanError and malformed user input cannot panic.
    Given six malformed `src/Main.lex.tex` payloads including invalid UTF-8, 64 NUL bytes, a truncated environment, a 5000-parenthesis title, a missing operand, and stray braces
    When each is written into a fresh example copy and checked under `catch_unwind`
    Then no input panics
    And every input is rejected with a LexLeanError
    And no rejection maps to exit code 70

  @CL-17 @build
  Scenario: Environment variables cannot alter semantic project configuration.
    Given a baseline build ID of the nat-add-zero example
    When a fresh copy is built with `LEXLEAN_MODULE_PREFIX=Hijacked`, `LEXLEAN_LIMITS=0`, and `LC_ALL=C` set
    Then the build succeeds
    And its build ID equals the baseline

  @CL-18 @build
  Scenario: Version output reports compiler, language, semantics ID, and Lean toolchain exactly.
    Given the repository root as the working directory
    When `lexlean --version` runs
    Then the exit code is 0
    And stdout is exactly four lines `lexlean`, `language`, `compiler-semantics`, and `lean-toolchain` each followed by the compiled-in value
