# Measuring test coverage

Lean has no coverage tool, and the tests that run during elaboration (`#guard`, `#eval`) are not
measured by anything. This project measures coverage of the code that Lean compiles to C, by running
the same test tables from a native executable.

```sh
just coverage                       # summary
just coverage --list-missed         # functions that still have uncovered code
just coverage --show-uncovered      # every uncovered region with its C source line
just coverage --fail-under 90       # exit with an error below 90% (regions or branch arms)
```

## How it works

1. `UrllibTest/CoverageMain.lean` is an executable (`lake build coverage`) that runs every test table
   at run time: the `*Failures` lists and the `guardChecks` of each test module. It exits with an
   error if any case fails, so a coverage run is also a test run.
2. `scripts/coverage.sh` copies the repository to a work directory
   (`$COVERAGE_DIR`, default `$TMPDIR/urllib-lean-coverage`), appends instrumentation flags to the
   copy's `lakefile.toml` (`-O0 -fprofile-instr-generate -fcoverage-mapping`), builds with the system
   `clang` (`LEAN_CC`), runs the executable, and merges the profile with `llvm-profdata`.
3. `scripts/coverage_report.py` reads the `llvm-cov export` JSON and prints functions, regions, and
   branch arms for the library modules.

The repository's own build is never instrumented.

## Requirements

- `clang`, `llvm-cov`, and `llvm-profdata` of the same family. On macOS they come from Xcode
  (`xcrun` is used). Elsewhere put `clang`, `llvm-cov`, and `llvm-profdata` on `PATH`, or set
  `LEAN_CC`, `LLVM_COV`, and `LLVM_PROFDATA`.
- Do not mix compilers. Instrumenting with the clang bundled in the Lean toolchain and linking the
  profile runtime of another clang crashes at run time, because the bundled clang ships no profile
  runtime and the formats differ.

Verified on macOS (arm64, Xcode clang 21, Lean 4.35). Linux is expected to work the same way but has
not been run.

## Reading the report

Coverage is measured on the generated C, not on the Lean source, so the numbers are an approximation:

| Column | Meaning |
| :--- | :--- |
| functions | compiled functions that were called at least once |
| regions | C code regions executed at least once (close to statement coverage, C0) |
| branch arms | taken arms of C conditions (close to branch coverage, C1) |

Two kinds of code are left out so that the numbers reflect what a test can reach:

- **Compiler-generated helpers**: boxed wrappers, constructor eliminators, derived instances
  (`Repr`, `DecidableEq`, enum conversions), constant initializers, equation-lemma splitters, and
  wrappers that only forward to an `___redArg` variant.
- **Object reuse paths**: branches that test whether an object is shared before reusing it
  (`isShared`, `reuseFailAlloc`, `resetjp`, `reusejp`). They depend on reference counts, not on the
  behavior under test. The report prints how many regions and arms were excluded, so the exclusion
  stays visible.

Branches inside big-number arithmetic live in `lean.h` and are not part of the library files.

## Findings

State on 2026-11-04, after adding the run-time driver:

| Measure | Result |
| :--- | :--- |
| functions | 99.0% (102 of 103) |
| regions | 98.0% (1204 of 1228) |
| branch arms | 94.5% (450 of 476) |
| excluded object reuse paths | 99 regions, 190 arms |

The report found real test gaps, for example uppercase letters `A`–`Z` as Punycode digits and
characters above `9` after the digit range are never decoded, a BOM prefix that is only partly
present is never decoded, and `utf8PercentEncodeCodePoint` is never called. The remaining gaps are
tracked in `docs/todo.md`.

## Adding tests

A test only counts if it is reachable from `UrllibTest/CoverageMain.lean`. Write cases as data:

- a table of cases and a `*Failures` function that returns the names of failing cases, or
- a `guardChecks` list of named `UrllibTest.Check` values.

Keep the `#guard_msgs` check next to the table so that `lake test` still verifies it, and call the
table from `CoverageMain.lean`.

## Alternatives considered

- **Mutation testing** ([jubnzv/Mutate.lean](https://github.com/jubnzv/Mutate.lean)) measures whether
  tests detect changes, not which code runs. It complements coverage; it has no license, so it is not
  used here.
- **Instrumenting the elaborator-time tests** is not possible: `#guard` runs in the interpreter, and
  no coverage data is produced.
