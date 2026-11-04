# Contributing

## Prerequisites

- [elan](https://github.com/leanprover/elan) — Lean toolchain manager (`lean` and `lake` are installed from `lean-toolchain`)
- [just](https://just.systems/) — task runner
- [pre-commit](https://pre-commit.com/) — hook runner

## Setup

```sh
git clone https://github.com/connect0459/urllib-lean
cd urllib-lean
just setup
```

`just setup` runs `lake update` to fetch dependencies and installs the pre-commit hooks (`pre-commit install`).

### pre-commit hooks

To run all hooks manually:

```sh
pre-commit run --all-files
```

## Development workflow

| Command | Purpose |
| :--- | :--- |
| `lake build` | Build the library |
| `lake build --wfail` | Build and fail on any warning (as CI does) |
| `lake test` | Build and run the test library |
| `just coverage` | Measure test coverage (see [docs/coverage.md](docs/coverage.md)) |
| `just verify` | Run the full CI-equivalent check locally |

Before opening a pull request, run the full verification suite:

```sh
just verify
```

## Testing guidelines

This project follows **Red → Green → Refactor** (Detroit-school TDD):

- Write a failing test first, then implement.
- Use real objects; mocks are only permitted at external boundaries.
- Test names describe **what business rule** is verified, not how.

Specifications are written as `example` and `#guard` in `UrllibTest/`. Where a property holds for all inputs, state it as a `theorem` as well.

## Commit format

```text
<type>(<scope>): <subject>
```

**Types**: `feat`, `fix`, `docs`, `style`, `refactor`, `tidy`, `test`, `chore`, `ci`, `perf`

**Scope**: module name when the change targets a specific module (`punycode`, `host`); omit for project-wide changes.

**Subject**: imperative mood, 72 characters max, no trailing period.

Examples:

```text
feat(punycode): add RFC 3492 encoder
fix(host): reject empty IPv6 zone identifiers
tidy(punycode): name the bias adaptation constants
```

## Pull request process

1. Fork the repository and create a branch: `feat/xxx`, `fix/xxx`, `docs/xxx`.
2. Follow the Red → Green → Refactor cycle.
3. Run `just verify` and commit any resulting diffs.
4. If the change touches the public API, update `README.md` so it reflects the new behaviour.
5. Open a pull request. `sorry` and `axiom` are not accepted.

## Code style

- No code comments unless the **why** is genuinely non-obvious.
- Prefer immutability; avoid mutable state unless necessary.
- Keep the executable definition and its specification separate.
- All user-facing strings (test names, error messages, doc comments) must be in **English**.
