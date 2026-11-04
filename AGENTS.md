# Project Agents.md Guide

This is a [Lean 4](https://lean-lang.org) project: a WHATWG-oriented URL library with machine-checked properties.

## Language Convention

This project may be released publicly. All of the following must be written in **English**:

- Commit messages
- Code comments
- Documentation (including `AGENTS.md`, `README.md`, etc.)
- Test names
- Error messages

## Project Structure

- `lakefile.toml` declares two libraries: `Urllib` (the public library) and `UrllibTest` (tests, run by `lake test`).
- Modules live under `Urllib/` and are re-exported from the root `Urllib.lean`.
- Tests live under `UrllibTest/` and mirror the module layout (`Urllib/Punycode.lean` → `UrllibTest/Punycode.lean`).
- `lean-toolchain` pins the Lean version; bump it deliberately in its own commit.
- `autoImplicit` is disabled; declare every variable explicitly.

## Coding convention

- Separate the executable definition (`def`) from its specification (`theorem`); a module's proofs may live in a companion file so the executable core stays readable.
- Prefer total functions. Use `partial` or `unsafe` only with the user's approval.
- `sorry` and `axiom` must never be committed. A proof that is not finished stays on a branch.
- Prefer immutable structures and value-based equality (`deriving DecidableEq, Repr`).
- Name accessors after the field (`url.host`), not `getHost`.

## Tooling

- `lake build --wfail` builds the library and treats warnings as errors.
- `lake test` builds `UrllibTest`; a failing `#guard` or `example` fails the build.
- For local quality verification, use two mechanisms:
  - **pre-commit hooks** — catch formatting and build issues on every commit (`pre-commit run --all-files` to run manually).
  - **`just verify`** — run the CI-equivalent check (build, test, hooks) before opening a PR.
- When a change affects the public API, update `README.md` in the same PR.

## Testing

- Express specifications as `example` and `#guard` in `UrllibTest/`; use `#guard_msgs` for diagnostic output.
- Use RFC / WPT test vectors verbatim where they exist, and cite the source in the commit message rather than in the code.
- A theorem about a function is a test of its universal behavior; keep a few concrete `example`s next to it so a regression is readable.

## Development Philosophy

### Red/Green TDD (Detroit school)

- Red → Green → Refactor cycle strictly followed
- Use real objects; mocks are only permitted at external boundaries (file system, external API, network)
- Write tests BEFORE implementation; run tests AFTER implementation
- Discuss coverage targets with the user before starting implementation

### Domain Object Design

- Rich domain objects: pair data and logic in the same type
- Prefer immutability; avoid mutable state unless necessary
- Distinguish entities (identity-based) from value objects (value-based)
- Enforce layer boundaries through abstract types; no direct dependency on concrete implementations

### Evergreen Tests

- Test names describe WHAT business rule is being verified, not HOW
- Test names must not reference implementation details
- Test code serves as living documentation of the system's behavior

### Code Comments

- Do NOT write code comments unless explicitly permitted by the user
- Let the code speak for itself; let tests document the behavior
- Code = How, Tests = What, Commit messages = Why

## Git Conventions

### Format

```text
<type>(<scope>): <subject>

<body>

<footer>
```

### Types

| Type | Description |
| :--- | :--- |
| `feat` | New feature |
| `fix` | Bug fix |
| `docs` | Documentation only |
| `style` | Code style (formatting, whitespace) |
| `refactor` | Code change that is neither a fix nor a feature |
| `tidy` | Small, safe cleanup (< 2 min; no behavior change) |
| `test` | Adding or updating tests |
| `chore` | Build process, tooling, or config changes |
| `ci` | CI/CD pipeline changes (GitHub Actions, workflows) |
| `perf` | Performance improvement |

### Scopes

Scope is optional; use the module name when the change targets a specific module (e.g., `punycode`, `host`). Omit for project-wide changes.

### Type vs. Scope Precedence

The type vocabulary above mixes two axes: an **impact axis** (`feat`, `fix`, `perf`, `refactor` — the SemVer-relevant effect of a change) and a **domain axis** (`docs`, `style`, `test`, `chore`, `ci`, `tidy` — a layer with no runtime/SemVer effect). When a change is fully contained within a domain, use that domain as `type` (e.g. `docs: fix typo`); do not use it as `scope` on an impact-axis type (avoid `fix(docs): ...`). `scope` sub-divides whatever `type` already established (e.g. `feat(auth)`); it is not a substitute classification axis. This also matches how release automation typically bumps versions from `type` alone, without inspecting `scope`.

### Subject Line

- Use the imperative mood: "add", "fix", "remove" — not "added" or "adds"
- 72 characters max
- No trailing period

### Body (optional)

- Explain **why**, not what — the diff already shows what changed

### Footer (optional)

- `BREAKING CHANGE: <description>` for breaking changes
- `Closes <https://github.com/owner/repo/issues/123>` to link issues

### Branch naming

`feat/xxx`, `fix/xxx`, `docs/xxx`
