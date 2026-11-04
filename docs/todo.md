# todo - urllib-lean

Current state: **project scaffold only (no library code yet)**  
Target: **v0.1.0 = M1 (Punycode, RFC 3492, with a machine-checked round-trip property) + M2 (percent-encoding and host parsing)**

Later milestones (not in v0.1.0): M3 URL parser and WPT conformance, M4 URL Pattern Standard. See the milestone table in `README.md`.

---

## Infrastructure

- [x] **Lake project** — `Urllib` library, `UrllibTest` test library, `autoImplicit = false`, Lean v4.35.0 pinned
- [x] **License** — Apache-2.0
- [x] **Community standard files** — `CODE_OF_CONDUCT.md`, `CONTRIBUTING.md`, `SECURITY.md`, PR / issue templates
- [x] **Agent guide** — `AGENTS.md` (`CLAUDE.md` is a symlink)
- [x] **Quality gates** — pre-commit hooks (`lake build --wfail`, `lake test`, markdownlint), `justfile`
- [x] **CI** — `.github/workflows/ci.yml`, dependabot
- [ ] **Create the GitHub repository and push** — `connect0459/urllib-lean`
- [ ] **Verify the first CI run** — the `leanprover/lean-action` inputs (`build-args`, `test`, `lint`, `use-github-cache`) are unverified
- [ ] **Remove `UrllibTest/.gitkeep`** — once the first test file exists
- [ ] **Run `pre-commit install`** — via `just setup`

---

## M1: Punycode (RFC 3492)

### Decisions to make before implementation

- [ ] **Coverage target** — agree on a target with the user before writing code
- [ ] **Public API shape** — `encode` / `decode` over `String` (code points) with an error type, vs. `Array UInt32`
- [ ] **Error model** — `Except PunycodeError` variants (overflow, invalid digit, invalid input)
- [ ] **Dependency policy** — Lean core and `Std` only; no external packages

### Red — specification as tests (`UrllibTest/Punycode.lean`)

- [ ] **RFC 3492 section 7.1 sample strings** — all 19 samples (A–S) as `#guard` round-trip vectors
- [ ] **Edge cases** — empty input, ASCII-only input (basic code points only, trailing delimiter), single non-ASCII code point
- [ ] **Failure cases** — invalid digit, truncated input, integer overflow

### Green — implementation (`Urllib/Punycode.lean`)

- [ ] **Constants** — `base`, `tMin`, `tMax`, `skew`, `damp`, `initialBias`, `initialN`, delimiter
- [ ] **Digit mapping** — `basicToDigit` / `digitToBasic`
- [ ] **Bias adaptation** — `adapt`
- [ ] **Encoder** — `encode`
- [ ] **Decoder** — `decode`
- [ ] **Totality** — no `partial` / `unsafe`; termination proved or structurally evident

### Proofs (`Urllib/Punycode/Spec.lean`)

- [ ] **Output is ASCII** — every code point of `encode s` is below 128
- [ ] **Round trip** — `decode (encode s) = .ok s` for every input accepted by `encode`
- [ ] **Basic code points preserved** — the prefix before the delimiter equals the basic code points of the input
- [ ] **No `sorry` / `axiom`** — checked by `lake build --wfail`; document any property deliberately left unproved

### Refactor

- [ ] **Tidy names and module layout** — per `AGENTS.md` naming rules
- [ ] **Separate executable core from proofs** — proofs in a companion module so the core stays readable

---

## M2: Percent-encoding and host parsing

### Decisions to make before implementation

- [ ] **Domain handling without UTS #46** — full IDNA processing (mapping table, NFC, Bidi / Joiners) is out of scope for v0.1.0; agree on the interim behavior for non-ASCII domains (reject with a dedicated error vs. Punycode-encode labels without mapping)
- [ ] **Module layout** — `Urllib.PercentEncoding` and `Urllib.Host` (with `Ipv4`, `Ipv6`, `OpaqueHost`); `Host` depends on `PercentEncoding` and `Punycode`, never the reverse
- [ ] **`Host` representation** — an inductive type (`domain`, `ipv4`, `ipv6`, `opaque`, `empty`) with smart constructors that enforce the invariants

### Percent-encoding (WHATWG URL Standard, section 1.3)

- [ ] **Red** — tests for each percent-encode set, UTF-8 percent-encode, and percent-decode (including invalid sequences and `%` at end of input)
- [ ] **Percent-encode sets** — C0 control, fragment, query, special-query, path, userinfo, component
- [ ] **UTF-8 percent-encode** — code point and string variants
- [ ] **Percent-decode** — byte sequence and string variants; UTF-8 decode without BOM
- [ ] **Proof: decode after encode** — `percentDecode (percentEncode set s) = s` as bytes, for every set
- [ ] **Proof: encoded output** — output contains only bytes outside the set, `%`-escapes, or unchanged members of the set's complement

### Host parsing (WHATWG URL Standard, section 3)

- [ ] **Red** — tests for each host kind, using WPT host vectors where they exist
- [ ] **Forbidden host / domain code points** — predicates
- [ ] **IPv4 parser** — number parsing (decimal / octal / hex), part-count rules, overflow, "ends in a number" checker
- [ ] **IPv6 parser** — compression, embedded IPv4, validation errors
- [ ] **Opaque host parser** — forbidden code point check and C0 percent-encoding
- [ ] **Domain host parser** — percent-decode, ASCII lowercase, forbidden code points, interim non-ASCII behavior per the decision above
- [ ] **Host serializer** — IPv4 dotted form, IPv6 with the longest zero run compressed
- [ ] **Proof: IPv4 round trip** — `parseIpv4 (serializeIpv4 a) = some a`
- [ ] **Proof: IPv6 round trip** — `parseIpv6 (serializeIpv6 a) = some a`
- [ ] **Proof: serialization idempotence** — `serialize (parse (serialize h)) = serialize h`

---

## Release v0.1.0

- [ ] **README** — usage examples for `Urllib.Punycode`, `Urllib.PercentEncoding`, and `Urllib.Host`, API summary, statement of proved properties, relationship to `ammkrn/lean-url`
- [ ] **Docs for public API** — doc-strings on every public declaration
- [ ] **Milestone table** — mark M1 and M2 as done in `README.md`
- [ ] **CHANGELOG** — create `CHANGELOG.md` with a `[0.1.0]` section (deferred until release time)
- [ ] **Version** — confirm `version = "0.1.0"` in `lakefile.toml`
- [ ] **Full verification** — `just verify` passes locally and CI is green on `main`
- [ ] **Tag** — `git tag v0.1.0 && git push origin v0.1.0`
- [ ] **Reservoir** — confirm the package is indexed at `reservoir.lean-lang.org/@connect0459/Urllib`
- [ ] **GitHub Release** — notes derived from the CHANGELOG entry
