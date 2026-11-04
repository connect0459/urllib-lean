# todo - urllib-lean

Current state: **M1 Punycode and M2 percent-encoding implemented and tested; host parsing not started; full round-trip proofs open**  
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
- [ ] **Coverage measurement spike** — no Lean coverage tool exists (`jubnzv/Mutate.lean` offers mutation testing, a complementary measure of test strength, not C0/C1, and has no license); evaluate compiling the library with `--coverage` (gcov / llvm-cov on Lean's generated C) and running the test vectors from a `lean_exe` driver, because `#guard` runs in the elaborator and is not measured; until then, track branches by hand against the test matrix
- [ ] **Verify the first CI run** — the `leanprover/lean-action` inputs (`build-args`, `test`, `lint`, `use-github-cache`) are unverified
- [x] **Remove `UrllibTest/.gitkeep`** — once the first test file exists
- [x] **Run `pre-commit install`** — via `just setup`

---

## M1: Punycode (RFC 3492)

### Decisions to make before implementation

- [x] **Coverage target** — C0 (statement) and C1 (branch) coverage: 100% where achievable, 90% as the floor; proof-only declarations (`theorem`) are excluded from the measurement
- [x] **Public API shape** — `encode : String → String` (total) and `decode : String → Except DecodeError String`, both over code points
- [x] **Error model** — `DecodeError`: `nonBasicCodePoint`, `invalidDigit`, `truncated`, `invalidCodePoint`; no `overflow` because `Nat` arithmetic cannot overflow, so an out-of-range result surfaces as `invalidCodePoint`
- [x] **Dependency policy** — Lean core only; no external packages

### Red — specification as tests (`UrllibTest/Punycode.lean`)

- [x] **RFC 3492 section 7.1 sample strings** — all 19 samples (A–S), cross-checked against an independent implementation, as encode and decode vectors
- [x] **Edge cases** — empty input, ASCII-only input (trailing delimiter), single non-ASCII code point, supplementary-plane code point, delimiter-only input
- [x] **Failure cases** — invalid digit, truncated input, non-basic code point before the delimiter, out-of-range code point

### Green — implementation (`Urllib/Punycode.lean`)

- [x] **Constants** — `base`, `tMin`, `tMax`, `skew`, `damp`, `initialBias`, `initialN`, delimiter
- [x] **Digit mapping** — `charToDigit?` / `digitToChar`
- [x] **Bias adaptation** — `adapt`
- [x] **Encoder** — `encode`
- [x] **Decoder** — `decode`
- [x] **Totality** — no `partial` / `unsafe`; `adaptLoop` and `encodeIntegerFrom` terminate by proof, the two outer loops by fuel

### Proofs (`Urllib/Punycode/Spec.lean`)

- [x] **Output is ASCII** — every code point of `encode s` is below 128 (`encode_isAscii`)
- [x] **Variable-length integer round trip** — `decodeInteger` inverts `encodeIntegerFrom` (`decodeInteger_encodeIntegerFrom`)
- [ ] **Round trip** — `decode (encode s) = .ok s` for every input accepted by `encode`
- [ ] **Basic code points preserved** — the prefix before the delimiter equals the basic code points of the input
- [x] **No `sorry` / `axiom`** — only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`) are used

### Refactor

- [ ] **Tidy names and module layout** — per `AGENTS.md` naming rules
- [ ] **Separate executable core from proofs** — proofs in a companion module so the core stays readable

---

## M2: Percent-encoding and host parsing

### Decisions to make before implementation

- [ ] **Domain handling without UTS #46** — full IDNA processing (mapping table, NFC, Bidi / Joiners) is out of scope for v0.1.0; agree on the interim behavior for non-ASCII domains (reject with a dedicated error vs. Punycode-encode labels without mapping)
- [x] **Module layout** — `Urllib.PercentEncoding` and `Urllib.Host` (with `Ipv4`, `Ipv6`, `OpaqueHost`); `Host` depends on `PercentEncoding` and `Punycode`, never the reverse
- [ ] **`Host` representation** — an inductive type (`domain`, `ipv4`, `ipv6`, `opaque`, `empty`) with smart constructors that enforce the invariants

### Percent-encoding (WHATWG URL Standard, section 1.3)

- [x] **Red** — tests for each percent-encode set, UTF-8 percent-encode, percent-decode, and the replacement behavior of UTF-8 decode (`UrllibTest/PercentEncoding.lean`)
- [x] **Percent-encode sets** — C0 control, fragment, query, special-query, path, userinfo, component (cross-checked against the MoonBit `urllib` definitions; note the component set contains `%` through its `$`–`&` range)
- [x] **UTF-8 percent-encode** — code point and string variants
- [x] **Percent-decode** — byte sequence and string variants; UTF-8 decode without BOM (replacement decoding, checked against an independent decoder)
- [x] **Proof: single-byte escape round trip** — decoding `%XX` yields the original byte for all 256 bytes (`decodeBytes_percentEncodeByte`)
- [ ] **Proof: decode after encode** — `percentDecode (utf8PercentEncode set s).toUTF8 = s.toUTF8`, which holds only when `%` is in the set (component) or absent from `s`; for the other sets a literal `%41` decodes to `A`, so the unconditional statement is false
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
