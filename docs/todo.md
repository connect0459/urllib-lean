# todo - urllib-lean

Current state: **M1 (Punycode) and M2 (percent-encoding, host parsing) implemented and tested; round trips proved for Punycode, percent-encoding, IPv4, and IPv6**  
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
- [x] **Round trip** — `decode (encode s) = .ok s` for every string (`Punycode.decode_encode`); `encode` is stated through an insertion plan (non-basic code points sorted by value and position), and it is proved equal to the RFC scanning algorithm kept in `Reference.encode`
- [x] **Basic code points preserved** — the encoding is the basic code points of the input in their original order, then a hyphen when there is at least one, then an extension without hyphens (`Punycode.encode_basic_prefix`, `encode_basic_prefix_of_nonempty`, `encode_no_delimiter_of_no_basic`)
- [x] **Scanning encoder equals the plan-based encoder** — `Reference.encode = encode` for every string (`Punycode.reference_encode_eq`); the differential tests on the RFC samples and 3000 generated strings remain as a regression check
- [x] **No `sorry` / `axiom`** — only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`) are used

### Refactor

- [ ] **Tidy names and module layout** — per `AGENTS.md` naming rules
- [ ] **Separate executable core from proofs** — proofs in a companion module so the core stays readable

---

## M2: Percent-encoding and host parsing

### Decisions to make before implementation

- [x] **Domain handling without UTS #46** — full IDNA processing (mapping table, NFC, Bidi / Joiners) is out of scope for v0.1.0; non-ASCII domains are rejected with `nonAsciiDomain`, and ASCII domains are lowercased with `xn--` labels passed through unchanged (as in the MoonBit `urllib`)
- [x] **Module layout** — `Urllib.PercentEncoding` and `Urllib.Host` (with `Ipv4`, `Ipv6`, `OpaqueHost`); `Host` depends on `PercentEncoding` and `Punycode`, never the reverse
- [x] **`Host` representation** — an inductive type (`domain`, `ipv4`, `ipv6`, `opaqueHost`, `empty`); invariants are established by `Host.parse`; smart constructors are deferred until the URL parser (M3) shows which invariants callers rely on

### Percent-encoding (WHATWG URL Standard, section 1.3)

- [x] **Red** — tests for each percent-encode set, UTF-8 percent-encode, percent-decode, and the replacement behavior of UTF-8 decode (`UrllibTest/PercentEncoding.lean`)
- [x] **Percent-encode sets** — C0 control, fragment, query, special-query, path, userinfo, component (cross-checked against the MoonBit `urllib` definitions; note the component set contains `%` through its `$`–`&` range)
- [x] **UTF-8 percent-encode** — code point and string variants
- [x] **Percent-decode** — byte sequence and string variants; UTF-8 decode without BOM (replacement decoding, checked against an independent decoder)
- [x] **Proof: single-byte escape round trip** — decoding `%XX` yields the original byte for all 256 bytes (`decodeBytes_percentEncodeByte`)
- [x] **Proof: decode after encode** — `percentDecode (utf8PercentEncode set s).toUTF8 = s.toUTF8` when `%` is in the set or absent from `s` (`percentDecode_utf8PercentEncode`); for the component set it holds for every input; for the other sets a literal `%41` decodes to `A`, so the unconditional statement is false
- [x] **Proof: encoded output** — the output of `utf8PercentEncode` is `WellEncoded`: a sequence of characters outside the set, kept as is, and `%XX` escapes of single bytes (`utf8PercentEncode_wellEncoded`); an escape is a percent sign followed by two uppercase hexadecimal digits (`percentEncodeByteChars_form`, `hexDigit_upper_hex`)

### Host parsing (WHATWG URL Standard, section 3)

- [x] **Red** — tests for each host kind (`UrllibTest/Host.lean`, `UrllibTest/Host/Ipv4.lean`, `UrllibTest/Host/Ipv6.lean`); WPT host vectors arrive with the URL parser in M3
- [x] **Forbidden host / domain code points** — predicates
- [x] **IPv4 parser** — number parsing (decimal / octal / hex), part-count rules, overflow, "ends in a number" checker
- [x] **IPv6 parser** — compression, embedded IPv4, validation errors
- [x] **Opaque host parser** — forbidden code point check and C0 percent-encoding
- [x] **Domain host parser** — percent-decode, ASCII lowercase, forbidden code points, non-ASCII rejection per the decision above
- [x] **Host serializer** — IPv4 dotted form, IPv6 with the longest zero run compressed
- [x] **Proof: IPv4 round trip** — `Ipv4.parse a.serialize = .ok a` for every address (`Ipv4.parse_serialize`)
- [x] **Proof: IPv6 round trip** — `Ipv6.parse a.serialize = .ok a` for every address (`Ipv6.parse_serialize`); it holds for any compression point at a zero piece, so the longest-run choice is covered by tests only
- [x] **Proof: serialization idempotence** — if `Host.parse input isOpaque = .ok h`, then `Host.parse (Host.serialize h) isOpaque = .ok h` (`Host.parse_serialize_of_parse`), hence `serialize (parse (serialize h)) = serialize h`; IPv4 and IPv6 hosts also re-parse to themselves for every address

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
