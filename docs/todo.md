# todo - urllib-lean

Current state: **Punycode, percent-encoding, and host parsing are implemented, tested, and proved; coverage measured; the rest of the v0.1.0 scope is planned below**  
Target: **v0.1.0 = feature parity with the MoonBit reference implementation's v0.1.0 (URL parser with WPT conformance, URLSearchParams, IDNA / UTS #46, URL Pattern), built on the completed Punycode, percent-encoding, and host foundations**

Milestone numbers (M1–M4) are retired: work is ordered by dependency (see "Remaining scope for v0.1.0"). The scope is frozen as of 2026-11-04; anything discovered later goes to a later release.

Proofs are added incrementally: each remaining component is first specified by tests (WPT vectors where they exist), and machine-checked properties follow as separate steps. The proof scope per component is decided when that component starts.

---

## Infrastructure

- [x] **Lake project** — `Urllib` library, `UrllibTest` test library, `autoImplicit = false`, Lean v4.35.0 pinned
- [x] **License** — Apache-2.0
- [x] **Community standard files** — `CODE_OF_CONDUCT.md`, `CONTRIBUTING.md`, `SECURITY.md`, PR / issue templates
- [x] **Agent guide** — `AGENTS.md` (`CLAUDE.md` is a symlink)
- [x] **Quality gates** — pre-commit hooks (`lake build --wfail`, `lake test`, markdownlint), `justfile`
- [x] **CI** — `.github/workflows/ci.yml`, dependabot
- [ ] **Create the GitHub repository and push** — `connect0459/urllib-lean`; do this before the release so that CI is verified early
- [x] **Coverage measurement** — `just coverage` builds an instrumented copy with the system clang and summarizes the library on the generated C (see `docs/coverage.md`); the floor is met: functions 99.0%, regions 98.0%, branch arms 94.5%, with compiler-generated helpers and object reuse branches reported separately
- [x] **Close the remaining coverage gaps** — functions, regions, and branch arms of the library are at 100% (see `docs/coverage.md`); 7 regions and 7 arms are accepted as unreachable by construction in `scripts/coverage_accepted.json`, each with a reason
- [ ] **Run the coverage script on Linux** — verified on macOS only; add a CI job once it runs there
- [ ] **Verify the first CI run** — the `leanprover/lean-action` inputs (`build-args`, `test`, `lint`, `use-github-cache`) are unverified
- [x] **Remove `UrllibTest/.gitkeep`** — once the first test file exists
- [x] **Run `pre-commit install`** — via `just setup`

---

## Done: Punycode (RFC 3492)

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

## Done: Percent-encoding and host parsing

### Decisions to make before implementation

- [x] **Domain handling without UTS #46** — full IDNA processing (mapping table, NFC, Bidi / Joiners) is deferred to the UTS #46 item below; until then non-ASCII domains are rejected with `nonAsciiDomain`, and ASCII domains are lowercased with `xn--` labels passed through unchanged (as in other existing implementations)
- [x] **Module layout** — `Urllib.PercentEncoding` and `Urllib.Host` (with `Ipv4`, `Ipv6`, `OpaqueHost`); `Host` depends on `PercentEncoding` and `Punycode`, never the reverse
- [x] **`Host` representation** — an inductive type (`domain`, `ipv4`, `ipv6`, `opaqueHost`, `empty`); invariants are established by `Host.parse`; smart constructors are deferred until the URL parser shows which invariants callers rely on

### Percent-encoding (WHATWG URL Standard, section 1.3)

- [x] **Red** — tests for each percent-encode set, UTF-8 percent-encode, percent-decode, and the replacement behavior of UTF-8 decode (`UrllibTest/PercentEncoding.lean`)
- [x] **Percent-encode sets** — C0 control, fragment, query, special-query, path, userinfo, component (cross-checked against existing implementations; note the component set contains `%` through its `$`–`&` range)
- [x] **UTF-8 percent-encode** — code point and string variants
- [x] **Percent-decode** — byte sequence and string variants; UTF-8 decode without BOM (replacement decoding, checked against an independent decoder)
- [x] **Proof: single-byte escape round trip** — decoding `%XX` yields the original byte for all 256 bytes (`decodeBytes_percentEncodeByte`)
- [x] **Proof: decode after encode** — `percentDecode (utf8PercentEncode set s).toUTF8 = s.toUTF8` when `%` is in the set or absent from `s` (`percentDecode_utf8PercentEncode`); for the component set it holds for every input; for the other sets a literal `%41` decodes to `A`, so the unconditional statement is false
- [x] **Proof: encoded output** — the output of `utf8PercentEncode` is `WellEncoded`: a sequence of characters outside the set, kept as is, and `%XX` escapes of single bytes (`utf8PercentEncode_wellEncoded`); an escape is a percent sign followed by two uppercase hexadecimal digits (`percentEncodeByteChars_form`, `hexDigit_upper_hex`)

### Host parsing (WHATWG URL Standard, section 3)

- [x] **Red** — tests for each host kind (`UrllibTest/Host.lean`, `UrllibTest/Host/Ipv4.lean`, `UrllibTest/Host/Ipv6.lean`); WPT host vectors arrive with the URL parser
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

## Gap analysis against the reference implementations

Compared with existing URL implementations in other languages, restricted to the already implemented parts (Punycode, percent-encoding, host parsing).

### No gap

- **Punycode** — constants, `adapt`, digit mapping, encoder, decoder, and error cases match; the reference encode / decode entry points correspond to `decode` / `encode`
- **Percent-encode sets** — fragment, query, special-query, path, and userinfo match the reference definitions; the component set is an addition
- **Forbidden host code points** — the forbidden host set matches; the forbidden domain set follows the URL Standard (forbidden host + C0 controls + `%` + U+007F)
- **IPv4 / IPv6 / opaque host** — same rules as the references, plus machine-checked round trips

### Decided differences (no action)

- **Extra forbidden domain code points in a reference implementation** — U+FFFD, noncharacters, U+00A0, and U+3000 are rejected after UTS #46 mapping; unreachable here because non-ASCII domains are rejected earlier (`nonAsciiDomain`)
- **UTS #46 / `domain_to_unicode`** — not implemented yet; planned below (see the domain handling decision)

### Candidate gaps

- [x] **Percent-encode a byte sequence** — `percentEncodeBytes` and `EncodeSet.containsByte`; agrees with `utf8PercentEncode` on the UTF-8 bytes of a string (checked by tests on every set; not proved)
- [x] **Strict UTF-8 decode** — `utf8DecodeWithoutBomOrFail` returns `none` on malformed input (truncated, overlong, surrogate, above U+10FFFF, stray continuation)
- [x] **`Host.empty` is never produced by `Host.parse`** — the opaque-host parser now returns `.empty` for empty input; `Host.parse_serialize_of_parse` covers it, and an empty domain stays an error (`emptyDomain`)
- [ ] **`application/x-www-form-urlencoded` parse / serialize** — found by comparing against the reference implementations; WHATWG URL Standard section 5.1; planned as the first item of the remaining scope
- [ ] **Opaque-path trailing-space encoding** — deferred to the URL parser: its behavior is defined by the URL parser's handling of `?` and `#` after an opaque path, so it cannot be specified or tested in isolation

---

## Remaining scope for v0.1.0

Ordered by dependency. Each item: Red (tests, WPT vectors verbatim where they exist) → Green → Refactor; proofs are added incrementally and recorded per item. Coverage targets are agreed with the user before each item starts.

1. [ ] **form-urlencoded** (`Urllib.FormUrlencoded`) — parse / serialize per URL Standard section 5.1; depends on `PercentEncoding`; WPT `urlencoded-parser` vectors
2. [ ] **URLSearchParams, standalone part** — list of name-value pairs with `append`, `delete`, `get`, `getAll`, `has`, `set`, `sort`, `toString`; the `sort` order must follow UTF-16 code units, which differs from code point order for supplementary-plane characters (decide the comparison before implementing); WPT `urlsearchparams-*` vectors
3. [ ] **UTS #46 / IDNA** — mapping and status tables (pinned Unicode version, generated), NFC, Bidi and Joiner checks, `domainToAscii` / `domainToUnicode`; replaces the `nonAsciiDomain` rejection in `Host.parseDomain`; WPT `IdnaTestV2` vectors
4. [ ] **URL parser** — state machine, URL record, serializer, getters; WPT `urltestdata` vectors; closes the opaque-path trailing-space gap above
5. [ ] **URL setters and helpers** — setters, path utilities, file URL helpers, relative resolution
6. [ ] **URLSearchParams / URL binding** — the update steps that tie a `URLSearchParams` to a URL's query
7. [ ] **URL Pattern** — tokenizer, pattern parser, constructor-string parser, matching, `generate`, `compare_component`; WPT `urlpattern` vectors
8. [ ] **Proofs** — added incrementally per component; candidates: form-urlencoded round trip, UTF-16 order of `sort`, serializer idempotence of the URL parser

---

## Release v0.1.0

- [x] **README** — usage examples for `Urllib.Punycode`, `Urllib.PercentEncoding`, and `Urllib.Host`, API summary, statement of proved properties
- [x] **Docs for public API** — doc-strings on every public declaration; `weak.linter.missingDocs` is enabled for `Urllib` in `lakefile.toml`
- [ ] **Status table** — keep the component table in `README.md` current as each item lands
- [ ] **CHANGELOG** — create `CHANGELOG.md` with a `[0.1.0]` section (deferred until release time)
- [ ] **Version** — confirm `version = "0.1.0"` in `lakefile.toml`
- [ ] **Full verification** — `just verify` passes locally and CI is green on `main`
- [ ] **Tag** — `git tag v0.1.0 && git push origin v0.1.0`
- [ ] **Reservoir** — confirm the package is indexed at `reservoir.lean-lang.org/@connect0459/Urllib`
- [ ] **GitHub Release** — notes derived from the CHANGELOG entry
