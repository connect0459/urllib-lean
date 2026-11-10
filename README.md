# urllib-lean

[![CI](https://github.com/connect0459/urllib-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/connect0459/urllib-lean/actions/workflows/ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](https://github.com/connect0459/urllib-lean/blob/main/LICENSE)

A [Lean 4](https://lean-lang.org) implementation of the [URL Standard](https://url.spec.whatwg.org/), aiming at conformance with the Web Platform Tests and at machine-checked properties of its core algorithms.

This library is a Lean counterpart of [connect0459/urllib](https://github.com/connect0459/urllib) (MoonBit).

## Packages

| Module | Main declarations |
| :--- | :--- |
| `Urllib.Punycode` | `encode : String → String`, `decode : String → Except DecodeError String` |
| `Urllib.PercentEncoding` | `EncodeSet`, `utf8PercentEncode`, `percentEncodeBytes`, `percentDecode`, `utf8DecodeWithoutBom`, `utf8DecodeWithoutBomOrFail` |
| `Urllib.FormUrlencoded` | `parse : String → Pairs`, `parseBytes`, `serialize : Pairs → String` |
| `Urllib.SearchParams` | `ofString`, `append`, `delete`, `get`, `getAll`, `has`, `set`, `sort` (UTF-16 order), `toString` |
| `Urllib.Idna` | `toAscii`, `toUnicode` (UTS #46, nontransitional, Unicode 18.0.0), `Idna.Options`, `Options.whatwg` |
| `Urllib.Unicode.Normalization` | `nfc` (Normalization Form C) |
| `Urllib.Host` | `Host`, `Host.parse (input : String) (isOpaque : Bool)`, `Host.serialize`, `Host.Ipv4`, `Host.Ipv6` |

Domains are processed with UTS #46 as the URL Standard specifies (nontransitional processing, `CheckHyphens` off, `CheckBidi` and `CheckJoiners` on, STD3 rules and DNS length checks off); a failure is reported as `Host.Error.idna`. The Unicode data tables are generated from Unicode 18.0.0 by `scripts/generate_unicode_data.py` and committed.

## Status

Pre-release (v0.1.0 in preparation). Nothing is published yet.

| Component | State |
| :--- | :--- |
| Punycode (RFC 3492) with a round-trip proof | Done |
| Percent-encoding and host parsing | Done |
| form-urlencoded | Done |
| URLSearchParams (standalone) | Done |
| UTS #46 (IDNA) | Done |
| URL parser and WPT conformance | Planned |
| URL Pattern Standard | Planned |

v0.1.0 will be released once all of the above are implemented.

## Installation

Once published, add the package to your `lakefile.toml`:

```toml
[[require]]
name = "Urllib"
scope = "connect0459"
```

## Usage

```lean
import Urllib
open Urllib

#eval Punycode.encode "münchen"                -- "mnchen-3ya"
#eval Punycode.decode "mnchen-3ya"             -- Except.ok "münchen"

#eval PercentEncoding.utf8PercentEncode .path "a b/ü?"   -- "a%20b/%C3%BC%3F"
#eval PercentEncoding.utf8DecodeWithoutBom
  (PercentEncoding.percentDecodeString "%E3%81%82%20b")  -- "あ b"
#eval PercentEncoding.percentEncodeBytes .path (ByteArray.mk #[0x61, 0x20, 0xFF])  -- "a%20%FF"
#eval PercentEncoding.utf8DecodeWithoutBomOrFail (ByteArray.mk #[0xFF])  -- none

#eval FormUrlencoded.parse "a=b+c&d=%41"        -- [("a", "b c"), ("d", "A")]
#eval FormUrlencoded.serialize [("a b", "c&d")] -- "a+b=c%26d"

#eval Idna.toAscii (Idna.Options.whatwg false) "bücher.de"  -- Except.ok "xn--bcher-kva.de"
#eval (Idna.toUnicode (Idna.Options.whatwg false) "xn--bcher-kva.de").1  -- "bücher.de"

#eval Host.parse "EXAMPLE.com" false           -- Except.ok (Host.domain "example.com")
#eval Host.parse "faß.de" false                -- Except.ok (Host.domain "xn--fa-hia.de")
#eval (Host.parse "0x7f.1" false).map Host.serialize     -- Except.ok "127.0.0.1"
#eval (Host.parse "[2001:db8:0:0:1:0:0:1]" false).map Host.serialize
                                               -- Except.ok "[2001:db8::1:0:0:1]"
```

## Compliance

The percent-encoding and host algorithms follow the URL Standard but are not yet checked against the Web Platform Tests; WPT conformance arrives with the URL parser. UTS #46 is checked against every line of `IdnaTestV2.txt` of Unicode 18.0.0 (except two lines with unpaired surrogates, which a Lean string cannot hold) under four flag settings.

### Proved properties

All proofs are checked by Lean; no `sorry` or additional axiom is used.

- `Punycode.decode_encode`: `decode (encode s) = .ok s` for every string.
- `Punycode.encode_isAscii`: the output of `encode` is ASCII.
- `Punycode.reference_encode_eq`: the scanning encoder of RFC 3492 equals `encode`.
- `PercentEncoding.percentDecode_utf8PercentEncode`: decoding after encoding restores the input when `%` is in the set or absent from the input (unconditionally for the component set).
- `PercentEncoding.utf8PercentEncode_wellEncoded`: the output is a sequence of unencoded characters and `%XX` escapes.
- `Host.Ipv4.parse_serialize` and `Host.Ipv6.parse_serialize`: parsing the serialization of an address returns the address.
- `Idna.toAsciiChars_idempotent`: processing the result of a successful UTS #46 ToASCII again returns it unchanged.
- `Idna.toAsciiChars_ok_clean`: the result of a successful ToASCII consists of ASCII code points that the mapping table keeps as is.
- `Idna.nfc_ascii`: Normalization Form C does not change an ASCII string.
- `Host.parse_serialize_of_parse`: a successfully parsed host re-parses to itself after serialization.

## Documentation

Every public declaration carries a doc-string. Proofs live in the `Spec` module next to each implementation module.

- [docs/coverage.md](https://github.com/connect0459/urllib-lean/blob/main/docs/coverage.md) : Coverage measurement and accepted gaps

## Contributing

See [CONTRIBUTING.md](https://github.com/connect0459/urllib-lean/blob/main/CONTRIBUTING.md).

## License

[Apache-2.0](https://github.com/connect0459/urllib-lean/blob/main/LICENSE)
