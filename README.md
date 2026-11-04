# urllib-lean

[![CI](https://github.com/connect0459/urllib-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/connect0459/urllib-lean/actions/workflows/ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](https://github.com/connect0459/urllib-lean/blob/main/LICENSE)

A [Lean 4](https://lean-lang.org) implementation of the [URL Standard](https://url.spec.whatwg.org/), aiming at conformance with the Web Platform Tests and at machine-checked properties of its core algorithms.

This library is a Lean counterpart of [connect0459/urllib](https://github.com/connect0459/urllib) (MoonBit). It is independent of [ammkrn/lean-url](https://github.com/ammkrn/lean-url).

## Status

Early development. Nothing is published yet.

| Milestone | Scope | State |
| :--- | :--- | :--- |
| M1 | Punycode (RFC 3492) with a round-trip proof | Planned |
| M2 | Percent-encoding and host parsing | Planned |
| M3 | URL parser and WPT conformance | Planned |
| M4 | URL Pattern Standard | Planned |

## Installation

Once published, add the package to your `lakefile.toml`:

```toml
[[require]]
name = "Urllib"
scope = "connect0459"
```

## Development

See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

[Apache-2.0](LICENSE)
