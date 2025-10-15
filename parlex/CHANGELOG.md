# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog],
and this project adheres to [Semantic Versioning].

[Keep a Changelog]: https://keepachangelog.com/en/1.0.0/
[Semantic Versioning]: https://semver.org/spec/v2.0.0.html


## [0.2.x] — 2025-10-12

### ⚠️  Breaking Changes

We completely reworked the **Parlex API** in this release — thank you for your patience as we refined the design for clarity, composability, and stronger type safety.

This version refactors the public API, documentation, and trait design to make lexer and parser integration **more consistent, extensible, and ergonomic**.

The two core design ideas introduced in this release are:
1. **Composable `TryNextWithContext` sources** — Parlex now uses the `try-next` crate to generalize input byte sources, lexers and parsers.
2. **Driver-based architecture** — users now implement *lexer* and *parser drivers*, which encapsulate all user-defined logic.
   These drivers integrate seamlessly with the generic DFA and SLR automata provided by the Parlex core library.

During parsing, the core components invoke driver callbacks to perform custom lexer and parser logic — enabling a clean separation between generated automata and user-defined semantics.


## [0.1.x] — 2025-09-17
Initial experimental release of Parlex with early parser and lexer integration.

