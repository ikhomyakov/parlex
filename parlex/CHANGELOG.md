# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog],
and this project adheres to [Semantic Versioning].

[Keep a Changelog]: https://keepachangelog.com/en/1.0.0/
[Semantic Versioning]: https://semver.org/spec/v2.0.0.html


## [0.4.0] — 2026-04-21

### ⚠️  Breaking Changes

- Upgraded to **[`try-next`] 0.5.0**.

### ✨ New Features

- **Span tracking**: Introduced `LexerCursor` with `Span`, `Position`, and `LineHistory` for precise source location tracking. Both `Token` and `ParlexError` now carry `Option<Span>`.
- **Ring-buffer line history**: `LineHistory` is now a fixed-capacity ring buffer, allowing bounded retreat without unbounded memory growth.
- Added `Lexer::span_ref()` for borrowing the current span.
- Added `max_consecutive_unreads` to `LexerStats`.

### 🔧 Improvements

- Relaxed input error bound from `std::error::Error` to `Display`.
- Reworked error handling with `ParlexError` carrying optional span context.
- Removed unused dependencies (`regex-syntax`); moved `env_logger` to dev-dependencies.
- Documented encoding-agnostic design in README.

### 📜 License

- Switched license from LGPL-3.0-or-later to **MIT**.


## [0.3.x] — 2025-10-15

### ⚠️  Breaking Changes

This release introduces a **new type parameter `C` (context)** to the core [`Lexer`] and [`Parser`] structs.  
The change was driven by the upgrade to **[`try-next`] version 0.4.0**, which refined the `TryNextWithContext` trait to make the context type (`C`) explicit and generic:

- **`Lexer<I, D>` → `Lexer<I, D, C>`**
- **`Parser<I, D>` → `Parser<I, D, C>`**

[`try-next`]: https://crates.io/crates/try-next


## [0.2.x] — 2025-10-12

### ⚠️  Breaking Changes

We completely reworked the **Parlex API** in this release — thank you for your patience as we refined the design for clarity, composability, and stronger type safety.

This version refactors the public API, documentation, and trait design to make lexer and parser integration **more consistent, extensible, and ergonomic**.

The two core design ideas introduced in this release are:
1. **Composable `TryNextWithContext<C>` sources** — Parlex now uses the `try-next` crate to generalize input byte sources, lexers and parsers.
2. **Driver-based architecture** — users now implement *lexer* and *parser drivers*, which encapsulate all user-defined logic.
   These drivers integrate seamlessly with the generic DFA and SLR automata provided by the Parlex core library.

During parsing, the core components invoke driver callbacks to perform custom lexer and parser logic — enabling a clean separation between generated automata and user-defined semantics.


## [0.1.x] — 2025-09-17
Initial experimental release of Parlex with early parser and lexer integration.

