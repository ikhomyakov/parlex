# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog],
and this project adheres to [Semantic Versioning].

[Keep a Changelog]: https://keepachangelog.com/en/1.0.0/
[Semantic Versioning]: https://semver.org/spec/v2.0.0.html

## [0.4.0] — 2026-04-21

### 🧩 Changes

- Updated to depend on **[parlex](https://crates.io/crates/parlex)** `0.4.0` and **[`try-next`]** `0.5.0`.
- Removed unused dependencies (`log`); cleaned up unused imports.
- Added missing `LICENSE.md`.

### 📜 License

- Switched license from LGPL-3.0-or-later to **MIT**.

[`try-next`]: https://crates.io/crates/try-next


## [0.3.x] — 2025-10-15

### ✨ Completed Example

The **`parlex-calc`** example has been fully completed, refactored, and documented.  
It now demonstrates a full lexer–parser pipeline using the updated Parlex 0.3.0 API.

### ⚙️  Breaking Changes

- Updated to **`try-next` 0.4.0**, introducing explicit context type parameters in lexer and parser definitions.

