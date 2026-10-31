# ARCHIVED: Retired Research

> **Status:** Retired October 2026. No longer maintained.
>
> This repository preserves an earlier Lean 4 formalization developed
> during the Structural Explainability research program.
> It informed the current research, which no longer builds on it.
>
> Its definitions, assumptions, and results
> **no longer authoritative** and do not reflect current Structural
> Explainability theory.
>
> It is preserved unchanged for historical reference and
> research provenance.
>
> Current formalizations are maintained in
> [Structural Explainability](https://github.com/structural-explainability)
> in the **`se-theory-` repositories**.

---

## Structural Explainability: Contextual Evidence & Explanations (CEE)

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/license/MIT)
![Build Status](https://github.com/structural-explainability/CEE/actions/workflows/ci-lean.yml/badge.svg?branch=main)
[![Check Links](https://github.com/structural-explainability/CEE/actions/workflows/links.yml/badge.svg)](https://github.com/structural-explainability/CEE/actions/workflows/links.yml)

> Lean 4 formalization of the contextual structural explainability layer.

## What This Formalizes

This repository provides a Lean 4 formalization
of the Contextual Evidence & Explanations (CEE) layer.

## Build and Run

```shell
lake update
lake build
lake exe verify

npx markdownlint-cli2 --fix
```

## Annotations

[ANNOTATIONS.md](./ANNOTATIONS.md)

## Citation

[CITATION.cff](./CITATION.cff)

## License

[MIT](./LICENSE)
