# FormalizedSparse

![CI](https://github.com/YijunYuan/FormalizedSparse/actions/workflows/lean_action_ci.yml/badge.svg)
[![Lean](https://img.shields.io/badge/Lean-4.33.0-5C2D91)](https://leanprover.github.io)
[![mathlib](https://img.shields.io/badge/mathlib-db584cd6d46c92f209a44c0f1c829460d327499d-5C2D91)](https://github.com/leanprover-community/mathlib4)

[![Graph](https://img.shields.io/badge/Dependency_graph-100000?style=for-the-badge&logo=GitHub&logoColor=white&labelColor=black&color=black)](https://yijunyuan.github.io/lean-graph/?url=https://raw.githubusercontent.com/YijunYuan/FormalizedSparse/refs/heads/4.33.0/FormalizedSparse.json#dark)

A full formalization in Lean 4 of the paper **"p-adic Hahn Series with Sparse Support"** by Shanwen Wang and Yijun Yuan.

## Overview

The paper introduces a combinatorial "sparseness" condition on the support of a p-adic Hahn series and proves that any p-adic Hahn series satisfying this condition is transcendental over ℚᶜᵘⁿ_[p], the completed maximal unramified extension of ℚ_[p] (and hence over ℚ_[p]). As an application, it proves the **order-type conjecture** for ℚ_[p]-algebraic p-adic Hahn series with bounded support: under the assumption that the support has only finitely many accumulation points, such a series has finite support, so the order type of its support is either finite or at least ω².

The formalization covers every definition, lemma, proposition, theorem, and corollary from the paper, following the same section structure.

## Project Structure

The foundational material (§2) and Kedlaya's external results (§6) live in the
[TrustworthyKedlaya](https://github.com/YijunYuan/TrustworthyKedlaya) project, on which this
project depends. TrustworthyKedlaya fully formalizes Kedlaya's theorems, so nothing in the
development is admitted.

| File | Paper § | Description |
|------|---------|-------------|
| `TrustworthyKedlaya/Miscellaneous.lean` (dependency) | — | Helper: `WithZeroRat.toNNReal` for the p-adic absolute value |
| `TrustworthyKedlaya/WittVector.lean` (dependency) | §2 | ℚᶜᵘⁿ_[p] via Witt vectors, Teichmüller lift, valuation topology |
| `TrustworthyKedlaya/PAdicHahnSeries.lean` (dependency) | §2 | 𝕃_[p] as W(𝔽ᵃ_[p])((t^ℚ)) / null series, coefficients, support well-orderedness |
| `FormalizedSparse/Sparse.lean` | §3 | Digit series, (c,n)-sparseness, sparseness of disjoint-digit sets |
| `FormalizedSparse/Tscaled.lean` | §4 | T-scaled realization of 𝕃_[p]: adjoining p^(1/T), T-null-series, isomorphism 𝕃_[p] ≅ W(𝔽ᵃ_[p])[p^(1/T)]((t^ℚ))/N_T |
| `FormalizedSparse/MainTheorem.lean` | §5 | Main theorem: sparse support ⇒ transcendental over ℚᶜᵘⁿ_[p] |
| `TrustworthyKedlaya/Kedlaya.lean` (dependency) | §6 | External results of Kedlaya, fully proved in TrustworthyKedlaya |
| `FormalizedSparse/QuasiTwistRecurrent.lean` | §6.1 | Quasi-twist-recurrent (QTR) functions and Kedlaya's integrality criterion |
| `FormalizedSparse/RayDecomposition.lean` | §6.2 | Ray decomposition of bounded QTR sets |
| `FormalizedSparse/BoundedSupport.lean` | §6.3 | Sparse representatives and finiteness of bounded QTR supports (the application) |
| `FormalizedSparse/HuangStefanescu.lean` | §1.3 | Huang–Stefanescu equivalence and divergence of sparse ℚᶜᵘⁿ_[p]-algebraic support sequences (headline consequences of the §6.3 engine) |

## Key Definitions and Theorems

### Sparseness (§3)

- `Sparse.DigitSeries` — the direct sum ⨁_{ℕ₊} ℕ, modeling base-p digit expansions
- `Sparse.IsCNSparse S c n` — (c,n)-sparseness (Definition 3.5)
- `Sparse.IsSparse p W` — sparseness for subsets of [0,1) ∩ ℚ (Definition 1.4)
- `Sparse.IsSparse_of_digit_disjoint` — Example 3.7: disjoint-digit sets are sparse

### T-scaled Realization (§4)

- `TScaled.OQpCUnT` (`ℤᶜᵘⁿ_[p,T]`) — W(𝔽ᵃ_[p])[p^(1/T)] via `AdjoinRoot`
- `TScaled.TNullSeriesIdeal` — the T-null-series ideal N_T
- `TScaled.σ` — the isomorphism σ : 𝕃_[p] ≃+* 𝕃_[p,T]

### Main Theorem (§5)

- `main_theorem` — Theorem 1.7 / 5.3: if −T·Supp(f) admits a nonzero sparse set of representatives mod ℤ, then f is transcendental over ℚᶜᵘⁿ_[p]
- `main_theorem'` — the same conclusion phrased over ℚ_[p]

### Application: bounded support (§6)

- `IsQTR` — quasi-twist-recurrent functions (Definition 6.2)
- `isAlgebraic_iff_isQTR` — Proposition 6.3: algebraicity over 𝔽̄_p((t)) ⇔ QTR
- `isQTR_of_isAlgebraic_of_bddSupport` — Proposition 6.6: bounded ℚᶜᵘⁿ_[p]-algebraic ⇒ QTR
- `qtr_ray_decomposition` — Corollary 6.20: a bounded QTR set with finitely many accumulation points is a finite set plus finitely many pairwise-disjoint rays
- `finite_support_of_qpun_algebraic_of_bounded_support` — Theorem 6.23: a ℚ_[p]-algebraic p-adic Hahn series with bounded support and finitely many accumulation points has finite support
- `order_type_of_qp_algebraic_of_bounded_support` — Corollary 6.24: the order type of such a support is either finite or at least ω²

### Huang–Stefanescu equivalence (§1.3)

- `tendsto_atTop_of_strictMono_support_of_qpun_algebraic` — Corollary 1.12: if a ℚᶜᵘⁿ_[p]-algebraic p-adic Hahn series has support enumerated by a strictly monotone rational sequence, that sequence diverges to +∞
- `padic_huang_stefanescu_tfae` — Proposition 1.14: the p-adic analogue of the Huang–Stefanescu equivalence — for a series supported in {−p^(−i) : i ∈ ℕ₊}, finite support, ℚᶜᵘⁿ_[p]-algebraicity, and ℚ_[p]-algebraicity are all equivalent (the algebraic ⇒ finite direction is deduced from Corollary 1.12)

## Namespace convention

Declarations that correspond to a stated item of the paper live at the top level of the
`FormalizedSparse` namespace; formalization-internal helper lemmas are placed in a sub-namespace
named after the file's section (`QuasiTwistRecurrent`, `RayDecomposition`, `BoundedSupport`). The
§3–§4 files (`Sparse`, `Tscaled`) instead keep all of their content inside a single concept
namespace (`Sparse`, `TScaled`), which enables mathlib-style dot notation such as `d.norm` and
`d.Psi`; the §2 material (`WittVector`, `PAdicHahnSeries`) follows the same convention inside the
`TrustworthyKedlaya` namespace of the dependency.

## Formalization Statistics

- ~19,000 lines of Lean code (plus ~26000 lines of Lean code in the TrustworthyKedlaya dependency)
- All results of the paper are **fully formalized**. Kedlaya's external results, formerly admitted
  as black boxes, are now fully proved in the
  [TrustworthyKedlaya](https://github.com/YijunYuan/TrustworthyKedlaya) dependency, so the whole
  development is free of `admit`/`sorry`.
- Builds against Lean 4.33.0 and mathlib (commit db584cd6d46c92f209a44c0f1c829460d327499d)
