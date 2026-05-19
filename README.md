# FormalizedSparse

![CI](https://github.com/YijunYuan/FormalizedSparse/actions/workflows/lean_action_ci.yml/badge.svg)
[![Lean](https://img.shields.io/badge/Lean-4.28.0-5C2D91)](https://leanprover.github.io)
[![mathlib](https://img.shields.io/badge/mathlib-v4.28.0-5C2D91)](https://github.com/leanprover-community/mathlib4)

[![Graph](https://img.shields.io/badge/Dependency_graph-100000?style=for-the-badge&logo=GitHub&logoColor=white&labelColor=black&color=black)](https://yijunyuan.github.io/lean-graph/?url=https://github.com/YijunYuan/FormalizedSparse/raw/refs/heads/master/FormalizedSparse.json#dark)

A full formalization in Lean 4 of the paper **"$p$-adic Hahn Series with Sparse Support"** by Shanwen Wang and Yijun Yuan.

## Overview

The paper introduces a combinatorial "sparseness" condition on the support of a $p$-adic Hahn series and proves that any $p$-adic Hahn series satisfying this condition is transcendental over the completed maximal unramified extension of $\mathbb{Q}_p$ (and hence over $\mathbb{Q}_p$). As an application, it proves a $p$-adic analogue of a classical result of Huang and Ştefănescu on the algebraicity of equal-characteristic Hahn series.

The formalization covers all definitions, lemmas, and theorems from the paper, including the main theorem (Theorem 1.7/5.1) and its applications (Proposition 5.3, Corollary 5.4).

## Project Structure

| File | Paper § | Description |
|------|---------|-------------|
| `FormalizedSparse/References/WittVector.lean` | §2 | $\mathbb{Q}_p^{\operatorname{un}}$ via Witt vectors, Teichmüller lift, valuation topology |
| `FormalizedSparse/References/PAdicHahnSeries.lean` | §2 | $\mathbb{L}_p$ as $W(\overline{\mathbb{F}}_p)((p^{\mathbb{Q}}))$, null series, support well-orderedness |
| `FormalizedSparse/Sparse.lean` | §3 | Digit series, (c,n)-sparseness, sparseness of disjoint-digit sets |
| `FormalizedSparse/Tscaled.lean` | §4 | $T$-scaled realization of $\mathbb{L}_p$: adjoining $p^{1/T}$, $T$-null-series, isomorphism $\mathbb{L}_p \cong W(\mathbb{F}_p^-)[p^{1/T}]((t^{\mathbb{Q}}))/N_T$ |
| `FormalizedSparse/MainTheorem.lean` | §5.1 | Main theorem: sparse support ⇒ transcendental over $\mathbb{Q}_p^{\operatorname{un}}$ |
| `FormalizedSparse/Application.lean` | §5.2 | Proposition 5.3 (disjoint-digit transcendence) and Corollary 5.4 ($p$-adic Huang–Ştefănescu) |
| `FormalizedSparse/References/Miscellaneous.lean` | — | Helper: `WithZeroRat.toNNReal` for $p$-adic absolute value |

## Key Definitions and Theorems

### Sparseness (§3)

- `DigitSeries` — the direct sum ⨁_{ℕ₊} ℕ, modeling base-$p$ digit expansions
- `IsCSparse S c n` — (c,n)-sparseness (Definition 3.5)
- `IsSparse p W` — sparseness for subsets of $[0,1) ∩ \mathbb{Q}$ (Definition 1.4)
- `IsSparse_of_digit_disjoint` — Example 3.7: disjoint-digit sets are sparse

### T-scaled Realization (§4)

- `ℤᵘⁿ_[p,T]` — $W(\overline{\mathbb{F}}_p)[p^{1/T}]$ via AdjoinRoot
- `TScaledNullSeries` — $T$-null-series ideal $N_T$
- `sigma_iso` — isomorphism σ : $\mathbb{L}_p \to W(\mathbb{F}_p^-)[p^{1/T}]((t^{\mathbb{Q}}))/N_T$

### Main Theorem (§5)

- `main_theorem` — Theorem 5.1: if −T·Supp(f) admits a non-zero sparse set of representatives mod ℤ, then f is transcendental over $\mathbb{Q}_p^{\operatorname{un}}$
- `trans_of_digit_disjoint` — Proposition 5.3: transcendence for series with non-overlapping base-$p$ digits
- `pAdicHuangStefanescu` — Corollary 5.4: $p$-adic analogue of Huang–Ştefănescu; for $f = \sum_{i=1}^\infty [f(i)]·p^{−1/p^i}$, algebraicity over $\mathbb{Q}_p$ is equivalent to finite support.

## Formalization Statistics

- ~19,700 lines of Lean code
- All results from the paper are **fully formalized** with no `sorry` gaps
- Builds against mathlib v4.28.0
