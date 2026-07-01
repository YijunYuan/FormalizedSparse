/-
Copyright (c) 2025 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Yijun Yuan
-/
module

public import FormalizedSparse.BoundedSupport

/-!
# Huang–Stefanescu: algebraicity of `p`-adic Hahn series with sparse support

This file records two consequences of the bounded-support finiteness engine
`finite_support_of_qpun_algebraic_of_bounded_support` (Theorem 6.23 of `BoundedSupport.lean`).

The first, `test`, says that an `ℚᵘⁿ_[p]`-algebraic series whose support is the range of a strictly
monotone rational sequence `s` forces `s` to diverge to `+∞`: such a support cannot be bounded
above. The proof is by contradiction — a bounded strictly monotone sequence accumulates only at its
supremum, so the support has finitely many accumulation points, and the engine would then make it
finite, contradicting the injectivity of `s`.

The second, `pAdicHuangStefanescu`, is the Huang–Stefanescu equivalence for a series supported in
the sparse set `{-p^{-i} | i : ℕ+}`: finite support, algebraicity over `ℚᵘⁿ_[p]`, and algebraicity
over `ℚ_[p]` are all equivalent. The nontrivial implication (algebraic over `ℚᵘⁿ_[p]` ⟹ finite
support) runs the same engine: the support lies in `[-1, 0]`, hence is bounded, and its image under
`ℚ ↪ ℝ` is covered by the range of `n ↦ -p^{-n}`, which converges to `0`, so its ℝ-derived set is
finite.

## Main statements

- `FormalizedSparse.test`: a strictly monotone rational support sequence of an `ℚᵘⁿ_[p]`-algebraic
  series diverges to `+∞`.
- `FormalizedSparse.pAdicHuangStefanescu`: the Huang–Stefanescu equivalence for series supported in
  `{-p^{-i} | i : ℕ+}`.

## Tags

p-adic, Hahn series, sparse support, algebraic, accumulation point
-/

@[expose] public section

namespace FormalizedSparse

open Filter Topology in
/-- If a real sequence `u` converges to `L`, then `L` is its only accumulation point: the derived
set of `Set.range u` is contained in `{L}`. Indeed, if `x ≠ L`, choose disjoint neighbourhoods
`U ∋ x`, `V ∋ L`; convergence puts all but finitely many `u n` in `V`, so `U ∩ Set.range u` is
finite and `x` cannot be an accumulation point of `Set.range u`. -/
private theorem derivedSet_range_subset_of_tendsto {u : ℕ → ℝ} {L : ℝ}
    (h : Tendsto u atTop (𝓝 L)) : derivedSet (Set.range u) ⊆ {L} := by
  intro x hx
  rw [mem_derivedSet] at hx
  simp only [Set.mem_singleton_iff]
  by_contra hxL
  obtain ⟨U, V, hUopen, hVopen, hxU, hLV, hUV⟩ := t2_separation hxL
  have hUnhds : U ∈ 𝓝 x := hUopen.mem_nhds hxU
  -- Localise the accumulation to `U ∩ Set.range u`, which must then be infinite.
  have hinf : (U ∩ Set.range u).Infinite := Set.Infinite.of_accPt (hx.nhds_inter hUnhds)
  apply hinf
  -- But convergence to `L ∈ V` forces all but finitely many `u n` into `V`, hence out of `U`.
  have hev : ∀ᶠ n in atTop, u n ∈ V := h (hVopen.mem_nhds hLV)
  rw [← Nat.cofinite_eq_atTop] at hev
  have hcofin : {n : ℕ | u n ∉ V}.Finite := hev
  apply (hcofin.image u).subset
  rintro y ⟨hyU, n, rfl⟩
  exact ⟨n, fun hnV => (hUV.ne_of_mem hyU hnV) rfl, rfl⟩

/-- A subset of `ℚ` that is bounded below and above is bounded for the metric bornology. -/
private theorem isBounded_of_bddBelow_bddAbove {s : Set ℚ} (hb : BddBelow s) (ha : BddAbove s) :
    Bornology.IsBounded s := by
  rw [Metric.isBounded_iff]
  obtain ⟨a, ha'⟩ := hb
  obtain ⟨b, hb'⟩ := ha
  refine ⟨(b : ℝ) - a, fun x hx y hy => ?_⟩
  rw [Rat.dist_eq, abs_le]
  have hxa : (a : ℝ) ≤ x := by exact_mod_cast ha' hx
  have hxb : (x : ℝ) ≤ b := by exact_mod_cast hb' hx
  have hya : (a : ℝ) ≤ y := by exact_mod_cast ha' hy
  have hyb : (y : ℝ) ≤ b := by exact_mod_cast hb' hy
  constructor <;> linarith

open Filter Topology in
/-- If `f : 𝕃_[p]` is algebraic over `ℚᵘⁿ_[p]` and its support is the range of a strictly monotone
rational sequence `s`, then `s` diverges to `+∞`. Equivalently, the support of such an `f` is
unbounded above: were it bounded, the sequence would accumulate at its supremum, and
`finite_support_of_qpun_algebraic_of_bounded_support` would force the support finite, contradicting
the injectivity of `s`. -/
theorem test {p : ℕ} [Fact (Nat.Prime p)] (s : ℕ → ℚ) (hs : StrictMono s) (f : 𝕃_[p])
    (hf1 : IsAlgebraic ℚᵘⁿ_[p] f) (hf2 : f.support = Set.range s) :
    Tendsto s atTop atTop := by
  -- It suffices to show `Set.range s` is unbounded above.
  apply tendsto_atTop_atTop_of_monotone hs.monotone
  by_contra hbdd
  simp only [not_forall, not_exists, not_le] at hbdd
  -- `hbdd : ∃ b, ∀ n, s n < b`, so `Set.range s` is bounded above.
  obtain ⟨b, hb⟩ := hbdd
  have hba : BddAbove (Set.range s) := ⟨b, by rintro _ ⟨n, rfl⟩; exact (hb n).le⟩
  -- `Set.range s` is bounded below by `s 0` (monotonicity).
  have hbb : BddBelow (Set.range s) :=
    ⟨s 0, by rintro _ ⟨n, rfl⟩; exact hs.monotone (Nat.zero_le n)⟩
  -- Hence `f.support = Set.range s` is bounded for the metric bornology.
  have hbounded : Bornology.IsBounded f.support :=
    hf2 ▸ isBounded_of_bddBelow_bddAbove hbb hba
  -- The cast sequence `n ↦ (s n : ℝ)` is monotone and bounded above, so it converges to its sup.
  have hmono_r : Monotone (fun n => (s n : ℝ)) :=
    fun a c hac => by simp only; exact_mod_cast hs.monotone hac
  have hba_r : BddAbove (Set.range (fun n => (s n : ℝ))) :=
    ⟨(b : ℝ), by rintro _ ⟨n, rfl⟩; simp only; exact_mod_cast (hb n).le⟩
  have htend : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 (⨆ n, (s n : ℝ))) :=
    tendsto_atTop_ciSup hmono_r hba_r
  -- So the ℝ-derived set of the image support is contained in the singleton `{sup}`, hence finite.
  have himg : (Rat.cast : ℚ → ℝ) '' f.support = Set.range (fun n => (s n : ℝ)) := by
    rw [hf2, ← Set.range_comp]; rfl
  have hderiv_fin : (derivedSet ((Rat.cast : ℚ → ℝ) '' f.support)).Finite := by
    rw [himg]
    exact Set.Finite.subset (Set.finite_singleton _) (derivedSet_range_subset_of_tendsto htend)
  -- The engine now forces `f.support` to be finite.
  have hfin : f.support.Finite :=
    finite_support_of_qpun_algebraic_of_bounded_support f hf1 hbounded hderiv_fin
  -- But `f.support = Set.range s` is infinite since `s` is injective.
  exact (hf2 ▸ Set.infinite_range_of_injective hs.injective) hfin

open Filter Topology pAdicHahnSeries in
/-- **Huang–Stefanescu.** For a `p`-adic Hahn series `f` whose support is contained in the sparse
set `{-p^{-i} | i : ℕ+}`, the following are equivalent: `f` has finite support, `f` is algebraic
over `ℚᵘⁿ_[p]`, and `f` is algebraic over `ℚ_[p]`. -/
theorem pAdicHuangStefanescu (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p])
    (hf : f.support ⊆ {-(p : ℚ) ^ (-(i : ℤ)) | i : ℕ+}) :
    List.TFAE [f.support.Finite, IsAlgebraic ℚᵘⁿ_[p] f, IsAlgebraic ℚ_[p] f] := by
  tfae_have 3 → 2 := fun a ↦ alg_QpUn_of_alg_Qp p f a
  tfae_have 1 → 3 := fun a ↦ alg_of_fin_supp p f a
  tfae_have 2 → 1 := by
    intro halg
    -- The support sits in `[-1, 0]`, so it is bounded for the metric bornology.
    have hbdd : ∀ q ∈ f.support, -1 ≤ q ∧ q ≤ 0 := by
      intro q hq
      obtain ⟨i, hi⟩ := hf hq
      have hp1 : (1 : ℚ) ≤ (p : ℚ) := by
        exact_mod_cast Nat.one_le_of_lt (Fact.out (p := Nat.Prime p)).two_le
      have hpow_pos : (0 : ℚ) < (p : ℚ) ^ (-(i : ℤ)) := by positivity
      have hpow_le : (p : ℚ) ^ (-(i : ℤ)) ≤ 1 := by
        rw [zpow_neg, inv_le_one_iff₀]
        exact Or.inr (one_le_zpow₀ hp1 (by positivity))
      exact ⟨by rw [← hi]; linarith, by rw [← hi]; linarith⟩
    have hbounded : Bornology.IsBounded f.support :=
      isBounded_of_bddBelow_bddAbove
        ⟨-1, fun q hq => (hbdd q hq).1⟩ ⟨0, fun q hq => (hbdd q hq).2⟩
    -- The cast support is covered by the range of `n ↦ -(p : ℝ) ^ (-n)`, which tends to `0`.
    have htend : Tendsto (fun n : ℕ => -(p : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
      have key : Tendsto (fun n : ℕ => (p : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
        have hrw : (fun n : ℕ => (p : ℝ) ^ (-(n : ℤ))) = (fun n : ℕ => ((p : ℝ)⁻¹) ^ n) := by
          funext n; rw [zpow_neg, zpow_natCast, inv_pow]
        rw [hrw]
        refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
        rw [inv_lt_one_iff₀]
        exact Or.inr (by exact_mod_cast (Fact.out (p := Nat.Prime p)).one_lt)
      simpa using key.neg
    have hsub : (Rat.cast : ℚ → ℝ) '' f.support ⊆
        Set.range (fun n : ℕ => -(p : ℝ) ^ (-(n : ℤ))) := by
      rintro y ⟨q, hq, rfl⟩
      obtain ⟨i, hi⟩ := hf hq
      exact ⟨(i : ℕ), by rw [← hi]; push_cast; ring⟩
    -- Its ℝ-derived set is then contained in `{0}`, hence finite; feed the engine.
    have hderiv_fin : (derivedSet ((Rat.cast : ℚ → ℝ) '' f.support)).Finite := by
      apply Set.Finite.subset (Set.finite_singleton (0 : ℝ))
      exact (derivedSet_mono _ _ hsub).trans (derivedSet_range_subset_of_tendsto htend)
    exact finite_support_of_qpun_algebraic_of_bounded_support f halg hbounded hderiv_fin
  tfae_finish

end FormalizedSparse
