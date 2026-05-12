import FormalizedSparse.References.WittVector
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.WittVector.TeichmullerSeries
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

open WittVector

namespace Poonen1993
-- W(𝔽ₚ^⁻)((t^ℚ))
abbrev LiftedPAdicHahnSeries (p : ℕ) [Fact (Nat.Prime p)] := HahnSeries ℚ (ℤᵘⁿ_[p])
namespace LiftedPAdicHahnSeries
-- Define an element of W(𝔽ₚ^⁻)((t^ℚ)) from a function ℚ → 𝔽ₚ^⁻ with well-ordered support
-- by the formula f ↦ ∑ₖ [f(k)]tᵏ
noncomputable def from_coeff {p : ℕ} [Fact (Nat.Prime p)]
(s : ℚ → Fpbar p) (hspwo : (Function.support s).IsPWO) :
LiftedPAdicHahnSeries p where
  coeff := fun n => teichmuller p (s n)
  isPWO_support' := by
    suffices h : (Function.support fun n ↦ (teichmuller p) (s n)) = Function.support s by rwa [h]
    ext z
    simp only [Function.mem_support]
    refine Function.Injective.ne_iff' ?_ ?_
    · exact injective_teichmuller p
    · simp
end LiftedPAdicHahnSeries

def finprop {p : ℕ} [Fact (Nat.Prime p)] (x : LiftedPAdicHahnSeries p) (g : ℚ) (N : ℕ) :
  Finite {n : ℤ | g + n ≤ N ∧ x.coeff (g + n) ≠ 0} := by
  by_cases hs : Set.Nonempty x.support
  · let m : ℚ := x.isWF_support.min hs
    have hsubset :
        {n : ℤ | g + n ≤ N ∧ x.coeff (g + n) ≠ 0} ⊆
          Set.Icc (⌈m - g⌉ : ℤ) ⌊(N : ℚ) - g⌋ := by
      intro n hn
      have hm_le : m ≤ g + n := x.isWF_support.min_le hs <| (HahnSeries.mem_support x (g + n)).2 hn.2
      have hlower : (⌈m - g⌉ : ℤ) ≤ n := by
        apply Int.ceil_le.mpr
        rw [sub_le_iff_le_add]
        simpa [add_comm, add_left_comm, add_assoc] using hm_le
      have hupper : n ≤ ⌊(N : ℚ) - g⌋ := by
        apply Int.le_floor.mpr
        rw [le_sub_iff_add_le]
        simpa [add_comm, add_left_comm, add_assoc] using hn.1
      exact ⟨hlower, hupper⟩
    exact ((Set.finite_Icc (⌈m - g⌉ : ℤ) ⌊(N : ℚ) - g⌋).subset hsubset).to_subtype
  · have hcoeff : ∀ q : ℚ, x.coeff q = 0 := by
      intro q
      by_contra hq
      exact hs ⟨q, (HahnSeries.mem_support x q).2 hq⟩
    have hset : {n : ℤ | g + n ≤ N ∧ x.coeff (g + n) ≠ 0} = ∅ := by
      ext n
      simp [hcoeff (g + n)]
    simpa [hset] using (Set.finite_empty : (∅ : Set ℤ).Finite).to_subtype

-- An element ∑ₖ aₖ tᵏof W(𝔽ₚ^⁻)((t^ℚ)) called a `null series` if ∀ g ∈ ℚ, ∑ₙ a_{g+n}pⁿ = 0
open Topology Filter in
def IsNullSeries {p : ℕ} [Fact (Nat.Prime p)] (x : LiftedPAdicHahnSeries p) : Prop :=
  ∀ g : ℚ, Filter.Tendsto (fun M => (∑ n : Set.Finite.toFinset (finprop x g M),
      (p : QpUn p) ^ n.val * algebraMap (OQpUn p) (QpUn p) (x.coeff (g + n)))) atTop (𝓝 0)

noncomputable def finpropInt {p : ℕ} [Fact (Nat.Prime p)]
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (K : ℤ) :
    Finite {n : ℤ | n ≤ K ∧ x.coeff (g + n) ≠ 0} := by
  by_cases hs : Set.Nonempty x.support
  · let m : ℚ := x.isWF_support.min hs
    have hsubset : {n : ℤ | n ≤ K ∧ x.coeff (g + n) ≠ 0} ⊆ Set.Icc (⌈m - g⌉ : ℤ) K := by
      intro n hn
      have hm_le : m ≤ g + n := x.isWF_support.min_le hs <| (HahnSeries.mem_support x (g + n)).2 hn.2
      have hlower : (⌈m - g⌉ : ℤ) ≤ n := by
        apply Int.ceil_le.mpr
        rw [sub_le_iff_le_add]
        simpa [add_comm, add_left_comm, add_assoc] using hm_le
      exact ⟨hlower, hn.1⟩
    exact ((Set.finite_Icc (⌈m - g⌉ : ℤ) K).subset hsubset).to_subtype
  · have hcoeff : ∀ q : ℚ, x.coeff q = 0 := by
      intro q
      by_contra hq
      exact hs ⟨q, (HahnSeries.mem_support x q).2 hq⟩
    have hset : {n : ℤ | n ≤ K ∧ x.coeff (g + n) ≠ 0} = ∅ := by
      ext n
      simp [hcoeff (g + n)]
    simpa [hset] using (Set.finite_empty : (∅ : Set ℤ).Finite).to_subtype

noncomputable def intPartial {p : ℕ} [Fact (Nat.Prime p)]
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (K : ℤ) : QpUn p :=
  ∑ n : Set.Finite.toFinset (finpropInt x g K),
    (p : QpUn p) ^ n.1 * algebraMap (OQpUn p) (QpUn p) (x.coeff (g + n))

-- The valuation of `p : QpUn p` is `ofAdd(-1)`; a uniformizer fact reused throughout.
private lemma valued_v_p {p : ℕ} [Fact (Nat.Prime p)] :
    Valued.v ((p : QpUn p)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
  rw [show ((p : QpUn p)) = algebraMap (OQpUn p) (QpUn p) (p : OQpUn p) from by
    push_cast; rfl]
  rw [show (Valued.v : QpUn p → _) =
      (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation _ from rfl]
  rw [(IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation_of_algebraMap]
  have hirr : Irreducible (p : OQpUn p) := WittVector.irreducible p
  have hpe : (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).asIdeal =
      Ideal.span {(p : OQpUn p)} := hirr.maximalIdeal_eq
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
    (WittVector.p_nonzero p _) hpe]
  rfl

-- The valuation of `(p : QpUn p)^n` is `ofAdd(-n)` for integer `n`.
private lemma valued_v_p_zpow {p : ℕ} [Fact (Nat.Prime p)] (n : ℤ) :
    Valued.v ((p : QpUn p)^n) =
      ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
  have hzpow : Valued.v ((p : QpUn p)^n) = (Valued.v ((p : QpUn p)))^n :=
    map_zpow₀ Valued.v _ _
  rw [hzpow, valued_v_p, ← WithZero.coe_zpow]
  congr 1
  rw [← ofAdd_zsmul n (-1 : ℤ)]
  congr 1
  ring

-- Per-term bound: for `a : OQpUn p` and `n : ℤ`, `Valued.v (p^n · algMap a) ≤ ofAdd(-n)`.
private lemma valued_v_term_le {p : ℕ} [Fact (Nat.Prime p)] (a : OQpUn p) (n : ℤ) :
    Valued.v ((p : QpUn p)^n * algebraMap (OQpUn p) (QpUn p) a) ≤
      ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
  rw [Valuation.map_mul, valued_v_p_zpow]
  have h_alg : Valued.v (algebraMap (OQpUn p) (QpUn p) a) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation_le_one a
  calc ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) *
          Valued.v (algebraMap (OQpUn p) (QpUn p) a)
      ≤ ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) * 1 :=
        mul_le_mul' (le_refl _) h_alg
    _ = ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := mul_one _

-- For a unit `u : (OQpUn p)ˣ`, `Valued.v (algebraMap ... u.val) = 1`.
private lemma valued_v_algebraMap_unit_one {p : ℕ} [Fact (Nat.Prime p)] (u : (OQpUn p)ˣ) :
    Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) = 1 := by
  have h1 : Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation_le_one u.val
  have h2 : Valued.v (algebraMap (OQpUn p) (QpUn p) u.inv) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation_le_one u.inv
  have h3 : Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) *
            Valued.v (algebraMap (OQpUn p) (QpUn p) u.inv) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, u.val_inv]; simp
  by_contra h_ne_one
  have h1_lt : Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) < 1 :=
    lt_of_le_of_ne h1 h_ne_one
  have h_lt : Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) *
            Valued.v (algebraMap (OQpUn p) (QpUn p) u.inv) < 1 := by
    calc
      Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) *
          Valued.v (algebraMap (OQpUn p) (QpUn p) u.inv) ≤
          Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) * 1 := mul_le_mul' (le_refl _) h2
      _ = Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) := mul_one _
      _ < 1 := h1_lt
  rw [h3] at h_lt
  exact lt_irrefl _ h_lt

-- For `K ≤ K'`, the difference `intPartial K' - intPartial K` equals the sum over the
-- set-difference of the finpropInt index sets.
private lemma intPartial_diff_eq_sdiff_sum {p : ℕ} [Fact (Nat.Prime p)]
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (K K' : ℤ) (h : K ≤ K') :
    intPartial x g K' - intPartial x g K =
      ∑ n ∈ (Set.Finite.toFinset (finpropInt x g K') \
              Set.Finite.toFinset (finpropInt x g K)),
        (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (x.coeff (g + n)) := by
  have hsub : Set.Finite.toFinset (finpropInt x g K) ⊆
      Set.Finite.toFinset (finpropInt x g K') := by
    intro n hn
    have hn_mem : n ∈ {n : ℤ | n ≤ K ∧ x.coeff (g + n) ≠ 0} :=
      (Set.Finite.mem_toFinset _).mp hn
    exact (Set.Finite.mem_toFinset _).mpr ⟨le_trans hn_mem.1 h, hn_mem.2⟩
  have e1 : intPartial x g K' = ∑ n ∈ Set.Finite.toFinset (finpropInt x g K'),
      (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (x.coeff (g + n)) :=
    Finset.sum_attach (s := Set.Finite.toFinset (finpropInt x g K'))
      (f := fun m : ℤ => (p : QpUn p) ^ m * algebraMap (OQpUn p) (QpUn p) (x.coeff (g + m)))
  have e2 : intPartial x g K = ∑ n ∈ Set.Finite.toFinset (finpropInt x g K),
      (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (x.coeff (g + n)) :=
    Finset.sum_attach (s := Set.Finite.toFinset (finpropInt x g K))
      (f := fun m : ℤ => (p : QpUn p) ^ m * algebraMap (OQpUn p) (QpUn p) (x.coeff (g + m)))
  rw [e1, e2, ← Finset.sum_sdiff hsub, add_sub_cancel_right]

-- **Helper 1** (partial_sum_cauchy): For `K₁ ≤ K₂`, the difference
-- `intPartial x g' K₂ - intPartial x g' K₁` has valuation `≤ ofAdd(-(K₁ + 1))`.
-- This is the "tail below K₁ is small" strict-ultrametric bound.
private lemma partial_sum_valuation_cauchy {p : ℕ} [Fact (Nat.Prime p)]
    (x : LiftedPAdicHahnSeries p) (g' : ℚ) (K₁ K₂ : ℤ) (h : K₁ ≤ K₂) :
    Valued.v (intPartial x g' K₂ - intPartial x g' K₁) ≤
      ((Multiplicative.ofAdd (-(K₁ + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
  rw [intPartial_diff_eq_sdiff_sum x g' K₁ K₂ h]
  apply Valuation.map_sum_le
  intro n hn
  have hn_mem : n ∈ Set.Finite.toFinset (finpropInt x g' K₂) ∧
      n ∉ Set.Finite.toFinset (finpropInt x g' K₁) := Finset.mem_sdiff.mp hn
  have hn1 : n ≤ K₂ ∧ x.coeff (g' + n) ≠ 0 :=
    (Set.Finite.mem_toFinset (hs := finpropInt x g' K₂)).mp hn_mem.1
  have hn2 : ¬ (n ≤ K₁ ∧ x.coeff (g' + n) ≠ 0) := by
    intro h'
    exact hn_mem.2 ((Set.Finite.mem_toFinset (hs := finpropInt x g' K₁)).mpr h')
  have hn_gt : K₁ < n := by
    by_contra hle
    push_neg at hle
    exact hn2 ⟨hle, hn1.2⟩
  have h1 := valued_v_term_le (x.coeff (g' + n)) n
  have h2 : ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) ≤
      ((Multiplicative.ofAdd (-(K₁ + 1) : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_le_coe]
    exact Multiplicative.ofAdd_le.mpr (by omega)
  exact h1.trans h2

-- The `IsNullSeries` partial sum at `(g, M)` (over `ℕ`) equals the `intPartial` at
-- `(g, ⌊M - g⌋)` (over `ℤ`). This is the key index-set realignment for translating
-- between the `ℕ`-atTop and `ℤ`-atTop framings.
private lemma partialSum_eq_intPartial {p : ℕ} [Fact (Nat.Prime p)]
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (M : ℕ) :
    (∑ n : Set.Finite.toFinset (finprop x g M),
        (p : QpUn p) ^ n.val * algebraMap (OQpUn p) (QpUn p) (x.coeff (g + n))) =
      intPartial x g ⌊(M : ℚ) - g⌋ := by
  sorry

-- **Helper 3** (null_series_tail_bound): for a null series `x`, the integer-cutoff
-- partial sum `intPartial x g K` has valuation `≤ ofAdd(-(K + 1))`. Proof: from
-- `IsNullSeries x` (via cofinality of `⌊M - g⌋` in `ℤ` as `M : ℕ → ∞`), pick `K' ≥ K`
-- with `Valued.v (intPartial x g K') < ofAdd(-(K + 2))`. Then by Helper 1 + ultrametric,
-- `Valued.v (intPartial x g K) ≤ ofAdd(-(K + 1))`.
private lemma null_series_tail_bound {p : ℕ} [Fact (Nat.Prime p)]
    {x : LiftedPAdicHahnSeries p} (hx : IsNullSeries x) (g : ℚ) (K : ℤ) :
    Valued.v (intPartial x g K) ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
  sorry

-- The integer set `{n : ℤ | n ≤ K, g + n ∈ s}` is finite for a PWO set `s ⊆ ℚ`.
-- Argument: if `s` is empty, trivial. Else `s` has min `q_min`, so `g + n ≥ q_min`,
-- hence `n ≥ ⌈q_min - g⌉`, giving a finite integer interval.
private lemma finite_int_in_pwo_below {s : Set ℚ} (hs : s.IsPWO) (g : ℚ) (K : ℤ) :
    {n : ℤ | n ≤ K ∧ g + (n : ℚ) ∈ s}.Finite := by
  sorry

-- **Bound for `intPartial (c*x) g K`** — the key lemma feeding the main proof.
-- Strategy: expand `(c*x).coeff(g+n)` via `HahnSeries.coeff_mul`, reindex by
-- `(a, n)` instead of `(n, (a, b))` (with `b = g - a + n` implicit), group by `a`,
-- recognize the inner sum as `intPartial x (g - a) K`, apply ultrametric + Helper 3.
private lemma intPartial_mul_valuation_bound {p : ℕ} [Fact (Nat.Prime p)]
    (c x : LiftedPAdicHahnSeries p) (hx : IsNullSeries x) (g : ℚ) (K : ℤ) :
    Valued.v (intPartial (c * x) g K) ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
  sorry

-- [Proposition 3, Poonen1993] : The null series form an ideal of W(𝔽ₚ^⁻)((t^ℚ)).
def NullSeriesIdeal (p : ℕ) [Fact (Nat.Prime p)] : Ideal (LiftedPAdicHahnSeries p) where
  carrier := {x | IsNullSeries x}
  add_mem' := by
    sorry
  zero_mem' := by simp [IsNullSeries]
  smul_mem' := by
    sorry

-- Sub-Obj 2a of `(NullSeriesIdeal p).IsMaximal` decomposition (Session 7).
-- `1 ∉ NullSeriesIdeal p`. Direct route: at `g = 0`, the partial-sum sequence in
-- the definition of `IsNullSeries` is constantly `1` (only `n = 0` survives, and
-- `(1).coeff 0 = 1`), but `IsNullSeries` requires it to tend to `0`; uniqueness
-- of limits in `QpUn p` forces `1 = 0`, contradicting `one_ne_zero`.
-- We avoid `null_series_no_unit_leading` (defined later at L3064) here so the
-- lemma is available at L719 for the future Sub-Obj 2c integration.
private lemma one_notMem_NullSeriesIdeal (p : ℕ) [Fact (Nat.Prime p)] :
    (1 : LiftedPAdicHahnSeries p) ∉ NullSeriesIdeal p := by
  sorry

-- Eagerly establish `Nontrivial` of the quotient from `one_notMem_NullSeriesIdeal`.
-- The full `IsMaximal` (and therefore `Field`) instance is established later, after
-- `canonical_leading_coeff_isUnit` and `exists_inverse_of_nonzero`. Some intermediate
-- proofs (notably `val_one_eq_zero`) need `(1 : Quot) ≠ 0` before that point, which
-- this `Nontrivial` instance supplies without circularity.
instance (p : ℕ) [Fact (Nat.Prime p)] :
    Nontrivial ((LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) :=
  Submodule.Quotient.nontrivial_iff.mpr
    ((Ideal.ne_top_iff_one _).mpr (one_notMem_NullSeriesIdeal p))

/-
  Auxiliary infrastructure for the proof of `exists_canonical_expansion`.

  Following `informal/exists_canonical_expansion.md`, the proof is decomposed
  into helper lemmas. The deepest step (uniqueness of the Teichmuller series)
  is a TODO upstream in Mathlib (`Mathlib.RingTheory.WittVector.TeichmullerSeries`).
  Existence comes from `dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff`
  applied per coset `g ∈ Set.Ico (0:ℚ) 1`.
-/

set_option maxHeartbeats 250000 in
-- maxHeartbeats: heavy elaboration in the multi-phase proof body
/--
**Existence of a Teichmuller-style canonical expansion**.

For every `α : LiftedPAdicHahnSeries p`, there exists `s : ℚ → Fpbar p` with
PWO support such that `α - LiftedPAdicHahnSeries.from_coeff s hspwo` is a null
series (i.e. lies in `NullSeriesIdeal p`).

The construction (per Poonen, p. 6 / `informal/exists_canonical_expansion.md`):
for each coset rep `g ∈ Set.Ico 0 1`, take `f_g := ∑_{n∈ℤ} α_{g+n} p^n ∈ ℚᵘⁿ_[p]`,
shift to land in the integers, and read off coefficients via Mathlib's
`WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff`.

This proof relies on `existsCanonicalExpansionAux.exists_lim_intPartial`,
`existsCanonicalExpansionAux.exists_teichmuller_digits`, and the
support-PWO bound combining `Set.IsPWO.add` with
`existsCanonicalExpansionAux.natRange_isPWO`.
-/
theorem exists_canonical_representative {p : ℕ} [Fact (Nat.Prime p)]
    (α : LiftedPAdicHahnSeries p) :
    ∃ (s : ℚ → Fpbar p) (hspwo : (Function.support s).IsPWO),
      α - LiftedPAdicHahnSeries.from_coeff s hspwo ∈ NullSeriesIdeal p := by
  sorry

set_option maxHeartbeats 220000 in
-- maxHeartbeats: heavy elaboration in the multi-phase proof body
/--
**Uniqueness of the Teichmuller-style canonical expansion**.

If `s, s'` both have PWO support and `from_coeff s ≡ from_coeff s'` modulo
`NullSeriesIdeal p`, then `s = s'`.

The argument (per `informal/exists_canonical_expansion.md`, §"Uniqueness"):
working coset by coset, the limit of partial sums is the same on both sides;
by `existsCanonicalExpansionAux.teichmuller_digits_unique`, the per-coset
coefficients agree, hence so do `s` and `s'`.
-/
theorem unique_canonical_representative {p : ℕ} [Fact (Nat.Prime p)]
    {s s' : ℚ → Fpbar p}
    (hspwo : (Function.support s).IsPWO) (hspwo' : (Function.support s').IsPWO)
    (h : LiftedPAdicHahnSeries.from_coeff s hspwo -
         LiftedPAdicHahnSeries.from_coeff s' hspwo' ∈ NullSeriesIdeal p) :
    s = s' := by
  sorry

-- [Proposition 4, Poonen1993] : Every element of pAdicHahnSeries p has a unique representative
-- in W(𝔽ₚ^⁻)((t^ℚ)) of the form ∑ₖ [aₖ] tᵏ
theorem exists_canonical_expansion {p : ℕ} [Fact (Nat.Prime p)] :
  ∀ A : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p),
    ∃! (s : {f : ℚ → Fpbar p // (Function.support f).IsPWO}),
      Ideal.Quotient.ringCon (NullSeriesIdeal p)
      A.out (LiftedPAdicHahnSeries.from_coeff s.val s.prop) := by
  intro A
  -- Apply the existence helper to `α := A.out`.
  obtain ⟨s, hspwo, hα⟩ := exists_canonical_representative (A.out)
  refine ⟨⟨s, hspwo⟩, ?_, ?_⟩
  · -- Existence: `A.out - from_coeff s ∈ NullSeriesIdeal` ↔ the relation holds.
    -- `Ideal.Quotient.ringCon` is the relation `a ≡ b ↔ a - b ∈ I` (for an
    -- additive group), so we just unfold it.
    -- The relation is what `Quotient.exact` gives us from `mk a = mk b`.
    have hmk :
        (Ideal.Quotient.mk (NullSeriesIdeal p)) (A.out) =
          (Ideal.Quotient.mk (NullSeriesIdeal p))
            (LiftedPAdicHahnSeries.from_coeff s hspwo) :=
      Ideal.Quotient.eq.mpr hα
    exact Quotient.exact hmk
  · -- Uniqueness: any `⟨s', hspwo'⟩` satisfying the relation has `s = s'`.
    rintro ⟨s', hspwo'⟩ h'
    -- `h'` says `A.out - from_coeff s' ∈ NullSeriesIdeal p` (modulo
    -- unfolding the `ringCon` relation).
    have hα' :
        A.out - LiftedPAdicHahnSeries.from_coeff s' hspwo' ∈ NullSeriesIdeal p := by
      have hmk' :
          (Ideal.Quotient.mk (NullSeriesIdeal p)) (A.out) =
            (Ideal.Quotient.mk (NullSeriesIdeal p))
              (LiftedPAdicHahnSeries.from_coeff s' hspwo') :=
        Quotient.sound h'
      exact Ideal.Quotient.eq.mp hmk'
    -- Subtract: `from_coeff s - from_coeff s'` is in the ideal.
    -- We have `(A.out - from_coeff s') - (A.out - from_coeff s) = from_coeff s - from_coeff s'`
    -- via `sub_sub_sub_cancel_left`.
    have hsub :
        LiftedPAdicHahnSeries.from_coeff s hspwo -
          LiftedPAdicHahnSeries.from_coeff s' hspwo' ∈ NullSeriesIdeal p := by
      have h1 := (NullSeriesIdeal p).sub_mem hα' hα
      simpa [sub_sub_sub_cancel_left] using h1
    -- Apply uniqueness helper at the function level, then lift to subtypes.
    have hfun : s = s' := unique_canonical_representative hspwo hspwo' hsub
    subst hfun
    rfl

-- The support of a p-adic Hahn series is well-ordered.
theorem support_IsPWO {p : ℕ} [Fact (Nat.Prime p)]
  (x : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) :
  (exists_canonical_expansion x).choose.val.support.IsPWO := by
  simp only [Subtype.forall]
  convert (exists_canonical_expansion x).choose.prop
  simp

-- When p-adic Hahn series x ≠ 0, its support is nonempty.
theorem support_nonempty_of_nonzero
    (p : ℕ) [inst : Fact (Nat.Prime p)]
    (x : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) (h : ¬x = 0) :
    (exists_canonical_expansion x).choose.val.support.Nonempty := by
  contrapose h
  simp only [Subtype.forall, Function.support_nonempty_iff, ne_eq, not_not] at h
  have := (exists_canonical_expansion x).choose_spec.1
  simp only [Subtype.forall, h] at this
  suffices h' : (@LiftedPAdicHahnSeries.from_coeff p _ 0 (by simp)) = 0 by
    simp only [h'] at this
    rw [← Quotient.out_eq x]
    exact Quotient.sound this
  simpa [LiftedPAdicHahnSeries.from_coeff] using Eq.symm Pi.zero_def

-- Helper for `val.map_one'`: the minimum of the canonical expansion's support of `1` is `0`.
-- Strategy: `s := Pi.single 0 1` is a canonical-expansion candidate for `1`; uniqueness
-- (`exists_canonical_expansion.choose_spec.2`) forces `(exists_canonical_expansion 1).choose.val`
-- to equal `s`. Hence the support is `{0}`, and `Set.IsWF.min` of `{0}` is `0`.
private lemma val_one_eq_zero (p : ℕ) [Fact (Nat.Prime p)] :
    (support_IsPWO (1 : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p))).isWF.min
      (support_nonempty_of_nonzero p 1 one_ne_zero) = (0 : ℚ) := by
  sorry

-- A null series cannot have a unit-valued leading coefficient. The "engine" lemma
-- powering the strict-ultrametric arguments in `val.map_add_le_max'` and `val.map_mul'`.
-- Mirrors the `h_sum_eq`-then-tendsto-contradiction pattern of `exists_canonical_representative`
-- (L1455-1518): if `Δ.coeff q` is a unit, the partial sums of `IsNullSeries Δ` at `g := q`
-- have valuation = `ofAdd(0)` for all M ≥ ⌈q⌉ (strict ultrametric: n=0 term dominates), but
-- `Tendsto _ (𝓝 0)` requires the valuation to eventually drop below `ofAdd(0)`. Contradiction.
private lemma null_series_no_unit_leading {p : ℕ} [Fact (Nat.Prime p)]
    {Δ : LiftedPAdicHahnSeries p} (hΔ : Δ ∈ NullSeriesIdeal p)
    {q : ℚ} (hq_unit : IsUnit (Δ.coeff q))
    (hq_lead : ∀ q' < q, Δ.coeff q' = 0) : False := by
  sorry

/-- The leading coefficient of a `from_coeff`-built series at the minimum of its support
is a unit in `𝕎(Fpbar p)`. This abstracts the Teichmüller-leading-unit pattern from
Session 6's `support_ZpUn_embd_nonneg` (L4065–4077). -/
private lemma canonical_leading_coeff_isUnit
    {p : ℕ} [Fact (Nat.Prime p)]
    {s : ℚ → Fpbar p} (hspwo : (Function.support s).IsPWO)
    (hsne : (Function.support s).Nonempty) :
    IsUnit ((LiftedPAdicHahnSeries.from_coeff s hspwo).coeff
      (hspwo.isWF.min hsne)) := by
  set q₀ := hspwo.isWF.min hsne with hq₀_def
  have hq₀_in : q₀ ∈ Function.support s := hspwo.isWF.min_mem hsne
  have hsq₀_ne : s q₀ ≠ 0 := hq₀_in
  change IsUnit (teichmuller p (s q₀))
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [WittVector.teichmuller_coeff_zero]
  exact hsq₀_ne

/-- For any nonzero element `A` of the quotient `LiftedPAdicHahnSeries p ⧸ NullSeriesIdeal p`,
there exists an inverse `B` with `A * B = 1`. The proof uses the canonical expansion to obtain
a representative `f := from_coeff s_A`, applies `canonical_leading_coeff_isUnit` to show
`IsUnit f.leadingCoeff`, then concludes `IsUnit f` via Mathlib's `HahnSeries.isUnit_iff`,
and finally projects the Mathlib-supplied inverse to the quotient. -/
private lemma exists_inverse_of_nonzero
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) (hA : A ≠ 0) :
    ∃ B, A * B = 1 := by
  set s_A : ℚ → Fpbar p := (exists_canonical_expansion A).choose.val with hs_A_def
  have hspwo : (Function.support s_A).IsPWO := (exists_canonical_expansion A).choose.prop
  have hsne : (Function.support s_A).Nonempty := support_nonempty_of_nonzero p A hA
  set f : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.from_coeff s_A hspwo with hf_def
  -- f represents A in the quotient.
  have hmk_f : (Ideal.Quotient.mk (NullSeriesIdeal p)) f = A := by
    have h := (exists_canonical_expansion A).choose_spec.1
    have h_eq : (Ideal.Quotient.mk (NullSeriesIdeal p)) A.out =
        (Ideal.Quotient.mk (NullSeriesIdeal p)) f := Quotient.sound h
    exact h_eq.symm.trans (Quotient.out_eq A)
  -- f.support = Function.support s_A (via injectivity of teichmuller).
  have h_supp_eq : f.support = Function.support s_A := by
    ext n
    simp only [HahnSeries.mem_support, Function.mem_support]
    change teichmuller p (s_A n) ≠ 0 ↔ s_A n ≠ 0
    refine ⟨fun h h' => h (by rw [h', WittVector.teichmuller_zero p]), fun h h' => h ?_⟩
    exact (injective_teichmuller p) (by rw [h', WittVector.teichmuller_zero p])
  -- f ≠ 0 from the support being nonempty.
  have hf_ne : f ≠ 0 := by
    intro hf0
    have h_zero_supp : Function.support s_A = ∅ := by
      rw [← h_supp_eq, hf0]
      exact HahnSeries.support_zero
    exact (Set.not_nonempty_iff_eq_empty.mpr h_zero_supp) hsne
  -- Bridge the Mathlib leading coefficient to the support-min coefficient.
  have h_lc_eq : f.leadingCoeff = f.coeff (hspwo.isWF.min hsne) := by
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.order_of_ne hf_ne]
    congr!
  -- IsUnit of the leading coefficient via the Session 8 lemma.
  have h_lc_unit : IsUnit f.leadingCoeff := by
    rw [h_lc_eq]
    exact canonical_leading_coeff_isUnit hspwo hsne
  -- IsUnit of f via Mathlib's HahnSeries.isUnit_iff (uses IsDomain (ℤᵘⁿ_[p])).
  have hf_unit : IsUnit f := HahnSeries.isUnit_iff.mpr h_lc_unit
  -- Take the inverse in LiftedPAdicHahnSeries p.
  set u := hf_unit.unit with hu_def
  have hu_val : u.val = f := IsUnit.unit_spec hf_unit
  set g : LiftedPAdicHahnSeries p := (u⁻¹).val with hg_def
  have hfg : f * g = 1 := by
    rw [← hu_val]
    exact u.mul_inv
  -- Project to the quotient.
  refine ⟨(Ideal.Quotient.mk (NullSeriesIdeal p)) g, ?_⟩
  rw [← hmk_f, ← (Ideal.Quotient.mk _).map_mul, hfg, (Ideal.Quotient.mk _).map_one]

-- [Corollary 3, Poonen1993] : The ideal of null series is maximal, so pAdicHahnSeries p is a field.
instance (p : ℕ) [Fact (Nat.Prime p)] : (NullSeriesIdeal p).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  refine ⟨?_, ?_, ?_⟩
  · -- exists_pair_ne: 1 ≠ 0 in the quotient.
    refine ⟨1, 0, ?_⟩
    intro h
    apply one_notMem_NullSeriesIdeal p
    have h1 : (Ideal.Quotient.mk (NullSeriesIdeal p)) (1 : LiftedPAdicHahnSeries p) =
        (Ideal.Quotient.mk (NullSeriesIdeal p)) (0 : LiftedPAdicHahnSeries p) := by
      simp [h]
    have := Ideal.Quotient.eq.mp h1
    simpa using this
  · -- mul_comm: from CommRing structure.
    intros a b
    exact mul_comm a b
  · -- mul_inv_cancel: every nonzero element has a right inverse.
    intros a ha
    exact exists_inverse_of_nonzero p a ha

-- The valuation of a p-adic Hahn series x is defined to be the minimum of the support of x.
open Classical in
noncomputable def val
  (p : ℕ) [Fact (Nat.Prime p)] :
  AddValuation ((LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) (WithTop ℚ) := {
  toFun x :=
    if h : x = 0 then (⊤ : WithTop ℚ)
    else ((support_IsPWO x).isWF.min (support_nonempty_of_nonzero p x h) : WithTop ℚ)
  map_zero' := by
    simp only
    rfl
  map_one' := by
    simp only
    rw [dif_neg (one_ne_zero : (1 : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) ≠ 0)]
    rw [val_one_eq_zero p]
    rfl
  map_mul' := by
    sorry
  map_add_le_max' := by
    sorry
}

abbrev pAdicHahnSeries (p : ℕ) [Fact (Nat.Prime p)] : Type _ := WithVal (val p)

notation "𝕃_[" p "]" => pAdicHahnSeries p

namespace pAdicHahnSeries
-- Given a p-adic Hahn series x, write x = ∑ₖ [aₖ] pᵏ where aₖ ∈ 𝔽ₚ^⁻, then the `coefficients` of x
-- is defined to be the function k ↦ aₖ, where k∈ 𝔽ₚ^-.
noncomputable def coeff {p : ℕ} [Fact (Nat.Prime p)] (x : 𝕃_[p]) :
  ℚ → Fpbar p := (exists_canonical_expansion x).choose.val

-- The `support` of a p-adic Hahn series x is defined to be the support of the coefficients function
-- of x.
noncomputable def support {p : ℕ} [Fact (Nat.Prime p)] (x : 𝕃_[p]) : Set ℚ :=
  (exists_canonical_expansion x).choose.val.support

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Field (𝕃_[p]) := by
  apply Ideal.Quotient.field

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
  Valued (𝕃_[p]) (Multiplicative (WithTop ℚ)ᵒᵈ) := by
  unfold pAdicHahnSeries
  infer_instance

/-- Helper: in `WittVector p (Fpbar p) = ℤᵘⁿ_[p]`, the Teichmüller lifts of two distinct
elements differ by a unit. The argument uses the residue-field map (the `0`-th coefficient
in characteristic `p`) and `WittVector.isUnit_of_coeff_zero_ne_zero`. -/
private lemma teich_sub_isUnit {p : ℕ} [Fact (Nat.Prime p)]
    {a b : Fpbar p} (h : a ≠ b) :
    IsUnit (teichmuller p a - teichmuller p b) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  intro h0
  have h_imp : ∀ i < 1, ((teichmuller p) a - (teichmuller p) b).coeff i = 0 := by
    intro i hi; interval_cases i; exact h0
  have h_eq : ((teichmuller p) a).coeff 0 = ((teichmuller p) b).coeff 0 :=
    (WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero (n := 1)).mpr h_imp 0 (by omega)
  rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at h_eq
  exact h h_eq

set_option synthInstance.maxHeartbeats 220000 in
-- Heartbeat ceilings raised: the proof contains many `set` bindings over the canonical-expansion
-- choose_spec apparatus and exercises typeclass synthesis through the WithVal alias when calling
-- `Quotient.sound` on the choose_spec relation; the default budgets fall short.
/-- The canonical-section map `x ↦ LPHS.from_coeff x.coeff (support_IsPWO x)` is an
isometry from the val-topology on 𝕃_[p] to the orderTop-topology on LPHS p:
`HahnSeries.orderTop (canonical(x) - canonical(y)) = val(x - y)` for all `x, y ∈ 𝕃_[p]`.

This is the strategic linchpin for the LaurentSeries-style proof of `CompleteSpace 𝕃_[p]`:
a Cauchy filter in 𝕃_[p] lifts to a Cauchy filter in LPHS via this section. The proof uses
`null_series_no_unit_leading` twice: once to show that `Δ := f_x - f_y - f_z` (a null series)
cannot have its leading coefficient strictly below `q_z := val(x - y)` (via `teich_sub_isUnit`
applied to differing s_x, s_y values at q_Δ), and once to show that `(f_x - f_y).coeff q_z ≠ 0`
(else `Δ.coeff q_z = -teich(s_z q_z)` is a unit, contradicting `null_series_no_unit_leading`). -/
private lemma canonical_isometry (p : ℕ) [Fact (Nat.Prime p)] (x y : 𝕃_[p]) :
    HahnSeries.orderTop
      (LiftedPAdicHahnSeries.from_coeff (coeff x) (support_IsPWO x) -
       LiftedPAdicHahnSeries.from_coeff (coeff y) (support_IsPWO y)) =
    (val p) (x - y) := by
  sorry

/-USER: This should be easy, since every element of L_p can be written as ∑[a_k]p^k with k ∈ ℚ. Given a Cauchy sequence {a_k} in L_p, v_p(a_k-a_{k+1}) is large means that their truncation agrees up to a large power of p. This should be enough-/
-- The field of p-adic Hahn series is complete with respect to the valuation defined above.

/-
Decomposition of `instCompleteSpace` (mirroring `LaurentSeries.instLaurentSeriesComplete`,
adapted for ℚ-indexed Hahn series via the `canonical_isometry` linchpin from L588):

  Step A. (`coeff_stable`) For every Cauchy filter `ℱ` in `𝕃_[p]` and every `q : ℚ`,
    there is a unique `c_q : Fpbar p` with `∀ᶠ x in ℱ, (coeff x) q = c_q`.

  Step B. (`limit_coeff_pwo`) The function `c : ℚ → Fpbar p` produced in Step A has
    PWO support: pick a base element `x₀ ∈ ℱ`; for every `q ∉ x₀.support`, eventually
    `coeff x q = c_q`, and a careful choice of "small ε" forces `c_q = x₀.coeff q = 0`
    once `q` is bigger than every support point of `x₀` plus the chosen tail bound.
    More carefully, `support c ⊆ ⋃_{n} support (xₙ)` for a sequence of choices; each
    `support xₙ` is PWO, and a ω-style cofinal union of PWO sets in ℚ is again PWO.

  Step C. (`limit_construction`) Define `x_lim := from_coeff c (limit_coeff_pwo)`.

  Step D. (`limit_convergence`) Show `ℱ ≤ 𝓝 x_lim`. Given a basic open `U` of `x_lim`,
    use `canonical_isometry` to translate the val-distance between `x` and `x_lim`
    into `HahnSeries.orderTop` of the difference of canonical reps; combined with
    Step A and a uniform support-stabilization, eventually all `x ∈ ℱ` lie in `U`.

We isolate Steps A, B, C, D as named scoped lemmas so subsequent rounds can attack
them individually.
-/

-- Step A: coefficient stabilization. For each q, `(fun x => (coeff x) q)` pushes a
-- Cauchy filter forward to a Cauchy filter in the discrete space `Fpbar p`, which
-- (being discrete and nonempty) converges to a unique constant.
private lemma coeff_stable_of_cauchy {p : ℕ} [Fact (Nat.Prime p)]
    {ℱ : Filter (𝕃_[p])} (hℱ : Cauchy ℱ) (q : ℚ) :
    ∃ c : Fpbar p, ∀ᶠ x in ℱ, (pAdicHahnSeries.coeff x) q = c := by
  -- The coefficient map `pAdicHahnSeries.coeff (·) q : 𝕃_[p] → Fpbar p` is uniformly
  -- continuous via `canonical_isometry`: when `val (x - y) > q`, the canonical reps
  -- agree at `q`, hence `coeff x q = coeff y q`. So `Filter.map (coeff · q) ℱ` is a
  -- Cauchy filter on the discrete space `Fpbar p`, which converges to a unique value.
  sorry

-- Step B: PWO support of the limit coefficient function. Bundles the existence claim
-- of Step A with the PWO conclusion via classical choice.
private noncomputable def limit_coeff {p : ℕ} [Fact (Nat.Prime p)]
    {ℱ : Filter (𝕃_[p])} (hℱ : Cauchy ℱ) : ℚ → Fpbar p :=
  fun q => (coeff_stable_of_cauchy hℱ q).choose

private lemma limit_coeff_pwo {p : ℕ} [Fact (Nat.Prime p)]
    {ℱ : Filter (𝕃_[p])} (hℱ : Cauchy ℱ) :
    (Function.support (limit_coeff hℱ)).IsPWO := by
  -- For any `q` with `limit_coeff hℱ q ≠ 0`, eventually `coeff x q = limit_coeff hℱ q ≠ 0`,
  -- so `q ∈ support (coeff x)` for some `x ∈ ℱ`. Choose, for each ε, a `xε ∈ ℱ` with
  -- `val (x - y) ≥ ε` for all `x, y ∈ ℱ`-eventually; the support of `xε.coeff` is PWO.
  -- A uniform-Cauchy argument shows `support (limit_coeff hℱ) ⊆ ⋃_n support (xn.coeff)`
  -- for a countable chain; the countable union of PWO sets in ℚ controlled by an
  -- ascending Cauchy structure is PWO.
  sorry

-- Step C: construct the limit element of 𝕃_[p].
private noncomputable def limit_elt {p : ℕ} [Fact (Nat.Prime p)]
    {ℱ : Filter (𝕃_[p])} (hℱ : Cauchy ℱ) : 𝕃_[p] :=
  Ideal.Quotient.mk (NullSeriesIdeal p)
    (LiftedPAdicHahnSeries.from_coeff (limit_coeff hℱ) (limit_coeff_pwo hℱ))

-- Step D: convergence. Use `canonical_isometry` to translate val-distance to
-- `HahnSeries.orderTop` and conclude `ℱ ≤ 𝓝 (limit_elt hℱ)`.
open Topology Filter in
private lemma limit_elt_isLimit {p : ℕ} [Fact (Nat.Prime p)]
    {ℱ : Filter (𝕃_[p])} (hℱ : Cauchy ℱ) :
    ℱ ≤ 𝓝 (limit_elt hℱ) := by
  -- For each ε, the open ball `{y | val (y - limit_elt hℱ) > ε}` (in additive terms,
  -- via `Multiplicative` / `WithTop ℚ`) is generated by the val-uniformity. Apply
  -- `canonical_isometry`: `val (y - limit_elt hℱ) = HahnSeries.orderTop (canon y - canon (limit_elt hℱ))`.
  -- Since `canon (limit_elt hℱ) = from_coeff (limit_coeff hℱ) (limit_coeff_pwo hℱ)` (up to
  -- the section being canonical), the orderTop is large iff the two canonical reps agree
  -- at all q ≤ ε. By Step A, eventually `coeff x q = limit_coeff hℱ q` for each fixed q;
  -- a uniform argument over a finite "low-q" set (using PWO of `support (limit_coeff hℱ)
  -- ∪ support (coeff x)` for some witness `x`) closes the ball.
  sorry

instance instCompleteSpace {p : ℕ} [Fact (Nat.Prime p)] :
    CompleteSpace (𝕃_[p]) := by
  refine ⟨fun {ℱ} hℱ => ?_⟩
  exact ⟨limit_elt hℱ, limit_elt_isLimit hℱ⟩


end pAdicHahnSeries
end Poonen1993
