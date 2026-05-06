import FormalizedSparse.References.WittVector
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.WittVector.TeichmullerSeries

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
      have hm_le : m ≤ g + n := by
        exact x.isWF_support.min_le hs <| (HahnSeries.mem_support x (g + n)).2 hn.2
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
      have hm_le : m ≤ g + n := by
        exact x.isWF_support.min_le hs <| (HahnSeries.mem_support x (g + n)).2 hn.2
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

-- [Proposition 3, Poonen1993] : The null series form an ideal of W(𝔽ₚ^⁻)((t^ℚ)).
def NullSeriesIdeal (p : ℕ) [Fact (Nat.Prime p)] : Ideal (LiftedPAdicHahnSeries p) where
  carrier := {x | IsNullSeries x}
  add_mem' := by
    intro x y hx hy
    change IsNullSeries x at hx
    change IsNullSeries y at hy
    change IsNullSeries (x + y)
    intro g
    let sx : ℕ → Finset ℤ := fun M => Set.Finite.toFinset (finprop x g M)
    let sy : ℕ → Finset ℤ := fun M => Set.Finite.toFinset (finprop y g M)
    let sxy : ℕ → Finset ℤ := fun M => Set.Finite.toFinset (finprop (x + y) g M)
    let su : ℕ → Finset ℤ := fun M => sx M ∪ sy M
    let fx : ℕ → ℤ → QpUn p := fun M n =>
      (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (x.coeff (g + n))
    let fy : ℕ → ℤ → QpUn p := fun M n =>
      (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (y.coeff (g + n))
    let fxy : ℕ → ℤ → QpUn p := fun M n =>
      (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) ((x + y).coeff (g + n))
    have hsxy_sub : ∀ M, sxy M ⊆ su M := by
      intro M n hn
      have hn' : g + n ≤ M ∧ (x + y).coeff (g + n) ≠ 0 := by
        exact (Set.Finite.mem_toFinset (hs := finprop (x + y) g M) (a := n)).1 hn
      have hmem : g + n ∈ (x + y).support := by
        exact (HahnSeries.mem_support (x + y) (g + n)).2 hn'.2
      have hunion := HahnSeries.support_add_subset (x := x) (y := y) hmem
      rcases hunion with hxmem | hymem
      · exact Finset.mem_union_left _ <|
          (Set.Finite.mem_toFinset (hs := finprop x g M) (a := n)).2 ⟨hn'.1, hxmem⟩
      · exact Finset.mem_union_right _ <|
          (Set.Finite.mem_toFinset (hs := finprop y g M) (a := n)).2 ⟨hn'.1, hymem⟩
    have hsumx (M : ℕ) : Finset.sum (su M) (fx M) = Finset.sum (sx M) (fx M) := by
      symm
      apply Finset.sum_subset
      · intro n hn
        exact Finset.mem_union_left _ hn
      · intro n hnu hnsx
        have hny : n ∈ sy M := (Finset.mem_union.mp hnu).resolve_left hnsx
        have hmem : g + n ≤ M ∧ y.coeff (g + n) ≠ 0 :=
          (Set.Finite.mem_toFinset (hs := finprop y g M) (a := n)).1 hny
        have hxzero : x.coeff (g + n) = 0 := by
          by_contra hxne
          exact hnsx <|
            (Set.Finite.mem_toFinset (hs := finprop x g M) (a := n)).2 ⟨hmem.1, hxne⟩
        simp [hxzero]
    have hsumy (M : ℕ) : Finset.sum (su M) (fy M) = Finset.sum (sy M) (fy M) := by
      symm
      apply Finset.sum_subset
      · intro n hn
        exact Finset.mem_union_right _ hn
      · intro n hnu hnsy
        have hnx : n ∈ sx M := (Finset.mem_union.mp hnu).resolve_right hnsy
        have hmem : g + n ≤ M ∧ x.coeff (g + n) ≠ 0 :=
          (Set.Finite.mem_toFinset (hs := finprop x g M) (a := n)).1 hnx
        have hyzero : y.coeff (g + n) = 0 := by
          by_contra hyne
          exact hnsy <|
            (Set.Finite.mem_toFinset (hs := finprop y g M) (a := n)).2 ⟨hmem.1, hyne⟩
        simp [hyzero]
    have hsumxy (M : ℕ) : Finset.sum (su M) (fxy M) = Finset.sum (sxy M) (fxy M) := by
      symm
      apply Finset.sum_subset
      · exact hsxy_sub M
      · intro n hnu hnsxy
        have hcoeff : (x + y).coeff (g + n) = 0 := by
          by_contra hne
          exact hnsxy <| (Set.Finite.mem_toFinset (hs := finprop (x + y) g M) (a := n)).2 ⟨by
            rcases Finset.mem_union.mp hnu with hnx | hny
            · exact (Set.Finite.mem_toFinset (hs := finprop x g M) (a := n)).1 hnx |>.1
            · exact (Set.Finite.mem_toFinset (hs := finprop y g M) (a := n)).1 hny |>.1, hne⟩
        simp [hcoeff]
    have hfun :
        (fun M => Finset.sum (sxy M) (fxy M)) =
          fun M => Finset.sum (sx M) (fx M) + Finset.sum (sy M) (fy M) := by
      funext M
      rw [← hsumxy M]
      calc
        Finset.sum (su M) (fxy M) = Finset.sum (su M) (fun n => fx M n + fy M n) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [fxy, fx, fy, HahnSeries.coeff_add', mul_add, map_add]
        _ = Finset.sum (su M) (fx M) + Finset.sum (su M) (fy M) := by
          rw [Finset.sum_add_distrib]
        _ = Finset.sum (sx M) (fx M) + Finset.sum (sy M) (fy M) := by
          rw [hsumx M, hsumy M]
    have hxmain :
        (fun M => ∑ n ∈ (Set.Finite.toFinset (finprop x g M)).attach,
            (p : QpUn p) ^ n.val * algebraMap (OQpUn p) (QpUn p) (x.coeff (g + n))) =
          fun M => Finset.sum (sx M) (fx M) := by
      funext M
      dsimp [sx, fx]
      simpa using (Finset.sum_attach (s := Set.Finite.toFinset (finprop x g M))
        (f := fun n : ℤ => (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (x.coeff (g + n))))
    have hymain :
        (fun M => ∑ n ∈ (Set.Finite.toFinset (finprop y g M)).attach,
            (p : QpUn p) ^ n.val * algebraMap (OQpUn p) (QpUn p) (y.coeff (g + n))) =
          fun M => Finset.sum (sy M) (fy M) := by
      funext M
      dsimp [sy, fy]
      simpa using (Finset.sum_attach (s := Set.Finite.toFinset (finprop y g M))
        (f := fun n : ℤ => (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (y.coeff (g + n))))
    have hmain :
        (fun M =>
          ∑ n : Set.Finite.toFinset (finprop (x + y) g M),
            (p : QpUn p) ^ n.val * algebraMap (OQpUn p) (QpUn p) ((x + y).coeff (g + n))) =
          fun M => Finset.sum (sxy M) (fxy M) := by
      funext M
      dsimp [sxy, fxy]
      simpa using (Finset.sum_attach (s := Set.Finite.toFinset (finprop (x + y) g M))
        (f := fun n : ℤ =>
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) ((x + y).coeff (g + n))))
    have hx' : Filter.Tendsto (fun M => Finset.sum (sx M) (fx M)) Filter.atTop (nhds 0) := by
      rw [← hxmain]
      exact hx g
    have hy' : Filter.Tendsto (fun M => Finset.sum (sy M) (fy M)) Filter.atTop (nhds 0) := by
      rw [← hymain]
      exact hy g
    rw [hmain]
    rw [hfun]
    simpa using hx'.add hy'
  zero_mem' := by simp [IsNullSeries]
  smul_mem' := by admit

-- [Corollary 3, Poonen1993] : The ideal of null series is maximal, so pAdicHahnSeries p is a field.
instance (p : ℕ) [Fact (Nat.Prime p)] : (NullSeriesIdeal p).IsMaximal := by admit

/-
  Auxiliary infrastructure for the proof of `exists_canonical_expansion`.

  Following `informal/exists_canonical_expansion.md`, the proof is decomposed
  into helper lemmas. The deepest step (uniqueness of the Teichmuller series)
  is a TODO upstream in Mathlib (`Mathlib.RingTheory.WittVector.TeichmullerSeries`).
  Existence comes from `dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff`
  applied per coset `g ∈ Set.Ico (0:ℚ) 1`.
-/

namespace existsCanonicalExpansionAux

open scoped Pointwise

variable {p : ℕ} [Fact (Nat.Prime p)]

/--
The image of `ℕ` under the canonical embedding `ℕ → ℚ` is partially well-ordered.
This is a basic ingredient for the support-PWO bound `support s ⊆ support α + ℕ`.
-/
lemma natRange_isPWO : (Set.range ((↑) : ℕ → ℚ)).IsPWO := by
  have hUniv : (Set.univ : Set ℕ).IsPWO := Set.isPWO_of_wellQuasiOrderedLE _
  have hMono : MonotoneOn ((↑) : ℕ → ℚ) Set.univ := by
    intro a _ b _ h
    exact_mod_cast h
  simpa using hUniv.image_of_monotoneOn hMono

/--
**Support PWO bound.** If a function `s : ℚ → Fpbar p` has its support contained
in `α.support + Set.range ((↑) : ℕ → ℚ)`, then `support s` is partially
well-ordered. This is the key tool for closing the `IsPWO` obligation on `s`
in `exists_canonical_representative` once the construction yields the bound
`support s ⊆ support α + ℕ`.
-/
lemma support_isPWO_of_subset_support_add_natRange
    (α : LiftedPAdicHahnSeries p) {s : ℚ → Fpbar p}
    (h : Function.support s ⊆ α.support + Set.range ((↑) : ℕ → ℚ)) :
    (Function.support s).IsPWO :=
  (α.isPWO_support.add natRange_isPWO).mono h
/--
For every rational `q : ℚ`, the decomposition `q = Int.fract q + ⌊q⌋` holds,
with `Int.fract q ∈ Set.Ico 0 1`.
-/
lemma rat_decompose (q : ℚ) :
    Int.fract q + (⌊q⌋ : ℚ) = q ∧
    (0 : ℚ) ≤ Int.fract q ∧ Int.fract q < 1 := by
  refine ⟨?_, Int.fract_nonneg q, Int.fract_lt_one q⟩
  have h := Int.fract_add_floor q
  linarith

/--
**Cauchy partial sums** (sub-claim of existence). For each `g : ℚ`, the
integer-cutoff partial sums `intPartial α g K` form a Cauchy sequence in
`ℚᵘⁿ_[p]` as `K → ∞`. This follows because `α.coeff (g+n) p^n` has
`v(·) ≥ n` (in fact more, since `α.coeff (g+n) ∈ ℤᵘⁿ_[p]`), so the tail
contribution is `≤ p^{-n} → 0`. **Sub-task for next session.**
-/
lemma intPartial_isCauchy (α : LiftedPAdicHahnSeries p) (g : ℚ) :
    ∀ ε : NNReal, 0 < ε → ∃ K₀ : ℤ, ∀ K K' : ℤ, K₀ ≤ K → K₀ ≤ K' →
      ‖intPartial α g K - intPartial α g K'‖ < ε := by
  -- Strategy: bound `Valued.v (intPartial K - intPartial K')` by the valuation of
  -- a "tail" sum whose entries each have valuation `≤ ofAdd(-(min K K' + 1))`,
  -- then convert to norm via `WithZeroMulInt.toNNReal_strictMono`.
  intro ε hε
  -- Preliminaries: `Valued.v (p : QpUn p) = ofAdd(-1)` (uniformizer in WittVector DVR)
  have hp_val : Valued.v ((p : QpUn p)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
    rw [show ((p : QpUn p)) = algebraMap (OQpUn p) (QpUn p) (p : OQpUn p) from by push_cast; rfl]
    rw [show (Valued.v : QpUn p → _) =
        (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation _ from rfl]
    rw [(IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation_of_algebraMap]
    have hirr : Irreducible (p : OQpUn p) := WittVector.irreducible p
    have hpe : (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).asIdeal =
        Ideal.span {(p : OQpUn p)} := hirr.maximalIdeal_eq
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
      (WittVector.p_nonzero p _) hpe]
    rfl
  -- Per-summand bound: `Valued.v (p^n · algebraMap a) ≤ ofAdd(-n)` for `a : OQpUn p`.
  have hterm_bound : ∀ (a : OQpUn p) (n : ℤ),
      Valued.v ((p : QpUn p)^n * algebraMap (OQpUn p) (QpUn p) a) ≤
        ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
    intro a n
    rw [Valuation.map_mul]
    have hpn_val : Valued.v ((p : QpUn p)^n) =
        ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
      have hzpow : Valued.v ((p : QpUn p)^n) = (Valued.v ((p : QpUn p)))^n :=
        map_zpow₀ Valued.v _ _
      rw [hzpow, hp_val, ← WithZero.coe_zpow]
      congr 1
      rw [← ofAdd_zsmul n (-1 : ℤ)]
      congr 1
      ring
    rw [hpn_val]
    have h_alg : Valued.v (algebraMap (OQpUn p) (QpUn p) a) ≤ 1 :=
      (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation_le_one a
    calc ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) *
            Valued.v (algebraMap (OQpUn p) (QpUn p) a)
        ≤ ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) * 1 :=
          mul_le_mul' (le_refl _) h_alg
      _ = ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := mul_one _
  -- Difference of intPartials at K ≤ K' is a sum over a Finset of `n > K, n ≤ K'`.
  have hdiff_eq : ∀ K K' : ℤ, K ≤ K' →
      intPartial α g K' - intPartial α g K =
        ∑ n ∈ (Set.Finite.toFinset (finpropInt α g K') \
                Set.Finite.toFinset (finpropInt α g K)),
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + n)) := by
    intro K K' hKK'
    have hsub : Set.Finite.toFinset (finpropInt α g K) ⊆
        Set.Finite.toFinset (finpropInt α g K') := by
      intro n hn
      have hn_mem : n ∈ {n : ℤ | n ≤ K ∧ α.coeff (g + n) ≠ 0} :=
        (Set.Finite.mem_toFinset _).mp hn
      exact (Set.Finite.mem_toFinset _).mpr ⟨le_trans hn_mem.1 hKK', hn_mem.2⟩
    have e1 : intPartial α g K' = ∑ n ∈ Set.Finite.toFinset (finpropInt α g K'),
        (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + n)) :=
      Finset.sum_attach (s := Set.Finite.toFinset (finpropInt α g K'))
        (f := fun m : ℤ => (p : QpUn p) ^ m * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + m)))
    have e2 : intPartial α g K = ∑ n ∈ Set.Finite.toFinset (finpropInt α g K),
        (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + n)) :=
      Finset.sum_attach (s := Set.Finite.toFinset (finpropInt α g K))
        (f := fun m : ℤ => (p : QpUn p) ^ m * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + m)))
    rw [e1, e2, ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  -- Norm conversion: `‖a‖ = ↑(toNNReal (Valued.v a))`
  have hnorm_eq : ∀ a : QpUn p, ‖a‖ =
      ((WithZeroMulInt.toNNReal (p_ne_zero p) (Valued.v a) : NNReal) : ℝ) := fun a => rfl
  -- p > 1 in NNReal
  have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
  have hpinv_lt : (p : NNReal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hpinv_nn : 0 ≤ ((p : NNReal)⁻¹ : NNReal) := zero_le _
  -- Strict monotonicity of toNNReal
  have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
    WithZeroMulInt.toNNReal_strictMono hp1
  -- toNNReal of ofAdd(-n) = (p : NNReal)^(-n)
  have htoNN : ∀ n : ℤ,
      (WithZeroMulInt.toNNReal (p_ne_zero p)
        (((Multiplicative.ofAdd (n : ℤ) : Multiplicative ℤ) : WithZero _))) = (p : NNReal)^n := by
    intro n
    simp [WithZeroMulInt.toNNReal]
  -- Find N : ℕ such that (p : NNReal)⁻¹^N < ε
  have htendsto : Filter.Tendsto (fun n : ℕ => ((p : NNReal)⁻¹)^n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hpinv_nn hpinv_lt
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ((p : NNReal)⁻¹)^N < ε := by
    have h_eventually : ∀ᶠ n : ℕ in Filter.atTop, ((p : NNReal)⁻¹)^n < ε :=
      htendsto.eventually (eventually_lt_nhds hε)
    exact h_eventually.exists
  -- Set K₀ := N - 1 (an integer). For K ≥ K₀, K + 1 ≥ N.
  refine ⟨(N : ℤ) - 1, ?_⟩
  intro K K' hK hK'
  -- Reduce to K ≤ K' case
  rcases le_total K K' with hKK' | hKK'
  · -- K ≤ K' case: ‖intPartial K - intPartial K'‖ = ‖intPartial K' - intPartial K‖
    rw [norm_sub_rev, hdiff_eq K K' hKK']
    -- Show valuation bound
    have hval_bound : Valued.v (∑ n ∈ (Set.Finite.toFinset (finpropInt α g K') \
            Set.Finite.toFinset (finpropInt α g K)),
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + n))) ≤
        ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
      apply Valuation.map_sum_le
      intro n hn
      have hn_mem : n ∈ Set.Finite.toFinset (finpropInt α g K') ∧
          n ∉ Set.Finite.toFinset (finpropInt α g K) := Finset.mem_sdiff.mp hn
      have hn1 : n ≤ K' ∧ α.coeff (g + n) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finpropInt α g K')).mp hn_mem.1
      have hn2 : ¬ (n ≤ K ∧ α.coeff (g + n) ≠ 0) := by
        intro h
        exact hn_mem.2 ((Set.Finite.mem_toFinset (hs := finpropInt α g K)).mpr h)
      have hn_gt : K < n := by
        by_contra hle
        push_neg at hle
        exact hn2 ⟨hle, hn1.2⟩
      have hn_ge : K + 1 ≤ n := hn_gt
      -- Apply per-summand bound
      have h1 := hterm_bound (α.coeff (g + n)) n
      -- Bound by ofAdd(-(K+1)) using monotonicity
      have h2 : ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) ≤
          ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
        rw [WithZero.coe_le_coe]
        exact Multiplicative.ofAdd_le.mpr (by omega)
      exact h1.trans h2
    -- Convert valuation bound to norm bound
    rw [hnorm_eq]
    have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (∑ n ∈ (Set.Finite.toFinset (finpropInt α g K') \
            Set.Finite.toFinset (finpropInt α g K)),
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + n)))) ≤
        WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) :=
      hsm.monotone hval_bound
    rw [htoNN (-(K + 1))] at h_nnreal_le
    have h_pow_lt : (p : NNReal)^(-((K : ℤ) + 1)) < ε := by
      have h_pow_eq : (p : NNReal)^(-((K : ℤ) + 1)) = ((p : NNReal)⁻¹)^((K : ℤ) + 1) := by
        rw [zpow_neg, ← inv_zpow]
      rw [h_pow_eq]
      have hKN : (N : ℤ) ≤ K + 1 := by linarith
      have hN_pos : 0 ≤ (K : ℤ) + 1 := by linarith
      -- ((p : NNReal)⁻¹)^(K+1 : ℤ) = ((p : NNReal)⁻¹)^(K+1).toNat
      have h_zpow_toNat : ((p : NNReal)⁻¹)^((K : ℤ) + 1) =
          ((p : NNReal)⁻¹)^((K + 1).toNat) := by
        rw [← zpow_natCast]
        congr 1
        omega
      rw [h_zpow_toNat]
      -- For K+1 ≥ N, ((p⁻¹))^(K+1) ≤ ((p⁻¹))^N (decreasing)
      have h_le : ((p : NNReal)⁻¹)^((K + 1).toNat) ≤ ((p : NNReal)⁻¹)^N := by
        apply pow_le_pow_of_le_one hpinv_nn (le_of_lt hpinv_lt)
        omega
      exact h_le.trans_lt hN
    have h_combined : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (∑ n ∈ (Set.Finite.toFinset (finpropInt α g K') \
              Set.Finite.toFinset (finpropInt α g K)),
            (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + n)))) < ε :=
      h_nnreal_le.trans_lt h_pow_lt
    exact_mod_cast h_combined
  · -- K' ≤ K case: diff is over T(K) \ T(K'), bound at K' + 1
    rw [hdiff_eq K' K hKK']
    have hval_bound : Valued.v (∑ n ∈ (Set.Finite.toFinset (finpropInt α g K) \
            Set.Finite.toFinset (finpropInt α g K')),
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + n))) ≤
        ((Multiplicative.ofAdd (-(K' + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
      apply Valuation.map_sum_le
      intro n hn
      have hn_mem : n ∈ Set.Finite.toFinset (finpropInt α g K) ∧
          n ∉ Set.Finite.toFinset (finpropInt α g K') := Finset.mem_sdiff.mp hn
      have hn1 : n ≤ K ∧ α.coeff (g + n) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finpropInt α g K)).mp hn_mem.1
      have hn2 : ¬ (n ≤ K' ∧ α.coeff (g + n) ≠ 0) := by
        intro h
        exact hn_mem.2 ((Set.Finite.mem_toFinset (hs := finpropInt α g K')).mpr h)
      have hn_gt : K' < n := by
        by_contra hle
        push_neg at hle
        exact hn2 ⟨hle, hn1.2⟩
      have hn_ge : K' + 1 ≤ n := hn_gt
      have h1 := hterm_bound (α.coeff (g + n)) n
      have h2 : ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) ≤
          ((Multiplicative.ofAdd (-(K' + 1) : ℤ) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
        rw [WithZero.coe_le_coe]
        exact Multiplicative.ofAdd_le.mpr (by omega)
      exact h1.trans h2
    rw [hnorm_eq]
    have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (∑ n ∈ (Set.Finite.toFinset (finpropInt α g K) \
            Set.Finite.toFinset (finpropInt α g K')),
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + n)))) ≤
        WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(K' + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) :=
      hsm.monotone hval_bound
    rw [htoNN (-(K' + 1))] at h_nnreal_le
    have h_pow_lt : (p : NNReal)^(-((K' : ℤ) + 1)) < ε := by
      have h_pow_eq : (p : NNReal)^(-((K' : ℤ) + 1)) = ((p : NNReal)⁻¹)^((K' : ℤ) + 1) := by
        rw [zpow_neg, ← inv_zpow]
      rw [h_pow_eq]
      have hKN : (N : ℤ) ≤ K' + 1 := by linarith
      have hN_pos : 0 ≤ (K' : ℤ) + 1 := by linarith
      have h_zpow_toNat : ((p : NNReal)⁻¹)^((K' : ℤ) + 1) =
          ((p : NNReal)⁻¹)^((K' + 1).toNat) := by
        rw [← zpow_natCast]
        congr 1
        omega
      rw [h_zpow_toNat]
      have h_le : ((p : NNReal)⁻¹)^((K' + 1).toNat) ≤ ((p : NNReal)⁻¹)^N := by
        apply pow_le_pow_of_le_one hpinv_nn (le_of_lt hpinv_lt)
        omega
      exact h_le.trans_lt hN
    have h_combined : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (∑ n ∈ (Set.Finite.toFinset (finpropInt α g K) \
              Set.Finite.toFinset (finpropInt α g K')),
            (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + n)))) < ε :=
      h_nnreal_le.trans_lt h_pow_lt
    exact_mod_cast h_combined

/--
**Limit of partial sums** (sub-claim of existence). The partial sums of `α` at
coset `g` converge in the complete DVR `ℚᵘⁿ_[p]` to a limit `f_g`.
Uses `intPartial_isCauchy` and `CompleteSpace ℚᵘⁿ_[p]` (which itself is an
admit in `WittVector.lean`, line 76). **Sub-task for next session.**
-/
lemma exists_lim_intPartial (α : LiftedPAdicHahnSeries p) (g : ℚ) :
    ∃ y : ℚᵘⁿ_[p], Filter.Tendsto (intPartial α g) Filter.atTop (nhds y) := by
  -- Cauchy in complete space ⇒ converges.
  -- Strategy: prove `CauchySeq` via `Valued.cauchy_iff` (since the default UniformSpace
  -- on `ℚᵘⁿ_[p]` is the Valued one, not the metric one from `WithAbs.normedField`).
  -- Translate Γ₀ˣ-style Cauchy condition to ε-NNReal-style via `WithZeroMulInt.toNNReal`.
  have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
    WithZeroMulInt.toNNReal_strictMono hp1
  have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
  have hCauchy : CauchySeq (intPartial α g) := by
    rw [show CauchySeq (intPartial α g) = Cauchy (Filter.atTop.map (intPartial α g)) from rfl,
        Valued.cauchy_iff]
    refine ⟨Filter.map_neBot, ?_⟩
    intro γ
    -- Convert γ to ε : NNReal
    set ε : NNReal :=
      WithZeroMulInt.toNNReal (p_ne_zero p) (γ : WithZero (Multiplicative ℤ)) with hε_def
    have hγ_ne : (γ : WithZero (Multiplicative ℤ)) ≠ 0 := γ.ne_zero
    have hε_pos : (0 : NNReal) < ε := by
      rw [hε_def]
      rw [show ((WithZeroMulInt.toNNReal (p_ne_zero p)) (γ : WithZero (Multiplicative ℤ)) =
        if h : (γ : WithZero (Multiplicative ℤ)) = 0 then 0
        else (p : NNReal) ^ ((WithZero.unzero h).toAdd : ℤ)) from rfl]
      simp [hγ_ne]
      exact zpow_pos hp_pos _
    obtain ⟨K₀, hK₀⟩ := intPartial_isCauchy α g ε hε_pos
    -- The set M = `intPartial α g` applied to integers ≥ K₀
    refine ⟨{ a | ∃ K : ℤ, K₀ ≤ K ∧ a = intPartial α g K }, ?_, ?_⟩
    · -- M ∈ Filter.atTop.map (intPartial α g)
      rw [Filter.mem_map]
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop K₀) ?_
      intro K hK
      exact ⟨K, hK, rfl⟩
    · -- For x, y ∈ M, Valued.v (y - x) < γ
      intro x hx y hy
      obtain ⟨K, hK, rfl⟩ := hx
      obtain ⟨K', hK', rfl⟩ := hy
      -- Need: Valued.v (intPartial α g K' - intPartial α g K) < (γ : WithZero (Multiplicative ℤ))
      have h_norm := hK₀ K' K hK' hK
      -- h_norm : ‖intPartial α g K' - intPartial α g K‖ < ε
      -- Convert to valuation bound
      have h_norm_eq :
          ‖intPartial α g K' - intPartial α g K‖ =
            ((WithZeroMulInt.toNNReal (p_ne_zero p)
              (Valued.v (intPartial α g K' - intPartial α g K)) : NNReal) : ℝ) := rfl
      rw [h_norm_eq] at h_norm
      have h_NN :
          (WithZeroMulInt.toNNReal (p_ne_zero p)
            (Valued.v (intPartial α g K' - intPartial α g K)) : NNReal) < ε := by
        exact_mod_cast h_norm
      have h_val_lt :
          Valued.v (intPartial α g K' - intPartial α g K) < (γ : WithZero (Multiplicative ℤ)) := by
        rw [hε_def] at h_NN
        exact hsm.lt_iff_lt.mp h_NN
      exact h_val_lt
  -- Apply `CauchySeq.tendsto_limUnder` (uses `[CompleteSpace ℚᵘⁿ_[p]]`)
  exact ⟨_, hCauchy.tendsto_limUnder⟩

/--
**Per-coset Teichmuller digit decomposition** (sub-claim of existence). For each
`y : ℚᵘⁿ_[p]`, there exist a function `b : ℤ → Fpbar p` and an integer cutoff
`m₀` such that `b k = 0` for `k < m₀` and the partial sums
`intPartial-style sums of [b]·p^·` converge to `y` in `ℚᵘⁿ_[p]`.

Built from Mathlib's
`WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff` after
shifting by `p^{-v(y)}` to land in the integers. **Sub-task for next session.**
-/
lemma exists_teichmuller_digits (y : ℚᵘⁿ_[p]) :
    ∃ (b : ℤ → Fpbar p) (m₀ : ℤ),
      (∀ k : ℤ, k < m₀ → b k = 0) ∧
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m₀ K,
          (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b k)))
        Filter.atTop (nhds y) := by
  -- Apply Mathlib's teichmuller-series existence to `p^{-v(y)} · y ∈ ℤᵘⁿ_[p]`.
  by_cases hy : y = 0
  · -- Case 1: y = 0. Take b ≡ 0, m₀ = 0. Each summand is 0.
    refine ⟨0, 0, fun _ _ => rfl, ?_⟩
    rw [hy]
    have hzero : (fun K : ℤ => ∑ k ∈ Finset.Icc (0 : ℤ) K,
        (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p)
          (teichmuller p ((0 : ℤ → Fpbar p) k))) = fun _ => (0 : QpUn p) := by
      funext K
      apply Finset.sum_eq_zero
      intro k _
      simp
    rw [hzero]
    exact tendsto_const_nhds
  · -- Case 2: y ≠ 0.
    have hv_ne : Valued.v y ≠ 0 := by
      simp [hy]
    -- m' : Multiplicative ℤ from WithZero.unzero
    set m' : Multiplicative ℤ := WithZero.unzero hv_ne with hm'_def
    -- m₀ := -m'.toAdd
    set m₀ : ℤ := -m'.toAdd with hm₀_def
    have hvy_eq : Valued.v y = (m' : WithZero (Multiplicative ℤ)) := by
      rw [hm'_def, WithZero.coe_unzero]
    have hm'_eq : (m' : WithZero (Multiplicative ℤ)) =
        ((Multiplicative.ofAdd (-m₀ : ℤ) : Multiplicative ℤ) : WithZero _) := by
      rw [hm₀_def, neg_neg]
      congr
    -- Pattern G: Valued.v ((p : QpUn p)) = ofAdd(-1)
    have hp_val : Valued.v ((p : QpUn p)) =
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
    -- Valued.v ((p : QpUn p)^n) = ofAdd(-n) for n : ℤ
    have hpn_val : ∀ n : ℤ, Valued.v ((p : QpUn p)^n) =
        ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
      intro n
      have hzpow : Valued.v ((p : QpUn p)^n) = (Valued.v ((p : QpUn p)))^n :=
        map_zpow₀ Valued.v _ _
      rw [hzpow, hp_val, ← WithZero.coe_zpow]
      congr 1
      rw [← ofAdd_zsmul n (-1 : ℤ)]
      congr 1
      ring
    -- z := (p : QpUn p)^(-m₀) * y, Valued.v z = 1
    set z : QpUn p := (p : QpUn p)^(-m₀) * y with hz_def
    have hvz : Valued.v z = 1 := by
      rw [hz_def, Valuation.map_mul, hpn_val (-m₀), hvy_eq, hm'_eq]
      rw [← WithZero.coe_mul]
      rw [show (Multiplicative.ofAdd (-(-m₀) : ℤ) * Multiplicative.ofAdd (-m₀ : ℤ)
            : Multiplicative ℤ) = 1 from by
        rw [← ofAdd_add]
        simp]
      rfl
    have hvz_le : Valued.v z ≤ 1 := hvz.le
    -- Lift z to OQpUn p
    obtain ⟨z', hz'⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (K := QpUn p) hvz_le
    -- Define the Teichmuller digits from z'
    let a : ℕ → Fpbar p := fun n => ((frobeniusEquiv (Fpbar p) p).symm ^ n) (z'.coeff n)
    let b : ℤ → Fpbar p := fun k =>
      if h : 0 ≤ k - m₀ then a (k - m₀).toNat else 0
    refine ⟨b, m₀, ?_, ?_⟩
    · -- ∀ k < m₀, b k = 0
      intro k hk
      have hneg : ¬ (0 ≤ k - m₀) := by linarith
      show (if h : 0 ≤ k - m₀ then a (k - m₀).toNat else 0) = 0
      rw [dif_neg hneg]
    · -- Filter.Tendsto (partial sums) atTop (nhds y)
      have hp_ne : (p : QpUn p) ≠ 0 := by
        rw [show (p : QpUn p) = algebraMap (OQpUn p) (QpUn p) (p : OQpUn p) from by
          push_cast; rfl]
        exact fun h => WittVector.p_nonzero p _
          ((IsFractionRing.injective (OQpUn p) (QpUn p))
            (by simpa using h))
      -- Key norm-like bound: for K ≥ m₀,
      -- Valued.v (y - partial_sum K) ≤ ofAdd(-(K+1))
      have hbound : ∀ K : ℤ, m₀ ≤ K → Valued.v (y -
          ∑ k ∈ Finset.Icc m₀ K,
            (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b k))) ≤
        ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
        intro K hK
        set n : ℕ := (K - m₀).toNat with hn_def
        have hK_eq : K = m₀ + (n : ℤ) := by
          rw [hn_def]; omega
        -- Mathlib's theorem applied to z'
        have hmathlib : (p : OQpUn p)^(n+1) ∣ z' - ∑ i ∈ Finset.Iic n,
            teichmuller p (a i) * (p : OQpUn p)^i :=
          WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff z' n
        obtain ⟨c, hc⟩ := hmathlib
        -- Transport to QpUn p via algebraMap
        have halg := congrArg (algebraMap (OQpUn p) (QpUn p)) hc
        simp only [map_sub, map_sum, map_mul, map_pow] at halg
        rw [hz'] at halg
        -- Introduce p in QpUn p form
        have hp_cast : algebraMap (OQpUn p) (QpUn p) (p : OQpUn p) = (p : QpUn p) := by
          push_cast; rfl
        rw [hp_cast] at halg
        -- halg : z - ∑ i ∈ Iic n, algebraMap (teichmuller p (a i)) * (p : QpUn p)^i =
        --        (p : QpUn p)^(n+1) * algebraMap c
        -- Multiply by (p : QpUn p)^m₀ to get y - partial_sum
        have hy_eq : y = (p : QpUn p)^m₀ * z := by
          rw [hz_def, ← mul_assoc, ← zpow_add₀ hp_ne, add_neg_cancel, zpow_zero, one_mul]
        -- Reindex the partial sum
        have hreindex : ∑ k ∈ Finset.Icc m₀ K,
            (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b k)) =
          (p : QpUn p)^m₀ * ∑ i ∈ Finset.Iic n,
            algebraMap (OQpUn p) (QpUn p) (teichmuller p (a i)) * (p : QpUn p)^i := by
          have hIcc_eq : Finset.Icc m₀ K =
              (Finset.range (n + 1)).map (Nat.castEmbedding.trans <| addLeftEmbedding m₀) := by
            rw [Int.Icc_eq_finset_map]
            congr 1
            have : K + 1 - m₀ = (n : ℤ) + 1 := by rw [hK_eq]; ring
            rw [this]
            simp
          rw [hIcc_eq, Finset.sum_map, ← Nat.range_succ_eq_Iic, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
            addLeftEmbedding_apply]
          have hbi : b (m₀ + (i : ℤ)) = a i := by
            show (if h : 0 ≤ (m₀ + (i : ℤ)) - m₀ then a ((m₀ + (i : ℤ)) - m₀).toNat else 0) = a i
            have h_nn : (0 : ℤ) ≤ (m₀ + (i : ℤ)) - m₀ := by omega
            rw [dif_pos h_nn]
            congr 1
            omega
          rw [hbi, zpow_add₀ hp_ne, zpow_natCast]
          ring
        -- y - partial_sum K = (p : QpUn p)^m₀ * ((p : QpUn p)^(n+1) * algebraMap c)
        have hkey : y - ∑ k ∈ Finset.Icc m₀ K,
            (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b k)) =
          (p : QpUn p)^m₀ * ((p : QpUn p)^(n+1) * algebraMap (OQpUn p) (QpUn p) c) := by
          rw [hreindex, hy_eq, ← mul_sub, halg]
        rw [hkey]
        rw [Valuation.map_mul, Valuation.map_mul, hpn_val m₀]
        rw [show ((p : QpUn p)^(n+1) : QpUn p) = ((p : QpUn p)^((n : ℤ)+1) : QpUn p) from by
          rw [← zpow_natCast (p : QpUn p) (n+1)]; push_cast; rfl]
        rw [hpn_val ((n : ℤ)+1)]
        have h_alg_le : Valued.v (algebraMap (OQpUn p) (QpUn p) c) ≤ 1 :=
          (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation_le_one c
        calc ((Multiplicative.ofAdd (-m₀ : ℤ) : Multiplicative ℤ) : WithZero _) *
            (((Multiplicative.ofAdd (-((n : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) *
              Valued.v (algebraMap (OQpUn p) (QpUn p) c))
            ≤ ((Multiplicative.ofAdd (-m₀ : ℤ) : Multiplicative ℤ) : WithZero _) *
              (((Multiplicative.ofAdd (-((n : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) * 1) :=
              mul_le_mul' (le_refl _) (mul_le_mul' (le_refl _) h_alg_le)
          _ = ((Multiplicative.ofAdd (-m₀ : ℤ) : Multiplicative ℤ) : WithZero _) *
              (((Multiplicative.ofAdd (-((n : ℤ) + 1)) : Multiplicative ℤ) : WithZero _)) := by
              rw [mul_one]
          _ = ((Multiplicative.ofAdd ((-m₀) + (-((n : ℤ) + 1))) : Multiplicative ℤ) : WithZero _) := by
              rw [← WithZero.coe_mul, ← ofAdd_add]
          _ = ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
              congr 2; omega
      -- Step 2: Use this bound to prove Tendsto.
      have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
      have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
      have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
        WithZeroMulInt.toNNReal_strictMono hp1
      have hpinv_lt : (p : NNReal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
      have hpinv_nn : 0 ≤ ((p : NNReal)⁻¹ : NNReal) := zero_le _
      rw [Filter.tendsto_iff_forall_eventually_mem]
      intro U hU
      rw [Valued.mem_nhds] at hU
      obtain ⟨γ, hγ⟩ := hU
      have hγ_ne : (γ : WithZero (Multiplicative ℤ)) ≠ 0 := γ.ne_zero
      set ε : NNReal :=
        WithZeroMulInt.toNNReal (p_ne_zero p) (γ : WithZero (Multiplicative ℤ)) with hε_def
      have hε_pos : (0 : NNReal) < ε := by
        rw [hε_def]
        rw [show ((WithZeroMulInt.toNNReal (p_ne_zero p)) (γ : WithZero (Multiplicative ℤ)) =
          if h : (γ : WithZero (Multiplicative ℤ)) = 0 then 0
          else (p : NNReal) ^ ((WithZero.unzero h).toAdd : ℤ)) from rfl]
        rw [dif_neg hγ_ne]
        exact zpow_pos hp_pos _
      have htendsto : Filter.Tendsto (fun n : ℕ => ((p : NNReal)⁻¹)^n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hpinv_nn hpinv_lt
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ((p : NNReal)⁻¹)^N < ε := by
        have h_eventually : ∀ᶠ n : ℕ in Filter.atTop, ((p : NNReal)⁻¹)^n < ε :=
          htendsto.eventually (eventually_lt_nhds hε_pos)
        exact h_eventually.exists
      rw [Filter.eventually_atTop]
      refine ⟨max m₀ ((N : ℤ) - 1), ?_⟩
      intro K hK
      have hK_ge_m₀ : m₀ ≤ K := le_of_max_le_left hK
      have hK_ge_N : (N : ℤ) - 1 ≤ K := le_of_max_le_right hK
      have hK_plus_1 : (N : ℤ) ≤ K + 1 := by linarith
      apply hγ
      show Valued.v ((∑ k ∈ Finset.Icc m₀ K,
        (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b k))) - y) < γ
      rw [Valuation.map_sub_swap]
      -- h1 : Valued.v (y - partial_sum K) ≤ ofAdd(-(K+1))
      have h1 := hbound K hK_ge_m₀
      have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p)
          (Valued.v (y - ∑ k ∈ Finset.Icc m₀ K,
            (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b k)))) ≤
          WithZeroMulInt.toNNReal (p_ne_zero p)
            (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) :=
        hsm.monotone h1
      have htoNN : WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) =
          (p : NNReal)^(-(K + 1)) := by
        simp [WithZeroMulInt.toNNReal]
      rw [htoNN] at h_nnreal_le
      -- Bound by ((p : NNReal)⁻¹)^N
      have h_pow_le : (p : NNReal)^(-(K + 1)) ≤ ((p : NNReal)⁻¹)^N := by
        rw [show (p : NNReal)^(-(K + 1)) = ((p : NNReal)⁻¹)^((K : ℤ) + 1) from by
          rw [zpow_neg, ← inv_zpow]]
        rw [show ((p : NNReal)⁻¹)^((K : ℤ) + 1) = ((p : NNReal)⁻¹)^((K + 1).toNat) from by
          rw [← zpow_natCast]
          congr 1
          omega]
        apply pow_le_pow_of_le_one hpinv_nn (le_of_lt hpinv_lt)
        omega
      have h_chain : WithZeroMulInt.toNNReal (p_ne_zero p)
          (Valued.v (y - ∑ k ∈ Finset.Icc m₀ K,
            (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b k)))) < ε :=
        (h_nnreal_le.trans h_pow_le).trans_lt hN
      -- Bridge back to valuation-form
      rw [hε_def] at h_chain
      exact hsm.lt_iff_lt.mp h_chain

set_option maxHeartbeats 1000000 in
/--
**Per-coset Teichmuller digit uniqueness** (sub-claim of uniqueness). Two
digit-decompositions `b, b' : ℤ → Fpbar p` of the same element of `ℚᵘⁿ_[p]`
with the same vanishing-below-cutoff property must agree.

Mathlib's `Mathlib.RingTheory.WittVector.TeichmullerSeries` lists this as
**TODO**. The argument: read off the lowest nonzero coefficient using
`teichmuller_mul_pow_coeff_of_ne` plus `teichmuller_mul_pow_coeff`, subtract,
and recurse.
-/
lemma teichmuller_digits_unique (b b' : ℤ → Fpbar p) (m₀ m₀' : ℤ)
    (hb : ∀ k : ℤ, k < m₀ → b k = 0) (hb' : ∀ k : ℤ, k < m₀' → b' k = 0)
    {y : ℚᵘⁿ_[p]}
    (htb : Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m₀ K,
          (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b k)))
        Filter.atTop (nhds y))
    (htb' : Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m₀' K,
          (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b' k)))
        Filter.atTop (nhds y)) :
    ∀ k : ℤ, b k = b' k := by
  -- ==========================================================================
  -- Strategy. Set m := min m₀ m₀'. Both `b, b'` vanish below `m`. Reindex
  -- both `Icc m₀ K`-sums to `Icc m K`-sums (zero on the gap). Define
  -- `c i := b (m + i)` and `c' i := b' (m + i)` (both `ℕ → Fpbar p`).
  -- After multiplying both Tendstos by the constant `(p : QpUn p)^(-m)`, we
  -- get `algebraMap (Spart c N) → z` and `algebraMap (Spart c' N) → z`
  -- where `Spart c N := ∑ i ∈ Iic N, (p : OQpUn p)^i * teichmuller p (c i)`
  -- and `z := (p : QpUn p)^(-m) * y`. Hence
  -- `algebraMap (Spart c N - Spart c' N) → 0` in QpUn p.
  --
  -- For each `i : ℕ`, eventually `Valued.v (algebraMap (Spart c N - Spart c' N))
  -- ≤ ofAdd(-(i+1))`, hence `(p : OQpUn p)^(i+1) ∣ Spart c N - Spart c' N`
  -- (DVR uniformizer characterization, via `IsDiscreteValuationRing.exists_lift_of_le_one`
  -- and injectivity of `algebraMap`).
  --
  -- Inductively, assume `c j = c' j` for all `j < i`. Then
  --   `Spart c N - Spart c' N
  --     = (teichmuller(c i) - teichmuller(c' i)) * p^i + p^(i+1) * rest`
  -- in OQpUn p. Combined with `p^(i+1) ∣ Spart c N - Spart c' N`, get
  -- `p ∣ teichmuller(c i) - teichmuller(c' i)`. Apply
  -- `WittVector.mem_span_p_pow_iff_le_coeff_eq_zero` (n=1) +
  -- `WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero` +
  -- `WittVector.teichmuller_coeff_zero` to extract `c i = c' i`.
  -- Lift back from ℕ to ℤ via the shift `k = m + i`.
  -- ==========================================================================
  -- Step 1. Define the unified cutoff `m`.
  set m : ℤ := min m₀ m₀' with hm_def
  have hm_le_m₀ : m ≤ m₀ := min_le_left _ _
  have hm_le_m₀' : m ≤ m₀' := min_le_right _ _
  have hb_below : ∀ k : ℤ, k < m → b k = 0 := fun k hk => hb k (lt_of_lt_of_le hk hm_le_m₀)
  have hb'_below : ∀ k : ℤ, k < m → b' k = 0 := fun k hk => hb' k (lt_of_lt_of_le hk hm_le_m₀')
  -- Step 2. ℕ-indexed digits.
  let c : ℕ → Fpbar p := fun i => b (m + i)
  let c' : ℕ → Fpbar p := fun i => b' (m + i)
  -- Step 3. Witt-integer partial sum.
  let Spart : (ℕ → Fpbar p) → ℕ → OQpUn p := fun d N =>
    ∑ i ∈ Finset.Iic N, (p : OQpUn p)^i * teichmuller p (d i)
  -- p ≠ 0 in QpUn p (used throughout)
  have hp_ne : (p : QpUn p) ≠ 0 := by
    rw [show (p : QpUn p) = algebraMap (OQpUn p) (QpUn p) (p : OQpUn p) from by
      push_cast; rfl]
    exact fun h => WittVector.p_nonzero p _
      ((IsFractionRing.injective (OQpUn p) (QpUn p))
        (by simpa using h))
  -- Pattern G — `Valued.v ((p : QpUn p)) = ofAdd(-1)` and zpow version.
  have hp_val : Valued.v ((p : QpUn p)) =
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
  have hpn_val : ∀ n : ℤ, Valued.v ((p : QpUn p)^n) =
      ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
    intro n
    have hzpow : Valued.v ((p : QpUn p)^n) = (Valued.v ((p : QpUn p)))^n :=
      map_zpow₀ Valued.v _ _
    rw [hzpow, hp_val, ← WithZero.coe_zpow]
    congr 1
    rw [← ofAdd_zsmul n (-1 : ℤ)]
    congr 1
    ring
  -- Step 4. Replace `Icc m₀ K`-sum with `Icc m K`-sum (extending b by 0).
  have hsum_eq_b : ∀ K : ℤ, ∑ k ∈ Finset.Icc m₀ K,
        (p : QpUn p)^k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b k)) =
      ∑ k ∈ Finset.Icc m K,
        (p : QpUn p)^k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b k)) := by
    intro K
    apply Finset.sum_subset
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      exact ⟨le_trans hm_le_m₀ hk.1, hk.2⟩
    · intro k hk hk_not
      rw [Finset.mem_Icc] at hk
      have hk_lt : k < m₀ := by
        by_contra hge
        push_neg at hge
        exact hk_not (Finset.mem_Icc.mpr ⟨hge, hk.2⟩)
      rw [hb k hk_lt]
      simp
  have hsum_eq_b' : ∀ K : ℤ, ∑ k ∈ Finset.Icc m₀' K,
        (p : QpUn p)^k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b' k)) =
      ∑ k ∈ Finset.Icc m K,
        (p : QpUn p)^k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b' k)) := by
    intro K
    apply Finset.sum_subset
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      exact ⟨le_trans hm_le_m₀' hk.1, hk.2⟩
    · intro k hk hk_not
      rw [Finset.mem_Icc] at hk
      have hk_lt : k < m₀' := by
        by_contra hge
        push_neg at hge
        exact hk_not (Finset.mem_Icc.mpr ⟨hge, hk.2⟩)
      rw [hb' k hk_lt]
      simp
  -- Step 5. Reindex `Icc m (m + N)` to `Iic N`, isolating `(p : QpUn p)^m` factor.
  -- Step 5b. Connect `Icc m (m + N)`-sum to `algebraMap(Spart c N)`.
  have h_to_Spart : ∀ (d : ℕ → Fpbar p) (N : ℕ),
      ∑ i ∈ Finset.Iic N,
        algebraMap (OQpUn p) (QpUn p) (teichmuller p (d i)) * (p : QpUn p)^i =
      algebraMap (OQpUn p) (QpUn p)
        (∑ i ∈ Finset.Iic N, (p : OQpUn p)^i * teichmuller p (d i)) := by
    intro d N
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, map_pow, mul_comm]
    push_cast
    rfl
  -- Step 6. Build the converging ℕ-indexed shifted sequence.
  -- σ N := algebraMap (Spart c N), σ' N := algebraMap (Spart c' N).
  -- Show σ N → z and σ' N → z, where z := (p : QpUn p)^(-m) * y.
  set z : QpUn p := (p : QpUn p)^(-m) * y with hz_def
  have h_natTendsto : ∀ (d : ℕ → Fpbar p),
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m K,
          (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (d (k - m).toNat)))
        Filter.atTop (nhds y) →
      Filter.Tendsto
        (fun N : ℕ => algebraMap (OQpUn p) (QpUn p) (Spart d N))
        Filter.atTop (nhds z) := by
    intro d hd
    -- Multiply by (p : QpUn p)^(-m) on the left
    have h_mul : Filter.Tendsto
        (fun K : ℤ => (p : QpUn p)^(-m) *
          ∑ k ∈ Finset.Icc m K, (p : QpUn p)^k *
            algebraMap (OQpUn p) (QpUn p) (teichmuller p (d (k - m).toNat)))
        Filter.atTop (nhds ((p : QpUn p)^(-m) * y)) := hd.const_mul _
    -- Compose with N ↦ m + N
    have h_compose : Filter.Tendsto (fun N : ℕ => m + (N : ℤ)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_left _ m tendsto_natCast_atTop_atTop
    have h_comp := h_mul.comp h_compose
    -- Rewrite using hreindex
    show Filter.Tendsto (fun N : ℕ => algebraMap (OQpUn p) (QpUn p) (Spart d N)) _ _
    apply h_comp.congr
    intro N
    simp only [Function.comp_apply]
    -- The sum at K = m + N reindexes: argument to teichmuller is d ((m + N - m).toNat) = d N
    -- Let's simplify the sum:
    have h_inner_eq : ∀ d : ℕ → Fpbar p, ∀ N : ℕ,
        ∑ k ∈ Finset.Icc m (m + (N : ℤ)),
          (p : QpUn p)^k * algebraMap (OQpUn p) (QpUn p)
            (teichmuller p (d (k - m).toNat)) =
        (p : QpUn p)^m * ∑ i ∈ Finset.Iic N,
          algebraMap (OQpUn p) (QpUn p) (teichmuller p (d i)) * (p : QpUn p)^i := by
      intros d N
      have hIcc_eq : Finset.Icc m ((m : ℤ) + N) =
          (Finset.range (N + 1)).map (Nat.castEmbedding.trans <| addLeftEmbedding m) := by
        rw [Int.Icc_eq_finset_map]
        congr 1
        have h_simp : (m + (N : ℤ)) + 1 - m = (N : ℤ) + 1 := by ring
        rw [h_simp]
        simp
      rw [hIcc_eq, Finset.sum_map, ← Nat.range_succ_eq_Iic, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
        addLeftEmbedding_apply]
      have h_toNat : ((m + (i : ℤ)) - m).toNat = i := by
        have h_simp_eq : (m + (i : ℤ)) - m = (i : ℤ) := by ring
        rw [h_simp_eq]
        simp
      rw [h_toNat]
      rw [zpow_add₀ hp_ne, zpow_natCast]
      ring
    rw [h_inner_eq d N]
    rw [show (p : QpUn p)^(-m) * ((p : QpUn p)^m * _) =
        ((p : QpUn p)^(-m) * (p : QpUn p)^m) *
        ∑ i ∈ Finset.Iic N,
          algebraMap (OQpUn p) (QpUn p) (teichmuller p (d i)) * (p : QpUn p)^i from by ring]
    rw [show (p : QpUn p)^(-m) * (p : QpUn p)^m = (1 : QpUn p) from by
      rw [← zpow_add₀ hp_ne]; rw [neg_add_cancel]; rw [zpow_zero]]
    rw [one_mul]
    rw [h_to_Spart d N]
  have hcb_to_z : Filter.Tendsto
      (fun N : ℕ => algebraMap (OQpUn p) (QpUn p) (Spart c N))
      Filter.atTop (nhds z) := by
    apply h_natTendsto c
    -- Need: Tendsto (fun K => ∑ k ∈ Icc m K, p^k * algebraMap (teichmuller p (c (k-m).toNat))) atTop (nhds y)
    -- Note c (k-m).toNat = b (m + (k-m).toNat).
    -- For k ≥ m, this equals b k. For k < m, b k = 0.
    -- So this is the original sum, just with different indexing.
    -- The original Tendsto from htb is over Icc m₀ K.
    -- Use Filter.Tendsto.congr' (eventually equal for K ≥ m).
    have h_eventual : ∀ᶠ K : ℤ in Filter.atTop,
        ∑ k ∈ Finset.Icc m K,
          (p : QpUn p)^k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (c (k - m).toNat)) =
        ∑ k ∈ Finset.Icc m₀ K,
          (p : QpUn p)^k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b k)) := by
      filter_upwards [Filter.eventually_ge_atTop m] with K hKm
      have h_inner : ∑ k ∈ Finset.Icc m K,
            (p : QpUn p)^k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (c (k - m).toNat)) =
          ∑ k ∈ Finset.Icc m K,
            (p : QpUn p)^k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Icc] at hk
        have h_toNat_eq : (k - m).toNat = (k - m).toNat := rfl
        have h_c_eq : c (k - m).toNat = b k := by
          show b (m + ((k - m).toNat : ℤ)) = b k
          have hkm : (0 : ℤ) ≤ k - m := by linarith
          rw [Int.toNat_of_nonneg hkm]
          ring_nf
        rw [h_c_eq]
      rw [h_inner, hsum_eq_b K]
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm h_eventual) htb
  have hcb'_to_z : Filter.Tendsto
      (fun N : ℕ => algebraMap (OQpUn p) (QpUn p) (Spart c' N))
      Filter.atTop (nhds z) := by
    apply h_natTendsto c'
    have h_eventual : ∀ᶠ K : ℤ in Filter.atTop,
        ∑ k ∈ Finset.Icc m K,
          (p : QpUn p)^k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (c' (k - m).toNat)) =
        ∑ k ∈ Finset.Icc m₀' K,
          (p : QpUn p)^k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b' k)) := by
      filter_upwards [Filter.eventually_ge_atTop m] with K hKm
      have h_inner : ∑ k ∈ Finset.Icc m K,
            (p : QpUn p)^k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (c' (k - m).toNat)) =
          ∑ k ∈ Finset.Icc m K,
            (p : QpUn p)^k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b' k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Icc] at hk
        have h_c'_eq : c' (k - m).toNat = b' k := by
          show b' (m + ((k - m).toNat : ℤ)) = b' k
          have hkm : (0 : ℤ) ≤ k - m := by linarith
          rw [Int.toNat_of_nonneg hkm]
          ring_nf
        rw [h_c'_eq]
      rw [h_inner, hsum_eq_b' K]
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm h_eventual) htb'
  -- Difference tends to 0.
  have hdiff_tendsto : Filter.Tendsto
      (fun N : ℕ => algebraMap (OQpUn p) (QpUn p) (Spart c N - Spart c' N))
      Filter.atTop (nhds 0) := by
    have h := hcb_to_z.sub hcb'_to_z
    simp only [sub_self] at h
    apply h.congr
    intro N
    rw [map_sub]
  -- Step 7. For each i, find N with `(p : OQpUn p)^(i+1) ∣ Spart c N - Spart c' N`.
  have h_eventual_div : ∀ i : ℕ, ∃ N : ℕ, N ≥ i ∧
      (p : OQpUn p)^(i+1) ∣ (Spart c N - Spart c' N) := by
    intro i
    -- Eventually `Valued.v (algebraMap (Spart c N - Spart c' N)) < ofAdd(-i)`,
    -- which gives `≤ ofAdd(-(i+1))` since values are discrete.
    -- Use Valued.mem_nhds with γ := WithZero.unitsWithZeroEquiv.symm (ofAdd(-i)).
    set γ : (WithZero (Multiplicative ℤ))ˣ :=
      WithZero.unitsWithZeroEquiv.symm (Multiplicative.ofAdd (-(i : ℤ)) : Multiplicative ℤ)
      with hγ_def
    have hγ_coe : (γ : WithZero (Multiplicative ℤ)) =
        ((Multiplicative.ofAdd (-(i : ℤ)) : Multiplicative ℤ) : WithZero _) := rfl
    have h_nhds : {a : QpUn p | Valued.v a < (γ : WithZero (Multiplicative ℤ))} ∈ nhds (0 : QpUn p) := by
      rw [Valued.mem_nhds]
      exact ⟨γ, by intro a ha; simpa using ha⟩
    have h_eventual : ∀ᶠ N : ℕ in Filter.atTop,
        algebraMap (OQpUn p) (QpUn p) (Spart c N - Spart c' N) ∈
          {a : QpUn p | Valued.v a < (γ : WithZero (Multiplicative ℤ))} := hdiff_tendsto h_nhds
    rw [Filter.eventually_atTop] at h_eventual
    obtain ⟨N₀, hN₀⟩ := h_eventual
    refine ⟨max N₀ i, le_max_right _ _, ?_⟩
    set N := max N₀ i
    have hN_ge : N₀ ≤ N := le_max_left _ _
    have h_lt : Valued.v (algebraMap (OQpUn p) (QpUn p) (Spart c N - Spart c' N)) <
        ((Multiplicative.ofAdd (-(i : ℤ)) : Multiplicative ℤ) : WithZero _) := by
      rw [← hγ_coe]; exact hN₀ N hN_ge
    -- From v(...) < ofAdd(-i), deduce v(...) ≤ ofAdd(-(i+1)).
    have h_le : Valued.v (algebraMap (OQpUn p) (QpUn p) (Spart c N - Spart c' N)) ≤
        ((Multiplicative.ofAdd (-((i : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) := by
      rcases eq_or_ne (Valued.v (algebraMap (OQpUn p) (QpUn p) (Spart c N - Spart c' N))) 0 with h0 | h0
      · rw [h0]; exact bot_le
      · rw [← WithZero.coe_unzero h0]
        rw [← WithZero.coe_unzero h0] at h_lt
        rw [WithZero.coe_lt_coe] at h_lt
        rw [WithZero.coe_le_coe]
        rw [show (WithZero.unzero h0) =
            Multiplicative.ofAdd (Multiplicative.toAdd (WithZero.unzero h0)) from rfl] at h_lt ⊢
        rw [Multiplicative.ofAdd_lt] at h_lt
        rw [Multiplicative.ofAdd_le]
        omega
    -- Now use the DVR uniformizer characterization to get divisibility.
    -- Strategy: lift `algebraMap(diff) * (p : QpUn p)^(-(i+1))` back to OQpUn p.
    -- Its valuation is ≤ ofAdd(0) = 1, so it's in OQpUn p.
    set diff : OQpUn p := Spart c N - Spart c' N with hdiff_def
    set q : QpUn p := algebraMap (OQpUn p) (QpUn p) diff * (p : QpUn p)^(-((i : ℤ)+1)) with hq_def
    have hq_val_le_one : Valued.v q ≤ 1 := by
      rw [hq_def, Valuation.map_mul, hpn_val (-((i : ℤ)+1))]
      rw [show (-(-((i : ℤ)+1))) = (i : ℤ)+1 from by ring]
      have h_prod : Valued.v (algebraMap (OQpUn p) (QpUn p) diff) *
          ((Multiplicative.ofAdd ((i : ℤ)+1) : Multiplicative ℤ) : WithZero _) ≤
          ((Multiplicative.ofAdd (-((i : ℤ)+1)) : Multiplicative ℤ) : WithZero _) *
          ((Multiplicative.ofAdd ((i : ℤ)+1) : Multiplicative ℤ) : WithZero _) :=
        mul_le_mul_right' h_le _
      have h_one : ((Multiplicative.ofAdd (-((i : ℤ)+1)) : Multiplicative ℤ) : WithZero _) *
          ((Multiplicative.ofAdd ((i : ℤ)+1) : Multiplicative ℤ) : WithZero _) =
          (1 : WithZero (Multiplicative ℤ)) := by
        rw [← WithZero.coe_mul]
        rw [show (Multiplicative.ofAdd (-((i : ℤ)+1)) * Multiplicative.ofAdd ((i : ℤ)+1)
              : Multiplicative ℤ) = 1 from by
          rw [← ofAdd_add]; rw [neg_add_cancel]; rfl]
        rfl
      rw [h_one] at h_prod
      exact h_prod
    obtain ⟨q', hq'⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (K := QpUn p) hq_val_le_one
    -- q' lifts q. Now show diff = (p : OQpUn p)^(i+1) * q'.
    have h_eq_QpUn : algebraMap (OQpUn p) (QpUn p) diff =
        (p : QpUn p)^((i : ℤ)+1) * algebraMap (OQpUn p) (QpUn p) q' := by
      rw [hq']; rw [hq_def]
      rw [show (p : QpUn p)^((i : ℤ)+1) *
          (algebraMap (OQpUn p) (QpUn p) diff * (p : QpUn p)^(-((i : ℤ)+1))) =
          algebraMap (OQpUn p) (QpUn p) diff *
          ((p : QpUn p)^((i : ℤ)+1) * (p : QpUn p)^(-((i : ℤ)+1))) from by ring]
      rw [show (p : QpUn p)^((i : ℤ)+1) * (p : QpUn p)^(-((i : ℤ)+1)) = 1 from by
        rw [← zpow_add₀ hp_ne]; rw [add_neg_cancel]; rw [zpow_zero]]
      rw [mul_one]
    -- Convert (p : QpUn p)^((i:ℤ)+1) to a coercion of (p : OQpUn p)^(i+1).
    have h_pow_alg : (p : QpUn p)^((i : ℤ)+1) =
        algebraMap (OQpUn p) (QpUn p) ((p : OQpUn p)^(i+1)) := by
      rw [show ((i : ℤ)+1) = ((i+1 : ℕ) : ℤ) from by push_cast; ring]
      rw [zpow_natCast, map_pow]
      push_cast
      rfl
    rw [h_pow_alg, ← map_mul] at h_eq_QpUn
    have h_eq_OQpUn : diff = (p : OQpUn p)^(i+1) * q' :=
      IsFractionRing.injective (OQpUn p) (QpUn p) h_eq_QpUn
    exact ⟨q', h_eq_OQpUn⟩
  -- Step 8. Inductively prove c i = c' i for all i : ℕ.
  -- Helper: for j ≤ i with c k = c' k for k < i, expand the difference.
  have h_induction : ∀ i : ℕ, c i = c' i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      have h_ih : ∀ j < i, c j = c' j := fun j hj => ih j hj
      -- Get N ≥ i with (p : OQpUn p)^(i+1) ∣ Spart c N - Spart c' N.
      obtain ⟨N, hNi, hN_dvd⟩ := h_eventual_div i
      -- Decompose Spart c N - Spart c' N.
      -- Each summand: (p : OQpUn p)^k * teichmuller p (c k) - (p : OQpUn p)^k * teichmuller p (c' k)
      --             = (p : OQpUn p)^k * (teichmuller p (c k) - teichmuller p (c' k))
      have h_diff_expand : Spart c N - Spart c' N =
          ∑ k ∈ Finset.Iic N, (p : OQpUn p)^k *
            (teichmuller p (c k) - teichmuller p (c' k)) := by
        show (∑ k ∈ Finset.Iic N, (p : OQpUn p)^k * teichmuller p (c k)) -
              (∑ k ∈ Finset.Iic N, (p : OQpUn p)^k * teichmuller p (c' k)) = _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      -- Use the IH to drop the first i terms (they vanish).
      have h_drop : Spart c N - Spart c' N =
          ∑ k ∈ Finset.Iic N \ Finset.range i, (p : OQpUn p)^k *
            (teichmuller p (c k) - teichmuller p (c' k)) := by
        rw [h_diff_expand]
        rw [show ∑ k ∈ Finset.Iic N, (p : OQpUn p)^k *
              (teichmuller p (c k) - teichmuller p (c' k)) =
            (∑ k ∈ Finset.Iic N ∩ Finset.range i, (p : OQpUn p)^k *
              (teichmuller p (c k) - teichmuller p (c' k))) +
            (∑ k ∈ Finset.Iic N \ Finset.range i, (p : OQpUn p)^k *
              (teichmuller p (c k) - teichmuller p (c' k))) from
            (Finset.sum_inter_add_sum_diff (Finset.Iic N) (Finset.range i) _).symm]
        have h_zero : ∑ k ∈ Finset.Iic N ∩ Finset.range i,
            (p : OQpUn p)^k * (teichmuller p (c k) - teichmuller p (c' k)) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          rw [Finset.mem_inter, Finset.mem_range] at hk
          rw [h_ih k hk.2]
          ring
        rw [h_zero, zero_add]
      -- Reindex: Iic N \ range i = Icc i N (since i ≤ N).
      have h_reindex_set : Finset.Iic N \ Finset.range i = Finset.Icc i N := by
        ext k
        simp only [Finset.mem_sdiff, Finset.mem_Iic, Finset.mem_range,
          Finset.mem_Icc, not_lt]
        tauto
      rw [h_reindex_set] at h_drop
      -- Reindex Icc i N to range (N - i + 1) shifted by i: k = i + j.
      have h_reindex_full : ∑ k ∈ Finset.Icc i N, (p : OQpUn p)^k *
            (teichmuller p (c k) - teichmuller p (c' k)) =
          (p : OQpUn p)^i * ∑ j ∈ Finset.range (N - i + 1), (p : OQpUn p)^j *
            (teichmuller p (c (i + j)) - teichmuller p (c' (i + j))) := by
        rw [show Finset.Icc i N =
            (Finset.range (N - i + 1)).map ⟨fun j => i + j, by
              intros a b h; simp only at h; omega⟩ from ?_]
        · rw [Finset.sum_map, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [Function.Embedding.coeFn_mk]
          rw [show (p : OQpUn p)^(i + j) = (p : OQpUn p)^i * (p : OQpUn p)^j from pow_add _ _ _]
          ring
        · ext k
          simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range,
            Function.Embedding.coeFn_mk]
          constructor
          · intro ⟨hk1, hk2⟩
            refine ⟨k - i, ?_, ?_⟩
            · omega
            · omega
          · rintro ⟨j, hj, rfl⟩
            constructor
            · omega
            · omega
      -- Now extract p^i factor.
      have h_factored : Spart c N - Spart c' N = (p : OQpUn p)^i *
          ∑ j ∈ Finset.range (N - i + 1), (p : OQpUn p)^j *
            (teichmuller p (c (i + j)) - teichmuller p (c' (i + j))) := by
        rw [h_drop, h_reindex_full]
      -- From divisibility p^(i+1) ∣ Spart c N - Spart c' N = p^i * X, deduce p ∣ X.
      obtain ⟨q', hq'⟩ := hN_dvd
      have h_eq : (p : OQpUn p)^i *
          ∑ j ∈ Finset.range (N - i + 1), (p : OQpUn p)^j *
            (teichmuller p (c (i + j)) - teichmuller p (c' (i + j))) =
          (p : OQpUn p)^(i+1) * q' := by
        rw [← h_factored]; exact hq'
      have h_p_pow_succ : (p : OQpUn p)^(i+1) = (p : OQpUn p)^i * (p : OQpUn p) := by
        rw [pow_succ]
      rw [h_p_pow_succ, mul_assoc] at h_eq
      have hpi_ne : (p : OQpUn p)^i ≠ 0 := by
        apply pow_ne_zero
        exact WittVector.p_nonzero p _
      have h_X_eq : ∑ j ∈ Finset.range (N - i + 1), (p : OQpUn p)^j *
            (teichmuller p (c (i + j)) - teichmuller p (c' (i + j))) =
          (p : OQpUn p) * q' :=
        mul_left_cancel₀ hpi_ne h_eq
      -- Split the X sum into j=0 term + p * (rest).
      have h_split : ∑ j ∈ Finset.range (N - i + 1), (p : OQpUn p)^j *
            (teichmuller p (c (i + j)) - teichmuller p (c' (i + j))) =
          (teichmuller p (c i) - teichmuller p (c' i)) +
          (p : OQpUn p) * ∑ j ∈ Finset.range (N - i), (p : OQpUn p)^j *
            (teichmuller p (c (i + 1 + j)) - teichmuller p (c' (i + 1 + j))) := by
        rw [Finset.sum_range_succ', add_comm]
        simp only [pow_zero, one_mul, Nat.add_zero]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [show i + (j + 1) = i + 1 + j from by ring]
        rw [show (p : OQpUn p)^(j + 1) = (p : OQpUn p) * (p : OQpUn p)^j from by
          rw [pow_succ]; ring]
        ring
      -- So `(t(c i) - t(c' i)) + p * Y = p * q'`, hence `p ∣ t(c i) - t(c' i)`.
      rw [h_split] at h_X_eq
      have h_p_div : (p : OQpUn p) ∣ teichmuller p (c i) - teichmuller p (c' i) := by
        refine ⟨q' -
            ∑ j ∈ Finset.range (N - i), (p : OQpUn p)^j *
              (teichmuller p (c (i + 1 + j)) - teichmuller p (c' (i + 1 + j))), ?_⟩
        linear_combination h_X_eq
      -- Use mem_span_p_pow_iff_le_coeff_eq_zero (with n = 1)
      have h_in_span : teichmuller p (c i) - teichmuller p (c' i) ∈
          Ideal.span {(p : OQpUn p)^1} := by
        rw [pow_one]
        rwa [Ideal.mem_span_singleton]
      rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero] at h_in_span
      -- h_in_span : ∀ m < 1, (teichmuller(c i) - teichmuller(c' i)).coeff m = 0
      have h_coeff_zero : (teichmuller p (c i) - teichmuller p (c' i)).coeff 0 = 0 :=
        h_in_span 0 (by omega)
      -- Use `le_coeff_eq_iff_le_sub_coeff_eq_zero` to translate:
      -- (teichmuller(c i) - teichmuller(c' i)).coeff 0 = 0
      --   ↔ (teichmuller(c i)).coeff 0 = (teichmuller(c' i)).coeff 0
      have h_coeffs_eq : ∀ j < 1, (teichmuller p (c i)).coeff j = (teichmuller p (c' i)).coeff j := by
        rw [WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero]
        intro j hj
        interval_cases j
        exact h_coeff_zero
      have h_at_zero := h_coeffs_eq 0 (by omega)
      rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at h_at_zero
      exact h_at_zero
  -- Step 9. Lift back to ℤ.
  intro k
  by_cases hk : k < m
  · rw [hb_below k hk, hb'_below k hk]
  · push_neg at hk
    have hk_eq : k = m + ((k - m).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (by linarith)]
      ring
    have h_c_eq : c (k - m).toNat = b k := by
      show b (m + ((k - m).toNat : ℤ)) = b k
      rw [← hk_eq]
    have h_c'_eq : c' (k - m).toNat = b' k := by
      show b' (m + ((k - m).toNat : ℤ)) = b' k
      rw [← hk_eq]
    rw [← h_c_eq, ← h_c'_eq]
    exact h_induction (k - m).toNat

end existsCanonicalExpansionAux

set_option maxHeartbeats 4000000 in
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
  classical
  -- ============================================================
  -- SETUP: hp_ne, hp_val, hpn_val
  -- ============================================================
  have hp_ne : (p : QpUn p) ≠ 0 := by
    rw [show (p : QpUn p) = algebraMap (OQpUn p) (QpUn p) (p : OQpUn p) from by
      push_cast; rfl]
    exact fun h_zero => WittVector.p_nonzero p _
      ((IsFractionRing.injective (OQpUn p) (QpUn p))
        (by simpa using h_zero))
  have hp_val : Valued.v ((p : QpUn p)) =
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
  have hpn_val : ∀ n : ℤ, Valued.v ((p : QpUn p)^n) =
      ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
    intro n
    have hzpow : Valued.v ((p : QpUn p)^n) = (Valued.v ((p : QpUn p)))^n :=
      map_zpow₀ Valued.v _ _
    rw [hzpow, hp_val, ← WithZero.coe_zpow]
    congr 1
    rw [← ofAdd_zsmul n (-1 : ℤ)]
    congr 1
    ring
  have hp_term_val : ∀ (a : Fpbar p) (n : ℤ), a ≠ 0 →
      Valued.v ((p : QpUn p)^n * algebraMap (OQpUn p) (QpUn p) (teichmuller p a)) =
        ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
    intro a n ha
    rw [Valuation.map_mul, hpn_val n]
    -- teichmuller p a is a unit in OQpUn p when a ≠ 0
    have h_a_unit : IsUnit a := isUnit_iff_ne_zero.mpr ha
    have h_teich_unit : IsUnit (teichmuller p a) := h_a_unit.map (teichmuller p)
    -- For a unit u in OQpUn p, Valued.v(algMap u) = 1
    have h_val_one : Valued.v (algebraMap (OQpUn p) (QpUn p) (teichmuller p a)) = 1 := by
      rcases h_teich_unit with ⟨u, hu⟩
      rw [← hu]
      have h1 : Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) ≤ 1 :=
        (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation_le_one u.val
      have h2 : Valued.v (algebraMap (OQpUn p) (QpUn p) u.inv) ≤ 1 :=
        (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation_le_one u.inv
      have h3 : Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) *
                Valued.v (algebraMap (OQpUn p) (QpUn p) u.inv) = 1 := by
        rw [← Valuation.map_mul, ← map_mul]
        rw [u.val_inv]
        simp
      by_contra h_ne_one
      have h1_lt : Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) < 1 :=
        lt_of_le_of_ne h1 h_ne_one
      have h_lt : Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) *
                Valued.v (algebraMap (OQpUn p) (QpUn p) u.inv) < 1 := by
        calc Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) *
                Valued.v (algebraMap (OQpUn p) (QpUn p) u.inv) ≤
            Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) * 1 := by
              apply mul_le_mul' (le_refl _) h2
          _ = Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) := mul_one _
          _ < 1 := h1_lt
      rw [h3] at h_lt
      exact lt_irrefl _ h_lt
    rw [h_val_one, mul_one]
  -- ============================================================
  -- Per-γ data: f γ, b γ, m_b γ
  -- ============================================================
  set f : ℚ → QpUn p := fun γ =>
    (existsCanonicalExpansionAux.exists_lim_intPartial α γ).choose with hf_def
  have hf_spec : ∀ γ, Filter.Tendsto (intPartial α γ) Filter.atTop (nhds (f γ)) :=
    fun γ => (existsCanonicalExpansionAux.exists_lim_intPartial α γ).choose_spec
  set b : ℚ → ℤ → Fpbar p := fun γ =>
    (existsCanonicalExpansionAux.exists_teichmuller_digits (f γ)).choose with hb_def
  set m_b : ℚ → ℤ := fun γ =>
    (existsCanonicalExpansionAux.exists_teichmuller_digits (f γ)).choose_spec.choose with hmb_def
  have hb_spec : ∀ γ : ℚ,
      (∀ k : ℤ, k < m_b γ → b γ k = 0) ∧
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc (m_b γ) K,
          (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b γ k)))
        Filter.atTop (nhds (f γ)) := fun γ =>
    (existsCanonicalExpansionAux.exists_teichmuller_digits (f γ)).choose_spec.choose_spec
  have hb_vanish : ∀ γ k, k < m_b γ → b γ k = 0 := fun γ => (hb_spec γ).1
  have hb_tendsto : ∀ γ, Filter.Tendsto
      (fun K : ℤ => ∑ k ∈ Finset.Icc (m_b γ) K,
        (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b γ k)))
      Filter.atTop (nhds (f γ)) := fun γ => (hb_spec γ).2
  -- ============================================================
  -- Key claim: ∀ γ k, b γ k ≠ 0 → ∃ n_α ≤ k with α.coeff (γ + n_α) ≠ 0.
  -- Proof via strict ultrametric.
  -- ============================================================
  have h_key : ∀ γ : ℚ, ∀ k : ℤ, b γ k ≠ 0 →
      ∃ n_α : ℤ, n_α ≤ k ∧ α.coeff (γ + n_α) ≠ 0 := by
    intro γ k hbk
    -- Step 0: Define k_min := smallest j ≥ m_b γ with b γ j ≠ 0.
    have h_k_in : k ∈ {j : ℤ | m_b γ ≤ j ∧ b γ j ≠ 0} := by
      refine ⟨?_, hbk⟩
      by_contra h_nge
      push_neg at h_nge
      exact hbk (hb_vanish γ k h_nge)
    have hbset_ne : ({j : ℤ | m_b γ ≤ j ∧ b γ j ≠ 0}).Nonempty := ⟨k, h_k_in⟩
    have hbset_bdd : BddBelow {j : ℤ | m_b γ ≤ j ∧ b γ j ≠ 0} := ⟨m_b γ, fun j hj => hj.1⟩
    obtain ⟨k_min, hk_min_mem, hk_min_le⟩ := Int.exists_least_of_bdd hbset_bdd hbset_ne
    -- Step 1: For K ≥ k_min, Valued.v(Icc m_b γ K sum) = ofAdd(-k_min) by strict ultrametric.
    have h_sum_eq : ∀ K : ℤ, k_min ≤ K → Valued.v (∑ j ∈ Finset.Icc (m_b γ) K,
          (p : QpUn p) ^ j * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b γ j))) =
        ((Multiplicative.ofAdd (-k_min : ℤ) : Multiplicative ℤ) : WithZero _) := by
      intro K hK
      have h_in : k_min ∈ Finset.Icc (m_b γ) K := Finset.mem_Icc.mpr ⟨hk_min_mem.1, hK⟩
      rw [show Finset.Icc (m_b γ) K = insert k_min ((Finset.Icc (m_b γ) K).erase k_min) from
        (Finset.insert_erase h_in).symm]
      rw [Finset.sum_insert (Finset.notMem_erase _ _)]
      rw [Valuation.map_add_eq_of_lt_left]
      · exact hp_term_val (b γ k_min) k_min hk_min_mem.2
      · -- v(rest) < ofAdd(-k_min)
        have h_bound : Valued.v (∑ j ∈ (Finset.Icc (m_b γ) K).erase k_min,
              (p : QpUn p) ^ j * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b γ j))) ≤
            ((Multiplicative.ofAdd (-(k_min + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
          apply Valuation.map_sum_le
          intro j hj_mem
          rw [Finset.mem_erase, Finset.mem_Icc] at hj_mem
          by_cases h_zero : b γ j = 0
          · rw [h_zero, WittVector.teichmuller_zero, map_zero, mul_zero]
            rw [Valuation.map_zero]
            exact bot_le
          · have hj_in : j ∈ {i : ℤ | m_b γ ≤ i ∧ b γ i ≠ 0} := ⟨hj_mem.2.1, h_zero⟩
            have hj_ge : k_min ≤ j := hk_min_le j hj_in
            have hj_gt : k_min < j := lt_of_le_of_ne hj_ge (Ne.symm hj_mem.1)
            rw [hp_term_val (b γ j) j h_zero]
            rw [WithZero.coe_le_coe]
            exact Multiplicative.ofAdd_le.mpr (by omega)
        apply lt_of_le_of_lt h_bound
        rw [hp_term_val (b γ k_min) k_min hk_min_mem.2]
        rw [WithZero.coe_lt_coe]
        exact Multiplicative.ofAdd_lt.mpr (by omega)
    -- Step 2: We need to derive contradictions / equations using Tendsto.
    -- Helper: Tendsto + eventually constant valuation ⇒ Valued.v(limit) constraint.
    -- Specifically, if y ≠ 0 then Valued.v y equals the constant.
    -- If y = 0 and the constant is nonzero, contradiction.
    -- Apply with y = f γ.
    by_cases h_fγ : f γ = 0
    · -- f γ = 0 case: contradiction since Tendsto sum → 0 but eventually Valued.v(sum K) ≠ 0.
      exfalso
      -- Build a neighborhood of 0 that excludes the eventually-equal sum value.
      set γ_unit : (WithZero (Multiplicative ℤ))ˣ :=
        WithZero.unitsWithZeroEquiv.symm (Multiplicative.ofAdd (-k_min : ℤ) : Multiplicative ℤ)
        with hγ_unit
      have hγ_unit_eq : (γ_unit : WithZero (Multiplicative ℤ)) =
          ((Multiplicative.ofAdd (-k_min : ℤ) : Multiplicative ℤ) : WithZero _) := rfl
      have h_nhds :
          {x : QpUn p | Valued.v x < (γ_unit : WithZero (Multiplicative ℤ))} ∈ nhds (0 : QpUn p) := by
        rw [Valued.mem_nhds]
        exact ⟨γ_unit, fun x ha => by simpa using ha⟩
      have h_evtl_close : ∀ᶠ K : ℤ in Filter.atTop,
          Valued.v (∑ j ∈ Finset.Icc (m_b γ) K,
              (p : QpUn p) ^ j * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b γ j))) <
            ((Multiplicative.ofAdd (-k_min : ℤ) : Multiplicative ℤ) : WithZero _) := by
        have h_tend := hb_tendsto γ
        rw [h_fγ] at h_tend
        have := h_tend h_nhds
        rw [hγ_unit_eq] at this
        exact this
      have h_evtl_K_ge : ∀ᶠ K : ℤ in Filter.atTop, k_min ≤ K := Filter.eventually_ge_atTop k_min
      obtain ⟨K, hKge, hKclose⟩ := (h_evtl_K_ge.and h_evtl_close).exists
      rw [h_sum_eq K hKge] at hKclose
      exact lt_irrefl _ hKclose
    · -- f γ ≠ 0 case.
      -- Show Valued.v(f γ) = ofAdd(-k_min) using ultrametric stability.
      have h_v_fγ_eq : Valued.v (f γ) =
          ((Multiplicative.ofAdd (-k_min : ℤ) : Multiplicative ℤ) : WithZero _) := by
        -- Use that eventually Valued.v(sum K) = Valued.v(f γ) (valuation stability)
        -- AND eventually Valued.v(sum K) = ofAdd(-k_min) (h_sum_eq).
        -- Combine to get Valued.v(f γ) = ofAdd(-k_min).
        have h_v_fγ_ne : Valued.v (f γ) ≠ 0 := by rwa [Valuation.ne_zero_iff]
        set γ_unit_y : (WithZero (Multiplicative ℤ))ˣ :=
          WithZero.unitsWithZeroEquiv.symm ((Valued.v (f γ)).unzero h_v_fγ_ne) with hγ_unit_y
        have hγ_unit_y_eq : (γ_unit_y : WithZero (Multiplicative ℤ)) = Valued.v (f γ) := by
          simp [γ_unit_y, WithZero.coe_unzero]
        have h_nhds_y :
            {x : QpUn p | Valued.v (x - f γ) < (γ_unit_y : WithZero (Multiplicative ℤ))} ∈
              nhds (f γ) := by
          rw [Valued.mem_nhds]
          exact ⟨γ_unit_y, fun x ha => by simpa using ha⟩
        have h_evtl_stable : ∀ᶠ K : ℤ in Filter.atTop,
            Valued.v ((∑ j ∈ Finset.Icc (m_b γ) K,
                (p : QpUn p) ^ j *
                  algebraMap (OQpUn p) (QpUn p) (teichmuller p (b γ j))) - f γ) <
              Valued.v (f γ) := by
          have := hb_tendsto γ h_nhds_y
          rw [hγ_unit_y_eq] at this
          exact this
        have h_evtl_K_ge : ∀ᶠ K : ℤ in Filter.atTop, k_min ≤ K :=
          Filter.eventually_ge_atTop k_min
        obtain ⟨K, hKge, hKstable⟩ := (h_evtl_K_ge.and h_evtl_stable).exists
        -- Now: Valued.v(sum K - f γ) < Valued.v(f γ).
        -- f γ = sum K - (sum K - f γ).
        -- By ultrametric strict: Valued.v(f γ) = Valued.v(sum K).
        have h_valeq : Valued.v (∑ j ∈ Finset.Icc (m_b γ) K,
              (p : QpUn p) ^ j *
                algebraMap (OQpUn p) (QpUn p) (teichmuller p (b γ j))) =
              Valued.v (f γ) := by
          rw [show (∑ j ∈ Finset.Icc (m_b γ) K,
                (p : QpUn p) ^ j *
                  algebraMap (OQpUn p) (QpUn p) (teichmuller p (b γ j))) =
              f γ + ((∑ j ∈ Finset.Icc (m_b γ) K,
                (p : QpUn p) ^ j *
                  algebraMap (OQpUn p) (QpUn p) (teichmuller p (b γ j))) - f γ) from by ring]
          rw [Valuation.map_add_eq_of_lt_left]
          exact hKstable
        rw [← h_valeq, h_sum_eq K hKge]
      -- Slice nonempty
      set slice : Set ℤ := {n : ℤ | α.coeff (γ + n) ≠ 0} with hslice_def
      have h_slice_ne : slice.Nonempty := by
        -- f γ ≠ 0 ⟹ intPartial α γ has some nonzero K, which has some nonzero term.
        -- intPartial α γ K = 0 iff slice ∩ ≤K is empty.
        -- If slice is empty then intPartial α γ ≡ 0, hence f γ = 0. Contradiction.
        by_contra h_sl_e
        apply h_fγ
        have h_intP_zero : ∀ K : ℤ, intPartial α γ K = 0 := by
          intro K
          simp only [intPartial]
          apply Finset.sum_eq_zero
          intro n _
          have hn_mem : n.1 ≤ K ∧ α.coeff (γ + n.1) ≠ 0 :=
            (Set.Finite.mem_toFinset (hs := finpropInt α γ K)).mp n.2
          exfalso
          apply h_sl_e
          exact ⟨n.1, hn_mem.2⟩
        have h := hf_spec γ
        rw [show (intPartial α γ) = (fun _ => (0 : QpUn p)) from funext h_intP_zero] at h
        exact (tendsto_nhds_unique h tendsto_const_nhds)
      have hslice_bdd : BddBelow slice := by
        by_cases hsupp : α.support.Nonempty
        · refine ⟨⌈(α.isWF_support.min hsupp - γ : ℚ)⌉, ?_⟩
          intro n hn
          have hn_mem : (γ + (n : ℚ)) ∈ α.support := hn
          have hmin_le : α.isWF_support.min hsupp ≤ γ + n :=
            α.isWF_support.min_le hsupp hn_mem
          have : (α.isWF_support.min hsupp - γ : ℚ) ≤ (n : ℚ) := by linarith
          exact Int.ceil_le.mpr this
        · exfalso
          obtain ⟨n, hn⟩ := h_slice_ne
          apply hsupp
          exact ⟨γ + n, hn⟩
      obtain ⟨m, hm_mem, hm_min⟩ := Int.exists_least_of_bdd hslice_bdd h_slice_ne
      refine ⟨m, ?_, hm_mem⟩
      -- Need m ≤ k. Show via Valued.v(f γ) ≤ ofAdd(-m).
      have h_v_fγ_le : Valued.v (f γ) ≤
          ((Multiplicative.ofAdd (-m : ℤ) : Multiplicative ℤ) : WithZero _) := by
        -- Argue: eventually Valued.v(intPartial K) ≤ ofAdd(-m).
        -- Combined with eventually Valued.v(intPartial K) = Valued.v(f γ) (stability):
        -- Valued.v(f γ) ≤ ofAdd(-m).
        have h_intP_α_bound : ∀ K : ℤ, m ≤ K →
            Valued.v (intPartial α γ K) ≤
              ((Multiplicative.ofAdd (-m : ℤ) : Multiplicative ℤ) : WithZero _) := by
          intro K hK
          simp only [intPartial]
          rw [show (∑ n : Set.Finite.toFinset (finpropInt α γ K),
                (p : QpUn p) ^ n.1 *
                  algebraMap (OQpUn p) (QpUn p) (α.coeff (γ + n))) =
              ∑ n ∈ Set.Finite.toFinset (finpropInt α γ K),
                (p : QpUn p) ^ n *
                  algebraMap (OQpUn p) (QpUn p) (α.coeff (γ + n)) from
              Finset.sum_attach (s := Set.Finite.toFinset (finpropInt α γ K))
                (f := fun n : ℤ => (p : QpUn p) ^ n *
                  algebraMap (OQpUn p) (QpUn p) (α.coeff (γ + n)))]
          apply Valuation.map_sum_le
          intro n hn
          have hn_mem : n ≤ K ∧ α.coeff (γ + n) ≠ 0 :=
            (Set.Finite.mem_toFinset (hs := finpropInt α γ K)).mp hn
          have hn_in_slice : n ∈ slice := hn_mem.2
          have hm_le_n : m ≤ n := hm_min n hn_in_slice
          rw [Valuation.map_mul, hpn_val n]
          have h_alg_le : Valued.v (algebraMap (OQpUn p) (QpUn p) (α.coeff (γ + n))) ≤ 1 :=
            (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation_le_one (α.coeff (γ + n))
          calc ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) *
                  Valued.v (algebraMap (OQpUn p) (QpUn p) (α.coeff (γ + n)))
              ≤ ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) * 1 :=
                mul_le_mul' (le_refl _) h_alg_le
            _ = ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := mul_one _
            _ ≤ ((Multiplicative.ofAdd (-m : ℤ) : Multiplicative ℤ) : WithZero _) := by
                rw [WithZero.coe_le_coe]
                exact Multiplicative.ofAdd_le.mpr (by omega)
        -- Use ultrametric stability to get Valued.v(f γ) ≤ ofAdd(-m).
        have h_v_fγ_ne : Valued.v (f γ) ≠ 0 := by rwa [Valuation.ne_zero_iff]
        set γ_unit_y : (WithZero (Multiplicative ℤ))ˣ :=
          WithZero.unitsWithZeroEquiv.symm ((Valued.v (f γ)).unzero h_v_fγ_ne) with hγ_unit_y
        have hγ_unit_y_eq : (γ_unit_y : WithZero (Multiplicative ℤ)) = Valued.v (f γ) := by
          simp [γ_unit_y, WithZero.coe_unzero]
        have h_nhds_y :
            {x : QpUn p | Valued.v (x - f γ) < (γ_unit_y : WithZero (Multiplicative ℤ))} ∈
              nhds (f γ) := by
          rw [Valued.mem_nhds]
          exact ⟨γ_unit_y, fun x ha => by simpa using ha⟩
        have h_evtl_stable : ∀ᶠ K : ℤ in Filter.atTop,
            Valued.v (intPartial α γ K - f γ) < Valued.v (f γ) := by
          have := hf_spec γ h_nhds_y
          rw [hγ_unit_y_eq] at this
          exact this
        have h_evtl_K_ge : ∀ᶠ K : ℤ in Filter.atTop, m ≤ K := Filter.eventually_ge_atTop m
        obtain ⟨K, hKge, hKstable⟩ := (h_evtl_K_ge.and h_evtl_stable).exists
        have h_intP_le := h_intP_α_bound K hKge
        have h_v_intP_eq_fγ : Valued.v (intPartial α γ K) = Valued.v (f γ) := by
          rw [show intPartial α γ K =
              f γ + (intPartial α γ K - f γ) from by ring]
          rw [Valuation.map_add_eq_of_lt_left]
          exact hKstable
        rw [h_v_intP_eq_fγ] at h_intP_le
        exact h_intP_le
      rw [h_v_fγ_eq] at h_v_fγ_le
      rw [WithZero.coe_le_coe] at h_v_fγ_le
      have hk_min_ge_m : m ≤ k_min := by
        have := Multiplicative.ofAdd_le.mp h_v_fγ_le
        omega
      have hk_min_le_k : k_min ≤ k := hk_min_le k h_k_in
      omega
  -- ============================================================
  -- DEFINE s := fun q => b (Int.fract q) ⌊q⌋
  -- ============================================================
  set s : ℚ → Fpbar p := fun q => b (Int.fract q) ⌊q⌋ with hs_def
  -- ============================================================
  -- Show support s ⊆ support α + Set.range (Nat.cast : ℕ → ℚ)
  -- ============================================================
  open scoped Pointwise in
  have hsupp_sub : Function.support s ⊆ α.support + Set.range ((↑) : ℕ → ℚ) := by
    intro q hq
    simp only [hs_def, Function.mem_support] at hq
    -- hq : b (Int.fract q) ⌊q⌋ ≠ 0
    obtain ⟨n_α, hn_α_le, hn_α_ne⟩ := h_key (Int.fract q) ⌊q⌋ hq
    refine ⟨Int.fract q + n_α, hn_α_ne, ((⌊q⌋ - n_α).toNat : ℕ), ?_, ?_⟩
    · exact Set.mem_range_self _
    · -- Goal: Int.fract q + n_α + ((⌊q⌋ - n_α).toNat : ℚ) = q
      have h_pos : 0 ≤ ⌊q⌋ - n_α := sub_nonneg.mpr hn_α_le
      have h_toNat_int : ((⌊q⌋ - n_α).toNat : ℤ) = ⌊q⌋ - n_α := Int.toNat_of_nonneg h_pos
      have h_cast : ((⌊q⌋ - n_α).toNat : ℚ) = ((⌊q⌋ : ℤ) : ℚ) - (n_α : ℚ) := by
        have h1 : ((⌊q⌋ - n_α).toNat : ℚ) = (((⌊q⌋ - n_α).toNat : ℤ) : ℚ) := by push_cast; rfl
        rw [h1, h_toNat_int]
        push_cast
        ring
      have hf := Int.fract_add_floor q
      show Int.fract q + (n_α : ℚ) + ((⌊q⌋ - n_α).toNat : ℚ) = q
      rw [h_cast]
      linarith
  -- ============================================================
  -- support s.IsPWO
  -- ============================================================
  have hspwo : (Function.support s).IsPWO :=
    existsCanonicalExpansionAux.support_isPWO_of_subset_support_add_natRange α hsupp_sub
  refine ⟨s, hspwo, ?_⟩
  -- ============================================================
  -- IsNullSeries (α - from_coeff s)
  -- ============================================================
  change IsNullSeries (α - LiftedPAdicHahnSeries.from_coeff s hspwo)
  intro g
  set β : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.from_coeff s hspwo with hβ_def
  set γ : ℚ := Int.fract g with hγ_def
  set n₀ : ℤ := ⌊g⌋ with hn₀_def
  have hg_eq : g = γ + (n₀ : ℚ) := by
    have h := Int.fract_add_floor g
    show g = Int.fract g + (⌊g⌋ : ℚ)
    linarith
  have hγ_in_Ico : 0 ≤ γ ∧ γ < 1 := ⟨Int.fract_nonneg g, Int.fract_lt_one g⟩
  have hγ_self : Int.fract γ = γ := Int.fract_eq_self.mpr hγ_in_Ico
  have hβ_coeff : ∀ q : ℚ, β.coeff q = teichmuller p (s q) := fun _ => rfl
  -- ============================================================
  -- h_intPartial_eq_Icc — generalized over γ' parameter
  -- ============================================================
  have h_intPartial_eq_Icc :
      ∀ (γ' : ℚ) (β' : LiftedPAdicHahnSeries p) (t : ℚ → Fpbar p) (m : ℤ),
        (∀ q : ℚ, β'.coeff q = teichmuller p (t q)) →
        (∀ k : ℤ, k < m → t (γ' + k) = 0) →
        ∀ K : ℤ, m ≤ K →
        intPartial β' γ' K =
          ∑ k ∈ Finset.Icc m K,
            (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (t (γ' + k))) := by
    intro γ' β' t m hβ'_coeff hm K hK
    have h_step1 : intPartial β' γ' K =
        ∑ n ∈ Set.Finite.toFinset (finpropInt β' γ' K),
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β'.coeff (γ' + n)) := by
      simp only [intPartial]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finpropInt β' γ' K))
        (f := fun n : ℤ => (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β'.coeff (γ' + n)))
    rw [h_step1]
    have h_subset : Set.Finite.toFinset (finpropInt β' γ' K) ⊆ Finset.Icc m K := by
      intro n hn
      have hn_mem : n ≤ K ∧ β'.coeff (γ' + n) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finpropInt β' γ' K)).mp hn
      have h_t_ne : t (γ' + n) ≠ 0 := by
        intro h_zero
        apply hn_mem.2
        rw [hβ'_coeff (γ' + n), h_zero]
        exact WittVector.teichmuller_zero p
      have h_n_ge : m ≤ n := by
        by_contra h_lt
        push_neg at h_lt
        exact h_t_ne (hm n h_lt)
      exact Finset.mem_Icc.mpr ⟨h_n_ge, hn_mem.1⟩
    have h_extend : ∑ n ∈ Set.Finite.toFinset (finpropInt β' γ' K),
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β'.coeff (γ' + n)) =
        ∑ n ∈ Finset.Icc m K,
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β'.coeff (γ' + n)) := by
      apply Finset.sum_subset h_subset
      intro n hn_Icc hn_not
      rw [Finset.mem_Icc] at hn_Icc
      have h_β_zero : β'.coeff (γ' + n) = 0 := by
        by_contra hne
        apply hn_not
        exact (Set.Finite.mem_toFinset (hs := finpropInt β' γ' K)).mpr ⟨hn_Icc.2, hne⟩
      rw [h_β_zero]
      simp
    rw [h_extend]
    apply Finset.sum_congr rfl
    intro n _
    rw [hβ'_coeff (γ' + n)]
  -- ============================================================
  -- intPartial β γ K → f γ via h_intPartial_eq_Icc + hb_tendsto
  -- ============================================================
  have hs_eq_b : ∀ k : ℤ, s (γ + (k : ℚ)) = b γ k := by
    intro k
    show b (Int.fract (γ + (k : ℚ))) ⌊(γ : ℚ) + (k : ℚ)⌋ = b γ k
    have h_fract : Int.fract ((γ : ℚ) + (k : ℚ)) = γ := by
      rw [Int.fract_add_intCast γ k]
      exact hγ_self
    have h_floor : ⌊(γ : ℚ) + (k : ℚ)⌋ = k := by
      rw [Int.floor_add_intCast γ k]
      have hγ_floor : ⌊(γ : ℚ)⌋ = 0 := by
        apply Int.floor_eq_zero_iff.mpr
        exact ⟨hγ_in_Ico.1, hγ_in_Ico.2⟩
      rw [hγ_floor, zero_add]
    rw [h_fract, h_floor]
  have h_vanish_γ : ∀ k : ℤ, k < m_b γ → s (γ + (k : ℚ)) = 0 := by
    intro k hk
    rw [hs_eq_b k]; exact hb_vanish γ k hk
  have h_β_eq_γ : ∀ K : ℤ, m_b γ ≤ K →
      intPartial β γ K =
        ∑ k ∈ Finset.Icc (m_b γ) K,
          (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (b γ k)) := by
    intro K hK
    rw [h_intPartial_eq_Icc γ β s (m_b γ) hβ_coeff h_vanish_γ K hK]
    apply Finset.sum_congr rfl
    intro k _
    rw [hs_eq_b k]
  have h_tendsto_β_γ : Filter.Tendsto (intPartial β γ) Filter.atTop (nhds (f γ)) := by
    apply (hb_tendsto γ).congr'
    rw [Filter.EventuallyEq]
    filter_upwards [Filter.eventually_ge_atTop (m_b γ)] with K hK
    exact (h_β_eq_γ K hK).symm
  -- ============================================================
  -- Translation: intPartial β' g K = (p:QpUn)^(-n₀) * intPartial β' γ (K + n₀)
  -- ============================================================
  have h_translate : ∀ (β' : LiftedPAdicHahnSeries p) (K : ℤ),
      intPartial β' g K = (p : QpUn p) ^ (-n₀) * intPartial β' γ (K + n₀) := by
    intro β' K
    have hL : intPartial β' g K =
        ∑ n ∈ Set.Finite.toFinset (finpropInt β' g K),
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β'.coeff (g + n)) := by
      simp only [intPartial]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finpropInt β' g K))
        (f := fun n : ℤ => (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β'.coeff (g + n)))
    have hR : intPartial β' γ (K + n₀) =
        ∑ n ∈ Set.Finite.toFinset (finpropInt β' γ (K + n₀)),
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β'.coeff (γ + n)) := by
      simp only [intPartial]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finpropInt β' γ (K + n₀)))
        (f := fun n : ℤ => (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β'.coeff (γ + n)))
    rw [hL, hR]
    have h_image : Set.Finite.toFinset (finpropInt β' γ (K + n₀)) =
        (Set.Finite.toFinset (finpropInt β' g K)).image (fun n : ℤ => n + n₀) := by
      ext n'
      simp only [Set.Finite.mem_toFinset, Finset.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨n' - n₀, ⟨by omega, ?_⟩, by omega⟩
        have h_eq_q : (g : ℚ) + ((n' - n₀ : ℤ) : ℚ) = (γ : ℚ) + (n' : ℚ) := by
          push_cast
          rw [hg_eq]; ring
        rw [h_eq_q]; exact h2
      · rintro ⟨n, ⟨hn1, hn2⟩, h_eq⟩
        refine ⟨by omega, ?_⟩
        have h_eq_q : (γ : ℚ) + (n' : ℚ) = (g : ℚ) + (n : ℚ) := by
          have h_n' : (n' : ℚ) = ((n + n₀ : ℤ) : ℚ) := by exact_mod_cast h_eq.symm
          rw [h_n']; push_cast; rw [hg_eq]; ring
        rw [h_eq_q]; exact hn2
    rw [h_image]
    rw [Finset.sum_image (by
      intro a _ b _ h
      simp only at h
      omega)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have h_coeff : β'.coeff ((γ : ℚ) + ((n + n₀ : ℤ) : ℚ)) = β'.coeff ((g : ℚ) + (n : ℚ)) := by
      congr 1
      push_cast
      rw [hg_eq]; ring
    rw [h_coeff]
    rw [show ((p : QpUn p) ^ (-n₀)) * ((p : QpUn p) ^ (n + n₀) *
          algebraMap (OQpUn p) (QpUn p) (β'.coeff ((g : ℚ) + (n : ℚ)))) =
        ((p : QpUn p) ^ (-n₀) * (p : QpUn p) ^ (n + n₀)) *
          algebraMap (OQpUn p) (QpUn p) (β'.coeff ((g : ℚ) + (n : ℚ))) from by ring]
    rw [show (p : QpUn p) ^ (-n₀) * (p : QpUn p) ^ (n + n₀) = (p : QpUn p) ^ n from by
      rw [← zpow_add₀ hp_ne]
      congr 1
      omega]
  -- ============================================================
  -- intPartial β g K → f g (via translation + h_tendsto_β_γ + uniqueness)
  -- ============================================================
  have h_α_g : Filter.Tendsto (intPartial α g) Filter.atTop (nhds (f g)) := hf_spec g
  have h_α_γ : Filter.Tendsto (intPartial α γ) Filter.atTop (nhds (f γ)) := hf_spec γ
  have h_shift_atTop : Filter.Tendsto (fun K : ℤ => K + n₀) Filter.atTop Filter.atTop := by
    exact Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
  have h_α_γ_shift : Filter.Tendsto (fun K : ℤ => intPartial α γ (K + n₀)) Filter.atTop
      (nhds (f γ)) := h_α_γ.comp h_shift_atTop
  have h_α_γ_mul : Filter.Tendsto
      (fun K : ℤ => (p : QpUn p) ^ (-n₀) * intPartial α γ (K + n₀)) Filter.atTop
      (nhds ((p : QpUn p) ^ (-n₀) * f γ)) := h_α_γ_shift.const_mul _
  have h_α_translate : Filter.Tendsto (intPartial α g) Filter.atTop
      (nhds ((p : QpUn p) ^ (-n₀) * f γ)) := by
    apply h_α_γ_mul.congr'
    rw [Filter.EventuallyEq]
    filter_upwards with K
    exact (h_translate α K).symm
  have h_fg_eq : f g = (p : QpUn p) ^ (-n₀) * f γ :=
    tendsto_nhds_unique h_α_g h_α_translate
  have h_β_γ_shift : Filter.Tendsto (fun K : ℤ => intPartial β γ (K + n₀)) Filter.atTop
      (nhds (f γ)) := h_tendsto_β_γ.comp h_shift_atTop
  have h_β_γ_mul : Filter.Tendsto
      (fun K : ℤ => (p : QpUn p) ^ (-n₀) * intPartial β γ (K + n₀)) Filter.atTop
      (nhds ((p : QpUn p) ^ (-n₀) * f γ)) := h_β_γ_shift.const_mul _
  have h_β_g : Filter.Tendsto (intPartial β g) Filter.atTop (nhds (f g)) := by
    rw [h_fg_eq]
    apply h_β_γ_mul.congr'
    rw [Filter.EventuallyEq]
    filter_upwards with K
    exact (h_translate β K).symm
  -- ============================================================
  -- intPartial (α - β) g K = intPartial α g K - intPartial β g K
  -- ============================================================
  have h_intPartial_sub : ∀ K : ℤ,
      intPartial (α - β) g K = intPartial α g K - intPartial β g K := by
    intro K
    set T_α : Finset ℤ := Set.Finite.toFinset (finpropInt α g K) with hT_α_def
    set T_β : Finset ℤ := Set.Finite.toFinset (finpropInt β g K) with hT_β_def
    set T_d : Finset ℤ := Set.Finite.toFinset (finpropInt (α - β) g K) with hT_d_def
    set T_U : Finset ℤ := T_α ∪ T_β with hT_U_def
    have e_α : intPartial α g K =
        ∑ n ∈ T_α, (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + n)) := by
      simp only [intPartial, hT_α_def]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finpropInt α g K))
        (f := fun n : ℤ => (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + n)))
    have e_β : intPartial β g K =
        ∑ n ∈ T_β, (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β.coeff (g + n)) := by
      simp only [intPartial, hT_β_def]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finpropInt β g K))
        (f := fun n : ℤ => (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β.coeff (g + n)))
    have e_d : intPartial (α - β) g K =
        ∑ n ∈ T_d, (p : QpUn p) ^ n *
          algebraMap (OQpUn p) (QpUn p) ((α - β).coeff (g + n)) := by
      simp only [intPartial, hT_d_def]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finpropInt (α - β) g K))
        (f := fun n : ℤ => (p : QpUn p) ^ n *
          algebraMap (OQpUn p) (QpUn p) ((α - β).coeff (g + n)))
    have h_α_sub_U : T_α ⊆ T_U := Finset.subset_union_left
    have h_β_sub_U : T_β ⊆ T_U := Finset.subset_union_right
    have h_d_sub_U : T_d ⊆ T_U := by
      intro n hn
      have hn_mem : n ≤ K ∧ (α - β).coeff (g + n) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finpropInt (α - β) g K)).mp hn
      have h_sub_eq : (α - β).coeff (g + n) = α.coeff (g + n) - β.coeff (g + n) := rfl
      rw [h_sub_eq] at hn_mem
      by_cases h_α_z : α.coeff (g + n) = 0
      · have h_β_ne : β.coeff (g + n) ≠ 0 := by
          intro h_β_z
          apply hn_mem.2
          rw [h_α_z, h_β_z, sub_self]
        exact Finset.mem_union_right T_α
          ((Set.Finite.mem_toFinset (hs := finpropInt β g K)).mpr ⟨hn_mem.1, h_β_ne⟩)
      · exact Finset.mem_union_left T_β
          ((Set.Finite.mem_toFinset (hs := finpropInt α g K)).mpr ⟨hn_mem.1, h_α_z⟩)
    have he_α_U : ∑ n ∈ T_α,
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + n)) =
        ∑ n ∈ T_U,
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (g + n)) := by
      apply Finset.sum_subset h_α_sub_U
      intro n hn_U hn_not_α
      have hn_le_K : n ≤ K := by
        rcases Finset.mem_union.mp hn_U with h_α_mem | h_β_mem
        · exact ((Set.Finite.mem_toFinset (hs := finpropInt α g K)).mp h_α_mem).1
        · exact ((Set.Finite.mem_toFinset (hs := finpropInt β g K)).mp h_β_mem).1
      have h_α_z : α.coeff (g + n) = 0 := by
        by_contra hne
        exact hn_not_α
          ((Set.Finite.mem_toFinset (hs := finpropInt α g K)).mpr ⟨hn_le_K, hne⟩)
      rw [h_α_z]
      simp
    have he_β_U : ∑ n ∈ T_β,
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β.coeff (g + n)) =
        ∑ n ∈ T_U,
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β.coeff (g + n)) := by
      apply Finset.sum_subset h_β_sub_U
      intro n hn_U hn_not_β
      have hn_le_K : n ≤ K := by
        rcases Finset.mem_union.mp hn_U with h_α_mem | h_β_mem
        · exact ((Set.Finite.mem_toFinset (hs := finpropInt α g K)).mp h_α_mem).1
        · exact ((Set.Finite.mem_toFinset (hs := finpropInt β g K)).mp h_β_mem).1
      have h_β_z : β.coeff (g + n) = 0 := by
        by_contra hne
        exact hn_not_β
          ((Set.Finite.mem_toFinset (hs := finpropInt β g K)).mpr ⟨hn_le_K, hne⟩)
      rw [h_β_z]
      simp
    have he_d_U : ∑ n ∈ T_d,
          (p : QpUn p) ^ n *
            algebraMap (OQpUn p) (QpUn p) ((α - β).coeff (g + n)) =
        ∑ n ∈ T_U,
          (p : QpUn p) ^ n *
            algebraMap (OQpUn p) (QpUn p) ((α - β).coeff (g + n)) := by
      apply Finset.sum_subset h_d_sub_U
      intro n hn_U hn_not_d
      have hn_le_K : n ≤ K := by
        rcases Finset.mem_union.mp hn_U with h_α_mem | h_β_mem
        · exact ((Set.Finite.mem_toFinset (hs := finpropInt α g K)).mp h_α_mem).1
        · exact ((Set.Finite.mem_toFinset (hs := finpropInt β g K)).mp h_β_mem).1
      have h_d_z : (α - β).coeff (g + n) = 0 := by
        by_contra hne
        exact hn_not_d
          ((Set.Finite.mem_toFinset (hs := finpropInt (α - β) g K)).mpr ⟨hn_le_K, hne⟩)
      rw [h_d_z]
      simp
    rw [e_d, he_d_U, e_α, he_α_U, e_β, he_β_U]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have h_sub_coeff : (α - β).coeff (g + n) = α.coeff (g + n) - β.coeff (g + n) := rfl
    rw [h_sub_coeff, map_sub, mul_sub]
  -- ============================================================
  -- intPartial (α - β) g K → 0
  -- ============================================================
  have h_intPartial_zero : Filter.Tendsto (fun K : ℤ => intPartial (α - β) g K) Filter.atTop
      (nhds (0 : QpUn p)) := by
    have h_diff : Filter.Tendsto
        (fun K : ℤ => intPartial α g K - intPartial β g K) Filter.atTop
        (nhds ((f g) - (f g))) := h_α_g.sub h_β_g
    rw [sub_self] at h_diff
    apply h_diff.congr'
    rw [Filter.EventuallyEq]
    filter_upwards with K
    exact (h_intPartial_sub K).symm
  -- ============================================================
  -- Phase 1: bridge finprop ⇄ intPartial
  -- ============================================================
  have h_finprop_eq_finpropInt :
      ∀ (x : LiftedPAdicHahnSeries p) (M : ℕ),
        (Set.Finite.toFinset (finprop x g M) : Finset ℤ) =
        (Set.Finite.toFinset (finpropInt x g ⌊((M : ℚ) - g)⌋) : Finset ℤ) := by
    intro x M
    ext n
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    constructor
    · intro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hineq : (n : ℚ) ≤ (M : ℚ) - g := by linarith
      exact Int.le_floor.mpr hineq
    · intro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hineq : (n : ℚ) ≤ (M : ℚ) - g :=
        le_trans (by exact_mod_cast h1) (Int.floor_le ((M : ℚ) - g))
      linarith
  have h_finprop_to_intPartial :
      (fun M : ℕ => ∑ n : Set.Finite.toFinset (finprop (α - β) g M),
        (p : QpUn p) ^ n.val *
          algebraMap (OQpUn p) (QpUn p) ((α - β).coeff (g + n))) =
      fun M : ℕ => intPartial (α - β) g ⌊((M : ℚ) - g)⌋ := by
    funext M
    simp only [intPartial]
    have h_attach_α := Finset.sum_attach
      (s := Set.Finite.toFinset (finprop (α - β) g M))
      (f := fun n : ℤ => (p : QpUn p) ^ n *
        algebraMap (OQpUn p) (QpUn p) ((α - β).coeff (g + n)))
    have h_attach_β := Finset.sum_attach
      (s := Set.Finite.toFinset (finpropInt (α - β) g ⌊((M : ℚ) - g)⌋))
      (f := fun n : ℤ => (p : QpUn p) ^ n *
        algebraMap (OQpUn p) (QpUn p) ((α - β).coeff (g + n)))
    rw [show (∑ n : Set.Finite.toFinset (finprop (α - β) g M),
        (p : QpUn p) ^ n.val *
          algebraMap (OQpUn p) (QpUn p) ((α - β).coeff (g + n))) =
      ∑ n ∈ Set.Finite.toFinset (finprop (α - β) g M),
        (p : QpUn p) ^ n *
          algebraMap (OQpUn p) (QpUn p) ((α - β).coeff (g + n)) from h_attach_α]
    rw [show (∑ n : Set.Finite.toFinset (finpropInt (α - β) g ⌊((M : ℚ) - g)⌋),
        (p : QpUn p) ^ n.1 *
          algebraMap (OQpUn p) (QpUn p) ((α - β).coeff (g + n))) =
      ∑ n ∈ Set.Finite.toFinset (finpropInt (α - β) g ⌊((M : ℚ) - g)⌋),
        (p : QpUn p) ^ n *
          algebraMap (OQpUn p) (QpUn p) ((α - β).coeff (g + n)) from h_attach_β]
    rw [h_finprop_eq_finpropInt (α - β) M]
  have h_φ : Filter.Tendsto (fun M : ℕ => ⌊((M : ℚ) - g)⌋) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge ((b : ℚ) + g)
    refine ⟨N, ?_⟩
    intro M hM
    rw [Int.le_floor]
    have hM' : (N : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
    linarith
  -- ============================================================
  -- Compose to get the goal
  -- ============================================================
  rw [h_finprop_to_intPartial]
  exact h_intPartial_zero.comp h_φ

set_option maxHeartbeats 1000000 in
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
  classical
  set α : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.from_coeff s hspwo with hα_def
  set α' : LiftedPAdicHahnSeries p := LiftedPAdicHahnSeries.from_coeff s' hspwo' with hα'_def
  -- Unfold null series
  change IsNullSeries (α - α') at h
  -- p ≠ 0 in QpUn p
  have hp_ne : (p : QpUn p) ≠ 0 := by
    rw [show (p : QpUn p) = algebraMap (OQpUn p) (QpUn p) (p : OQpUn p) from by
      push_cast; rfl]
    exact fun h_zero => WittVector.p_nonzero p _
      ((IsFractionRing.injective (OQpUn p) (QpUn p))
        (by simpa using h_zero))
  -- Coefficient identities
  have hα_coeff : ∀ q : ℚ, α.coeff q = teichmuller p (s q) := fun _ => rfl
  have hα'_coeff : ∀ q : ℚ, α'.coeff q = teichmuller p (s' q) := fun _ => rfl
  have hsub_coeff : ∀ q : ℚ,
      (α - α').coeff q = teichmuller p (s q) - teichmuller p (s' q) := fun _ => rfl
  -- ============================================================
  -- funext
  -- ============================================================
  funext q
  set γ : ℚ := Int.fract q with hγ_def
  set n₀ : ℤ := ⌊q⌋ with hn₀_def
  have hq_eq : q = γ + (n₀ : ℚ) := by
    have := Int.fract_add_floor q
    linarith
  rw [hq_eq]
  set Bs : ℤ → Fpbar p := fun k => s (γ + k) with hBs_def
  set Bs' : ℤ → Fpbar p := fun k => s' (γ + k) with hBs'_def
  show s (γ + (n₀ : ℚ)) = s' (γ + (n₀ : ℚ))
  suffices h_Bs_eq : ∀ k : ℤ, Bs k = Bs' k by
    exact h_Bs_eq n₀
  -- ============================================================
  -- Get cutoffs m_s, m_s'
  -- ============================================================
  obtain ⟨m_s, hm_s⟩ : ∃ m_s : ℤ, ∀ k : ℤ, k < m_s → Bs k = 0 := by
    by_cases hsp : (Function.support s).Nonempty
    · refine ⟨⌈(hspwo.isWF.min hsp - γ : ℚ)⌉, ?_⟩
      intro k hk
      show s (γ + k) = 0
      by_contra hne
      have hmem : (γ + (k : ℚ)) ∈ Function.support s := hne
      have hmin_le : hspwo.isWF.min hsp ≤ γ + k := hspwo.isWF.min_le hsp hmem
      have hk_ineq : (hspwo.isWF.min hsp - γ : ℚ) ≤ (k : ℚ) := by linarith
      have hceil : ⌈(hspwo.isWF.min hsp - γ : ℚ)⌉ ≤ k := Int.ceil_le.mpr hk_ineq
      linarith
    · refine ⟨0, ?_⟩
      intro k _
      show s (γ + k) = 0
      have hs_zero : s = 0 := Function.support_eq_empty_iff.mp
        (Set.not_nonempty_iff_eq_empty.mp hsp)
      simp [hs_zero]
  obtain ⟨m_s', hm_s'⟩ : ∃ m_s' : ℤ, ∀ k : ℤ, k < m_s' → Bs' k = 0 := by
    by_cases hsp : (Function.support s').Nonempty
    · refine ⟨⌈(hspwo'.isWF.min hsp - γ : ℚ)⌉, ?_⟩
      intro k hk
      show s' (γ + k) = 0
      by_contra hne
      have hmem : (γ + (k : ℚ)) ∈ Function.support s' := hne
      have hmin_le : hspwo'.isWF.min hsp ≤ γ + k := hspwo'.isWF.min_le hsp hmem
      have hk_ineq : (hspwo'.isWF.min hsp - γ : ℚ) ≤ (k : ℚ) := by linarith
      have hceil : ⌈(hspwo'.isWF.min hsp - γ : ℚ)⌉ ≤ k := Int.ceil_le.mpr hk_ineq
      linarith
    · refine ⟨0, ?_⟩
      intro k _
      show s' (γ + k) = 0
      have hs'_zero : s' = 0 := Function.support_eq_empty_iff.mp
        (Set.not_nonempty_iff_eq_empty.mp hsp)
      simp [hs'_zero]
  -- ============================================================
  -- Get limits y_s, y_s', y_d
  -- ============================================================
  obtain ⟨y_s, hy_s⟩ := existsCanonicalExpansionAux.exists_lim_intPartial α γ
  obtain ⟨y_s', hy_s'⟩ := existsCanonicalExpansionAux.exists_lim_intPartial α' γ
  obtain ⟨y_d, hy_d⟩ := existsCanonicalExpansionAux.exists_lim_intPartial (α - α') γ
  -- ============================================================
  -- Helper: intPartial = Icc-form sum (for K ≥ m)
  -- ============================================================
  have h_intPartial_eq_Icc :
      ∀ (β : LiftedPAdicHahnSeries p) (t : ℚ → Fpbar p) (m : ℤ),
        (∀ q : ℚ, β.coeff q = teichmuller p (t q)) →
        (∀ k : ℤ, k < m → t (γ + k) = 0) →
        ∀ K : ℤ, m ≤ K →
        intPartial β γ K =
          ∑ k ∈ Finset.Icc m K,
            (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (t (γ + k))) := by
    intro β t m hβ_coeff hm K hK
    have h_step1 : intPartial β γ K =
        ∑ n ∈ Set.Finite.toFinset (finpropInt β γ K),
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β.coeff (γ + n)) := by
      simp only [intPartial]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finpropInt β γ K))
        (f := fun n : ℤ => (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β.coeff (γ + n)))
    rw [h_step1]
    have h_subset : Set.Finite.toFinset (finpropInt β γ K) ⊆ Finset.Icc m K := by
      intro n hn
      have hn_mem : n ≤ K ∧ β.coeff (γ + n) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finpropInt β γ K)).mp hn
      have h_t_ne : t (γ + n) ≠ 0 := by
        intro h_zero
        apply hn_mem.2
        rw [hβ_coeff (γ + n), h_zero]
        exact WittVector.teichmuller_zero p
      have h_n_ge : m ≤ n := by
        by_contra h_lt
        push_neg at h_lt
        exact h_t_ne (hm n h_lt)
      exact Finset.mem_Icc.mpr ⟨h_n_ge, hn_mem.1⟩
    have h_extend : ∑ n ∈ Set.Finite.toFinset (finpropInt β γ K),
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β.coeff (γ + n)) =
        ∑ n ∈ Finset.Icc m K,
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (β.coeff (γ + n)) := by
      apply Finset.sum_subset h_subset
      intro n hn_Icc hn_not
      rw [Finset.mem_Icc] at hn_Icc
      have h_β_zero : β.coeff (γ + n) = 0 := by
        by_contra hne
        apply hn_not
        exact (Set.Finite.mem_toFinset (hs := finpropInt β γ K)).mpr ⟨hn_Icc.2, hne⟩
      rw [h_β_zero]
      simp
    rw [h_extend]
    apply Finset.sum_congr rfl
    intro n _
    rw [hβ_coeff (γ + n)]
  -- ============================================================
  -- Tendsto in Icc form for α and α'
  -- ============================================================
  have htendsto_s :
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m_s K,
          (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (Bs k)))
        Filter.atTop (nhds y_s) := by
    apply hy_s.congr'
    rw [Filter.EventuallyEq]
    filter_upwards [Filter.eventually_ge_atTop m_s] with K hK
    have := h_intPartial_eq_Icc α s m_s hα_coeff hm_s K hK
    show intPartial α γ K = _
    rw [this]
  have htendsto_s' :
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m_s' K,
          (p : QpUn p) ^ k * algebraMap (OQpUn p) (QpUn p) (teichmuller p (Bs' k)))
        Filter.atTop (nhds y_s') := by
    apply hy_s'.congr'
    rw [Filter.EventuallyEq]
    filter_upwards [Filter.eventually_ge_atTop m_s'] with K hK
    have := h_intPartial_eq_Icc α' s' m_s' hα'_coeff hm_s' K hK
    show intPartial α' γ K = _
    rw [this]
  -- ============================================================
  -- Show y_d = y_s - y_s' (via intPartial of difference)
  -- ============================================================
  have h_intPartial_sub : ∀ K : ℤ,
      intPartial (α - α') γ K = intPartial α γ K - intPartial α' γ K := by
    intro K
    -- Setup: index sets and union
    set T_α : Finset ℤ := Set.Finite.toFinset (finpropInt α γ K) with hT_α_def
    set T_α' : Finset ℤ := Set.Finite.toFinset (finpropInt α' γ K) with hT_α'_def
    set T_d : Finset ℤ := Set.Finite.toFinset (finpropInt (α - α') γ K) with hT_d_def
    set T_U : Finset ℤ := T_α ∪ T_α' with hT_U_def
    -- Convert each intPartial to plain Finset.sum
    have e_α : intPartial α γ K =
        ∑ n ∈ T_α, (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (γ + n)) := by
      simp only [intPartial, hT_α_def]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finpropInt α γ K))
        (f := fun n : ℤ => (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (γ + n)))
    have e_α' : intPartial α' γ K =
        ∑ n ∈ T_α', (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α'.coeff (γ + n)) := by
      simp only [intPartial, hT_α'_def]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finpropInt α' γ K))
        (f := fun n : ℤ => (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α'.coeff (γ + n)))
    have e_d : intPartial (α - α') γ K =
        ∑ n ∈ T_d, (p : QpUn p) ^ n *
          algebraMap (OQpUn p) (QpUn p) ((α - α').coeff (γ + n)) := by
      simp only [intPartial, hT_d_def]
      exact Finset.sum_attach (s := Set.Finite.toFinset (finpropInt (α - α') γ K))
        (f := fun n : ℤ => (p : QpUn p) ^ n *
          algebraMap (OQpUn p) (QpUn p) ((α - α').coeff (γ + n)))
    -- Subset claims
    have h_α_sub_U : T_α ⊆ T_U := Finset.subset_union_left
    have h_α'_sub_U : T_α' ⊆ T_U := Finset.subset_union_right
    have h_d_sub_U : T_d ⊆ T_U := by
      intro n hn
      have hn_mem : n ≤ K ∧ (α - α').coeff (γ + n) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := finpropInt (α - α') γ K)).mp hn
      have h_sub_eq : (α - α').coeff (γ + n) = α.coeff (γ + n) - α'.coeff (γ + n) := rfl
      rw [h_sub_eq] at hn_mem
      by_cases h_α_z : α.coeff (γ + n) = 0
      · have h_α'_ne : α'.coeff (γ + n) ≠ 0 := by
          intro h_α'_z
          apply hn_mem.2
          rw [h_α_z, h_α'_z, sub_self]
        exact Finset.mem_union_right T_α
          ((Set.Finite.mem_toFinset (hs := finpropInt α' γ K)).mpr ⟨hn_mem.1, h_α'_ne⟩)
      · exact Finset.mem_union_left T_α'
          ((Set.Finite.mem_toFinset (hs := finpropInt α γ K)).mpr ⟨hn_mem.1, h_α_z⟩)
    -- Extend each sum to T_U
    have he_α_U : ∑ n ∈ T_α,
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (γ + n)) =
        ∑ n ∈ T_U,
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α.coeff (γ + n)) := by
      apply Finset.sum_subset h_α_sub_U
      intro n hn_U hn_not_α
      have hn_le_K : n ≤ K := by
        rcases Finset.mem_union.mp hn_U with h_α_mem | h_α'_mem
        · exact ((Set.Finite.mem_toFinset (hs := finpropInt α γ K)).mp h_α_mem).1
        · exact ((Set.Finite.mem_toFinset (hs := finpropInt α' γ K)).mp h_α'_mem).1
      have h_α_z : α.coeff (γ + n) = 0 := by
        by_contra hne
        exact hn_not_α
          ((Set.Finite.mem_toFinset (hs := finpropInt α γ K)).mpr ⟨hn_le_K, hne⟩)
      rw [h_α_z]
      simp
    have he_α'_U : ∑ n ∈ T_α',
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α'.coeff (γ + n)) =
        ∑ n ∈ T_U,
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (α'.coeff (γ + n)) := by
      apply Finset.sum_subset h_α'_sub_U
      intro n hn_U hn_not_α'
      have hn_le_K : n ≤ K := by
        rcases Finset.mem_union.mp hn_U with h_α_mem | h_α'_mem
        · exact ((Set.Finite.mem_toFinset (hs := finpropInt α γ K)).mp h_α_mem).1
        · exact ((Set.Finite.mem_toFinset (hs := finpropInt α' γ K)).mp h_α'_mem).1
      have h_α'_z : α'.coeff (γ + n) = 0 := by
        by_contra hne
        exact hn_not_α'
          ((Set.Finite.mem_toFinset (hs := finpropInt α' γ K)).mpr ⟨hn_le_K, hne⟩)
      rw [h_α'_z]
      simp
    have he_d_U : ∑ n ∈ T_d,
          (p : QpUn p) ^ n *
            algebraMap (OQpUn p) (QpUn p) ((α - α').coeff (γ + n)) =
        ∑ n ∈ T_U,
          (p : QpUn p) ^ n *
            algebraMap (OQpUn p) (QpUn p) ((α - α').coeff (γ + n)) := by
      apply Finset.sum_subset h_d_sub_U
      intro n hn_U hn_not_d
      have hn_le_K : n ≤ K := by
        rcases Finset.mem_union.mp hn_U with h_α_mem | h_α'_mem
        · exact ((Set.Finite.mem_toFinset (hs := finpropInt α γ K)).mp h_α_mem).1
        · exact ((Set.Finite.mem_toFinset (hs := finpropInt α' γ K)).mp h_α'_mem).1
      have h_d_z : (α - α').coeff (γ + n) = 0 := by
        by_contra hne
        exact hn_not_d
          ((Set.Finite.mem_toFinset (hs := finpropInt (α - α') γ K)).mpr ⟨hn_le_K, hne⟩)
      rw [h_d_z]
      simp
    -- Combine
    rw [e_d, he_d_U, e_α, he_α_U, e_α', he_α'_U]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    have h_sub_coeff : (α - α').coeff (γ + n) = α.coeff (γ + n) - α'.coeff (γ + n) := rfl
    rw [h_sub_coeff, map_sub, mul_sub]
  have h_yd_eq : y_d = y_s - y_s' := by
    have h := hy_s.sub hy_s'
    have h_congr : Filter.Tendsto
        (fun K : ℤ => intPartial α γ K - intPartial α' γ K) Filter.atTop (nhds (y_s - y_s')) := h
    have h_eq_fn : (fun K : ℤ => intPartial (α - α') γ K) =
        (fun K : ℤ => intPartial α γ K - intPartial α' γ K) := by
      funext K
      exact h_intPartial_sub K
    have hy_d' : Filter.Tendsto
        (fun K : ℤ => intPartial α γ K - intPartial α' γ K) Filter.atTop (nhds y_d) := by
      rw [← h_eq_fn]; exact hy_d
    exact tendsto_nhds_unique hy_d' h_congr
  -- ============================================================
  -- Show y_d = 0 (using IsNullSeries)
  -- ============================================================
  have h_yd_zero : y_d = 0 := by
    -- Bridge: ∑ finprop x γ M = intPartial x γ ⌊M - γ⌋
    have h_finprop_eq_finpropInt :
        ∀ (x : LiftedPAdicHahnSeries p) (M : ℕ),
          (Set.Finite.toFinset (finprop x γ M) : Finset ℤ) =
          (Set.Finite.toFinset (finpropInt x γ ⌊((M : ℚ) - γ)⌋) : Finset ℤ) := by
      intro x M
      ext n
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      constructor
      · intro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        have hineq : (n : ℚ) ≤ (M : ℚ) - γ := by linarith
        exact Int.le_floor.mpr hineq
      · intro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        have hineq : (n : ℚ) ≤ (M : ℚ) - γ :=
          le_trans (by exact_mod_cast h1) (Int.floor_le ((M : ℚ) - γ))
        linarith
    -- Bridge the finprop sum to intPartial form
    have h_finprop_to_intPartial :
        (fun M : ℕ => ∑ n : Set.Finite.toFinset (finprop (α - α') γ M),
          (p : QpUn p) ^ n.val *
            algebraMap (OQpUn p) (QpUn p) ((α - α').coeff (γ + n))) =
        fun M : ℕ => intPartial (α - α') γ ⌊((M : ℚ) - γ)⌋ := by
      funext M
      simp only [intPartial]
      have h_attach_α := Finset.sum_attach
        (s := Set.Finite.toFinset (finprop (α - α') γ M))
        (f := fun n : ℤ => (p : QpUn p) ^ n *
          algebraMap (OQpUn p) (QpUn p) ((α - α').coeff (γ + n)))
      have h_attach_β := Finset.sum_attach
        (s := Set.Finite.toFinset (finpropInt (α - α') γ ⌊((M : ℚ) - γ)⌋))
        (f := fun n : ℤ => (p : QpUn p) ^ n *
          algebraMap (OQpUn p) (QpUn p) ((α - α').coeff (γ + n)))
      rw [show (∑ n : Set.Finite.toFinset (finprop (α - α') γ M),
          (p : QpUn p) ^ n.val *
            algebraMap (OQpUn p) (QpUn p) ((α - α').coeff (γ + n))) =
        ∑ n ∈ Set.Finite.toFinset (finprop (α - α') γ M),
          (p : QpUn p) ^ n *
            algebraMap (OQpUn p) (QpUn p) ((α - α').coeff (γ + n)) from h_attach_α]
      rw [show (∑ n : Set.Finite.toFinset (finpropInt (α - α') γ ⌊((M : ℚ) - γ)⌋),
          (p : QpUn p) ^ n.1 *
            algebraMap (OQpUn p) (QpUn p) ((α - α').coeff (γ + n))) =
        ∑ n ∈ Set.Finite.toFinset (finpropInt (α - α') γ ⌊((M : ℚ) - γ)⌋),
          (p : QpUn p) ^ n *
            algebraMap (OQpUn p) (QpUn p) ((α - α').coeff (γ + n)) from h_attach_β]
      rw [h_finprop_eq_finpropInt (α - α') M]
    -- Apply hypothesis at γ
    have h_at_γ := h γ
    rw [h_finprop_to_intPartial] at h_at_γ
    -- h_at_γ : Tendsto (fun M => intPartial (α - α') γ ⌊M - γ⌋) atTop (𝓝 0)
    -- Compose: φ M = ⌊(M : ℚ) - γ⌋, φ → ∞
    have h_φ : Filter.Tendsto (fun M : ℕ => ⌊((M : ℚ) - γ)⌋) Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_atTop.mpr
      intro b
      obtain ⟨N, hN⟩ := exists_nat_ge ((b : ℚ) + γ)
      refine ⟨N, ?_⟩
      intro M hM
      rw [Int.le_floor]
      have hM' : (N : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
      linarith
    -- y_d is the limit of intPartial (α - α') γ; composing with φ gives y_d
    have h_comp : Filter.Tendsto
        (fun M : ℕ => intPartial (α - α') γ ⌊((M : ℚ) - γ)⌋) Filter.atTop (nhds y_d) := by
      have := hy_d.comp h_φ
      exact this
    exact tendsto_nhds_unique h_comp h_at_γ
  -- y_s = y_s'
  have h_y_eq : y_s = y_s' := by
    have h1 : y_s - y_s' = 0 := by rw [← h_yd_eq, h_yd_zero]
    exact sub_eq_zero.mp h1
  -- ============================================================
  -- Apply teichmuller_digits_unique
  -- ============================================================
  rw [h_y_eq] at htendsto_s
  exact existsCanonicalExpansionAux.teichmuller_digits_unique
    Bs Bs' m_s m_s' hm_s hm_s' htendsto_s htendsto_s'

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

-- The valuation of a p-adic Hahn series x is defined to be the minimum of the support of x.
open Classical in
noncomputable def val
  (p : ℕ) [Fact (Nat.Prime p)] :
  AddValuation ((LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) (WithTop ℚ) := {
  toFun x :=
    if h : x = 0 then (⊤ : WithTop ℚ)
    else ((support_IsPWO x).isWF.min (support_nonempty_of_nonzero p x h) : WithTop ℚ)
  map_zero' := by admit
  map_one' := by admit
  map_mul' := by admit
  map_add_le_max' := by admit
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

-- The field of p-adic Hahn series is complete with respect to the valuation defined above.
instance instCompleteSpace {p : ℕ} [Fact (Nat.Prime p)] :
    CompleteSpace (𝕃_[p]) := by admit

-- Define an element of W(𝔽ₚ^⁻)((p^ℚ)) from a function ℚ → 𝔽ₚ^⁻ with well-ordered support by the
-- formula f ↦ ∑ₖ [f(k)]pᵏ
noncomputable def from_coeff {p : ℕ} [Fact (Nat.Prime p)]
    (s : ℚ → Fpbar p) (hspwo : (Function.support s).IsPWO) :
    (𝕃_[p]) :=
  Ideal.Quotient.mk (NullSeriesIdeal p) (LiftedPAdicHahnSeries.from_coeff s hspwo)

-- The `coefficients` of the p-adic Hahn series obtained from a function ℚ → 𝔽ₚ^⁻ by
-- the `from_coeff` construction is the original function.
theorem coeff_of_from_coeff_eq_self {p : ℕ} [Fact (Nat.Prime p)]
    (s : ℚ → Fpbar p) (hspwo : s.support.IsPWO) :
    (from_coeff s hspwo).coeff = s := by
  have hEq :
      ⟨s, hspwo⟩ = (exists_canonical_expansion (from_coeff s hspwo)).choose := by
    apply (exists_canonical_expansion (from_coeff s hspwo)).choose_spec.2
    simpa [from_coeff] using
      (Quotient.exact (Quotient.out_eq (from_coeff s hspwo)))
  exact (congrArg Subtype.val hEq).symm

-- The converse of the above theorem.
theorem from_coeff_of_coeff_eq_self {p : ℕ} [Fact (Nat.Prime p)]
    (x : 𝕃_[p]) :
    from_coeff x.coeff (support_IsPWO x) = x := by
  simp only [from_coeff, coeff]
  set s := (exists_canonical_expansion x).choose
  have h := (exists_canonical_expansion x).choose_spec.1
  dsimp at h
  obtain ⟨y, hy⟩ := h
  have : Ideal.Quotient.mk (NullSeriesIdeal p)
      (LiftedPAdicHahnSeries.from_coeff s.val s.prop) =
    Ideal.Quotient.mk (NullSeriesIdeal p) x.out := by
    apply Quotient.sound
    change (Ideal.Quotient.ringCon (NullSeriesIdeal p))
      (LiftedPAdicHahnSeries.from_coeff s.val s.prop) x.out
    exact ⟨-y, by dsimp; rw [neg_vadd_eq_iff]; dsimp at hy; exact hy.symm⟩
  rw [this]; exact Quotient.out_eq x

theorem eq_zero_iff_coeff_zero {p : ℕ} [Fact (Nat.Prime p)] (x : 𝕃_[p]) :
  x = 0 ↔ ∀ q ∈ x.support, x.coeff q = 0 := by
  have hfrom_zero : from_coeff (p := p) 0 (by simp) = (0 : 𝕃_[p]) := by
    have hlift_zero : LiftedPAdicHahnSeries.from_coeff (p := p) 0 (by simp) = 0 := by
      simpa [LiftedPAdicHahnSeries.from_coeff] using Eq.symm (Pi.zero_def : (0 : ℚ → ℤᵘⁿ_[p]) = 0)
    simpa [from_coeff] using congrArg (Ideal.Quotient.mk (NullSeriesIdeal p)) hlift_zero
  have hcoeff_zero : (0 : 𝕃_[p]).coeff = 0 := by
    rw [← hfrom_zero]
    exact coeff_of_from_coeff_eq_self 0 (by simp)
  constructor
  · intro hx q _
    simpa [hx] using congrArg (fun f : ℚ → Fpbar p => f q) hcoeff_zero
  · intro hx
    by_contra hne
    rcases support_nonempty_of_nonzero p x hne with ⟨q, hq⟩
    have hq_ne : x.coeff q ≠ 0 := by
      simpa [support, coeff, Function.mem_support] using hq
    exact hq_ne (hx q hq)

noncomputable def ZpUn_embd {p : ℕ} [Fact (Nat.Prime p)] : ℤᵘⁿ_[p] →+* 𝕃_[p] where
  toFun a := Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 a)
  map_one' := by simp
  map_mul' := by
    intro a b
    change Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 (a * b)) =
      Ideal.Quotient.mk (NullSeriesIdeal p) ((HahnSeries.single 0 a) * (HahnSeries.single 0 b))
    rw [HahnSeries.single_mul_single]
    simp
  map_zero' := by simp
  map_add' := by
    intro a b
    change Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 (a + b)) =
      Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 a + HahnSeries.single 0 b)
    rw [HahnSeries.single_add]

lemma ZpUn_embd_injective {p : ℕ} [Fact (Nat.Prime p)] :
  Function.Injective (ZpUn_embd (p := p)) := by
  intro a b hab
  have hmem0 : IsNullSeries (HahnSeries.single (0 : ℚ) a - HahnSeries.single (0 : ℚ) b) := by
    simpa [NullSeriesIdeal, ZpUn_embd, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] using
      (Ideal.Quotient.eq.mp hab)
  have hsingle : HahnSeries.single (0 : ℚ) a - HahnSeries.single (0 : ℚ) b =
    HahnSeries.single (0 : ℚ) (a - b) := by
    ext q
    by_cases hq : q = 0
    · simp only [HahnSeries.coeff_sub', Pi.sub_apply, HahnSeries.single_sub]
    · simp [HahnSeries.coeff_single_of_ne hq]
  have hmem := hmem0
  rw [hsingle] at hmem
  let s : ℕ → Finset ℤ := fun M =>
    Set.Finite.toFinset (finprop (HahnSeries.single (0 : ℚ) (a - b)) 0 M)
  let f : ℕ → QpUn p := fun M =>
    Finset.sum (s M).attach fun n =>
      (p : QpUn p) ^ n.val *
        algebraMap (OQpUn p) (QpUn p) ((HahnSeries.single (0 : ℚ) (a - b)).coeff (0 + n))
  have h0 : Filter.Tendsto f Filter.atTop (nhds 0) := by
    simpa [f, s] using hmem 0
  have hconst : f = fun _ : ℕ => algebraMap (OQpUn p) (QpUn p) (a - b) := by
    funext M
    classical
    unfold f
    by_cases hsub : a - b = 0
    · simp [hsub, s]
    · have hset : {n : ℤ | (0 : ℚ) + n ≤ M ∧
        (HahnSeries.single (0 : ℚ) (a - b)).coeff ((0 : ℚ) + n) ≠ 0} = {0} := by
        ext n
        constructor
        · intro hn
          have hz := HahnSeries.eq_of_mem_support_single <| (HahnSeries.mem_support _ _).2 hn.2
          have hn0 : n = 0 := by exact_mod_cast (by simpa using hz : (n : ℚ) = 0)
          simp [hn0]
        · intro hn
          rcases Set.mem_singleton_iff.mp hn with rfl
          simp [hsub]
      have hs : s M = ({0} : Finset ℤ) := by
        have hs' := (Set.Finite.toFinset_inj (hs := finprop (HahnSeries.single (0 : ℚ) (a - b)) 0 M)
          (ht := Set.finite_singleton (0 : ℤ))).2 hset
        simpa [s] using hs'
      rw [hs]
      have hatt : ({0} : Finset ℤ).attach = {⟨0, by simp⟩} := by
        ext x
        rcases x with ⟨x, hx⟩
        simp at hx
        simp [hx]
      simp [hatt]
  have ht : Filter.Tendsto (fun _ : ℕ => algebraMap (OQpUn p) (QpUn p) (a - b))
    Filter.atTop (nhds 0) := by
    simpa [hconst] using h0
  have hmap : algebraMap (OQpUn p) (QpUn p) (a - b) = 0 := by
    simpa using (tendsto_const_nhds_iff.mp ht)
  exact sub_eq_zero.mp <|
    (IsFractionRing.injective (R := OQpUn p) (K := QpUn p)) (by simpa using hmap)

noncomputable def QpUn_embd {p : ℕ} [Fact (Nat.Prime p)] : ℚᵘⁿ_[p] →+* 𝕃_[p] :=
  IsFractionRing.map (j := ZpUn_embd (p := p)) ZpUn_embd_injective

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Algebra ℚᵘⁿ_[p] 𝕃_[p] := QpUn_embd.toAlgebra

end pAdicHahnSeries
end Poonen1993

namespace QpUn

noncomputable abbrev to_Lp {p : ℕ} [Fact (Nat.Prime p)] : ℚᵘⁿ_[p] →+* 𝕃_[p] :=
  Poonen1993.pAdicHahnSeries.QpUn_embd

lemma mem_QpUn_iff_supp_int {p : ℕ} [Fact (Nat.Prime p)] (x : 𝕃_[p]) :
  ∀ q ∈ x.support, q.isInt ↔ ∃ y : ℚᵘⁿ_[p], y.to_Lp = x := by
  sorry

end QpUn

namespace Poonen1993
namespace pAdicHahnSeries

instance (p : ℕ) [Fact (Nat.Prime p)] : IsAlgClosed (𝕃_[p]) := by admit

variable (p : ℕ) [Fact (Nat.Prime p)]

noncomputable def alg_Cp_embd {p : ℕ} [Fact (Nat.Prime p)] : ℂ_[p] →ₐ[ℚᵘⁿ_[p]] 𝕃_[p] :=
  @IsAlgClosed.lift 𝕃_[p] _ _ ℚᵘⁿ_[p] _ _ ℂ_[p] _ _ _ _ _ _ _

noncomputable def Cp_embd {p : ℕ} [Fact (Nat.Prime p)] : ℂ_[p] →+* 𝕃_[p] :=
  alg_Cp_embd.toRingHom

open Classical in
noncomputable def abs {p : ℕ} [Fact (Nat.Prime p)] : AbsoluteValue 𝕃_[p] ℝ where
  toFun a := WithZeroRat.toNNReal (pInv_ne_zero p) (Valued.v a)
  map_mul' := by admit
  nonneg' := by admit
  eq_zero' := by admit
  add_le' := by admit

open Classical in
lemma abs_def (p : ℕ) [Fact (Nat.Prime p)] (a : 𝕃_[p]) :
  abs a = WithZeroRat.toNNReal (pInv_ne_zero p) (Valued.v a) := rfl

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : NormedField 𝕃_[p] :=
  WithAbs.normedField abs

theorem QpUn_embd_keep_val (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ x : ℚᵘⁿ_[p],
    WithZero.map' (AddMonoidHom.toMultiplicative (Int.castAddHom ℚ)) (Valued.v x) =
      Valued.v (QpUn_embd x) := by
  admit

theorem QpUn_embd_keep_norm (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ x : ℚᵘⁿ_[p], ‖x‖ = ‖(QpUn_embd x)‖ := by
  admit

theorem Cp_embd_keep_norm (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ y : ℂ_[p], ‖y‖ = ‖(Cp_embd y)‖ := by
  admit

theorem Cp_embd_keep_val (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ y : ℂ_[p],
    Valued.v y =
      WithZeroRat.toNNReal (pInv_ne_zero p) (Valued.v (Cp_embd y)) := by
  intro y
  have h := Cp_embd_keep_norm p y
  change ((Valued.v y : NNReal) : ℝ) = abs (Cp_embd y) at h
  simp [abs_def] at h
  convert h using 2
  simp [one_div]

def IsHyperAlgebraic {p : ℕ} [Fact (Nat.Prime p)] (x : 𝕃_[p]) : Prop :=
  (∃ T : ℕ, ∀ q ∈ x.support, ∃ k : ℕ, (T * (p ^ k) * q).isInt) ∧
  (Set.image x.coeff x.support).Finite

def HyperAlgebraicSubfield (p : ℕ) [Fact (Nat.Prime p)] : Subfield (𝕃_[p]) where
  carrier := {x | IsHyperAlgebraic x}
  zero_mem' := by admit
  one_mem' := by admit
  add_mem' := by admit
  mul_mem' := by admit
  neg_mem' := by admit
  inv_mem' := by admit

theorem HyperAlgebraicSubfield_isAlgClosed (p : ℕ) [Fact (Nat.Prime p)] :
  IsAlgClosed (HyperAlgebraicSubfield p) := by
  admit

theorem HyperAlgebraicSubfield_include_Qp (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ x : ℚ_[p], IsHyperAlgebraic x.to_QpUn.to_Lp := by
  admit

theorem HyperAlgebraicSubfield_include_PadicAlgCl (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ x : (PadicAlgCl p), IsHyperAlgebraic (Cp_embd (p := p) x) := by
  admit

end pAdicHahnSeries
end Poonen1993
