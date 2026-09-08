/-
Copyright (c) 2025 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Yijun Yuan
-/
module

public import TrustworthyKedlaya.Lp.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# T-scaled realization of `p`-adic Hahn series

This file formalizes Section 4 of the paper. It builds the `T`-scaled realization of `𝕃_[p]`,
obtained by adjoining a `T`-th root `p^(1/T)` of `p`, and establishes the isomorphism
`𝕃_[p] ≅ W(𝔽ᵃ_[p])((t^ℚ))[p^(1/T)] / N_T`. Most proofs parallel those in `PAdicHahnSeries.lean`.

## Main definitions

- `FormalizedSparse.TScaled.OQpCUnT` (`ℤᶜᵘⁿ_[p,T]`): the ring `W(𝔽ᵃ_[p])[p^(1/T)]` via `AdjoinRoot`.
- `FormalizedSparse.TScaled.TScaledNullSeries`: the `T`-null-series ideal `N_T`.

## Main statements

- `FormalizedSparse.TScaled.sigma_iso`: the isomorphism
  `σ : 𝕃_[p] → W(𝔽ᵃ_[p])[p^(1/T)]((t^ℚ)) / N_T`.

## Notation

- `ℤᶜᵘⁿ_[p,T]`, `ℚᶜᵘⁿ_[p,T]` for the `T`-scaled rings introduced here.

## Tags

p-adic, Hahn series, T-scaled, adjoin root, null series
-/

@[expose] public section

open WittVector

namespace FormalizedSparse

open TrustworthyKedlaya

namespace TScaled

variable (p : ℕ) [Fact (Nat.Prime p)] (T : ℕ) [NeZero T]

/-! ### The rings `ℤᶜᵘⁿ_[p,T]` and `ℚᶜᵘⁿ_[p,T]` -/

/-- The polynomial `X^T - p` over `ℤᶜᵘⁿ_[p]`, used to adjoin a `T`-th root of `p`. -/
noncomputable def TPoly : Polynomial (ℤᶜᵘⁿ_[p]) :=
  Polynomial.X ^ T - Polynomial.C ((p : ℕ) : ℤᶜᵘⁿ_[p])

/-- The ring `W(𝔽ₚ^⁻)[p^{1/T}]`, realised as `AdjoinRoot (X^T - p)`. -/
abbrev OQpCUnT : Type _ := AdjoinRoot (TPoly p T)

@[inherit_doc] notation "ℤᶜᵘⁿ_[" p "," T "]" => OQpCUnT p T

/-- The canonical root `p^{1/T}` of `X^T - p` inside `ℤᶜᵘⁿ_[p,T]`. -/
noncomputable def pInvT : ℤᶜᵘⁿ_[p,T] := AdjoinRoot.root (TPoly p T)

omit [NeZero T] in
/-- The defining relation `(p^{1/T})^T = p`. -/
lemma pInvT_pow_T :
    (pInvT p T) ^ T =
      (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) ((p : ℕ) : ℤᶜᵘⁿ_[p]) := by
  have h := AdjoinRoot.eval₂_root (TPoly p T)
  unfold TPoly at h
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, sub_eq_zero] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact h

/-- `TPoly p T = X^T - C p` is monic. -/
private lemma TPoly_monic : (TPoly p T).Monic := by
  unfold TPoly
  exact Polynomial.monic_X_pow_sub_C _ (NeZero.ne T)

omit [NeZero T] in
/-- `TPoly p T` has natural degree `T`. -/
private lemma TPoly_natDegree : (TPoly p T).natDegree = T := by
  unfold TPoly; exact Polynomial.natDegree_X_pow_sub_C

/-- `TPoly p T` is Eisenstein at the maximal ideal of `ℤᶜᵘⁿ_[p]`. -/
private lemma TPoly_isEisensteinAt :
    (TPoly p T).IsEisensteinAt (IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p])) := by
  have hp_ne : ((p : ℕ) : ℤᶜᵘⁿ_[p]) ≠ 0 := WittVector.p_nonzero p _
  have hT_ne : T ≠ 0 := NeZero.ne T
  have hM_eq : IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) =
      Ideal.span {((p : ℕ) : ℤᶜᵘⁿ_[p])} := (WittVector.irreducible p).maximalIdeal_eq
  refine (TPoly_monic p T).isEisensteinAt_of_mem_of_notMem ?_ ?_ ?_
  · exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  · intro n hn
    rw [TPoly_natDegree] at hn
    have hcoeff : (TPoly p T).coeff n =
        (if n = T then 1 else 0) - (if n = 0 then ((p : ℕ) : ℤᶜᵘⁿ_[p]) else 0) := by
      unfold TPoly
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    rw [hcoeff, hM_eq]
    have hnT : n ≠ T := Nat.ne_of_lt hn
    by_cases hn0 : n = 0
    · subst hn0
      have hT0 : (0 : ℕ) ≠ T := fun h => hT_ne h.symm
      simp only [hT0, if_false, if_true, zero_sub]
      exact (Ideal.span {((p : ℕ) : ℤᶜᵘⁿ_[p])}).neg_mem
        (Ideal.subset_span (Set.mem_singleton _))
    · simp [hnT, hn0]
  · -- coeff 0 of `X^T - C p` is `-p`; show `-p ∉ maximalIdeal^2`.
    have h0 : (TPoly p T).coeff 0 = -((p : ℕ) : ℤᶜᵘⁿ_[p]) := by
      unfold TPoly
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      simp [hT_ne.symm]
    rw [h0]
    intro hmem
    have hmem' : ((p : ℕ) : ℤᶜᵘⁿ_[p]) ∈
        (IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p])) ^ 2 := by
      have h := (IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) ^ 2).neg_mem hmem
      simpa using h
    rw [hM_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hmem'
    obtain ⟨r, hr⟩ := hmem'
    -- p = p^2 * r ⇒ p * (1 - p*r) = 0 ⇒ since p ≠ 0, p*r = 1, so p is a unit, contradiction.
    have hzero : ((p : ℕ) : ℤᶜᵘⁿ_[p]) * (1 - ((p : ℕ) : ℤᶜᵘⁿ_[p]) * r) = 0 := by
      have : ((p : ℕ) : ℤᶜᵘⁿ_[p]) - ((p : ℕ) : ℤᶜᵘⁿ_[p]) ^ 2 * r = 0 := by
        rw [← hr]; ring
      linear_combination this
    rcases mul_eq_zero.mp hzero with h | h
    · exact hp_ne h
    · have hpr : ((p : ℕ) : ℤᶜᵘⁿ_[p]) * r = 1 := by
        have hh : 1 - ((p : ℕ) : ℤᶜᵘⁿ_[p]) * r = 0 := h
        linear_combination -hh
      have hunit : IsUnit ((p : ℕ) : ℤᶜᵘⁿ_[p]) :=
        IsUnit.of_mul_eq_one (a := ((p : ℕ) : ℤᶜᵘⁿ_[p])) r hpr
      exact (WittVector.irreducible p).not_isUnit hunit

/-- `TPoly p T` is irreducible. -/
private lemma TPoly_irreducible : Irreducible (TPoly p T) := by
  apply (TPoly_isEisensteinAt p T).irreducible
  · exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  · exact (TPoly_monic p T).isPrimitive
  · rw [TPoly_natDegree]; exact (NeZero.pos T)

/-- `ℤᶜᵘⁿ_[p,T]` is a domain.
The argument: `X^T - p` is Eisenstein at the maximal ideal of the DVR `ℤᶜᵘⁿ_[p]`, hence
irreducible, hence the quotient `AdjoinRoot (X^T - p)` is an integral domain.  This is the same
content as Lemma 4.1. -/
instance instIsDomainOQpCUnT : IsDomain (ℤᶜᵘⁿ_[p,T]) := by
  apply AdjoinRoot.isDomain_of_prime
  exact (UniqueFactorizationMonoid.irreducible_iff_prime).mp (TPoly_irreducible p T)

/-! ### Lemma 4.1 (continued) — `ℤᶜᵘⁿ_[p,T]` is a discrete valuation ring -/

/-- `pInvT p T` is nonzero. Proof: `(pInvT)^T = algebraMap p` is nonzero in `S`, since `p` is
nonzero in `R` and `algebraMap` is injective. -/
private lemma pInvT_ne_zero : pInvT p T ≠ 0 := by
  intro h
  have h1 : (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) ((p : ℕ) : ℤᶜᵘⁿ_[p]) = 0 := by
    rw [← pInvT_pow_T, h, zero_pow (NeZero.ne T)]
  have hinj : Function.Injective (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) := by
    rw [AdjoinRoot.algebraMap_eq]
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree (TPoly_monic p T).ne_zero, TPoly_natDegree]
    exact_mod_cast NeZero.ne T
  have h2 : ((p : ℕ) : ℤᶜᵘⁿ_[p]) = 0 :=
    hinj (by rw [h1, map_zero])
  exact WittVector.p_nonzero p _ h2

/-- The residue map `ρ : ℤᶜᵘⁿ_[p,T] →+* IsLocalRing.ResidueField (ℤᶜᵘⁿ_[p])` obtained
by lifting the quotient `ℤᶜᵘⁿ_[p] →+* (ℤᶜᵘⁿ_[p])/m` along the relation `(pInvT)^T = p`.
Sends `pInvT` to `0`. -/
private noncomputable def TResidue :
    ℤᶜᵘⁿ_[p,T] →+* IsLocalRing.ResidueField (ℤᶜᵘⁿ_[p]) :=
  AdjoinRoot.lift (IsLocalRing.residue (ℤᶜᵘⁿ_[p])) 0 (by
    -- Show `(TPoly p T).eval₂ residue 0 = 0`.
    unfold TPoly
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      zero_pow (NeZero.ne T), zero_sub, neg_eq_zero]
    -- The residue of `p` in the residue field is zero because `p` lies in the max ideal.
    have hM_eq : IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) =
        Ideal.span {((p : ℕ) : ℤᶜᵘⁿ_[p])} := (WittVector.irreducible p).maximalIdeal_eq
    change (IsLocalRing.residue (ℤᶜᵘⁿ_[p])) ((p : ℕ) : ℤᶜᵘⁿ_[p]) = 0
    rw [IsLocalRing.residue_eq_zero_iff, hM_eq]
    exact Ideal.subset_span (Set.mem_singleton _))

private lemma TResidue_pInvT : TResidue p T (pInvT p T) = 0 := by
  unfold TResidue pInvT
  exact AdjoinRoot.lift_root _

private lemma TResidue_of (a : ℤᶜᵘⁿ_[p]) :
    TResidue p T (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) a) =
      IsLocalRing.residue (ℤᶜᵘⁿ_[p]) a := by
  unfold TResidue
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of]

/-- The kernel of the residue map equals the principal ideal generated by `pInvT`.
This is the power-basis kernel calculation. -/
private lemma TResidue_eq_zero_iff (x : ℤᶜᵘⁿ_[p,T]) :
    TResidue p T x = 0 ↔ pInvT p T ∣ x := by
  constructor
  · intro hx
    set f := TPoly p T with hf_def
    have hf_monic : f.Monic := TPoly_monic p T
    set q : Polynomial (ℤᶜᵘⁿ_[p]) := AdjoinRoot.modByMonicHom hf_monic x with hq_def
    have hq : AdjoinRoot.mk f q = x := AdjoinRoot.mk_leftInverse hf_monic x
    have hRes : TResidue p T x =
        IsLocalRing.residue (ℤᶜᵘⁿ_[p]) (q.coeff 0) := by
      rw [← hq]
      change AdjoinRoot.lift (IsLocalRing.residue (ℤᶜᵘⁿ_[p])) 0 _ (AdjoinRoot.mk f q) = _
      rw [AdjoinRoot.lift_mk, Polynomial.eval₂_eq_eval_map,
        ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
    rw [hRes, IsLocalRing.residue_eq_zero_iff] at hx
    have hM_eq : IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) =
        Ideal.span {((p : ℕ) : ℤᶜᵘⁿ_[p])} := (WittVector.irreducible p).maximalIdeal_eq
    rw [hM_eq, Ideal.mem_span_singleton] at hx
    obtain ⟨b, hb⟩ := hx
    have hq_split : Polynomial.X * q.divX + Polynomial.C (q.coeff 0) = q :=
      Polynomial.X_mul_divX_add q
    have hxeq : x = pInvT p T * AdjoinRoot.mk f q.divX +
        algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (q.coeff 0) := by
      conv_lhs => rw [← hq, ← hq_split]
      rw [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
      rfl
    rw [hxeq, hb]
    have hpπT : algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (((p : ℕ) : ℤᶜᵘⁿ_[p]) * b) =
        (pInvT p T) ^ T * algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) b := by
      rw [map_mul]
      congr 1
      exact (pInvT_pow_T p T).symm
    rw [hpπT]
    refine ⟨AdjoinRoot.mk f q.divX +
      (pInvT p T) ^ (T - 1) * algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) b, ?_⟩
    have hT_split : (pInvT p T) ^ T = pInvT p T * (pInvT p T) ^ (T - 1) := by
      conv_rhs => rw [← pow_succ', Nat.sub_add_cancel (NeZero.pos T)]
    rw [hT_split]; ring
  · rintro ⟨y, rfl⟩
    rw [map_mul, TResidue_pInvT, zero_mul]

/-- `pInvT p T` is irreducible. -/
private lemma pInvT_irreducible : Irreducible (pInvT p T) := by
  have hπ_ne : pInvT p T ≠ 0 := pInvT_ne_zero p T
  refine ⟨?_, ?_⟩
  · intro hu
    have h0 : TResidue p T (pInvT p T) = 0 := TResidue_pInvT p T
    have hu' : IsUnit (TResidue p T (pInvT p T)) := hu.map _
    rw [h0] at hu'
    exact not_isUnit_zero hu'
  · intro a b hab
    have h0 : TResidue p T (a * b) = 0 := by rw [← hab, TResidue_pInvT]
    rw [map_mul] at h0
    rcases mul_eq_zero.mp h0 with ha0 | hb0
    · obtain ⟨c, rfl⟩ := (TResidue_eq_zero_iff p T a).mp ha0
      have hcb : c * b = 1 := by
        have h1 : pInvT p T * (c * b) = pInvT p T * 1 := by
          rw [mul_one]; linear_combination -hab
        exact mul_left_cancel₀ hπ_ne h1
      have hbc : b * c = 1 := by rw [mul_comm]; exact hcb
      exact Or.inr (IsUnit.of_mul_eq_one c hbc)
    · obtain ⟨c, rfl⟩ := (TResidue_eq_zero_iff p T b).mp hb0
      have hac : a * c = 1 := by
        have h1 : pInvT p T * (a * c) = pInvT p T * 1 := by
          rw [mul_one]; linear_combination -hab
        exact mul_left_cancel₀ hπ_ne h1
      exact Or.inl (IsUnit.of_mul_eq_one c hac)

/-- `(pInvT)` is a maximal ideal: `S/(pInvT) ≅ ResidueField R` is a field. -/
private lemma pInvT_maximal :
    (Ideal.span {pInvT p T} : Ideal (ℤᶜᵘⁿ_[p,T])).IsMaximal := by
  -- The kernel of TResidue equals span {pInvT}, and TResidue is surjective onto a field.
  have hker : RingHom.ker (TResidue p T) = Ideal.span {pInvT p T} := by
    ext x
    rw [RingHom.mem_ker, TResidue_eq_zero_iff, Ideal.mem_span_singleton]
  have hsurj : Function.Surjective (TResidue p T) := by
    intro y
    -- Every element of the residue field is the residue of some r : R; lift via algebraMap.
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) r, ?_⟩
    rw [TResidue_of]; exact hr
  -- S/(pInvT) ≅ ResidueField R via lift.
  have hquot_field :
      (Ideal.span {pInvT p T} : Ideal (ℤᶜᵘⁿ_[p,T])).IsMaximal := by
    rw [← hker]
    exact RingHom.ker_isMaximal_of_surjective (TResidue p T) hsurj
  exact hquot_field

/-- `ℤᶜᵘⁿ_[p,T]` is a local ring with maximal ideal `(pInvT)`. -/
private lemma instLocalRingOQpCUnT : IsLocalRing (ℤᶜᵘⁿ_[p,T]) := by
  refine IsLocalRing.of_unique_max_ideal ?_
  refine ⟨Ideal.span {pInvT p T}, pInvT_maximal p T, ?_⟩
  intro M hM
  have hint : Algebra.IsIntegral (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) := by
    have := (TPoly_monic p T).finite_adjoinRoot
    exact Algebra.IsIntegral.of_finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])
  have hMmax : M.IsMaximal := hM
  have hMcomap_max : (M.comap (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  have hMcomap_eq : M.comap (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) =
      IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) :=
    IsLocalRing.eq_maximalIdeal hMcomap_max
  have hpR_mem : (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) ((p : ℕ) : ℤᶜᵘⁿ_[p]) ∈ M := by
    have : ((p : ℕ) : ℤᶜᵘⁿ_[p]) ∈ M.comap (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) := by
      rw [hMcomap_eq]
      have hM_eq : IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p]) =
          Ideal.span {((p : ℕ) : ℤᶜᵘⁿ_[p])} := (WittVector.irreducible p).maximalIdeal_eq
      rw [hM_eq]; exact Ideal.subset_span (Set.mem_singleton _)
    exact Ideal.mem_comap.mp this
  have hπpow_mem : (pInvT p T) ^ T ∈ M := by
    rw [pInvT_pow_T]; exact hpR_mem
  have hπ_mem : pInvT p T ∈ M := hM.isPrime.mem_of_pow_mem T hπpow_mem
  have hsub : Ideal.span {pInvT p T} ≤ M := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hπ_mem
  exact ((pInvT_maximal p T).eq_of_le hM.ne_top hsub).symm

/-- All elements of a multiset associated to a fixed element have product associated to a power. -/
private lemma _root_.Multiset.prod_assoc_pow {α : Type*} [CommMonoid α] (m : Multiset α) (a : α)
    (h : ∀ q ∈ m, Associated q a) : Associated m.prod (a ^ Multiset.card m) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons q m' ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ']
    exact (h q (Multiset.mem_cons_self q m')).mul_mul
      (ih (fun r hr => h r (Multiset.mem_cons_of_mem hr)))

/-- Every nonzero `x : ℤᶜᵘⁿ_[p,T]` factors as `(pInvT)^n * u` for some unit `u`.
This is the existence half of `HasUnitMulPowIrreducibleFactorization`. -/
private lemma exists_pInvT_pow_unit_decomposition (x : ℤᶜᵘⁿ_[p,T]) (hx : x ≠ 0) :
    ∃ (n : ℕ), Associated ((pInvT p T) ^ n) x := by
  have : IsLocalRing (ℤᶜᵘⁿ_[p,T]) := instLocalRingOQpCUnT p T
  have : Module.Finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) := (TPoly_monic p T).finite_adjoinRoot
  have : IsNoetherian (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
    isNoetherian_of_isNoetherianRing_of_finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])
  have : IsNoetherianRing (ℤᶜᵘⁿ_[p,T]) := by
    refine isNoetherianRing_of_surjective (Polynomial (ℤᶜᵘⁿ_[p])) (ℤᶜᵘⁿ_[p,T])
      (AdjoinRoot.mk (TPoly p T)) ?_
    exact AdjoinRoot.mk_surjective
  have : WfDvdMonoid (ℤᶜᵘⁿ_[p,T]) := IsNoetherianRing.wfDvdMonoid
  obtain ⟨fx, hfx⟩ := WfDvdMonoid.exists_factors x hx
  refine ⟨Multiset.card fx, ?_⟩
  have hπ_irr : Irreducible (pInvT p T) := pInvT_irreducible p T
  have hassoc_each : ∀ q ∈ fx, Associated q (pInvT p T) := by
    intro q hq
    have hq_irr : Irreducible q := hfx.1 q hq
    -- q is irreducible, hence not a unit, hence in the unique maximal ideal = span {pInvT}
    have hq_nu : ¬ IsUnit q := hq_irr.not_isUnit
    have hπ_max : (IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])) = Ideal.span {pInvT p T} := by
      have hmax := pInvT_maximal p T
      exact (IsLocalRing.eq_maximalIdeal hmax).symm
    have hq_mem : q ∈ Ideal.span {pInvT p T} := by
      rw [← hπ_max]; exact hq_nu
    rw [Ideal.mem_span_singleton] at hq_mem
    obtain ⟨y, hy⟩ := hq_mem
    rcases hq_irr.isUnit_or_isUnit hy with hu | hu
    · exact absurd hu (pInvT_irreducible p T).not_isUnit
    · -- q = pInvT * y, y is a unit, hence Associated q pInvT.
      obtain ⟨v, hv⟩ := hu
      refine ⟨v⁻¹, ?_⟩
      rw [hy, mul_assoc, ← hv, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hprod_assoc : Associated fx.prod ((pInvT p T) ^ (Multiset.card fx)) :=
    Multiset.prod_assoc_pow fx (pInvT p T) hassoc_each
  exact hprod_assoc.symm.trans hfx.2

instance instDVROQpCUnT : IsDiscreteValuationRing (ℤᶜᵘⁿ_[p,T]) := by
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨pInvT p T, pInvT_irreducible p T, ?_⟩
  intro x hx
  exact exists_pInvT_pow_unit_decomposition p T x hx

/-- `ℚᶜᵘⁿ_[p,T]` := the fraction field of `ℤᶜᵘⁿ_[p,T]`, equipped with the `(pInvT)`-adic
valuation via the `WithVal` wrapper (mirroring the `QpCUn` convention from
`WittVector.lean:21`). The `Valued (ℚᶜᵘⁿ_[p,T]) (WithZero (Multiplicative ℤ))` instance is
synthesised automatically by `WithVal.instValued`. -/
abbrev QpCUnT : Type _ :=
  WithVal ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation
    (FractionRing (ℤᶜᵘⁿ_[p,T])))

@[inherit_doc] notation "ℚᶜᵘⁿ_[" p "," T "]" => QpCUnT p T

/-- Sanity check: the `WithVal` wrapping of the maximal-ideal valuation gives the desired
`Valued (ℚᶜᵘⁿ_[p,T])` instance via instance synthesis. -/
noncomputable example : Valued (ℚᶜᵘⁿ_[p,T]) (WithZero (Multiplicative ℤ)) := inferInstance

/-- The element `p^{1/T}` viewed inside the fraction field `ℚᶜᵘⁿ_[p,T]`. -/
noncomputable def pInvTQ : ℚᶜᵘⁿ_[p,T] :=
  algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (pInvT p T)

/-- The valuation of the uniformizer `pInvTQ p T` (a `T`-th root of `p`) is `ofAdd(-1)` — the
`T`-scaled analogue of `valued_v_p`. -/
lemma valued_v_pInvT :
    Valued.v (pInvTQ p T) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
  unfold pInvTQ
  rw [WithVal.algebraMap_right_apply, WithVal.valued_toVal,
    (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_of_algebraMap]
  have hirr : Irreducible (pInvT p T) := pInvT_irreducible p T
  have hpe : (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).asIdeal =
      Ideal.span {pInvT p T} := hirr.maximalIdeal_eq
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
    (pInvT_ne_zero p T) hpe]
  rfl

/-- The valuation of `(pInvTQ p T)^n` is `ofAdd(-n)` for integer `n`. -/
lemma valued_v_pInvT_zpow (n : ℤ) :
    Valued.v ((pInvTQ p T) ^ n) =
      ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
  have hzpow : Valued.v ((pInvTQ p T) ^ n) = (Valued.v (pInvTQ p T)) ^ n :=
    map_zpow₀ Valued.v _ _
  rw [hzpow, valued_v_pInvT, ← WithZero.coe_zpow]
  congr 1
  rw [← ofAdd_zsmul n (-1 : ℤ)]
  congr 1
  ring

-- v4.31 `WithVal`-migration helpers (analogues of those in `PAdicHahnSeries.lean`): the valued
-- nhds basis is now phrased via `MonoidWithZeroHom.ValueGroup₀`, so we package the bridges once.

/-- The open ball `{y | v(y) < c}` is a neighbourhood of `0` in `ℚᶜᵘⁿ_[p,T]` for any nonzero `c` —
the `T`-scaled analogue of `mem_nhds_zero_v_lt`. -/
lemma Tmem_nhds_zero_v_lt {c : WithZero (Multiplicative ℤ)} (hc : c ≠ 0) :
    {y : ℚᶜᵘⁿ_[p,T] | Valued.v y < c} ∈ nhds (0 : ℚᶜᵘⁿ_[p,T]) := by
  rw [Valued.mem_nhds]
  have hva : Valued.v ((pInvTQ p T) ^ (-(WithZero.log c))) = c := by
    rw [valued_v_pInvT_zpow, neg_neg, ← WithZero.exp_eq_coe_ofAdd, WithZero.exp_log hc]
  have hane : Valued.v.restrict ((pInvTQ p T) ^ (-(WithZero.log c))) ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hva]; exact hc
  refine ⟨Units.mk0 (Valued.v.restrict ((pInvTQ p T) ^ (-(WithZero.log c)))) hane, ?_⟩
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, sub_zero, Units.val_mk0,
    Valuation.embedding_restrict, hva] at hy
  exact hy

/-- Every neighbourhood `U` of `0` in `ℚᶜᵘⁿ_[p,T]` contains a valuation ball `{y | v(y) < c}` for
some nonzero `c`. -/
lemma Texists_v_lt_subset {U : Set (ℚᶜᵘⁿ_[p,T])} (hU : U ∈ nhds (0 : ℚᶜᵘⁿ_[p,T])) :
    ∃ c : WithZero (Multiplicative ℤ), c ≠ 0 ∧ {y : ℚᶜᵘⁿ_[p,T] | Valued.v y < c} ⊆ U := by
  rw [Valued.mem_nhds] at hU
  obtain ⟨γ, hγ⟩ := hU
  refine ⟨MonoidWithZeroHom.ValueGroup₀.embedding γ.1,
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ, ?_⟩
  intro y hy
  apply hγ
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, sub_zero]
  exact hy

/-- Given a witness `w` with `v(w) = c ≠ 0`, the ball `{y | v(y - x) < c}` is a neighbourhood of
`x` in `ℚᶜᵘⁿ_[p,T]`. -/
lemma Tmem_nhds_v_sub_lt {x w : ℚᶜᵘⁿ_[p,T]} {c : WithZero (Multiplicative ℤ)}
    (hc : c ≠ 0) (hw : Valued.v w = c) :
    {y : ℚᶜᵘⁿ_[p,T] | Valued.v (y - x) < c} ∈ nhds x := by
  rw [Valued.mem_nhds]
  have hane : Valued.v.restrict w ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hw]; exact hc
  refine ⟨Units.mk0 (Valued.v.restrict w) hane, ?_⟩
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, Units.val_mk0,
    Valuation.embedding_restrict, hw] at hy
  exact hy

/-- Every neighbourhood `U` of `x` in `ℚᶜᵘⁿ_[p,T]` contains a ball `{y | v(y - x) < c}` for some
nonzero `c`. -/
lemma Texists_v_sub_lt_subset {U : Set (ℚᶜᵘⁿ_[p,T])} {x : ℚᶜᵘⁿ_[p,T]} (hU : U ∈ nhds x) :
    ∃ c : WithZero (Multiplicative ℤ), c ≠ 0 ∧ {y : ℚᶜᵘⁿ_[p,T] | Valued.v (y - x) < c} ⊆ U := by
  rw [Valued.mem_nhds] at hU
  obtain ⟨γ, hγ⟩ := hU
  refine ⟨MonoidWithZeroHom.ValueGroup₀.embedding γ.1,
    MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ, ?_⟩
  intro y hy
  apply hγ
  simp only [Set.mem_ofPred_eq] at hy ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact hy

/-! ### Inclusions `ℤᶜᵘⁿ_[p] ↪ ℤᶜᵘⁿ_[p,T]` and `ℚᶜᵘⁿ_[p] ↪ ℚᶜᵘⁿ_[p,T]` -/

/-- The natural ring inclusion `ℤᶜᵘⁿ_[p] ↪ ℤᶜᵘⁿ_[p,T]`. -/
noncomputable def OQpCUn_embd : ℤᶜᵘⁿ_[p] →+* ℤᶜᵘⁿ_[p,T] :=
  algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])

/-- The inclusion `ℤᶜᵘⁿ_[p] ↪ ℤᶜᵘⁿ_[p,T]` is injective.  Follows from Lemma 4.1
(`X^T - p` has positive degree, hence the quotient algebra is free of rank `T`). -/
lemma OQpCUn_embd_injective : Function.Injective (OQpCUn_embd p T) := by
  unfold OQpCUn_embd
  rw [AdjoinRoot.algebraMap_eq]
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  rw [Polynomial.degree_eq_natDegree (TPoly_monic p T).ne_zero, TPoly_natDegree]
  exact_mod_cast NeZero.ne T

/-- The natural field inclusion `ℚᶜᵘⁿ_[p] ↪ ℚᶜᵘⁿ_[p,T]`, obtained by extending
`OQpCUn_embd` to the fraction fields. -/
noncomputable def QpCUn_embd : ℚᶜᵘⁿ_[p] →+* ℚᶜᵘⁿ_[p,T] :=
  IsFractionRing.lift (A := ℤᶜᵘⁿ_[p]) (K := ℚᶜᵘⁿ_[p]) (L := ℚᶜᵘⁿ_[p,T])
    (g := (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])).comp (OQpCUn_embd p T))
    (((IsFractionRing.injective (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])).comp
      (OQpCUn_embd_injective p T)))

/-- View `ℚᶜᵘⁿ_[p,T]` as a `ℚᶜᵘⁿ_[p]`-algebra via `QpCUn_embd`. -/
noncomputable instance : Algebra (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) :=
  (QpCUn_embd p T).toAlgebra

/-- The natural scalar-tower `ℤᶜᵘⁿ_[p] → ℚᶜᵘⁿ_[p] → ℚᶜᵘⁿ_[p,T]` via the localization
square plus the Eisenstein extension. Promoted to a global instance because the closure
construction `Module.Basis.localizationLocalization` (used in Lemma 4.8) requires it. -/
instance instIsScalarTowerOQpCUnQpCUnQpCUnT :
    IsScalarTower (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) x =
    QpCUn_embd p T (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) x)
  have hL : (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) x =
      (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])) (OQpCUn_embd p T x) := by
    rw [show (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) =
        (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])).comp (OQpCUn_embd p T) from ?_]
    · rfl
    · ext y
      change (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) y =
        (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])) ((OQpCUn_embd p T) y)
      unfold OQpCUn_embd
      exact IsScalarTower.algebraMap_apply (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) y
  rw [hL]
  rw [show QpCUn_embd p T (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) x) =
      ((algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])).comp (OQpCUn_embd p T)) x from
    IsFractionRing.lift_algebraMap _ x]
  rfl

/-- `ℤᶜᵘⁿ_[p,T]` is module-finite over `ℤᶜᵘⁿ_[p]` (it is `R₀`-free of rank `T`). Promoted to
a global instance so Lemma 4.8 helpers do not have to re-derive it from
`AdjoinRoot.powerBasis'`. -/
instance instModuleFiniteOQpCUnT : Module.Finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
  (AdjoinRoot.powerBasis' (TPoly_monic p T)).finite

instance instFaithfulSMulOQpCUnT : FaithfulSMul (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (OQpCUn_embd_injective p T)

instance instAlgebraIsAlgebraicOQpCUnT : Algebra.IsAlgebraic (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
  Algebra.IsAlgebraic.of_finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])

/-- `ℚᶜᵘⁿ_[p,T]` is a localization of `ℤᶜᵘⁿ_[p,T]` at the image of nonzero divisors of
`ℤᶜᵘⁿ_[p]`. Promoted to a global instance so `Module.Basis.localizationLocalization` synthesises
without per-call typeclass-search timeouts. -/
instance instIsLocalizationOQpCUnTQpCUnT :
    IsLocalization (Algebra.algebraMapSubmonoid (ℤᶜᵘⁿ_[p,T])
      (nonZeroDivisors (ℤᶜᵘⁿ_[p]))) (ℚᶜᵘⁿ_[p,T]) :=
  Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors _ _ _

/-- `ℚᶜᵘⁿ_[p,T]` is module-finite over `ℚᶜᵘⁿ_[p]` (it inherits the rank-`T` basis from
`ℤᶜᵘⁿ_[p,T]`). Promoted to a global instance so `LinearMap.continuous_of_finiteDimensional`
fires without typeclass-search timeouts. -/
instance instModuleFiniteQpCUnT : Module.Finite (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) := by
  have hpb : Module.Finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
    (AdjoinRoot.powerBasis' (TPoly_monic p T)).finite
  exact Module.Finite.of_isLocalization (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])
    (Rₚ := ℚᶜᵘⁿ_[p]) (Sₚ := ℚᶜᵘⁿ_[p,T]) (nonZeroDivisors (ℤᶜᵘⁿ_[p]))

/-! ### Lemma 4.1 — Eisenstein criterion / degree formula -/

/-- **Lemma 4.1.**  `[ℚᶜᵘⁿ_[p,T] : ℚᶜᵘⁿ_[p]] = T`.

Equivalently, `1, p^{1/T}, …, p^{(T-1)/T}` form a basis of `ℚᶜᵘⁿ_[p,T]` over `ℚᶜᵘⁿ_[p]`.
The proof uses the Eisenstein criterion for general DVFs (`X^T - p` is Eisenstein at the
maximal ideal of the DVR `ℤᶜᵘⁿ_[p]`). -/
theorem rank_QpCUnT_over_QpCUn :
    Module.finrank (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) = T := by
  -- Step 1: rank of `ℤᶜᵘⁿ_[p,T]` over `ℤᶜᵘⁿ_[p]` equals `T` via the AdjoinRoot power basis.
  have hpb : Module.finrank (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) = T := by
    rw [(AdjoinRoot.powerBasis' (TPoly_monic p T)).finrank,
      AdjoinRoot.powerBasis'_dim, TPoly_natDegree]
  have : Module.Finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
    (AdjoinRoot.powerBasis' (TPoly_monic p T)).finite
  have : FaithfulSMul (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (OQpCUn_embd_injective p T)
  have : Algebra.IsAlgebraic (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
    Algebra.IsAlgebraic.of_finite (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])
  have : IsScalarTower (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) := inferInstance
  have : IsScalarTower (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    -- `algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p,T] = QpCUn_embd ∘ algebraMap ℤᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p]`
    -- `algebraMap ℚᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p,T] = QpCUn_embd` (definitionally)
    change (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) x =
      QpCUn_embd p T (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) x)
    -- the LHS factors through ℤᶜᵘⁿ_[p,T]:
    have hL : (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) x =
        (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])) (OQpCUn_embd p T x) := by
      rw [show (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) =
          (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])).comp (OQpCUn_embd p T) from ?_]
      · rfl
      · ext y
        change (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) y =
          (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])) ((OQpCUn_embd p T) y)
        unfold OQpCUn_embd
        exact IsScalarTower.algebraMap_apply (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) y
    rw [hL]
    -- the RHS also goes through ℤᶜᵘⁿ_[p,T] using IsFractionRing.lift_algebraMap:
    rw [show QpCUn_embd p T (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) x) =
        ((algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])).comp (OQpCUn_embd p T)) x from
      IsFractionRing.lift_algebraMap _ x]
    rfl
  -- Now apply the finrank-of-fraction-ring lemma.
  have := IsFractionRing.finrank_eq (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
  rw [this, hpb]

/-! ### Lemma 4.2 — Teichmüller series for `ℤᶜᵘⁿ_[p,T]` -/

/-
  **Lemma 4.2** is stated and proved further down (after the `TResidue`/
  `TTeichmuller` infrastructure used in its proof) as
  `exists_teichmuller_series_OQpCUnT`.  We move the placement so the proof can
  reuse the digit-extraction lemmas `Texists_T_pInvT_digits` /
  `Tteichmuller_digits_unique` rather than duplicating them inline.
-/

/-! ### `TLiftedPAdicHahnSeries := W(𝔽ₚ^⁻)[p^{1/T}]((t^ℚ))` -/

/-- The T-scaled lifted Hahn series ring `W(𝔽ₚ^⁻)[p^{1/T}]((t^ℚ))`. -/
abbrev TLiftedPAdicHahnSeries : Type _ := HahnSeries ℚ (ℤᶜᵘⁿ_[p,T])

namespace TLiftedPAdicHahnSeries

/-- Build a T-lifted Hahn series from a coefficient function `s : ℚ → 𝔽ᵃ_[p]` with
well-ordered support, using the composition Teichmüller-lift then `OQpCUn_embd`. -/
noncomputable def fromCoeff (s : ℚ → Fpbar p) (hspwo : (Function.support s).IsPWO) :
    TLiftedPAdicHahnSeries p T where
  coeff n := OQpCUn_embd p T (teichmuller p (s n))
  isPWO_support' := by
    apply hspwo.mono
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro hsn
    apply hn
    rw [hsn, WittVector.teichmuller_zero, map_zero]

end TLiftedPAdicHahnSeries

/-- The natural ring inclusion `LiftedPAdicHahnSeries p ↪ TLiftedPAdicHahnSeries p T`,
obtained by applying `OQpCUn_embd` coefficient-wise (Remark 2.3). -/
noncomputable def Lifted_to_TLifted :
    LiftedPAdicHahnSeries p →+* TLiftedPAdicHahnSeries p T where
  toFun x := x.map (OQpCUn_embd p T : ℤᶜᵘⁿ_[p] →+* ℤᶜᵘⁿ_[p,T])
  map_zero' := by
    change HahnSeries.map 0 (OQpCUn_embd p T) = 0
    exact HahnSeries.map_zero (OQpCUn_embd p T : ZeroHom (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]))
  map_one' := HahnSeries.map_one (OQpCUn_embd p T).toMonoidWithZeroHom
  map_add' x y := by
    change HahnSeries.map (x + y) (OQpCUn_embd p T) =
      HahnSeries.map x (OQpCUn_embd p T) + HahnSeries.map y (OQpCUn_embd p T)
    exact HahnSeries.map_add (OQpCUn_embd p T : ℤᶜᵘⁿ_[p] →+ ℤᶜᵘⁿ_[p,T])
  map_mul' x y := HahnSeries.map_mul (OQpCUn_embd p T).toNonUnitalRingHom

/-! ### Definition 2.4 — `IsTNullSeries` -/

/-- T-shifted analogue of `finiteBelow` (line 21).

For `g ∈ ℚ` and `M ∈ ℕ`, the index set of integers `n` such that `g + n/T ≤ M` and the
coefficient `x.coeff (g + n/T)` is non-zero is finite.

The well-orderedness of the support transfers via the order-preserving rescaling
`q ↦ g + q/T` (recall `T ≠ 0` from `[NeZero T]`). -/
abbrev TfiniteBelow (x : TLiftedPAdicHahnSeries p T) (g : ℚ) (M : ℕ) :
    Set.Finite {n : ℤ | g + (n : ℚ) / T ≤ M ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} := by
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  by_cases hs : Set.Nonempty x.support
  · let m : ℚ := x.isWF_support.min hs
    have hsubset :
        {n : ℤ | g + (n : ℚ) / T ≤ M ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} ⊆
          Set.Icc (⌈(T : ℚ) * (m - g)⌉ : ℤ) ⌊(T : ℚ) * ((M : ℚ) - g)⌋ := by
      intro n hn
      have hm_le : m ≤ g + (n : ℚ) / T :=
        x.isWF_support.min_le hs <| (HahnSeries.mem_support x _).2 hn.2
      have hT_eq : (T : ℚ) * ((n : ℚ) / T) = n := by
        rw [mul_div_assoc']; field_simp
      have hlower : (⌈(T : ℚ) * (m - g)⌉ : ℤ) ≤ n := by
        apply Int.ceil_le.mpr
        have h1 : m - g ≤ (n : ℚ) / T := by linarith
        have h2 : (T : ℚ) * (m - g) ≤ (T : ℚ) * ((n : ℚ) / T) :=
          mul_le_mul_of_nonneg_left h1 hT_pos.le
        rw [hT_eq] at h2
        exact_mod_cast h2
      have hupper : n ≤ ⌊(T : ℚ) * ((M : ℚ) - g)⌋ := by
        apply Int.le_floor.mpr
        have h1 : (n : ℚ) / T ≤ (M : ℚ) - g := by linarith [hn.1]
        have h2 : (T : ℚ) * ((n : ℚ) / T) ≤ (T : ℚ) * ((M : ℚ) - g) :=
          mul_le_mul_of_nonneg_left h1 hT_pos.le
        rw [hT_eq] at h2
        exact_mod_cast h2
      exact ⟨hlower, hupper⟩
    exact ((Set.finite_Icc _ _).subset hsubset)
  · have hcoeff : ∀ q : ℚ, x.coeff q = 0 := by
      intro q
      by_contra hq
      exact hs ⟨q, (HahnSeries.mem_support x q).2 hq⟩
    have hset : {n : ℤ | g + (n : ℚ) / T ≤ M ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} = ∅ := by
      ext n
      simp [hcoeff (g + (n : ℚ) / T)]
    simp [hset]

open Topology Filter in
/--
**Definition 2.4.**  An element `x = ∑ c_q t^q ∈ TLiftedPAdicHahnSeries p T` is a
*T-null-series* iff for every `g ∈ ℚ`, the partial sums
`∑_{n : g + n/T ≤ M, c_{g+n/T} ≠ 0} (pInvTQ p T)^n · c_{g+n/T}` (mapped into `ℚᶜᵘⁿ_[p,T]`
via `algebraMap`) tend to `0` as `M → ∞`.

This mirrors `IsNullSeries` (line 55) verbatim with two substitutions:
* `(p : QpCUn p)` is replaced by `pInvTQ p T` (the T-th root of `p` in `ℚᶜᵘⁿ_[p,T]`);
* coefficient indices are shifted by `1/T` rather than `1`. -/
def IsTNullSeries (x : TLiftedPAdicHahnSeries p T) : Prop :=
  ∀ g : ℚ, Filter.Tendsto (fun M : ℕ => ∑ n : Set.Finite.toFinset (TfiniteBelow p T x g M),
      (pInvTQ p T) ^ (n.val : ℤ) *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n.val : ℚ) / T))) atTop (𝓝 0)

/-! ### Helpers for `smul_mem'` — T-scaled ports of Poonen1993 helpers (Lemma 4.6 (1)) -/

/-- T-scaled analogue of `finiteBelowInt` (line 61). Indexes integers `n ≤ K` whose
shifted coefficient `x.coeff (g + n/T)` is non-zero. -/
private abbrev TfiniteBelowInt
    (x : TLiftedPAdicHahnSeries p T) (g : ℚ) (K : ℤ) :
    Set.Finite {n : ℤ | n ≤ K ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} := by
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  by_cases hs : Set.Nonempty x.support
  · let m : ℚ := x.isWF_support.min hs
    have hsubset :
        {n : ℤ | n ≤ K ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} ⊆
          Set.Icc (⌈(T : ℚ) * (m - g)⌉ : ℤ) K := by
      intro n hn
      have hm_le : m ≤ g + (n : ℚ) / T :=
        x.isWF_support.min_le hs <| (HahnSeries.mem_support x _).2 hn.2
      have hT_eq : (T : ℚ) * ((n : ℚ) / T) = n := by
        rw [mul_div_assoc']; field_simp
      have hlower : (⌈(T : ℚ) * (m - g)⌉ : ℤ) ≤ n := by
        apply Int.ceil_le.mpr
        have h1 : m - g ≤ (n : ℚ) / T := by linarith
        have h2 : (T : ℚ) * (m - g) ≤ (T : ℚ) * ((n : ℚ) / T) :=
          mul_le_mul_of_nonneg_left h1 hT_pos.le
        rw [hT_eq] at h2
        exact_mod_cast h2
      exact ⟨hlower, hn.1⟩
    exact ((Set.finite_Icc _ _).subset hsubset)
  · have hcoeff : ∀ q : ℚ, x.coeff q = 0 := by
      intro q
      by_contra hq
      exact hs ⟨q, (HahnSeries.mem_support x q).2 hq⟩
    have hset : {n : ℤ | n ≤ K ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} = ∅ := by
      ext n
      simp [hcoeff (g + (n : ℚ) / T)]
    simp [hset]

/-- T-scaled analogue of `intPartial` (line 84). -/
private noncomputable def TintPartial
    (x : TLiftedPAdicHahnSeries p T) (g : ℚ) (K : ℤ) : ℚᶜᵘⁿ_[p,T] :=
  ∑ n : Set.Finite.toFinset (TfiniteBelowInt p T x g K),
    (pInvTQ p T) ^ (n.1 : ℤ) *
      algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n.1 : ℚ) / T))

/-- T-scaled analogue of `valued_v_term_le` (line 118). -/
private lemma Tvalued_v_term_le (a : ℤᶜᵘⁿ_[p,T]) (n : ℤ) :
    Valued.v ((pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) a) ≤
      ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
  rw [Valuation.map_mul, valued_v_pInvT_zpow]
  have h_alg : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) a) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_le_one a
  calc ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) *
          Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) a)
      ≤ ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) * 1 :=
        mul_le_mul' (le_refl _) h_alg
    _ = ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := mul_one _

/-- T-scaled analogue of `valued_v_algebraMap_unit_one` (line 131). -/
private lemma Tvalued_v_algebraMap_unit_one (u : (ℤᶜᵘⁿ_[p,T])ˣ) :
    Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) = 1 := by
  have h1 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_le_one u.val
  have h2 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.inv) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_le_one u.inv
  have h3 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) *
            Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.inv) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, u.val_inv]; simp
  by_contra h_ne_one
  have h1_lt : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) < 1 :=
    lt_of_le_of_ne h1 h_ne_one
  have h_lt : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) *
            Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.inv) < 1 := by
    calc
      Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) *
          Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.inv) ≤
          Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) * 1 := mul_le_mul' (le_refl _) h2
      _ = Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) u.val) := mul_one _
      _ < 1 := h1_lt
  rw [h3] at h_lt
  exact lt_irrefl _ h_lt

/-- T-scaled analogue of `intPartial_diff_eq_sdiff_sum` (line 156). -/
private lemma TintPartial_diff_eq_sdiff_sum
    (x : TLiftedPAdicHahnSeries p T) (g : ℚ) (K K' : ℤ) (h : K ≤ K') :
    TintPartial p T x g K' - TintPartial p T x g K =
      ∑ n ∈ (Set.Finite.toFinset (TfiniteBelowInt p T x g K') \
              Set.Finite.toFinset (TfiniteBelowInt p T x g K)),
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)) := by
  have hsub : Set.Finite.toFinset (TfiniteBelowInt p T x g K) ⊆
      Set.Finite.toFinset (TfiniteBelowInt p T x g K') := by
    intro n hn
    have hn_mem : n ∈ {n : ℤ | n ≤ K ∧ x.coeff (g + (n : ℚ) / T) ≠ 0} :=
      (Set.Finite.mem_toFinset _).mp hn
    exact (Set.Finite.mem_toFinset _).mpr ⟨le_trans hn_mem.1 h, hn_mem.2⟩
  have e1 : TintPartial p T x g K' = ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T x g K'),
      (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)) :=
    Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T x g K'))
      (f := fun m : ℤ => (pInvTQ p T) ^ m *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (m : ℚ) / T)))
  have e2 : TintPartial p T x g K = ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T x g K),
      (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)) :=
    Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T x g K))
      (f := fun m : ℤ => (pInvTQ p T) ^ m *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (m : ℚ) / T)))
  rw [e1, e2, ← Finset.sum_sdiff hsub, add_sub_cancel_right]

/-- T-scaled analogue of `partial_sum_valuation_cauchy` (line 181). -/
private lemma Tpartial_sum_valuation_cauchy
    (x : TLiftedPAdicHahnSeries p T) (g' : ℚ) (K₁ K₂ : ℤ) (h : K₁ ≤ K₂) :
    Valued.v (TintPartial p T x g' K₂ - TintPartial p T x g' K₁) ≤
      ((Multiplicative.ofAdd (-(K₁ + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
  rw [TintPartial_diff_eq_sdiff_sum p T x g' K₁ K₂ h]
  apply Valuation.map_sum_le
  intro n hn
  have hn_mem : n ∈ Set.Finite.toFinset (TfiniteBelowInt p T x g' K₂) ∧
      n ∉ Set.Finite.toFinset (TfiniteBelowInt p T x g' K₁) := Finset.mem_sdiff.mp hn
  have hn1 : n ≤ K₂ ∧ x.coeff (g' + (n : ℚ) / T) ≠ 0 :=
    (Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T x g' K₂)).mp hn_mem.1
  have hn2 : ¬ (n ≤ K₁ ∧ x.coeff (g' + (n : ℚ) / T) ≠ 0) := by
    intro h'
    exact hn_mem.2 ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T x g' K₁)).mpr h')
  have hn_gt : K₁ < n := by
    by_contra hle
    push Not at hle
    exact hn2 ⟨hle, hn1.2⟩
  have h1 := Tvalued_v_term_le p T (x.coeff (g' + (n : ℚ) / T)) n
  have h2 : ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) ≤
      ((Multiplicative.ofAdd (-(K₁ + 1) : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_le_coe]
    exact Multiplicative.ofAdd_le.mpr (by omega)
  exact h1.trans h2

/-- T-scaled analogue of `partialSum_eq_intPartial` (line 211).
The natural-number partial sum equals the integer-cutoff `TintPartial` at
`K = ⌊T · (M - g)⌋`. -/
private lemma TpartialSum_eq_intPartial
    (x : TLiftedPAdicHahnSeries p T) (g : ℚ) (M : ℕ) :
    (∑ n : Set.Finite.toFinset (TfiniteBelow p T x g M),
        (pInvTQ p T) ^ (n.val : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n.val : ℚ) / T))) =
      TintPartial p T x g ⌊(T : ℚ) * ((M : ℚ) - g)⌋ := by
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  have hT_eq : ∀ n : ℤ, (T : ℚ) * ((n : ℚ) / T) = n := by
    intro n; rw [mul_div_assoc']; field_simp
  have hset_eq : Set.Finite.toFinset (TfiniteBelow p T x g M) =
      Set.Finite.toFinset
        (TfiniteBelowInt p T x g ⌊(T : ℚ) * ((M : ℚ) - g)⌋) := by
    ext n
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hle, hne⟩
      refine ⟨?_, hne⟩
      have h1 : (n : ℚ) / T ≤ (M : ℚ) - g := by linarith
      have h2 : (T : ℚ) * ((n : ℚ) / T) ≤ (T : ℚ) * ((M : ℚ) - g) :=
        mul_le_mul_of_nonneg_left h1 hT_pos.le
      rw [hT_eq n] at h2
      have h3 : (n : ℚ) ≤ (T : ℚ) * ((M : ℚ) - g) := h2
      exact Int.le_floor.mpr h3
    · rintro ⟨hle, hne⟩
      refine ⟨?_, hne⟩
      have hfloor : ((⌊(T : ℚ) * ((M : ℚ) - g)⌋ : ℤ) : ℚ) ≤ (T : ℚ) * ((M : ℚ) - g) :=
        Int.floor_le _
      have hcast : (n : ℚ) ≤ (⌊(T : ℚ) * ((M : ℚ) - g)⌋ : ℤ) := by exact_mod_cast hle
      have h_n_le : (n : ℚ) ≤ (T : ℚ) * ((M : ℚ) - g) := hcast.trans hfloor
      have hT_ne : (T : ℚ) ≠ 0 := ne_of_gt hT_pos
      have h_div : (n : ℚ) / T ≤ (M : ℚ) - g := by
        rw [div_le_iff₀ hT_pos]; linarith
      linarith
  unfold TintPartial
  rw [show (∑ n : Set.Finite.toFinset (TfiniteBelow p T x g M),
        (pInvTQ p T) ^ (n.val : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n.val : ℚ) / T))) =
      ∑ n ∈ Set.Finite.toFinset (TfiniteBelow p T x g M),
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)) from
      Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelow p T x g M))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)))]
  rw [show (∑ n : Set.Finite.toFinset
            (TfiniteBelowInt p T x g ⌊(T : ℚ) * ((M : ℚ) - g)⌋),
        (pInvTQ p T) ^ (n.1 : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n.1 : ℚ) / T))) =
      ∑ n ∈ Set.Finite.toFinset
          (TfiniteBelowInt p T x g ⌊(T : ℚ) * ((M : ℚ) - g)⌋),
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)) from
      Finset.sum_attach (s := Set.Finite.toFinset
          (TfiniteBelowInt p T x g ⌊(T : ℚ) * ((M : ℚ) - g)⌋))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n : ℚ) / T)))]
  rw [hset_eq]

/-- T-scaled analogue of `null_series_tail_bound` (line 253). -/
private lemma Tnull_series_tail_bound
    {x : TLiftedPAdicHahnSeries p T} (hx : IsTNullSeries p T x) (g : ℚ) (K : ℤ) :
    Valued.v (TintPartial p T x g K) ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  have hnhds :
      {y : ℚᶜᵘⁿ_[p,T] | Valued.v y <
          ((Multiplicative.ofAdd (-(K + 2) : ℤ) : Multiplicative ℤ) : WithZero _)} ∈
        nhds (0 : ℚᶜᵘⁿ_[p,T]) :=
    Tmem_nhds_zero_v_lt p T WithZero.coe_ne_zero
  have hev_close : ∀ᶠ M : ℕ in Filter.atTop,
      Valued.v (∑ n : Set.Finite.toFinset (TfiniteBelow p T x g M),
          (pInvTQ p T) ^ (n.val : ℤ) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g + (n.val : ℚ) / T))) <
        ((Multiplicative.ofAdd (-(K + 2) : ℤ) : Multiplicative ℤ) : WithZero _) :=
    hx g hnhds
  -- Need ⌊T·(M - g)⌋ ≥ K, i.e., T·(M - g) ≥ K, i.e., M ≥ g + K/T.
  have hev_floor : ∀ᶠ M : ℕ in Filter.atTop, K ≤ ⌊(T : ℚ) * ((M : ℚ) - g)⌋ := by
    have h_int : ∀ᶠ M : ℕ in Filter.atTop, ⌈g + (K : ℚ) / T⌉₊ ≤ M :=
      Filter.eventually_ge_atTop ⌈g + (K : ℚ) / T⌉₊
    filter_upwards [h_int] with M hM
    have h1 : g + (K : ℚ) / T ≤ (⌈g + (K : ℚ) / T⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : ((⌈g + (K : ℚ) / T⌉₊ : ℕ) : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
    have h3 : g + (K : ℚ) / T ≤ (M : ℚ) := h1.trans h2
    have h4 : (K : ℚ) / T ≤ (M : ℚ) - g := by linarith
    have h5 : (T : ℚ) * ((K : ℚ) / T) ≤ (T : ℚ) * ((M : ℚ) - g) :=
      mul_le_mul_of_nonneg_left h4 hT_pos.le
    have hT_eq : (T : ℚ) * ((K : ℚ) / T) = K := by
      rw [mul_div_assoc']; field_simp
    rw [hT_eq] at h5
    exact Int.le_floor.mpr (by exact_mod_cast h5)
  obtain ⟨M, hMle, hMfloor⟩ := (hev_close.and hev_floor).exists
  set K' : ℤ := ⌊(T : ℚ) * ((M : ℚ) - g)⌋ with hK'_def
  have hK'ge : K ≤ K' := hMfloor
  have hpartial_eq := TpartialSum_eq_intPartial p T x g M
  rw [← hK'_def] at hpartial_eq
  rw [hpartial_eq] at hMle
  have hcauchy := Tpartial_sum_valuation_cauchy p T x g K K' hK'ge
  have hsplit : TintPartial p T x g K =
      TintPartial p T x g K' - (TintPartial p T x g K' - TintPartial p T x g K) := by
    ring
  rw [hsplit]
  have h1 : Valued.v (TintPartial p T x g K') ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
    have h_le : ((Multiplicative.ofAdd (-(K + 2) : ℤ) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) ≤
        ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
      rw [WithZero.coe_le_coe]
      exact Multiplicative.ofAdd_le.mpr (by omega)
    exact le_trans (le_of_lt hMle) h_le
  calc Valued.v (TintPartial p T x g K' - (TintPartial p T x g K' - TintPartial p T x g K))
      ≤ max (Valued.v (TintPartial p T x g K'))
            (Valued.v (TintPartial p T x g K' - TintPartial p T x g K)) :=
        Valuation.map_sub Valued.v _ _
    _ ≤ ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) :=
        max_le h1 hcauchy

/-- T-scaled analogue of `intPartial_mul_valuation_bound` (line 349). -/
private lemma TintPartial_mul_valuation_bound
    (c x : TLiftedPAdicHahnSeries p T) (hx : IsTNullSeries p T x) (g : ℚ) (K : ℤ) :
    Valued.v (TintPartial p T (c * x) g K) ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
  open Pointwise in
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  -- The set of integers `n ≤ K` with `g + n/T ∈ c.support + x.support` is finite.
  have h_sum_pwo : (c.support + x.support).IsPWO := c.isPWO_support.add x.isPWO_support
  have h_outer_ext_finite :
      {n : ℤ | n ≤ K ∧ g + (n : ℚ) / T ∈ c.support + x.support}.Finite := by
    by_cases hs_ne : (c.support + x.support).Nonempty
    · let q_min : ℚ := h_sum_pwo.isWF.min hs_ne
      have hbound : {n : ℤ | n ≤ K ∧ g + (n : ℚ) / T ∈ c.support + x.support} ⊆
          Set.Icc ⌈(T : ℚ) * (q_min - g)⌉ K := by
        intro n hn
        have hge : q_min ≤ g + (n : ℚ) / T := h_sum_pwo.isWF.min_le hs_ne hn.2
        have h1 : q_min - g ≤ (n : ℚ) / T := by linarith
        have h2 : (T : ℚ) * (q_min - g) ≤ (T : ℚ) * ((n : ℚ) / T) :=
          mul_le_mul_of_nonneg_left h1 hT_pos.le
        have hT_eq : (T : ℚ) * ((n : ℚ) / T) = n := by
          rw [mul_div_assoc']; field_simp
        rw [hT_eq] at h2
        refine ⟨?_, hn.1⟩
        exact Int.ceil_le.mpr (by exact_mod_cast h2)
      exact (Set.finite_Icc _ _).subset hbound
    · have hempty : {n : ℤ | n ≤ K ∧ g + (n : ℚ) / T ∈ c.support + x.support} = ∅ := by
        ext n
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hg
        exact (hs_ne ⟨g + (n : ℚ) / T, hg⟩).elim
      rw [hempty]; exact Set.finite_empty
  let OuterExt : Finset ℤ := h_outer_ext_finite.toFinset
  have hOuterExt_mem : ∀ n : ℤ, n ∈ OuterExt ↔
      n ≤ K ∧ g + (n : ℚ) / T ∈ c.support + x.support := by
    intro n
    exact Set.Finite.mem_toFinset _
  have h_outer_sub : Set.Finite.toFinset (TfiniteBelowInt p T (c * x) g K) ⊆ OuterExt := by
    intro n hn
    have hn_data : n ≤ K ∧ (c * x).coeff (g + (n : ℚ) / T) ≠ 0 :=
      (Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T (c * x) g K)).mp hn
    have hcoeff_ne := hn_data.2
    have hsupp : g + (n : ℚ) / T ∈ (c * x).support :=
      (HahnSeries.mem_support _ _).mpr hcoeff_ne
    have hsubset : (c * x).support ⊆ c.support + x.support := HahnSeries.support_mul_subset
    exact (hOuterExt_mem n).mpr ⟨hn_data.1, hsubset hsupp⟩
  have h_intPartial_attach : TintPartial p T (c * x) g K =
      ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T (c * x) g K),
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((c * x).coeff (g + (n : ℚ) / T)) :=
    Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T (c * x) g K))
      (f := fun n : ℤ => (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((c * x).coeff (g + (n : ℚ) / T)))
  have h_extend_eq : TintPartial p T (c * x) g K =
      ∑ n ∈ OuterExt, (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((c * x).coeff (g + (n : ℚ) / T)) := by
    rw [h_intPartial_attach]
    apply Finset.sum_subset h_outer_sub
    intro n hn_outer hn_orig
    have h_ext_data : n ≤ K ∧ g + (n : ℚ) / T ∈ c.support + x.support :=
      (hOuterExt_mem n).mp hn_outer
    have h_ne_orig : ¬ (n ≤ K ∧ (c * x).coeff (g + (n : ℚ) / T) ≠ 0) := by
      intro h
      exact hn_orig
        ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T (c * x) g K)).mpr h)
    have hcx_zero : (c * x).coeff (g + (n : ℚ) / T) = 0 := by
      by_contra hne
      exact h_ne_orig ⟨h_ext_data.1, hne⟩
    rw [hcx_zero, map_zero, mul_zero]
  have h_expand : ∀ n ∈ OuterExt,
      (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((c * x).coeff (g + (n : ℚ) / T)) =
        ∑ ab ∈ Finset.antidiagonal c.isPWO_support x.isPWO_support
            (g + (n : ℚ) / T),
          (pInvTQ p T) ^ n *
            (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff ab.1) *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff ab.2)) := by
    intro n _
    rw [HahnSeries.coeff_mul, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ab _
    rw [map_mul]
  rw [h_extend_eq, Finset.sum_congr rfl h_expand]
  have h_sigma_eq := Finset.sum_sigma (s := OuterExt)
        (t := fun n => Finset.antidiagonal c.isPWO_support x.isPWO_support
          (g + (n : ℚ) / T))
        (f := fun p_sig : Sigma (fun _ : ℤ => ℚ × ℚ) => (pInvTQ p T) ^ p_sig.1 *
          (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff p_sig.2.1) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff p_sig.2.2)))
  rw [← h_sigma_eq]
  let Triples : Finset (Sigma (fun _ : ℤ => ℚ × ℚ)) :=
    OuterExt.sigma (fun n => Finset.antidiagonal c.isPWO_support x.isPWO_support
      (g + (n : ℚ) / T))
  let AOf : Finset ℚ := Triples.image (fun s => s.2.1)
  have h_fubini : (∑ p_sig ∈ Triples,
        (pInvTQ p T) ^ p_sig.1 *
          (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff p_sig.2.1) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff p_sig.2.2))) =
      ∑ a ∈ AOf, algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a) *
        TintPartial p T x (g - a) K := by
    rw [show (∑ a ∈ AOf, algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a) *
          TintPartial p T x (g - a) K) =
        ∑ a ∈ AOf, algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a) *
          ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T x (g - a) K),
            (pInvTQ p T) ^ n *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g - a + (n : ℚ) / T)) from by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T x (g - a) K))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g - a + (n : ℚ) / T)))]
    rw [show (∑ a ∈ AOf, algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a) *
          ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T x (g - a) K),
            (pInvTQ p T) ^ n *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (x.coeff (g - a + (n : ℚ) / T))) =
        ∑ a ∈ AOf, ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T x (g - a) K),
            (pInvTQ p T) ^ n *
              (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a) *
                algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
                  (x.coeff (g - a + (n : ℚ) / T))) from by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring]
    have h_sigma_eq2 := Finset.sum_sigma (s := AOf)
      (t := fun a => Set.Finite.toFinset (TfiniteBelowInt p T x (g - a) K))
      (f := fun p_sig : Sigma (fun _ : ℚ => ℤ) =>
        (pInvTQ p T) ^ p_sig.2 *
          (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff p_sig.1) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (x.coeff (g - p_sig.1 + (p_sig.2 : ℚ) / T))))
    rw [← h_sigma_eq2]
    refine Finset.sum_bij
      (fun s _ => ⟨s.2.1, s.1⟩)
      ?_ ?_ ?_ ?_
    · intro s hs
      have hs_data := Finset.mem_sigma.mp hs
      have h_outer_data : s.1 ≤ K ∧ g + (s.1 : ℚ) / T ∈ c.support + x.support :=
        (hOuterExt_mem s.1).mp hs_data.1
      have h_anti_data : s.2.1 ∈ c.support ∧ s.2.2 ∈ x.support ∧
          s.2.1 + s.2.2 = g + (s.1 : ℚ) / T :=
        Finset.mem_antidiagonal.mp hs_data.2
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
      · refine (Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T x (g - s.2.1) K)).mpr
            ⟨h_outer_data.1, ?_⟩
        have hb_eq : g - s.2.1 + (s.1 : ℚ) / T = s.2.2 := by linarith [h_anti_data.2.2]
        rw [hb_eq]
        exact (HahnSeries.mem_support _ _).mp h_anti_data.2.1
    · intro s₁ hs₁ s₂ hs₂ h_eq
      have hs₁_data := Finset.mem_sigma.mp hs₁
      have hs₂_data := Finset.mem_sigma.mp hs₂
      have h_anti_data₁ := Finset.mem_antidiagonal.mp hs₁_data.2
      have h_anti_data₂ := Finset.mem_antidiagonal.mp hs₂_data.2
      have h_a_eq : s₁.2.1 = s₂.2.1 := (Sigma.mk.inj_iff.mp h_eq).1
      have h_n_eq : s₁.1 = s₂.1 := by
        have h := (Sigma.mk.inj_iff.mp h_eq).2
        exact eq_of_heq h
      have h_b_eq : s₁.2.2 = s₂.2.2 := by
        have h1 : s₁.2.1 + s₁.2.2 = g + (s₁.1 : ℚ) / T := h_anti_data₁.2.2
        have h2 : s₂.2.1 + s₂.2.2 = g + (s₂.1 : ℚ) / T := h_anti_data₂.2.2
        rw [h_a_eq, h_n_eq] at h1
        linarith
      cases s₁ with
      | mk fst snd =>
        cases s₂ with
        | mk fst' snd' =>
          cases snd with
          | mk a b =>
            cases snd' with
            | mk a' b' =>
              simp only at h_a_eq h_n_eq h_b_eq
              subst h_a_eq h_n_eq h_b_eq
              rfl
    · intro t ht
      have ht_data := Finset.mem_sigma.mp ht
      have ht_a_in : t.1 ∈ AOf := ht_data.1
      have ht_n_data : t.2 ≤ K ∧ x.coeff (g - t.1 + (t.2 : ℚ) / T) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T x (g - t.1) K)).mp ht_data.2
      obtain ⟨s_orig, hs_orig, hs_eq⟩ := Finset.mem_image.mp ht_a_in
      have hs_orig_data := Finset.mem_sigma.mp hs_orig
      have h_anti_orig := Finset.mem_antidiagonal.mp hs_orig_data.2
      have ha_in_supp : t.1 ∈ c.support := hs_eq ▸ h_anti_orig.1
      let b : ℚ := g - t.1 + (t.2 : ℚ) / T
      have hb_in_supp : b ∈ x.support := (HahnSeries.mem_support _ _).mpr ht_n_data.2
      have hab_sum : t.1 + b = g + (t.2 : ℚ) / T := by simp [b]; ring
      have hn_outer : t.2 ∈ OuterExt := by
        refine (hOuterExt_mem t.2).mpr ⟨ht_n_data.1, ?_⟩
        exact ⟨t.1, ha_in_supp, b, hb_in_supp, hab_sum⟩
      refine ⟨⟨t.2, t.1, b⟩, ?_, ?_⟩
      · refine Finset.mem_sigma.mpr ⟨hn_outer, ?_⟩
        exact Finset.mem_antidiagonal.mpr ⟨ha_in_supp, hb_in_supp, hab_sum⟩
      · rfl
    · intro s hs
      have hs_data := Finset.mem_sigma.mp hs
      have h_anti_data := Finset.mem_antidiagonal.mp hs_data.2
      have hb_eq : g - s.2.1 + (s.1 : ℚ) / T = s.2.2 := by linarith [h_anti_data.2.2]
      simp only [hb_eq]
  rw [h_fubini]
  apply Valuation.map_sum_le
  intro a _
  rw [Valuation.map_mul]
  have h_alg_le : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a)) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_le_one (c.coeff a)
  have h_inner_le : Valued.v (TintPartial p T x (g - a) K) ≤
      ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) :=
    Tnull_series_tail_bound p T hx (g - a) K
  calc Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (c.coeff a)) *
          Valued.v (TintPartial p T x (g - a) K)
      ≤ 1 * Valued.v (TintPartial p T x (g - a) K) := mul_le_mul' h_alg_le (le_refl _)
    _ = Valued.v (TintPartial p T x (g - a) K) := one_mul _
    _ ≤ ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := h_inner_le

/-! ### Lemma 4.6 (1) — `TNullSeriesIdeal` is an ideal -/

/-- **Lemma 4.6 (1).**  T-null-series form an ideal of `TLiftedPAdicHahnSeries p T`. -/
def TNullSeriesIdeal : Ideal (TLiftedPAdicHahnSeries p T) where
  carrier := { x | IsTNullSeries p T x }
  add_mem' := by
    -- Mirrors `NullSeriesIdeal.add_mem'` (lean:541–656).
    -- Standard linearity argument: rewrite each partial sum as a sum over the union
    -- of the index sets, then apply `Tendsto.add`.
    intro a b ha hb
    change IsTNullSeries p T a at ha
    change IsTNullSeries p T b at hb
    change IsTNullSeries p T (a + b)
    intro g
    let sa : ℕ → Finset ℤ := fun M => Set.Finite.toFinset (TfiniteBelow p T a g M)
    let sb : ℕ → Finset ℤ := fun M => Set.Finite.toFinset (TfiniteBelow p T b g M)
    let sab : ℕ → Finset ℤ := fun M => Set.Finite.toFinset (TfiniteBelow p T (a + b) g M)
    let su : ℕ → Finset ℤ := fun M => sa M ∪ sb M
    let fa : ℕ → ℤ → ℚᶜᵘⁿ_[p,T] := fun _ n =>
      (pInvTQ p T) ^ n * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (a.coeff (g + (n : ℚ) / T))
    let fb : ℕ → ℤ → ℚᶜᵘⁿ_[p,T] := fun _ n =>
      (pInvTQ p T) ^ n * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (b.coeff (g + (n : ℚ) / T))
    let fab : ℕ → ℤ → ℚᶜᵘⁿ_[p,T] := fun _ n =>
      (pInvTQ p T) ^ n * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((a + b).coeff (g + (n : ℚ) / T))
    have hsab_sub : ∀ M, sab M ⊆ su M := by
      intro M n hn
      have hn' : g + (n : ℚ) / T ≤ M ∧ (a + b).coeff (g + (n : ℚ) / T) ≠ 0 :=
        (Set.Finite.mem_toFinset (hs := TfiniteBelow p T (a + b) g M) (a := n)).1 hn
      have hmem : g + (n : ℚ) / T ∈ (a + b).support :=
        (HahnSeries.mem_support (a + b) _).2 hn'.2
      have hunion := HahnSeries.support_add_subset (x := a) (y := b) hmem
      rcases hunion with hxmem | hymem
      · exact Finset.mem_union_left _ <|
          (Set.Finite.mem_toFinset (hs := TfiniteBelow p T a g M) (a := n)).2 ⟨hn'.1, hxmem⟩
      · exact Finset.mem_union_right _ <|
          (Set.Finite.mem_toFinset (hs := TfiniteBelow p T b g M) (a := n)).2 ⟨hn'.1, hymem⟩
    have hsuma (M : ℕ) : Finset.sum (su M) (fa M) = Finset.sum (sa M) (fa M) := by
      symm; apply Finset.sum_subset
      · intro n hn; exact Finset.mem_union_left _ hn
      · intro n hnu hnsa
        have hnb : n ∈ sb M := (Finset.mem_union.mp hnu).resolve_left hnsa
        have hmem : g + (n : ℚ) / T ≤ M ∧ b.coeff (g + (n : ℚ) / T) ≠ 0 :=
          (Set.Finite.mem_toFinset (hs := TfiniteBelow p T b g M) (a := n)).1 hnb
        have hxzero : a.coeff (g + (n : ℚ) / T) = 0 := by
          by_contra hxne
          exact hnsa <|
            (Set.Finite.mem_toFinset (hs := TfiniteBelow p T a g M) (a := n)).2 ⟨hmem.1, hxne⟩
        simp [hxzero]
    have hsumb (M : ℕ) : Finset.sum (su M) (fb M) = Finset.sum (sb M) (fb M) := by
      symm; apply Finset.sum_subset
      · intro n hn; exact Finset.mem_union_right _ hn
      · intro n hnu hnsb
        have hna : n ∈ sa M := (Finset.mem_union.mp hnu).resolve_right hnsb
        have hmem : g + (n : ℚ) / T ≤ M ∧ a.coeff (g + (n : ℚ) / T) ≠ 0 :=
          (Set.Finite.mem_toFinset (hs := TfiniteBelow p T a g M) (a := n)).1 hna
        have hyzero : b.coeff (g + (n : ℚ) / T) = 0 := by
          by_contra hyne
          exact hnsb <|
            (Set.Finite.mem_toFinset (hs := TfiniteBelow p T b g M) (a := n)).2 ⟨hmem.1, hyne⟩
        simp [hyzero]
    have hsumab (M : ℕ) : Finset.sum (su M) (fab M) = Finset.sum (sab M) (fab M) := by
      symm; apply Finset.sum_subset
      · exact hsab_sub M
      · intro n hnu hnsab
        have hcoeff : (a + b).coeff (g + (n : ℚ) / T) = 0 := by
          by_contra hne
          exact hnsab <|
            (Set.Finite.mem_toFinset (hs := TfiniteBelow p T (a + b) g M) (a := n)).2 ⟨by
              rcases Finset.mem_union.mp hnu with hna | hnb
              · exact (Set.Finite.mem_toFinset (hs := TfiniteBelow p T a g M) (a := n)).1 hna |>.1
              · exact (Set.Finite.mem_toFinset (hs := TfiniteBelow p T b g M) (a := n)).1 hnb |>.1,
              hne⟩
        simp [hcoeff]
    have hfun :
        (fun M => Finset.sum (sab M) (fab M)) =
          fun M => Finset.sum (sa M) (fa M) + Finset.sum (sb M) (fb M) := by
      funext M
      rw [← hsumab M]
      calc
        Finset.sum (su M) (fab M) = Finset.sum (su M) (fun n => fa M n + fb M n) := by
          apply Finset.sum_congr rfl
          intro n _
          simp [fab, fa, fb, HahnSeries.coeff_add', mul_add, map_add]
        _ = Finset.sum (su M) (fa M) + Finset.sum (su M) (fb M) := by
          rw [Finset.sum_add_distrib]
        _ = Finset.sum (sa M) (fa M) + Finset.sum (sb M) (fb M) := by
          rw [hsuma M, hsumb M]
    have hxmain :
        (fun M => ∑ n : Set.Finite.toFinset (TfiniteBelow p T a g M),
            (pInvTQ p T) ^ (n.val : ℤ) *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (a.coeff (g + (n.val : ℚ) / T))) =
          fun M => Finset.sum (sa M) (fa M) := by
      funext M
      dsimp [sa, fa]
      simpa using (Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelow p T a g M))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (a.coeff (g + (n : ℚ) / T))))
    have hymain :
        (fun M => ∑ n : Set.Finite.toFinset (TfiniteBelow p T b g M),
            (pInvTQ p T) ^ (n.val : ℤ) *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (b.coeff (g + (n.val : ℚ) / T))) =
          fun M => Finset.sum (sb M) (fb M) := by
      funext M
      dsimp [sb, fb]
      simpa using (Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelow p T b g M))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (b.coeff (g + (n : ℚ) / T))))
    have hmain :
        (fun M : ℕ => ∑ n : Set.Finite.toFinset (TfiniteBelow p T (a + b) g M),
            (pInvTQ p T) ^ (n.val : ℤ) *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((a + b).coeff (g + (n.val : ℚ) / T))) =
          fun M => Finset.sum (sab M) (fab M) := by
      funext M
      dsimp [sab, fab]
      simpa using (Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelow p T (a + b) g M))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((a + b).coeff (g + (n : ℚ) / T))))
    have ha' : Filter.Tendsto (fun M => Finset.sum (sa M) (fa M)) Filter.atTop (nhds 0) := by
      rw [← hxmain]; exact ha g
    have hb' : Filter.Tendsto (fun M => Finset.sum (sb M) (fb M)) Filter.atTop (nhds 0) := by
      rw [← hymain]; exact hb g
    rw [hmain, hfun]
    simpa using ha'.add hb'
  zero_mem' := by
    -- Mirrors `NullSeriesIdeal.zero_mem'` (lean:657).
    -- The zero series has identically-zero coefficients, so each partial sum is `0`,
    -- and the constant-zero sequence trivially tends to `0`.
    change IsTNullSeries p T 0
    intro g
    simp
  smul_mem' := by
    -- Mirrors `NullSeriesIdeal.smul_mem'` (lean:658–742).
    -- Mechanical translation strategy: replace every occurrence of `(p : QpCUn p)` with
    -- `pInvTQ p T`, every `valued_v_p` with `valued_v_pInvT` (now proved), every
    -- `valued_v_p_zpow` with `valued_v_pInvT_zpow` (now proved), every `finiteBelow` with
    -- `TfiniteBelow`, every `(g + n)` with `(g + (n : ℚ) / T)`.
    --
    -- However, the Poonen proof relies on several intermediate helpers that have not yet
    -- been ported to the T-scaled setting:
    --   * `intPartial` (lean:84) — index-set realignment, ℕ-atTop ↔ ℤ-atTop
    --   * `partialSum_eq_intPartial` (lean:211) — the key bridge
    --   * `intPartial_diff_eq_sdiff_sum` (lean:156)
    --   * `partial_sum_valuation_cauchy` (lean:181) — strict-ultrametric bound
    --   * `intPartial_mul_valuation_bound` — used at line 715, the central bound
    -- These ~200 lines need to be ported with the same `(g + n)` ↦ `(g + n/T)` shift.
    --
    -- The strict-ultrametric ε-style argument then carries over verbatim:
    -- 1. Pick γ from Valued.mem_nhds; convert to ε ∈ ℝ via WithZeroMulInt.toNNReal.
    -- 2. Pick N with (p⁻¹)^N < ε using tendsto_pow_atTop_nhds_zero_of_lt_one.
    -- 3. For M ≥ ⌈N - 1 + g⌉, show the partial sum's valuation is ≤ ofAdd(-(K+1)) ≤ ofAdd(-N)
    --    using `intPartial_mul_valuation_bound` (the T-scaled version).
    -- 4. Convert back to the γ-form via the strict-monotonicity of toNNReal.
    --
    -- Setup for the proof framework (verifies inputs; the deep step is the bound):
    intro c x hx
    change IsTNullSeries p T (c * x)
    change IsTNullSeries p T x at hx
    intro g
    -- Step 1: rewrite the partial sum as `TintPartial (c*x) g ⌊T·(M - g)⌋`.
    have hpartial_eq : (fun M : ℕ => ∑ n : Set.Finite.toFinset (TfiniteBelow p T (c * x) g M),
        (pInvTQ p T) ^ (n.val : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((c * x).coeff (g + (n.val : ℚ) / T))) =
      fun M : ℕ => TintPartial p T (c * x) g ⌊(T : ℚ) * ((M : ℚ) - g)⌋ := by
      funext M
      exact TpartialSum_eq_intPartial p T (c * x) g M
    rw [hpartial_eq]
    -- Step 2: setup for ε-style argument via Valued.mem_nhds.
    have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
    have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
      WithZeroMulInt.toNNReal_strictMono hp1
    have hpinv_lt : (p : NNReal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    have hpinv_nn : 0 ≤ ((p : NNReal)⁻¹ : NNReal) := zero_le
    have hT_pos : (0 : ℚ) < T := by
      have hT : T ≠ 0 := NeZero.ne T
      exact_mod_cast Nat.pos_of_ne_zero hT
    rw [Filter.tendsto_iff_forall_eventually_mem]
    intro U hU
    obtain ⟨γ, hγ_ne, hγ⟩ := Texists_v_lt_subset p T hU
    set ε : NNReal :=
      WithZeroMulInt.toNNReal (p_ne_zero p) (γ : WithZero (Multiplicative ℤ)) with hε_def
    have hε_pos : (0 : NNReal) < ε := by
      rw [hε_def]
      exact WithZeroMulInt.toNNReal_pos (p_ne_zero p) hγ_ne
    have htendsto : Filter.Tendsto (fun n : ℕ => ((p : NNReal)⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hpinv_nn hpinv_lt
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ((p : NNReal)⁻¹) ^ N < ε := by
      have h_eventually : ∀ᶠ n : ℕ in Filter.atTop, ((p : NNReal)⁻¹) ^ n < ε :=
        htendsto.eventually (eventually_lt_nhds hε_pos)
      exact h_eventually.exists
    -- Step 3: pick M₀ so that for M ≥ M₀, ⌊T·(M - g)⌋ + 1 ≥ N.
    rw [Filter.eventually_atTop]
    refine ⟨⌈g + ((N : ℚ) - 1) / T⌉₊, ?_⟩
    intro M hM
    set K : ℤ := ⌊(T : ℚ) * ((M : ℚ) - g)⌋ with hK_def
    have hK_ge : (N : ℤ) - 1 ≤ K := by
      rw [hK_def]
      apply Int.le_floor.mpr
      have h1 : (g + ((N : ℚ) - 1) / T) ≤ (⌈g + ((N : ℚ) - 1) / T⌉₊ : ℚ) := Nat.le_ceil _
      have h2 : ((⌈g + ((N : ℚ) - 1) / T⌉₊ : ℕ) : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
      have h3 : (g + ((N : ℚ) - 1) / T) ≤ (M : ℚ) := h1.trans h2
      have h4 : ((N : ℚ) - 1) / T ≤ (M : ℚ) - g := by linarith
      have h5 : (T : ℚ) * (((N : ℚ) - 1) / T) ≤ (T : ℚ) * ((M : ℚ) - g) :=
        mul_le_mul_of_nonneg_left h4 hT_pos.le
      have hT_eq : (T : ℚ) * (((N : ℚ) - 1) / T) = (N : ℚ) - 1 := by
        rw [mul_div_assoc']; field_simp
      rw [hT_eq] at h5
      push_cast
      linarith
    have hK_plus_1 : (N : ℤ) ≤ K + 1 := by linarith
    -- Step 4: apply the bound and convert to ε-form.
    apply hγ
    change Valued.v (TintPartial p T (c * x) g K) < γ
    have hbound := TintPartial_mul_valuation_bound p T c x hx g K
    have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (TintPartial p T (c * x) g K)) ≤
        WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) :=
      hsm.monotone hbound
    have htoNN : WithZeroMulInt.toNNReal (p_ne_zero p)
        (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) =
        (p : NNReal) ^ (-(K + 1)) := by
      rw [WithZeroMulInt.toNNReal_neg_apply (p_ne_zero p) WithZero.coe_ne_zero, WithZero.unzero_coe]
      congr 1
    rw [htoNN] at h_nnreal_le
    have h_pow_le : (p : NNReal) ^ (-(K + 1)) ≤ ((p : NNReal)⁻¹) ^ N := by
      rw [show (p : NNReal) ^ (-(K + 1)) = ((p : NNReal)⁻¹) ^ ((K : ℤ) + 1) from by
        rw [zpow_neg, ← inv_zpow]]
      rw [show ((p : NNReal)⁻¹) ^ ((K : ℤ) + 1) = ((p : NNReal)⁻¹) ^ ((K + 1).toNat) from by
        rw [← zpow_natCast]
        congr 1
        omega]
      apply pow_le_pow_of_le_one hpinv_nn (le_of_lt hpinv_lt)
      omega
    have h_combined : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (TintPartial p T (c * x) g K)) < ε :=
      lt_of_le_of_lt (h_nnreal_le.trans h_pow_le) hN
    rw [hε_def] at h_combined
    exact hsm.lt_iff_lt.mp h_combined

/-! ### Phase 1 infrastructure for `exists_canonical_T_expansion` -/

/-- T-scaled analogue of `existsCanonicalExpansionAux.natRange_isPWO`
(Poonen line 839).  The image of `ℕ` under the canonical embedding `ℕ → ℚ` is
partially well-ordered.  No T-dependence; statement is identical. -/
private lemma Tnatrange_isPWO : (Set.range ((↑) : ℕ → ℚ)).IsPWO := by
  have hUniv : (Set.univ : Set ℕ).IsPWO := Set.isPWO_of_wellQuasiOrderedLE _
  have hMono : MonotoneOn ((↑) : ℕ → ℚ) Set.univ := by
    intro a _ b _ h
    exact_mod_cast h
  simpa using hUniv.image_of_monotoneOn hMono

/-- T-scaled `ℕ/T`-range: `{n/T | n : ℕ}`.  Used as the index set in the T-shifted
support-PWO bound (analogue of Poonen's `Set.range ((↑) : ℕ → ℚ)`). -/
private lemma TnatrangeDivT_isPWO (T : ℕ) [NeZero T] :
    (Set.range (fun n : ℕ => (n : ℚ) / T)).IsPWO := by
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  have hUniv : (Set.univ : Set ℕ).IsPWO := Set.isPWO_of_wellQuasiOrderedLE _
  have hMono : MonotoneOn (fun n : ℕ => (n : ℚ) / T) Set.univ := by
    intro a _ b _ h
    have h1 : (a : ℚ) ≤ b := by exact_mod_cast h
    exact div_le_div_of_nonneg_right h1 hT_pos.le
  simpa using hUniv.image_of_monotoneOn hMono

open scoped Pointwise in
/-- T-scaled analogue of
  `existsCanonicalExpansionAux.support_isPWO_of_subset_support_add_natRange`
(Poonen line 853).  If `Function.support s ⊆ α.support + {n/T | n : ℕ}`, then
`Function.support s` is partially well-ordered. -/
private lemma Tsupport_isPWO_of_subset_support_add_natRange
    (α : TLiftedPAdicHahnSeries p T) {s : ℚ → Fpbar p}
    (h : Function.support s ⊆ α.support + Set.range (fun n : ℕ => (n : ℚ) / T)) :
    (Function.support s).IsPWO :=
  (α.isPWO_support.add (TnatrangeDivT_isPWO T)).mono h

/-- T-scaled analogue of `existsCanonicalExpansionAux.rat_decompose`
(Poonen line 862).  No T-dependence; statement identical. -/
private lemma Trat_decompose (q : ℚ) :
    Int.fract q + (⌊q⌋ : ℚ) = q ∧
    (0 : ℚ) ≤ Int.fract q ∧ Int.fract q < 1 := by
  refine ⟨?_, Int.fract_nonneg q, Int.fract_lt_one q⟩
  have h := Int.fract_add_floor q
  linarith

/-! #### `one_notMem_TNullSeriesIdeal` (Lemma 4.6 (1) byproduct) -/

/-- T-scaled analogue of `one_notMem_NullSeriesIdeal` (Poonen line 751).
`(1 : TLiftedPAdicHahnSeries p T)` is not a T-null-series; the partial-sum sequence
at `g = 0` is constantly `1`, hence its limit (in the Hausdorff `Valued`-topology) is
`1 ≠ 0`. -/
private lemma one_notMem_TNullSeriesIdeal :
    (1 : TLiftedPAdicHahnSeries p T) ∉ TNullSeriesIdeal p T := by
  classical
  intro h_null
  have h_NS : IsTNullSeries p T (1 : TLiftedPAdicHahnSeries p T) := h_null
  have htend := h_NS 0
  -- The partial-sum sequence is constantly `1` for every `M : ℕ`.
  have h_partial_sum_one : ∀ M : ℕ,
      (∑ n : Set.Finite.toFinset (TfiniteBelow p T (1 : TLiftedPAdicHahnSeries p T) 0 M),
          (pInvTQ p T) ^ (n.val : ℤ) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              ((1 : TLiftedPAdicHahnSeries p T).coeff (0 + (n.val : ℚ) / T)))
        = 1 := by
    intro M
    set S := Set.Finite.toFinset (TfiniteBelow p T (1 : TLiftedPAdicHahnSeries p T) 0 M)
      with hS_def
    have hT_pos : (0 : ℚ) < T := by
      have hT : T ≠ 0 := NeZero.ne T
      exact_mod_cast Nat.pos_of_ne_zero hT
    have hT_ne : (T : ℚ) ≠ 0 := ne_of_gt hT_pos
    -- The TfiniteBelow set at `g = 0` is `{0}` for any `M : ℕ`, since
    -- `(1).coeff q = 0` whenever `q ≠ 0`, and `n = 0` is admissible (since `0 ≤ M`).
    have hS_eq : S = ({0} : Finset ℤ) := by
      ext n
      simp only [hS_def, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h_ne⟩
        by_contra h_n_ne_zero
        apply h_ne
        have hn_ne_q : (n : ℚ) ≠ 0 := by exact_mod_cast h_n_ne_zero
        have hquot_ne : (n : ℚ) / T ≠ 0 := div_ne_zero hn_ne_q hT_ne
        have hq_ne : (0 : ℚ) + (n : ℚ) / T ≠ 0 := by rw [zero_add]; exact hquot_ne
        rw [HahnSeries.coeff_one]; exact if_neg hq_ne
      · rintro rfl
        refine ⟨?_, ?_⟩
        · have hM_nn : (0 : ℚ) ≤ (M : ℚ) := by exact_mod_cast (Nat.zero_le M)
          have hzero : (0 : ℚ) + (((0 : ℤ) : ℚ)) / T = 0 := by push_cast; ring
          rw [hzero]; exact hM_nn
        · have hzero : (0 : ℚ) + (((0 : ℤ) : ℚ)) / T = 0 := by push_cast; ring
          rw [hzero]; simp [HahnSeries.coeff_one]
    rw [show (∑ n : S, (pInvTQ p T) ^ (n.val : ℤ) *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          ((1 : TLiftedPAdicHahnSeries p T).coeff (0 + (n.val : ℚ) / T))) =
        ∑ n ∈ S, (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            ((1 : TLiftedPAdicHahnSeries p T).coeff (0 + (n : ℚ) / T)) from
      Finset.sum_attach (s := S) (f := fun n : ℤ =>
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            ((1 : TLiftedPAdicHahnSeries p T).coeff (0 + (n : ℚ) / T)))]
    rw [hS_eq, Finset.sum_singleton]
    have h_zero_eq : (0 : ℚ) + (((0 : ℤ) : ℚ)) / T = 0 := by push_cast; ring
    rw [h_zero_eq, show ((1 : TLiftedPAdicHahnSeries p T).coeff 0) = 1 by
      rw [HahnSeries.coeff_one]; simp, map_one, mul_one]
    exact zpow_zero _
  -- The sequence is eventually `1`, so it tends to `1`. By uniqueness of limits in
  -- `ℚᶜᵘⁿ_[p,T]` (which is `T2`), `1 = 0`, contradicting `one_ne_zero`.
  have h_tend_one :
      Filter.Tendsto
        (fun M : ℕ =>
          ∑ n : Set.Finite.toFinset (TfiniteBelow p T (1 : TLiftedPAdicHahnSeries p T) 0 M),
            (pInvTQ p T) ^ (n.val : ℤ) *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
                ((1 : TLiftedPAdicHahnSeries p T).coeff (0 + (n.val : ℚ) / T)))
        Filter.atTop (nhds (1 : ℚᶜᵘⁿ_[p,T])) := by
    apply Filter.Tendsto.congr (fun M => (h_partial_sum_one M).symm)
    exact tendsto_const_nhds
  have h_eq : (1 : ℚᶜᵘⁿ_[p,T]) = 0 := tendsto_nhds_unique h_tend_one htend
  exact one_ne_zero h_eq

/-! #### Cauchy property + limit of integer partial sums (Sub-tasks 1B, 1C) -/

/-- T-scaled analogue of `existsCanonicalExpansionAux.intPartial_isCauchy`
(Poonen line 876).  Stated in `CauchySeq` form (the form actually consumed by
`Texists_lim_intPartial`).  Strategy: bound `Valued.v (TintPartial K' - TintPartial K)`
by `ofAdd(-(min K K' + 1))` via `Tpartial_sum_valuation_cauchy`, convert to ε-form via
`WithZeroMulInt.toNNReal`, and use `tendsto_pow_atTop_nhds_zero_of_lt_one`. -/
private lemma TintPartial_isCauchy
    (x : TLiftedPAdicHahnSeries p T) (g : ℚ) :
    CauchySeq (fun K : ℤ => TintPartial p T x g K) := by
  rw [show CauchySeq (fun K : ℤ => TintPartial p T x g K) =
        Cauchy (Filter.atTop.map (fun K : ℤ => TintPartial p T x g K)) from rfl,
      Valued.cauchy_iff]
  refine ⟨Filter.map_neBot, ?_⟩
  intro γ
  have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
  have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
    WithZeroMulInt.toNNReal_strictMono hp1
  have hpinv_lt : (p : NNReal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hpinv_nn : 0 ≤ ((p : NNReal)⁻¹ : NNReal) := zero_le
  -- In v4.31 `γ : (ValueGroup₀ Valued.v)ˣ`; bridge to a `WithZero (Multiplicative ℤ)` bound `c`.
  set c : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc_def
  have hγ_ne : c ≠ 0 := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  set ε : NNReal :=
    WithZeroMulInt.toNNReal (p_ne_zero p) c with hε_def
  have hε_pos : (0 : NNReal) < ε := by
    rw [hε_def]
    exact WithZeroMulInt.toNNReal_pos (p_ne_zero p) hγ_ne
  have htendsto : Filter.Tendsto (fun n : ℕ => ((p : NNReal)⁻¹) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hpinv_nn hpinv_lt
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ((p : NNReal)⁻¹) ^ N < ε := by
    have h_eventually : ∀ᶠ n : ℕ in Filter.atTop, ((p : NNReal)⁻¹) ^ n < ε :=
      htendsto.eventually (eventually_lt_nhds hε_pos)
    exact h_eventually.exists
  -- Helper: convert a `≤ ofAdd(-(L+1))` bound (with L ≥ N - 1) into a `< γ.1` bound.
  have h_convert : ∀ L : ℤ, (N : ℤ) - 1 ≤ L →
      ∀ a : ℚᶜᵘⁿ_[p,T],
        Valued.v a ≤
          ((Multiplicative.ofAdd (-(L + 1) : ℤ) : Multiplicative ℤ) : WithZero _) →
        Valued.v.restrict a < γ.1 := by
    intro L hL a hbound
    rw [Valuation.restrict_lt_iff_lt_embedding, ← hc_def]
    have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p) (Valued.v a) ≤
        WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(L + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) :=
      hsm.monotone hbound
    have htoNN : WithZeroMulInt.toNNReal (p_ne_zero p)
        (((Multiplicative.ofAdd (-(L + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) =
        (p : NNReal) ^ (-(L + 1)) := by
      rw [WithZeroMulInt.toNNReal_neg_apply (p_ne_zero p) WithZero.coe_ne_zero, WithZero.unzero_coe]
      congr 1
    rw [htoNN] at h_nnreal_le
    have h_pow_le : (p : NNReal) ^ (-(L + 1)) ≤ ((p : NNReal)⁻¹) ^ N := by
      rw [show (p : NNReal) ^ (-(L + 1)) = ((p : NNReal)⁻¹) ^ ((L : ℤ) + 1) from by
        rw [zpow_neg, ← inv_zpow]]
      rw [show ((p : NNReal)⁻¹) ^ ((L : ℤ) + 1) = ((p : NNReal)⁻¹) ^ ((L + 1).toNat) from by
        rw [← zpow_natCast]
        congr 1
        omega]
      apply pow_le_pow_of_le_one hpinv_nn (le_of_lt hpinv_lt)
      omega
    have h_combined : WithZeroMulInt.toNNReal (p_ne_zero p) (Valued.v a) < ε :=
      lt_of_le_of_lt (h_nnreal_le.trans h_pow_le) hN
    rw [hε_def] at h_combined
    exact hsm.lt_iff_lt.mp h_combined
  refine ⟨{ a | ∃ K : ℤ, (N : ℤ) - 1 ≤ K ∧ a = TintPartial p T x g K }, ?_, ?_⟩
  · rw [Filter.mem_map]
    exact Filter.mem_of_superset (Filter.Ici_mem_atTop ((N : ℤ) - 1))
      (fun K hK => ⟨K, hK, rfl⟩)
  · intro a ha b hb
    obtain ⟨K, hK, rfl⟩ := ha
    obtain ⟨K', hK', rfl⟩ := hb
    rcases le_total K K' with hKK' | hKK'
    · -- K ≤ K': use bound at K
      have hbound := Tpartial_sum_valuation_cauchy p T x g K K' hKK'
      exact h_convert K hK _ hbound
    · -- K' ≤ K: bound at K' applied to negated sum
      have hbound := Tpartial_sum_valuation_cauchy p T x g K' K hKK'
      have hneg : TintPartial p T x g K' - TintPartial p T x g K =
          -(TintPartial p T x g K - TintPartial p T x g K') := by ring
      rw [hneg, Valuation.map_neg]
      exact h_convert K' hK' _ hbound

/-- Algebra-map square commutativity: viewing `OQpCUn_embd` followed by `algebraMap` to `K`
agrees with `algebraMap` to `K₀` followed by the field inclusion `K₀ ↪ K`. -/
private lemma algebraMap_OQpCUn_embd_compat_early (a : ℤᶜᵘⁿ_[p]) :
    algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (OQpCUn_embd p T a) =
      algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a) := by
  change algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) a) =
    QpCUn_embd p T (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a)
  unfold QpCUn_embd
  exact (IsFractionRing.lift_algebraMap (g :=
    (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])).comp (OQpCUn_embd p T)) _ a).symm

/-- The integer-side valuation identity for the totally ramified extension `K₀ ↪ K`. -/
private lemma valued_v_algebraMap_K₀_K_int_early (a : ℤᶜᵘⁿ_[p]) :
    Valued.v (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a)) =
      (Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a))^T := by
  rw [← algebraMap_OQpCUn_embd_compat_early]
  by_cases ha : a = 0
  · subst ha; simp [map_zero, zero_pow (NeZero.ne T)]
  · obtain ⟨n, h⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha
      (WittVector.irreducible p)
    obtain ⟨u, hu⟩ := h.symm
    rw [← hu]
    rw [map_mul (OQpCUn_embd p T), map_pow (OQpCUn_embd p T)]
    rw [map_mul, map_pow]
    rw [Valuation.map_mul, Valuation.map_pow]
    rw [show algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (((p : ℕ) : ℤᶜᵘⁿ_[p]) ^ n * u.val) =
          algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (((p : ℕ) : ℤᶜᵘⁿ_[p])) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val from by
      rw [map_mul, map_pow]]
    rw [Valuation.map_mul, Valuation.map_pow]
    have h_unit_K : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
        (OQpCUn_embd p T u.val)) = 1 := by
      have hunit : IsUnit (OQpCUn_embd p T u.val) :=
        (OQpCUn_embd p T).isUnit_map u.isUnit
      obtain ⟨v, hv⟩ := hunit
      rw [← hv]
      exact Tvalued_v_algebraMap_unit_one (p := p) (T := T) v
    have h_unit_K0 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) = 1 := by
      have h1 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) ≤ 1 :=
        (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).valuation_le_one u.val
      have h2 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.inv) ≤ 1 :=
        (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).valuation_le_one u.inv
      have h3 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) *
          Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.inv) = 1 := by
        rw [← Valuation.map_mul, ← map_mul, u.val_inv, map_one, Valuation.map_one]
      have hpos : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) ≠ 0 := by
        intro hz
        rw [hz, zero_mul] at h3
        exact zero_ne_one h3
      exact le_antisymm h1 (by
        rcases (eq_or_lt_of_le h1) with hEq | hLt
        · exact le_of_eq hEq.symm
        · exfalso
          have hprod : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) *
              Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.inv) < 1 :=
            mul_lt_one_of_lt_of_le hLt h2
          rw [h3] at hprod
          exact lt_irrefl _ hprod)
    rw [h_unit_K, h_unit_K0, mul_one, mul_pow, one_pow, mul_one, ← pow_mul]
    have hLHS : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          (OQpCUn_embd p T ((p : ℕ) : ℤᶜᵘⁿ_[p]))) =
        ((Multiplicative.ofAdd (-(T : ℤ)) : Multiplicative ℤ) : WithZero _) := by
      rw [show OQpCUn_embd p T ((p : ℕ) : ℤᶜᵘⁿ_[p]) = (pInvT p T) ^ T from
            (pInvT_pow_T p T).symm]
      rw [map_pow]
      rw [show algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (pInvT p T) = pInvTQ p T from rfl]
      rw [show ((pInvTQ p T) ^ T) = ((pInvTQ p T) ^ ((T : ℤ))) by rfl]
      exact valued_v_pInvT_zpow (p := p) (T := T) (T : ℤ)
    have hRHS : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) ((p : ℕ) : ℤᶜᵘⁿ_[p])) =
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
      rw [QpCUn.valued_algebraMap]
      have hirr : Irreducible ((p : ℕ) : ℤᶜᵘⁿ_[p]) := WittVector.irreducible p
      have hpe : (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).asIdeal =
          Ideal.span {((p : ℕ) : ℤᶜᵘⁿ_[p])} := hirr.maximalIdeal_eq
      rw [IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
        (WittVector.p_nonzero p _) hpe]
      rfl
    rw [hLHS, hRHS, ← WithZero.coe_pow, ← WithZero.coe_pow]
    congr 1
    rw [← ofAdd_nsmul, ← ofAdd_nsmul]
    congr 1
    ring_nf
    rw [mul_comm]

/-- The ramification-index valuation identity `v_K(ι̃ z) = (v_{K₀}(z))^T`. -/
private lemma valued_v_algebraMap_K₀_K_early (z : ℚᶜᵘⁿ_[p]) :
    Valued.v (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) z) = (Valued.v z)^T := by
  obtain ⟨a, b, _, hz⟩ := IsFractionRing.div_surjective (A := ℤᶜᵘⁿ_[p]) z
  rw [← hz]
  simp only [map_div₀, div_pow]
  rw [valued_v_algebraMap_K₀_K_int_early, valued_v_algebraMap_K₀_K_int_early]

/-- The algebra map `K₀ ↪ K` is continuous at `0`. -/
private lemma tendsto_algebraMap_K₀_K_zero_early :
    Filter.Tendsto (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) (nhds 0) (nhds 0) := by
  rw [(Valued.hasBasis_nhds_zero (ℚᶜᵘⁿ_[p,T]) _).tendsto_right_iff]
  intro γ _
  -- In v4.31 `γ : (ValueGroup₀ Valued.v)ˣ`; work with its `WithZero (Multiplicative ℤ)` image.
  set c : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc_def
  have hc_ne : c ≠ 0 := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  set γ_m : Multiplicative ℤ := WithZero.unzero hc_ne with hγ_m_def
  set n : ℤ := Multiplicative.toAdd γ_m with hn_def
  set k : ℤ := min (n - 1) (-1) with hk_def
  have hk_lt_n : k ≤ n - 1 := min_le_left _ _
  have hT_pos : 0 < (T : ℤ) := by exact_mod_cast Nat.pos_of_neZero T
  have hkT : k * T < n := by
    have h1 : k * T ≤ k * 1 := by
      apply mul_le_mul_of_nonpos_left
      · exact_mod_cast hT_pos
      · linarith [min_le_right (n - 1) (-1)]
    have h2 : k * 1 = k := mul_one _
    linarith
  -- Source bound: the ball `{z | Valued.v z < ofAdd k}` on `ℚᶜᵘⁿ_[p]`.
  rw [Filter.eventually_iff]
  have hsrc : {z : ℚᶜᵘⁿ_[p] | Valued.v z <
      ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero _)} ∈ nhds (0 : ℚᶜᵘⁿ_[p]) :=
    mem_nhds_zero_v_lt WithZero.coe_ne_zero
  refine Filter.mem_of_superset hsrc ?_
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz ⊢
  -- Goal: `Valued.v.restrict (algebraMap z) < γ.1`, i.e. `Valued.v (algebraMap z) < c`.
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc_def, valued_v_algebraMap_K₀_K_early]
  have hc_eq : c = ((γ_m : Multiplicative ℤ) : WithZero _) :=
    (WithZero.coe_unzero hc_ne).symm
  have hγm_eq : γ_m = Multiplicative.ofAdd n := rfl
  calc (Valued.v z)^T
      ≤ (((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero _))^T := by
        apply pow_le_pow_left₀ _ (le_of_lt hz)
        exact zero_le (a := Valued.v z)
    _ < c := by
        rw [← WithZero.coe_pow]
        rw [show ((Multiplicative.ofAdd k : Multiplicative ℤ)^T : Multiplicative ℤ) =
              Multiplicative.ofAdd (k * T) from by
          rw [← ofAdd_nsmul]; congr 1; ring]
        rw [hc_eq, hγm_eq, WithZero.coe_lt_coe]
        exact Multiplicative.ofAdd_lt.mpr hkT

/-- Continuity of `algebraMap K₀ → K`. -/
private lemma continuous_algebraMap_K₀_K_early :
    Continuous (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) := by
  have h0 : ContinuousAt (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) 0 := by
    rw [ContinuousAt, map_zero]
    exact tendsto_algebraMap_K₀_K_zero_early p T
  exact continuous_of_continuousAt_zero
    (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])).toAddMonoidHom h0

-- The valuation on `ℚᶜᵘⁿ_[p,T]` is rank-one discrete (transferred from the adic valuation on
-- `FractionRing ℤᶜᵘⁿ_[p,T]` via the value-group equality for `WithVal`). In v4.31 `RankOne` no
-- longer takes a bare `hom`/`exists_val_nontrivial`; we build it through `IsRankOneDiscrete`.
noncomputable instance :
    (Valued.v : Valuation ℚᶜᵘⁿ_[p,T] (WithZero (Multiplicative ℤ))).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    have h : ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation
        (FractionRing (ℤᶜᵘⁿ_[p,T]))).IsRankOneDiscrete := inferInstance
    obtain ⟨γ, hγ, hγ1⟩ := h.exists_generator_lt_one'
    exact ⟨γ, by rw [WithVal.valueGroup_eq]; exact hγ, hγ1⟩

noncomputable instance :
  Valuation.RankOne (Valued.v : Valuation ℚᶜᵘⁿ_[p,T] (WithZero (Multiplicative ℤ))) :=
  Valuation.IsRankOneDiscrete.rankOne
    (v := (Valued.v : Valuation ℚᶜᵘⁿ_[p,T] (WithZero (Multiplicative ℤ))))
    (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt : (1 : NNReal) < (p : NNReal))

noncomputable instance : NontriviallyNormedField ℚᶜᵘⁿ_[p,T] :=
  Valued.toNontriviallyNormedField (ℚᶜᵘⁿ_[p,T]) (WithZero (Multiplicative ℤ))

-- Surjectivity of `Valued.v` on `ℚᶜᵘⁿ_[p,T]` (via the `WithVal` bridge to the height-one
-- valuation on `FractionRing ℤᶜᵘⁿ_[p,T]`). Used by the norm/lift bridges below.
private lemma Tvalued_v_surjective :
    Function.Surjective (Valued.v : ℚᶜᵘⁿ_[p,T] → WithZero (Multiplicative ℤ)) := by
  intro x
  obtain ⟨y, hy⟩ := (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_surjective
    (FractionRing (ℤᶜᵘⁿ_[p,T])) x
  exact ⟨WithVal.toVal _ y, by rw [WithVal.valued_toVal]; exact hy⟩

/-- The norm on `ℚᶜᵘⁿ_[p,T]` is the real number `toNNReal (v a)`: the rank-one valuation `v`
composed with the base-`p` embedding of the value group into `ℝ≥0`. -/
-- v4.31: `‖·‖` on the `Valued.toNormedField` is `RankOne.hom (Valued.v.restrict ·)`, no longer
-- defeq to `toNNReal (Valued.v ·)`; bridge through the rank-one `hom` plus surjectivity.
lemma Tnorm_eq_toNNReal_valued (a : ℚᶜᵘⁿ_[p,T]) :
    ‖a‖ = ((WithZeroMulInt.toNNReal (p_ne_zero p) (Valued.v a) : NNReal) : ℝ) := by
  rw [Valued.toNormedField.norm_def]
  norm_cast
  rw [show (Valuation.RankOne.hom (Valued.v : Valuation ℚᶜᵘⁿ_[p,T] _)) (Valued.v.restrict a)
        = WithZeroMulInt.toNNReal (p_ne_zero p)
            ((Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt
              (v := (Valued.v : Valuation ℚᶜᵘⁿ_[p,T] _))) (Valued.v.restrict a)) from rfl,
     Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
       (Tvalued_v_surjective p T) a]

/-- An element of `ℚᶜᵘⁿ_[p,T]` with valuation `≤ 1` lifts to the ring of integers `ℤᶜᵘⁿ_[p,T]`; i.e.
the valuation ring is exactly the closed unit ball. -/
-- Routes through the `FractionRing` to avoid the `whnf` timeout on the `WithVal` structure.
lemma Texists_lift_of_valued_le_one {z : ℚᶜᵘⁿ_[p,T]} (hz : Valued.v z ≤ 1) :
    ∃ a : ℤᶜᵘⁿ_[p,T], algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) a = z := by
  have hz' : ((IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation
      ((FractionRing (ℤᶜᵘⁿ_[p,T])))) (WithVal.equiv _ z) ≤ 1 := by
    rw [WithVal.val_apply_equiv]; exact hz
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one
    (A := ℤᶜᵘⁿ_[p,T]) (K := FractionRing (ℤᶜᵘⁿ_[p,T])) hz'
  refine ⟨a, ?_⟩
  apply (WithVal.equiv _).injective
  rw [WithVal.algebraMap_right_apply] at *
  simpa [WithVal.equiv] using ha

instance : ContinuousSMul (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) :=
    continuousSMul_of_algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (continuous_algebraMap_K₀_K_early p T)

/-- The `Valued`-induced topology on `ℚᶜᵘⁿ_[p,T]` is complete.

Discharged via `FiniteDimensional.complete` over the finite extension
`ℚᶜᵘⁿ_[p,T] / ℚᶜᵘⁿ_[p]`.  We first view both fields as rank-one nonarchimedean
normed fields using their `Valued` structures, then obtain `ContinuousSMul`
from `isModuleTopologyOfFiniteDimensional`. -/
instance instCompleteSpaceQpCUnT : CompleteSpace (ℚᶜᵘⁿ_[p,T]) :=
  FiniteDimensional.complete (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])

/-- T-scaled analogue of `existsCanonicalExpansionAux.exists_lim_intPartial`
(Poonen line 1043).  The integer-cutoff partial sums converge to a limit in the
complete DVF `ℚᶜᵘⁿ_[p,T]`. -/
private lemma Texists_lim_intPartial
    (x : TLiftedPAdicHahnSeries p T) (g : ℚ) :
    ∃ y : ℚᶜᵘⁿ_[p,T], Filter.Tendsto (TintPartial p T x g) Filter.atTop (nhds y) :=
  ⟨_, (TintPartial_isCauchy p T x g).tendsto_limUnder⟩

/-! ### Phase 2A infrastructure: per-element Teichmüller digits -/

/-- The residue field of `ℤᶜᵘⁿ_[p]` is canonically isomorphic to `Fpbar p`.

Built from `WittVector.quotientPEquiv : 𝕎 k ⧸ (p) ≃+* k` and the fact that the maximal
ideal of `ℤᶜᵘⁿ_[p] = 𝕎 (Fpbar p)` is `(p)`. -/
private noncomputable def TResidueIsoFpbar :
    IsLocalRing.ResidueField (ℤᶜᵘⁿ_[p]) ≃+* Fpbar p :=
  (Ideal.quotEquivOfEq (WittVector.irreducible p).maximalIdeal_eq).trans
    WittVector.quotientPEquiv

/-- The composite residue map `ℤᶜᵘⁿ_[p,T] →+* Fpbar p`.  Sends `pInvT` to `0` and
`algebraMap (teichmuller p α)` to `α`. -/
private noncomputable def TRes : ℤᶜᵘⁿ_[p,T] →+* Fpbar p :=
  (TResidueIsoFpbar p).toRingHom.comp (TResidue p T)

/-- The Teichmüller section `Fpbar p →* ℤᶜᵘⁿ_[p,T]`, lifting `WittVector.teichmuller p`
through the inclusion `ℤᶜᵘⁿ_[p] → ℤᶜᵘⁿ_[p,T]`.

Only a `MonoidHom`, not a `RingHom` — `teichmuller` is multiplicative but not additive. -/
private noncomputable def TTeichmuller : Fpbar p →* ℤᶜᵘⁿ_[p,T] :=
  ((algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])).toMonoidHom).comp (teichmuller p)

/-- **Step 2a key identity.**  `TRes (TTeichmuller α) = α`. -/
private lemma TRes_TTeichmuller (α : Fpbar p) :
    TRes p T (TTeichmuller p T α) = α := by
  change (TResidueIsoFpbar p) (TResidue p T (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])
      (teichmuller p α))) = α
  rw [TResidue_of]
  show (TResidueIsoFpbar p) (IsLocalRing.residue (ℤᶜᵘⁿ_[p]) (teichmuller p α)) = α
  unfold TResidueIsoFpbar
  change WittVector.quotientPEquiv
      ((Ideal.quotEquivOfEq (WittVector.irreducible p).maximalIdeal_eq)
        (Ideal.Quotient.mk _ (teichmuller p α))) = α
  rw [Ideal.quotEquivOfEq_mk]
  change WittVector.quotientPEquiv (Quot.mk _ (teichmuller p α)) = α
  rw [WittVector.quotientPEquiv_mk]
  change (teichmuller p α).coeff 0 = α
  exact WittVector.teichmuller_coeff_zero p α

/-- For any `r : ℤᶜᵘⁿ_[p,T]`, `r` and `TTeichmuller (TRes r)` have the same residue. -/
private lemma TResidue_TTeichmuller_TRes (r : ℤᶜᵘⁿ_[p,T]) :
    TResidue p T (TTeichmuller p T (TRes p T r)) = TResidue p T r := by
  apply (TResidueIsoFpbar p).injective
  change TRes p T (TTeichmuller p T (TRes p T r)) = TRes p T r
  exact TRes_TTeichmuller p T (TRes p T r)

/-- `pInvT` divides `r - TTeichmuller (TRes r)` for every `r : ℤᶜᵘⁿ_[p,T]`. -/
private lemma pInvT_dvd_sub_TTeichmuller_TRes (r : ℤᶜᵘⁿ_[p,T]) :
    pInvT p T ∣ r - TTeichmuller p T (TRes p T r) := by
  apply (TResidue_eq_zero_iff p T _).mp
  rw [map_sub, TResidue_TTeichmuller_TRes, sub_self]

/-- The recursive residual sequence used to extract Teichmüller digits.
`TpInvTResidual z 0 = z`; `TpInvTResidual z (n+1) := (r n - TTeich(TRes (r n))) / pInvT`. -/
private noncomputable def TpInvTResidual (z : ℤᶜᵘⁿ_[p,T]) : ℕ → ℤᶜᵘⁿ_[p,T]
  | 0 => z
  | n+1 => (pInvT_dvd_sub_TTeichmuller_TRes p T (TpInvTResidual z n)).choose

/-- The `n`-th Teichmüller digit of `z` (as a `Fpbar p`-valued sequence). -/
private noncomputable def TpInvTDigit (z : ℤᶜᵘⁿ_[p,T]) (n : ℕ) : Fpbar p :=
  TRes p T (TpInvTResidual p T z n)

/-- The defining recursion: each step pulls out a factor of `pInvT`. -/
private lemma TpInvTResidual_succ_eq (z : ℤᶜᵘⁿ_[p,T]) (n : ℕ) :
    TpInvTResidual p T z n - TTeichmuller p T (TpInvTDigit p T z n) =
      pInvT p T * TpInvTResidual p T z (n+1) :=
  (pInvT_dvd_sub_TTeichmuller_TRes p T (TpInvTResidual p T z n)).choose_spec

/-- Auxiliary partial-sum identity: after subtracting the first `n+1` Teichmüller terms
from `z`, the remainder equals `(pInvT)^(n+1) * r(n+1)`. -/
private lemma TpInvT_partial_sum_eq (z : ℤᶜᵘⁿ_[p,T]) (n : ℕ) :
    z - ∑ i ∈ Finset.Iic n, (pInvT p T)^i * TTeichmuller p T (TpInvTDigit p T z i) =
      (pInvT p T)^(n+1) * TpInvTResidual p T z (n+1) := by
  induction n with
  | zero =>
    rw [show Finset.Iic (0 : ℕ) = {0} from rfl, Finset.sum_singleton, pow_zero, one_mul,
      pow_one]
    have h := TpInvTResidual_succ_eq p T z 0
    change z - TTeichmuller p T (TpInvTDigit p T z 0) =
      pInvT p T * TpInvTResidual p T z 1
    -- TpInvTResidual z 0 = z by defn
    have hr0 : TpInvTResidual p T z 0 = z := rfl
    rw [← hr0]
    exact h
  | succ n ih =>
    rw [show Finset.Iic (n + 1) = insert (n + 1) (Finset.Iic n) from by
      ext x; simp [Finset.mem_Iic]; omega]
    rw [Finset.sum_insert (by simp)]
    -- LHS = z - (term_{n+1} + sum_n)
    have hstep := TpInvTResidual_succ_eq p T z (n + 1)
    -- hstep: r(n+1) - TTeich(d(n+1)) = pInvT * r(n+2)
    calc z - ((pInvT p T)^(n+1) * TTeichmuller p T (TpInvTDigit p T z (n+1)) +
            ∑ i ∈ Finset.Iic n, (pInvT p T)^i * TTeichmuller p T (TpInvTDigit p T z i))
        = (z - ∑ i ∈ Finset.Iic n, (pInvT p T)^i *
              TTeichmuller p T (TpInvTDigit p T z i)) -
            (pInvT p T)^(n+1) * TTeichmuller p T (TpInvTDigit p T z (n+1)) := by ring
      _ = (pInvT p T)^(n+1) * TpInvTResidual p T z (n+1) -
            (pInvT p T)^(n+1) * TTeichmuller p T (TpInvTDigit p T z (n+1)) := by rw [ih]
      _ = (pInvT p T)^(n+1) * (TpInvTResidual p T z (n+1) -
              TTeichmuller p T (TpInvTDigit p T z (n+1))) := by ring
      _ = (pInvT p T)^(n+1) * (pInvT p T * TpInvTResidual p T z (n+2)) := by rw [hstep]
      _ = (pInvT p T)^(n+1+1) * TpInvTResidual p T z (n+1+1) := by ring

/-- **Phase 2A digit lemma** (T-DVR analogue of
`WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff`).

For every `z : ℤᶜᵘⁿ_[p,T]`, there exist Teichmüller digits `a : ℕ → Fpbar p` such that
for every `n`, `(pInvT)^(n+1)` divides `z - ∑ i ≤ n, (pInvT)^i * algMap (teichmuller p (a i))`. -/
private lemma Texists_T_pInvT_digits (z : ℤᶜᵘⁿ_[p,T]) :
    ∃ a : ℕ → Fpbar p,
      ∀ n : ℕ,
        (pInvT p T)^(n+1) ∣ z - ∑ i ∈ Finset.Iic n,
          (pInvT p T)^i * algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (a i)) := by
  refine ⟨TpInvTDigit p T z, fun n => ?_⟩
  refine ⟨TpInvTResidual p T z (n+1), ?_⟩
  have h := TpInvT_partial_sum_eq p T z n
  -- TTeichmuller α = algebraMap (teichmuller p α) by defn
  change z - ∑ i ∈ Finset.Iic n,
      (pInvT p T)^i * algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])
        (teichmuller p (TpInvTDigit p T z i)) =
      (pInvT p T)^(n+1) * TpInvTResidual p T z (n+1)
  exact h

set_option maxHeartbeats 1000000 in
-- maxHeartbeats: heavy elaboration in the multi-phase proof body (mirrors
-- exists_teichmuller_digits)
/-- **Phase 2A wrapper** — T-port of `exists_teichmuller_digits`.

For every `y : ℚᶜᵘⁿ_[p,T]`, there exist Teichmüller digits `b : ℤ → Fpbar p` and a
cutoff `m₀ : ℤ` such that `b k = 0` for `k < m₀` and the partial sums
`∑_{k ∈ [m₀, K]} (pInvTQ p T)^k * algMap (teichmuller p (b k))` converge to `y`. -/
private lemma Texists_teichmuller_digits (y : ℚᶜᵘⁿ_[p,T]) :
    ∃ (b : ℤ → Fpbar p) (m₀ : ℤ),
      (∀ k : ℤ, k < m₀ → b k = 0) ∧
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m₀ K,
          (pInvTQ p T) ^ k *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b k))))
        Filter.atTop (nhds y) := by
  by_cases hy : y = 0
  · -- Case 1: y = 0. Take b ≡ 0, m₀ = 0.
    refine ⟨0, 0, fun _ _ => rfl, ?_⟩
    rw [hy]
    have hzero : (fun K : ℤ => ∑ k ∈ Finset.Icc (0 : ℤ) K,
        (pInvTQ p T) ^ k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])
            (teichmuller p ((0 : ℤ → Fpbar p) k)))) = fun _ => (0 : ℚᶜᵘⁿ_[p,T]) := by
      funext K
      apply Finset.sum_eq_zero
      intro k _
      simp
    rw [hzero]
    exact tendsto_const_nhds
  · -- Case 2: y ≠ 0.
    have hv_ne : Valued.v y ≠ 0 := by simp [hy]
    set m' : Multiplicative ℤ := WithZero.unzero hv_ne with hm'_def
    set m₀ : ℤ := -m'.toAdd with hm₀_def
    have hvy_eq : Valued.v y = (m' : WithZero (Multiplicative ℤ)) := by
      rw [hm'_def, WithZero.coe_unzero]
    have hm'_eq : (m' : WithZero (Multiplicative ℤ)) =
        ((Multiplicative.ofAdd (-m₀ : ℤ) : Multiplicative ℤ) : WithZero _) := by
      rw [hm₀_def, neg_neg]
      congr
    have hpn_val := valued_v_pInvT_zpow (p := p) (T := T)
    -- z := pInvTQ^(-m₀) * y, Valued.v z = 1
    set z : ℚᶜᵘⁿ_[p,T] := (pInvTQ p T)^(-m₀) * y with hz_def
    have hpInvTQ_ne : pInvTQ p T ≠ 0 := by
      unfold pInvTQ
      intro h
      exact pInvT_ne_zero p T
        ((IsFractionRing.injective (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]))
          (by simpa using h))
    have hvz : Valued.v z = 1 := by
      rw [hz_def, Valuation.map_mul, hpn_val (-m₀), hvy_eq, hm'_eq]
      rw [← WithZero.coe_mul]
      rw [show (Multiplicative.ofAdd (-(-m₀) : ℤ) * Multiplicative.ofAdd (-m₀ : ℤ)
            : Multiplicative ℤ) = 1 from by
        rw [← ofAdd_add]; simp]
      rfl
    have hvz_le : Valued.v z ≤ 1 := hvz.le
    -- Lift z to ℤᶜᵘⁿ_[p,T]
    obtain ⟨z', hz'⟩ := Texists_lift_of_valued_le_one p T hvz_le
    -- Apply Texists_T_pInvT_digits
    obtain ⟨a, ha⟩ := Texists_T_pInvT_digits p T z'
    let b : ℤ → Fpbar p := fun k =>
      if h : 0 ≤ k - m₀ then a (k - m₀).toNat else 0
    refine ⟨b, m₀, ?_, ?_⟩
    · intro k hk
      have hneg : ¬ (0 ≤ k - m₀) := by linarith
      change (if h : 0 ≤ k - m₀ then a (k - m₀).toNat else 0) = 0
      rw [dif_neg hneg]
    · -- Tendsto via bound argument
      -- Bound: for K ≥ m₀, Valued.v (y - partial_sum K) ≤ ofAdd(-(K+1))
      have hbound : ∀ K : ℤ, m₀ ≤ K → Valued.v (y -
          ∑ k ∈ Finset.Icc m₀ K,
            (pInvTQ p T) ^ k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b k)))) ≤
        ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
        intro K hK
        set n : ℕ := (K - m₀).toNat with hn_def
        have hK_eq : K = m₀ + (n : ℤ) := by rw [hn_def]; omega
        -- Apply digit lemma at z'
        have hdigit : (pInvT p T)^(n+1) ∣ z' - ∑ i ∈ Finset.Iic n,
            (pInvT p T)^i * algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (a i)) :=
          ha n
        obtain ⟨c, hc⟩ := hdigit
        -- Transport to ℚᶜᵘⁿ_[p,T]
        have halg := congrArg (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])) hc
        simp only [map_sub, map_sum, map_mul, map_pow] at halg
        rw [hz'] at halg
        -- algebraMap (pInvT) = pInvTQ
        have hpInvT_cast : algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (pInvT p T) = pInvTQ p T :=
          rfl
        rw [hpInvT_cast] at halg
        -- y = pInvTQ^m₀ * z
        have hy_eq : y = (pInvTQ p T)^m₀ * z := by
          rw [hz_def, ← mul_assoc, ← zpow_add₀ hpInvTQ_ne, add_neg_cancel,
            zpow_zero, one_mul]
        -- Reindex partial sum
        have hreindex : ∑ k ∈ Finset.Icc m₀ K,
            (pInvTQ p T) ^ k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b k))) =
          (pInvTQ p T)^m₀ * ∑ i ∈ Finset.Iic n,
            (pInvTQ p T)^i * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (a i))) := by
          have hIcc_eq : Finset.Icc m₀ K =
              (Finset.range (n + 1)).map (Nat.castEmbedding.trans <| addLeftEmbedding m₀) := by
            rw [Int.Icc_eq_finset_map]
            congr 1
            have : K + 1 - m₀ = (n : ℤ) + 1 := by rw [hK_eq]; ring
            rw [this]; simp
          rw [hIcc_eq, Finset.sum_map, ← Nat.range_succ_eq_Iic, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
            addLeftEmbedding_apply]
          have hbi : b (m₀ + (i : ℤ)) = a i := by
            change (if h : 0 ≤ (m₀ + (i : ℤ)) - m₀ then
              a ((m₀ + (i : ℤ)) - m₀).toNat else 0) = a i
            have h_nn : (0 : ℤ) ≤ (m₀ + (i : ℤ)) - m₀ := by omega
            rw [dif_pos h_nn]
            congr 1; omega
          rw [hbi, zpow_add₀ hpInvTQ_ne, zpow_natCast]
          ring
        -- y - partial_sum K = pInvTQ^m₀ * (pInvTQ^(n+1) * algebraMap c)
        have hkey : y - ∑ k ∈ Finset.Icc m₀ K,
            (pInvTQ p T) ^ k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b k))) =
          (pInvTQ p T)^m₀ *
            ((pInvTQ p T)^(n+1) * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) c) := by
          rw [hreindex, hy_eq, ← mul_sub, halg]
        rw [hkey]
        rw [Valuation.map_mul, Valuation.map_mul, hpn_val m₀]
        rw [show ((pInvTQ p T)^(n+1) : ℚᶜᵘⁿ_[p,T]) =
              ((pInvTQ p T)^((n : ℤ)+1) : ℚᶜᵘⁿ_[p,T]) from by
          rw [← zpow_natCast (pInvTQ p T) (n+1)]; push_cast; rfl]
        rw [hpn_val ((n : ℤ)+1)]
        have h_alg_le : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) c) ≤ 1 :=
          (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_le_one c
        calc ((Multiplicative.ofAdd (-m₀ : ℤ) : Multiplicative ℤ) : WithZero _) *
            (((Multiplicative.ofAdd (-((n : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) *
              Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) c))
            ≤ ((Multiplicative.ofAdd (-m₀ : ℤ) : Multiplicative ℤ) : WithZero _) *
              (((Multiplicative.ofAdd (-((n : ℤ) + 1)) : Multiplicative ℤ) :
                  WithZero _) * 1) :=
              mul_le_mul' (le_refl _) (mul_le_mul' (le_refl _) h_alg_le)
          _ = ((Multiplicative.ofAdd (-m₀ : ℤ) : Multiplicative ℤ) : WithZero _) *
              (((Multiplicative.ofAdd (-((n : ℤ) + 1)) : Multiplicative ℤ) :
                  WithZero _)) := by rw [mul_one]
          _ = ((Multiplicative.ofAdd ((-m₀) + (-((n : ℤ) + 1))) : Multiplicative ℤ) :
                WithZero _) := by rw [← WithZero.coe_mul, ← ofAdd_add]
          _ = ((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
              congr 2; omega
      -- Convert bound to Tendsto
      have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
      have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
      have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
        WithZeroMulInt.toNNReal_strictMono hp1
      have hpinv_lt : (p : NNReal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
      have hpinv_nn : 0 ≤ ((p : NNReal)⁻¹ : NNReal) := zero_le
      rw [Filter.tendsto_iff_forall_eventually_mem]
      intro U hU
      obtain ⟨γ, hγ_ne, hγ⟩ := Texists_v_sub_lt_subset p T hU
      set ε : NNReal :=
        WithZeroMulInt.toNNReal (p_ne_zero p) (γ : WithZero (Multiplicative ℤ)) with hε_def
      have hε_pos : (0 : NNReal) < ε := by
        rw [hε_def]
        exact WithZeroMulInt.toNNReal_pos (p_ne_zero p) hγ_ne
      have htendsto : Filter.Tendsto (fun n : ℕ => ((p : NNReal)⁻¹)^n)
          Filter.atTop (nhds 0) :=
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
      change Valued.v ((∑ k ∈ Finset.Icc m₀ K,
        (pInvTQ p T) ^ k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b k)))) - y) < γ
      rw [Valuation.map_sub_swap]
      have h1 := hbound K hK_ge_m₀
      have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p)
          (Valued.v (y - ∑ k ∈ Finset.Icc m₀ K,
            (pInvTQ p T) ^ k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b k))))) ≤
          WithZeroMulInt.toNNReal (p_ne_zero p)
            (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) :=
        hsm.monotone h1
      have htoNN : WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(K + 1) : ℤ) : Multiplicative ℤ) : WithZero _)) =
          (p : NNReal)^(-(K + 1)) := by
        rw [WithZeroMulInt.toNNReal_neg_apply (p_ne_zero p) WithZero.coe_ne_zero,
          WithZero.unzero_coe]
        congr 1
      rw [htoNN] at h_nnreal_le
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
            (pInvTQ p T) ^ k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b k))))) < ε :=
        (h_nnreal_le.trans h_pow_le).trans_lt hN
      rw [hε_def] at h_chain
      exact hsm.lt_iff_lt.mp h_chain

/-! ### Phase 2B: uniqueness of Teichmüller digits -/

omit [NeZero T] in
/-- **Helper.** `TTeichmuller (0 : Fpbar p) = 0`. Needed because `TTeichmuller`
is only a `MonoidHom`, so `MonoidHom.map_zero` does not apply directly. -/
private lemma TTeichmuller_zero : TTeichmuller p T (0 : Fpbar p) = 0 := by
  change algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (0 : Fpbar p)) = 0
  rw [WittVector.teichmuller_zero, map_zero]

/-- **Helper A.** `TTeichmuller p T` is injective. Composition of
`OQpCUn_embd_injective` with `injective_teichmuller`. -/
private lemma Tinjective_TTeichmuller :
    Function.Injective (TTeichmuller p T) :=
  (OQpCUn_embd_injective p T).comp (injective_teichmuller p)

set_option maxHeartbeats 1000000 in
-- maxHeartbeats: heavy elaboration in the multi-phase proof body (mirrors
-- teichmuller_digits_unique)
/-- **Phase 2B (T-Lemma 4.5).** Uniqueness of Teichmüller digits for `ℚᶜᵘⁿ_[p,T]`.
T-scaled analogue of `teichmuller_digits_unique` (Poonen 1336–1818).

Steps 1–7 follow Poonen mechanically with the substitution rule
`(p : QpCUn p) ↦ pInvTQ p T`, `(p : OQpCUn p) ↦ pInvT p T`,
`teichmuller ↦ TTeichmuller`, `valued_v_p_zpow ↦ valued_v_pInvT_zpow`.
Step 9 (extraction of leading digit) **diverges**: where Poonen routes through
`WittVector.mem_span_p_pow_iff_le_coeff_eq_zero` + `teichmuller_coeff_zero`,
we use the residue map `TRes` and the identity `TRes_TTeichmuller`. -/
private lemma Tteichmuller_digits_unique
    (b b' : ℤ → Fpbar p) (m₀ m₀' : ℤ)
    (hb : ∀ k : ℤ, k < m₀  → b  k = 0)
    (hb' : ∀ k : ℤ, k < m₀' → b' k = 0)
    {y : ℚᶜᵘⁿ_[p,T]}
    (htb : Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m₀ K,
          (pInvTQ p T) ^ k *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (TTeichmuller p T (b k)))
        Filter.atTop (nhds y))
    (htb' : Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m₀' K,
          (pInvTQ p T) ^ k *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (TTeichmuller p T (b' k)))
        Filter.atTop (nhds y)) :
    ∀ k : ℤ, b k = b' k := by
  -- Step 1. Unify cutoff
  set m : ℤ := min m₀ m₀' with hm_def
  have hm_le_m₀ : m ≤ m₀ := min_le_left _ _
  have hm_le_m₀' : m ≤ m₀' := min_le_right _ _
  have hb_below : ∀ k : ℤ, k < m → b k = 0 := fun k hk => hb k (lt_of_lt_of_le hk hm_le_m₀)
  have hb'_below : ∀ k : ℤ, k < m → b' k = 0 := fun k hk => hb' k (lt_of_lt_of_le hk hm_le_m₀')
  -- Step 2. ℕ-indexed digits.
  let c : ℕ → Fpbar p := fun i => b (m + i)
  let c' : ℕ → Fpbar p := fun i => b' (m + i)
  -- Step 3. Witt-integer partial sum.
  let Spart : (ℕ → Fpbar p) → ℕ → ℤᶜᵘⁿ_[p,T] := fun d N =>
    ∑ i ∈ Finset.Iic N, (pInvT p T)^i * TTeichmuller p T (d i)
  have hpInvTQ_ne : pInvTQ p T ≠ 0 := by
    unfold pInvTQ
    intro h
    exact pInvT_ne_zero p T
      ((IsFractionRing.injective (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]))
        (by simpa using h))
  have hpn_val := valued_v_pInvT_zpow (p := p) (T := T)
  -- Step 4. Replace `Icc m₀ K`-sum with `Icc m K`-sum (extending b by 0).
  have hsum_eq_b : ∀ K : ℤ, ∑ k ∈ Finset.Icc m₀ K,
        (pInvTQ p T)^k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          (TTeichmuller p T (b k)) =
      ∑ k ∈ Finset.Icc m K,
        (pInvTQ p T)^k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          (TTeichmuller p T (b k)) := by
    intro K
    apply Finset.sum_subset
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      exact ⟨le_trans hm_le_m₀ hk.1, hk.2⟩
    · intro k hk hk_not
      rw [Finset.mem_Icc] at hk
      have hk_lt : k < m₀ := by
        by_contra hge
        push Not at hge
        exact hk_not (Finset.mem_Icc.mpr ⟨hge, hk.2⟩)
      rw [hb k hk_lt, TTeichmuller_zero, map_zero, mul_zero]
  have hsum_eq_b' : ∀ K : ℤ, ∑ k ∈ Finset.Icc m₀' K,
        (pInvTQ p T)^k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          (TTeichmuller p T (b' k)) =
      ∑ k ∈ Finset.Icc m K,
        (pInvTQ p T)^k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          (TTeichmuller p T (b' k)) := by
    intro K
    apply Finset.sum_subset
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      exact ⟨le_trans hm_le_m₀' hk.1, hk.2⟩
    · intro k hk hk_not
      rw [Finset.mem_Icc] at hk
      have hk_lt : k < m₀' := by
        by_contra hge
        push Not at hge
        exact hk_not (Finset.mem_Icc.mpr ⟨hge, hk.2⟩)
      rw [hb' k hk_lt, TTeichmuller_zero, map_zero, mul_zero]
  -- Step 5. Bridge sum to algebraMap of Spart.
  have h_to_Spart : ∀ (d : ℕ → Fpbar p) (N : ℕ),
      ∑ i ∈ Finset.Iic N,
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          (TTeichmuller p T (d i)) * (pInvTQ p T)^i =
      algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
        (∑ i ∈ Finset.Iic N, (pInvT p T)^i * TTeichmuller p T (d i)) := by
    intro d N
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, map_pow, mul_comm]
    rfl
  -- Step 6. Build converging shifted sequence.
  set z : ℚᶜᵘⁿ_[p,T] := (pInvTQ p T)^(-m) * y with hz_def
  have h_natTendsto : ∀ (d : ℕ → Fpbar p),
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m K,
          (pInvTQ p T) ^ k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (TTeichmuller p T (d (k - m).toNat)))
        Filter.atTop (nhds y) →
      Filter.Tendsto
        (fun N : ℕ => algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Spart d N))
        Filter.atTop (nhds z) := by
    intro d hd
    have h_mul : Filter.Tendsto
        (fun K : ℤ => (pInvTQ p T)^(-m) *
          ∑ k ∈ Finset.Icc m K, (pInvTQ p T)^k *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (TTeichmuller p T (d (k - m).toNat)))
        Filter.atTop (nhds ((pInvTQ p T)^(-m) * y)) := hd.const_mul _
    have h_compose : Filter.Tendsto (fun N : ℕ => m + (N : ℤ)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_left _ m tendsto_natCast_atTop_atTop
    have h_comp := h_mul.comp h_compose
    change Filter.Tendsto
      (fun N : ℕ => algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Spart d N)) _ _
    apply h_comp.congr
    intro N
    simp only [Function.comp_apply]
    have h_inner_eq : ∀ d : ℕ → Fpbar p, ∀ N : ℕ,
        ∑ k ∈ Finset.Icc m (m + (N : ℤ)),
          (pInvTQ p T)^k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (TTeichmuller p T (d (k - m).toNat)) =
        (pInvTQ p T)^m * ∑ i ∈ Finset.Iic N,
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (TTeichmuller p T (d i)) * (pInvTQ p T)^i := by
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
        rw [h_simp_eq]; simp
      rw [h_toNat, zpow_add₀ hpInvTQ_ne, zpow_natCast]
      ring
    rw [h_inner_eq d N]
    rw [show (pInvTQ p T)^(-m) * ((pInvTQ p T)^m * _) =
        ((pInvTQ p T)^(-m) * (pInvTQ p T)^m) *
        ∑ i ∈ Finset.Iic N,
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (TTeichmuller p T (d i)) * (pInvTQ p T)^i from by ring]
    rw [show (pInvTQ p T)^(-m) * (pInvTQ p T)^m = (1 : ℚᶜᵘⁿ_[p,T]) from by
      rw [← zpow_add₀ hpInvTQ_ne]; rw [neg_add_cancel]; rw [zpow_zero]]
    rw [one_mul]
    rw [h_to_Spart d N]
  have hcb_to_z : Filter.Tendsto
      (fun N : ℕ => algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Spart c N))
      Filter.atTop (nhds z) := by
    apply h_natTendsto c
    have h_eventual : ∀ᶠ K : ℤ in Filter.atTop,
        ∑ k ∈ Finset.Icc m K,
          (pInvTQ p T)^k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (TTeichmuller p T (c (k - m).toNat)) =
        ∑ k ∈ Finset.Icc m₀ K,
          (pInvTQ p T)^k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (TTeichmuller p T (b k)) := by
      filter_upwards [Filter.eventually_ge_atTop m] with K hKm
      have h_inner : ∑ k ∈ Finset.Icc m K,
            (pInvTQ p T)^k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (TTeichmuller p T (c (k - m).toNat)) =
          ∑ k ∈ Finset.Icc m K,
            (pInvTQ p T)^k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (TTeichmuller p T (b k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Icc] at hk
        have h_c_eq : c (k - m).toNat = b k := by
          change b (m + ((k - m).toNat : ℤ)) = b k
          have hkm : (0 : ℤ) ≤ k - m := by linarith
          rw [Int.toNat_of_nonneg hkm]
          ring_nf
        rw [h_c_eq]
      rw [h_inner, hsum_eq_b K]
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm h_eventual) htb
  have hcb'_to_z : Filter.Tendsto
      (fun N : ℕ => algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Spart c' N))
      Filter.atTop (nhds z) := by
    apply h_natTendsto c'
    have h_eventual : ∀ᶠ K : ℤ in Filter.atTop,
        ∑ k ∈ Finset.Icc m K,
          (pInvTQ p T)^k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (TTeichmuller p T (c' (k - m).toNat)) =
        ∑ k ∈ Finset.Icc m₀' K,
          (pInvTQ p T)^k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (TTeichmuller p T (b' k)) := by
      filter_upwards [Filter.eventually_ge_atTop m] with K hKm
      have h_inner : ∑ k ∈ Finset.Icc m K,
            (pInvTQ p T)^k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (TTeichmuller p T (c' (k - m).toNat)) =
          ∑ k ∈ Finset.Icc m K,
            (pInvTQ p T)^k * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (TTeichmuller p T (b' k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Icc] at hk
        have h_c'_eq : c' (k - m).toNat = b' k := by
          change b' (m + ((k - m).toNat : ℤ)) = b' k
          have hkm : (0 : ℤ) ≤ k - m := by linarith
          rw [Int.toNat_of_nonneg hkm]
          ring_nf
        rw [h_c'_eq]
      rw [h_inner, hsum_eq_b' K]
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm h_eventual) htb'
  have hdiff_tendsto : Filter.Tendsto
      (fun N : ℕ => algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Spart c N - Spart c' N))
      Filter.atTop (nhds 0) := by
    have h := hcb_to_z.sub hcb'_to_z
    simp only [sub_self] at h
    apply h.congr
    intro N
    rw [map_sub]
  -- Step 7. Eventually `pInvT^(i+1) ∣ Spart c N - Spart c' N`.
  have h_eventual_div : ∀ i : ℕ, ∃ N : ℕ, N ≥ i ∧
      (pInvT p T)^(i+1) ∣ (Spart c N - Spart c' N) := by
    intro i
    set cval : WithZero (Multiplicative ℤ) :=
      ((Multiplicative.ofAdd (-(i : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      with hcval_def
    have h_nhds :
        {a : ℚᶜᵘⁿ_[p,T] | Valued.v a < cval} ∈ nhds (0 : ℚᶜᵘⁿ_[p,T]) :=
      Tmem_nhds_zero_v_lt p T WithZero.coe_ne_zero
    have h_eventual : ∀ᶠ N : ℕ in Filter.atTop,
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Spart c N - Spart c' N) ∈
          {a : ℚᶜᵘⁿ_[p,T] | Valued.v a < cval} :=
      hdiff_tendsto h_nhds
    rw [Filter.eventually_atTop] at h_eventual
    obtain ⟨N₀, hN₀⟩ := h_eventual
    refine ⟨max N₀ i, le_max_right _ _, ?_⟩
    set N := max N₀ i
    have hN_ge : N₀ ≤ N := le_max_left _ _
    have h_lt : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Spart c N - Spart c' N)) <
        ((Multiplicative.ofAdd (-(i : ℤ)) : Multiplicative ℤ) : WithZero _) := by
      rw [← hcval_def]; exact hN₀ N hN_ge
    have h_le : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Spart c N - Spart c' N)) ≤
        ((Multiplicative.ofAdd (-((i : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) := by
      rcases eq_or_ne
          (Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Spart c N - Spart c' N))) 0
        with h0 | h0
      · rw [h0]; exact bot_le
      · rw [← WithZero.coe_unzero h0 ,WithZero.coe_le_coe]
        rw [← WithZero.coe_unzero h0, WithZero.coe_lt_coe] at h_lt
        rw [show (WithZero.unzero h0) =
            Multiplicative.ofAdd (Multiplicative.toAdd (WithZero.unzero h0)) from rfl]
            at h_lt ⊢
        rw [Multiplicative.ofAdd_lt] at h_lt
        rw [Multiplicative.ofAdd_le]
        omega
    set diff : ℤᶜᵘⁿ_[p,T] := Spart c N - Spart c' N with hdiff_def
    set q : ℚᶜᵘⁿ_[p,T] := algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) diff *
      (pInvTQ p T)^(-((i : ℤ)+1)) with hq_def
    have hq_val_le_one : Valued.v q ≤ 1 := by
      rw [hq_def, Valuation.map_mul, hpn_val (-((i : ℤ)+1))]
      rw [show (-(-((i : ℤ)+1))) = (i : ℤ)+1 from by ring]
      have h_prod : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) diff) *
          ((Multiplicative.ofAdd ((i : ℤ)+1) : Multiplicative ℤ) : WithZero _) ≤
          ((Multiplicative.ofAdd (-((i : ℤ)+1)) : Multiplicative ℤ) : WithZero _) *
          ((Multiplicative.ofAdd ((i : ℤ)+1) : Multiplicative ℤ) : WithZero _) :=
        mul_le_mul_left h_le _
      have h_one : ((Multiplicative.ofAdd (-((i : ℤ)+1)) : Multiplicative ℤ) : WithZero _) *
          ((Multiplicative.ofAdd ((i : ℤ)+1) : Multiplicative ℤ) : WithZero _) =
          (1 : WithZero (Multiplicative ℤ)) := by
        rw [← WithZero.coe_mul]
        rw [show (Multiplicative.ofAdd (-((i : ℤ)+1)) * Multiplicative.ofAdd ((i : ℤ)+1)
              : Multiplicative ℤ) = 1 from by
          rw [← ofAdd_add]; rw [neg_add_cancel]; rfl]
        rfl
      rwa [h_one] at h_prod
    obtain ⟨q', hq'⟩ := Texists_lift_of_valued_le_one p T hq_val_le_one
    have h_eq_QpCUn : algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) diff =
        (pInvTQ p T)^((i : ℤ)+1) * algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) q' := by
      rw [hq']; rw [hq_def]
      rw [show (pInvTQ p T)^((i : ℤ)+1) *
          (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) diff *
            (pInvTQ p T)^(-((i : ℤ)+1))) =
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) diff *
          ((pInvTQ p T)^((i : ℤ)+1) * (pInvTQ p T)^(-((i : ℤ)+1))) from by ring]
      rw [show (pInvTQ p T)^((i : ℤ)+1) * (pInvTQ p T)^(-((i : ℤ)+1)) = 1 from by
        rw [← zpow_add₀ hpInvTQ_ne]; rw [add_neg_cancel]; rw [zpow_zero]]
      rw [mul_one]
    have h_pow_alg : (pInvTQ p T)^((i : ℤ)+1) =
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((pInvT p T)^(i+1)) := by
      have hz : (pInvTQ p T)^((i : ℤ)+1) = (pInvTQ p T)^(i+1) := by
        rw [show ((i : ℤ)+1) = ((i+1 : ℕ) : ℤ) from by push_cast; ring]; exact zpow_natCast _ _
      rw [hz, map_pow]
      rfl
    rw [h_pow_alg, ← map_mul] at h_eq_QpCUn
    exact ⟨q', IsFractionRing.injective (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) h_eq_QpCUn⟩
  -- Step 8. Induction `c i = c' i`.
  have h_induction : ∀ i : ℕ, c i = c' i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      have h_ih : ∀ j < i, c j = c' j := fun j hj => ih j hj
      obtain ⟨N, hNi, hN_dvd⟩ := h_eventual_div i
      have h_diff_expand : Spart c N - Spart c' N =
          ∑ k ∈ Finset.Iic N, (pInvT p T)^k *
            (TTeichmuller p T (c k) - TTeichmuller p T (c' k)) := by
        change (∑ k ∈ Finset.Iic N, (pInvT p T)^k * TTeichmuller p T (c k)) -
              (∑ k ∈ Finset.Iic N, (pInvT p T)^k * TTeichmuller p T (c' k)) = _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      have h_drop : Spart c N - Spart c' N =
          ∑ k ∈ Finset.Iic N \ Finset.range i, (pInvT p T)^k *
            (TTeichmuller p T (c k) - TTeichmuller p T (c' k)) := by
        rw [h_diff_expand]
        rw [show ∑ k ∈ Finset.Iic N, (pInvT p T)^k *
              (TTeichmuller p T (c k) - TTeichmuller p T (c' k)) =
            (∑ k ∈ Finset.Iic N ∩ Finset.range i, (pInvT p T)^k *
              (TTeichmuller p T (c k) - TTeichmuller p T (c' k))) +
            (∑ k ∈ Finset.Iic N \ Finset.range i, (pInvT p T)^k *
              (TTeichmuller p T (c k) - TTeichmuller p T (c' k))) from
            (Finset.sum_inter_add_sum_sdiff (Finset.Iic N) (Finset.range i) _).symm]
        have h_zero : ∑ k ∈ Finset.Iic N ∩ Finset.range i,
            (pInvT p T)^k *
              (TTeichmuller p T (c k) - TTeichmuller p T (c' k)) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          rw [Finset.mem_inter, Finset.mem_range] at hk
          rw [h_ih k hk.2]
          ring
        rw [h_zero, zero_add]
      have h_reindex_set : Finset.Iic N \ Finset.range i = Finset.Icc i N := by
        ext k
        simp only [Finset.mem_sdiff, Finset.mem_Iic, Finset.mem_range,
          Finset.mem_Icc, not_lt]
        tauto
      rw [h_reindex_set] at h_drop
      have h_reindex_full : ∑ k ∈ Finset.Icc i N, (pInvT p T)^k *
            (TTeichmuller p T (c k) - TTeichmuller p T (c' k)) =
          (pInvT p T)^i * ∑ j ∈ Finset.range (N - i + 1), (pInvT p T)^j *
            (TTeichmuller p T (c (i + j)) - TTeichmuller p T (c' (i + j))) := by
        rw [show Finset.Icc i N =
            (Finset.range (N - i + 1)).map ⟨fun j => i + j, by
              intros a b h; simp only at h; omega⟩ from ?_]
        · rw [Finset.sum_map, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          change (pInvT p T)^(i + j) *
            (TTeichmuller p T (c (i + j)) - TTeichmuller p T (c' (i + j))) = _
          rw [show (pInvT p T)^(i + j) = (pInvT p T)^i * (pInvT p T)^j from
            pow_add _ _ _]
          ring
        · ext k
          simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range]
          constructor
          · intro ⟨hk1, hk2⟩
            refine ⟨k - i, by omega, ?_⟩
            change i + (k - i) = k
            omega
          · rintro ⟨j, hj, hjk⟩
            have hk : i + j = k := hjk
            omega
      have h_factored : Spart c N - Spart c' N = (pInvT p T)^i *
          ∑ j ∈ Finset.range (N - i + 1), (pInvT p T)^j *
            (TTeichmuller p T (c (i + j)) - TTeichmuller p T (c' (i + j))) := by
        rw [h_drop, h_reindex_full]
      obtain ⟨q', hq'⟩ := hN_dvd
      have h_eq : (pInvT p T)^i *
          ∑ j ∈ Finset.range (N - i + 1), (pInvT p T)^j *
            (TTeichmuller p T (c (i + j)) - TTeichmuller p T (c' (i + j))) =
          (pInvT p T)^(i+1) * q' := by
        rw [← h_factored]; exact hq'
      have h_p_pow_succ : (pInvT p T)^(i+1) = (pInvT p T)^i * (pInvT p T) := by
        rw [pow_succ]
      rw [h_p_pow_succ, mul_assoc] at h_eq
      have hpi_ne : (pInvT p T)^i ≠ 0 := pow_ne_zero _ (pInvT_ne_zero p T)
      have h_X_eq : ∑ j ∈ Finset.range (N - i + 1), (pInvT p T)^j *
            (TTeichmuller p T (c (i + j)) - TTeichmuller p T (c' (i + j))) =
          pInvT p T * q' :=
        mul_left_cancel₀ hpi_ne h_eq
      have h_split : ∑ j ∈ Finset.range (N - i + 1), (pInvT p T)^j *
            (TTeichmuller p T (c (i + j)) - TTeichmuller p T (c' (i + j))) =
          (TTeichmuller p T (c i) - TTeichmuller p T (c' i)) +
          pInvT p T * ∑ j ∈ Finset.range (N - i), (pInvT p T)^j *
            (TTeichmuller p T (c (i + 1 + j)) - TTeichmuller p T (c' (i + 1 + j))) := by
        rw [Finset.sum_range_succ', add_comm]
        simp only [pow_zero, one_mul, Nat.add_zero]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [show i + (j + 1) = i + 1 + j from by ring]
        rw [show (pInvT p T)^(j + 1) = pInvT p T * (pInvT p T)^j from by
          rw [pow_succ]; ring]
        ring
      rw [h_split] at h_X_eq
      have h_p_div : pInvT p T ∣ TTeichmuller p T (c i) - TTeichmuller p T (c' i) := by
        refine ⟨q' -
            ∑ j ∈ Finset.range (N - i), (pInvT p T)^j *
              (TTeichmuller p T (c (i + 1 + j)) - TTeichmuller p T (c' (i + 1 + j))),
          ?_⟩
        linear_combination h_X_eq
      -- Step 9 (T-DVR specific). Apply TRes to extract leading digit.
      -- Replaces Poonen 1782–1802 (Witt-coefficient extraction) with a
      -- 4-line residue-map argument.
      have hres_zero :
          TRes p T (TTeichmuller p T (c i) - TTeichmuller p T (c' i)) = 0 := by
        change (TResidueIsoFpbar p) (TResidue p T
            (TTeichmuller p T (c i) - TTeichmuller p T (c' i))) = 0
        rw [(TResidue_eq_zero_iff p T _).mpr h_p_div, map_zero]
      rw [map_sub, TRes_TTeichmuller, TRes_TTeichmuller] at hres_zero
      exact sub_eq_zero.mp hres_zero
  -- Step 10. Lift back from ℕ to ℤ.
  intro k
  by_cases hk : k < m
  · rw [hb_below k hk, hb'_below k hk]
  · push Not at hk
    have hk_eq : k = m + ((k - m).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (by linarith)]
      ring
    have h_c_eq : c (k - m).toNat = b k := by
      change b (m + ((k - m).toNat : ℤ)) = b k
      rw [← hk_eq]
    have h_c'_eq : c' (k - m).toNat = b' k := by
      change b' (m + ((k - m).toNat : ℤ)) = b' k
      rw [← hk_eq]
    rw [← h_c_eq, ← h_c'_eq]
    exact h_induction (k - m).toNat

/-! ### Lemma 4.2 proper — Teichmüller series for `ℤᶜᵘⁿ_[p,T]` -/

open Topology Filter in
/-- **Lemma 4.2.**  Every element of `ℤᶜᵘⁿ_[p,T]` can be uniquely written as
`∑_{k≥0} [c_k] · (pInvT)^k` with `c_k ∈ 𝔽ᵃ_[p]`, where the sum converges in the
`(pInvT)`-adic topology on `ℤᶜᵘⁿ_[p,T]` (formalised here as the `Valued`-induced topology
on `ℚᶜᵘⁿ_[p,T]` after taking `algebraMap`).

This is a consequence of the Teichmüller-series representation of `ℤᶜᵘⁿ_[p]` (Mathlib
`WittVector.TeichmullerSeries`) combined with Lemma 4.1.

Existence comes from `Texists_T_pInvT_digits` (the divisibility step) plus a standard
valuation/Tendsto argument; uniqueness is obtained by extending `c : ℕ → 𝔽ᵃ_[p]` to
`b : ℤ → 𝔽ᵃ_[p]` with cutoff `m₀ = 0` and applying `Tteichmuller_digits_unique`. -/
theorem exists_teichmuller_series_OQpCUnT :
    ∀ a : ℤᶜᵘⁿ_[p,T], ∃! c : ℕ → 𝔽ᵃ_[p],
      Filter.Tendsto
        (fun N : ℕ => ∑ k ∈ Finset.range N,
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (OQpCUn_embd p T (teichmuller p (c k)) * (pInvT p T) ^ k))
        Filter.atTop
        (𝓝 (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) a)) := by
  intro a
  obtain ⟨digits, hdigits⟩ := Texists_T_pInvT_digits p T a
  -- Common ingredients used in both existence and uniqueness branches.
  have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
  have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
    WithZeroMulInt.toNNReal_strictMono hp1
  have hpinv_lt : (p : NNReal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hpinv_nn : 0 ≤ ((p : NNReal)⁻¹ : NNReal) := zero_le
  -- Abbreviation: `algMapₐ` is the algebra map `ℤᶜᵘⁿ_[p,T] → ℚᶜᵘⁿ_[p,T]`.
  set algMapₐ : ℤᶜᵘⁿ_[p,T] →+* ℚᶜᵘⁿ_[p,T] := algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) with halgMapₐ
  -- Convenience: rewrite the partial-sum form in two equivalent ways.
  -- Form A (the goal's form): algMapₐ (OQpCUn_embd p T teich(c k) * (pInvT)^k)
  -- Form B (TTeichmuller form, used in Tteichmuller_digits_unique):
  --   (pInvTQ)^k * algMapₐ (TTeichmuller (c k))   -- using TTeichmuller := algMap ∘ teich
  -- Equality of forms: form A = (pInvTQ)^k * algMapₐ (algMapₐ_inner (teich (c k)))
  -- where algMapₐ_inner = algebraMap ℤᶜᵘⁿ_[p] → ℤᶜᵘⁿ_[p,T].
  -- Build the existence-side bound first.
  have hbound : ∀ (digits' : ℕ → Fpbar p),
      (∀ n : ℕ,
        (pInvT p T)^(n+1) ∣ a - ∑ i ∈ Finset.Iic n,
          (pInvT p T)^i * algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (digits' i))) →
      ∀ N : ℕ, 1 ≤ N → Valued.v (algMapₐ a -
        ∑ k ∈ Finset.range N,
          algMapₐ (OQpCUn_embd p T (teichmuller p (digits' k)) * (pInvT p T) ^ k)) ≤
      ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _) := by
    intro digits' hdigits' N hN
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 1 := ⟨N - 1, by omega⟩
    have hdiv := hdigits' n
    obtain ⟨c, hc⟩ := hdiv
    have halg := congrArg algMapₐ hc
    simp only [map_sub, map_sum, map_mul, map_pow] at halg
    have hreindex :
        (∑ k ∈ Finset.range (n + 1),
          algMapₐ (OQpCUn_embd p T (teichmuller p (digits' k)) * (pInvT p T) ^ k)) =
        ∑ i ∈ Finset.Iic n,
          algMapₐ ((pInvT p T)^i *
            algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (digits' i))) := by
      rw [← Nat.range_succ_eq_Iic]
      apply Finset.sum_congr rfl
      intro i _
      unfold OQpCUn_embd
      rw [mul_comm]
    rw [hreindex]
    have hkey : algMapₐ a -
        ∑ i ∈ Finset.Iic n,
          algMapₐ ((pInvT p T)^i *
            algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (digits' i))) =
        algMapₐ ((pInvT p T)^(n+1) * c) := by
      rw [← map_sum, ← map_sub, hc]
    rw [hkey]
    rw [show algMapₐ ((pInvT p T)^(n+1) * c) =
        algMapₐ ((pInvT p T)^(n+1)) * algMapₐ c from map_mul _ _ _]
    rw [Valuation.map_mul, map_pow]
    have hpInvT_cast : algMapₐ (pInvT p T) = pInvTQ p T := rfl
    rw [hpInvT_cast]
    have hpn_val := valued_v_pInvT_zpow (p := p) (T := T)
    rw [show ((pInvTQ p T) ^ (n + 1) : ℚᶜᵘⁿ_[p,T]) =
          (pInvTQ p T) ^ ((n : ℤ) + 1) from by
      rw [← zpow_natCast (pInvTQ p T) (n+1)]; push_cast; rfl]
    rw [hpn_val ((n : ℤ) + 1)]
    have h_alg_le : Valued.v (algMapₐ c) ≤ 1 :=
      (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_le_one c
    calc ((Multiplicative.ofAdd (-((n : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) *
        Valued.v (algMapₐ c)
        ≤ ((Multiplicative.ofAdd (-((n : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) * 1 :=
          mul_le_mul' (le_refl _) h_alg_le
      _ = ((Multiplicative.ofAdd (-((n : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) :=
          mul_one _
      _ = ((Multiplicative.ofAdd (-((n + 1 : ℕ) : ℤ)) : Multiplicative ℤ) : WithZero _) := by
          push_cast; rfl
  -- Convert valuation bound to Tendsto for any digits satisfying the divisibility.
  have htendsto_of_bound : ∀ (digits' : ℕ → Fpbar p),
      (∀ n : ℕ,
        (pInvT p T)^(n+1) ∣ a - ∑ i ∈ Finset.Iic n,
          (pInvT p T)^i * algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (digits' i))) →
      Filter.Tendsto
        (fun N : ℕ => ∑ k ∈ Finset.range N,
          algMapₐ (OQpCUn_embd p T (teichmuller p (digits' k)) * (pInvT p T) ^ k))
        Filter.atTop
        (𝓝 (algMapₐ a)) := by
    intro digits' hdigits'
    rw [Filter.tendsto_iff_forall_eventually_mem]
    intro U hU
    obtain ⟨γ, hγ_ne, hγ⟩ := Texists_v_sub_lt_subset p T hU
    set ε : NNReal :=
      WithZeroMulInt.toNNReal (p_ne_zero p) (γ : WithZero (Multiplicative ℤ)) with hε_def
    have hε_pos : (0 : NNReal) < ε := by
      rw [hε_def]
      exact WithZeroMulInt.toNNReal_pos (p_ne_zero p) hγ_ne
    have htendsto_pow : Filter.Tendsto (fun n : ℕ => ((p : NNReal)⁻¹)^n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hpinv_nn hpinv_lt
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ((p : NNReal)⁻¹)^N₀ < ε := by
      have h_eventually : ∀ᶠ n : ℕ in Filter.atTop, ((p : NNReal)⁻¹)^n < ε :=
        htendsto_pow.eventually (eventually_lt_nhds hε_pos)
      exact h_eventually.exists
    rw [Filter.eventually_atTop]
    refine ⟨max 1 N₀, ?_⟩
    intro N hN
    have hN_ge_1 : 1 ≤ N := le_of_max_le_left hN
    have hN_ge_N₀ : N₀ ≤ N := le_of_max_le_right hN
    apply hγ
    change Valued.v ((∑ k ∈ Finset.range N,
        algMapₐ (OQpCUn_embd p T (teichmuller p (digits' k)) * (pInvT p T) ^ k)) -
          algMapₐ a) < γ
    rw [Valuation.map_sub_swap]
    have h1 := hbound digits' hdigits' N hN_ge_1
    have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (algMapₐ a - ∑ k ∈ Finset.range N,
          algMapₐ (OQpCUn_embd p T (teichmuller p (digits' k)) * (pInvT p T) ^ k))) ≤
        WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _)) :=
      hsm.monotone h1
    have htoNN : WithZeroMulInt.toNNReal (p_ne_zero p)
        (((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _)) =
        (p : NNReal)^(-(N : ℤ)) := by
      rw [WithZeroMulInt.toNNReal_neg_apply (p_ne_zero p) WithZero.coe_ne_zero, WithZero.unzero_coe]
      congr 1
    rw [htoNN] at h_nnreal_le
    have h_pow_le : (p : NNReal)^(-(N : ℤ)) ≤ ((p : NNReal)⁻¹)^N₀ := by
      rw [show (p : NNReal)^(-(N : ℤ)) = ((p : NNReal)⁻¹)^(N : ℤ) from by
        rw [zpow_neg, ← inv_zpow]]
      rw [show ((p : NNReal)⁻¹)^(N : ℤ) = ((p : NNReal)⁻¹)^N from by
        rw [zpow_natCast]]
      apply pow_le_pow_of_le_one hpinv_nn (le_of_lt hpinv_lt)
      exact hN_ge_N₀
    have h_chain : WithZeroMulInt.toNNReal (p_ne_zero p)
        (Valued.v (algMapₐ a - ∑ k ∈ Finset.range N,
          algMapₐ (OQpCUn_embd p T (teichmuller p (digits' k)) * (pInvT p T) ^ k))) < ε :=
      (h_nnreal_le.trans h_pow_le).trans_lt hN₀
    rw [hε_def] at h_chain
    exact hsm.lt_iff_lt.mp h_chain
  refine ⟨digits, htendsto_of_bound digits hdigits, ?_⟩
  -- Uniqueness.
  intro c' hc'
  -- We show that any `c'` satisfying the convergence statement must coincide with `digits`.
  -- The strategy: extend each function `f : ℕ → Fpbar p` to `b : ℤ → Fpbar p` by 0 on
  -- negatives, and verify the convergence in the form expected by `Tteichmuller_digits_unique`.
  -- Then `Tteichmuller_digits_unique` forces the two extensions to agree.
  -- We then transport equality back to `ℕ`.
  set b  : ℤ → Fpbar p := fun k => if h : 0 ≤ k then digits k.toNat else 0 with hb_def
  set b' : ℤ → Fpbar p := fun k => if h : 0 ≤ k then c' k.toNat else 0 with hb'_def
  have hb_below : ∀ k : ℤ, k < 0 → b k = 0 := by
    intro k hk
    change (if h : 0 ≤ k then digits k.toNat else 0) = 0
    rw [dif_neg (by linarith)]
  have hb'_below : ∀ k : ℤ, k < 0 → b' k = 0 := by
    intro k hk
    change (if h : 0 ≤ k then c' k.toNat else 0) = 0
    rw [dif_neg (by linarith)]
  -- Connection: for `f : ℕ → Fpbar p`, the partial sums in the goal's `Finset.range N` form
  -- equal the partial sums in `Tteichmuller_digits_unique`'s `Finset.Icc 0 K` form when
  -- `K = N - 1` (and `0 ≤ K`).
  have hsum_eq : ∀ (f : ℕ → Fpbar p) (b'' : ℤ → Fpbar p)
      (hb'' : ∀ k : ℕ, b'' (k : ℤ) = f k) (N : ℕ),
      (∑ k ∈ Finset.range N,
        algMapₐ (OQpCUn_embd p T (teichmuller p (f k)) * (pInvT p T) ^ k)) =
      (∑ k ∈ Finset.Icc (0 : ℤ) (N - 1 : ℤ),
        (pInvTQ p T) ^ k *
        algMapₐ (TTeichmuller p T (b'' k))) := by
    intro f b'' hb'' N
    induction N with
    | zero => simp
    | succ N ih =>
      have hcast : ((N + 1 : ℕ) : ℤ) - 1 = (N : ℤ) := by push_cast; ring
      rw [Finset.sum_range_succ, ih]
      rw [hcast]
      have hIcc_split : Finset.Icc (0 : ℤ) (N : ℤ) =
          insert (N : ℤ) (Finset.Icc (0 : ℤ) (N - 1 : ℤ)) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        constructor
        · rintro ⟨h1, h2⟩
          rcases eq_or_lt_of_le h2 with rfl | hlt
          · exact Or.inl rfl
          · exact Or.inr ⟨h1, by omega⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨by exact_mod_cast Nat.zero_le N, le_refl _⟩
          · exact ⟨h1, by omega⟩
      have hN_not_mem : (N : ℤ) ∉ Finset.Icc (0 : ℤ) (N - 1 : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      rw [hIcc_split, Finset.sum_insert hN_not_mem]
      -- Identify the new term and reorder.
      have hbN : b'' (N : ℤ) = f N := hb'' N
      have hTT_eq :
          algMapₐ (OQpCUn_embd p T (teichmuller p (f N)) * (pInvT p T) ^ N) =
          (pInvTQ p T) ^ ((N : ℤ)) * algMapₐ (TTeichmuller p T (b'' (N : ℤ))) := by
        rw [hbN, map_mul, map_pow]
        have hpInvT_cast : algMapₐ (pInvT p T) = pInvTQ p T := rfl
        rw [hpInvT_cast]
        unfold OQpCUn_embd TTeichmuller
        rw [show (pInvTQ p T) ^ ((N : ℤ)) = (pInvTQ p T) ^ N from zpow_natCast _ _, mul_comm]
        rfl
      rw [hTT_eq]
      ring
  -- For `digits` and `c'`, the extensions `b`, `b'` satisfy `b k = digits k` and
  -- `b' k = c' k` on naturals.
  have hb_nat : ∀ k : ℕ, b (k : ℤ) = digits k := by
    intro k
    change (if h : 0 ≤ (k : ℤ) then digits ((k : ℤ).toNat) else 0) = digits k
    rw [dif_pos (by exact_mod_cast Nat.zero_le k)]
    simp
  have hb'_nat : ∀ k : ℕ, b' (k : ℤ) = c' k := by
    intro k
    change (if h : 0 ≤ (k : ℤ) then c' ((k : ℤ).toNat) else 0) = c' k
    rw [dif_pos (by exact_mod_cast Nat.zero_le k)]
    simp
  -- Get the Tendsto in the Tteichmuller_digits_unique form for both `b` and `b'`.
  -- Strategy: compose Tendsto over ℕ with the cofinal map `K : ℤ ↦ (K + 1).toNat` (atTop → atTop).
  -- Set `g(K) := (K+1).toNat` so that `Finset.Icc 0 K = Finset.range (g K)` (when `0 ≤ K`).
  have h_tendsto_Z_form : ∀ (digits' : ℕ → Fpbar p) (b'' : ℤ → Fpbar p)
      (hb_eq : ∀ k : ℕ, b'' (k : ℤ) = digits' k)
      (hb_below'' : ∀ k : ℤ, k < 0 → b'' k = 0)
      (h_orig_tendsto : Filter.Tendsto
        (fun N : ℕ => ∑ k ∈ Finset.range N,
          algMapₐ (OQpCUn_embd p T (teichmuller p (digits' k)) * (pInvT p T) ^ k))
        Filter.atTop (𝓝 (algMapₐ a))),
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc (0 : ℤ) K,
          (pInvTQ p T) ^ k * algMapₐ (TTeichmuller p T (b'' k)))
        Filter.atTop (𝓝 (algMapₐ a)) := by
    intro digits' b'' hb_eq hb_below'' h_orig_tendsto
    -- The map K : ℤ ↦ (K + 1).toNat sends atTop to atTop.
    have hcofinal : Filter.Tendsto (fun K : ℤ => (K + 1).toNat) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro M
      refine ⟨(M : ℤ) - 1, ?_⟩
      intro K hK
      have hM_le : (M : ℤ) ≤ K + 1 := by linarith
      have hM_nn : (0 : ℤ) ≤ (M : ℤ) := Int.natCast_nonneg M
      have h_pos : 0 ≤ K + 1 := le_trans hM_nn hM_le
      have h_toN : ((K + 1).toNat : ℤ) = K + 1 := Int.toNat_of_nonneg h_pos
      have hM_le_toN : (M : ℤ) ≤ ((K + 1).toNat : ℤ) := by rw [h_toN]; exact hM_le
      exact_mod_cast hM_le_toN
    have h_comp := h_orig_tendsto.comp hcofinal
    -- Now show `comp ≡ Z-form` eventually for K ≥ 0.
    apply h_comp.congr'
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨0, ?_⟩
    intro K hK
    -- For K ≥ 0, `(K + 1).toNat - 1 = K` so `Finset.Icc 0 K = Finset.Icc 0 ((K+1).toNat - 1)`.
    have h_toNat : ((K + 1).toNat : ℤ) = K + 1 := Int.toNat_of_nonneg (by linarith)
    have hK_eq : (((K + 1).toNat : ℕ) : ℤ) - 1 = K := by
      omega
    change (∑ k ∈ Finset.range (K + 1).toNat,
          algMapₐ (OQpCUn_embd p T (teichmuller p (digits' k)) * (pInvT p T) ^ k)) =
        ∑ k ∈ Finset.Icc (0 : ℤ) K, (pInvTQ p T) ^ k * algMapₐ (TTeichmuller p T (b'' k))
    rw [hsum_eq digits' b'' hb_eq (K + 1).toNat]
    rw [hK_eq]
  have ht_digits := h_tendsto_Z_form digits b hb_nat hb_below
    (htendsto_of_bound digits hdigits)
  have ht_c' := h_tendsto_Z_form c' b' hb'_nat hb'_below hc'
  -- Apply Tteichmuller_digits_unique with m₀ = m₀' = 0.
  have h_b_eq_b' : ∀ k : ℤ, b k = b' k :=
    Tteichmuller_digits_unique (p := p) (T := T) b b' 0 0
      (fun k hk => hb_below k hk)
      (fun k hk => hb'_below k hk) ht_digits ht_c'
  -- Transport equality back to ℕ.
  funext k
  have h_eq_at_k : b (k : ℤ) = b' (k : ℤ) := h_b_eq_b' (k : ℤ)
  rw [hb_nat, hb'_nat] at h_eq_at_k
  exact h_eq_at_k.symm

/-! ### Phase 3A: existence of canonical T-representative -/

/-- T-analogue of `exists_canonical_representative`'s `hp_term_val` (lines
1856–1868).  Equality version of `Tvalued_v_term_le` (line 702), valid when the
Teichmüller argument is nonzero. -/
private lemma Tvalued_v_pInvTQ_term_val
    (a : Fpbar p) (n : ℤ) (ha : a ≠ 0) :
    Valued.v ((pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p a))) =
      ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
  rw [Valuation.map_mul, valued_v_pInvT_zpow]
  have h_a_unit : IsUnit a := isUnit_iff_ne_zero.mpr ha
  have h_teich_unit : IsUnit (teichmuller p a) := h_a_unit.map (teichmuller p)
  have h_inner_unit : IsUnit (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p a)) :=
    h_teich_unit.map (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]))
  have h_val_one : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
      (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p a))) = 1 := by
    rcases h_inner_unit with ⟨u, hu⟩
    rw [← hu, Tvalued_v_algebraMap_unit_one p T u]
  rw [h_val_one, mul_one]

/-- T-analogue of `exists_canonical_representative`'s `h_intPartial_eq_Icc` (lines
2173–2219).  Bridges `TintPartial` to a `Finset.Icc` sum when the coefficient function is
Teichmüller-valued and vanishes below `m`. -/
private lemma Th_intPartial_eq_Icc
    (γ' : ℚ) (β' : TLiftedPAdicHahnSeries p T) (t : ℚ → Fpbar p) (m : ℤ)
    (hβ' : ∀ q : ℚ, β'.coeff q =
      algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (t q)))
    (hm  : ∀ k : ℤ, k < m → t (γ' + (k : ℚ) / T) = 0) :
    ∀ K : ℤ, m ≤ K →
      TintPartial p T β' γ' K =
        ∑ k ∈ Finset.Icc m K,
          (pInvTQ p T) ^ k *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (t (γ' + (k : ℚ) / T)))) := by
  intro K hK
  have h_step1 : TintPartial p T β' γ' K =
      ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T β' γ' K),
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (β'.coeff (γ' + (n : ℚ) / T)) := by
    simp only [TintPartial]
    exact Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T β' γ' K))
      (f := fun n : ℤ => (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (β'.coeff (γ' + (n : ℚ) / T)))
  rw [h_step1]
  have h_subset : Set.Finite.toFinset (TfiniteBelowInt p T β' γ' K) ⊆ Finset.Icc m K := by
    intro n hn
    have hn_mem : n ≤ K ∧ β'.coeff (γ' + (n : ℚ) / T) ≠ 0 :=
      (Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T β' γ' K)).mp hn
    have h_t_ne : t (γ' + (n : ℚ) / T) ≠ 0 := by
      intro h_zero
      apply hn_mem.2
      rw [hβ' (γ' + (n : ℚ) / T), h_zero, WittVector.teichmuller_zero, map_zero]
    have h_n_ge : m ≤ n := by
      by_contra h_lt
      push Not at h_lt
      exact h_t_ne (hm n h_lt)
    exact Finset.mem_Icc.mpr ⟨h_n_ge, hn_mem.1⟩
  have h_extend : ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T β' γ' K),
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (β'.coeff (γ' + (n : ℚ) / T)) =
      ∑ n ∈ Finset.Icc m K,
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (β'.coeff (γ' + (n : ℚ) / T)) := by
    apply Finset.sum_subset h_subset
    intro n hn_Icc hn_not
    rw [Finset.mem_Icc] at hn_Icc
    have h_β_zero : β'.coeff (γ' + (n : ℚ) / T) = 0 := by
      by_contra hne
      apply hn_not
      exact (Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T β' γ' K)).mpr ⟨hn_Icc.2, hne⟩
    rw [h_β_zero]
    simp
  rw [h_extend]
  apply Finset.sum_congr rfl
  intro n _
  rw [hβ' (γ' + (n : ℚ) / T)]

/-- T-analogue of `exists_canonical_representative`'s `h_intPartial_sub` (lines
2344–2440).  Subdistributivity of `TintPartial` over subtraction. -/
private lemma Th_intPartial_sub
    (α β : TLiftedPAdicHahnSeries p T) (g : ℚ) (K : ℤ) :
    TintPartial p T (α - β) g K = TintPartial p T α g K - TintPartial p T β g K := by
  set T_α : Finset ℤ := Set.Finite.toFinset (TfiniteBelowInt p T α g K) with hT_α_def
  set T_β : Finset ℤ := Set.Finite.toFinset (TfiniteBelowInt p T β g K) with hT_β_def
  set T_d : Finset ℤ := Set.Finite.toFinset (TfiniteBelowInt p T (α - β) g K) with hT_d_def
  set T_U : Finset ℤ := T_α ∪ T_β with hT_U_def
  have e_α : TintPartial p T α g K =
      ∑ n ∈ T_α, (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (α.coeff (g + (n : ℚ) / T)) := by
    simp only [TintPartial, hT_α_def]
    exact Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T α g K))
      (f := fun n : ℤ => (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (α.coeff (g + (n : ℚ) / T)))
  have e_β : TintPartial p T β g K =
      ∑ n ∈ T_β, (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (β.coeff (g + (n : ℚ) / T)) := by
    simp only [TintPartial, hT_β_def]
    exact Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T β g K))
      (f := fun n : ℤ => (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (β.coeff (g + (n : ℚ) / T)))
  have e_d : TintPartial p T (α - β) g K =
      ∑ n ∈ T_d, (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - β).coeff (g + (n : ℚ) / T)) := by
    simp only [TintPartial, hT_d_def]
    exact Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T (α - β) g K))
      (f := fun n : ℤ => (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - β).coeff (g + (n : ℚ) / T)))
  have h_α_sub_U : T_α ⊆ T_U := Finset.subset_union_left
  have h_β_sub_U : T_β ⊆ T_U := Finset.subset_union_right
  have h_d_sub_U : T_d ⊆ T_U := by
    intro n hn
    have hn_mem : n ≤ K ∧ (α - β).coeff (g + (n : ℚ) / T) ≠ 0 :=
      (Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T (α - β) g K)).mp hn
    have h_sub_eq : (α - β).coeff (g + (n : ℚ) / T) =
        α.coeff (g + (n : ℚ) / T) - β.coeff (g + (n : ℚ) / T) := rfl
    rw [h_sub_eq] at hn_mem
    by_cases h_α_z : α.coeff (g + (n : ℚ) / T) = 0
    · have h_β_ne : β.coeff (g + (n : ℚ) / T) ≠ 0 := by
        intro h_β_z
        apply hn_mem.2
        rw [h_α_z, h_β_z, sub_self]
      exact Finset.mem_union_right T_α
        ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T β g K)).mpr ⟨hn_mem.1, h_β_ne⟩)
    · exact Finset.mem_union_left T_β
        ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T α g K)).mpr ⟨hn_mem.1, h_α_z⟩)
  have he_α_U : ∑ n ∈ T_α,
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (α.coeff (g + (n : ℚ) / T)) =
      ∑ n ∈ T_U,
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (α.coeff (g + (n : ℚ) / T)) := by
    apply Finset.sum_subset h_α_sub_U
    intro n hn_U hn_not_α
    have hn_le_K : n ≤ K := by
      rcases Finset.mem_union.mp hn_U with h_α_mem | h_β_mem
      · exact ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T α g K)).mp h_α_mem).1
      · exact ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T β g K)).mp h_β_mem).1
    have h_α_z : α.coeff (g + (n : ℚ) / T) = 0 := by
      by_contra hne
      exact hn_not_α
        ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T α g K)).mpr ⟨hn_le_K, hne⟩)
    rw [h_α_z]
    simp
  have he_β_U : ∑ n ∈ T_β,
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (β.coeff (g + (n : ℚ) / T)) =
      ∑ n ∈ T_U,
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (β.coeff (g + (n : ℚ) / T)) := by
    apply Finset.sum_subset h_β_sub_U
    intro n hn_U hn_not_β
    have hn_le_K : n ≤ K := by
      rcases Finset.mem_union.mp hn_U with h_α_mem | h_β_mem
      · exact ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T α g K)).mp h_α_mem).1
      · exact ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T β g K)).mp h_β_mem).1
    have h_β_z : β.coeff (g + (n : ℚ) / T) = 0 := by
      by_contra hne
      exact hn_not_β
        ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T β g K)).mpr ⟨hn_le_K, hne⟩)
    rw [h_β_z]
    simp
  have he_d_U : ∑ n ∈ T_d,
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - β).coeff (g + (n : ℚ) / T)) =
      ∑ n ∈ T_U,
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - β).coeff (g + (n : ℚ) / T)) := by
    apply Finset.sum_subset h_d_sub_U
    intro n hn_U hn_not_d
    have hn_le_K : n ≤ K := by
      rcases Finset.mem_union.mp hn_U with h_α_mem | h_β_mem
      · exact ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T α g K)).mp h_α_mem).1
      · exact ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T β g K)).mp h_β_mem).1
    have h_d_z : (α - β).coeff (g + (n : ℚ) / T) = 0 := by
      by_contra hne
      exact hn_not_d
        ((Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T (α - β) g K)).mpr ⟨hn_le_K, hne⟩)
    rw [h_d_z]
    simp
  rw [e_d, he_d_U, e_α, he_α_U, e_β, he_β_U]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have h_sub_coeff : (α - β).coeff (g + (n : ℚ) / T) =
      α.coeff (g + (n : ℚ) / T) - β.coeff (g + (n : ℚ) / T) := rfl
  rw [h_sub_coeff, map_sub, mul_sub]

/-- T-analogue of `exists_canonical_representative`'s `h_key` (lines
1893–2121).  Given a sequence `b : ℤ → Fpbar p` whose Teichmüller-power sums converge to
`(Texists_lim_intPartial p T α γ).choose`, if `b k ≠ 0` then there is some `n_α ≤ k` with
`α.coeff (γ + n_α / T) ≠ 0`. -/
private lemma Th_key
    (α : TLiftedPAdicHahnSeries p T) (γ : ℚ) (k : ℤ)
    (b : ℤ → Fpbar p) (m_b : ℤ)
    (hb_vanish : ∀ k' : ℤ, k' < m_b → b k' = 0)
    (hb_tendsto : Filter.Tendsto
      (fun K : ℤ => ∑ j ∈ Finset.Icc m_b K,
        (pInvTQ p T) ^ j *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b j))))
      Filter.atTop (nhds (Texists_lim_intPartial p T α γ).choose))
    (hbk : b k ≠ 0) :
    ∃ n_α : ℤ, n_α ≤ k ∧ α.coeff (γ + (n_α : ℚ) / T) ≠ 0 := by
  classical
  set y : ℚᶜᵘⁿ_[p,T] := (Texists_lim_intPartial p T α γ).choose with hy_def
  have hy_spec : Filter.Tendsto (TintPartial p T α γ) Filter.atTop (nhds y) :=
    (Texists_lim_intPartial p T α γ).choose_spec
  -- Step 0: define `k_min`.
  have h_k_in : k ∈ {j : ℤ | m_b ≤ j ∧ b j ≠ 0} := by
    refine ⟨?_, hbk⟩
    by_contra h_nge
    push Not at h_nge
    exact hbk (hb_vanish k h_nge)
  have hbset_ne : ({j : ℤ | m_b ≤ j ∧ b j ≠ 0}).Nonempty := ⟨k, h_k_in⟩
  have hbset_bdd : BddBelow {j : ℤ | m_b ≤ j ∧ b j ≠ 0} :=
    ⟨m_b, fun j hj => hj.1⟩
  obtain ⟨k_min, hk_min_mem, hk_min_le⟩ :=
    Int.exists_least_of_bdd hbset_bdd hbset_ne
  -- Step 1: strict-ultrametric valuation of the truncated sum.
  have h_sum_eq : ∀ K : ℤ, k_min ≤ K → Valued.v (∑ j ∈ Finset.Icc m_b K,
        (pInvTQ p T) ^ j *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b j)))) =
      ((Multiplicative.ofAdd (-k_min : ℤ) : Multiplicative ℤ) : WithZero _) := by
    intro K hK
    have h_in : k_min ∈ Finset.Icc m_b K := Finset.mem_Icc.mpr ⟨hk_min_mem.1, hK⟩
    rw [show Finset.Icc m_b K = insert k_min ((Finset.Icc m_b K).erase k_min) from
      (Finset.insert_erase h_in).symm]
    rw [Finset.sum_insert (Finset.notMem_erase _ _)]
    rw [Valuation.map_add_eq_of_lt_left]
    · exact Tvalued_v_pInvTQ_term_val p T (b k_min) k_min hk_min_mem.2
    · have h_bound : Valued.v (∑ j ∈ (Finset.Icc m_b K).erase k_min,
            (pInvTQ p T) ^ j *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
                (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b j)))) ≤
          ((Multiplicative.ofAdd (-(k_min + 1) : ℤ) : Multiplicative ℤ) : WithZero _) := by
        apply Valuation.map_sum_le
        intro j hj_mem
        rw [Finset.mem_erase, Finset.mem_Icc] at hj_mem
        by_cases h_zero : b j = 0
        · rw [h_zero, WittVector.teichmuller_zero, map_zero, map_zero, mul_zero]
          rw [Valuation.map_zero]
          exact bot_le
        · have hj_in : j ∈ {i : ℤ | m_b ≤ i ∧ b i ≠ 0} := ⟨hj_mem.2.1, h_zero⟩
          have hj_ge : k_min ≤ j := hk_min_le j hj_in
          have hj_gt : k_min < j := lt_of_le_of_ne hj_ge (Ne.symm hj_mem.1)
          rw [Tvalued_v_pInvTQ_term_val p T (b j) j h_zero]
          rw [WithZero.coe_le_coe]
          exact Multiplicative.ofAdd_le.mpr (by omega)
      apply lt_of_le_of_lt h_bound
      rw [Tvalued_v_pInvTQ_term_val p T (b k_min) k_min hk_min_mem.2]
      rw [WithZero.coe_lt_coe]
      exact Multiplicative.ofAdd_lt.mpr (by omega)
  -- Step 2: case-split on `y = 0`.
  by_cases h_y : y = 0
  · -- Step 2A: `y = 0` ⇒ contradiction.
    exfalso
    have h_nhds :
        {x : ℚᶜᵘⁿ_[p,T] | Valued.v x <
            ((Multiplicative.ofAdd (-k_min : ℤ) : Multiplicative ℤ) : WithZero _)} ∈
          nhds (0 : ℚᶜᵘⁿ_[p,T]) :=
      Tmem_nhds_zero_v_lt p T WithZero.coe_ne_zero
    have h_evtl_close : ∀ᶠ K : ℤ in Filter.atTop,
        Valued.v (∑ j ∈ Finset.Icc m_b K,
            (pInvTQ p T) ^ j *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
                (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b j)))) <
          ((Multiplicative.ofAdd (-k_min : ℤ) : Multiplicative ℤ) : WithZero _) := by
      have h_tend := hb_tendsto
      rw [h_y] at h_tend
      exact h_tend h_nhds
    have h_evtl_K_ge : ∀ᶠ K : ℤ in Filter.atTop, k_min ≤ K :=
      Filter.eventually_ge_atTop k_min
    obtain ⟨K, hKge, hKclose⟩ := (h_evtl_K_ge.and h_evtl_close).exists
    rw [h_sum_eq K hKge] at hKclose
    exact lt_irrefl _ hKclose
  · -- Step 2B: `y ≠ 0`. Derive `Valued.v y = ofAdd(-k_min)`.
    have h_v_y_eq : Valued.v y =
        ((Multiplicative.ofAdd (-k_min : ℤ) : Multiplicative ℤ) : WithZero _) := by
      have h_v_y_ne : Valued.v y ≠ 0 := by rwa [Valuation.ne_zero_iff]
      have h_nhds_y :
          {x : ℚᶜᵘⁿ_[p,T] | Valued.v (x - y) < Valued.v y} ∈ nhds y :=
        Tmem_nhds_v_sub_lt p T h_v_y_ne rfl
      have h_evtl_stable : ∀ᶠ K : ℤ in Filter.atTop,
          Valued.v ((∑ j ∈ Finset.Icc m_b K,
              (pInvTQ p T) ^ j *
                algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
                  (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b j)))) - y) <
            Valued.v y :=
        hb_tendsto h_nhds_y
      have h_evtl_K_ge : ∀ᶠ K : ℤ in Filter.atTop, k_min ≤ K :=
        Filter.eventually_ge_atTop k_min
      obtain ⟨K, hKge, hKstable⟩ := (h_evtl_K_ge.and h_evtl_stable).exists
      have h_valeq : Valued.v (∑ j ∈ Finset.Icc m_b K,
            (pInvTQ p T) ^ j *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
                (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b j)))) =
          Valued.v y := by
        rw [show (∑ j ∈ Finset.Icc m_b K,
              (pInvTQ p T) ^ j *
                algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
                  (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b j)))) =
            y + ((∑ j ∈ Finset.Icc m_b K,
              (pInvTQ p T) ^ j *
                algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
                  (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b j)))) - y)
            from by ring]
        rw [Valuation.map_add_eq_of_lt_left]
        exact hKstable
      rw [← h_valeq, h_sum_eq K hKge]
    -- Step 2C: build `slice` and bound `Valued.v y ≤ ofAdd(-m)`.
    set slice : Set ℤ := {n : ℤ | α.coeff (γ + (n : ℚ) / T) ≠ 0} with hslice_def
    have h_slice_ne : slice.Nonempty := by
      by_contra h_sl_e
      apply h_y
      have h_intP_zero : ∀ K : ℤ, TintPartial p T α γ K = 0 := by
        intro K
        simp only [TintPartial]
        apply Finset.sum_eq_zero
        intro n _
        have hn_mem : n.1 ≤ K ∧ α.coeff (γ + (n.1 : ℚ) / T) ≠ 0 :=
          (Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T α γ K)).mp n.2
        exfalso
        apply h_sl_e
        exact ⟨n.1, hn_mem.2⟩
      have h := hy_spec
      rw [show (TintPartial p T α γ) = (fun _ => (0 : ℚᶜᵘⁿ_[p,T])) from
        funext h_intP_zero] at h
      exact (tendsto_nhds_unique h tendsto_const_nhds)
    have hT_pos : (0 : ℚ) < T := by
      have hT : T ≠ 0 := NeZero.ne T
      exact_mod_cast Nat.pos_of_ne_zero hT
    have hslice_bdd : BddBelow slice := by
      by_cases hsupp : α.support.Nonempty
      · refine ⟨⌈(T : ℚ) * (α.isWF_support.min hsupp - γ : ℚ)⌉, ?_⟩
        intro n hn
        have hn_mem : (γ + (n : ℚ) / T) ∈ α.support := hn
        have hmin_le : α.isWF_support.min hsupp ≤ γ + (n : ℚ) / T :=
          α.isWF_support.min_le hsupp hn_mem
        have h1 : (α.isWF_support.min hsupp - γ : ℚ) ≤ (n : ℚ) / T := by linarith
        have h2 : (T : ℚ) * (α.isWF_support.min hsupp - γ) ≤ (T : ℚ) * ((n : ℚ) / T) :=
          mul_le_mul_of_nonneg_left h1 hT_pos.le
        have hT_eq : (T : ℚ) * ((n : ℚ) / T) = n := by
          rw [mul_div_assoc']; field_simp
        rw [hT_eq] at h2
        apply Int.ceil_le.mpr
        exact_mod_cast h2
      · exfalso
        obtain ⟨n, hn⟩ := h_slice_ne
        apply hsupp
        exact ⟨γ + (n : ℚ) / T, hn⟩
    obtain ⟨m, hm_mem, hm_min⟩ := Int.exists_least_of_bdd hslice_bdd h_slice_ne
    refine ⟨m, ?_, hm_mem⟩
    have h_v_y_le : Valued.v y ≤
        ((Multiplicative.ofAdd (-m : ℤ) : Multiplicative ℤ) : WithZero _) := by
      have h_intP_α_bound : ∀ K : ℤ, m ≤ K →
          Valued.v (TintPartial p T α γ K) ≤
            ((Multiplicative.ofAdd (-m : ℤ) : Multiplicative ℤ) : WithZero _) := by
        intro K _
        simp only [TintPartial]
        rw [show (∑ n : Set.Finite.toFinset (TfiniteBelowInt p T α γ K),
              (pInvTQ p T) ^ n.1 *
                algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (α.coeff (γ + (n.1 : ℚ) / T))) =
            ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T α γ K),
              (pInvTQ p T) ^ n *
                algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (α.coeff (γ + (n : ℚ) / T)) from
            Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T α γ K))
              (f := fun n : ℤ => (pInvTQ p T) ^ n *
                algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (α.coeff (γ + (n : ℚ) / T)))]
        apply Valuation.map_sum_le
        intro n hn
        have hn_mem : n ≤ K ∧ α.coeff (γ + (n : ℚ) / T) ≠ 0 :=
          (Set.Finite.mem_toFinset (hs := TfiniteBelowInt p T α γ K)).mp hn
        have hn_in_slice : n ∈ slice := hn_mem.2
        have hm_le_n : m ≤ n := hm_min n hn_in_slice
        rw [Valuation.map_mul, valued_v_pInvT_zpow (p := p) (T := T) n]
        have h_alg_le : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (α.coeff (γ + (n : ℚ) / T))) ≤ 1 :=
          (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_le_one
            (α.coeff (γ + (n : ℚ) / T))
        calc ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) *
                Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
                  (α.coeff (γ + (n : ℚ) / T)))
            ≤ ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) * 1 :=
              mul_le_mul' (le_refl _) h_alg_le
          _ = ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := mul_one _
          _ ≤ ((Multiplicative.ofAdd (-m : ℤ) : Multiplicative ℤ) : WithZero _) := by
              rw [WithZero.coe_le_coe]
              exact Multiplicative.ofAdd_le.mpr (by omega)
      have h_v_y_ne : Valued.v y ≠ 0 := by rwa [Valuation.ne_zero_iff]
      have h_nhds_y :
          {x : ℚᶜᵘⁿ_[p,T] | Valued.v (x - y) < Valued.v y} ∈ nhds y :=
        Tmem_nhds_v_sub_lt p T h_v_y_ne rfl
      have h_evtl_stable : ∀ᶠ K : ℤ in Filter.atTop,
          Valued.v (TintPartial p T α γ K - y) < Valued.v y :=
        hy_spec h_nhds_y
      have h_evtl_K_ge : ∀ᶠ K : ℤ in Filter.atTop, m ≤ K := Filter.eventually_ge_atTop m
      obtain ⟨K, hKge, hKstable⟩ := (h_evtl_K_ge.and h_evtl_stable).exists
      have h_intP_le := h_intP_α_bound K hKge
      have h_v_intP_eq_y : Valued.v (TintPartial p T α γ K) = Valued.v y := by
        rw [show TintPartial p T α γ K = y + (TintPartial p T α γ K - y) from by ring]
        rw [Valuation.map_add_eq_of_lt_left]
        exact hKstable
      rw [h_v_intP_eq_y] at h_intP_le
      exact h_intP_le
    -- Step 3: conclude `m ≤ k`.
    rw [h_v_y_eq] at h_v_y_le
    rw [WithZero.coe_le_coe] at h_v_y_le
    have hk_min_ge_m : m ≤ k_min := by
      have := Multiplicative.ofAdd_le.mp h_v_y_le
      omega
    have hk_min_le_k : k_min ≤ k := hk_min_le k h_k_in
    omega

open scoped Pointwise in
/-- **Phase 3A-iii main assembly.**  T-analogue of
`exists_canonical_representative` (lines 1841–2515).  Given a T-lifted Hahn
series `α`, there exists a coefficient function `s : ℚ → 𝔽ᵃ_[p]` with PWO support so
that `α - fromCoeff p T s` is a T-null-series. -/
theorem Texists_canonical_T_representative
    (α : TLiftedPAdicHahnSeries p T) :
    ∃ (s : ℚ → Fpbar p) (hspwo : (Function.support s).IsPWO),
      α - TLiftedPAdicHahnSeries.fromCoeff p T s hspwo ∈ TNullSeriesIdeal p T := by
  classical
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  have hT_ne : (T : ℚ) ≠ 0 := ne_of_gt hT_pos
  -- Setup: hp_ne, hpn_val
  have hp_ne : pInvTQ p T ≠ 0 := by
    unfold pInvTQ
    intro h
    exact pInvT_ne_zero p T
      ((IsFractionRing.injective (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]))
        (by simpa using h))
  -- Per-γ data: f γ, b γ, m_b γ via choose
  set f : ℚ → ℚᶜᵘⁿ_[p,T] := fun γ =>
    (Texists_lim_intPartial p T α γ).choose with hf_def
  have hf_spec : ∀ γ, Filter.Tendsto (TintPartial p T α γ) Filter.atTop (nhds (f γ)) :=
    fun γ => (Texists_lim_intPartial p T α γ).choose_spec
  set b : ℚ → ℤ → Fpbar p := fun γ =>
    (Texists_teichmuller_digits p T (f γ)).choose with hb_def
  set m_b : ℚ → ℤ := fun γ =>
    (Texists_teichmuller_digits p T (f γ)).choose_spec.choose with hmb_def
  have hb_spec : ∀ γ : ℚ,
      (∀ k : ℤ, k < m_b γ → b γ k = 0) ∧
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc (m_b γ) K,
          (pInvTQ p T) ^ k *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b γ k))))
        Filter.atTop (nhds (f γ)) := fun γ =>
    (Texists_teichmuller_digits p T (f γ)).choose_spec.choose_spec
  have hb_vanish : ∀ γ k, k < m_b γ → b γ k = 0 := fun γ => (hb_spec γ).1
  have hb_tendsto : ∀ γ, Filter.Tendsto
      (fun K : ℤ => ∑ k ∈ Finset.Icc (m_b γ) K,
        (pInvTQ p T) ^ k *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b γ k))))
      Filter.atTop (nhds (f γ)) := fun γ => (hb_spec γ).2
  -- Key claim: ∀ γ k, b γ k ≠ 0 → ∃ n_α ≤ k with α.coeff (γ + n_α/T) ≠ 0.
  have h_key : ∀ γ : ℚ, ∀ k : ℤ, b γ k ≠ 0 →
      ∃ n_α : ℤ, n_α ≤ k ∧ α.coeff (γ + (n_α : ℚ) / T) ≠ 0 := by
    intro γ k hbk
    -- The hypothesis hb_tendsto γ uses (Texists_lim_intPartial p T α γ).choose, which is f γ.
    have hb_tendsto_γ' : Filter.Tendsto
        (fun K : ℤ => ∑ j ∈ Finset.Icc (m_b γ) K,
          (pInvTQ p T) ^ j *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b γ j))))
        Filter.atTop (nhds ((Texists_lim_intPartial p T α γ).choose)) := hb_tendsto γ
    exact Th_key p T α γ k (b γ) (m_b γ) (hb_vanish γ) hb_tendsto_γ' hbk
  -- DEFINE s
  set s : ℚ → Fpbar p := fun q => b (Int.fract ((T : ℚ) * q) / T) ⌊(T : ℚ) * q⌋ with hs_def
  -- Coordinate split identity
  have h_split_id : ∀ q : ℚ,
      Int.fract ((T : ℚ) * q) / T + (⌊(T : ℚ) * q⌋ : ℚ) / T = q := by
    intro q
    have hf := Int.fract_add_floor ((T : ℚ) * q)
    field_simp
    linarith
  -- Show support s ⊆ α.support + Set.range (n/T : ℕ → ℚ)
  have hsupp_sub : Function.support s ⊆
      α.support + Set.range (fun n : ℕ => (n : ℚ) / T) := by
    intro q hq
    simp only [hs_def, Function.mem_support] at hq
    set γ_q : ℚ := Int.fract ((T : ℚ) * q) / T with hγq_def
    set n_q : ℤ := ⌊(T : ℚ) * q⌋ with hnq_def
    -- hq : b γ_q n_q ≠ 0
    obtain ⟨n_α, hn_α_le, hn_α_ne⟩ := h_key γ_q n_q hq
    refine ⟨γ_q + (n_α : ℚ) / T, hn_α_ne, ((n_q - n_α).toNat : ℚ) / T, ⟨(n_q - n_α).toNat, rfl⟩, ?_⟩
    · -- Goal: γ_q + n_α/T + ((n_q - n_α).toNat : ℚ) / T = q
      have h_pos : 0 ≤ n_q - n_α := sub_nonneg.mpr hn_α_le
      have h_toNat_int : ((n_q - n_α).toNat : ℤ) = n_q - n_α := Int.toNat_of_nonneg h_pos
      have h_cast : ((n_q - n_α).toNat : ℚ) = ((n_q : ℚ) - (n_α : ℚ)) := by
        have h1 : ((n_q - n_α).toNat : ℚ) = (((n_q - n_α).toNat : ℤ) : ℚ) := by push_cast; rfl
        rw [h1, h_toNat_int]
        push_cast
        ring
      change γ_q + (n_α : ℚ) / T + ((n_q - n_α).toNat : ℚ) / T = q
      rw [h_cast]
      have h_id := h_split_id q
      rw [show γ_q = Int.fract ((T : ℚ) * q) / T from rfl,
          show n_q = ⌊(T : ℚ) * q⌋ from rfl] at *
      field_simp
      have h_idT : Int.fract ((T : ℚ) * q) + (⌊(T : ℚ) * q⌋ : ℚ) = q * T := by
        have := h_id
        field_simp at this
        linarith
      linarith
  -- support s.IsPWO
  have hspwo : (Function.support s).IsPWO :=
    Tsupport_isPWO_of_subset_support_add_natRange p T α hsupp_sub
  refine ⟨s, hspwo, ?_⟩
  change IsTNullSeries p T (α - TLiftedPAdicHahnSeries.fromCoeff p T s hspwo)
  intro g
  set β : TLiftedPAdicHahnSeries p T := TLiftedPAdicHahnSeries.fromCoeff p T s hspwo with hβ_def
  set γ : ℚ := Int.fract ((T : ℚ) * g) / T with hγ_def
  set n₀ : ℤ := ⌊(T : ℚ) * g⌋ with hn₀_def
  have hg_eq : g = γ + (n₀ : ℚ) / T := by
    have h := h_split_id g
    rw [← hγ_def, ← hn₀_def] at h
    linarith
  have hTγ_eq : (T : ℚ) * γ = Int.fract ((T : ℚ) * g) := by
    rw [hγ_def]
    field_simp
  have hTγ_in_Ico : 0 ≤ (T : ℚ) * γ ∧ (T : ℚ) * γ < 1 := by
    rw [hTγ_eq]
    exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hβ_coeff : ∀ q : ℚ, β.coeff q =
      algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (s q)) := fun _ => rfl
  -- intPartial β γ K → f γ via Th_intPartial_eq_Icc + hb_tendsto
  have hs_eq_b : ∀ k : ℤ, s (γ + (k : ℚ) / T) = b γ k := by
    intro k
    change b (Int.fract ((T : ℚ) * (γ + (k : ℚ) / T)) / T)
        ⌊(T : ℚ) * (γ + (k : ℚ) / T)⌋ = b γ k
    have hT_dist : (T : ℚ) * (γ + (k : ℚ) / T) = (T : ℚ) * γ + (k : ℚ) := by
      field_simp
    rw [hT_dist]
    have h_fract : Int.fract ((T : ℚ) * γ + (k : ℚ)) = (T : ℚ) * γ := by
      rw [Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr hTγ_in_Ico
    have h_floor : ⌊(T : ℚ) * γ + (k : ℚ)⌋ = k := by
      rw [Int.floor_add_intCast]
      have : ⌊(T : ℚ) * γ⌋ = 0 := Int.floor_eq_zero_iff.mpr hTγ_in_Ico
      rw [this, zero_add]
    rw [h_fract, h_floor]
    have hγ_recover : (T : ℚ) * γ / T = γ := by field_simp
    rw [hγ_recover]
  have h_vanish_γ : ∀ k : ℤ, k < m_b γ → s (γ + (k : ℚ) / T) = 0 := by
    intro k hk
    rw [hs_eq_b k]; exact hb_vanish γ k hk
  have h_β_eq_γ : ∀ K : ℤ, m_b γ ≤ K →
      TintPartial p T β γ K =
        ∑ k ∈ Finset.Icc (m_b γ) K,
          (pInvTQ p T) ^ k *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (b γ k))) := by
    intro K hK
    rw [Th_intPartial_eq_Icc p T γ β s (m_b γ) hβ_coeff h_vanish_γ K hK]
    apply Finset.sum_congr rfl
    intro k _
    rw [hs_eq_b k]
  have h_tendsto_β_γ : Filter.Tendsto (TintPartial p T β γ) Filter.atTop (nhds (f γ)) := by
    apply (hb_tendsto γ).congr'
    rw [Filter.EventuallyEq]
    filter_upwards [Filter.eventually_ge_atTop (m_b γ)] with K hK
    exact (h_β_eq_γ K hK).symm
  -- Translation: TintPartial p T β' g K = (pInvTQ)^(-n₀) * TintPartial p T β' γ (K + n₀)
  have h_translate : ∀ (β' : TLiftedPAdicHahnSeries p T) (K : ℤ),
      TintPartial p T β' g K = (pInvTQ p T) ^ (-n₀) * TintPartial p T β' γ (K + n₀) := by
    intro β' K
    have hL : TintPartial p T β' g K =
        ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T β' g K),
          (pInvTQ p T) ^ n *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (β'.coeff (g + (n : ℚ) / T)) := by
      simp only [TintPartial]
      exact Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T β' g K))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (β'.coeff (g + (n : ℚ) / T)))
    have hR : TintPartial p T β' γ (K + n₀) =
        ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T β' γ (K + n₀)),
          (pInvTQ p T) ^ n *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (β'.coeff (γ + (n : ℚ) / T)) := by
      simp only [TintPartial]
      exact Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelowInt p T β' γ (K + n₀)))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (β'.coeff (γ + (n : ℚ) / T)))
    rw [hL, hR]
    have h_image : Set.Finite.toFinset (TfiniteBelowInt p T β' γ (K + n₀)) =
        (Set.Finite.toFinset (TfiniteBelowInt p T β' g K)).image (fun n : ℤ => n + n₀) := by
      ext n'
      simp only [Set.Finite.mem_toFinset, Finset.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨n' - n₀, ⟨by omega, ?_⟩, by omega⟩
        have h_eq_q : (g : ℚ) + ((n' - n₀ : ℤ) : ℚ) / T = (γ : ℚ) + (n' : ℚ) / T := by
          push_cast
          rw [hg_eq]; ring
        rw [h_eq_q]; exact h2
      · rintro ⟨n, ⟨hn1, hn2⟩, h_eq⟩
        refine ⟨by omega, ?_⟩
        have h_eq_q : (γ : ℚ) + (n' : ℚ) / T = (g : ℚ) + (n : ℚ) / T := by
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
    intro n _
    have h_coeff : β'.coeff ((γ : ℚ) + ((n + n₀ : ℤ) : ℚ) / T) =
        β'.coeff ((g : ℚ) + (n : ℚ) / T) := by
      congr 1
      push_cast
      rw [hg_eq]; ring
    rw [h_coeff]
    rw [show ((pInvTQ p T) ^ (-n₀)) * ((pInvTQ p T) ^ (n + n₀) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (β'.coeff ((g : ℚ) + (n : ℚ) / T))) =
        ((pInvTQ p T) ^ (-n₀) * (pInvTQ p T) ^ (n + n₀)) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (β'.coeff ((g : ℚ) + (n : ℚ) / T)) from by ring]
    rw [show (pInvTQ p T) ^ (-n₀) * (pInvTQ p T) ^ (n + n₀) = (pInvTQ p T) ^ n from by
      rw [← zpow_add₀ hp_ne]
      congr 1
      omega]
  -- intPartial β g K → f g
  have h_α_g : Filter.Tendsto (TintPartial p T α g) Filter.atTop (nhds (f g)) := hf_spec g
  have h_α_γ : Filter.Tendsto (TintPartial p T α γ) Filter.atTop (nhds (f γ)) := hf_spec γ
  have h_shift_atTop : Filter.Tendsto (fun K : ℤ => K + n₀) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
  have h_α_γ_shift : Filter.Tendsto (fun K : ℤ => TintPartial p T α γ (K + n₀)) Filter.atTop
      (nhds (f γ)) := h_α_γ.comp h_shift_atTop
  have h_α_γ_mul : Filter.Tendsto
      (fun K : ℤ => (pInvTQ p T) ^ (-n₀) * TintPartial p T α γ (K + n₀)) Filter.atTop
      (nhds ((pInvTQ p T) ^ (-n₀) * f γ)) := h_α_γ_shift.const_mul _
  have h_α_translate : Filter.Tendsto (TintPartial p T α g) Filter.atTop
      (nhds ((pInvTQ p T) ^ (-n₀) * f γ)) := by
    apply h_α_γ_mul.congr'
    rw [Filter.EventuallyEq]
    filter_upwards with K
    exact (h_translate α K).symm
  have h_fg_eq : f g = (pInvTQ p T) ^ (-n₀) * f γ :=
    tendsto_nhds_unique h_α_g h_α_translate
  have h_β_γ_shift : Filter.Tendsto (fun K : ℤ => TintPartial p T β γ (K + n₀)) Filter.atTop
      (nhds (f γ)) := h_tendsto_β_γ.comp h_shift_atTop
  have h_β_γ_mul : Filter.Tendsto
      (fun K : ℤ => (pInvTQ p T) ^ (-n₀) * TintPartial p T β γ (K + n₀)) Filter.atTop
      (nhds ((pInvTQ p T) ^ (-n₀) * f γ)) := h_β_γ_shift.const_mul _
  have h_β_g : Filter.Tendsto (TintPartial p T β g) Filter.atTop (nhds (f g)) := by
    rw [h_fg_eq]
    apply h_β_γ_mul.congr'
    rw [Filter.EventuallyEq]
    filter_upwards with K
    exact (h_translate β K).symm
  -- intPartial (α - β) g K → 0
  have h_intPartial_zero : Filter.Tendsto (fun K : ℤ => TintPartial p T (α - β) g K)
      Filter.atTop (nhds (0 : ℚᶜᵘⁿ_[p,T])) := by
    have h_diff : Filter.Tendsto
        (fun K : ℤ => TintPartial p T α g K - TintPartial p T β g K) Filter.atTop
        (nhds ((f g) - (f g))) := h_α_g.sub h_β_g
    rw [sub_self] at h_diff
    apply h_diff.congr'
    rw [Filter.EventuallyEq]
    filter_upwards with K
    exact (Th_intPartial_sub p T α β g K).symm
  -- Bridge finiteBelow ⇄ finiteBelowInt (T-shifted)
  have h_finiteBelow_eq_finiteBelowInt :
      ∀ (x : TLiftedPAdicHahnSeries p T) (M : ℕ),
        (Set.Finite.toFinset (TfiniteBelow p T x g M) : Finset ℤ) =
        (Set.Finite.toFinset (TfiniteBelowInt p T x g ⌊(T : ℚ) * ((M : ℚ) - g)⌋) : Finset ℤ) := by
    intro x M
    ext n
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · intro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      -- h1 : g + n/T ≤ M ⇒ n ≤ floor(T*(M - g))
      have hineq : (n : ℚ) / T ≤ (M : ℚ) - g := by linarith
      have hineq' : (T : ℚ) * ((n : ℚ) / T) ≤ (T : ℚ) * ((M : ℚ) - g) :=
        mul_le_mul_of_nonneg_left hineq hT_pos.le
      have hT_eq : (T : ℚ) * ((n : ℚ) / T) = n := by
        rw [mul_div_assoc']; field_simp
      rw [hT_eq] at hineq'
      apply Int.le_floor.mpr
      exact_mod_cast hineq'
    · intro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      -- h1 : n ≤ ⌊T*(M - g)⌋ ⇒ g + n/T ≤ M
      have h1' : (n : ℚ) ≤ (T : ℚ) * ((M : ℚ) - g) := by
        have h1q : ((n : ℤ) : ℚ) ≤ ((⌊(T : ℚ) * ((M : ℚ) - g)⌋ : ℤ) : ℚ) := by
          exact_mod_cast h1
        exact le_trans h1q (Int.floor_le _)
      have h2' : (n : ℚ) / T ≤ ((T : ℚ) * ((M : ℚ) - g)) / T := by
        exact div_le_div_of_nonneg_right h1' hT_pos.le
      have hT_eq : ((T : ℚ) * ((M : ℚ) - g)) / T = (M : ℚ) - g := by
        field_simp
      rw [hT_eq] at h2'
      linarith
  have h_finiteBelow_to_intPartial :
      (fun M : ℕ => ∑ n : Set.Finite.toFinset (TfiniteBelow p T (α - β) g M),
        (pInvTQ p T) ^ (n.val : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            ((α - β).coeff (g + (n.val : ℚ) / T))) =
      fun M : ℕ => TintPartial p T (α - β) g ⌊(T : ℚ) * ((M : ℚ) - g)⌋ := by
    funext M
    simp only [TintPartial]
    have h_attach_α := Finset.sum_attach
      (s := Set.Finite.toFinset (TfiniteBelow p T (α - β) g M))
      (f := fun n : ℤ => (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - β).coeff (g + (n : ℚ) / T)))
    have h_attach_β := Finset.sum_attach
      (s := Set.Finite.toFinset (TfiniteBelowInt p T (α - β) g ⌊(T : ℚ) * ((M : ℚ) - g)⌋))
      (f := fun n : ℤ => (pInvTQ p T) ^ n *
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - β).coeff (g + (n : ℚ) / T)))
    rw [show (∑ n : Set.Finite.toFinset (TfiniteBelow p T (α - β) g M),
        (pInvTQ p T) ^ (n.val : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - β).coeff (g + (n.val : ℚ) / T))) =
      ∑ n ∈ Set.Finite.toFinset (TfiniteBelow p T (α - β) g M),
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - β).coeff (g + (n : ℚ) / T)) from h_attach_α]
    rw [show (∑ n : Set.Finite.toFinset
          (TfiniteBelowInt p T (α - β) g ⌊(T : ℚ) * ((M : ℚ) - g)⌋),
        (pInvTQ p T) ^ (n.1 : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - β).coeff (g + (n.1 : ℚ) / T))) =
      ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T (α - β) g ⌊(T : ℚ) * ((M : ℚ) - g)⌋),
        (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - β).coeff (g + (n : ℚ) / T)) from h_attach_β]
    rw [h_finiteBelow_eq_finiteBelowInt (α - β) M]
  have h_φ : Filter.Tendsto (fun M : ℕ => ⌊(T : ℚ) * ((M : ℚ) - g)⌋) Filter.atTop
      Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b'
    obtain ⟨N, hN⟩ := exists_nat_ge ((b' : ℚ) / T + g)
    refine ⟨N, ?_⟩
    intro M hM
    rw [Int.le_floor]
    have hM' : (N : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
    have h_step : (b' : ℚ) / T + g ≤ (M : ℚ) := le_trans hN hM'
    have : (b' : ℚ) / T ≤ (M : ℚ) - g := by linarith
    have h_mul : (T : ℚ) * ((b' : ℚ) / T) ≤ (T : ℚ) * ((M : ℚ) - g) :=
      mul_le_mul_of_nonneg_left this hT_pos.le
    have hT_eq : (T : ℚ) * ((b' : ℚ) / T) = b' := by
      rw [mul_div_assoc']; field_simp
    rw [hT_eq] at h_mul
    exact_mod_cast h_mul
  -- Compose
  rw [h_finiteBelow_to_intPartial]
  exact h_intPartial_zero.comp h_φ

/-! ### Phase 3B: uniqueness of canonical T-representative -/

/-- **Phase 3B.**  T-analogue of `unique_canonical_representative`
(lines 2517–2883).  Two coefficient functions producing T-equivalent canonical
expansions are equal. -/
theorem Tunique_canonical_T_representative
    {s s' : ℚ → Fpbar p}
    (hspwo : (Function.support s).IsPWO) (hspwo' : (Function.support s').IsPWO)
    (h : TLiftedPAdicHahnSeries.fromCoeff p T s hspwo
        - TLiftedPAdicHahnSeries.fromCoeff p T s' hspwo'
        ∈ TNullSeriesIdeal p T) :
    s = s' := by
  classical
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  have hT_ne : (T : ℚ) ≠ 0 := ne_of_gt hT_pos
  set α  : TLiftedPAdicHahnSeries p T :=
    TLiftedPAdicHahnSeries.fromCoeff p T s  hspwo  with hα_def
  set α' : TLiftedPAdicHahnSeries p T :=
    TLiftedPAdicHahnSeries.fromCoeff p T s' hspwo' with hα'_def
  change IsTNullSeries p T (α - α') at h
  have hp_ne : pInvTQ p T ≠ 0 := by
    unfold pInvTQ
    intro h_z
    exact pInvT_ne_zero p T
      ((IsFractionRing.injective (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]))
        (by simpa using h_z))
  have hα_coeff  : ∀ q : ℚ, α.coeff  q
      = algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (s  q)) := fun _ => rfl
  have hα'_coeff : ∀ q : ℚ, α'.coeff q
      = algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (s' q)) := fun _ => rfl
  funext q
  set γ  : ℚ := Int.fract ((T : ℚ) * q) / T with hγ_def
  set n₀ : ℤ := ⌊(T : ℚ) * q⌋ with hn₀_def
  have hq_eq : q = γ + (n₀ : ℚ) / T := by
    have hf := Int.fract_add_floor ((T : ℚ) * q)
    change q = Int.fract ((T : ℚ) * q) / T + (⌊(T : ℚ) * q⌋ : ℚ) / T
    rw [show (T : ℚ) * q = q * T from mul_comm _ _] at hf
    field_simp
    linarith
  set Bs  : ℤ → Fpbar p := fun k => s  (γ + (k : ℚ) / T) with hBs_def
  set Bs' : ℤ → Fpbar p := fun k => s' (γ + (k : ℚ) / T) with hBs'_def
  change s q = s' q
  rw [hq_eq]
  suffices h_Bs_eq : ∀ k : ℤ, Bs k = Bs' k by
    exact h_Bs_eq n₀
  -- Cutoffs: ∃ m_s, ∀ k < m_s, Bs k = 0
  obtain ⟨m_s, hm_s⟩ : ∃ m_s : ℤ, ∀ k : ℤ, k < m_s → Bs k = 0 := by
    by_cases hsp : (Function.support s).Nonempty
    · refine ⟨⌈(T : ℚ) * (hspwo.isWF.min hsp - γ)⌉, ?_⟩
      intro k hk
      change s (γ + (k : ℚ) / T) = 0
      by_contra hne
      have hmem : (γ + (k : ℚ) / T) ∈ Function.support s := hne
      have hmin_le : hspwo.isWF.min hsp ≤ γ + (k : ℚ) / T :=
        hspwo.isWF.min_le hsp hmem
      have hk_ineq : ((T : ℚ) * (hspwo.isWF.min hsp - γ) : ℚ) ≤ (k : ℚ) := by
        have h1 : hspwo.isWF.min hsp - γ ≤ (k : ℚ) / T := by linarith
        have h2 : (T : ℚ) * (hspwo.isWF.min hsp - γ) ≤ (T : ℚ) * ((k : ℚ) / T) :=
          mul_le_mul_of_nonneg_left h1 hT_pos.le
        have hT_eq : (T : ℚ) * ((k : ℚ) / T) = k := by
          rw [mul_div_assoc']; field_simp
        rw [hT_eq] at h2
        exact h2
      have hceil : ⌈(T : ℚ) * (hspwo.isWF.min hsp - γ)⌉ ≤ k := Int.ceil_le.mpr hk_ineq
      linarith
    · refine ⟨0, ?_⟩
      intro k _
      change s (γ + (k : ℚ) / T) = 0
      have hs_zero : s = 0 := Function.support_eq_empty_iff.mp
        (Set.not_nonempty_iff_eq_empty.mp hsp)
      simp [hs_zero]
  obtain ⟨m_s', hm_s'⟩ : ∃ m_s' : ℤ, ∀ k : ℤ, k < m_s' → Bs' k = 0 := by
    by_cases hsp : (Function.support s').Nonempty
    · refine ⟨⌈(T : ℚ) * (hspwo'.isWF.min hsp - γ)⌉, ?_⟩
      intro k hk
      change s' (γ + (k : ℚ) / T) = 0
      by_contra hne
      have hmem : (γ + (k : ℚ) / T) ∈ Function.support s' := hne
      have hmin_le : hspwo'.isWF.min hsp ≤ γ + (k : ℚ) / T :=
        hspwo'.isWF.min_le hsp hmem
      have hk_ineq : ((T : ℚ) * (hspwo'.isWF.min hsp - γ) : ℚ) ≤ (k : ℚ) := by
        have h1 : hspwo'.isWF.min hsp - γ ≤ (k : ℚ) / T := by linarith
        have h2 : (T : ℚ) * (hspwo'.isWF.min hsp - γ) ≤ (T : ℚ) * ((k : ℚ) / T) :=
          mul_le_mul_of_nonneg_left h1 hT_pos.le
        have hT_eq : (T : ℚ) * ((k : ℚ) / T) = k := by
          rw [mul_div_assoc']; field_simp
        rw [hT_eq] at h2
        exact h2
      have hceil : ⌈(T : ℚ) * (hspwo'.isWF.min hsp - γ)⌉ ≤ k := Int.ceil_le.mpr hk_ineq
      linarith
    · refine ⟨0, ?_⟩
      intro k _
      change s' (γ + (k : ℚ) / T) = 0
      have hs_zero : s' = 0 := Function.support_eq_empty_iff.mp
        (Set.not_nonempty_iff_eq_empty.mp hsp)
      simp [hs_zero]
  -- Limits via Texists_lim_intPartial
  obtain ⟨y_s,  hy_s⟩  := Texists_lim_intPartial p T α  γ
  obtain ⟨y_s', hy_s'⟩ := Texists_lim_intPartial p T α' γ
  obtain ⟨y_d,  hy_d⟩  := Texists_lim_intPartial p T (α - α') γ
  -- Tendsto in Icc form via Th_intPartial_eq_Icc citation
  have hvanish_s : ∀ k : ℤ, k < m_s → s (γ + (k : ℚ) / T) = 0 := hm_s
  have hvanish_s' : ∀ k : ℤ, k < m_s' → s' (γ + (k : ℚ) / T) = 0 := hm_s'
  have htendsto_s :
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m_s K,
          (pInvTQ p T) ^ k *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (Bs k))))
        Filter.atTop (nhds y_s) := by
    apply hy_s.congr'
    rw [Filter.EventuallyEq]
    filter_upwards [Filter.eventually_ge_atTop m_s] with K hK
    exact Th_intPartial_eq_Icc p T γ α s m_s hα_coeff hvanish_s K hK
  have htendsto_s' :
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m_s' K,
          (pInvTQ p T) ^ k *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) (teichmuller p (Bs' k))))
        Filter.atTop (nhds y_s') := by
    apply hy_s'.congr'
    rw [Filter.EventuallyEq]
    filter_upwards [Filter.eventually_ge_atTop m_s'] with K hK
    exact Th_intPartial_eq_Icc p T γ α' s' m_s' hα'_coeff hvanish_s' K hK
  -- intPartial of difference (one-line citation)
  have h_intPartial_sub : ∀ K : ℤ,
      TintPartial p T (α - α') γ K = TintPartial p T α γ K - TintPartial p T α' γ K :=
    fun K => Th_intPartial_sub p T α α' γ K
  -- y_d = y_s - y_s'
  have h_yd_eq : y_d = y_s - y_s' := by
    have h_diff : Filter.Tendsto
        (fun K : ℤ => TintPartial p T α γ K - TintPartial p T α' γ K)
        Filter.atTop (nhds (y_s - y_s')) := hy_s.sub hy_s'
    have hy_d' : Filter.Tendsto
        (fun K : ℤ => TintPartial p T α γ K - TintPartial p T α' γ K)
        Filter.atTop (nhds y_d) := by
      apply hy_d.congr'
      rw [Filter.EventuallyEq]
      filter_upwards with K
      exact h_intPartial_sub K
    exact tendsto_nhds_unique hy_d' h_diff
  -- `y_d = 0` follows from `IsTNullSeries` via the T-shifted `finiteBelow` bridge.
  have h_yd_zero : y_d = 0 := by
    have h_finiteBelow_eq_finiteBelowInt :
        ∀ (x : TLiftedPAdicHahnSeries p T) (M : ℕ),
          (Set.Finite.toFinset (TfiniteBelow p T x γ M) : Finset ℤ) =
          (Set.Finite.toFinset (TfiniteBelowInt p T x γ ⌊(T : ℚ) * ((M : ℚ) - γ)⌋) : Finset ℤ) := by
      intro x M
      ext n
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      constructor
      · intro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        have hineq : (n : ℚ) / T ≤ (M : ℚ) - γ := by linarith
        have hineq' : (T : ℚ) * ((n : ℚ) / T) ≤ (T : ℚ) * ((M : ℚ) - γ) :=
          mul_le_mul_of_nonneg_left hineq hT_pos.le
        have hT_eq : (T : ℚ) * ((n : ℚ) / T) = n := by
          rw [mul_div_assoc']; field_simp
        rw [hT_eq] at hineq'
        apply Int.le_floor.mpr
        exact_mod_cast hineq'
      · intro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        have h1' : (n : ℚ) ≤ (T : ℚ) * ((M : ℚ) - γ) := by
          have h1q : ((n : ℤ) : ℚ) ≤ ((⌊(T : ℚ) * ((M : ℚ) - γ)⌋ : ℤ) : ℚ) := by
            exact_mod_cast h1
          exact le_trans h1q (Int.floor_le _)
        have h2' : (n : ℚ) / T ≤ ((T : ℚ) * ((M : ℚ) - γ)) / T :=
          div_le_div_of_nonneg_right h1' hT_pos.le
        have hT_eq : ((T : ℚ) * ((M : ℚ) - γ)) / T = (M : ℚ) - γ := by
          field_simp
        rw [hT_eq] at h2'
        linarith
    have h_finiteBelow_to_intPartial :
        (fun M : ℕ => ∑ n : Set.Finite.toFinset (TfiniteBelow p T (α - α') γ M),
          (pInvTQ p T) ^ (n.val : ℤ) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
              ((α - α').coeff (γ + (n.val : ℚ) / T))) =
        fun M : ℕ => TintPartial p T (α - α') γ ⌊(T : ℚ) * ((M : ℚ) - γ)⌋ := by
      funext M
      simp only [TintPartial]
      have h_attach_α := Finset.sum_attach
        (s := Set.Finite.toFinset (TfiniteBelow p T (α - α') γ M))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - α').coeff (γ + (n : ℚ) / T)))
      have h_attach_β := Finset.sum_attach
        (s := Set.Finite.toFinset (TfiniteBelowInt p T (α - α') γ ⌊(T : ℚ) * ((M : ℚ) - γ)⌋))
        (f := fun n : ℤ => (pInvTQ p T) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - α').coeff (γ + (n : ℚ) / T)))
      rw [show (∑ n : Set.Finite.toFinset (TfiniteBelow p T (α - α') γ M),
          (pInvTQ p T) ^ (n.val : ℤ) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - α').coeff (γ + (n.val : ℚ) / T))) =
        ∑ n ∈ Set.Finite.toFinset (TfiniteBelow p T (α - α') γ M),
          (pInvTQ p T) ^ n *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - α').coeff (γ + (n : ℚ) / T)) from h_attach_α]
      rw [show (∑ n : Set.Finite.toFinset
            (TfiniteBelowInt p T (α - α') γ ⌊(T : ℚ) * ((M : ℚ) - γ)⌋),
          (pInvTQ p T) ^ (n.1 : ℤ) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - α').coeff (γ + (n.1 : ℚ) / T))) =
        ∑ n ∈ Set.Finite.toFinset (TfiniteBelowInt p T (α - α') γ ⌊(T : ℚ) * ((M : ℚ) - γ)⌋),
          (pInvTQ p T) ^ n *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((α - α').coeff (γ + (n : ℚ) / T)) from h_attach_β]
      rw [h_finiteBelow_eq_finiteBelowInt (α - α') M]
    have h_at_γ := h γ
    rw [h_finiteBelow_to_intPartial] at h_at_γ
    have h_φ : Filter.Tendsto (fun M : ℕ => ⌊(T : ℚ) * ((M : ℚ) - γ)⌋) Filter.atTop
        Filter.atTop := by
      apply Filter.tendsto_atTop_atTop.mpr
      intro b'
      obtain ⟨N, hN⟩ := exists_nat_ge ((b' : ℚ) / T + γ)
      refine ⟨N, ?_⟩
      intro M hM
      rw [Int.le_floor]
      have hM' : (N : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
      have h_step : (b' : ℚ) / T + γ ≤ (M : ℚ) := le_trans hN hM'
      have hh : (b' : ℚ) / T ≤ (M : ℚ) - γ := by linarith
      have h_mul : (T : ℚ) * ((b' : ℚ) / T) ≤ (T : ℚ) * ((M : ℚ) - γ) :=
        mul_le_mul_of_nonneg_left hh hT_pos.le
      have hT_eq : (T : ℚ) * ((b' : ℚ) / T) = b' := by
        rw [mul_div_assoc']; field_simp
      rw [hT_eq] at h_mul
      exact_mod_cast h_mul
    have h_comp : Filter.Tendsto
        (fun M : ℕ => TintPartial p T (α - α') γ ⌊(T : ℚ) * ((M : ℚ) - γ)⌋)
        Filter.atTop (nhds y_d) := hy_d.comp h_φ
    exact tendsto_nhds_unique h_comp h_at_γ
  -- Wrap-up: y_s = y_s' ⇒ Tteichmuller_digits_unique
  have h_y_eq : y_s = y_s' := by
    have h1 : y_s - y_s' = 0 := by rw [← h_yd_eq, h_yd_zero]
    exact sub_eq_zero.mp h1
  rw [h_y_eq] at htendsto_s
  -- Convert doubled-algebraMap form into TTeichmuller form to match Tteichmuller_digits_unique
  have htendsto_s_TT :
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m_s K,
          (pInvTQ p T) ^ k *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (TTeichmuller p T (Bs k)))
        Filter.atTop (nhds y_s') := htendsto_s
  have htendsto_s'_TT :
      Filter.Tendsto
        (fun K : ℤ => ∑ k ∈ Finset.Icc m_s' K,
          (pInvTQ p T) ^ k *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (TTeichmuller p T (Bs' k)))
        Filter.atTop (nhds y_s') := htendsto_s'
  exact Tteichmuller_digits_unique (p := p) (T := T)
    Bs Bs' m_s m_s' hm_s hm_s' htendsto_s_TT htendsto_s'_TT

/-! ### Lemma 4.6 (2) — canonical Teichmüller expansion -/

/-- **Lemma 4.6 (2).**  Every class in `TLiftedPAdicHahnSeries p T / TNullSeriesIdeal p T`
admits a unique representative of the canonical Teichmüller form `∑ [g(q)] t^q` for some
`g : ℚ → 𝔽ᵃ_[p]` with well-ordered support. -/
theorem exists_canonical_T_expansion :
    ∀ A : (TLiftedPAdicHahnSeries p T) ⧸ (TNullSeriesIdeal p T),
      ∃! (s : {f : ℚ → Fpbar p // (Function.support f).IsPWO}),
        Ideal.Quotient.ringCon (TNullSeriesIdeal p T)
          A.out (TLiftedPAdicHahnSeries.fromCoeff p T s.val s.prop) := by
  intro A
  obtain ⟨s, hspwo, hα⟩ := Texists_canonical_T_representative (p := p) (T := T) A.out
  refine ⟨⟨s, hspwo⟩, ?_, ?_⟩
  · have hmk :
        (Ideal.Quotient.mk (TNullSeriesIdeal p T)) A.out =
          (Ideal.Quotient.mk (TNullSeriesIdeal p T))
            (TLiftedPAdicHahnSeries.fromCoeff p T s hspwo) :=
      Ideal.Quotient.eq.mpr hα
    exact Quotient.exact hmk
  · rintro ⟨s', hspwo'⟩ h'
    have hα' :
        A.out - TLiftedPAdicHahnSeries.fromCoeff p T s' hspwo' ∈ TNullSeriesIdeal p T := by
      have hmk' :
          (Ideal.Quotient.mk (TNullSeriesIdeal p T)) A.out =
            (Ideal.Quotient.mk (TNullSeriesIdeal p T))
              (TLiftedPAdicHahnSeries.fromCoeff p T s' hspwo') :=
        Quotient.sound h'
      exact Ideal.Quotient.eq.mp hmk'
    have hsub :
        TLiftedPAdicHahnSeries.fromCoeff p T s hspwo -
          TLiftedPAdicHahnSeries.fromCoeff p T s' hspwo' ∈ TNullSeriesIdeal p T := by
      have h1 := (TNullSeriesIdeal p T).sub_mem hα' hα
      simpa [sub_sub_sub_cancel_left] using h1
    have hfun : s = s' :=
      Tunique_canonical_T_representative (p := p) (T := T) hspwo hspwo' hsub
    subst hfun
    rfl

/-! ### Lemma 4.6 (3) — `TNullSeriesIdeal` is maximal -/

/-- **Helper B.** Port of `support_nonempty_of_nonzero` (lines 2940–2952).
For a nonzero class `x` in the quotient, the canonical T-expansion has nonempty support. -/
private lemma Tsupport_nonempty_of_nonzero
    (x : (TLiftedPAdicHahnSeries p T) ⧸ (TNullSeriesIdeal p T)) (h : ¬x = 0) :
    (exists_canonical_T_expansion p T x).choose.val.support.Nonempty := by
  contrapose h
  simp only [Subtype.forall, Function.support_nonempty_iff, ne_eq, not_not] at h
  have := (exists_canonical_T_expansion p T x).choose_spec.1
  simp only [Subtype.forall, h] at this
  suffices h' : (TLiftedPAdicHahnSeries.fromCoeff p T (0 : ℚ → Fpbar p) (by simp)) = 0 by
    simp only [h'] at this
    rw [← Quotient.out_eq x]
    exact Quotient.sound this
  apply HahnSeries.ext
  funext n
  change OQpCUn_embd p T (teichmuller p ((0 : ℚ → Fpbar p) n)) =
    (0 : TLiftedPAdicHahnSeries p T).coeff n
  simp [WittVector.teichmuller_zero]

/-- **Helper D.** Port of `null_series_no_unit_leading` (Poonen 3013–3144).
A T-null-series cannot have a unit-valued leading coefficient. -/
private lemma Tnull_series_no_unit_leading
    {Δ : TLiftedPAdicHahnSeries p T} (hΔ : Δ ∈ TNullSeriesIdeal p T)
    {q : ℚ} (hq_unit : IsUnit (Δ.coeff q))
    (hq_lead : ∀ q' < q, Δ.coeff q' = 0) : False := by
  change IsTNullSeries p T Δ at hΔ
  have htend := hΔ q
  have hpn_val := valued_v_pInvT_zpow (p := p) (T := T)
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  have hT_ne : (T : ℚ) ≠ 0 := ne_of_gt hT_pos
  -- n=0 term has valuation ofAdd(0).
  have h_lead_val : Valued.v ((pInvTQ p T)^(0 : ℤ) *
      algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Δ.coeff q)) =
      ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _) := by
    rw [Valuation.map_mul, hpn_val 0]
    have hval : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Δ.coeff q)) = 1 := by
      rcases hq_unit with ⟨u, hu⟩
      rw [← hu, Tvalued_v_algebraMap_unit_one (p := p) (T := T) u]
    rw [hval, mul_one]
    rfl
  have hq_ne : Δ.coeff q ≠ 0 := by
    intro h
    rw [h] at hq_unit
    exact (not_isUnit_zero) hq_unit
  -- index helper: q + (0 : ℤ)/T = q
  have h_zero_idx : (q + (((0 : ℤ) : ℚ)) / T) = q := by push_cast; ring
  have h_zero_in : ∀ M : ℕ, q ≤ (M : ℚ) →
      (0 : ℤ) ∈ Set.Finite.toFinset (TfiniteBelow p T Δ q M) := by
    intro M hMq
    apply (Set.Finite.mem_toFinset (hs := TfiniteBelow p T Δ q M) (a := 0)).2
    refine ⟨?_, ?_⟩
    · rw [h_zero_idx]; exact hMq
    · rw [h_zero_idx]; exact hq_ne
  have h_sum_eq : ∀ M : ℕ, q ≤ (M : ℚ) →
      Valued.v (∑ n : Set.Finite.toFinset (TfiniteBelow p T Δ q M),
          (pInvTQ p T) ^ (n.val : ℤ) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Δ.coeff (q + (n.val : ℚ) / T))) =
        ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _) := by
    intro M hMq
    rw [show (∑ n : Set.Finite.toFinset (TfiniteBelow p T Δ q M),
            (pInvTQ p T) ^ (n.val : ℤ) *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Δ.coeff (q + (n.val : ℚ) / T))) =
        ∑ n ∈ Set.Finite.toFinset (TfiniteBelow p T Δ q M),
          (pInvTQ p T) ^ n *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Δ.coeff (q + (n : ℚ) / T)) from
        Finset.sum_attach (s := Set.Finite.toFinset (TfiniteBelow p T Δ q M))
          (f := fun n : ℤ => (pInvTQ p T) ^ n *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Δ.coeff (q + (n : ℚ) / T)))]
    have h_in : (0 : ℤ) ∈ Set.Finite.toFinset (TfiniteBelow p T Δ q M) := h_zero_in M hMq
    rw [show Set.Finite.toFinset (TfiniteBelow p T Δ q M) =
        insert (0 : ℤ) ((Set.Finite.toFinset (TfiniteBelow p T Δ q M)).erase 0) from
        (Finset.insert_erase h_in).symm]
    rw [Finset.sum_insert (Finset.notMem_erase _ _)]
    rw [Valuation.map_add_eq_of_lt_left]
    · rw [h_zero_idx]; exact h_lead_val
    · have h_bound : Valued.v (∑ n ∈ (Set.Finite.toFinset (TfiniteBelow p T Δ q M)).erase 0,
            (pInvTQ p T) ^ n *
              algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Δ.coeff (q + (n : ℚ) / T))) ≤
          ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
        apply Valuation.map_sum_le
        intro n hn_mem
        have hn_ne_zero : n ≠ 0 := Finset.ne_of_mem_erase hn_mem
        have hn_in_finset : n ∈ Set.Finite.toFinset (TfiniteBelow p T Δ q M) :=
          (Finset.mem_erase.mp hn_mem).2
        have hn_data : q + (n : ℚ) / T ≤ (M : ℚ) ∧ Δ.coeff (q + (n : ℚ) / T) ≠ 0 :=
          (Set.Finite.mem_toFinset (hs := TfiniteBelow p T Δ q M) (a := n)).1 hn_in_finset
        have hn_pos : 1 ≤ n := by
          rcases Int.lt_or_le n 0 with hlt | hle
          · exfalso
            apply hn_data.2
            apply hq_lead
            have hncast : ((n : ℚ)) < 0 := by exact_mod_cast hlt
            have hnT_lt : (n : ℚ) / T < 0 := div_neg_of_neg_of_pos hncast hT_pos
            linarith
          · omega
        rw [Valuation.map_mul, hpn_val n]
        have h_alg_le : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            (Δ.coeff (q + (n : ℚ) / T))) ≤ 1 :=
          (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p,T])).valuation_le_one
            (Δ.coeff (q + (n : ℚ) / T))
        calc ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) *
                Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Δ.coeff (q + (n : ℚ) / T)))
            ≤ ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) * 1 :=
              mul_le_mul' (le_refl _) h_alg_le
          _ = ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := mul_one _
          _ ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
              rw [WithZero.coe_le_coe]
              exact Multiplicative.ofAdd_le.mpr (by omega)
      apply lt_of_le_of_lt h_bound
      rw [h_zero_idx, h_lead_val]
      rw [WithZero.coe_lt_coe]
      exact Multiplicative.ofAdd_lt.mpr (by omega)
  have h_nhds :
      {x : ℚᶜᵘⁿ_[p,T] | Valued.v x <
          ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _)} ∈
        nhds (0 : ℚᶜᵘⁿ_[p,T]) :=
    Tmem_nhds_zero_v_lt p T WithZero.coe_ne_zero
  have h_evtl_close : ∀ᶠ M : ℕ in Filter.atTop,
      Valued.v (∑ n : Set.Finite.toFinset (TfiniteBelow p T Δ q M),
          (pInvTQ p T) ^ (n.val : ℤ) *
            algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (Δ.coeff (q + (n.val : ℚ) / T))) <
        ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _) :=
    htend h_nhds
  have h_evtl_M_ge : ∀ᶠ M : ℕ in Filter.atTop, q ≤ (M : ℚ) := by
    have h_int : ∀ᶠ M : ℕ in Filter.atTop, ⌈q⌉₊ ≤ M := Filter.eventually_ge_atTop ⌈q⌉₊
    filter_upwards [h_int] with M hM
    have h1 : (q : ℚ) ≤ (⌈q⌉₊ : ℚ) := Nat.le_ceil q
    have h2 : ((⌈q⌉₊ : ℕ) : ℚ) ≤ ((M : ℕ) : ℚ) := by exact_mod_cast hM
    linarith
  obtain ⟨M, hMge, hMclose⟩ := (h_evtl_M_ge.and h_evtl_close).exists
  rw [h_sum_eq M hMge] at hMclose
  exact lt_irrefl _ hMclose

/-- **Helper C.** Port of `canonical_leading_coeff_isUnit` (Poonen 3149–3162),
re-routed via the residue map (since `WittVector.isUnit_of_coeff_zero_ne_zero` does not
apply to `ℤᶜᵘⁿ_[p,T]`). -/
private lemma Tcanonical_leading_coeff_isUnit
    {s : ℚ → Fpbar p} (hspwo : (Function.support s).IsPWO)
    (hsne : (Function.support s).Nonempty) :
    IsUnit ((TLiftedPAdicHahnSeries.fromCoeff p T s hspwo).coeff
      (hspwo.isWF.min hsne)) := by
  set q₀ := hspwo.isWF.min hsne with hq₀_def
  have hq₀_in : q₀ ∈ Function.support s := hspwo.isWF.min_mem hsne
  have hsq₀_ne : s q₀ ≠ 0 := hq₀_in
  change IsUnit (TTeichmuller p T (s q₀))
  -- In the local ring `ℤᶜᵘⁿ_[p,T]`, `IsUnit a ↔ a ∉ maximalIdeal`.
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  -- Apply the residue route: `TRes (TTeichmuller α) = α`, but if it lies in maximalIdeal then
  -- its residue is 0.
  have hmax_eq : IsLocalRing.maximalIdeal (ℤᶜᵘⁿ_[p,T]) =
      Ideal.span {pInvT p T} := (IsLocalRing.eq_maximalIdeal (pInvT_maximal p T)).symm
  rw [hmax_eq, Ideal.mem_span_singleton] at hmem
  have hres : TResidue p T (TTeichmuller p T (s q₀)) = 0 :=
    (TResidue_eq_zero_iff p T _).mpr hmem
  have hRes : TRes p T (TTeichmuller p T (s q₀)) = 0 := by
    change (TResidueIsoFpbar p) (TResidue p T (TTeichmuller p T (s q₀))) = 0
    rw [hres, map_zero]
  rw [TRes_TTeichmuller] at hRes
  exact hsq₀_ne hRes

/-- **Helper E.** Port of `exists_inverse_of_nonzero` (Poonen 3168–3215). -/
private lemma Texists_inverse_of_nonzero
    (A : (TLiftedPAdicHahnSeries p T) ⧸ (TNullSeriesIdeal p T)) (hA : A ≠ 0) :
    ∃ B, A * B = 1 := by
  set s_A : ℚ → Fpbar p := (exists_canonical_T_expansion p T A).choose.val with hs_A_def
  have hspwo : (Function.support s_A).IsPWO := (exists_canonical_T_expansion p T A).choose.prop
  have hsne : (Function.support s_A).Nonempty :=
    Tsupport_nonempty_of_nonzero p T A hA
  set f : TLiftedPAdicHahnSeries p T :=
    TLiftedPAdicHahnSeries.fromCoeff p T s_A hspwo with hf_def
  have hmk_f : (Ideal.Quotient.mk (TNullSeriesIdeal p T)) f = A := by
    have h := (exists_canonical_T_expansion p T A).choose_spec.1
    have h_eq : (Ideal.Quotient.mk (TNullSeriesIdeal p T)) A.out =
        (Ideal.Quotient.mk (TNullSeriesIdeal p T)) f := Quotient.sound h
    exact h_eq.symm.trans (Quotient.out_eq A)
  have h_supp_eq : f.support = Function.support s_A := by
    ext n
    simp only [HahnSeries.mem_support, Function.mem_support]
    change TTeichmuller p T (s_A n) ≠ 0 ↔ s_A n ≠ 0
    refine ⟨fun h h' => h (by rw [h', TTeichmuller_zero]), fun h h' => h ?_⟩
    exact (Tinjective_TTeichmuller p T) (by rw [h', TTeichmuller_zero])
  have hf_ne : f ≠ 0 := by
    intro hf0
    have h_zero_supp : Function.support s_A = ∅ := by
      rw [← h_supp_eq, hf0]
      exact HahnSeries.support_zero
    exact (Set.not_nonempty_iff_eq_empty.mpr h_zero_supp) hsne
  have h_lc_eq : f.leadingCoeff = f.coeff (hspwo.isWF.min hsne) := by
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.order_of_ne hf_ne]
    congr!
  have h_lc_unit : IsUnit f.leadingCoeff := by
    rw [h_lc_eq]
    exact Tcanonical_leading_coeff_isUnit p T hspwo hsne
  have hf_unit : IsUnit f := HahnSeries.isUnit_iff.mpr h_lc_unit
  set u := hf_unit.unit with hu_def
  have hu_val : u.val = f := IsUnit.unit_spec hf_unit
  set g : TLiftedPAdicHahnSeries p T := (u⁻¹).val with hg_def
  have hfg : f * g = 1 := by
    rw [← hu_val]
    exact u.mul_inv
  refine ⟨(Ideal.Quotient.mk (TNullSeriesIdeal p T)) g, ?_⟩
  rw [← hmk_f, ← (Ideal.Quotient.mk _).map_mul, hfg, (Ideal.Quotient.mk _).map_one]

/-- **Lemma 4.6 (3).**  `TNullSeriesIdeal p T` is a maximal ideal, hence the quotient is a
field (the T-scaled p-adic Hahn series field). -/
instance instMaximalTNullSeriesIdeal : (TNullSeriesIdeal p T).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨1, 0, ?_⟩
    intro h
    apply one_notMem_TNullSeriesIdeal p T
    have h1 : (Ideal.Quotient.mk (TNullSeriesIdeal p T)) (1 : TLiftedPAdicHahnSeries p T) =
        (Ideal.Quotient.mk (TNullSeriesIdeal p T)) (0 : TLiftedPAdicHahnSeries p T) := by
      simp [h]
    have := Ideal.Quotient.eq.mp h1
    simpa using this
  · intros a b
    exact mul_comm a b
  · intros a ha
    exact Texists_inverse_of_nonzero p T a ha

/-! ### `TScaledPAdicHahnSeries := 𝕃_[p,T]` -/

/-- The T-scaled p-adic Hahn series field
`𝕃_[p,T] := TLiftedPAdicHahnSeries p T / TNullSeriesIdeal p T`. -/
abbrev TScaledPAdicHahnSeries : Type _ :=
  (TLiftedPAdicHahnSeries p T) ⧸ (TNullSeriesIdeal p T)

@[inherit_doc] notation "𝕃_[" p "," T "]" => TScaledPAdicHahnSeries p T

namespace TScaledPAdicHahnSeries

/-- Coefficient function of an element of `𝕃_[p,T]`: writing `x = ∑ [a_q] p^q` in canonical
form, this is the function `q ↦ a_q : ℚ → 𝔽ᵃ_[p]`. -/
noncomputable def coeff (x : 𝕃_[p,T]) : ℚ → Fpbar p :=
  (exists_canonical_T_expansion p T x).choose.val

/-- Support of an element of `𝕃_[p,T]`. -/
noncomputable def support (x : 𝕃_[p,T]) : Set ℚ :=
  (exists_canonical_T_expansion p T x).choose.val.support

end TScaledPAdicHahnSeries

/-! ### Phase 5 — Projection infrastructure for Lemmas 2.8 and 2.9

These helpers set up the projection layer used in Lemmas 2.8 and 2.9.
The `R₀`-coordinate projection layer (`OQpCUn_basis`, `OQpCUn_basis_apply`,
`OQpCUn_proj`, `OQpCUn_basis_decomp`), the `K₀`-side base-change, and the
index-splitting identities are developed here.

Auxiliary algebra-map identities below (`pInvTQ_pow_T`, `algebraMap_OQpCUn_embd_compat`,
`Lifted_to_TLifted_coeff`) are reused throughout these arguments. -/

/-- Reindexed `R₀`-power-basis of `ℤᶜᵘⁿ_[p,T]`: the basis `{1, π, …, π^(T-1)}` indexed by
`Fin T` (rather than `Fin (TPoly p T).natDegree`). -/
private noncomputable def OQpCUn_basis :
    Module.Basis (Fin T) (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) :=
  ((AdjoinRoot.powerBasis' (TPoly_monic p T)).basis).reindex
    (finCongr (by rw [AdjoinRoot.powerBasis'_dim, TPoly_natDegree]))

private lemma OQpCUn_basis_apply (i : Fin T) :
    OQpCUn_basis p T i = (pInvT p T) ^ (i.val : ℕ) := by
  unfold OQpCUn_basis
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- The `R₀`-coordinate projection on the `i`-th vector of the `R₀`-power-basis of
`ℤᶜᵘⁿ_[p,T]`. -/
private noncomputable def OQpCUn_proj (i : Fin T) :
    ℤᶜᵘⁿ_[p,T] →ₗ[ℤᶜᵘⁿ_[p]] ℤᶜᵘⁿ_[p] :=
  (OQpCUn_basis p T).coord i

/-- Basis decomposition: every `c : ℤᶜᵘⁿ_[p,T]` writes as a `ℤᶜᵘⁿ_[p]`-linear combination of
`{1, π, …, π^(T-1)}`. -/
private lemma OQpCUn_basis_decomp (c : ℤᶜᵘⁿ_[p,T]) :
    c = ∑ i : Fin T, (pInvT p T) ^ (i.val : ℕ) *
        OQpCUn_embd p T (OQpCUn_proj p T i c) := by
  have h := (OQpCUn_basis p T).sum_repr c
  conv_lhs => rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OQpCUn_basis_apply, Algebra.smul_def, mul_comm]
  rfl

/-- The valuation identity `(pInvTQ)^T = algebraMap p`, viewed inside `ℚᶜᵘⁿ_[p,T]`. -/
private lemma pInvTQ_pow_T :
    (pInvTQ p T) ^ T =
      algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
        ((algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T])) ((p : ℕ) : ℤᶜᵘⁿ_[p])) := by
  unfold pInvTQ
  rw [← map_pow, pInvT_pow_T]

omit [NeZero T] in
/-- Coefficient identity for the inclusion: `Lifted_to_TLifted` acts coefficient-wise via
`OQpCUn_embd`. -/
private lemma Lifted_to_TLifted_coeff (x : LiftedPAdicHahnSeries p) (q : ℚ) :
    (Lifted_to_TLifted p T x).coeff q = OQpCUn_embd p T (x.coeff q) := rfl

private noncomputable def QpCUn_basis :
    Module.Basis (Fin T) (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) :=
  (OQpCUn_basis p T).localizationLocalization
    (Rₛ := ℚᶜᵘⁿ_[p]) (Aₛ := ℚᶜᵘⁿ_[p,T]) (S := nonZeroDivisors (ℤᶜᵘⁿ_[p]))

private lemma QpCUn_basis_apply (i : Fin T) :
    QpCUn_basis p T i = (pInvTQ p T) ^ (i.val : ℕ) := by
  unfold QpCUn_basis
  rw [Module.Basis.localizationLocalization_apply, OQpCUn_basis_apply]
  unfold pInvTQ
  rw [map_pow]

/-- `K₀`-coordinate projection on the `i`-th basis vector of the `K₀`-power-basis of `K`. -/
private noncomputable def QpCUn_proj (i : Fin T) :
    ℚᶜᵘⁿ_[p,T] →ₗ[ℚᶜᵘⁿ_[p]] ℚᶜᵘⁿ_[p] :=
  (QpCUn_basis p T).coord i

-- K₀-basis decomposition: every `c : ℚᶜᵘⁿ_[p,T]` writes as a `K₀`-linear combination of
-- `{1, π, …, π^(T-1)}`.
private lemma QpCUn_basis_decomp (c : ℚᶜᵘⁿ_[p,T]) :
    c = ∑ i : Fin T, (pInvTQ p T) ^ (i.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T i c) := by
  have h := (QpCUn_basis p T).sum_repr c
  conv_lhs => rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [QpCUn_basis_apply, Algebra.smul_def, mul_comm]
  rfl

-- Naturality of the `K₀`-projection: on the image of `algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])`,
-- `QpCUn_proj` agrees with `OQpCUn_proj` followed by the localization map of `ℤᶜᵘⁿ_[p]`.
private lemma QpCUn_proj_algebraMap (i : Fin T) (c : ℤᶜᵘⁿ_[p,T]) :
    QpCUn_proj p T i (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) c) =
      algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (OQpCUn_proj p T i c) := by
  unfold QpCUn_proj OQpCUn_proj QpCUn_basis
  exact Module.Basis.localizationLocalization_repr_algebraMap
    (Rₛ := ℚᶜᵘⁿ_[p]) (Aₛ := ℚᶜᵘⁿ_[p,T]) (S := nonZeroDivisors (ℤᶜᵘⁿ_[p])) _ _ _

-- Key extraction lemma: `QpCUn_proj j` extracts the `j`-th coordinate from a `K₀`-linear
-- combination of `{1, π, …, π^(T-1)}`.
private lemma QpCUn_proj_sum (a : Fin T → ℚᶜᵘⁿ_[p]) (j : Fin T) :
    QpCUn_proj p T j (∑ i : Fin T, (pInvTQ p T) ^ (i.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (a i)) = a j := by
  have h : (∑ i : Fin T, (pInvTQ p T) ^ (i.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (a i)) =
      ∑ i : Fin T, (a i) • (QpCUn_basis p T i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [QpCUn_basis_apply, Algebra.smul_def, mul_comm]
  rw [h]
  unfold QpCUn_proj
  rw [map_sum, Finset.sum_eq_single j]
  · rw [LinearMap.map_smul, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp
  · intros i _ hij
    rw [LinearMap.map_smul, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp [hij]
  · intro h0; exact absurd (Finset.mem_univ _) h0

/-- Algebra-map square commutativity: viewing `OQpCUn_embd` followed by `algebraMap` to `K`
agrees with `algebraMap` to `K₀` followed by the field inclusion `K₀ ↪ K`. -/
lemma algebraMap_OQpCUn_embd_compat (a : ℤᶜᵘⁿ_[p]) :
    algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (OQpCUn_embd p T a) =
      algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a) := by
  change algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (algebraMap (ℤᶜᵘⁿ_[p]) (ℤᶜᵘⁿ_[p,T]) a) =
    QpCUn_embd p T (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a)
  unfold QpCUn_embd
  exact (IsFractionRing.lift_algebraMap (g :=
    (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])).comp (OQpCUn_embd p T)) _ a).symm

/-- `pInvTQ` is nonzero — used for `zpow` arithmetic on negative exponents. -/
private lemma pInvTQ_ne_zero : (pInvTQ p T) ≠ 0 := by
  change (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])) (pInvT p T) ≠ 0
  intro h
  have hinj := FaithfulSMul.algebraMap_injective (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
  exact pInvT_ne_zero p T (hinj (by rw [h, map_zero]))

/-- `(pInvTQ)^T` equals the image of `(p : ℚᶜᵘⁿ_[p])` in `K`. -/
private lemma pInvTQ_pow_T_K :
    (pInvTQ p T) ^ T =
      algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) ((p : ℕ) : ℤᶜᵘⁿ_[p])) := by
  rw [pInvTQ_pow_T]
  exact algebraMap_OQpCUn_embd_compat p T _

-- `(pInvTQ)^(T·m)` equals `algebraMap K₀ K` of `(p)^m` for any integer `m`.
private lemma pInvTQ_pow_T_zmul (m : ℤ) :
    (pInvTQ p T) ^ ((T : ℤ) * m) =
      algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (((p : ℕ) : ℚᶜᵘⁿ_[p]) ^ m) := by
  have hp_K0 : ((p : ℕ) : ℚᶜᵘⁿ_[p]) =
      algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) ((p : ℕ) : ℤᶜᵘⁿ_[p]) := by simp
  rw [hp_K0, map_zpow₀, ← pInvTQ_pow_T_K]
  -- Goal: pInvTQ ^ (T * m) = (pInvTQ ^ T) ^ m
  rw [zpow_mul, zpow_natCast]

-- The integer-side valuation identity: for `a : ℤᶜᵘⁿ_[p]`,
-- `v_K(algMap_{K₀→K}(algMap_{R₀→K₀} a)) = (v_{K₀}(algMap_{R₀→K₀} a))^T`.
-- Derived via the DVR canonical decomposition `a = u · p^n` together with
-- `OQpCUn_embd p = pInvT^T` and `pInvTQ^T = algMap p`.
lemma valued_v_algebraMap_K₀_K_int (a : ℤᶜᵘⁿ_[p]) :
    Valued.v (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a)) =
      (Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a))^T := by
  rw [← algebraMap_OQpCUn_embd_compat]
  by_cases ha : a = 0
  · subst ha; simp [map_zero, zero_pow (NeZero.ne T)]
  · obtain ⟨n, h⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha
      (WittVector.irreducible p)
    obtain ⟨u, hu⟩ := h.symm
    rw [← hu]
    rw [map_mul (OQpCUn_embd p T), map_pow (OQpCUn_embd p T)]
    rw [map_mul, map_pow]
    rw [Valuation.map_mul, Valuation.map_pow]
    -- Now also expand the RHS algebraMap (p^n * u)
    rw [show algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (((p : ℕ) : ℤᶜᵘⁿ_[p]) ^ n * u.val) =
          algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (((p : ℕ) : ℤᶜᵘⁿ_[p])) ^ n *
          algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val from by
      rw [map_mul, map_pow]]
    rw [Valuation.map_mul, Valuation.map_pow]
    have h_unit_K : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
        (OQpCUn_embd p T u.val)) = 1 := by
      have hunit : IsUnit (OQpCUn_embd p T u.val) :=
        (OQpCUn_embd p T).isUnit_map u.isUnit
      obtain ⟨v, hv⟩ := hunit
      rw [← hv]
      exact Tvalued_v_algebraMap_unit_one (p := p) (T := T) v
    have h_unit_K0 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) = 1 := by
      have h1 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) ≤ 1 :=
        (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).valuation_le_one u.val
      have h2 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.inv) ≤ 1 :=
        (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).valuation_le_one u.inv
      have h3 : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) *
          Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.inv) = 1 := by
        rw [← Valuation.map_mul, ← map_mul, u.val_inv, map_one, Valuation.map_one]
      have hpos : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) ≠ 0 := by
        intro hz
        rw [hz, zero_mul] at h3
        exact zero_ne_one h3
      exact le_antisymm h1 (by
        rcases (eq_or_lt_of_le h1) with h | h
        · exact le_of_eq h.symm
        · exfalso
          have hi_lt : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.inv) ≤ 1 := h2
          have hprod : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.val) *
              Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u.inv) < 1 :=
            mul_lt_one_of_lt_of_le h hi_lt
          rw [h3] at hprod
          exact lt_irrefl _ hprod)
    rw [h_unit_K, h_unit_K0, mul_one, mul_pow, one_pow, mul_one, ← pow_mul]
    have hLHS : Valued.v (algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          (OQpCUn_embd p T ((p : ℕ) : ℤᶜᵘⁿ_[p]))) =
        ((Multiplicative.ofAdd (-(T : ℤ)) : Multiplicative ℤ) : WithZero _) := by
      rw [show OQpCUn_embd p T ((p : ℕ) : ℤᶜᵘⁿ_[p]) = (pInvT p T) ^ T from
            (pInvT_pow_T p T).symm]
      rw [map_pow]
      rw [show algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (pInvT p T) = pInvTQ p T from rfl]
      rw [show ((pInvTQ p T) ^ T) = ((pInvTQ p T) ^ ((T : ℤ))) by rfl]
      exact valued_v_pInvT_zpow (p := p) (T := T) (T : ℤ)
    have hRHS : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) ((p : ℕ) : ℤᶜᵘⁿ_[p])) =
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
      rw [QpCUn.valued_algebraMap]
      have hirr : Irreducible ((p : ℕ) : ℤᶜᵘⁿ_[p]) := WittVector.irreducible p
      have hpe : (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).asIdeal =
          Ideal.span {((p : ℕ) : ℤᶜᵘⁿ_[p])} := hirr.maximalIdeal_eq
      rw [IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
        (WittVector.p_nonzero p _) hpe]
      rfl
    rw [hLHS, hRHS, ← WithZero.coe_pow, ← WithZero.coe_pow]
    congr 1
    rw [← ofAdd_nsmul, ← ofAdd_nsmul]
    congr 1
    ring_nf
    rw [mul_comm]
/-- The valuation identity for the totally-ramified extension `K₀ ↪ K`:
`v_K(ι̃ z) = (v_{K₀}(z))^T`, encoding the ramification index `T`. -/
lemma valued_v_algebraMap_K₀_K (z : ℚᶜᵘⁿ_[p]) :
    Valued.v (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) z) = (Valued.v z)^T := by
  obtain ⟨a, b, _, hz⟩ := IsFractionRing.div_surjective (A := ℤᶜᵘⁿ_[p]) z
  rw [← hz]
  simp only [map_div₀, div_pow]
  rw [valued_v_algebraMap_K₀_K_int, valued_v_algebraMap_K₀_K_int]

/-- The algebra map `K₀ ↪ K` is `Tendsto`-continuous at `0`. Built from the
ramification-index identity `v_K(ι̃ z) = (v_{K₀}(z))^T` plus the topological-valuation
basis (`Valued.hasBasis_nhds_zero`). -/
private lemma tendsto_algebraMap_K₀_K_zero :
    Filter.Tendsto (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) (nhds 0) (nhds 0) := by
  rw [(Valued.hasBasis_nhds_zero (ℚᶜᵘⁿ_[p,T]) _).tendsto_right_iff]
  intro γ _
  -- v4.31: `γ : (ValueGroup₀ Valued.v)ˣ`; work with its `WithZero (Multiplicative ℤ)` image.
  set c : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc_def
  have hc_ne : c ≠ 0 := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  set γ_m : Multiplicative ℤ := WithZero.unzero hc_ne with hγ_m_def
  set n : ℤ := Multiplicative.toAdd γ_m with hn_def
  set k : ℤ := min (n - 1) (-1) with hk_def
  have hk_neg : k ≤ -1 := min_le_right _ _
  have hk_lt_n : k ≤ n - 1 := min_le_left _ _
  have hT_pos : 0 < (T : ℤ) := by exact_mod_cast Nat.pos_of_neZero T
  have hkT : k * T < n := by
    have h1 : k * T ≤ k * 1 := by
      apply mul_le_mul_of_nonpos_left
      · exact_mod_cast hT_pos
      · linarith
    have h2 : k * 1 = k := mul_one _
    linarith
  rw [Filter.eventually_iff]
  have hsrc : {z : ℚᶜᵘⁿ_[p] | Valued.v z <
      ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero _)} ∈ nhds (0 : ℚᶜᵘⁿ_[p]) :=
    mem_nhds_zero_v_lt WithZero.coe_ne_zero
  refine Filter.mem_of_superset hsrc ?_
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc_def, valued_v_algebraMap_K₀_K]
  have hc_eq : c = ((γ_m : Multiplicative ℤ) : WithZero _) :=
    (WithZero.coe_unzero hc_ne).symm
  have hγm_eq : γ_m = Multiplicative.ofAdd n := rfl
  calc (Valued.v z)^T
      ≤ (((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero _))^T := by
        apply pow_le_pow_left₀ _ (le_of_lt hz)
        exact zero_le (a := Valued.v z)
    _ < c := by
        rw [← WithZero.coe_pow]
        rw [show ((Multiplicative.ofAdd k : Multiplicative ℤ)^T : Multiplicative ℤ) =
              Multiplicative.ofAdd (k * T) from by
          rw [← ofAdd_nsmul]; congr 1; ring]
        rw [hc_eq, hγm_eq, WithZero.coe_lt_coe]
        exact Multiplicative.ofAdd_lt.mpr hkT

/-- Continuity of `algebraMap K₀ → K`. Derived from continuity at `0`
(`tendsto_algebraMap_K₀_K_zero`) plus the additive-group-hom upgrade. -/
private lemma continuous_algebraMap_K₀_K :
    Continuous (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) := by
  have h0 : ContinuousAt (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])) 0 := by
    rw [ContinuousAt, map_zero]
    exact tendsto_algebraMap_K₀_K_zero p T
  exact continuous_of_continuousAt_zero
    (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])).toAddMonoidHom h0

-- Helper 1B: for each j, the j-th K₀-coordinate of the basis decomposition
-- has valuation bounded by `v(c) * ofAdd(j)`. Proof via strict ultrametric: nonzero
-- terms in `c = Σ_i pInvTQ^i · algMap(QpCUn_proj i c)` have pairwise distinct
-- K-valuations (mod T argument), hence by `Valuation.map_sum_eq_of_lt`,
-- `v(c) = max_i v(term_i) ≥ v(term_j)`.

private lemma valued_v_QpCUn_proj_term_le (c : ℚᶜᵘⁿ_[p,T]) (j : Fin T) :
    Valued.v ((pInvTQ p T) ^ (j.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T j c)) ≤ Valued.v c := by
  -- Notation: term_i := pInvTQ^i * algMap (QpCUn_proj i c).
  let term : Fin T → ℚᶜᵘⁿ_[p,T] := fun i =>
    (pInvTQ p T) ^ (i.val : ℕ) *
      algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T i c)
  change Valued.v (term j) ≤ Valued.v c
  have h_decomp : c = ∑ i : Fin T, term i := QpCUn_basis_decomp p T c
  -- If term j = 0, the bound is trivial.
  by_cases hj : term j = 0
  · rw [hj, Valuation.map_zero]; exact zero_le (a := Valued.v c)
  classical
  let supp : Finset (Fin T) := (Finset.univ.filter (fun i => term i ≠ 0))
  have hj_supp : j ∈ supp := by simp [supp, hj]
  have h_mem_supp : ∀ {i}, i ∈ supp ↔ term i ≠ 0 := by
    intro i; simp [supp]
  -- Pairwise distinct valuations on supp, via the mod-T argument.
  have h_distinct : ∀ i₁ ∈ supp, ∀ i₂ ∈ supp, i₁ ≠ i₂ →
      Valued.v (term i₁) ≠ Valued.v (term i₂) := by
    intro i₁ hi₁ i₂ hi₂ h_ne
    have hterm₁_ne : term i₁ ≠ 0 := h_mem_supp.mp hi₁
    have hterm₂_ne : term i₂ ≠ 0 := h_mem_supp.mp hi₂
    -- term i = pInvTQ^i * algMap (QpCUn_proj i c)
    have hpInvTQ_ne : (pInvTQ p T) ≠ 0 := pInvTQ_ne_zero p T
    have hpInvTQ_pow_ne : ∀ k : ℕ, ((pInvTQ p T) ^ k) ≠ 0 := fun k =>
      pow_ne_zero k hpInvTQ_ne
    have h_a₁_ne : QpCUn_proj p T i₁ c ≠ 0 := by
      intro h0
      apply hterm₁_ne
      change (pInvTQ p T) ^ (i₁.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T i₁ c) = 0
      rw [h0, map_zero, mul_zero]
    have h_a₂_ne : QpCUn_proj p T i₂ c ≠ 0 := by
      intro h0
      apply hterm₂_ne
      change (pInvTQ p T) ^ (i₂.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T i₂ c) = 0
      rw [h0, map_zero, mul_zero]
    -- v(QpCUn_proj i_k c) ≠ 0
    have h_v_a_ne₁ : Valued.v (QpCUn_proj p T i₁ c) ≠ 0 := by
      intro h0
      apply h_a₁_ne
      exact (Valuation.zero_iff _).1 h0
    have h_v_a_ne₂ : Valued.v (QpCUn_proj p T i₂ c) ≠ 0 := by
      intro h0
      apply h_a₂_ne
      exact (Valuation.zero_iff _).1 h0
    -- Express valuations via Helper 1A.
    have h_alg_eq₁ : Valued.v (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (QpCUn_proj p T i₁ c)) = (Valued.v (QpCUn_proj p T i₁ c))^T :=
      valued_v_algebraMap_K₀_K p T _
    have h_alg_eq₂ : Valued.v (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (QpCUn_proj p T i₂ c)) = (Valued.v (QpCUn_proj p T i₂ c))^T :=
      valued_v_algebraMap_K₀_K p T _
    have h_pInvTQ₁ : Valued.v ((pInvTQ p T) ^ (i₁.val : ℕ)) =
        ((Multiplicative.ofAdd (-(i₁.val : ℤ)) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
      rw [show ((pInvTQ p T) ^ (i₁.val : ℕ)) = ((pInvTQ p T) ^ ((i₁.val : ℤ))) by rfl]
      exact valued_v_pInvT_zpow (p := p) (T := T) (i₁.val : ℤ)
    have h_pInvTQ₂ : Valued.v ((pInvTQ p T) ^ (i₂.val : ℕ)) =
        ((Multiplicative.ofAdd (-(i₂.val : ℤ)) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
      rw [show ((pInvTQ p T) ^ (i₂.val : ℕ)) = ((pInvTQ p T) ^ ((i₂.val : ℤ))) by rfl]
      exact valued_v_pInvT_zpow (p := p) (T := T) (i₂.val : ℤ)
    intro h_eq
    -- Unfold term and apply valuation calculations.
    have h_v_term₁ : Valued.v (term i₁) =
        ((Multiplicative.ofAdd (-(i₁.val : ℤ)) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) * (Valued.v (QpCUn_proj p T i₁ c))^T := by
      change Valued.v ((pInvTQ p T) ^ (i₁.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T i₁ c)) = _
      rw [Valuation.map_mul, h_pInvTQ₁, h_alg_eq₁]
    have h_v_term₂ : Valued.v (term i₂) =
        ((Multiplicative.ofAdd (-(i₂.val : ℤ)) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) * (Valued.v (QpCUn_proj p T i₂ c))^T := by
      change Valued.v ((pInvTQ p T) ^ (i₂.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T i₂ c)) = _
      rw [Valuation.map_mul, h_pInvTQ₂, h_alg_eq₂]
    rw [h_v_term₁, h_v_term₂] at h_eq
    set m₁ : ℤ := Multiplicative.toAdd (WithZero.unzero h_v_a_ne₁) with hm₁_def
    set m₂ : ℤ := Multiplicative.toAdd (WithZero.unzero h_v_a_ne₂) with hm₂_def
    have hva₁ : Valued.v (QpCUn_proj p T i₁ c) =
        ((Multiplicative.ofAdd m₁ : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
      rw [hm₁_def]; simp [WithZero.coe_unzero h_v_a_ne₁]
    have hva₂ : Valued.v (QpCUn_proj p T i₂ c) =
        ((Multiplicative.ofAdd m₂ : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
      rw [hm₂_def]; simp [WithZero.coe_unzero h_v_a_ne₂]
    rw [hva₁, hva₂] at h_eq
    rw [← WithZero.coe_pow, ← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_mul,
      WithZero.coe_inj, ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_add,
      Multiplicative.ofAdd.injective.eq_iff] at h_eq
    -- h_eq : -i₁ + T • m₁ = -i₂ + T • m₂
    have h_sub : (T : ℤ) * m₁ - (T : ℤ) * m₂ = (i₁.val : ℤ) - (i₂.val : ℤ) := by
      have h_smul₁ : (T : ℕ) • m₁ = (T : ℤ) * m₁ := by simp
      have h_smul₂ : (T : ℕ) • m₂ = (T : ℤ) * m₂ := by simp
      linarith [h_eq, h_smul₁, h_smul₂]
    have hT_pos : (0 : ℤ) < T := by exact_mod_cast Nat.pos_of_neZero T
    have hT_dvd : (T : ℤ) ∣ (i₁.val : ℤ) - (i₂.val : ℤ) := by
      rw [← h_sub]
      refine ⟨m₁ - m₂, ?_⟩
      ring
    have h_lt₁ : (i₁.val : ℤ) < T := by exact_mod_cast i₁.isLt
    have h_lt₂ : (i₂.val : ℤ) < T := by exact_mod_cast i₂.isLt
    have h_nn₁ : (0 : ℤ) ≤ i₁.val := Int.natCast_nonneg _
    have h_nn₂ : (0 : ℤ) ≤ i₂.val := Int.natCast_nonneg _
    have h_val_eq : i₁.val = i₂.val := by
      obtain ⟨q, hq⟩ := hT_dvd
      have h_q_zero : q = 0 := by nlinarith [sq_nonneg q]
      have : (i₁.val : ℤ) = (i₂.val : ℤ) := by
        rw [h_q_zero, mul_zero] at hq; omega
      exact_mod_cast this
    exact h_ne (Fin.ext h_val_eq)
  -- Apply strict ultrametric: identify the term with maximum valuation, restricted to supp.
  have h_supp_ne : supp.Nonempty := ⟨j, hj_supp⟩
  obtain ⟨k, hk_supp, hk_max⟩ := supp.exists_max_image (fun i => Valued.v (term i)) h_supp_ne
  have h_lt_max : ∀ i ∈ supp, i ≠ k → Valued.v (term i) < Valued.v (term k) := by
    intro i hi hik
    rcases lt_or_eq_of_le (hk_max i hi) with hlt | heq
    · exact hlt
    · exact absurd heq (h_distinct i hi k hk_supp hik)
  have h_decomp_supp : ∑ i : Fin T, term i = ∑ i ∈ supp, term i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi_notin
    by_contra h_ne_zero
    apply hi_notin
    exact h_mem_supp.mpr h_ne_zero
  have h_v_c : Valued.v c = Valued.v (term k) := by
    rw [h_decomp, h_decomp_supp]
    refine Valuation.map_sum_eq_of_lt _ hk_supp ?_
    intro i hi_diff
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi_diff
    exact h_lt_max i hi_diff.1 hi_diff.2
  rw [h_v_c]
  exact hk_max j hj_supp

-- Helper 1B: tendsto-at-zero of `QpCUn_proj j`. Built from
-- `valued_v_QpCUn_proj_term_le` plus Helper 1A `valued_v_algebraMap_K₀_K` (the
-- ramification identity `v(algMap z) = v(z)^T`).
private lemma tendsto_QpCUn_proj_zero (j : Fin T) :
    Filter.Tendsto (QpCUn_proj p T j) (nhds (0 : ℚᶜᵘⁿ_[p,T])) (nhds (0 : ℚᶜᵘⁿ_[p])) := by
  rw [(Valued.hasBasis_nhds_zero (ℚᶜᵘⁿ_[p]) _).tendsto_right_iff]
  intro γ' _
  -- v4.31: `γ' : (ValueGroup₀ Valued.v)ˣ` on the `K₀` side; use its `WithZero` image.
  set c' : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ'.1 with hc'_def
  have hc'_ne : c' ≠ 0 := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ'
  set γ'_m : Multiplicative ℤ := WithZero.unzero hc'_ne with hγ'_m_def
  set N : ℤ := Multiplicative.toAdd γ'_m with hN_def
  -- Choose k = N * T - j.val - 1 (so k + j.val + 1 ≤ N * T, i.e., k + j < N*T).
  set k : ℤ := N * T - (j.val : ℤ) - 1 with hk_def
  have hT_pos : (0 : ℤ) < T := by exact_mod_cast Nat.pos_of_neZero T
  -- Source ball on `K` side, with cutoff `ofAdd k`.
  rw [Filter.eventually_iff]
  have hsrc : {c : ℚᶜᵘⁿ_[p,T] | Valued.v c <
      ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero _)} ∈ nhds (0 : ℚᶜᵘⁿ_[p,T]) :=
    Tmem_nhds_zero_v_lt p T WithZero.coe_ne_zero
  refine Filter.mem_of_superset hsrc ?_
  intro c hc
  simp only [Set.mem_ofPred_eq] at hc ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc'_def]
  -- We have hc : v(c) < ofAdd k.
  -- Goal: v(QpCUn_proj j c) < c' = ofAdd N.
  have h_term_le : Valued.v ((pInvTQ p T) ^ (j.val : ℕ) *
      algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) (QpCUn_proj p T j c)) ≤ Valued.v c :=
    valued_v_QpCUn_proj_term_le p T c j
  -- Compute v(pInvTQ^j) = ofAdd(-j).
  have h_pInvTQ_j : Valued.v ((pInvTQ p T) ^ (j.val : ℕ)) =
      ((Multiplicative.ofAdd (-(j.val : ℤ)) : Multiplicative ℤ) : WithZero _) := by
    rw [show ((pInvTQ p T) ^ (j.val : ℕ)) = ((pInvTQ p T) ^ ((j.val : ℤ))) by rfl]
    exact valued_v_pInvT_zpow (p := p) (T := T) (j.val : ℤ)
  rw [Valuation.map_mul, h_pInvTQ_j, valued_v_algebraMap_K₀_K] at h_term_le
  -- h_term_le : ofAdd(-j) * v(QpCUn_proj j c)^T ≤ v(c) < ofAdd k.
  have h_combined :
      ((Multiplicative.ofAdd (-(j.val : ℤ)) : Multiplicative ℤ) : WithZero _) *
        (Valued.v (QpCUn_proj p T j c))^T <
      ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero _) :=
    lt_of_le_of_lt h_term_le hc
  -- Multiply both sides by ofAdd j: v(QpCUn_proj j c)^T < ofAdd(k + j).
  have h_pow_lt : (Valued.v (QpCUn_proj p T j c))^T <
      ((Multiplicative.ofAdd (k + (j.val : ℤ)) : Multiplicative ℤ) : WithZero _) := by
    have hofAdd_j_pos : (0 : WithZero (Multiplicative ℤ)) <
        ((Multiplicative.ofAdd ((j.val : ℤ)) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
      exact WithZero.zero_lt_coe _
    have h_mul := strictMono_mul_left_of_pos hofAdd_j_pos h_combined
    -- Simplify LHS: ofAdd(j) * (ofAdd(-j) * v^T) = v^T.
    have h_simpL : ((Multiplicative.ofAdd ((j.val : ℤ)) : Multiplicative ℤ) : WithZero _) *
        (((Multiplicative.ofAdd (-(j.val : ℤ)) : Multiplicative ℤ) : WithZero _) *
          (Valued.v (QpCUn_proj p T j c))^T) =
        (Valued.v (QpCUn_proj p T j c))^T := by
      rw [← mul_assoc]
      rw [← WithZero.coe_mul, ← ofAdd_add]
      simp
    -- Simplify RHS: ofAdd(j) * ofAdd(k) = ofAdd(j + k).
    have h_simpR : ((Multiplicative.ofAdd ((j.val : ℤ)) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) *
        ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
        ((Multiplicative.ofAdd (k + (j.val : ℤ)) : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.coe_mul, ← ofAdd_add]
      congr 1
      rw [add_comm]
    simp only [] at h_mul
    rw [h_simpL, h_simpR] at h_mul
    exact h_mul
  -- Now v^T < ofAdd(k + j) ≤ ofAdd(N*T - 1) < ofAdd(N*T) = (ofAdd N)^T = γ'^T.
  have h_kj_lt : k + (j.val : ℤ) < N * T := by
    rw [hk_def]; linarith
  have h_pow_lt_NT : (Valued.v (QpCUn_proj p T j c))^T <
      ((Multiplicative.ofAdd (N * T) : Multiplicative ℤ) : WithZero _) := by
    apply lt_of_lt_of_le h_pow_lt
    rw [WithZero.coe_le_coe, Multiplicative.ofAdd_le]
    linarith
  -- Convert to v < ofAdd N.
  have h_RHS_eq : ((Multiplicative.ofAdd (N * T) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) =
      (((Multiplicative.ofAdd N : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)))^T := by
    rw [← WithZero.coe_pow, ← ofAdd_nsmul]
    congr 1
    simp only [Int.nsmul_eq_mul, EmbeddingLike.apply_eq_iff_eq]
    ring
  rw [h_RHS_eq] at h_pow_lt_NT
  have h_rhs_pos : (0 : WithZero (Multiplicative ℤ)) <
      ((Multiplicative.ofAdd N : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    WithZero.zero_lt_coe _
  have h_lt : Valued.v (QpCUn_proj p T j c) <
      ((Multiplicative.ofAdd N : Multiplicative ℤ) : WithZero _) := by
    have hT_ne : T ≠ 0 := NeZero.ne T
    by_contra h_not_lt
    push Not at h_not_lt
    have h_pow_le : (((Multiplicative.ofAdd N : Multiplicative ℤ) : WithZero _))^T ≤
        (Valued.v (QpCUn_proj p T j c))^T :=
      pow_le_pow_left₀ (le_of_lt h_rhs_pos) h_not_lt T
    exact absurd (lt_of_lt_of_le h_pow_lt_NT h_pow_le) (lt_irrefl _)
  -- Convert c' to ofAdd N.
  have hc'_eq : c' = ((Multiplicative.ofAdd N : Multiplicative ℤ) : WithZero _) := by
    rw [hN_def, hγ'_m_def]
    simp [WithZero.coe_unzero hc'_ne]
  rw [hc'_eq]
  exact h_lt

-- Helper 1B: continuity of `QpCUn_proj j`. Derived from the
-- tendsto-at-zero result above plus the additive-group-hom upgrade.
private lemma continuous_QpCUn_proj (j : Fin T) :
    Continuous (QpCUn_proj p T j) := by
  have h0 : ContinuousAt (QpCUn_proj p T j) 0 := by
    rw [ContinuousAt, map_zero]
    exact tendsto_QpCUn_proj_zero p T j
  exact continuous_of_continuousAt_zero (QpCUn_proj p T j).toAddMonoidHom h0

-- Helper 1C: index-splitting identity (Sub-lemma 4.8.1).
-- For x : LiftedPAdic, g : ℚ, M : ℕ, the T-side partial sum at base g equals
-- the sum over r : Fin T of pInvTQ^r times algebraMap_{K₀→K} of the K₀-side
-- partial sum at base g + r/T. Reindex via n = T*m + r.
private lemma TLifted_partial_sum_split
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (M : ℕ) :
    (∑ n : Set.Finite.toFinset (TfiniteBelow p T (Lifted_to_TLifted p T x) g M),
        (pInvTQ p T) ^ (n.val : ℤ) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            ((Lifted_to_TLifted p T x).coeff (g + (n.val : ℚ) / T)))
    =
    ∑ r : Fin T, (pInvTQ p T) ^ (r.val : ℕ) *
      algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (∑ m : Set.Finite.toFinset (finiteBelow x (g + (r.val : ℚ) / T) M),
            ((p : ℕ) : ℚᶜᵘⁿ_[p]) ^ (m.val : ℤ) *
              algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p])
                (x.coeff ((g + (r.val : ℚ) / T) + (m.val : ℚ)))) := by
  classical
  have hT_ne : (T : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne T
  have hT_pos : (0 : ℤ) < T := by exact_mod_cast Nat.pos_of_neZero T
  have hT_pos_q : (0 : ℚ) < T := by exact_mod_cast Nat.pos_of_neZero T
  have hpInvTQ_ne : (pInvTQ p T) ≠ 0 := pInvTQ_ne_zero p T
  -- Convert sums-over-attach to sums-over-finset.
  rw [Finset.univ_eq_attach, Finset.sum_attach
    (Set.Finite.toFinset (TfiniteBelow p T (Lifted_to_TLifted p T x) g M))
    (fun n => (pInvTQ p T) ^ (n : ℤ) *
      algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
        ((Lifted_to_TLifted p T x).coeff (g + (n : ℚ) / T)))]
  -- Push algebraMap and reindex on RHS to a doubled sum on K side.
  have h_RHS : ∀ r : Fin T,
      (pInvTQ p T) ^ (r.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
          (∑ m : Set.Finite.toFinset (finiteBelow x (g + (r.val : ℚ) / T) M),
            ((p : ℕ) : ℚᶜᵘⁿ_[p]) ^ (m.val : ℤ) *
              algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p])
                (x.coeff ((g + (r.val : ℚ) / T) + (m.val : ℚ)))) =
      ∑ m ∈ Set.Finite.toFinset (finiteBelow x (g + (r.val : ℚ) / T) M),
        (pInvTQ p T) ^ ((T : ℤ) * (m : ℤ) + (r.val : ℤ)) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            ((Lifted_to_TLifted p T x).coeff
              (g + (((T : ℤ) * (m : ℤ) + (r.val : ℤ) : ℤ) : ℚ) / T)) := by
    intro r
    rw [Finset.univ_eq_attach, Finset.sum_attach
      (Set.Finite.toFinset (finiteBelow x (g + (r.val : ℚ) / T) M))
      (fun m => ((p : ℕ) : ℚᶜᵘⁿ_[p]) ^ (m : ℤ) *
        algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (x.coeff ((g + (r.val : ℚ) / T) + (m : ℚ))))]
    rw [map_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    -- Single-term identity:
    -- pInvTQ^r * algMap (p^m * algMap (x.coeff h)) where h = g + r/T + m
    -- = pInvTQ^(T*m+r) * algMap_{R→K}(OQpCUn_embd (x.coeff h))
    -- = pInvTQ^(T*m+r) * algMap_{R→K}((ι x).coeff (g + (T*m+r)/T))
    rw [map_mul, map_zpow₀]
    -- p in K₀ as algMap from R₀
    have hp_K0 : ((p : ℕ) : ℚᶜᵘⁿ_[p]) =
        algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) ((p : ℕ) : ℤᶜᵘⁿ_[p]) := by simp
    -- algMap_{K₀→K} (algMap_{R₀→K₀} z) = algMap_{R→K} (OQpCUn_embd z)
    have h_compat : algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (x.coeff ((g + (r.val : ℚ) / T) + (m : ℚ)))) =
        algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
          (OQpCUn_embd p T (x.coeff ((g + (r.val : ℚ) / T) + (m : ℚ)))) :=
      (algebraMap_OQpCUn_embd_compat p T _).symm
    rw [h_compat]
    -- Compute index identity g + (T*m+r)/T = (g + r/T) + m
    have h_idx : g + (((T : ℤ) * (m : ℤ) + (r.val : ℤ) : ℤ) : ℚ) / T =
        (g + (r.val : ℚ) / T) + (m : ℚ) := by
      push_cast; field_simp; ring
    rw [show (Lifted_to_TLifted p T x).coeff
        (g + (((T : ℤ) * (m : ℤ) + (r.val : ℤ) : ℤ) : ℚ) / T) =
        OQpCUn_embd p T (x.coeff ((g + (r.val : ℚ) / T) + (m : ℚ))) from by
      rw [h_idx]; rfl]
    -- Now compute pInvTQ^r * algMap p^m * algMap_{R→K}(...)
    -- = pInvTQ^r * pInvTQ^(T*m) * algMap_{R→K}(...)
    have h_alg_p_pow : (algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) ((p : ℕ) : ℤᶜᵘⁿ_[p])))^(m : ℤ) =
        (pInvTQ p T) ^ ((T : ℤ) * (m : ℤ)) := by
      rw [← hp_K0, ← map_zpow₀, ← pInvTQ_pow_T_zmul]
    rw [hp_K0]
    rw [h_alg_p_pow]
    -- Combine: pInvTQ^r * pInvTQ^(T*m) = pInvTQ^(T*m + r)
    rw [← mul_assoc]
    rw [show ((pInvTQ p T) ^ (r.val : ℕ)) = ((pInvTQ p T) ^ ((r.val : ℤ))) by rfl]
    rw [show ((pInvTQ p T) ^ ((r.val : ℤ)) * (pInvTQ p T) ^ ((T : ℤ) * (m : ℤ))) =
        (pInvTQ p T) ^ (((T : ℤ) * (m : ℤ)) + (r.val : ℤ)) from by
      rw [← zpow_add₀ hpInvTQ_ne]; congr 1; ring]
  simp_rw [h_RHS]
  -- Now both sides are sums of the same kind of terms, indexed differently.
  -- Apply Finset.sum_sigma to combine the RHS into a sum over a sigma type,
  -- then use Finset.sum_bij with the bijection n ↔ (r, m) where n = T*m + r.val.
  rw [← Finset.sum_sigma Finset.univ
      (fun r : Fin T => Set.Finite.toFinset (finiteBelow x (g + (r.val : ℚ) / T) M))
      (fun rm : Σ _ : Fin T, ℤ =>
        (pInvTQ p T) ^ ((T : ℤ) * rm.2 + (rm.1.val : ℤ)) *
          algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
            ((Lifted_to_TLifted p T x).coeff
              (g + (((T : ℤ) * rm.2 + (rm.1.val : ℤ) : ℤ) : ℚ) / T)))]
  -- Apply Finset.sum_bij with the bijection n ↔ ⟨n % T, n / T⟩.
  classical
  have hT_natpos : (0 : ℕ) < T := Nat.pos_of_neZero T
  refine Finset.sum_bij
      (fun n (_ : n ∈ Set.Finite.toFinset (TfiniteBelow p T (Lifted_to_TLifted p T x) g M)) =>
        (⟨⟨(n.emod (T : ℤ)).toNat, ?_⟩, n.ediv (T : ℤ)⟩ : Σ _ : Fin T, ℤ)) ?_ ?_ ?_ ?_
  · -- (n.emod T).toNat < T
    have hmod_nn : 0 ≤ n.emod (T : ℤ) := Int.emod_nonneg n hT_ne
    have hmod_lt : n.emod (T : ℤ) < (T : ℤ) := Int.emod_lt_of_pos n hT_pos
    omega
  · -- membership: ⟨n%T, n/T⟩ ∈ univ.sigma (...)
    intro n hn
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and]
    rw [Set.Finite.mem_toFinset] at hn ⊢
    have hmod_nn : 0 ≤ n.emod (T : ℤ) := Int.emod_nonneg n hT_ne
    have hmod_lt : n.emod (T : ℤ) < (T : ℤ) := Int.emod_lt_of_pos n hT_pos
    have htoNat : ((n.emod (T : ℤ)).toNat : ℤ) = n.emod (T : ℤ) := Int.toNat_of_nonneg hmod_nn
    have hsplit_int : (T : ℤ) * n.ediv (T : ℤ) + n.emod (T : ℤ) = n := Int.mul_ediv_add_emod n T
    have hn_split : ((n : ℚ) / T) =
        (((n.emod (T : ℤ)).toNat : ℚ) / T + (n.ediv (T : ℤ) : ℚ)) := by
      have hQ : (n : ℚ) =
          ((T : ℤ) * n.ediv (T : ℤ) + n.emod (T : ℤ) : ℤ) := by exact_mod_cast hsplit_int.symm
      rw [hQ]; push_cast
      have hcast : ((n.emod (T : ℤ) : ℤ) : ℚ) = ((n.emod (T : ℤ)).toNat : ℚ) := by
        have := htoNat
        exact_mod_cast this.symm
      rw [hcast]
      field_simp; ring
    have hcoeff_eq : (Lifted_to_TLifted p T x).coeff (g + (n : ℚ) / T) = OQpCUn_embd p T
      (x.coeff (g + ((n.emod (T : ℤ)).toNat : ℚ) / T + (n.ediv (T : ℤ) : ℚ))) := by
      rw [show g + (n : ℚ) / T =
          g + ((n.emod (T : ℤ)).toNat : ℚ) / T + (n.ediv (T : ℤ) : ℚ) from by
        rw [hn_split]; ring]
      rfl
    refine ⟨?_, ?_⟩
    · have h1 := hn.1
      rw [hn_split] at h1; linarith
    · intro h0
      apply hn.2
      rw [hcoeff_eq, h0, map_zero]
  · -- injectivity
    intro n₁ hn₁ n₂ hn₂ hij
    simp only [Sigma.mk.injEq, Fin.mk.injEq, heq_eq_eq] at hij
    obtain ⟨hmod, hdiv⟩ := hij
    have hmod_nn₁ : 0 ≤ n₁.emod (T : ℤ) := Int.emod_nonneg n₁ hT_ne
    have hmod_nn₂ : 0 ≤ n₂.emod (T : ℤ) := Int.emod_nonneg n₂ hT_ne
    have h_emod : n₁.emod (T : ℤ) = n₂.emod (T : ℤ) := by
      have h1 : ((n₁.emod (T : ℤ)).toNat : ℤ) = n₁.emod (T : ℤ) := Int.toNat_of_nonneg hmod_nn₁
      have h2 : ((n₂.emod (T : ℤ)).toNat : ℤ) = n₂.emod (T : ℤ) := Int.toNat_of_nonneg hmod_nn₂
      have hcast : ((n₁.emod (T : ℤ)).toNat : ℤ) = ((n₂.emod (T : ℤ)).toNat : ℤ) := by
        exact_mod_cast hmod
      rw [h1, h2] at hcast; exact hcast
    have h_split₁ : (T : ℤ) * n₁.ediv (T : ℤ) + n₁.emod (T : ℤ) = n₁ := Int.mul_ediv_add_emod _ _
    have h_split₂ : (T : ℤ) * n₂.ediv (T : ℤ) + n₂.emod (T : ℤ) = n₂ := Int.mul_ediv_add_emod _ _
    rw [← h_split₁, ← h_split₂, hdiv, h_emod]
  · -- surjectivity
    rintro ⟨r, m⟩ hrm
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hrm
    rw [Set.Finite.mem_toFinset] at hrm
    refine ⟨(T : ℤ) * m + (r.val : ℤ), ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]
      have hidx : g + (((T : ℤ) * m + (r.val : ℤ) : ℤ) : ℚ) / T =
          g + (r.val : ℚ) / T + (m : ℚ) := by
        push_cast; field_simp; ring
      refine ⟨?_, ?_⟩
      · rw [hidx]; exact hrm.1
      · rw [hidx]
        intro h0
        apply hrm.2
        have h1 : OQpCUn_embd p T (x.coeff (g + (r.val : ℚ) / T + (m : ℚ))) = 0 := h0
        have : OQpCUn_embd p T (x.coeff (g + (r.val : ℚ) / T + (m : ℚ))) =
          OQpCUn_embd p T 0 := by rw [h1, map_zero]
        exact (OQpCUn_embd_injective p T) this
    · -- bijection function value matches
      have hr_lt : (r.val : ℤ) < T := by exact_mod_cast r.isLt
      have hr_nn : (0 : ℤ) ≤ r.val := Int.natCast_nonneg _
      have h_emod : ((T : ℤ) * m + (r.val : ℤ)).emod (T : ℤ) = (r.val : ℤ) := by
        have : ((T : ℤ) * m + (r.val : ℤ)) % (T : ℤ) = (r.val : ℤ) := by
          have heq : (T : ℤ) * m + (r.val : ℤ) = (r.val : ℤ) + m * (T : ℤ) := by ring
          rw [heq, Int.add_mul_emod_self_right]
          exact Int.emod_eq_of_lt hr_nn hr_lt
        exact this
      have h_ediv : ((T : ℤ) * m + (r.val : ℤ)).ediv (T : ℤ) = m := by
        have : ((T : ℤ) * m + (r.val : ℤ)) / (T : ℤ) = m := by
          have heq : (T : ℤ) * m + (r.val : ℤ) = (r.val : ℤ) + m * (T : ℤ) := by ring
          rw [heq, Int.add_mul_ediv_right _ _ hT_ne]
          rw [show (r.val : ℤ) / (T : ℤ) = 0 from Int.ediv_eq_zero_of_lt hr_nn hr_lt, zero_add]
        exact this
      apply Sigma.ext
      · simp only [h_emod]
        apply Fin.ext
        simp only
        exact_mod_cast Int.toNat_of_nonneg hr_nn
      · simp only [h_ediv, heq_eq_eq]
  · -- function values agree
    intro n hn
    rw [Set.Finite.mem_toFinset] at hn
    have hT_ne_q : (T : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne T
    have hmod_nn : 0 ≤ n.emod (T : ℤ) := Int.emod_nonneg n hT_ne
    have htoNat : ((n.emod (T : ℤ)).toNat : ℤ) = n.emod (T : ℤ) := Int.toNat_of_nonneg hmod_nn
    have hsplit_int : (T : ℤ) * n.ediv (T : ℤ) + ((n.emod (T : ℤ)).toNat : ℤ) = n := by
      rw [htoNat]; exact Int.mul_ediv_add_emod n T
    have h_idx_eq :
        (g + ((((n.emod (T : ℤ)).toNat : ℤ) : ℚ) / T + (n.ediv (T : ℤ) : ℚ))) =
        (g + (n : ℚ) / T) := by
      have hQ : (n : ℚ) = ((T : ℤ) * n.ediv (T : ℤ) + ((n.emod (T : ℤ)).toNat : ℤ) : ℤ) := by
        exact_mod_cast hsplit_int.symm
      rw [hQ]; push_cast; field_simp; ring
    -- Show: pInvTQ^(T*(n/T) + (n%T).toNat) * algMap ((ι x).coeff (g + (T*(n/T) + (n%T).toNat)/T))
    --     = pInvTQ^n * algMap ((ι x).coeff (g + n/T))
    have h_exp_eq : (T : ℤ) * n.ediv (T : ℤ) + ((n.emod (T : ℤ)).toNat : ℤ) = n := hsplit_int
    rw [h_exp_eq]

-- Opaque abbreviations for the K₀-side and K-side partial sums. Wrapping
-- the sums in `noncomputable def`s prevents Lean from re-elaborating the
-- `Set.Finite.toFinset`-based index sets on every defeq check during the long
-- `Tendsto.comp` / `tendsto_finsetSum` chains used in Lemma 4.8 below.

/-- K₀-side partial sum (Poonen `S_M(h; x)`).  Definitionally matches the body of
`IsNullSeries x` at base `h`, step `M`. -/
private noncomputable def S_partial
    (x : LiftedPAdicHahnSeries p) (h : ℚ) (M : ℕ) : ℚᶜᵘⁿ_[p] :=
  ∑ n : Set.Finite.toFinset (finiteBelow x h M),
    ((p : ℕ) : ℚᶜᵘⁿ_[p]) ^ (n.val : ℤ) *
      algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) (x.coeff (h + n.val))

/-- K-side partial sum (Poonen `T_M(g; ι x)`).  Definitionally matches the body of
`IsTNullSeries (Lifted_to_TLifted p T x)` at base `g`, step `M`. -/
private noncomputable def T_partial
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (M : ℕ) : ℚᶜᵘⁿ_[p,T] :=
  ∑ n : Set.Finite.toFinset (TfiniteBelow p T (Lifted_to_TLifted p T x) g M),
    (pInvTQ p T) ^ (n.val : ℤ) *
      algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
        ((Lifted_to_TLifted p T x).coeff (g + (n.val : ℚ) / T))

/-- Sub-lemma 4.8.1 packaged through the opaque names: the K-side partial sum
splits as `T` projections of the K₀-side partial sum at shifted bases. -/
private lemma T_partial_eq_proj_sum
    (x : LiftedPAdicHahnSeries p) (g : ℚ) (M : ℕ) :
    T_partial p T x g M
      = ∑ r : Fin T, (pInvTQ p T) ^ (r.val : ℕ) *
          algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
            (S_partial p x (g + (r.val : ℚ) / T) M) := by
  unfold T_partial S_partial
  exact TLifted_partial_sum_split (p := p) (T := T) x g M

-- (⇐) of Lemma 4.8: K₀-side null hypothesis transports to K-side null.
open Topology Filter in
private lemma tendsto_T_partial_of_null
    (x : LiftedPAdicHahnSeries p)
    (hN : ∀ h, Filter.Tendsto (fun M => S_partial p x h M) Filter.atTop (𝓝 0))
    (g : ℚ) :
    Filter.Tendsto (fun M => T_partial p T x g M) Filter.atTop (𝓝 0) := by
  have hf : (fun M => T_partial p T x g M) =
      (fun M => ∑ r : Fin T, (pInvTQ p T) ^ (r.val : ℕ) *
        algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
          (S_partial p x (g + (r.val : ℚ) / T) M)) := by
    funext M; exact T_partial_eq_proj_sum p T x g M
  rw [hf]
  have hzero : (0 : ℚᶜᵘⁿ_[p,T]) = ∑ _r : Fin T, (0 : ℚᶜᵘⁿ_[p,T]) := by simp
  rw [hzero]
  refine tendsto_finsetSum _ ?_
  intro r _
  -- For each r: π^r · ι̃(S_partial p x (g + r/T) M) → π^r · 0 = 0.
  have h_inner : Filter.Tendsto
      (fun M => algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T])
        (S_partial p x (g + (r.val : ℚ) / T) M))
      Filter.atTop (𝓝 0) := by
    have hcts := (continuous_algebraMap_K₀_K p T).tendsto 0
    have h0 : (0 : ℚᶜᵘⁿ_[p,T])
        = algebraMap (ℚᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p,T]) 0 := (map_zero _).symm
    rw [h0]
    exact hcts.comp (hN (g + (r.val : ℚ) / T))
  have h_mul := h_inner.const_mul ((pInvTQ p T) ^ (r.val : ℕ))
  simpa using h_mul

-- (⇒) of Lemma 4.8: K-side null hypothesis transports back via the j=0
-- coordinate projection.
open Topology Filter in
private lemma tendsto_S_partial_of_T_null
    (x : LiftedPAdicHahnSeries p)
    (hT : ∀ g, Filter.Tendsto (fun M => T_partial p T x g M) Filter.atTop (𝓝 0))
    (h : ℚ) :
    Filter.Tendsto (fun M => S_partial p x h M) Filter.atTop (𝓝 0) := by
  -- Apply continuous_QpCUn_proj 0 to hT h.
  have h_proj : Filter.Tendsto
      (fun M => QpCUn_proj p T 0 (T_partial p T x h M)) Filter.atTop (𝓝 0) := by
    have hcts := (continuous_QpCUn_proj p T 0).tendsto 0
    have h0 : (0 : ℚᶜᵘⁿ_[p]) = QpCUn_proj p T 0 0 := by
      rw [map_zero]
    rw [h0]
    exact hcts.comp (hT h)
  -- Show the projection equals S_partial pointwise.
  have h_eq : ∀ M, QpCUn_proj p T 0 (T_partial p T x h M) = S_partial p x h M := by
    intro M
    rw [T_partial_eq_proj_sum]
    rw [QpCUn_proj_sum (p := p) (T := T)
        (a := fun r : Fin T => S_partial p x (h + (r.val : ℚ) / T) M) 0]
    show S_partial p x (h + ((0 : Fin T).val : ℚ) / T) M = S_partial p x h M
    have hzero : ((0 : Fin T).val : ℚ) = 0 := by simp
    rw [hzero]
    simp
  exact h_proj.congr h_eq

-- Proved via the opaque-abbreviation strategy (see `S_partial`, `T_partial`, and the four
-- supporting private lemmas above).
open Topology Filter in
/-- **Lemma 4.7.** Pulling back the `T`-null-series ideal along the inclusion
`Lifted_to_TLifted : W(𝔽ᵃ_[p])((t^ℚ)) ↪ W(𝔽ᵃ_[p])[p^{1/T}]((t^ℚ))` recovers the null-series ideal:
`TNullSeriesIdeal ∩ image = NullSeriesIdeal`. This compatibility is what lets the isomorphism `σ`
descend to the quotient. -/
theorem TNullSeriesIdeal_inter_image :
    ∀ x : LiftedPAdicHahnSeries p,
      Lifted_to_TLifted p T x ∈ TNullSeriesIdeal p T ↔ x ∈ NullSeriesIdeal p := by
  intro x
  change IsTNullSeries p T (Lifted_to_TLifted p T x) ↔ IsNullSeries x
  change (∀ g, Filter.Tendsto (fun M => T_partial p T x g M) Filter.atTop (𝓝 0))
      ↔ (∀ h, Filter.Tendsto (fun M => S_partial p x h M) Filter.atTop (𝓝 0))
  refine ⟨fun hT h => ?_, fun hN g => ?_⟩
  · exact tendsto_S_partial_of_T_null (p := p) (T := T) x hT h
  · exact tendsto_T_partial_of_null (p := p) (T := T) x hN g

/-! ### Lemma 4.8 -/

-- Helpers for the linear-shift element trick.

/-- Shift a `LiftedPAdic` Hahn series by `δ : ℚ`: coefficient at `q` is `z.coeff (q - δ)`.
Support is `support z + δ`, which is PWO because `(· + δ) : ℚ → ℚ` is monotone. -/
private noncomputable def LiftedPAdic_shift
    (δ : ℚ) (z : LiftedPAdicHahnSeries p) : LiftedPAdicHahnSeries p where
  coeff q := z.coeff (q - δ)
  isPWO_support' := by
    have hsupp : {q : ℚ | z.coeff (q - δ) ≠ 0} = (· + δ) '' {q : ℚ | z.coeff q ≠ 0} := by
      ext q
      refine ⟨fun hq => ⟨q - δ, hq, by ring⟩, ?_⟩
      rintro ⟨q', hq', rfl⟩
      simp only [Set.mem_ofPred_eq, add_sub_cancel_right]
      exact hq'
    change {q : ℚ | z.coeff (q - δ) ≠ 0}.IsPWO
    rw [hsupp]
    exact z.isPWO_support'.image_of_monotone (fun a b hab => by linarith)

private lemma LiftedPAdic_shift_coeff (δ : ℚ) (z : LiftedPAdicHahnSeries p) (q : ℚ) :
    (LiftedPAdic_shift (p := p) δ z).coeff q = z.coeff (q - δ) := rfl

/-- The i-th `R₀`-coordinate projection of `y : TLifted` viewed as a `LiftedPAdic`
Hahn series. Coefficient at `q` is `OQpCUn_proj p T i (y.coeff q)`. Support is
`⊆ y.support` because `OQpCUn_proj` sends 0 to 0. -/
private noncomputable def sProj
    (y : TLiftedPAdicHahnSeries p T) (i : Fin T) : LiftedPAdicHahnSeries p where
  coeff q := OQpCUn_proj p T i (y.coeff q)
  isPWO_support' := by
    apply y.isPWO_support'.mono
    intro q hq h_y_zero
    apply hq
    change OQpCUn_proj p T i (y.coeff q) = 0
    rw [show y.coeff q = 0 from h_y_zero, map_zero]

private lemma sProj_coeff
    (y : TLiftedPAdicHahnSeries p T) (i : Fin T) (q : ℚ) :
    (sProj p T y i).coeff q = OQpCUn_proj p T i (y.coeff q) := rfl

/-- The "linear-shift element": `pInvT^i` at index 0 minus `1` at index `i.val/T`.
This element has at most two non-zero coefficients, and lies in `TNullSeriesIdeal`. -/
private noncomputable def linearShiftElt
    (i : Fin T) : TLiftedPAdicHahnSeries p T :=
  HahnSeries.single 0 ((pInvT p T) ^ (i.val)) -
    HahnSeries.single ((i.val : ℚ) / T) 1

omit [NeZero T] in
/-- For `i = 0`, `linearShiftElt 0 = 0`. -/
private lemma linearShiftElt_eq_zero_of_zero (i : Fin T) (hi : i.val = 0) :
    linearShiftElt p T i = 0 := by
  unfold linearShiftElt
  rw [hi]
  simp

/-- The two relevant points `0` and `i.val/T` are distinct when `i.val ≠ 0`. -/
private lemma zero_ne_iT (i : Fin T) (hi : i.val ≠ 0) :
    (0 : ℚ) ≠ (i.val : ℚ) / T := by
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  intro h
  apply hi
  have hi_q : (i.val : ℚ) = 0 := by
    have h2 : (i.val : ℚ) / T = 0 := h.symm
    rw [div_eq_zero_iff] at h2
    rcases h2 with hi_zero | hT_zero
    · exact hi_zero
    · exact absurd hT_zero hT_pos.ne'
  exact_mod_cast hi_q

/-- Coefficient of `linearShiftElt` at index `0`: `(pInvT)^i` (when `i.val ≠ 0`). -/
private lemma linearShiftElt_coeff_zero (i : Fin T) (hi : i.val ≠ 0) :
    (linearShiftElt p T i).coeff 0 = (pInvT p T) ^ (i.val) := by
  unfold linearShiftElt
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_same,
    HahnSeries.coeff_single_of_ne (zero_ne_iT T i hi)]
  ring

/-- Coefficient of `linearShiftElt` at index `i.val/T`: `-1` (when `i.val ≠ 0`). -/
private lemma linearShiftElt_coeff_iT (i : Fin T) (hi : i.val ≠ 0) :
    (linearShiftElt p T i).coeff ((i.val : ℚ) / T) = -1 := by
  unfold linearShiftElt
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_same,
    HahnSeries.coeff_single_of_ne (zero_ne_iT T i hi).symm]
  ring

omit [NeZero T] in
/-- Coefficient of `linearShiftElt` is zero outside the support `{0, i.val/T}`. -/
private lemma linearShiftElt_coeff_other
    (i : Fin T) (q : ℚ) (h0 : q ≠ 0) (hi : q ≠ (i.val : ℚ) / T) :
    (linearShiftElt p T i).coeff q = 0 := by
  unfold linearShiftElt
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_of_ne h0,
    HahnSeries.coeff_single_of_ne hi, sub_zero]

/-- K-side partial sum for `linearShiftElt` at base `g`, step `M`.  Definitionally matches
the body of `IsTNullSeries (linearShiftElt p T i)` at `(g, M)`.  Wrapping the sum in an
opaque `private noncomputable def` prevents Lean from re-elaborating the
`Set.Finite.toFinset`-based index sets on every defeq check. -/
private noncomputable def linearShiftPartial
    (i : Fin T) (g : ℚ) (M : ℕ) : ℚᶜᵘⁿ_[p,T] :=
  ∑ n : Set.Finite.toFinset (TfiniteBelow p T (linearShiftElt p T i) g M),
    (pInvTQ p T) ^ (n.val : ℤ) *
      algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
        ((linearShiftElt p T i).coeff (g + (n.val : ℚ) / T))

-- **Bridge.** Unfolding `IsTNullSeries (linearShiftElt p T i)` to the opaque partial-sum
-- form.
open Topology Filter in
private lemma isTNullSeries_linearShiftElt_iff (i : Fin T) :
    IsTNullSeries p T (linearShiftElt p T i)
      ↔ ∀ g, Filter.Tendsto (fun M => linearShiftPartial p T i g M)
          Filter.atTop (𝓝 0) := Iff.rfl

/-- **The key analytic fact.**  For every `g`, the partial sum of `linearShiftElt i`
at base `g` is eventually zero (for `M ≥ ⌈i.val/T⌉`).  The proof case-splits on whether
`gT ∈ ℤ`: if no, the support condition forces an empty index set; if yes, the index
set is `{n_0, n_1}` with `n_1 = n_0 + i.val`, and the two terms cancel exactly. -/
private lemma linearShiftPartial_eventually_zero (i : Fin T) (g : ℚ) :
    ∀ᶠ M : ℕ in Filter.atTop, linearShiftPartial p T i g M = 0 := by
  by_cases hi : i.val = 0
  · -- Case `i.val = 0`: linearShiftElt = 0, so coefficient is identically zero.
    have h_pt : ∀ q : ℚ, (linearShiftElt p T i).coeff q = 0 := by
      intro q
      unfold linearShiftElt
      rw [hi]
      simp
    apply Filter.Eventually.of_forall
    intro M
    unfold linearShiftPartial
    apply Finset.sum_eq_zero
    rintro n -
    rw [h_pt, map_zero, mul_zero]
  -- Main case: i.val ≠ 0.
  rw [Filter.eventually_atTop]
  refine ⟨⌈(i.val : ℚ) / T⌉₊, fun M hM => ?_⟩
  have hT_pos : (0 : ℚ) < T := by
    have hT : T ≠ 0 := NeZero.ne T
    exact_mod_cast Nat.pos_of_ne_zero hT
  have hT_ne : (T : ℚ) ≠ 0 := hT_pos.ne'
  have hi_le_M : (i.val : ℚ) / T ≤ M := by
    have h1 : (i.val : ℚ) / T ≤ (⌈(i.val : ℚ) / T⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : ((⌈(i.val : ℚ) / T⌉₊ : ℕ) : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
    linarith
  have hi_ne_zero_q : (0 : ℚ) ≠ (i.val : ℚ) / T := zero_ne_iT T i hi
  -- Convert attach sum to ordinary sum.
  unfold linearShiftPartial
  rw [Finset.univ_eq_attach, Finset.sum_attach
    (Set.Finite.toFinset (TfiniteBelow p T (linearShiftElt p T i) g M))
    (fun n => (pInvTQ p T) ^ (n : ℤ) *
      algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T])
        ((linearShiftElt p T i).coeff (g + (n : ℚ) / T)))]
  -- Now case-split on whether `gT ∈ ℤ`.
  by_cases hgT : ∃ k : ℤ, g + (k : ℚ) / T = 0
  · -- Case `gT ∈ ℤ`: there is `n_0` with `g + n_0/T = 0`. Set `n_1 = n_0 + i.val`.
    obtain ⟨n_0, hn_0⟩ := hgT
    set n_1 : ℤ := n_0 + (i.val : ℤ) with hn_1_def
    have hn_1 : g + (n_1 : ℚ) / T = (i.val : ℚ) / T := by
      have h_split : g + ((n_0 + (i.val : ℤ) : ℤ) : ℚ) / T
          = (g + (n_0 : ℚ) / T) + (i.val : ℚ) / T := by
        push_cast; field_simp; ring
      rw [hn_1_def, h_split, hn_0, zero_add]
    have hn_0_ne_n_1 : n_0 ≠ n_1 := by
      intro h_eq
      have h_q : (n_0 : ℚ) = (n_1 : ℚ) := by exact_mod_cast h_eq
      have h_div : (n_0 : ℚ) / T = (n_1 : ℚ) / T := by rw [h_q]
      have hcomb : g + (n_0 : ℚ) / T = g + (n_1 : ℚ) / T := by rw [h_div]
      rw [hn_0, hn_1] at hcomb
      have hi_zero : (i.val : ℚ) = 0 := by
        have h_div_zero : (i.val : ℚ) / T = 0 := hcomb.symm
        have : (i.val : ℚ) = (i.val : ℚ) / T * T := by field_simp
        rw [this, h_div_zero, zero_mul]
      exact hi (by exact_mod_cast hi_zero)
    -- Show TfiniteBelow = {n_0, n_1}.
    have h_finiteBelow : Set.Finite.toFinset (TfiniteBelow p T (linearShiftElt p T i) g M)
        = ({n_0, n_1} : Finset ℤ) := by
      ext n
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h_coeff⟩
        by_contra h_not
        push Not at h_not
        obtain ⟨hn_0', hn_1'⟩ := h_not
        apply h_coeff
        apply linearShiftElt_coeff_other p T i
        · intro h_eq_0
          apply hn_0'
          have h_arg : g + (n : ℚ) / T = g + (n_0 : ℚ) / T := by rw [h_eq_0, hn_0]
          have h_div : (n : ℚ) / T = (n_0 : ℚ) / T := by linarith
          have : (n : ℚ) = (n_0 : ℚ) := by
            field_simp at h_div
            linarith
          exact_mod_cast this
        · intro h_eq_i
          apply hn_1'
          have h_arg : g + (n : ℚ) / T = g + (n_1 : ℚ) / T := by rw [h_eq_i, hn_1]
          have h_div : (n : ℚ) / T = (n_1 : ℚ) / T := by linarith
          have : (n : ℚ) = (n_1 : ℚ) := by
            field_simp at h_div
            linarith
          exact_mod_cast this
      · rintro (rfl | rfl)
        · refine ⟨?_, ?_⟩
          · rw [hn_0]; exact_mod_cast Nat.zero_le M
          · rw [hn_0, linearShiftElt_coeff_zero p T i hi]
            exact pow_ne_zero _ (pInvT_ne_zero p T)
        · refine ⟨?_, ?_⟩
          · rw [hn_1]; exact hi_le_M
          · rw [hn_1, linearShiftElt_coeff_iT p T i hi]
            exact neg_ne_zero.mpr one_ne_zero
    rw [h_finiteBelow, Finset.sum_pair hn_0_ne_n_1]
    rw [hn_0, hn_1, linearShiftElt_coeff_zero p T i hi,
      linearShiftElt_coeff_iT p T i hi]
    -- Goal: (pInvTQ)^n_0 * algMap(pInvT^i) + (pInvTQ)^n_1 * algMap(-1) = 0
    have h_alg_pInvT_pow : algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) ((pInvT p T) ^ (i.val))
        = (pInvTQ p T) ^ (i.val : ℤ) := by
      unfold pInvTQ
      rw [map_pow]
      rfl
    have h_alg_neg_one : algebraMap (ℤᶜᵘⁿ_[p,T]) (ℚᶜᵘⁿ_[p,T]) (-1 : ℤᶜᵘⁿ_[p,T]) = -1 := by
      rw [map_neg, map_one]
    rw [h_alg_pInvT_pow, h_alg_neg_one]
    rw [show (pInvTQ p T) ^ (n_0 : ℤ) * (pInvTQ p T) ^ (i.val : ℤ)
        = (pInvTQ p T) ^ (n_1 : ℤ) by
      rw [← zpow_add₀ (pInvTQ_ne_zero p T), hn_1_def]]
    ring
  · -- Case `gT ∉ ℤ`: TfiniteBelow is empty.
    have h_empty : Set.Finite.toFinset (TfiniteBelow p T (linearShiftElt p T i) g M) = ∅ := by
      ext n
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.notMem_empty,
        iff_false, not_and]
      intro _ h_coeff
      apply h_coeff
      apply linearShiftElt_coeff_other p T i
      · intro h_eq
        apply hgT
        exact ⟨n, h_eq⟩
      · intro h_eq
        apply hgT
        refine ⟨n - (i.val : ℤ), ?_⟩
        have h_split : g + ((n - (i.val : ℤ) : ℤ) : ℚ) / T
            = (g + (n : ℚ) / T) - (i.val : ℚ) / T := by
          push_cast; field_simp; ring
        rw [h_split, h_eq, sub_self]
    rw [h_empty, Finset.sum_empty]

/-- **Sub-lemma:** `linearShiftElt i ∈ TNullSeriesIdeal` for every `i : Fin T`. -/
private lemma linearShiftElt_mem_TNullSeriesIdeal (i : Fin T) :
    linearShiftElt p T i ∈ TNullSeriesIdeal p T := by
  rw [show (linearShiftElt p T i ∈ TNullSeriesIdeal p T)
      ↔ IsTNullSeries p T (linearShiftElt p T i) from Iff.rfl]
  rw [isTNullSeries_linearShiftElt_iff]
  intro g
  -- The partial sum is eventually zero, so it tends to 0.
  refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℚᶜᵘⁿ_[p,T])))
  filter_upwards [linearShiftPartial_eventually_zero p T i g] with M hM
  exact hM.symm

/-- The reconstruction of `x` from `y`: the `R₀`-projection-shift of `y`. -/
private noncomputable def xFromY
    (y : TLiftedPAdicHahnSeries p T) : LiftedPAdicHahnSeries p :=
  ∑ i : Fin T, LiftedPAdic_shift (p := p) ((i.val : ℚ) / T) (sProj p T y i)

/-- **The key coefficient identity:** for every `q ∈ ℚ`,
`(y - ι(xFromY y)).coeff q = Σ_i (linearShiftElt i * ι(sProj y i)).coeff q`. -/
private lemma coeff_identity_n
    (y : TLiftedPAdicHahnSeries p T) (q : ℚ) :
    (y - Lifted_to_TLifted p T (xFromY p T y)).coeff q
      = ∑ i : Fin T,
          (linearShiftElt p T i * Lifted_to_TLifted p T (sProj p T y i)).coeff q := by
  -- RHS = Σ_i ((pInvT)^i * OQpCUn_embd((sProj y i).coeff q)
  --             - OQpCUn_embd((sProj y i).coeff (q - i/T)))
  have h_term : ∀ i : Fin T,
      (linearShiftElt p T i * Lifted_to_TLifted p T (sProj p T y i)).coeff q
        = (pInvT p T) ^ i.val * OQpCUn_embd p T (OQpCUn_proj p T i (y.coeff q))
            - OQpCUn_embd p T (OQpCUn_proj p T i (y.coeff (q - (i.val : ℚ) / T))) := by
    intro i
    unfold linearShiftElt
    rw [show ((HahnSeries.single 0 ((pInvT p T) ^ (i.val))
          - HahnSeries.single ((i.val : ℚ) / T) 1)
        * Lifted_to_TLifted p T (sProj p T y i))
        = HahnSeries.single 0 ((pInvT p T) ^ (i.val))
            * Lifted_to_TLifted p T (sProj p T y i)
          - HahnSeries.single ((i.val : ℚ) / T) (1 : ℤᶜᵘⁿ_[p,T])
            * Lifted_to_TLifted p T (sProj p T y i) from by ring]
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul,
      sub_zero, one_mul]
    rw [Lifted_to_TLifted_coeff, Lifted_to_TLifted_coeff, sProj_coeff, sProj_coeff]
  -- LHS expands via OQpCUn_basis_decomp.
  rw [HahnSeries.coeff_sub, Lifted_to_TLifted_coeff]
  unfold xFromY
  rw [HahnSeries.coeff_sum, map_sum]
  -- LHS: y.coeff q - Σ_i OQpCUn_embd ((sProj y i).coeff (q - i/T))
  -- Apply OQpCUn_basis_decomp to y.coeff q:
  conv_lhs => rw [OQpCUn_basis_decomp p T (y.coeff q)]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h_term i]
  -- Goal: (pInvT p T) ^ i.val * OQpCUn_embd .. y.coeff q
  --   - OQpCUn_embd ((LiftedPAdic_shift (i.val/T) (sProj y i)).coeff q)
  --   = (pInvT p T) ^ i.val * OQpCUn_embd .. y.coeff q
  --   - OQpCUn_embd (OQpCUn_proj i (y.coeff (q - i.val/T)))
  -- Reduces to: LiftedPAdic_shift δ z .coeff q = z.coeff (q - δ), and sProj.coeff = OQpCUn_proj.
  rfl

/-- **Lemma 4.8.**  The image of `Lifted_to_TLifted` together with `TNullSeriesIdeal` spans
the whole T-lifted ring:
for every `y ∈ TLiftedPAdicHahnSeries p T`, there exist `x ∈ LiftedPAdicHahnSeries p` and
`n ∈ TNullSeriesIdeal p T` with `y = Lifted_to_TLifted x + n`.

The proof uses the linear-shift-element trick. We set
`x := Σ_i shift_{i/T} (sProj y i)` and `n := y - ι(x)`, where `sProj y i` is the i-th
`R₀`-coordinate projection of `y`.  Coefficient-wise, `n = Σ_i (linearShiftElt i) · ι(sProj y i)`
and each summand lies in `TNullSeriesIdeal` because `linearShiftElt i ∈ TNullSeriesIdeal`
(its partial sum is eventually zero) and `TNullSeriesIdeal` is closed under multiplication. -/
theorem range_lifted_add_TNull :
    ∀ y : TLiftedPAdicHahnSeries p T,
      ∃ x : LiftedPAdicHahnSeries p, ∃ n : TLiftedPAdicHahnSeries p T,
        n ∈ TNullSeriesIdeal p T ∧ y = Lifted_to_TLifted p T x + n := by
  intro y
  refine ⟨xFromY p T y, y - Lifted_to_TLifted p T (xFromY p T y), ?_, ?_⟩
  · -- n ∈ TNullSeriesIdeal
    have h_decomp :
        y - Lifted_to_TLifted p T (xFromY p T y)
          = ∑ i : Fin T,
              linearShiftElt p T i * Lifted_to_TLifted p T (sProj p T y i) := by
      ext q
      rw [coeff_identity_n p T y q, HahnSeries.coeff_sum]
    rw [h_decomp]
    apply Submodule.sum_mem
    intro i _
    exact (TNullSeriesIdeal p T).mul_mem_right _
      (linearShiftElt_mem_TNullSeriesIdeal p T i)
  · -- y = ι(x) + (y - ι(x))
    abel

/-! ### Proposition 4.9 — isomorphism `σ : 𝕃_[p] ≃+* 𝕃_[p,T]` -/

-- Helpers for the standard quotient-isomorphism construction.

/-- The ring map `𝕃_[p] →+* 𝕃_[p,T]` lifted from
`Lifted_to_TLifted : LiftedPAdicHahnSeries p →+* TLiftedPAdicHahnSeries p T`
through the quotient by `NullSeriesIdeal p`.  The lifting kernel condition is the
(⇐) direction of Lemma 4.7 (`TNullSeriesIdeal_inter_image`). -/
noncomputable def σ_lift : 𝕃_[p] →+* 𝕃_[p,T] :=
  Ideal.Quotient.lift (NullSeriesIdeal p)
    ((Ideal.Quotient.mk (TNullSeriesIdeal p T)).comp (Lifted_to_TLifted p T))
    (fun x hx => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact (TNullSeriesIdeal_inter_image p T x).mpr hx)

/-- Computation rule for `σ_lift` on quotient classes: it sends the class of `x` to the class of its
image `Lifted_to_TLifted x`. -/
lemma σ_lift_mk (x : LiftedPAdicHahnSeries p) :
    σ_lift p T (Ideal.Quotient.mk (NullSeriesIdeal p) x) =
      Ideal.Quotient.mk (TNullSeriesIdeal p T) (Lifted_to_TLifted p T x) := by
  change Ideal.Quotient.lift _ _ _ _ = _
  rw [Ideal.Quotient.lift_mk, RingHom.comp_apply]

/-- The lifted map `σ_lift : 𝕃_[p] → 𝕃_[p,T]` is injective. -/
lemma σ_lift_injective : Function.Injective (σ_lift p T) := by
  intro f₁ f₂ h
  obtain ⟨x₁, rfl⟩ := Ideal.Quotient.mk_surjective f₁
  obtain ⟨x₂, rfl⟩ := Ideal.Quotient.mk_surjective f₂
  rw [σ_lift_mk, σ_lift_mk] at h
  rw [Ideal.Quotient.eq] at h
  rw [← map_sub] at h
  rw [Ideal.Quotient.eq]
  exact (TNullSeriesIdeal_inter_image p T (x₁ - x₂)).mp h

/-- The lifted map `σ_lift : 𝕃_[p] → 𝕃_[p,T]` is surjective; with injectivity this makes `σ` a ring
isomorphism. -/
lemma σ_lift_surjective : Function.Surjective (σ_lift p T) := by
  intro g
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨x, n, hn, hxy⟩ := range_lifted_add_TNull p T y
  refine ⟨Ideal.Quotient.mk (NullSeriesIdeal p) x, ?_⟩
  rw [σ_lift_mk, hxy]
  rw [show Ideal.Quotient.mk (TNullSeriesIdeal p T) ((Lifted_to_TLifted p T) x + n) =
      Ideal.Quotient.mk (TNullSeriesIdeal p T) ((Lifted_to_TLifted p T) x) +
        Ideal.Quotient.mk (TNullSeriesIdeal p T) n from rfl]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hn, add_zero]

-- The natural inclusion `Lifted_to_TLifted` carries the Teichmüller-style
-- `fromCoeff` constructor of the K₀-side to the K-side: for any
-- `s : ℚ → 𝔽ᵃ_[p]` with PWO support,
-- `Lifted_to_TLifted (Lifted.fromCoeff s) = TLifted.fromCoeff p T s`.
omit [NeZero T] in
private lemma Lifted_to_TLifted_fromCoeff_eq (s : ℚ → Fpbar p)
    (hspwo : (Function.support s).IsPWO) :
    Lifted_to_TLifted p T (LiftedPAdicHahnSeries.fromCoeff s hspwo) =
      TLiftedPAdicHahnSeries.fromCoeff p T s hspwo := by
  apply HahnSeries.ext
  funext q
  rfl

/-- **Proposition 4.9.**  The composition
`LiftedPAdicHahnSeries p → TLiftedPAdicHahnSeries p T → 𝕃_[p,T]`
factors through the quotient `𝕃_[p]` and induces a ring isomorphism
`σ : 𝕃_[p] ≃+* 𝕃_[p,T]`.

This is the standard fact "for `R₁ ⊂ R₂` with `R₁ + I = R₂`, `R₁/(I ∩ R₁) ≃ R₂/I`" applied
to Lemmas 4.7 and 4.8. -/
noncomputable def σ : 𝕃_[p] ≃+* 𝕃_[p,T] :=
  RingEquiv.ofBijective (σ_lift p T)
    (⟨σ_lift_injective p T, σ_lift_surjective p T⟩ :
      Function.Bijective ⇑(σ_lift p T))

/-! ### Remark 4.10 — coefficient compatibility -/

/-- **Remark 4.10.**  The isomorphism `σ` preserves Teichmüller coefficients:
`(σ f).coeff = f.coeff` for every `f : 𝕃_[p]`.  Equivalently, the natural commutative
diagram of Proposition 4.9 commutes on coefficients. -/
theorem σ_coeff_compat (f : 𝕃_[p]) :
    (σ p T f).coeff = f.coeff := by
  change (exists_canonical_T_expansion p T (σ p T f)).choose.val =
    (exists_canonical_expansion f).choose.val
  set s_sub := (exists_canonical_expansion f).choose with hs_def
  -- Property of the canonical K₀-side expansion of `f`.
  have hf_canon : Ideal.Quotient.ringCon (NullSeriesIdeal p) f.out
      (LiftedPAdicHahnSeries.fromCoeff s_sub.val s_sub.prop) :=
    (exists_canonical_expansion f).choose_spec.1
  have hf_mk : Ideal.Quotient.mk (NullSeriesIdeal p) f.out =
      Ideal.Quotient.mk (NullSeriesIdeal p)
        (LiftedPAdicHahnSeries.fromCoeff s_sub.val s_sub.prop) :=
    Quotient.sound hf_canon
  have hf_eq : f = Ideal.Quotient.mk (NullSeriesIdeal p)
      (LiftedPAdicHahnSeries.fromCoeff s_sub.val s_sub.prop) := by
    rw [← Ideal.Quotient.mk_out f]
    exact hf_mk
  -- Show that `s_sub` is also a canonical T-expansion of `σ p T f`.
  have h_T_canon : Ideal.Quotient.ringCon (TNullSeriesIdeal p T) (σ p T f).out
      (TLiftedPAdicHahnSeries.fromCoeff p T s_sub.val s_sub.prop) := by
    apply Quotient.exact
    change Ideal.Quotient.mk (TNullSeriesIdeal p T) (σ p T f).out =
      Ideal.Quotient.mk (TNullSeriesIdeal p T)
        (TLiftedPAdicHahnSeries.fromCoeff p T s_sub.val s_sub.prop)
    rw [Ideal.Quotient.mk_out, hf_eq]
    change σ_lift p T ((Ideal.Quotient.mk (NullSeriesIdeal p))
        (LiftedPAdicHahnSeries.fromCoeff s_sub.val s_sub.prop)) = _
    rw [σ_lift_mk, Lifted_to_TLifted_fromCoeff_eq]
  -- Apply unique-existence of the canonical T-expansion.
  have heq : s_sub = (exists_canonical_T_expansion p T (σ p T f)).choose :=
    (exists_canonical_T_expansion p T (σ p T f)).unique h_T_canon
      (exists_canonical_T_expansion p T (σ p T f)).choose_spec.1
  exact congrArg Subtype.val heq.symm

end TScaled

end FormalizedSparse
