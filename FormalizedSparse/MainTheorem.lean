/-
Copyright (c) 2025 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Yijun Yuan
-/
module

public import FormalizedSparse.Sparse
public import FormalizedSparse.Tscaled
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.PNat.Interval
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.RingTheory.Localization.Integral

/-!
# Main theorem: sparse support implies transcendence

This file contains the proof of the main theorem of the paper: if a `p`-adic Hahn series `f` has a
sparse set of representatives modulo `ℤ` (after scaling by some integer `T ≥ 1`), then `f` is
transcendental over `ℚᵘⁿ_[p]`, and hence over `ℚ_[p]`.

The proof is technical: one regroups the terms of `f` into "coefficient bundles" `C_s`, applies the
multinomial expansion to a hypothetical algebraic relation, and uses the sparseness condition to
isolate a single surviving nonzero term, producing a contradiction. See `Sparse.lean` for the
definition of `IsSparse` (Definition 1.4) and the associated notation.

## Main statements

- `FormalizedSparse.main_theorem`: the main transcendence theorem (Theorem 5.3): if `-T · Supp(f)`
  admits a nonzero sparse set of representatives modulo `ℤ`, then `f` is transcendental over
  `ℚᵘⁿ_[p]`.

## Tags

p-adic, Hahn series, transcendence, sparse, multinomial expansion
-/

@[expose] public section

-- Bring `NeZero T.val` into scope for any `T : ℕ+` so we can use `Tscaled` API.
instance PNat.coe_neZero (T : ℕ+) : NeZero (T : ℕ) := ⟨T.ne_zero⟩

/-- `CharZero ℚᵘⁿ_[p]` follows from the injective inclusion `ℚ_[p] → ℚᵘⁿ_[p]`. -/
private instance instCharZeroQpUn (p : ℕ) [Fact (Nat.Prime p)] : CharZero ℚᵘⁿ_[p] :=
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap ℚ_[p] ℚᵘⁿ_[p]))

/-- `CharZero ℚᵘⁿ_[p,T]` follows from the injective inclusion `ℚᵘⁿ_[p] → ℚᵘⁿ_[p,T]`. -/
private instance instCharZeroQpUnT (p : ℕ) [Fact (Nat.Prime p)] (T : ℕ+) :
    CharZero ℚᵘⁿ_[p, (T : ℕ)] :=
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap ℚᵘⁿ_[p] ℚᵘⁿ_[p, (T : ℕ)]))

namespace FormalizedSparse

open TrustworthyKedlaya Sparse TScaled

/-- `IsRepModZ A B` says that `A` is a **set of representatives of `B` modulo `ℤ`**: every element
of `B` is congruent modulo `ℤ` to a unique element of `A`, and every element of `A` is congruent
modulo `ℤ` to some element of `B`. -/
def IsRepModZ (A B : Set ℚ) : Prop :=
  (
    ∀ b ∈ B, ∃! a ∈ A, (a - b).isInt
  ) ∧ (
    ∀ a ∈ A, ∃ b ∈ B, (a - b).isInt
  )

namespace MainTheorem

/-! ### Step 1 — support cosets `Sd`, `muQ`, `Stilde`. -/

/-- The "coset slice" `f.support ∩ (-‖d‖/T + (1/T)ℤ)` for a `DigitSeries` `d`.
We use the equivalent algebraic form `(d.norm p + T·q).isInt`. -/
noncomputable def Sd (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+) (d : DigitSeries) :
    Set ℚ :=
  f.support ∩ {q | ((d.norm p : ℚ) + (T : ℚ) * q).isInt = true}

/-- The coset slice `Sd d` is contained in the support of `f`. -/
lemma Sd_subset_support {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+) (d : DigitSeries) :
    Sd p f T d ⊆ f.support :=
  Set.inter_subset_left

/-- The coset slice `Sd d` is well-ordered (as a subset of the well-ordered support of `f`), so it
has a minimum used to define `muQ`. -/
lemma Sd_isWF {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+) (d : DigitSeries) :
    (Sd p f T d).IsWF :=
  (support_IsPWO f).isWF.mono (Sd_subset_support f T d)

/-- `Sd d` is nonempty for every `d ∈ S`. Uses `hf2.2` (existence side of `IsRepModZ`). -/
lemma Sd_nonempty {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {d : DigitSeries} (hd : d ∈ S) :
    (Sd p f T d).Nonempty := by
  have hmem : (d.norm p : ℚ) ∈ ((DigitSeries.norm p) '' S) :=
    ⟨d, hd, rfl⟩
  obtain ⟨b, hb_mem, hint⟩ := hf2.2 _ hmem
  obtain ⟨q, hq_supp, hq_eq⟩ := hb_mem
  refine ⟨q, hq_supp, ?_⟩
  change ((d.norm p : ℚ) + (T : ℚ) * q).isInt = true
  have h_eq : (d.norm p : ℚ) - b = (d.norm p : ℚ) + (T : ℚ) * q := by
    rw [← hq_eq]; ring
  rw [← h_eq]; exact hint

/-- The minimum element of `Sd d`. -/
noncomputable def muQ {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d : S) : ℚ :=
  (Sd_isWF f T d.val).min (Sd_nonempty hf2 d.property)

/-- `muQ d` — the chosen representative for `d` — lies in the support of `f`. -/
lemma muQ_mem_support {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d : S) : muQ hf2 d ∈ f.support := by
  have h := (Sd_isWF f T d.val).min_mem (Sd_nonempty hf2 d.property)
  exact Sd_subset_support f T _ h

/-- The defining residue property of `muQ d`: `‖d‖ + T · muQ d` is an integer, i.e. `muQ d` lies in
the coset `-‖d‖/T + (1/T)ℤ` selected by `d`. -/
lemma muQ_residue {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d : S) : ((d.val.norm p : ℚ) + (T : ℚ) * muQ hf2 d).isInt = true :=
  ((Sd_isWF f T d.val).min_mem (Sd_nonempty hf2 d.property)).2

/-- The key uniqueness step: `muQ` is injective. -/
lemma muQ_injective {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} (hS : ∀ d ∈ S, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Function.Injective (muQ (T := T) hf2) := by
  intro d d' hmu
  have hd := muQ_residue hf2 d
  have hd' := muQ_residue hf2 d'
  have h_sub_int :
      ((d.val.norm p : ℚ) - (d'.val.norm p : ℚ)).isInt = true := by
    set a := (d.val.norm p : ℚ) + (T : ℚ) * muQ hf2 d with ha_def
    set b := (d'.val.norm p : ℚ) + (T : ℚ) * muQ hf2 d' with hb_def
    have h1 : (d.val.norm p : ℚ) - (d'.val.norm p : ℚ) = a - b := by
      rw [ha_def, hb_def, hmu]; ring
    rw [h1]
    have ha_eq : a = (a.num : ℚ) := Rat.eq_num_of_isInt hd
    have hb_eq : b = (b.num : ℚ) := Rat.eq_num_of_isInt hd'
    rw [ha_eq, hb_eq]
    have : (a.num : ℚ) - (b.num : ℚ) = ((a.num - b.num : ℤ) : ℚ) := by push_cast; ring
    rw [this, Rat.isInt]; simp
  have heq : d.val = d'.val :=
    DigitSeries.eq_of_norm_sub_isInt (hS d.val d.property) (hS d'.val d'.property) h_sub_int
  exact Subtype.ext heq

/-- The "S̃" of the PDF, packaged as a `Set ℚ`: `{ muQ d | d ∈ S }`. -/
noncomputable def Stilde {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) : Set ℚ :=
  Set.range (muQ (T := T) hf2)

/-- The set of representatives `S̃ = { muQ d | d ∈ S }` is contained in the support of `f`. -/
lemma Stilde_subset_support {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Stilde hf2 ⊆ f.support := by
  rintro q ⟨d, rfl⟩; exact muQ_mem_support hf2 d

/-- The set of representatives `S̃` is partially well-ordered (inheriting well-orderedness from the
support of `f`). -/
lemma Stilde_isPWO {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    (Stilde hf2).IsPWO :=
  (support_IsPWO f).mono (Stilde_subset_support hf2)

/-- The bijection `μ : S → Stilde`. -/
noncomputable def muToStilde {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    S → ↥(Stilde hf2) :=
  fun d => ⟨muQ hf2 d, ⟨d, rfl⟩⟩

/-- The map `μ : S → S̃` is a bijection: injectivity is the rigidity of the representatives, and
surjectivity holds by construction of `S̃` as the range of `muQ`. -/
lemma muToStilde_bijective {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} (hS : ∀ d ∈ S, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Function.Bijective (muToStilde (T := T) hf2) := by
  refine ⟨fun d d' h => ?_, ?_⟩
  · have : muQ hf2 d = muQ hf2 d' := by
      simpa [muToStilde] using congrArg Subtype.val h
    exact muQ_injective hS hf2 this
  · rintro ⟨q, ⟨d, hq_eq⟩⟩
    refine ⟨d, ?_⟩
    apply Subtype.ext
    simp [muToStilde, hq_eq]

/-- The S→Stilde bijection as an `Equiv`. -/
noncomputable def muEquiv {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} (hS : ∀ d ∈ S, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    S ≃ ↥(Stilde hf2) :=
  Equiv.ofBijective _ (muToStilde_bijective hS hf2)

/-! ### Step 2 — coefficient bundles `C_s`.

For `s ∈ Stilde`, the paper defines `C_s = ∑_{w ∈ ℤ} [f(s + w/T)] · pInvT^w ∈ ℤᵘⁿ_[p,T]`.
Since `s = muQ d` is the minimum of `Sd d`, the negative-`w` terms vanish, so
`C_s = ∑_{w ≥ 0} [f(s + w/T)] · pInvT^w`, a convergent series in the complete DVR
`ℤᵘⁿ_[p,T]`. We decompose the construction into a term `Cs_term`, a partial sum
`Cs_partial`, an existential limit lemma `exists_Cs` (the analytical hard step), and
the final definition `Cs`. -/

/-- the `w`-th summand `OQpUn_embd p T (teichmuller p (f.coeff (s + w/T))) · pInvT^w`. -/
noncomputable def Cs_term {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (w : ℕ) : ℤᵘⁿ_[p,(T : ℕ)] :=
  OQpUn_embd p T (WittVector.teichmuller p (f.coeff (s.val + (w : ℚ) / T))) * (pInvT p T) ^ w

/-- finite partial sum `∑_{w < N} Cs_term hf2 s w`. -/
noncomputable def Cs_partial {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (N : ℕ) : ℤᵘⁿ_[p,(T : ℕ)] :=
  ∑ w ∈ Finset.range N, Cs_term hf2 s w

/-- For `N ≤ N'`, the difference of partial sums
`Cs_partial s N' - Cs_partial s N` equals the explicit `Finset.Ico` sum of `Cs_term`. -/
private lemma Cs_partial_diff_eq_Ico_sum
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) {N N' : ℕ} (hN : N ≤ N') :
    Cs_partial hf2 s N' - Cs_partial hf2 s N
      = ∑ w ∈ Finset.Ico N N', Cs_term hf2 s w := by
  unfold Cs_partial
  simp only [Finset.range_eq_Ico]
  have h_split :
      ∑ w ∈ Finset.Ico 0 N', Cs_term hf2 s w =
        (∑ w ∈ Finset.Ico 0 N, Cs_term hf2 s w) +
        ∑ w ∈ Finset.Ico N N', Cs_term hf2 s w :=
    (Finset.sum_Ico_consecutive (fun w => Cs_term hf2 s w) (Nat.zero_le N) hN).symm
  rw [h_split, add_sub_cancel_left]

/-- Each summand `algebraMap (Cs_term hf2 s w)` has
valuation `ofAdd(-w)` in `ℚᵘⁿ_[p,T]`. -/
private lemma algebraMap_Cs_term_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (w : ℕ) :
    Valued.v (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s w))
      ≤ ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) : WithZero _) := by
  unfold Cs_term
  rw [map_mul]
  rw [map_pow]
  rw [show (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])) (pInvT p T) = pInvTQ p T from rfl]
  rw [Valuation.map_mul]
  rw [show ((pInvTQ p T) ^ w : ℚᵘⁿ_[p, (T : ℕ)]) = (pInvTQ p T) ^ (w : ℤ) from
    (zpow_natCast _ _).symm]
  rw [valued_v_pInvT_zpow]
  have h_OQ_le_one :
      Valued.v (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
        (OQpUn_embd p (T : ℕ)
          (WittVector.teichmuller p (f.coeff (s.val + (w : ℚ) / T))))) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p,(T : ℕ)])).valuation_le_one _
  calc Valued.v (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
          (OQpUn_embd p (T : ℕ)
            (WittVector.teichmuller p (f.coeff (s.val + (w : ℚ) / T))))) *
          ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) : WithZero _)
      ≤ 1 * ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) : WithZero _) :=
        mul_le_mul' h_OQ_le_one (le_refl _)
    _ = ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) : WithZero _) := one_mul _

/-- For `N ≤ N'`,
Valued.v (algebraMap (Cs_partial s N' - Cs_partial s N))
≤ ofAdd(-N)`. This is the explicit Cauchy property of the partial sums. -/
private lemma Cs_partial_diff_alg_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) {N N' : ℕ} (hN : N ≤ N') :
    Valued.v (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
              (Cs_partial hf2 s N' - Cs_partial hf2 s N))
      ≤ ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _) := by
  rw [Cs_partial_diff_eq_Ico_sum hf2 s hN]
  rw [map_sum]
  apply Valuation.map_sum_le
  intro w hw
  have hw_ge : N ≤ w := (Finset.mem_Ico.mp hw).1
  have h_w_term := algebraMap_Cs_term_v_le hf2 s w
  have h_le : ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) ≤
      ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_le_coe]
    apply Multiplicative.ofAdd_le.mpr
    have : (N : ℤ) ≤ (w : ℤ) := by exact_mod_cast hw_ge
    omega
  exact le_trans h_w_term h_le

/-- For `M ≤ M'` and `N ≤ M`, the algebraMap of the
partial-sum difference is bounded by `ofAdd(-N)` rather than the tighter `ofAdd(-M)`.
This single-direction helper packages the rewrite + bound + index-weakening together,
which `algebraMap_Cs_partial_isCauchy` invokes symmetrically in both `K ≤ K'` and
`K' ≤ K` branches. -/
private lemma algebraMap_Cs_partial_diff_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) {N M M' : ℕ} (hMM' : M ≤ M') (hNM : N ≤ M) :
    Valued.v
        (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s M')
          - algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s M)) ≤
        ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _) := by
  rw [← map_sub]
  refine le_trans (Cs_partial_diff_alg_v_le hf2 s hMM') ?_
  rw [WithZero.coe_le_coe]
  apply Multiplicative.ofAdd_le.mpr
  have : (N : ℤ) ≤ (M : ℤ) := by exact_mod_cast hNM
  omega

/-- `algebraMap ∘ Cs_partial s` is a Cauchy sequence in `ℚᵘⁿ_[p,T]`.

Pattern-copy of `TintPartial_isCauchy`: convert `γ ∈ Γ₀ˣ` to
`ε ∈ ℝ` via `WithZeroMulInt.toNNReal`, pick `N` such that `(p⁻¹)^N < ε`, and use
the partial-sum tail bound `Cs_partial_diff_alg_v_le` to verify the Cauchy
condition. -/
private lemma algebraMap_Cs_partial_isCauchy
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    CauchySeq (fun N : ℕ =>
      algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N)) := by
  rw [show CauchySeq (fun N : ℕ =>
        algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N)) =
        Cauchy (Filter.atTop.map (fun N : ℕ =>
          algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))) from rfl,
      Valued.cauchy_iff]
  refine ⟨Filter.map_neBot, ?_⟩
  intro γ
  have hp1 : (1 : NNReal) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp_pos : (0 : NNReal) < p := zero_lt_one.trans hp1
  have hsm : StrictMono (WithZeroMulInt.toNNReal (p_ne_zero p)) :=
    WithZeroMulInt.toNNReal_strictMono hp1
  have hpinv_lt : (p : NNReal)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hpinv_nn : 0 ≤ ((p : NNReal)⁻¹ : NNReal) := zero_le
  -- v4.31: `γ : (ValueGroup₀ Valued.v)ˣ`; bridge to a `WithZero (Multiplicative ℤ)` bound `c`.
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
  have h_convert : ∀ a : ℚᵘⁿ_[p, (T : ℕ)],
      Valued.v a ≤
        ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _) →
      Valued.v.restrict a < γ.1 := by
    intro a hbound
    rw [Valuation.restrict_lt_iff_lt_embedding, ← hc_def]
    have h_nnreal_le : WithZeroMulInt.toNNReal (p_ne_zero p) (Valued.v a) ≤
        WithZeroMulInt.toNNReal (p_ne_zero p)
          (((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _)) :=
      hsm.monotone hbound
    have htoNN : WithZeroMulInt.toNNReal (p_ne_zero p)
        (((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _)) =
        (p : NNReal) ^ (-(N : ℤ)) := by
      rw [WithZeroMulInt.toNNReal_neg_apply (p_ne_zero p) WithZero.coe_ne_zero, WithZero.unzero_coe]
      congr 1
    rw [htoNN] at h_nnreal_le
    have h_pow_le : (p : NNReal) ^ (-(N : ℤ)) ≤ ((p : NNReal)⁻¹) ^ N := by
      rw [show (p : NNReal) ^ (-(N : ℤ)) = ((p : NNReal)⁻¹) ^ (N : ℤ) from by
        rw [zpow_neg, ← inv_zpow]]
      rw [show ((p : NNReal)⁻¹) ^ (N : ℤ) = ((p : NNReal)⁻¹) ^ N from zpow_natCast _ _]
    have h_combined : WithZeroMulInt.toNNReal (p_ne_zero p) (Valued.v a) < ε :=
      lt_of_le_of_lt (h_nnreal_le.trans h_pow_le) hN
    rw [hε_def] at h_combined
    exact hsm.lt_iff_lt.mp h_combined
  refine ⟨{ a | ∃ K : ℕ, N ≤ K ∧ a =
    algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s K) }, ?_, ?_⟩
  · rw [Filter.mem_map]
    exact Filter.mem_of_superset (Filter.Ici_mem_atTop N) (fun K hK => ⟨K, hK, rfl⟩)
  · intro a ha b hb
    obtain ⟨K, hK, rfl⟩ := ha
    obtain ⟨K', hK', rfl⟩ := hb
    rcases le_total K K' with hKK' | hKK'
    · exact h_convert _ (algebraMap_Cs_partial_diff_v_le hf2 s hKK' hK)
    · have hneg :
          algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s K')
            - algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s K)
            = -(algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s K)
                - algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s K')) := by
        ring
      rw [hneg, Valuation.map_neg]
      exact h_convert _ (algebraMap_Cs_partial_diff_v_le hf2 s hKK' hK')

/-- `Cs_term hf2 s 0 = OQpUn_embd p T (teichmuller p (f.coeff s.val))` is a unit
in `ℤᵘⁿ_[p,T]`, so its `algebraMap` to `ℚᵘⁿ_[p,T]` has valuation `1`.

Reason: `s.val ∈ Stilde hf2 ⊆ f.support`, so `f.coeff s.val ≠ 0`. The Teichmüller
lift of a nonzero element has nonzero `coeff 0` (it IS the element), so by
`WittVector.isUnit_of_coeff_zero_ne_zero` the Teichmüller lift is a unit; the
image under `OQpUn_embd` (a ring hom) is also a unit; and `Valuation.Integers.one_of_isUnit'`
gives valuation `1`. -/
private lemma Cs_term_zero_v_eq_one
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    Valued.v (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)) =
      (1 : WithZero (Multiplicative ℤ)) := by
  unfold Cs_term
  simp only [Nat.cast_zero, zero_div, add_zero, pow_zero, mul_one]
  have h_supp : s.val ∈ f.support := Stilde_subset_support hf2 s.property
  have h_coeff_ne : f.coeff s.val ≠ 0 := h_supp
  have h_teich_unit : IsUnit (WittVector.teichmuller p (f.coeff s.val)) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [WittVector.teichmuller_coeff_zero]
    exact h_coeff_ne
  have h_embd_unit : IsUnit (OQpUn_embd p (T : ℕ)
      (WittVector.teichmuller p (f.coeff s.val))) :=
    h_teich_unit.map (OQpUn_embd p (T : ℕ))
  exact Valuation.Integers.one_of_isUnit' h_embd_unit
    (fun _ => (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p,(T : ℕ)])).valuation_le_one _)

/-- the partial sums `Cs_partial` admit a
non-zero limit in `ℤᵘⁿ_[p,T]`.

Construction outline: the algebraMap to the complete DVF `ℚᵘⁿ_[p,T]` carries the
sequence to a Cauchy sequence (using `valued_v_pInvT_zpow` to bound the tails by
`(ofAdd (-w) : WithZero _)`), the limit exists by `instCompleteSpaceQpUnT`, and it
lies in the closed unit ball (the image of `ℤᵘⁿ_[p,T]` under algebraMap). Non-vanishing
is from the `w = 0` term: `OQpUn_embd p T (teichmuller p (f.coeff s))` with
`f.coeff s ≠ 0` (since `s ∈ Stilde ⊆ f.support` via `Stilde_subset_support`). -/
lemma exists_Cs {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    ∃ c : ℤᵘⁿ_[p,(T : ℕ)],
      c ≠ 0 ∧
      Filter.Tendsto
        (fun N => algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))
        Filter.atTop
        (nhds (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) c)) := by
  -- Step 1: `algebraMap ∘ Cs_partial s` is Cauchy in `ℚᵘⁿ_[p,T]` (helper lemma).
  have h_cauchy := algebraMap_Cs_partial_isCauchy hf2 s
  -- Step 2: take limit `y` in the complete DVF `ℚᵘⁿ_[p,T]`.
  set y : ℚᵘⁿ_[p, (T : ℕ)] := Filter.limUnder Filter.atTop
    (fun N : ℕ => algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))
    with hy_def
  have hy_tendsto : Filter.Tendsto
      (fun N : ℕ => algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))
      Filter.atTop (nhds y) := h_cauchy.tendsto_limUnder
  -- Step 3: `y` lies in the integer subring, hence in the image of `algebraMap`.
  have h_y_v_le_one : Valued.v y ≤ (1 : WithZero (Multiplicative ℤ)) := by
    have h_eventually : ∀ᶠ N : ℕ in Filter.atTop,
        Valued.v (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
          (Cs_partial hf2 s N)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      apply Filter.Eventually.of_forall
      intro N
      exact (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p,(T : ℕ)])).valuation_le_one _
    have h_closed : IsClosed
        { x : ℚᵘⁿ_[p, (T : ℕ)] | Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) } := by
      have h := Valued.isClosed_integer (ℚᵘⁿ_[p, (T : ℕ)])
      convert h using 1
      ext x
      simp [Valuation.mem_integer_iff]
    exact h_closed.mem_of_tendsto hy_tendsto h_eventually
  -- Step 4: lift `y` to `c : ℤᵘⁿ_[p,T]` via `IsDiscreteValuationRing.exists_lift_of_le_one`.
  obtain ⟨c, hc_eq⟩ :
      ∃ c : ℤᵘⁿ_[p,(T : ℕ)],
        algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) c = y :=
    Texists_lift_of_valued_le_one p (T : ℕ) h_y_v_le_one
  -- Step 5a: control the tail valuation at `N = 1` via closed-ball + tendsto.
  have h_tail_bound :
      Valued.v (y - algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0))
        ≤ ((Multiplicative.ofAdd (-(1 : ℤ)) : Multiplicative ℤ) : WithZero _) := by
    set tgt : ℚᵘⁿ_[p, (T : ℕ)] :=
      y - algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)
      with htgt_def
    set ball : Set (ℚᵘⁿ_[p, (T : ℕ)]) :=
      { x | Valued.v x ≤ ((Multiplicative.ofAdd (-(1 : ℤ)) : Multiplicative ℤ) : WithZero _) }
      with hball_def
    have h_ball_closed : IsClosed ball := by
      -- v4.31: `isClosed_closedBall` is stated via `Valued.v.restrict`; bridge through the
      -- value-group class of `pInvTQ p T` (whose valuation is `ofAdd(-1)`).
      have hbridge : ball =
          {x : ℚᵘⁿ_[p, (T : ℕ)] | Valued.v.restrict x ≤ Valued.v.restrict (pInvTQ p (T : ℕ))} := by
        ext x
        rw [hball_def, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
          Valuation.restrict_le_iff_le_embedding, Valuation.embedding_restrict, valued_v_pInvT]
      rw [hbridge]
      exact Valued.isClosed_closedBall _ _
    have h_tendsto_tail :
        Filter.Tendsto
          (fun N : ℕ =>
            algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N)
              - algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0))
          Filter.atTop (nhds tgt) :=
      hy_tendsto.sub tendsto_const_nhds
    have h_eventually : ∀ᶠ N : ℕ in Filter.atTop,
        algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N)
          - algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0) ∈ ball := by
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      change Valued.v (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N)
            - algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)) ≤ _
      have h_partial_1 : Cs_partial hf2 s 1 = Cs_term hf2 s 0 := by
        simp [Cs_partial]
      rw [show algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0) =
            algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s 1)
          from by rw [h_partial_1]]
      rw [← map_sub]
      exact Cs_partial_diff_alg_v_le hf2 s hN
    exact h_ball_closed.mem_of_tendsto h_tendsto_tail h_eventually
  -- Step 5b: combined with the unit-valuation fact `Cs_term_zero_v_eq_one`, deduce
  -- `Valued.v y = 1` via the ultrametric strict-inequality lemma `Valuation.map_add_eq_of_lt_left`.
  have h_y_v_eq_one : Valued.v y = (1 : WithZero (Multiplicative ℤ)) := by
    have h_term_v_one := Cs_term_zero_v_eq_one hf2 s
    have h_ofAdd_neg_one_lt_one :
        ((Multiplicative.ofAdd (-(1 : ℤ)) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
      rw [show (1 : WithZero (Multiplicative ℤ)) =
          ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _) from rfl,
        WithZero.coe_lt_coe]
      exact Multiplicative.ofAdd_lt.mpr (by omega)
    have h_strict :
        Valued.v (y - algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)) <
          Valued.v (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)) := by
      rw [h_term_v_one]
      exact lt_of_le_of_lt h_tail_bound h_ofAdd_neg_one_lt_one
    have h_sum_eq := Valuation.map_add_eq_of_lt_left Valued.v h_strict
    have h_simplify :
        algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)
          + (y - algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s 0)) = y := by
      ring
    rw [h_simplify, h_term_v_one] at h_sum_eq
    exact h_sum_eq
  -- `c ≠ 0` from `y ≠ 0` (Valued.v y = 1) and injectivity of algebraMap.
  have h_y_ne_zero : y ≠ 0 := by
    intro h_y0
    rw [h_y0, map_zero] at h_y_v_eq_one
    exact zero_ne_one h_y_v_eq_one
  have h_c_ne_zero : c ≠ 0 := by
    intro h_c0
    apply h_y_ne_zero
    rw [← hc_eq, h_c0, map_zero]
  -- Final assembly.
  refine ⟨c, h_c_ne_zero, ?_⟩
  rw [hc_eq]
  exact hy_tendsto

/-- `Cs hf2 s ∈ ℤᵘⁿ_[p,T]`, the coefficient bundle for `s ∈ Stilde`. -/
noncomputable def Cs {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) : ℤᵘⁿ_[p,(T : ℕ)] :=
  (exists_Cs hf2 s).choose

/-- `Cs hf2 s ≠ 0`. Immediate from `exists_Cs`. -/
lemma Cs_ne_zero {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) : Cs hf2 s ≠ 0 :=
  (exists_Cs hf2 s).choose_spec.1

/-- `algebraMap (Cs_partial hf2 s N)` converges to `algebraMap (Cs hf2 s)` in
`ℚᵘⁿ_[p,T]`. This is the analytical characterization of `Cs` as a Cauchy sum. -/
lemma Cs_tendsto {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    Filter.Tendsto
      (fun N => algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))
      Filter.atTop
      (nhds (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs hf2 s))) :=
  (exists_Cs hf2 s).choose_spec.2

/-! ### Step 3 — the lift `fhat`. -/

/-- the coefficient function of `fhat`: `Cs ⟨q, h⟩` on `Stilde`, `0` elsewhere. -/
noncomputable def fhatCoeff {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (q : ℚ) : ℤᵘⁿ_[p,(T : ℕ)] := by
  classical
  exact (if h : q ∈ Stilde hf2 then Cs hf2 ⟨q, h⟩ else 0)

/-- the T-lifted Hahn series `fhat : TLiftedPAdicHahnSeries p T`. -/
noncomputable def fhat {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    TLiftedPAdicHahnSeries p (T : ℕ) where
  coeff := fhatCoeff hf2
  isPWO_support' := by
    apply (Stilde_isPWO hf2).mono
    intro q hq
    by_contra hq_notin
    apply hq
    show fhatCoeff hf2 q = 0
    unfold fhatCoeff
    exact dif_neg hq_notin

/-- `Support fhat ⊆ Stilde`. -/
lemma fhat_support_subset {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Function.support (fhat hf2).coeff ⊆ Stilde hf2 := by
  intro q hq
  by_contra hq_notin
  apply hq
  change fhatCoeff hf2 q = 0
  unfold fhatCoeff
  exact dif_neg hq_notin

/-- at `s ∈ Stilde`, the `fhat` coefficient is `Cs s`. -/
lemma fhatCoeff_eq_Cs {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) : (fhat hf2).coeff s.val = Cs hf2 s := by
  change fhatCoeff hf2 s.val = _
  unfold fhatCoeff
  exact dif_pos s.property

/-! The main lemma `mk_fhat_eq_sigma_f` glues them together with
`Ideal.Quotient.eq`.

Original proof outline: by canonical T-expansion uniqueness
(`exists_canonical_T_expansion`) applied to `σ p T f` (whose canonical coefficient
is `f.coeff` via `σ_coeff_compat`), it suffices to show
`fhat - TLiftedPAdicHahnSeries.fromCoeff p T f.coeff (support_IsPWO f)
∈ TNullSeriesIdeal p T`. The difference has support contained in `f.support`, with
coefficient `OQpUn_embd p T (teichmuller p (f.coeff q)) - fhatCoeff hf2 q`:
* at `q = s ∈ Stilde`, this is `teichmuller (f.coeff s) - Cs s`, the negation of the
  `w ≥ 1` tail of `Cs s`;
* at `q ∈ f.support \ Stilde`, by `Stilde_isRepModZ_oneOverT` we have a unique
  `s ∈ Stilde` and `w ≥ 1` with `q = s.val + w/T`, and the coefficient is precisely
  `Cs_term hf2 s w` (the `w`-th tail term of `Cs s`).
The partial-sum tendency at every `g ∈ ℚ` collapses by re-indexing into the same
Cauchy tail used in `exists_Cs`. -/

/-- Structural reduction: `σ p T f = mk (fromCoeff p T f.coeff (support_IsPWO f))`.
Pure σ-machinery; the proof mimics the σ_coeff_compat strategy and uses no `fhat` data. -/
private lemma sigma_eq_mk_fromCoeff_fcoeff
    {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+) :
    σ p (T : ℕ) f = Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ))
      (TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ) (pAdicHahnSeries.coeff f)
        (support_IsPWO f)) := by
  set s_σ := (exists_canonical_T_expansion p (T : ℕ) (σ p (T : ℕ) f)).choose
    with hs_σ_def
  -- s_σ.val = pAdicHahnSeries.coeff f by σ_coeff_compat.
  have hs_σ_val : s_σ.val = pAdicHahnSeries.coeff f := σ_coeff_compat p (T : ℕ) f
  -- The canonical-T-expansion choose_spec gives the ringCon witness.
  have h_ringCon : Ideal.Quotient.ringCon (TNullSeriesIdeal p (T : ℕ))
      (σ p (T : ℕ) f).out
      (TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ) s_σ.val s_σ.prop) :=
    (exists_canonical_T_expansion p (T : ℕ) (σ p (T : ℕ) f)).choose_spec.1
  -- Quotient.sound packages the ringCon into an equality of `mk`s.
  have h1 : Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) (σ p (T : ℕ) f).out
      = Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ))
            (TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ) s_σ.val s_σ.prop) :=
    Quotient.sound h_ringCon
  -- Rewrite the `fromCoeff`'s value argument using hs_σ_val (proof irrelevance on prop).
  have h2 : TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ) s_σ.val s_σ.prop
      = TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ) (pAdicHahnSeries.coeff f)
          (support_IsPWO f) := by
    apply HahnSeries.coeff_inj.mp
    funext n
    change OQpUn_embd p (T : ℕ) (WittVector.teichmuller p (s_σ.val n)) =
        OQpUn_embd p (T : ℕ) (WittVector.teichmuller p (pAdicHahnSeries.coeff f n))
    rw [hs_σ_val]
  rw [← Ideal.Quotient.mk_out (σ p (T : ℕ) f), h1, h2]

/-! #### `Rat.isInt` helpers. -/

/-- An integer cast to `ℚ` has `Rat.isInt = true`. -/
lemma isInt_intCast' (k : ℤ) : ((k : ℚ)).isInt = true := by
  rw [Rat.isInt]; simp

/-- A natural cast to `ℚ` has `Rat.isInt = true`. -/
lemma isInt_natCast' (k : ℕ) : ((k : ℚ)).isInt = true := by
  rw [Rat.isInt]; simp

/-- `(0 : ℚ).isInt = true`. -/
lemma isInt_zero' : ((0 : ℚ)).isInt = true := by
  rw [Rat.isInt]; simp

/-- `Rat.isInt` is closed under addition. -/
lemma isInt_add' {a b : ℚ} (ha : a.isInt = true) (hb : b.isInt = true) :
    (a + b).isInt = true := by
  have ha_eq : a = (a.num : ℚ) := Rat.eq_num_of_isInt ha
  have hb_eq : b = (b.num : ℚ) := Rat.eq_num_of_isInt hb
  rw [ha_eq, hb_eq]
  have h : (a.num : ℚ) + (b.num : ℚ) = (((a.num + b.num : ℤ)) : ℚ) := by
    push_cast; ring
  rw [h]
  exact isInt_intCast' _

/-- `Rat.isInt` is closed under subtraction. -/
lemma isInt_sub' {a b : ℚ} (ha : a.isInt = true) (hb : b.isInt = true) :
    (a - b).isInt = true := by
  have ha_eq : a = (a.num : ℚ) := Rat.eq_num_of_isInt ha
  have hb_eq : b = (b.num : ℚ) := Rat.eq_num_of_isInt hb
  rw [ha_eq, hb_eq]
  have h : (a.num : ℚ) - (b.num : ℚ) = (((a.num - b.num : ℤ)) : ℚ) := by
    push_cast; ring
  rw [h]
  exact isInt_intCast' _

/-- `Rat.isInt` is closed under multiplication. -/
lemma isInt_mul' {a b : ℚ} (ha : a.isInt = true) (hb : b.isInt = true) :
    (a * b).isInt = true := by
  have ha_eq : a = (a.num : ℚ) := Rat.eq_num_of_isInt ha
  have hb_eq : b = (b.num : ℚ) := Rat.eq_num_of_isInt hb
  rw [ha_eq, hb_eq]
  have h : (a.num : ℚ) * (b.num : ℚ) = (((a.num * b.num : ℤ)) : ℚ) := by
    push_cast; ring
  rw [h]
  exact isInt_intCast' _

/-- If every term `g i` is an integer (in the `Rat.isInt` sense) and `g`'s support
is finite, then the finsum `∑ᶠ i, g i` is an integer. -/
private lemma finsum_isInt {α : Type*} {g : α → ℚ}
    (hg_supp : (Function.support g).Finite)
    (hg_int : ∀ i, (g i).isInt = true) :
    (∑ᶠ i, g i).isInt = true := by
  have hsub : Function.support g ⊆ ↑hg_supp.toFinset := by
    simp [Set.Finite.coe_toFinset]
  rw [finsum_eq_sum_of_support_subset _ hsub]
  apply Finset.sum_induction g (fun a => a.isInt = true)
  · intros a b ha hb; exact isInt_add' ha hb
  · exact isInt_zero'
  · intros i _; exact hg_int i

/-! ### helpers: unique decomposition of `f.support` along `Stilde × ℕ`. -/

/-- From `hf2.1`, every `q ∈ f.support` has at least one `d ∈ S`
with the residue clause `(d.norm p + T·q).isInt = true`. Used in
`Stilde_unique_decomposition`. -/
private lemma exists_d_for_support
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {q : ℚ} (hq_supp : q ∈ f.support) :
    ∃ d : S, ((d.val.norm p : ℚ) + (T : ℚ) * q).isInt = true := by
  have hb_mem : (-1 * (T : ℚ) * q) ∈
      ({x | ∃ q' ∈ f.support, -1 * (T : ℚ) * q' = x} : Set ℚ) :=
    ⟨q, hq_supp, rfl⟩
  obtain ⟨a, ⟨ha_mem, hint⟩, _⟩ := hf2.1 _ hb_mem
  obtain ⟨d, hd_in_S, hd_eq⟩ := ha_mem
  refine ⟨⟨d, hd_in_S⟩, ?_⟩
  have h_eq : (a : ℚ) - (-1 * (T : ℚ) * q) = (d.norm p : ℚ) + (T : ℚ) * q := by
    rw [← hd_eq]; ring
  rw [← h_eq]
  exact hint

/-- The unique decomposition `q = s.val + w/T` for `q ∈ f.support`.

Existence: take `d` as above, then `s := muQ hf2 d` is the minimum of `Sd d`; by
construction `s ≤ q`, and the difference `T·(q - s)` is a non-negative integer,
giving `w : ℕ`. Uniqueness: any two decompositions yield `s.val - s'.val ∈ (1/T)ℤ`,
which combined with the residue clauses forces `(d.norm p - d'.norm p).isInt = true`;
applying `hf2.1`'s uniqueness, both decompositions correspond to the same residue
class, hence the same `muQ` value and the same `w`. -/
private lemma Stilde_unique_decomposition
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {q : ℚ} (hq_supp : q ∈ f.support) :
    ∃! sw : ↥(Stilde hf2) × ℕ, q = sw.1.val + (sw.2 : ℚ) / (T : ℚ) := by
  classical
  have hT_pos : (0 : ℚ) < (T : ℕ) := by exact_mod_cast T.pos
  have hT_ne : ((T : ℕ) : ℚ) ≠ 0 := ne_of_gt hT_pos
  -- Existence
  obtain ⟨d, hd_int⟩ := exists_d_for_support hf2 hq_supp
  have hq_in_Sd : q ∈ Sd p f T d.val := ⟨hq_supp, hd_int⟩
  set s := muQ hf2 d with hs_def
  have hs_residue : ((d.val.norm p : ℚ) + (T : ℚ) * s).isInt = true :=
    muQ_residue hf2 d
  have hs_le_q : s ≤ q := (Sd_isWF f T d.val).min_le (Sd_nonempty hf2 d.property) hq_in_Sd
  -- Compute T·(q - s) ∈ ℕ.
  have h_diff_isInt : ((T : ℚ) * (q - s)).isInt = true := by
    have h1 : ((d.val.norm p : ℚ) + (T : ℚ) * q
              - ((d.val.norm p : ℚ) + (T : ℚ) * s)).isInt = true :=
      isInt_sub' hd_int hs_residue
    have h_eq : (d.val.norm p : ℚ) + (T : ℚ) * q
                - ((d.val.norm p : ℚ) + (T : ℚ) * s)
              = (T : ℚ) * (q - s) := by ring
    rw [← h_eq]; exact h1
  have h_diff_nonneg : 0 ≤ (T : ℚ) * (q - s) :=
    mul_nonneg hT_pos.le (sub_nonneg.mpr hs_le_q)
  -- Extract the natural number.
  set wq_int := ((T : ℚ) * (q - s)).num with hwq_def
  have h_T_eq_num : ((T : ℚ) * (q - s)) = (wq_int : ℚ) :=
    Rat.eq_num_of_isInt h_diff_isInt
  have hwq_nonneg : 0 ≤ wq_int := by
    have : (0 : ℚ) ≤ (wq_int : ℚ) := h_T_eq_num ▸ h_diff_nonneg
    exact_mod_cast this
  set wq := wq_int.toNat with hwq_nat_def
  have hwq_int_eq : (wq : ℤ) = wq_int := Int.toNat_of_nonneg hwq_nonneg
  have hwq_eq : ((T : ℚ) * (q - s)) = (wq : ℚ) := by
    rw [h_T_eq_num, ← hwq_int_eq]; push_cast; rfl
  -- Therefore q = s + wq/T.
  have h_q_decomp : q = s + (wq : ℚ) / (T : ℚ) := by
    have hqs : (q - s) = (wq : ℚ) / (T : ℚ) := by
      field_simp; linarith [hwq_eq]
    linarith
  -- Package as the existence witness.
  refine ⟨((⟨s, ⟨d, rfl⟩⟩ : ↥(Stilde hf2)), wq), h_q_decomp, ?_⟩
  rintro ⟨s', w'⟩ h_eq
  -- s' ∈ Stilde, so s' = muQ hf2 d' for some d'.
  obtain ⟨d', hd'_eq⟩ := s'.property
  -- show s' = s (equivalently s'.val = muQ hf2 d), then w' = wq.
  have hs'_le_q : (s'.val : ℚ) ≤ q := by
    rw [h_eq]
    have : (0 : ℚ) ≤ (w' : ℚ) / (T : ℚ) := div_nonneg (Nat.cast_nonneg _) hT_pos.le
    linarith
  have hs'_residue : ((d'.val.norm p : ℚ) + (T : ℚ) * s'.val).isInt = true := by
    rw [← hd'_eq]
    exact muQ_residue hf2 d'
  -- T·(q - s') = w' (a non-negative integer).
  have hTqs'_int : ((T : ℚ) * (q - s'.val)).isInt = true := by
    have h_id : (T : ℚ) * (q - s'.val) = (w' : ℚ) := by
      rw [h_eq]; field_simp; ring
    rw [h_id]; exact isInt_natCast' _
  -- (norm d) - (norm d') ∈ ℤ.
  have h_d'_int : ((d'.val.norm p : ℚ) + (T : ℚ) * q).isInt = true := by
    have h_eq2 : (d'.val.norm p : ℚ) + (T : ℚ) * q
              = ((d'.val.norm p : ℚ) + (T : ℚ) * s'.val) + (T : ℚ) * (q - s'.val) := by
      ring
    rw [h_eq2]
    exact isInt_add' hs'_residue hTqs'_int
  -- Apply hf2.1's uniqueness at b = -T·q.
  have hb_mem : (-1 * (T : ℚ) * q) ∈
      ({x | ∃ q' ∈ f.support, -1 * (T : ℚ) * q' = x} : Set ℚ) :=
    ⟨q, hq_supp, rfl⟩
  obtain ⟨a, ⟨_ha_mem, _hint⟩, ha_unique⟩ := hf2.1 _ hb_mem
  have hd_norm_in : ((d.val.norm p : ℚ)) ∈ DigitSeries.norm p '' S :=
    ⟨d.val, d.property, rfl⟩
  have hd'_norm_in : ((d'.val.norm p : ℚ)) ∈ DigitSeries.norm p '' S :=
    ⟨d'.val, d'.property, rfl⟩
  have h_d_check : ((d.val.norm p : ℚ) - (-1 * (T : ℚ) * q)).isInt = true := by
    have h_id : (d.val.norm p : ℚ) - (-1 * (T : ℚ) * q)
              = (d.val.norm p : ℚ) + (T : ℚ) * q := by ring
    rw [h_id]; exact hd_int
  have h_d'_check : ((d'.val.norm p : ℚ) - (-1 * (T : ℚ) * q)).isInt = true := by
    have h_id : (d'.val.norm p : ℚ) - (-1 * (T : ℚ) * q)
              = (d'.val.norm p : ℚ) + (T : ℚ) * q := by ring
    rw [h_id]; exact h_d'_int
  have hd_eq_a : (d.val.norm p : ℚ) = a :=
    ha_unique _ ⟨hd_norm_in, h_d_check⟩
  have hd'_eq_a : (d'.val.norm p : ℚ) = a :=
    ha_unique _ ⟨hd'_norm_in, h_d'_check⟩
  have h_norm_eq : (d.val.norm p : ℚ) = (d'.val.norm p : ℚ) := hd_eq_a.trans hd'_eq_a.symm
  -- Now muQ hf2 d = muQ hf2 d' because Sd depends only on d.norm p.
  have h_Sd_eq : Sd p f T d.val = Sd p f T d'.val := by
    unfold Sd
    congr 1
    ext q'
    simp only [Set.mem_ofPred_eq, h_norm_eq]
  have h_mu_eq : muQ hf2 d = muQ hf2 d' := by
    unfold muQ
    have hd_ne := Sd_nonempty hf2 d.property
    have hd'_ne := Sd_nonempty hf2 d'.property
    apply le_antisymm
    · refine (Sd_isWF f T d.val).min_le hd_ne ?_
      rw [h_Sd_eq]
      exact (Sd_isWF f T d'.val).min_mem hd'_ne
    · refine (Sd_isWF f T d'.val).min_le hd'_ne ?_
      rw [← h_Sd_eq]
      exact (Sd_isWF f T d.val).min_mem hd_ne
  have hs_s'_val : s'.val = s := by
    have h1 : s'.val = muQ hf2 d' := hd'_eq.symm
    have h2 : muQ hf2 d' = s := h_mu_eq.symm.trans hs_def.symm
    exact h1.trans h2
  -- Now show w' = wq.
  have h_w_eq : (w' : ℚ) = (wq : ℚ) := by
    have h1 : q - s = (w' : ℚ) / (T : ℚ) := by
      rw [hs_s'_val] at h_eq; linarith
    have h2 : q - s = (wq : ℚ) / (T : ℚ) := by linarith [h_q_decomp]
    have h12 : (w' : ℚ) / (T : ℚ) = (wq : ℚ) / (T : ℚ) := h1.symm.trans h2
    have hT_ne_R : (T : ℚ) ≠ 0 := hT_ne
    field_simp at h12
    exact h12
  have h_w_nat_eq : w' = wq := by exact_mod_cast h_w_eq
  have h_s_subtype_eq : s' = (⟨s, ⟨d, rfl⟩⟩ : ↥(Stilde hf2)) := by
    apply Subtype.ext
    exact hs_s'_val
  exact Prod.ext h_s_subtype_eq h_w_nat_eq

/-- Stilde elements live in f.support (re-export of `Stilde_subset_support`). -/
private lemma Stilde_decomp_at_self
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    s.val ∈ f.support := Stilde_subset_support hf2 s.property

/-- If `q ∈ f.support` has decomposition `(s, w)` with `w ≥ 1`, then `q ∉ Stilde`. -/
private lemma not_Stilde_of_pos_w
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {q : ℚ} (hq_supp : q ∈ f.support)
    {s : ↥(Stilde hf2)} {w : ℕ}
    (hq_eq : q = s.val + (w : ℚ) / (T : ℚ)) (hw_pos : w ≥ 1) :
    q ∉ Stilde hf2 := by
  intro hq_stil
  obtain ⟨_unique_sw, _, h_unique⟩ := Stilde_unique_decomposition hf2 hq_supp
  have h1 : q = q + (0 : ℕ) / (T : ℚ) := by simp
  have h_eq1 : (((⟨q, hq_stil⟩ : ↥(Stilde hf2)), (0 : ℕ)) : ↥(Stilde hf2) × ℕ)
                = _unique_sw := h_unique _ h1
  have h_eq2 : ((s, w) : ↥(Stilde hf2) × ℕ) = _unique_sw := h_unique _ hq_eq
  have h_combined : (((⟨q, hq_stil⟩ : ↥(Stilde hf2)), (0 : ℕ)) : ↥(Stilde hf2) × ℕ)
                    = (s, w) := h_eq1.trans h_eq2.symm
  have h_w_zero : w = 0 := (Prod.mk.injEq _ _ _ _).mp h_combined |>.2.symm
  omega

/-! ### Coefficient formula for the difference. -/

/-- At `s ∈ Stilde`, the diff coefficient equals `Cs hf2 s - Cs_term hf2 s 0`. -/
private lemma fhat_diff_coeff_Stilde
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    (fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff s.val
      = Cs hf2 s - Cs_term hf2 s 0 := by
  rw [HahnSeries.coeff_sub, fhatCoeff_eq_Cs hf2 s]
  -- Goal: Cs hf2 s - (fromCoeff ...).coeff s.val = Cs hf2 s - Cs_term hf2 s 0.
  -- (fromCoeff p T f.coeff h).coeff s.val = OQpUn_embd p T (teichmuller p (f.coeff s.val))
  -- Cs_term hf2 s 0 = OQpUn_embd p T (teich p (f.coeff (s.val + 0/T))) * (pInvT p T)^0
  --                = OQpUn_embd p T (teich p (f.coeff s.val))
  unfold Cs_term
  have h0 : (s.val + (0 : ℕ) / (T : ℚ)) = s.val := by simp
  rw [h0, pow_zero, mul_one]
  rfl

/-- At `q ∈ f.support \ Stilde`, the diff coefficient equals
`-(OQpUn_embd p T (teichmuller p (f.coeff q)))`. -/
private lemma fhat_diff_coeff_outside_Stilde
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {q : ℚ} (hq_not_Stilde : q ∉ Stilde hf2) :
    (fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff q
      = -(OQpUn_embd p (T : ℕ) (WittVector.teichmuller p (pAdicHahnSeries.coeff f q))) := by
  rw [HahnSeries.coeff_sub]
  have h_fhat_zero : (fhat hf2).coeff q = 0 := by
    change fhatCoeff hf2 q = 0
    unfold fhatCoeff
    exact dif_neg hq_not_Stilde
  rw [h_fhat_zero, zero_sub]
  rfl

/-- At `q ∉ f.support`, the diff coefficient is 0. -/
private lemma fhat_diff_coeff_outside_support
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {q : ℚ} (hq_not_supp : q ∉ f.support) :
    (fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff q = 0 := by
  rw [HahnSeries.coeff_sub]
  have h_f_coeff_zero : pAdicHahnSeries.coeff f q = 0 := by
    by_contra h
    exact hq_not_supp h
  have h_fhat_zero : (fhat hf2).coeff q = 0 := by
    change fhatCoeff hf2 q = 0
    unfold fhatCoeff
    by_cases hq_stil : q ∈ Stilde hf2
    · exfalso
      apply hq_not_supp
      exact Stilde_subset_support hf2 hq_stil
    · exact dif_neg hq_stil
  have h_fromCoeff_zero : (TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff q = 0 := by
    change OQpUn_embd p (T : ℕ) (WittVector.teichmuller p (pAdicHahnSeries.coeff f q)) = 0
    rw [h_f_coeff_zero, WittVector.teichmuller_zero, map_zero]
  rw [h_fhat_zero, h_fromCoeff_zero, sub_zero]

/-! ### Analytical helpers for `fhat_diff_isTNullSeries` for the T-null-series argument.

These lemmas extract the `Cs s - Cs_partial s N` valuation tail bound, which is
the key analytical fact making the Tendsto-zero argument work.  All proofs use only
the `Cs_tendsto` interface plus the closed-ball-is-closed property of the valuation
topology on `ℚᵘⁿ_[p,T]`. -/

/-- `Valued.v (algebraMap (Cs hf2 s - Cs_partial hf2 s N)) ≤ ofAdd(-N)`.
Obtained from the Cauchy bound `Cs_partial_diff_alg_v_le` by taking the limit as
`N' → ∞`, using `Cs_tendsto` plus `Valued.isClosed_closedBall`. -/
private lemma Cs_diff_alg_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (N : ℕ) :
    Valued.v (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
              (Cs hf2 s - Cs_partial hf2 s N))
      ≤ ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _) := by
  -- algebraMap (Cs_partial s N') - algebraMap (Cs_partial s N) tends to
  -- algebraMap (Cs s) - algebraMap (Cs_partial s N) = algebraMap (Cs s - Cs_partial s N)
  -- as N' → ∞.  Eventually this value is in the closed ball; closed-ball-is-closed gives the result
  set target : ℚᵘⁿ_[p, (T : ℕ)] :=
    algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs hf2 s - Cs_partial hf2 s N)
    with htarget_def
  set ball : Set (ℚᵘⁿ_[p, (T : ℕ)]) :=
    { x | Valued.v x ≤ ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _) }
    with hball_def
  have h_ball_closed : IsClosed ball := by
    have hbridge : ball =
        {x : ℚᵘⁿ_[p, (T : ℕ)] |
          Valued.v.restrict x ≤ Valued.v.restrict ((pInvTQ p (T : ℕ)) ^ (N : ℤ))} := by
      ext x
      rw [hball_def, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
        Valuation.restrict_le_iff_le_embedding, Valuation.embedding_restrict,
        valued_v_pInvT_zpow]
    rw [hbridge]
    exact Valued.isClosed_closedBall _ _
  have h_tendsto :
      Filter.Tendsto
        (fun N' : ℕ => algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                        (Cs_partial hf2 s N' - Cs_partial hf2 s N))
        Filter.atTop (nhds target) := by
    have h_sub_tendsto :
        Filter.Tendsto
          (fun N' : ℕ => algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N')
                        - algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))
          Filter.atTop (nhds (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs hf2 s)
                              - algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                                  (Cs_partial hf2 s N))) :=
      (Cs_tendsto hf2 s).sub tendsto_const_nhds
    have h_target_eq :
        target =
          algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs hf2 s)
            - algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N) := by
      rw [htarget_def, map_sub]
    rw [h_target_eq]
    convert h_sub_tendsto using 1
    funext N'
    exact map_sub _ _ _
  have h_eventually : ∀ᶠ N' : ℕ in Filter.atTop,
      algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
        (Cs_partial hf2 s N' - Cs_partial hf2 s N) ∈ ball := by
    filter_upwards [Filter.eventually_ge_atTop N] with N' hN'
    exact Cs_partial_diff_alg_v_le hf2 s hN'
  exact h_ball_closed.mem_of_tendsto h_tendsto h_eventually

/-- Per-`s` slice collapse (inner-sum identity).

For fixed `s ∈ Stilde hf2`, an integer `n_s : ℤ`, and an `M : ℕ`, the algebraic
identity `(pInvTQ)^w · algebraMap (diff.coeff (s.val + w/T)) =
algebraMap ((pInvT)^w · diff.coeff (...))`
holds at each `w`, and the inner sum collapses:
`∑_{w = 0}^{W} (pInvTQ)^w · algebraMap (diff.coeff (s.val + w/T))
  = algebraMap (Cs hf2 s - Cs_partial hf2 s (W + 1))`. -/
private lemma per_s_inner_sum_eq
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (W : ℕ) :
    ∑ w ∈ Finset.range (W + 1),
        (pInvTQ p (T : ℕ)) ^ (w : ℤ) *
          algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
            ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                          (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
              (s.val + (w : ℚ) / T))
      = algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
            (Cs hf2 s - Cs_partial hf2 s (W + 1)) := by
  -- Step 1: Pull algebraMap outside the sum by rewriting (pInvTQ)^w = algebraMap (pInvT)^w.
  have h_pInvTQ_eq_alg : ∀ w : ℕ, (pInvTQ p (T : ℕ)) ^ (w : ℤ) =
      algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) ((pInvT p (T : ℕ)) ^ w) := by
    intro w
    rw [show (pInvTQ p (T : ℕ)) ^ (w : ℤ) = (pInvTQ p (T : ℕ)) ^ w from zpow_natCast _ _, map_pow]
    rfl
  have h_step1 :
      ∑ w ∈ Finset.range (W + 1),
        (pInvTQ p (T : ℕ)) ^ (w : ℤ) *
          algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
            ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                          (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
              (s.val + (w : ℚ) / T))
      = algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
          (∑ w ∈ Finset.range (W + 1),
            (pInvT p (T : ℕ)) ^ w *
              ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                            (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
                (s.val + (w : ℚ) / T))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [h_pInvTQ_eq_alg, map_mul]
  rw [h_step1]
  -- Step 2: Show the inner sum equals Cs s - Cs_partial s (W + 1) in ℤᵘⁿ_[p,T].
  congr 1
  -- Split off w = 0 from the sum.
  rw [Finset.sum_range_succ' (fun w => (pInvT p (T : ℕ)) ^ w *
        ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                      (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
          (s.val + (w : ℚ) / T))) W]
  -- Now we have: ∑_{w' ∈ range W} (pInvT)^{w'+1} · diff.coeff(s.val + (w'+1)/T) + (pInvT)^0
  -- · diff.coeff(s.val)
  -- For w = 0:
  have h_w0 : (pInvT p (T : ℕ)) ^ 0 *
      ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                    (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
        (s.val + ((0 : ℕ) : ℚ) / T))
      = Cs hf2 s - Cs_term hf2 s 0 := by
    rw [pow_zero, one_mul]
    have h0 : (s.val + ((0 : ℕ) : ℚ) / T) = s.val := by simp
    rw [h0]
    exact fhat_diff_coeff_Stilde hf2 s
  rw [h_w0]
  -- For w' ∈ range W (i.e., w = w' + 1 ≥ 1):
  have h_w_ge1 : ∀ w' ∈ Finset.range W,
      (pInvT p (T : ℕ)) ^ (w' + 1) *
        ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                      (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
          (s.val + ((w' + 1 : ℕ) : ℚ) / T))
      = -(Cs_term hf2 s (w' + 1)) := by
    intro w' _
    by_cases hsupp : s.val + ((w' + 1 : ℕ) : ℚ) / T ∈ f.support
    · -- In supp. Since w'+1 ≥ 1, by not_Stilde_of_pos_w, s.val + (w'+1)/T ∉ Stilde.
      have h_not_Stilde : (s.val + ((w' + 1 : ℕ) : ℚ) / T) ∉ Stilde hf2 := by
        apply not_Stilde_of_pos_w hf2 hsupp (s := s) (w := w' + 1) rfl
        omega
      rw [fhat_diff_coeff_outside_Stilde hf2 h_not_Stilde]
      unfold Cs_term
      ring
    · -- Not in supp. diff.coeff = 0, and Cs_term s (w'+1) = 0.
      rw [fhat_diff_coeff_outside_support hf2 hsupp, mul_zero]
      have h_fc_zero : f.coeff (s.val + ((w' + 1 : ℕ) : ℚ) / T) = 0 := by
        by_contra h
        exact hsupp h
      unfold Cs_term
      rw [h_fc_zero, WittVector.teichmuller_zero, map_zero, zero_mul, neg_zero]
  rw [Finset.sum_congr rfl h_w_ge1]
  rw [Finset.sum_neg_distrib]
  unfold Cs_partial
  -- Now: -∑_{w' ∈ range W} Cs_term s (w'+1) + (Cs s - Cs_term s 0)
  --      = Cs s - ∑_{w ∈ range (W+1)} Cs_term s w
  rw [Finset.sum_range_succ' (fun w => Cs_term hf2 s w) W]
  ring

/-- Per-`s` slice valuation bound. For fixed `s ∈ Stilde hf2`, an integer
`n_s : ℤ`, and `W : ℕ`, the per-`s` slice `(pInvTQ)^{n_s} · algebraMap(Cs s - Cs_partial s (W+1))`
has valuation `≤ ofAdd(-(n_s + W + 1))`. -/
private lemma per_s_slice_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (n_s : ℤ) (W : ℕ) :
    Valued.v ((pInvTQ p (T : ℕ)) ^ n_s *
              algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                (Cs hf2 s - Cs_partial hf2 s (W + 1)))
      ≤ ((Multiplicative.ofAdd (-(n_s + (W : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) := by
  rw [Valuation.map_mul, valued_v_pInvT_zpow]
  have h_alg : Valued.v (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
              (Cs hf2 s - Cs_partial hf2 s (W + 1)))
      ≤ ((Multiplicative.ofAdd (-((W + 1 : ℕ) : ℤ)) : Multiplicative ℤ) : WithZero _) :=
    Cs_diff_alg_v_le hf2 s (W + 1)
  have h_cast : ((W + 1 : ℕ) : ℤ) = (W : ℤ) + 1 := by push_cast; ring
  rw [h_cast] at h_alg
  calc ((Multiplicative.ofAdd (-n_s : ℤ) : Multiplicative ℤ) : WithZero _) *
          Valued.v (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
            (Cs hf2 s - Cs_partial hf2 s (W + 1)))
      ≤ ((Multiplicative.ofAdd (-n_s : ℤ) : Multiplicative ℤ) : WithZero _) *
          ((Multiplicative.ofAdd (-((W : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) :=
        mul_le_mul' (le_refl _) h_alg
    _ = ((Multiplicative.ofAdd (-n_s + -((W : ℤ) + 1)) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
        rw [← WithZero.coe_mul, ← ofAdd_add]
    _ = ((Multiplicative.ofAdd (-(n_s + (W : ℤ) + 1)) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
        congr 2; ring

/-! ### Body of `fhat_diff_isTNullSeries`. -/

/-- Per-`M` valuation bound for the `TfiniteBelow`-indexed partial sum of `diff`.

For each `g : ℚ` and `M : ℕ`, the partial sum
`P_M = ∑_{n ∈ TfiniteBelow diff g M} (pInvTQ)^n · algebraMap(diff.coeff(g + n/T))`
has valuation bounded by `ofAdd(-(K+1))` where `K = ⌊T·(M - g)⌋`.

Strategy:
1. For each `n ∈ TfiniteBelow`, by `Stilde_unique_decomposition`, `g + n/T = s.val + w/T`
   for a unique `(s, w) ∈ Stilde × ℕ`. Define `s_of n` and `w_of n`.
2. Let `Stilde_used := image (s_of)` (a Finset). For each `s ∈ Stilde_used`, define
   `n_s := T(s.val - g)` (an integer, since `T(s.val - g) = n - w ∈ ℤ`) and
   `W_s := ⌊T(M - s.val)⌋.toNat`.
3. Use `Finset.sum_bij'` to re-index
`P_M = ∑_{(s, w) ∈ image} (pInvTQ)^{n_s + w} · algebraMap(diff.coeff(s.val + w/T))`
   over a sigma `Stilde_used.sigma w_range`.
4. Extend the sum to all of `Stilde_used.sigma w_range` (added terms have zero coeff).
5. Apply `per_s_inner_sum_eq` per `s`:
inner sum = `algebraMap(Cs s - Cs_partial s (W_s + 1))`.
6. Apply `per_s_slice_v_le` + arithmetic identity `n_s + W_s = K` for the per-`s`
   valuation bound `ofAdd(-(n_s + W_s + 1)) = ofAdd(-(K + 1))`.
7. Apply `Valuation.map_sum_le` for the outer ultrametric. -/
private lemma fhat_diff_partial_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (g : ℚ) (M : ℕ) :
    Valued.v (∑ n : Set.Finite.toFinset (TfiniteBelow p (T : ℕ)
                  (fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                    (pAdicHahnSeries.coeff f) (support_IsPWO f)) g M),
              (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
                algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                  ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                    (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
                    (g + (n.val : ℚ) / T))) ≤
      ((Multiplicative.ofAdd (-(⌊(T : ℚ) * ((M : ℚ) - g)⌋ + 1) : ℤ) :
        Multiplicative ℤ) : WithZero _) := by
  classical
  set diff : TLiftedPAdicHahnSeries p (T : ℕ) :=
    fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                (pAdicHahnSeries.coeff f) (support_IsPWO f) with hdiff_def
  set K : ℤ := ⌊(T : ℚ) * ((M : ℚ) - g)⌋ with hK_def
  have hT_pos : (0 : ℚ) < (T : ℕ) := by exact_mod_cast T.pos
  have hT_ne : ((T : ℕ) : ℚ) ≠ 0 := ne_of_gt hT_pos
  -- For each n ∈ TfiniteBelow.toFinset, g + n/T ∈ f.support.
  have h_n_supp : ∀ n : ℤ, n ∈ Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M) →
      g + (n : ℚ) / (T : ℕ) ∈ f.support := by
    intro n hn
    have hn_data : g + (n : ℚ) / (T : ℕ) ≤ M ∧ diff.coeff (g + (n : ℚ) / (T : ℕ)) ≠ 0 :=
      (Set.Finite.mem_toFinset (hs := TfiniteBelow p (T : ℕ) diff g M) (a := n)).mp hn
    by_contra h
    exact hn_data.2 (fhat_diff_coeff_outside_support hf2 h)
  -- For each n ∈ TfiniteBelow.toFinset, also: g + n/T ≤ M.
  have h_n_le_M : ∀ n : ℤ, n ∈ Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M) →
      g + (n : ℚ) / (T : ℕ) ≤ M := by
    intro n hn
    exact ((Set.Finite.mem_toFinset (hs := TfiniteBelow p (T : ℕ) diff g M) (a := n)).mp hn).1
  -- Define the bijection map on the attached set.
  let sw_choose : (n : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M))) →
      ↥(Stilde hf2) × ℕ :=
    fun n => (Stilde_unique_decomposition hf2 (h_n_supp n.val n.property)).choose
  -- Property of sw_choose: g + n.val/T = (sw_choose n).1.val + (sw_choose n).2 / T.
  have h_sw_eq : ∀ n : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)),
      g + (n.val : ℚ) / (T : ℕ) = ((sw_choose n).1).val +
                                   ((sw_choose n).2 : ℚ) / (T : ℕ) :=
    fun n => (Stilde_unique_decomposition hf2 (h_n_supp n.val n.property)).choose_spec.1
  -- Uniqueness of sw_choose.
  have h_sw_unique : ∀ n : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)),
      ∀ sw', g + (n.val : ℚ) / (T : ℕ) = sw'.1.val + (sw'.2 : ℚ) / (T : ℕ) →
        sw' = sw_choose n :=
    fun n sw' h_eq => (Stilde_unique_decomposition hf2 (h_n_supp n.val n.property)).choose_spec.2
      sw' h_eq
  -- n.val = T·(s.val - g) + w (residue arithmetic).
  have h_n_decomp : ∀ n : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)),
      (n.val : ℚ) = (T : ℕ) * (((sw_choose n).1).val - g) + ((sw_choose n).2 : ℚ) := by
    intro n
    have h1 := h_sw_eq n
    have h2 : (n.val : ℚ) / (T : ℕ) = (((sw_choose n).1).val - g) +
                                       ((sw_choose n).2 : ℚ) / (T : ℕ) := by linarith
    have h3 : (T : ℕ) * ((n.val : ℚ) / (T : ℕ)) =
              (T : ℕ) * ((((sw_choose n).1).val - g) + ((sw_choose n).2 : ℚ) / (T : ℕ)) := by
      rw [h2]
    rw [mul_div_cancel₀ _ hT_ne] at h3
    rw [h3]
    field_simp
  -- T·(s.val - g) is an integer for s in image.
  have h_T_sub_int : ∀ n : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)),
      (T : ℕ) * (((sw_choose n).1).val - g) = (n.val - ((sw_choose n).2 : ℤ) : ℤ) := by
    intro n
    have h := h_n_decomp n
    have : (n.val : ℚ) - ((sw_choose n).2 : ℚ) = (T : ℕ) * (((sw_choose n).1).val - g) := by
      linarith
    rw [← this]; push_cast; ring
  -- Define Stilde_used: image of the s coordinate.
  set Stilde_used : Finset ↥(Stilde hf2) :=
    (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach.image
      (fun n => (sw_choose n).1) with hStilde_used_def
  -- For each s ∈ Stilde_used, define n_s : ℤ.
  -- n_s := T·(s.val - g).num (the integer value, which exists for s ∈ Stilde_used).
  set n_s_int : ↥(Stilde hf2) → ℤ := fun s => ((T : ℚ) * (s.val - g)).num with hn_s_def
  -- W_s : ℕ := ⌊T·(M - s.val)⌋.toNat.
  set W_s : ↥(Stilde hf2) → ℕ := fun s => ⌊(T : ℚ) * ((M : ℚ) - s.val)⌋.toNat with hW_s_def
  -- For s ∈ Stilde_used: properties.
  have h_used_isInt : ∀ s ∈ Stilde_used,
      ((T : ℕ) * (s.val - g) : ℚ) = (n_s_int s : ℚ) := by
    intro s hs
    obtain ⟨n, hn_mem, hn_eq⟩ := Finset.mem_image.mp hs
    have h := h_T_sub_int n
    have hn_eq' : (sw_choose n).1 = s := hn_eq
    rw [hn_eq'] at h
    -- h : ↑↑T * (↑s - g) = ↑(↑n - ↑(sw_choose n).2)
    have hT_sval_Q : ((T : ℚ) * (s.val - g)) = ((n.val - ((sw_choose n).2 : ℤ) : ℤ) : ℚ) := by
      have : ((T : ℕ) : ℚ) = (T : ℚ) := rfl
      exact h
    have h_isInt : ((T : ℚ) * (s.val - g)).isInt = true := by
      rw [hT_sval_Q]; exact isInt_intCast' _
    have h_num_val := Rat.eq_num_of_isInt h_isInt
    -- h_num_val : ((T : ℚ) * (s.val - g)) = (((T : ℚ) * (s.val - g)).num : ℚ)
    change ((T : ℕ) * (s.val - g) : ℚ) = (((T : ℚ) * (s.val - g)).num : ℚ)
    calc ((T : ℕ) * (s.val - g) : ℚ)
        = ((T : ℚ) * (s.val - g)) := by ring
      _ = (((T : ℚ) * (s.val - g)).num : ℚ) := h_num_val
  -- For s ∈ Stilde_used: s.val ≤ M.
  have h_used_sval_le : ∀ s ∈ Stilde_used, (s.val : ℚ) ≤ M := by
    intro s hs
    obtain ⟨n, hn_mem, hn_eq⟩ := Finset.mem_image.mp hs
    have h_le := h_n_le_M n.val n.property
    have h_decomp := h_sw_eq n
    rw [hn_eq] at h_decomp
    have h_w_nonneg : 0 ≤ ((sw_choose n).2 : ℚ) / (T : ℕ) := by
      apply div_nonneg
      · exact_mod_cast Nat.zero_le _
      · exact hT_pos.le
    linarith
  -- For s ∈ Stilde_used: arithmetic identity n_s + W_s = K.
  have h_used_arith : ∀ s ∈ Stilde_used,
      n_s_int s + (W_s s : ℤ) = K := by
    intro s hs
    have h_int := h_used_isInt s hs
    have h_le := h_used_sval_le s hs
    -- W_s s = ⌊T(M - s.val)⌋.toNat
    -- For s.val ≤ M, T(M - s.val) ≥ 0, so ⌊T(M - s.val)⌋ ≥ 0, so W_s s = ⌊T(M - s.val)⌋.
    have h_TMsval_nonneg : (0 : ℚ) ≤ (T : ℕ) * ((M : ℚ) - s.val) := by
      apply mul_nonneg hT_pos.le
      linarith
    have h_floor_nonneg : 0 ≤ ⌊(T : ℚ) * ((M : ℚ) - s.val)⌋ := by
      exact Int.floor_nonneg.mpr (by exact_mod_cast h_TMsval_nonneg)
    have h_W_s_eq : (W_s s : ℤ) = ⌊(T : ℚ) * ((M : ℚ) - s.val)⌋ := by
      change (⌊(T : ℚ) * ((M : ℚ) - s.val)⌋.toNat : ℤ) = ⌊(T : ℚ) * ((M : ℚ) - s.val)⌋
      exact Int.toNat_of_nonneg h_floor_nonneg
    rw [h_W_s_eq]
    -- Use n_s_plus_W_s_eq_floor style: T(M-g) = T(s.val-g) + T(M-s.val) = n_s + T(M-s.val).
    have h_eq : (T : ℚ) * ((M : ℚ) - g) = (n_s_int s : ℚ) + (T : ℚ) * ((M : ℚ) - s.val) := by
      have : (T : ℚ) * ((M : ℚ) - g) =
          (T : ℚ) * (s.val - g) + (T : ℚ) * ((M : ℚ) - s.val) := by ring
      rw [this]
      have h_int' : ((T : ℕ) * (s.val - g) : ℚ) = (n_s_int s : ℚ) := h_int
      rw [show ((T : ℚ) * (s.val - g)) = ((T : ℕ) * (s.val - g) : ℚ) from by ring]
      rw [h_int']
    rw [hK_def]
    rw [h_eq]
    have := Int.floor_intCast_add (n_s_int s) ((T : ℚ) * ((M : ℚ) - s.val))
    linarith
  -- For s ∈ Stilde_used: (Cs hf2 s - Cs_partial hf2 s (W_s s + 1)) bounds for per-s slice.
  -- Apply per_s_slice_v_le.
  have h_used_per_s_bound : ∀ s ∈ Stilde_used,
      Valued.v ((pInvTQ p (T : ℕ)) ^ (n_s_int s) *
                algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                  (Cs hf2 s - Cs_partial hf2 s (W_s s + 1))) ≤
      ((Multiplicative.ofAdd (-(K + 1)) : Multiplicative ℤ) : WithZero _) := by
    intro s hs
    have h_arith := h_used_arith s hs
    have h_slice := per_s_slice_v_le hf2 s (n_s_int s) (W_s s)
    have h_eq : (n_s_int s + (W_s s : ℤ) + 1 : ℤ) = K + 1 := by linarith
    rw [h_eq] at h_slice
    exact h_slice
  -- Step: Show the sum identity.
  -- For each n ∈ TfiniteBelow, the term equals (pInvTQ)^{n.val} · algebraMap(diff.coeff(g + n/T))
  --   = (pInvTQ)^{n_s_int s + (sw_choose n).2} · algebraMap(diff.coeff(s.val + w/T))
  -- where s = (sw_choose n).1, w = (sw_choose n).2.
  -- F : value at a Sigma pair.
  let F : (Σ _ : ↥(Stilde hf2), ℕ) → ℚᵘⁿ_[p, (T : ℕ)] := fun p_sig =>
    (pInvTQ p (T : ℕ)) ^ (n_s_int p_sig.1 + (p_sig.2 : ℤ)) *
      algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
        (diff.coeff (p_sig.1.val + (p_sig.2 : ℚ) / (T : ℕ)))
  -- sigma_of: the indexing function on the subtype.
  let sigma_of : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)) →
      Σ _ : ↥(Stilde hf2), ℕ :=
    fun n => ⟨(sw_choose n).1, (sw_choose n).2⟩
  -- F (sigma_of n) equals the original summand.
  have h_F_eq : ∀ n : ↥(Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)),
      F (sigma_of n) = (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
        algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
          (diff.coeff (g + (n.val : ℚ) / (T : ℕ))) := by
    intro n
    have hs_used : (sw_choose n).1 ∈ Stilde_used :=
      Finset.mem_image.mpr ⟨n, Finset.mem_attach _ _, rfl⟩
    have h_int := h_used_isInt _ hs_used
    have h_T_sub := h_T_sub_int n
    have h_int_cast : (n_s_int (sw_choose n).1 : ℚ) =
        ((n.val - ((sw_choose n).2 : ℤ) : ℤ) : ℚ) := by
      rw [← h_int]; exact_mod_cast h_T_sub
    have h_n_eq : n_s_int (sw_choose n).1 + ((sw_choose n).2 : ℤ) = (n.val : ℤ) := by
      have : (n_s_int (sw_choose n).1 : ℤ) = n.val - ((sw_choose n).2 : ℤ) := by
        exact_mod_cast h_int_cast
      omega
    have h_q_eq : (sw_choose n).1.val + ((sw_choose n).2 : ℚ) / (T : ℕ) =
        g + (n.val : ℚ) / (T : ℕ) := (h_sw_eq n).symm
    change (pInvTQ p (T : ℕ)) ^ (n_s_int (sw_choose n).1 + ((sw_choose n).2 : ℤ)) *
      algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
        (diff.coeff ((sw_choose n).1.val + ((sw_choose n).2 : ℚ) / (T : ℕ))) = _
    rw [h_n_eq, h_q_eq]
  -- sigma_of is injective.
  have h_sigma_inj : ∀ n₁ ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach,
      ∀ n₂ ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach,
      sigma_of n₁ = sigma_of n₂ → n₁ = n₂ := by
    intro n₁ _ n₂ _ h_eq
    have h_decomp_1 := h_sw_eq n₁
    have h_decomp_2 := h_sw_eq n₂
    have h_1 : (sw_choose n₁).1 = (sw_choose n₂).1 := by
      have : (sigma_of n₁).1 = (sigma_of n₂).1 := by rw [h_eq]
      exact this
    have h_2 : (sw_choose n₁).2 = (sw_choose n₂).2 := by
      have h_p1 : (sigma_of n₁).1 = (sigma_of n₂).1 := by rw [h_eq]
      have h_p2 : HEq (sigma_of n₁).2 (sigma_of n₂).2 := by rw [h_eq]
      have : HEq ((sw_choose n₁).2) ((sw_choose n₂).2) := h_p2
      exact eq_of_heq this
    apply Subtype.ext
    have h_q_eq : g + (n₁.val : ℚ) / (T : ℕ) = g + (n₂.val : ℚ) / (T : ℕ) := by
      rw [h_decomp_1, h_decomp_2, h_1, h_2]
    have : (n₁.val : ℚ) = (n₂.val : ℚ) := by
      have h_div : (n₁.val : ℚ) / (T : ℕ) = (n₂.val : ℚ) / (T : ℕ) := by linarith
      field_simp at h_div; exact h_div
    exact_mod_cast this
  -- sigma_of maps into FullSigma = Stilde_used.sigma w_range.
  have h_sigma_mem : ∀ n ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach,
      sigma_of n ∈ Stilde_used.sigma (fun s : ↥(Stilde hf2) => Finset.range (W_s s + 1)) := by
    intro n _
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨n, Finset.mem_attach _ _, rfl⟩
    · rw [Finset.mem_range]
      have hs_used : (sw_choose n).1 ∈ Stilde_used :=
        Finset.mem_image.mpr ⟨n, Finset.mem_attach _ _, rfl⟩
      have h_n_M := h_n_le_M n.val n.property
      have h_decomp := h_sw_eq n
      have h_w_le : ((sw_choose n).2 : ℚ) / (T : ℕ) ≤ (M : ℚ) - (sw_choose n).1.val := by linarith
      have h_w_le' : ((sw_choose n).2 : ℚ) ≤ (T : ℚ) * ((M : ℚ) - (sw_choose n).1.val) := by
        have h_div_le := (div_le_iff₀ hT_pos).mp h_w_le
        linarith
      have h_w_int : ((sw_choose n).2 : ℤ) ≤ ⌊(T : ℚ) * ((M : ℚ) - (sw_choose n).1.val)⌋ :=
        Int.le_floor.mpr (by exact_mod_cast h_w_le')
      have h_floor_nonneg : 0 ≤ ⌊(T : ℚ) * ((M : ℚ) - (sw_choose n).1.val)⌋ := by
        have h_sval_le : ((sw_choose n).1.val : ℚ) ≤ M := h_used_sval_le _ hs_used
        apply Int.floor_nonneg.mpr
        apply mul_nonneg hT_pos.le; linarith
      have h_toNat_eq : ((W_s (sw_choose n).1 : ℕ) : ℤ) =
          ⌊(T : ℚ) * ((M : ℚ) - (sw_choose n).1.val)⌋ :=
        Int.toNat_of_nonneg h_floor_nonneg
      have h_final : (sw_choose n).2 ≤ W_s (sw_choose n).1 := by
        have h : ((sw_choose n).2 : ℤ) ≤ ((W_s (sw_choose n).1 : ℕ) : ℤ) := by
          rw [h_toNat_eq]; exact h_w_int
        exact_mod_cast h
      change (sw_choose n).2 < W_s (sw_choose n).1 + 1
      omega
  -- For p ∈ FullSigma \ Image(sigma_of), F(p) = 0.
  have h_zero_outside : ∀ q_sig ∈ Stilde_used.sigma
      (fun s : ↥(Stilde hf2) => Finset.range (W_s s + 1)),
      q_sig ∉ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach.image sigma_of →
      F q_sig = 0 := by
    intro q_sig hq_sig h_not_im
    rcases q_sig with ⟨s, w⟩
    have hq_data := Finset.mem_sigma.mp hq_sig
    have hs_used : s ∈ Stilde_used := hq_data.1
    have hw_range : w ∈ Finset.range (W_s s + 1) := hq_data.2
    have hw_le_W : w ≤ W_s s := by
      have := Finset.mem_range.mp hw_range
      omega
    have h_sval_le_M_val : ((s.val : ℚ) + (w : ℚ) / (T : ℕ)) ≤ M := by
      have h_W_eq : ((W_s s : ℕ) : ℤ) = ⌊(T : ℚ) * ((M : ℚ) - s.val)⌋ := by
        apply Int.toNat_of_nonneg
        apply Int.floor_nonneg.mpr
        apply mul_nonneg hT_pos.le
        have := h_used_sval_le _ hs_used; linarith
      have h_w_le_floor : (w : ℤ) ≤ ⌊(T : ℚ) * ((M : ℚ) - s.val)⌋ := by
        rw [← h_W_eq]; exact_mod_cast hw_le_W
      have h_w_le_T : (w : ℚ) ≤ (T : ℚ) * ((M : ℚ) - s.val) := by
        have := Int.le_floor.mp h_w_le_floor
        exact_mod_cast this
      have h_div : (w : ℚ) / (T : ℕ) ≤ (M : ℚ) - s.val := by
        rw [div_le_iff₀ hT_pos]
        have h_w_le_T' : (w : ℚ) ≤ ((T : ℕ) : ℚ) * ((M : ℚ) - s.val) := h_w_le_T
        linarith
      linarith
    by_cases h_coeff : diff.coeff (s.val + (w : ℚ) / (T : ℕ)) = 0
    · change (pInvTQ p (T : ℕ)) ^ (n_s_int s + (w : ℤ)) *
        algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
          (diff.coeff (s.val + (w : ℚ) / (T : ℕ))) = 0
      rw [h_coeff, map_zero, mul_zero]
    · exfalso
      have h_supp : (s.val + (w : ℚ) / (T : ℕ)) ∈ f.support := by
        by_contra h
        exact h_coeff (fhat_diff_coeff_outside_support hf2 h)
      let n_candidate : ℤ := n_s_int s + (w : ℤ)
      have h_q_n_cand : g + (n_candidate : ℚ) / (T : ℕ) = s.val + (w : ℚ) / (T : ℕ) := by
        have h_int := h_used_isInt _ hs_used
        have h_rewrite : (n_candidate : ℚ) = ((T : ℕ) : ℚ) * (s.val - g) + w := by
          change ((n_s_int s + (w : ℤ) : ℤ) : ℚ) = _
          push_cast
          linarith
        rw [h_rewrite]
        field_simp
        ring
      have h_n_cand_in_Tfp : n_candidate ∈
          Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M) := by
        apply (Set.Finite.mem_toFinset _).mpr
        refine ⟨?_, ?_⟩
        · rw [h_q_n_cand]; exact h_sval_le_M_val
        · rw [h_q_n_cand]; exact h_coeff
      have h_sigma_n_cand : sigma_of ⟨n_candidate, h_n_cand_in_Tfp⟩ =
          (⟨s, w⟩ : Σ _ : ↥(Stilde hf2), ℕ) := by
        change (⟨(sw_choose ⟨n_candidate, h_n_cand_in_Tfp⟩).1,
              (sw_choose ⟨n_candidate, h_n_cand_in_Tfp⟩).2⟩ : Σ _ : ↥(Stilde hf2), ℕ) =
            ⟨s, w⟩
        have h_eq := h_sw_unique ⟨n_candidate, h_n_cand_in_Tfp⟩ (s, w) h_q_n_cand
        -- h_eq : (s, w) = sw_choose ⟨n_candidate, h_n_cand_in_Tfp⟩
        rw [← h_eq]
      have h_in_im : (⟨s, w⟩ : Σ _ : ↥(Stilde hf2), ℕ) ∈
          (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach.image sigma_of := by
        refine Finset.mem_image.mpr ?_
        refine ⟨⟨n_candidate, h_n_cand_in_Tfp⟩, Finset.mem_attach _ _, h_sigma_n_cand⟩
      exact h_not_im h_in_im
  -- Sum identity: via Finset.sum_image (injection) + Finset.sum_subset (extension).
  have h_sum_via_sigma :
      (∑ n ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach,
          (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
            algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
              (diff.coeff (g + (n.val : ℚ) / (T : ℕ)))) =
      ∑ p_sig ∈ Stilde_used.sigma (fun s : ↥(Stilde hf2) => Finset.range (W_s s + 1)),
        F p_sig := by
    have h_eq : (∑ n ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach,
          (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
            algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
              (diff.coeff (g + (n.val : ℚ) / (T : ℕ)))) =
        ∑ n ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach, F (sigma_of n) := by
      apply Finset.sum_congr rfl
      intro n _
      exact (h_F_eq n).symm
    rw [h_eq]
    rw [show (∑ n ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach,
              F (sigma_of n)) =
            ∑ p_sig ∈ (Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M)).attach.image
              sigma_of, F p_sig from
          (Finset.sum_image h_sigma_inj).symm]
    apply Finset.sum_subset
    · intro p hp
      obtain ⟨n, hn_attach, hn_eq⟩ := Finset.mem_image.mp hp
      rw [← hn_eq]
      exact h_sigma_mem n hn_attach
    · intro p hp h_not_im
      exact h_zero_outside p hp h_not_im
  -- Convert FullSigma sum to nested via Finset.sum_sigma, then per_s_inner_sum_eq.
  have h_sigma_to_per_s :
      (∑ p_sig ∈ Stilde_used.sigma (fun s : ↥(Stilde hf2) => Finset.range (W_s s + 1)),
        F p_sig) =
      ∑ s ∈ Stilde_used, (pInvTQ p (T : ℕ)) ^ (n_s_int s) *
        algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
          (Cs hf2 s - Cs_partial hf2 s (W_s s + 1)) := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro s _
    -- ∑ w ∈ range, F ⟨s, w⟩
    --   = ∑ w ∈ range, (pInvTQ)^{n_s + w} * algebraMap(diff.coeff(s.val + w/T))
    --   = (pInvTQ)^{n_s} * ∑ w ∈ range, (pInvTQ)^w * algebraMap(diff.coeff(s.val + w/T))
    --   = (pInvTQ)^{n_s} * algebraMap(Cs s - Cs_partial s (W_s + 1))  [per_s_inner_sum_eq]
    have hpInvTQ_ne_zero : pInvTQ p (T : ℕ) ≠ 0 := by
      intro h
      have hv := valued_v_pInvT (p := p) (T := T)
      rw [h] at hv
      simp at hv
    have h_pull_out : (∑ w ∈ Finset.range (W_s s + 1), F ⟨s, w⟩) =
        (pInvTQ p (T : ℕ)) ^ (n_s_int s) *
          ∑ w ∈ Finset.range (W_s s + 1), (pInvTQ p (T : ℕ)) ^ (w : ℤ) *
            algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
              (diff.coeff (s.val + (w : ℚ) / (T : ℕ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      change (pInvTQ p (T : ℕ)) ^ (n_s_int s + (w : ℤ)) *
          algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
            (diff.coeff (s.val + (w : ℚ) / (T : ℕ))) = _
      rw [zpow_add₀ hpInvTQ_ne_zero _ _]
      ring
    rw [h_pull_out]
    -- Apply per_s_inner_sum_eq.
    have h_inner := per_s_inner_sum_eq hf2 s (W_s s)
    rw [hdiff_def]
    rw [h_inner]
  -- Combine: LHS = nested ∑ s ∈ Stilde_used, (pInvTQ)^{n_s} * algebraMap(...).
  have h_LHS_eq :
      (∑ n : Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M),
        (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
          algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
            (diff.coeff (g + (n.val : ℚ) / (T : ℕ)))) =
      ∑ s ∈ Stilde_used, (pInvTQ p (T : ℕ)) ^ (n_s_int s) *
        algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
          (Cs hf2 s - Cs_partial hf2 s (W_s s + 1)) := by
    rw [← h_sigma_to_per_s, ← h_sum_via_sigma]
    rfl
  -- Now apply Valuation.map_sum_le using h_used_per_s_bound.
  rw [h_LHS_eq]
  apply Valuation.map_sum_le
  intro s hs
  exact h_used_per_s_bound s hs

/-- The difference `fhat hf2 - fromCoeff p T f.coeff (support_IsPWO f)`
is a T-null-series.

Strategy: For each `g : ℚ` and `M : ℕ`, the partial sum `P(M)` is bounded in valuation by
`ofAdd(-(K+1))` where `K = ⌊T·(M - g)⌋`.  The bound is obtained by recognising each
`n ∈ TfiniteBelow diff g M` as `n = T·(s.val - g) + w` for the unique decomposition
`(s, w) ∈ Stilde × ℕ` of `g + n/T ∈ f.support`, and observing that the per-`s`
fiber sums collapse to `(pInvTQ)^{n_s} · algebraMap (Cs hf2 s - Cs_partial hf2 s (W_s + 1))`,
whose valuation is `≤ ofAdd(-(n_s + W_s + 1)) = ofAdd(-(K+1))` by `Cs_diff_alg_v_le`. -/
private lemma fhat_diff_isTNullSeries
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)
      ∈ TNullSeriesIdeal p (T : ℕ) := by
  -- Structural prerequisites already in scope:
  -- * `Stilde_unique_decomposition` : unique `(s, w) : Stilde × ℕ` decomposition.
  -- * `not_Stilde_of_pos_w` : `w ≥ 1` ⇒ `q ∉ Stilde`.
  -- * `fhat_diff_coeff_Stilde` / `fhat_diff_coeff_outside_Stilde` /
  --   `fhat_diff_coeff_outside_support` : diff.coeff formulas at each location class.
  -- * `Cs_partial_diff_alg_v_le`: tail Cauchy bound.
  -- * `Cs_diff_alg_v_le`: limit bound
  --  `Valued.v (algebraMap (Cs s - Cs_partial s N)) ≤ ofAdd(-N)`.
  -- * `per_s_inner_sum_eq`: per-`s` inner-sum collapse to
  --   `algebraMap (Cs hf2 s - Cs_partial hf2 s (W + 1))`.
  intro g
  -- Set up notation.
  set diff : TLiftedPAdicHahnSeries p (T : ℕ) :=
    fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                (pAdicHahnSeries.coeff f) (support_IsPWO f)
    with hdiff_def
  -- The partial sum sequence.
  set P : ℕ → ℚᵘⁿ_[p, (T : ℕ)] := fun M =>
    ∑ n : Set.Finite.toFinset (TfiniteBelow p (T : ℕ) diff g M),
      (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
        algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (diff.coeff (g + (n.val : ℚ) / T))
    with hP_def
  -- We aim to show Tendsto P atTop (𝓝 0).  Use the Valued-topology characterisation:
  -- `(𝓝 0).HasBasis (fun γ : Γ₀ˣ => True) (fun γ => { x | Valued.v x < γ })`.
  -- KEY BOUND (analytical heart, structurally laid out below):
  --   `Valued.v (P M) ≤ ofAdd(-(⌊T·(M - g)⌋ + 1))`.
  -- As `M → ∞`, `⌊T·(M - g)⌋ → ∞`, so the bound `→ 0`, giving the result.
  --
  -- The bound follows from:
  -- (a) re-indexing `TfiniteBelow diff g M` over `(s, w) ∈ Stilde × ℕ` via
  --     `Stilde_unique_decomposition` (each `n ∈ TfiniteBelow` corresponds to a unique
  --     `(s, w)` with `g + n/T = s.val + w/T`);
  -- (b) for fixed `s`, per-`s` slice collapse via `per_s_inner_sum_eq`:
  --     `∑_w (pInvTQ)^w · algebraMap(diff.coeff(s.val + w/T))
  -- = algebraMap(Cs s - Cs_partial s (W_s + 1))`;
  -- (c) per-`s` valuation bound via `Cs_diff_alg_v_le`:
  --     `Valued.v((pInvTQ)^{n_s}
  -- · algebraMap(Cs s - Cs_partial s (W_s + 1))) ≤ ofAdd(-(n_s + W_s + 1))`;
  -- (d) arithmetic identity `n_s + W_s = ⌊T·(M - g)⌋` (residue condition implies);
  -- (e) ultrametric `Valuation.map_sum_le` over the (finite) Finset of active `s`s.

  -- Proof skeleton via the Valued neighbourhood characterisation:
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨c, hc_ne, hγ⟩ := Texists_v_lt_subset p (T : ℕ) hU
  -- It suffices to show: `∀ᶠ M, Valued.v (P M) < c`.
  suffices h_ev : ∀ᶠ M : ℕ in Filter.atTop,
      Valued.v (P M) < c by
    filter_upwards [h_ev] with M hM
    exact hγ (by simpa using hM)
  -- Reduce to: `∀ᶠ M, Valued.v (P M) ≤ ofAdd(-(K + 1))` where K = ⌊T(M-g)⌋,
  -- and as M → ∞, K → ∞ makes the bound < c eventually.
  -- Step 1: extract the integer exponent `k` corresponding to `c`.
  set k : ℤ := Multiplicative.toAdd (WithZero.unzero hc_ne) with hk_def
  have h_γ_val : c =
      ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [hk_def, ofAdd_toAdd, WithZero.coe_unzero]
  -- Step 2: choose threshold M₀ so that for M ≥ M₀, ⌊T(M-g)⌋ ≥ -k.
  -- Concretely: pick M₀ := ⌈g + (-k)/T⌉₊.
  have hT_pos : (0 : ℚ) < (T : ℕ) := by exact_mod_cast T.pos
  have hT_ne : ((T : ℕ) : ℚ) ≠ 0 := ne_of_gt hT_pos
  have h_ev_floor : ∀ᶠ M : ℕ in Filter.atTop,
      -k ≤ ⌊(T : ℚ) * ((M : ℚ) - g)⌋ := by
    have h_int : ∀ᶠ M : ℕ in Filter.atTop, ⌈g + (-(k : ℚ)) / T⌉₊ ≤ M :=
      Filter.eventually_ge_atTop ⌈g + (-(k : ℚ)) / T⌉₊
    filter_upwards [h_int] with M hM
    have h1 : g + (-(k : ℚ)) / T ≤ (⌈g + (-(k : ℚ)) / T⌉₊ : ℚ) := Nat.le_ceil _
    have h2 : ((⌈g + (-(k : ℚ)) / T⌉₊ : ℕ) : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
    have h3 : g + (-(k : ℚ)) / T ≤ (M : ℚ) := h1.trans h2
    have h4 : (-(k : ℚ)) / T ≤ (M : ℚ) - g := by linarith
    have h5 : (T : ℚ) * ((-(k : ℚ)) / T) ≤ (T : ℚ) * ((M : ℚ) - g) :=
      mul_le_mul_of_nonneg_left h4 hT_pos.le
    have hT_eq : (T : ℚ) * ((-(k : ℚ)) / T) = -(k : ℚ) := by
      rw [mul_div_assoc']; field_simp
    rw [hT_eq] at h5
    have h6 : (-(k : ℤ) : ℚ) ≤ (T : ℚ) * ((M : ℚ) - g) := by linarith
    exact Int.le_floor.mpr h6
  filter_upwards [h_ev_floor] with M hMfloor
  -- Step 3: apply fhat_diff_partial_v_le to get the per-M bound.
  have h_partial_le := fhat_diff_partial_v_le hf2 g M
  -- Unfold the partial-sum expression so it matches P M / hP_def.
  have h_P_eq : P M =
      ∑ n : Set.Finite.toFinset (TfiniteBelow p (T : ℕ)
                  (fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                    (pAdicHahnSeries.coeff f) (support_IsPWO f)) g M),
              (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
                algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                  ((fhat hf2 - TLiftedPAdicHahnSeries.fromCoeff p (T : ℕ)
                    (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
                    (g + (n.val : ℚ) / T)) := by
    rw [hP_def]
  rw [h_P_eq]
  -- Step 4: chain the per-M bound and the threshold into < γ.
  refine lt_of_le_of_lt h_partial_le ?_
  rw [h_γ_val]
  rw [WithZero.coe_lt_coe]
  apply Multiplicative.ofAdd_lt.mpr
  linarith

/-- The lift `fhat` represents `σ f`: its class modulo the `T`-null-series ideal equals the image
`σ p T f` of `f` under the T-scaling isomorphism. This identifies the constructed lift with the
canonical one, so the multinomial expansion of `P(fhat)` computes `P(σ f)`. -/
lemma mk_fhat_eq_sigma_f {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) (fhat hf2) = σ p (T : ℕ) f := by
  -- Step 1: rewrite σ p T f as mk (fromCoeff p T f.coeff (support_IsPWO f)).
  rw [sigma_eq_mk_fromCoeff_fcoeff]
  -- Step 2: equality of `mk`s reduces to difference in N_T (Ideal.Quotient.eq).
  exact (Ideal.Quotient.eq).mpr (fhat_diff_isTNullSeries hf2)

/-- Existential interface for the lift `fhat` constructed from `C_s`.

A nonzero coefficient bundle on `Stilde` whose corresponding `TLiftedPAdicHahnSeries`
projects to `σ p T f` in the quotient `𝕃_[p,T]`. -/
private def FhatData {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+)
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) : Prop :=
  ∃ (Cs : ↥(Stilde hf2) → ℤᵘⁿ_[p,(T : ℕ)])
    (fhat : TLiftedPAdicHahnSeries p (T : ℕ)),
    (∀ s, Cs s ≠ 0) ∧
    (Function.support fhat.coeff ⊆ Stilde hf2) ∧
    (∀ (s : ↥(Stilde hf2)), fhat.coeff s.val = Cs s) ∧
    (Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) fhat = σ p (T : ℕ) f)

/-- Existence of the lift data. Assembles the structural pieces `Cs`, `fhat`,
`Cs_ne_zero`, `fhat_support_subset`, `fhatCoeff_eq_Cs`, `mk_fhat_eq_sigma_f`.
The two analytical hard steps (the limit existence and the canonical T-expansion
identification) are encapsulated in `exists_Cs` and `mk_fhat_eq_sigma_f`. -/
private lemma exists_FhatData
    {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+)
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    FhatData f T hf2 :=
  ⟨Cs hf2, fhat hf2, Cs_ne_zero hf2, fhat_support_subset hf2,
    fhatCoeff_eq_Cs hf2, mk_fhat_eq_sigma_f hf2⟩

/-! ### Step 4–6 — Multinomial expansion, collapse via `lemma_3_8`, contradiction.

The high-level engine packing Steps 4–6 of the paper's proof. Given the lift data from
`exists_FhatData`, plus the `IsCNSparse` witness from sparsity, derives the
final identity
  `p^{r₀ + T·∑φ₀(d)·μ(d)} · a_n · n!/(∏φ₀(d)!) · ∏ C_{μ(d)}^{φ₀(d)} = 0`
and obtains a contradiction with `hP₀` / `Cs_ne_zero`.

This is the part that genuinely requires the multinomial expansion of `P.aeval fhat`
in `TLiftedPAdicHahnSeries`, the T-null-series identity (c) at `q = -r₀/T`, and the
application of `Sparse.lemma_3_8` to collapse equation (c) to a single term.

* `r0` — the rational `r₀ := ∑_{d ∈ S} ‖d‖·φ₀(d)`.
* `sigma_aeval_P_eq_zero` — `σ(P.aeval f) = 0` (trivial from ring-hom + hP_aeval).
* `identity_c` — the T-null-series identity at `q = -r₀/T`.
* `phi_tilde_constraint_at_phi0` — application of `Sparse.lemma_3_8` to collapse
  φ̃ to φ₀∘μ⁻¹.
* `identity_c_collapsed` — the surviving single-term equation obtained from
  the two lemmas above.
* `final_disjunction` — domain integrality of `ℤᵘⁿ_[p,T]` to extract the disjunction
  from `identity_c_collapsed`. -/

/-- The rational `r₀ := ∑_{d ∈ S} ‖d‖ · φ₀(d)`.

Although `r₀` is rational, the exponent `r₀ + T · ∑φ₀(d)·μ(d)` appearing in the
paper's Step 5 collapse is an integer (cf. `muQ_residue`). -/
noncomputable def r0 {p : ℕ} [Fact (Nat.Prime p)] {S : Set DigitSeries}
    {hS : ∀ d ∈ S, d.IsP p} {C n : ℕ+} (hSparse : IsCNSparse p C n S hS) : ℚ :=
  ∑ᶠ d : S, (d.val.norm p) * (Sparse.φ₀ hSparse d : ℚ)

/-- `σ p T (P.aeval f) = 0` in `𝕃_[p,T]`.

Trivial consequence of `σ` being a ring hom and `P.aeval f = 0`. The PDF uses this
together with the multinomial expansion of `f̂^i` in `TLiftedPAdicHahnSeries` to
deduce `P.aeval(f̂) ∈ N_T`. The bridge requires showing the multinomial expansion in
`TLiftedPAdicHahnSeries` projects to `P.aeval(σ f)` via the quotient; that bridge is
the body of `identity_c`. -/
private lemma sigma_aeval_P_eq_zero
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} (T : ℕ+)
    {P : Polynomial ℚᵘⁿ_[p]} (hP_aeval : (Polynomial.aeval f) P = 0) :
    σ p (T : ℕ) ((Polynomial.aeval f) P) = 0 := by
  rw [hP_aeval]; exact map_zero _

/-! ### clearing denominators and the `Pfhat_TLifted` construction.

We construct an explicit element `Pfhat_TLifted ∈ TLiftedPAdicHahnSeries p T` that
serves as the witness for `identity_c`. The construction uses
`IsLocalization.integerNormalization` to clear denominators of `P` by some
`c ∈ ℤᵘⁿ_[p]` (in `nonZeroDivisors ℤᵘⁿ_[p]`), giving `P_int : Polynomial ℤᵘⁿ_[p]`
with `P_int.map (algebraMap ℤᵘⁿ_[p] ℚᵘⁿ_[p]) = c • P`. Then
`Pfhat_TLifted := (P_int.map (OQpUn_embd p T)).aeval fhat` makes type-sense as a
`TLiftedPAdicHahnSeries p T`-valued evaluation.

The bridge lemma `Pfhat_TLifted_isTNullSeries` shows the resulting element is a
T-null-series, using `σ(P.aeval f) = 0` + ring-hom commutation. -/

/-- The denominator-cleared polynomial: `P_int := integerNormalization _ P`.
By `IsLocalization.integerNormalization_spec`, there exists `c ∈ nonZeroDivisors ℤᵘⁿ_[p]`
such that `P_int.map (algebraMap ℤᵘⁿ_[p] ℚᵘⁿ_[p]) = c • P`. -/
noncomputable def P_int {p : ℕ} [Fact (Nat.Prime p)]
    (P : Polynomial ℚᵘⁿ_[p]) : Polynomial ℤᵘⁿ_[p] :=
  IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P

/-- The TLifted-level multinomial expansion:
`Pfhat_TLifted := (P_int.map (OQpUn_embd p T)).aeval fhat`. -/
noncomputable def Pfhat_TLifted {p : ℕ} [Fact (Nat.Prime p)] (T : ℕ+)
    (P : Polynomial ℚᵘⁿ_[p])
    (fhat : TLiftedPAdicHahnSeries p (T : ℕ)) :
    TLiftedPAdicHahnSeries p (T : ℕ) :=
  ((P_int P).map (OQpUn_embd p T)).aeval fhat

/-- The bridge lemma: `Pfhat_TLifted` is a T-null-series.

Proof outline:
1. Compose ZpUn_embd = lift QpUn_embd ∘ algebraMap.
2. Apply `IsLocalization.integerNormalization_aeval_eq_zero` to get `P_int.aeval f = 0`
   in `𝕃_[p]`.
3. Establish `σ ∘ algebraMap ℤᵘⁿ_[p] 𝕃_[p] = algebraMap ℤᵘⁿ_[p] 𝕃_[p,T]` (a direct
   calculation via `σ_lift_mk` + `HahnSeries.map_single`).
4. Use `Polynomial.hom_eval₂` to commute σ with aeval, giving
   `σ (P_int.aeval f) = P_int.aeval (σ f)` in `𝕃_[p,T]`.
5. So `P_int.aeval (σ f) = σ 0 = 0`.
6. Use `Polynomial.aeval_map_algebraMap` (with `IsScalarTower ℤᵘⁿ_[p] ℤᵘⁿ_[p,T] 𝕃_[p,T]`,
   which is rfl) to bridge to `(P_int.map OQpUn_embd).aeval (σ f) = 0`.
7. Use `Polynomial.aeval_algHom_apply` with `Ideal.Quotient.mkₐ` to bridge
   `mk ((P_int.map OQpUn_embd).aeval fhat) = (P_int.map OQpUn_embd).aeval (mk fhat)`. -/
private lemma Pfhat_TLifted_isTNullSeries
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} (T : ℕ+)
    {P : Polynomial ℚᵘⁿ_[p]} (hP_aeval : (Polynomial.aeval f) P = 0)
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (h_mk_eq : Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) fhat = σ p (T : ℕ) f) :
    Pfhat_TLifted T P fhat ∈ TNullSeriesIdeal p (T : ℕ) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  unfold Pfhat_TLifted P_int
  -- Goal: mk ((integerNormalization _ P).map OQpUn_embd).aeval fhat = 0
  -- Step 2: P_int.aeval f = 0 in 𝕃_[p] via IsLocalization.integerNormalization_aeval_eq_zero.
  have hPint_f :
      (IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).aeval f = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero _ P hP_aeval
  -- Step 3: σ ∘ algebraMap ℤᵘⁿ_[p] 𝕃_[p] = algebraMap ℤᵘⁿ_[p] 𝕃_[p,T].
  have h_alg_compat : ∀ x : ℤᵘⁿ_[p],
      σ p (T : ℕ) ((algebraMap ℤᵘⁿ_[p] 𝕃_[p]) x) =
        (algebraMap ℤᵘⁿ_[p] 𝕃_[p, (T : ℕ)]) x := by
    intro x
    change σ p (T : ℕ) (pAdicHahnSeries.ZpUn_embd x) = _
    change σ p (T : ℕ)
        (Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 x)) = _
    rw [show σ p (T : ℕ)
          (Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 x)) =
        Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ))
          (Lifted_to_TLifted p (T : ℕ) (HahnSeries.single 0 x)) from rfl]
    have h_map : Lifted_to_TLifted p (T : ℕ) (HahnSeries.single 0 x) =
        HahnSeries.single 0 (OQpUn_embd p (T : ℕ) x) :=
      HahnSeries.map_single (a := (0 : ℚ)) (r := x)
        (f := (OQpUn_embd p (T : ℕ) : ZeroHom ℤᵘⁿ_[p] ℤᵘⁿ_[p,(T : ℕ)]))
    rw [h_map]
    rfl
  -- Step 4-5: σ(P_int.aeval f) = P_int.aeval (σ f) = 0.
  have h_eval_σ : σ p (T : ℕ)
      ((IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).aeval f) =
      (IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).aeval
        (σ p (T : ℕ) f) := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def]
    rw [show σ p (T : ℕ) (Polynomial.eval₂ (algebraMap ℤᵘⁿ_[p] 𝕃_[p]) f
          (IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P)) =
        (σ p (T : ℕ)).toRingHom (Polynomial.eval₂ (algebraMap ℤᵘⁿ_[p] 𝕃_[p]) f
          (IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P))
        from rfl]
    rw [Polynomial.hom_eval₂]
    congr 1
    ext x
    exact h_alg_compat x
  have hPint_σf : (IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).aeval
      (σ p (T : ℕ) f) = 0 := by
    rw [← h_eval_σ, hPint_f, map_zero]
  -- Step 6: now bridge (P_int.map OQpUn_embd).aeval (σ f) = P_int.aeval (σ f) = 0.
  have h_aeval_map :
      ((IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).map
        (OQpUn_embd p T)).aeval (σ p (T : ℕ) f) =
      (IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).aeval
        (σ p (T : ℕ) f) := by
    rw [show OQpUn_embd p T = algebraMap ℤᵘⁿ_[p] ℤᵘⁿ_[p,(T : ℕ)] from rfl]
    exact Polynomial.aeval_map_algebraMap _ _ _
  -- Step 7: bridge mk to (algebraMap-aeval) via Ideal.Quotient.mkₐ + aeval_algHom_apply.
  have key := Polynomial.aeval_algHom_apply
    (Ideal.Quotient.mkₐ (ℤᵘⁿ_[p,(T : ℕ)]) (TNullSeriesIdeal p (T : ℕ))) fhat
    (((IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).map
       (OQpUn_embd p T)))
  rw [show Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ))
        (((IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).map
          (OQpUn_embd p T)).aeval fhat) =
      Ideal.Quotient.mkₐ (ℤᵘⁿ_[p,(T : ℕ)])
        (TNullSeriesIdeal p (T : ℕ))
        (((IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).map
          (OQpUn_embd p T)).aeval fhat) from rfl]
  rw [← key]
  -- Goal: aeval (mkₐ fhat) (P_int.map OQpUn_embd) = 0
  have h_mkₐ_eq : Ideal.Quotient.mkₐ (ℤᵘⁿ_[p,(T : ℕ)])
      (TNullSeriesIdeal p (T : ℕ)) fhat = σ p (T : ℕ) f := h_mk_eq
  rw [h_mkₐ_eq, h_aeval_map, hPint_σf]

/-- Per-coefficient expansion of `Pfhat_TLifted`.

For each `q ∈ ℚ`, `(Pfhat_TLifted T P fhat).coeff q` decomposes as a finite sum
`∑ᵢ OQpUn_embd (P_int.coeff i) * (fhat^i).coeff q`. This is the entry point for
the multinomial expansion of `fhat^i.coeff q`. -/
lemma Pfhat_TLifted_coeff_eq {p : ℕ} [Fact (Nat.Prime p)] (T : ℕ+)
    (P : Polynomial ℚᵘⁿ_[p])
    (fhat : TLiftedPAdicHahnSeries p (T : ℕ)) (q : ℚ) :
    (Pfhat_TLifted T P fhat).coeff q =
      ∑ i ∈ Finset.range (((P_int P).map (OQpUn_embd p T)).natDegree + 1),
        OQpUn_embd p T ((P_int P).coeff i) * (fhat ^ i).coeff q := by
  unfold Pfhat_TLifted
  rw [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum]
  congr 1
  ext i
  rw [Polynomial.coeff_map, Algebra.smul_def]
  change ((HahnSeries.single 0 _) * fhat ^ i).coeff q = _
  rw [HahnSeries.single_zero_mul_eq_smul]
  rfl

/-- Identity (c): the IsTNullSeries identity for `P.aeval(f̂)` specialised at
`q = -r₀/T`.

PDF reasoning: by `sigma_aeval_P_eq_zero`, `σ(P.aeval f) = 0`. By multinomial expansion of `f̂^i`,
the element of `TLiftedPAdicHahnSeries p T` whose quotient image equals `σ(P.aeval f) = 0`
is in `N_T`. Applying `IsTNullSeries` at `q = -r₀/T` and using the prescribed
coefficient formula yields:
`∑_{w ∈ ℤ} p^w · ∑_{φ̃ : S̃ → ℕ, ∑φ̃ ≤ n, ∑φ̃(s)·s = -r₀/T + w/T}
  a_{∑φ̃} · multinomial · ∏ C_s^{φ̃(s)}  =  0`.

The statement is packaged as the (existential) existence of an explicit
`Pfhat ∈ TLiftedPAdicHahnSeries p T` with the multinomial coefficient formula and
membership in `TNullSeriesIdeal p T`. The detailed combinatorial formula requires
either an iterated `HahnSeries.coeff_mul` formula or a direct construction. -/
private lemma identity_c
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    {hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}}
    {C : ℕ+} {n : ℕ+} (_hSparse : IsCNSparse p C n S hS)
    {Cs : ↥(Stilde hf2) → ℤᵘⁿ_[p,(T : ℕ)]}
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (_h_supp : Function.support fhat.coeff ⊆ Stilde hf2)
    (_h_coeff_eq : ∀ (s : ↥(Stilde hf2)), fhat.coeff s.val = Cs s)
    (h_mk_eq : Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) fhat = σ p (T : ℕ) f)
    {P : Polynomial ℚᵘⁿ_[p]} (hP_aeval : (Polynomial.aeval f) P = 0)
    (_hP_natDegree : P.natDegree = n) :
    ∃ Pfhat : TLiftedPAdicHahnSeries p (T : ℕ),
      Pfhat ∈ TNullSeriesIdeal p (T : ℕ) := by
  exact ⟨Pfhat_TLifted T P fhat,
    Pfhat_TLifted_isTNullSeries T hP_aeval h_mk_eq⟩

/-! ### Step 5 — Collapse via Lemma 3.8. -/

/-- Every `φ̃ : Stilde → ℕ` satisfying the constraints from equation (c)
equals `φ₀ ∘ μ⁻¹`.

paper reasoning: define `φ := φ̃ ∘ μ : S → ℕ`. Using `muQ_residue` (i.e. `‖d‖ + T·μ(d) ∈ ℤ`):
`∑‖d‖·φ(d) ≡ -T·∑μ(d)·φ̃(μd) = -T·∑s·φ̃(s) (mod ℤ)`. From the residue hypothesis,
`-T·∑s·φ̃(s) ≡ r₀ (mod ℤ) = ∑‖d‖·φ₀(d) (mod ℤ)`. So `φ` satisfies the residue clause
of `Sparse.lemma_3_8`. Combined with finite support and the sum bound, lemma_3_8 yields
`φ = φ₀`. Translate back: `φ̃ = φ ∘ μ⁻¹ = φ₀ ∘ μ⁻¹`. -/
private lemma phi_tilde_constraint_at_phi0
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} (hS : ∀ d ∈ S, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    (phiT : ↥(Stilde hf2) → ℕ)
    (hphiT_finite : (Function.support phiT).Finite)
    (hphiT_sum : ∑ᶠ s : ↥(Stilde hf2), phiT s ≤ n)
    (hphiT_residue : ((T : ℚ) * (∑ᶠ s : ↥(Stilde hf2), (s.val : ℚ) * (phiT s : ℚ))
                    + r0 hSparse).isInt = true) :
    phiT = Sparse.φ₀ hSparse ∘ (muEquiv hS hf2).symm := by
  set μ := muEquiv hS hf2 with hμ_def
  set φ : S → ℕ := phiT ∘ μ with hφ_def
  -- Apply Sparse.lemma_3_8 to get φ = φ₀ hSparse.
  have hφ_eq : φ = Sparse.φ₀ hSparse := by
    refine Sparse.lemma_3_8 hSparse φ ?_ ?_ ?_
    · -- (Function.support φ).Finite: preimage of finite set under injective bijection.
      have h_eq : Function.support φ = μ ⁻¹' Function.support phiT := by
        rw [hφ_def, Function.support_comp_eq_preimage]
      rw [h_eq]
      exact hphiT_finite.preimage μ.injective.injOn
    · -- ∑ᶠ d : S, φ d ≤ n: via finsum_comp_equiv.
      have h_eq : ∑ᶠ d : S, φ d = ∑ᶠ s : ↥(Stilde hf2), phiT s := by
        rw [hφ_def]
        exact finsum_comp_equiv μ
      rw [h_eq]
      exact hphiT_sum
    · -- The residue clause: (∑ᶠ d, ‖d‖·φ d - ∑ᶠ d, ‖d‖·φ₀ d).isInt.
      -- use `muQ_residue d : (‖d‖ + T·μ_q d).isInt = true`, multiply
      -- by `phiT(μ d)`, sum over `d` (giving an integer sum), distribute, change
      -- variable `d ↦ μ d` to land at `∑ᶠ s, s·phiT s`, and combine with
      -- `hphiT_residue` to conclude.
      -- (μ d).val = muQ hf2 d, by def of `muEquiv` and `muToStilde`.
      have hμ_val : ∀ d : S, ((μ d : ↥(Stilde hf2)) : ℚ) = muQ hf2 d := fun _ => rfl
      -- Finite support of φ = phiT ∘ μ.
      have h_phi_supp_finite : (Function.support φ).Finite := by
        rw [hφ_def, Function.support_comp_eq_preimage]
        exact hphiT_finite.preimage μ.injective.injOn
      -- For each d : S, the term ((‖d‖) + T·(μ d).val) · phiT(μ d) is isInt.
      have h_each_int : ∀ d : S,
          (((d.val.norm p : ℚ) + (T : ℚ) * ((μ d : ↥(Stilde hf2)) : ℚ))
            * ((phiT (μ d) : ℕ) : ℚ)).isInt = true := by
        intro d
        refine isInt_mul' ?_ (isInt_natCast' _)
        rw [hμ_val]
        exact muQ_residue hf2 d
      -- Helper: support of a product is contained in `Function.support φ`
      -- whenever the second factor is the `phiT(μ ·)` cast.
      have h_supp_via_phi : ∀ (h : S → ℚ),
          (Function.support (fun d : S => h d * ((phiT (μ d) : ℕ) : ℚ))) ⊆
          Function.support φ := by
        intro h d hd
        simp only [Function.mem_support, ne_eq] at hd ⊢
        intro hφd_zero
        apply hd
        have : ((phiT (μ d) : ℕ) : ℚ) = 0 := by
          have : phiT (μ d) = 0 := by
            rw [hφ_def] at hφd_zero
            simpa [Function.comp_apply] using hφd_zero
          exact_mod_cast this
        rw [this, mul_zero]
      -- Finite supports of the relevant `d ↦ … · phiT(μ d)` summands.
      have h_combined_supp_finite :
          (Function.support (fun d : S =>
            ((d.val.norm p : ℚ) + (T : ℚ) * ((μ d : ↥(Stilde hf2)) : ℚ))
              * ((phiT (μ d) : ℕ) : ℚ))).Finite :=
        h_phi_supp_finite.subset (h_supp_via_phi _)
      have h_norm_supp_finite :
          (Function.support (fun d : S =>
            (d.val.norm p : ℚ) * ((phiT (μ d) : ℕ) : ℚ))).Finite :=
        h_phi_supp_finite.subset (h_supp_via_phi _)
      have h_Tmu_supp_finite :
          (Function.support (fun d : S =>
            (T : ℚ) * ((μ d : ↥(Stilde hf2)) : ℚ) * ((phiT (μ d) : ℕ) : ℚ))).Finite :=
        h_phi_supp_finite.subset (h_supp_via_phi _)
      have h_muval_phi_supp_finite :
          (Function.support (fun d : S =>
            ((μ d : ↥(Stilde hf2)) : ℚ) * ((phiT (μ d) : ℕ) : ℚ))).Finite :=
        h_phi_supp_finite.subset (h_supp_via_phi _)
      -- The combined sum is isInt.
      have h_combined_isInt :
          (∑ᶠ d : S, ((d.val.norm p : ℚ) + (T : ℚ) * ((μ d : ↥(Stilde hf2)) : ℚ))
                      * ((phiT (μ d) : ℕ) : ℚ)).isInt = true :=
        finsum_isInt h_combined_supp_finite h_each_int
      -- Distribute the combined sum into (norm · phi) + (T · (μ d).val · phi).
      have h_distrib :
          (∑ᶠ d : S, ((d.val.norm p : ℚ) + (T : ℚ) * ((μ d : ↥(Stilde hf2)) : ℚ))
                      * ((phiT (μ d) : ℕ) : ℚ)) =
          (∑ᶠ d : S, (d.val.norm p : ℚ) * ((phiT (μ d) : ℕ) : ℚ))
            + (∑ᶠ d : S, (T : ℚ) * ((μ d : ↥(Stilde hf2)) : ℚ)
                          * ((phiT (μ d) : ℕ) : ℚ)) := by
        rw [← finsum_add_distrib h_norm_supp_finite h_Tmu_supp_finite]
        apply finsum_congr
        intro d
        ring
      -- Pull T out of the second sum.
      have h_pull_T :
          (∑ᶠ d : S, (T : ℚ) * ((μ d : ↥(Stilde hf2)) : ℚ)
                      * ((phiT (μ d) : ℕ) : ℚ)) =
          (T : ℚ) * (∑ᶠ d : S, ((μ d : ↥(Stilde hf2)) : ℚ)
                                * ((phiT (μ d) : ℕ) : ℚ)) := by
        rw [mul_finsum' _ _ h_muval_phi_supp_finite]
        apply finsum_congr
        intro d
        ring
      -- Change of variable along μ : S ≃ Stilde hf2.
      have h_change_var :
          (∑ᶠ d : S, ((μ d : ↥(Stilde hf2)) : ℚ) * ((phiT (μ d) : ℕ) : ℚ)) =
          (∑ᶠ s : ↥(Stilde hf2), ((s : ℚ)) * ((phiT s : ℕ) : ℚ)) :=
        finsum_comp_equiv μ
          (f := fun s : ↥(Stilde hf2) => ((s : ℚ)) * ((phiT s : ℕ) : ℚ))
      -- Assemble: combined sum equals ∑‖d‖·phiT(μd) + T·∑ s·phiT s.
      have h_combined_eq :
          (∑ᶠ d : S, ((d.val.norm p : ℚ) + (T : ℚ) * ((μ d : ↥(Stilde hf2)) : ℚ))
                      * ((phiT (μ d) : ℕ) : ℚ)) =
          (∑ᶠ d : S, (d.val.norm p : ℚ) * ((phiT (μ d) : ℕ) : ℚ))
          + (T : ℚ) * (∑ᶠ s : ↥(Stilde hf2), ((s : ℚ)) * ((phiT s : ℕ) : ℚ)) := by
        rw [h_distrib, h_pull_T, h_change_var]
      -- So the (LHS in distributed form) is isInt.
      have h_LHS_isInt :
          ((∑ᶠ d : S, (d.val.norm p : ℚ) * ((phiT (μ d) : ℕ) : ℚ))
            + (T : ℚ) * (∑ᶠ s : ↥(Stilde hf2), ((s : ℚ)) * ((phiT s : ℕ) : ℚ))).isInt
            = true := by
        rw [← h_combined_eq]; exact h_combined_isInt
      -- Subtract `hphiT_residue` to get ((∑‖d‖·phiT(μd)) - r0).isInt.
      have h_subtract :
          ((∑ᶠ d : S, (d.val.norm p : ℚ) * ((phiT (μ d) : ℕ) : ℚ))
            - r0 hSparse).isInt = true := by
        have h_sub := isInt_sub' h_LHS_isInt hphiT_residue
        have heq :
            ((∑ᶠ d : S, (d.val.norm p : ℚ) * ((phiT (μ d) : ℕ) : ℚ))
              + (T : ℚ) * (∑ᶠ s : ↥(Stilde hf2), ((s : ℚ)) * ((phiT s : ℕ) : ℚ)))
            - ((T : ℚ) * (∑ᶠ s : ↥(Stilde hf2), ((s : ℚ)) * ((phiT s : ℕ) : ℚ))
                + r0 hSparse) =
            (∑ᶠ d : S, (d.val.norm p : ℚ) * ((phiT (μ d) : ℕ) : ℚ)) - r0 hSparse := by
          ring
        rw [heq] at h_sub
        exact h_sub
      -- Finally, rewrite the goal: φ d = phiT (μ d) and r0 = ∑ᶠ d, ‖d‖·φ₀ d (defn).
      have hφ_eq_phiT : ∀ d : S, ((φ d : ℕ) : ℚ) = ((phiT (μ d) : ℕ) : ℚ) := by
        intro d; rw [hφ_def]; simp [Function.comp_apply]
      have h_phi_finsum_eq :
          (∑ᶠ d : S, (d.val.norm p : ℚ) * ((φ d : ℕ) : ℚ)) =
          (∑ᶠ d : S, (d.val.norm p : ℚ) * ((phiT (μ d) : ℕ) : ℚ)) := by
        apply finsum_congr; intro d; rw [hφ_eq_phiT]
      have h_r0_def : r0 hSparse =
          ∑ᶠ d : S, (d.val.norm p : ℚ) * ((Sparse.φ₀ hSparse d : ℕ) : ℚ) := rfl
      rw [h_phi_finsum_eq, ← h_r0_def]
      exact h_subtract
  -- Translate `φ = φ₀ hSparse` into `phiT = φ₀ hSparse ∘ μ.symm`.
  ext s
  -- Goal (definitionally): phiT s = Sparse.φ₀ hSparse (μ.symm s).
  have h := congr_fun hφ_eq (μ.symm s)
  -- h : φ (μ.symm s) = Sparse.φ₀ hSparse (μ.symm s)
  simp only [hφ_def, Function.comp_apply, Equiv.apply_symm_apply] at h
  exact h

/-- The expression `r₀ + T·∑φ₀(d)·μ(d)` is an integer.

computation (equation for the surviving `w`):
* `r₀ = ∑ᶠ d : S, ||d|| · φ₀(d)` by definition.
* `T · ∑ᶠ d, φ₀(d) · μ(d) = ∑ᶠ d, φ₀(d) · (T · μ(d))`.
* So `r₀ + T·∑φ₀(d)·μ(d) = ∑ᶠ d, φ₀(d) · (||d|| + T · μ(d))`.
* Each `||d|| + T · μ(d) ∈ ℤ` by `muQ_residue`.
* The finite sum of integers is an integer.

This is used as the concrete construction of `w₀` in `Pfhat_TLifted_collapse_witness`. -/
private lemma w0_rat_isInt
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS) :
    (r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
        (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).isInt = true := by
  -- The combined sum is finitely supported (only d with φ₀(d) ≠ 0 contribute).
  -- Express r₀ + T·∑φ₀(d)·μ(d) as ∑φ₀(d)·(||d|| + T·μ(d)).
  -- Each summand is isInt by muQ_residue.
  -- The finite sum of isInts is isInt by finsum_isInt.
  have hφ_supp_finite : (Function.support (Sparse.φ₀ hSparse)).Finite := by
    refine Set.Finite.subset (Set.finite_range hSparse.2.choose) ?_
    intro d hd
    simp only [Function.mem_support, Sparse.φ₀, Set.mem_range] at hd ⊢
    by_contra h
    have hempty : hSparse.2.choose ⁻¹' {d} = ∅ := by
      ext i; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      intro hi; exact h ⟨i, hi⟩
    rw [hempty] at hd; simp at hd
  -- Auxiliary: the term map `d ↦ φ₀(d) · (||d|| + T · μ(d))` has finite support.
  have h_term_supp_finite :
      (Function.support (fun d : S =>
        ((Sparse.φ₀ hSparse d : ℕ) : ℚ) *
          ((d.val.norm p : ℚ) + (T : ℚ) * (muQ hf2 d : ℚ)))).Finite := by
    refine hφ_supp_finite.subset ?_
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd ⊢
    intro hφ_zero
    apply hd
    have : ((Sparse.φ₀ hSparse d : ℕ) : ℚ) = 0 := by exact_mod_cast hφ_zero
    rw [this, zero_mul]
  -- Each summand is isInt.
  have h_each_int : ∀ d : S,
      (((Sparse.φ₀ hSparse d : ℕ) : ℚ) *
        ((d.val.norm p : ℚ) + (T : ℚ) * (muQ hf2 d : ℚ))).isInt = true := by
    intro d
    refine isInt_mul' (isInt_natCast' _) ?_
    exact muQ_residue hf2 d
  -- So the combined sum is isInt.
  have h_combined_isInt :
      (∑ᶠ d : S, ((Sparse.φ₀ hSparse d : ℕ) : ℚ) *
        ((d.val.norm p : ℚ) + (T : ℚ) * (muQ hf2 d : ℚ))).isInt = true :=
    finsum_isInt h_term_supp_finite h_each_int
  -- Now rewrite the target as the combined sum.
  -- r₀ = ∑ᶠ d, ||d|| · φ₀(d), and T · ∑ᶠ d, φ₀(d) · μ(d) = ∑ᶠ d, φ₀(d) · (T · μ(d)).
  -- So r₀ + T·∑ = ∑ᶠ d, [||d||·φ₀(d) + φ₀(d)·(T·μ(d))] = ∑ᶠ d, φ₀(d) · (||d|| + T·μ(d)).
  have h_r0_supp_finite :
      (Function.support (fun d : S => (d.val.norm p : ℚ) *
        ((Sparse.φ₀ hSparse d : ℕ) : ℚ))).Finite := by
    refine hφ_supp_finite.subset ?_
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd ⊢
    intro hφ_zero
    apply hd
    have : ((Sparse.φ₀ hSparse d : ℕ) : ℚ) = 0 := by exact_mod_cast hφ_zero
    rw [this, mul_zero]
  have h_muprod_supp_finite :
      (Function.support (fun d : S =>
        ((Sparse.φ₀ hSparse d : ℕ) : ℚ) * (muQ hf2 d : ℚ))).Finite := by
    refine hφ_supp_finite.subset ?_
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd ⊢
    intro hφ_zero
    apply hd
    have : ((Sparse.φ₀ hSparse d : ℕ) : ℚ) = 0 := by exact_mod_cast hφ_zero
    rw [this, zero_mul]
  -- Distribute the combined sum.
  have h_distrib :
      (∑ᶠ d : S, ((Sparse.φ₀ hSparse d : ℕ) : ℚ) *
        ((d.val.norm p : ℚ) + (T : ℚ) * (muQ hf2 d : ℚ))) =
      (∑ᶠ d : S, ((Sparse.φ₀ hSparse d : ℕ) : ℚ) * (d.val.norm p : ℚ)) +
      (∑ᶠ d : S, ((Sparse.φ₀ hSparse d : ℕ) : ℚ) * ((T : ℚ) * (muQ hf2 d : ℚ))) := by
    rw [← finsum_add_distrib]
    · apply finsum_congr; intro d; ring
    · refine hφ_supp_finite.subset ?_
      intro d hd
      simp only [Function.mem_support, ne_eq] at hd ⊢
      intro hφ_zero
      apply hd
      have : ((Sparse.φ₀ hSparse d : ℕ) : ℚ) = 0 := by exact_mod_cast hφ_zero
      rw [this, zero_mul]
    · refine hφ_supp_finite.subset ?_
      intro d hd
      simp only [Function.mem_support, ne_eq] at hd ⊢
      intro hφ_zero
      apply hd
      have : ((Sparse.φ₀ hSparse d : ℕ) : ℚ) = 0 := by exact_mod_cast hφ_zero
      rw [this, zero_mul]
  -- Pull T out of the second sum.
  have h_pull_T :
      (∑ᶠ d : S, ((Sparse.φ₀ hSparse d : ℕ) : ℚ) * ((T : ℚ) * (muQ hf2 d : ℚ))) =
      (T : ℚ) * ∑ᶠ d : S, ((Sparse.φ₀ hSparse d : ℕ) : ℚ) * (muQ hf2 d : ℚ) := by
    rw [mul_finsum' _ _ h_muprod_supp_finite]
    apply finsum_congr; intro d; ring
  -- Commute the first sum.
  have h_swap :
      (∑ᶠ d : S, ((Sparse.φ₀ hSparse d : ℕ) : ℚ) * (d.val.norm p : ℚ)) =
      (∑ᶠ d : S, (d.val.norm p : ℚ) * ((Sparse.φ₀ hSparse d : ℕ) : ℚ)) := by
    apply finsum_congr; intro d; ring
  -- Combine.
  have h_combined_eq :
      (∑ᶠ d : S, ((Sparse.φ₀ hSparse d : ℕ) : ℚ) *
        ((d.val.norm p : ℚ) + (T : ℚ) * (muQ hf2 d : ℚ))) =
      r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
        (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ) := by
    rw [h_distrib, h_swap, h_pull_T]
    rfl
  rw [← h_combined_eq]
  exact h_combined_isInt

-- Trivial polynomial-degree bound, factored out to avoid heartbeat blowup
-- in the conjunct-(b) discharge.
private lemma Pfhat_map_natDegree_bound
    {p : ℕ} [Fact (Nat.Prime p)] (T : ℕ+)
    {P : Polynomial ℚᵘⁿ_[p]} {n : ℕ} (hP_natDegree : P.natDegree = n) :
    ((P_int P).map (OQpUn_embd p T)).natDegree ≤ n := by
  have h1 : ((P_int P).map (OQpUn_embd p T)).natDegree ≤ (P_int P).natDegree :=
    Polynomial.natDegree_map_le
  have h2 : (P_int P).natDegree ≤ P.natDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have h_P_coeff_zero : P.coeff N = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hN
    -- `(P_int P).coeff N = (integerNormalization _ P).coeff N`, which vanishes when `P.coeff N = 0`
    -- because `integerNormalization` has support contained in that of `P`.
    have h_coeff_zero : (P_int P).coeff N = 0 := by
      rw [← Polynomial.notMem_support_iff]
      exact fun hmem =>
        Polynomial.notMem_support_iff.mpr h_P_coeff_zero
          (IsLocalization.integerNormalization_support (nonZeroDivisors ℤᵘⁿ_[p]) P hmem)
    rw [h_coeff_zero]
  omega

/-- Multiset decomposition of the support of `fhat ^ i`. If `q ∈ (fhat ^ i).support`,
then `q` is the sum of `i` values drawn from `Stilde hf2` (with multiplicity). -/
private lemma fhat_pow_support_multiset_decomp
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    {hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}}
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (h_supp : Function.support fhat.coeff ⊆ Stilde hf2) :
    ∀ (i : ℕ) {q : ℚ},
      q ∈ (fhat ^ i).support →
      ∃ l : Multiset (↥(Stilde hf2)),
        l.card = i ∧ (l.map (fun s => (s.val : ℚ))).sum = q := by
  classical
  intro i
  induction i with
  | zero =>
    intro q hq
    have hq0 : q = 0 := by
      simpa [pow_zero, HahnSeries.support_one] using hq
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp [hq0]
  | succ i ih =>
    intro q hq
    have hq' : q ∈ (fhat ^ i * fhat).support := by
      simpa [pow_succ] using hq
    have h_sub := HahnSeries.support_mul_subset hq'
    rcases (by simpa [Set.mem_add] using h_sub) with ⟨a, ha_supp, b, hb_supp, hab⟩
    have hb_ne : fhat.coeff b ≠ 0 := by
      simpa [HahnSeries.mem_support] using hb_supp
    have hb_fun : b ∈ Function.support fhat.coeff := by
      simpa [Function.mem_support] using hb_ne
    have hb_in_Stilde : b ∈ Stilde hf2 := h_supp hb_fun
    obtain ⟨l_a, hl_a_card, hl_a_sum⟩ := ih ha_supp
    refine ⟨⟨b, hb_in_Stilde⟩ ::ₘ l_a, ?_, ?_⟩
    · simp [hl_a_card]
    · simp [Multiset.map_cons, Multiset.sum_cons, hl_a_sum, add_comm, hab]

/-- Residue-collapse of `(fhat ^ i).coeff q`. If the coefficient is non-zero
and the residue constraint holds, then `i = n` and the unique `phiT`
matching the multiset-count is `Sparse.φ₀ hSparse ∘ μ⁻¹`. -/
private lemma fhat_pow_coeff_residue_collapse
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (h_supp : Function.support fhat.coeff ⊆ Stilde hf2)
    (i : ℕ) (hi_le : i ≤ n) (q : ℚ)
    (hq_residue : ((T : ℚ) * q + r0 hSparse).isInt = true)
    (h_coeff_ne : (fhat ^ i).coeff q ≠ 0) :
    i = n ∧
    ∃! (phiT : ↥(Stilde hf2) → ℕ),
      (Function.support phiT).Finite ∧
      (∑ᶠ s : ↥(Stilde hf2), phiT s ≤ n) ∧
      phiT = Sparse.φ₀ hSparse ∘ (muEquiv hS hf2).symm := by
  classical
  have hq_mem : q ∈ (fhat ^ i).support := by
    simpa [HahnSeries.mem_support] using h_coeff_ne
  obtain ⟨l, hl_card, hl_sum⟩ :=
    fhat_pow_support_multiset_decomp (hf2 := hf2) (fhat := fhat) h_supp i hq_mem
  -- define phiT as the multiplicity/count function of l
  let phiT : ↥(Stilde hf2) → ℕ := (l.toFinsupp : _ →₀ ℕ)
  have hphiT_finite : (Function.support phiT).Finite := by
    simp [phiT]-- using (Finsupp.finite_support (l.toFinsupp))
  -- Bridge: ∑ᶠ phiT = l.card.
  have h_count_bridge : (∑ᶠ s : ↥(Stilde hf2), phiT s) = l.card := by
    have h_supp_subset :
        Function.support phiT ⊆ ((l.toFinsupp).support : Set (↥(Stilde hf2))) := by
      intro s hs
      simp only [Function.mem_support, ne_eq] at hs
      exact Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hs)
    rw [finsum_eq_sum_of_support_subset (s := (l.toFinsupp).support) phiT
      h_supp_subset]
    have hsum_eq : ∑ s ∈ (l.toFinsupp).support, phiT s
        = ∑ s ∈ (l.toFinsupp).support, l.count s := by
      apply Finset.sum_congr rfl
      intro s _
      simp [phiT, Multiset.toFinsupp_apply]
    rw [hsum_eq]
    have h_supp_eq_toFinset : (l.toFinsupp).support = l.toFinset := by
      ext s
      simp [Multiset.mem_toFinset]
    rw [h_supp_eq_toFinset]
    exact Multiset.toFinset_sum_count_eq l
  -- Bound on the sum of phiT (number of factors equals i)
  have hphiT_sum : ∑ᶠ s : ↥(Stilde hf2), phiT s ≤ n := by
    rw [h_count_bridge, hl_card]
    exact hi_le
  -- Residue clause: ∑ᶠ s, s.val * phiT s = q.
  have h_residue_bridge :
      (∑ᶠ s : ↥(Stilde hf2), (s.val : ℚ) * (phiT s : ℚ)) = q := by
    have h_supp_subset :
        Function.support (fun s : ↥(Stilde hf2) => (s.val : ℚ) * (phiT s : ℚ))
          ⊆ ((l.toFinsupp).support : Set (↥(Stilde hf2))) := by
      intro s hs
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hs
      have hphi_ne : (phiT s : ℚ) ≠ 0 := hs.2
      have hphi_ne_nat : phiT s ≠ 0 := by exact_mod_cast hphi_ne
      exact Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hphi_ne_nat)
    rw [finsum_eq_sum_of_support_subset
      (fun s : ↥(Stilde hf2) => (s.val : ℚ) * (phiT s : ℚ))
      (s := (l.toFinsupp).support) h_supp_subset]
    have h_supp_eq_toFinset : (l.toFinsupp).support = l.toFinset := by
      ext s
      simp [Multiset.mem_toFinset]
    rw [h_supp_eq_toFinset]
    -- Goal: ∑ s ∈ l.toFinset, (s.val : ℚ) * (phiT s : ℚ) = q.
    -- Identify phiT s = l.count s on l.toFinset.
    have h_each : ∀ s ∈ l.toFinset,
        (s.val : ℚ) * (phiT s : ℚ) = (s.val : ℚ) * (l.count s : ℚ) := by
      intro s _
      simp [phiT, Multiset.toFinsupp_apply]
    rw [Finset.sum_congr rfl h_each]
    -- Goal: ∑ s ∈ l.toFinset, (s.val : ℚ) * (l.count s : ℚ) = q.
    -- Use Finset.sum_multiset_map_count to identify with (l.map val).sum = q.
    have h_count_form :
        ∑ s ∈ l.toFinset, (s.val : ℚ) * (l.count s : ℚ) =
        ∑ s ∈ l.toFinset, (l.count s : ℕ) • (s.val : ℚ) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [nsmul_eq_mul]; ring
    rw [h_count_form]
    rw [← Finset.sum_multiset_map_count l (fun s : ↥(Stilde hf2) => (s.val : ℚ))]
    exact hl_sum
  -- Residue clause from the multiset sum identity
  have hphiT_residue :
      ((T : ℚ) * (∑ᶠ s : ↥(Stilde hf2), (s.val : ℚ) * (phiT s : ℚ))
        + r0 hSparse).isInt = true := by
    rw [h_residue_bridge]
    exact hq_residue
  have hphiT_eq :
      phiT = Sparse.φ₀ hSparse ∘ (muEquiv hS hf2).symm :=
    phi_tilde_constraint_at_phi0 hS hf2 hSparse phiT hphiT_finite hphiT_sum hphiT_residue
  refine And.intro ?_ ?_
  · -- Deduce i = n.
    -- i = l.card = ∑ᶠ phiT = ∑ᶠ d : S, Sparse.φ₀ hSparse d = n.
    have h_sum_phi_eq_n :
        (∑ᶠ d : S, Sparse.φ₀ hSparse d) = (n : ℕ) := by
      -- φ₀(d) = Nat.card (witness ⁻¹' {d}) and witness : Fin n → S.
      classical
      set witness := hSparse.2.choose with hwit_def
      have hφ₀_finite : (Function.support (Sparse.φ₀ hSparse)).Finite := by
        refine Set.Finite.subset (Set.finite_range witness) ?_
        intro d hd
        simp only [Function.mem_support, Sparse.φ₀, Set.mem_range] at hd ⊢
        by_contra h
        have hempty : witness ⁻¹' {d} = ∅ := by
          ext i
          simp only [Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_empty_iff_false, iff_false]
          intro hi; exact h ⟨i, hi⟩
        rw [hempty] at hd; simp at hd
      -- We'll go via Finset.card_eq_sum_card_fiberwise.
      have h_supp_subset :
          Function.support (Sparse.φ₀ hSparse) ⊆ (hφ₀_finite.toFinset : Set S) := by
        intro d hd
        simpa using hd
      rw [finsum_eq_sum_of_support_subset (Sparse.φ₀ hSparse)
            (s := hφ₀_finite.toFinset) h_supp_subset]
      -- ∑ d ∈ toFinset, φ₀ d = ∑ d ∈ toFinset, |witness⁻¹ {d}| (as ℕ)
      -- = card (Finset.univ : Finset (Fin n)) = n.
      simp only [Sparse.φ₀]
      have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          witness i ∈ hφ₀_finite.toFinset := by
        intro i _
        simp only [Set.Finite.mem_toFinset, Function.mem_support, Sparse.φ₀, ne_eq]
        rw [← hwit_def]
        intro h_card_zero
        have hmem : i ∈ (witness ⁻¹' ({witness i} : Set ↑S)) := by
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
        have h_nonempty : (witness ⁻¹' ({witness i} : Set ↑S)).Nonempty := ⟨i, hmem⟩
        rw [Nat.card_eq_zero] at h_card_zero
        cases h_card_zero with
        | inl h_empty =>
          have : Nonempty ↑(witness ⁻¹' ({witness i} : Set ↑S)) := h_nonempty.to_subtype
          exact not_nonempty_iff.mpr h_empty this
        | inr h_inf =>
          have : Finite ↑(witness ⁻¹' ({witness i} : Set ↑S)) := by infer_instance
          exact absurd this (not_finite_iff_infinite.mpr h_inf)
      -- Compute card by fiberwise sum over witness.
      have h_card_eq : ∀ x : S,
          Nat.card ↑(witness ⁻¹' {x}) =
          (Finset.univ.filter (fun i : Fin n => witness i = x)).card := by
        intro x
        rw [show ↑(witness ⁻¹' {x}) = {i : Fin n // witness i = x} from rfl]
        exact Nat.subtype_card _ (fun i => by simp)
      have h_rhs :
          ∑ d ∈ hφ₀_finite.toFinset, Nat.card ↑(witness ⁻¹' {d}) =
          ∑ d ∈ hφ₀_finite.toFinset,
            (Finset.univ.filter (fun i : Fin n => witness i = d)).card := by
        apply Finset.sum_congr rfl; intro d _; exact h_card_eq d
      have h_maps_to : Set.MapsTo witness
          ((Finset.univ : Finset (Fin n)) : Set (Fin n))
          (hφ₀_finite.toFinset : Set S) :=
        fun i _ => Finset.mem_coe.mpr (h_maps i (Finset.mem_univ i))
      rw [h_rhs]
      rw [← Finset.card_eq_sum_card_fiberwise (f := witness) h_maps_to]
      simp
    -- Now: i = l.card by hl_card; l.card = ∑ᶠ phiT by h_count_bridge;
    -- ∑ᶠ phiT = ∑ᶠ s, (φ₀ ∘ μ.symm) s by hphiT_eq;
    -- = ∑ᶠ d : S, φ₀ d by finsum_comp_equiv along μ.
    have h_chain :
        i = (∑ᶠ d : S, Sparse.φ₀ hSparse d) := by
      rw [← hl_card, ← h_count_bridge]
      have heq : (∑ᶠ s : ↥(Stilde hf2), phiT s) =
          ∑ᶠ s : ↥(Stilde hf2),
            (Sparse.φ₀ hSparse ∘ (muEquiv hS hf2).symm) s := by
        apply finsum_congr; intro s; rw [hphiT_eq]
      rw [heq]
      -- change of variable: along (muEquiv hS hf2).symm
      have := finsum_comp_equiv (muEquiv hS hf2)
        (f := Sparse.φ₀ hSparse ∘ (muEquiv hS hf2).symm)
      -- this : ∑ᶠ d : S, (φ₀ ∘ μ.symm) (μ d) = ∑ᶠ s, (φ₀ ∘ μ.symm) s
      have hcomp : (fun d : S =>
          (Sparse.φ₀ hSparse ∘ (muEquiv hS hf2).symm) ((muEquiv hS hf2) d))
          = Sparse.φ₀ hSparse := by
        funext d
        simp
      rw [hcomp] at this
      exact this.symm
    -- conclude i = n
    have : i = (n : ℕ) := by rw [h_chain, h_sum_phi_eq_n]
    exact_mod_cast this
  · refine ⟨phiT, ?_, ?_⟩
    · exact ⟨hphiT_finite, hphiT_sum, hphiT_eq⟩
    · intro phiU hphiU
      have hUeq : phiU = Sparse.φ₀ hSparse ∘ (muEquiv hS hf2).symm := hphiU.2.2
      have hTeq : phiT = Sparse.φ₀ hSparse ∘ (muEquiv hS hf2).symm := hphiT_eq
      simp [hUeq, hTeq]

/- Closure lemma for the coefficient-collapse argument.

After composing `coeff_pow_eq_sum_over_pi` → `Finset.sum_filter` →
`pi_filter_q0_eq_count_fiber` → `sum_over_functions_with_fixed_counts` →
`product_rewrite_with_coeff_eq`, the remaining reindexing
`∏ a : ↥A, Cs ⟨a, hA⟩ ^ m0 a = ∏ᶠ d : S, Cs (muToStilde d) ^ φ₀(d)`
and the identification
`Nat.cast (Nat.multinomial univ m0) =
  (Nat.multinomial hφ₀_finite.toFinset φ₀ : ℤᵘⁿ_[p,T])`
combine into the multinomial form of the collapsed coefficient.
-/

/-! ### closure-lemma truncation — Sub-lemma 1.

Sub-lemma 1 — `tuple_summing_to_q0_lies_in_A`: ANY tuple
`e : Fin n → ↥(Stilde hf2)` satisfying the residue constraint has every entry
in `μ(supp φ₀)`. The proof builds the multiset count function and invokes
`phi_tilde_constraint_at_phi0`. -/
private lemma tuple_summing_to_q0_lies_in_A
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    {hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}}
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    (_hφ₀_finite : (Function.support (Sparse.φ₀ hSparse)).Finite)
    (e : Fin n → ↥(Stilde hf2))
    (he_residue : ((T : ℚ) * (∑ i : Fin n, ((e i).val : ℚ)) +
                    r0 hSparse).isInt = true) :
    ∀ i : Fin n, ∃ d : S,
      Sparse.φ₀ hSparse d ≠ 0 ∧ (e i).val = muQ hf2 d := by
  classical
  -- Build the multiset l_e of (e i)'s and its toFinsupp count function phiT.
  let l_e : Multiset (↥(Stilde hf2)) :=
    (Finset.univ : Finset (Fin n)).val.map (fun i : Fin n => e i)
  let phiT : ↥(Stilde hf2) → ℕ := (l_e.toFinsupp : _ →₀ ℕ)
  -- card l_e = n.
  have hl_e_card : l_e.card = (n : ℕ) := by simp [l_e]
  -- (l_e.map val).sum = ∑ i, (e i).val.
  have hl_e_sum : (l_e.map (fun s => (s.val : ℚ))).sum
      = ∑ i : Fin n, ((e i).val : ℚ) := by
    simp [l_e, Function.comp_def, Finset.sum]
  -- Finite support of phiT.
  have hphiT_finite : (Function.support phiT).Finite := by
    simp [phiT]-- using (Finsupp.finite_support l_e.toFinsupp)
  -- Bridge: ∑ᶠ phiT = l_e.card.
  have h_count_bridge : (∑ᶠ s : ↥(Stilde hf2), phiT s) = l_e.card := by
    have h_supp_subset :
        Function.support phiT ⊆ ((l_e.toFinsupp).support : Set (↥(Stilde hf2))) := by
      intro s hs
      simp only [Function.mem_support, ne_eq] at hs
      exact Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hs)
    rw [finsum_eq_sum_of_support_subset (s := (l_e.toFinsupp).support) phiT
      h_supp_subset]
    have hsum_eq : ∑ s ∈ (l_e.toFinsupp).support, phiT s
        = ∑ s ∈ (l_e.toFinsupp).support, l_e.count s := by
      apply Finset.sum_congr rfl
      intro s _
      simp [phiT, Multiset.toFinsupp_apply]
    rw [hsum_eq]
    have h_supp_eq_toFinset : (l_e.toFinsupp).support = l_e.toFinset := by
      ext s
      simp [Multiset.mem_toFinset]
    rw [h_supp_eq_toFinset]
    exact Multiset.toFinset_sum_count_eq l_e
  have hphiT_sum : ∑ᶠ s : ↥(Stilde hf2), phiT s ≤ n := by
    rw [h_count_bridge, hl_e_card]
  -- Bridge: ∑ᶠ s, (s.val : ℚ) * (phiT s : ℚ) = ∑ i, (e i).val.
  have h_residue_bridge :
      (∑ᶠ s : ↥(Stilde hf2), (s.val : ℚ) * (phiT s : ℚ))
        = ∑ i : Fin n, ((e i).val : ℚ) := by
    have h_supp_subset :
        Function.support (fun s : ↥(Stilde hf2) => (s.val : ℚ) * (phiT s : ℚ))
          ⊆ ((l_e.toFinsupp).support : Set (↥(Stilde hf2))) := by
      intro s hs
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hs
      have hphi_ne : (phiT s : ℚ) ≠ 0 := hs.2
      have hphi_ne_nat : phiT s ≠ 0 := by exact_mod_cast hphi_ne
      exact Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hphi_ne_nat)
    rw [finsum_eq_sum_of_support_subset
      (fun s : ↥(Stilde hf2) => (s.val : ℚ) * (phiT s : ℚ))
      (s := (l_e.toFinsupp).support) h_supp_subset]
    have h_supp_eq_toFinset : (l_e.toFinsupp).support = l_e.toFinset := by
      ext s
      simp [Multiset.mem_toFinset]
    rw [h_supp_eq_toFinset]
    have h_each : ∀ s ∈ l_e.toFinset,
        (s.val : ℚ) * (phiT s : ℚ) = (s.val : ℚ) * (l_e.count s : ℚ) := by
      intro s _
      simp [phiT, Multiset.toFinsupp_apply]
    rw [Finset.sum_congr rfl h_each]
    have h_count_form :
        ∑ s ∈ l_e.toFinset, (s.val : ℚ) * (l_e.count s : ℚ) =
        ∑ s ∈ l_e.toFinset, (l_e.count s : ℕ) • (s.val : ℚ) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [nsmul_eq_mul]; ring
    rw [h_count_form]
    rw [← Finset.sum_multiset_map_count l_e (fun s : ↥(Stilde hf2) => (s.val : ℚ))]
    exact hl_e_sum
  have hphiT_residue :
      ((T : ℚ) * (∑ᶠ s : ↥(Stilde hf2), (s.val : ℚ) * (phiT s : ℚ))
        + r0 hSparse).isInt = true := by
    rw [h_residue_bridge]; exact he_residue
  -- Apply phi_tilde_constraint_at_phi0 to conclude phiT = φ₀ ∘ μ.symm.
  have hphiT_eq :
      phiT = Sparse.φ₀ hSparse ∘ (muEquiv hS hf2).symm :=
    phi_tilde_constraint_at_phi0 hS hf2 hSparse phiT hphiT_finite hphiT_sum hphiT_residue
  -- Now derive the conclusion for each i : Fin n.
  intro i
  -- e i ∈ l_e.
  have h_mem_l_e : e i ∈ l_e := by
    change e i ∈ (Finset.univ : Finset (Fin n)).val.map (fun i : Fin n => e i)
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  -- phiT (e i) ≥ 1.
  have h_phiT_pos : 1 ≤ phiT (e i) := by
    change 1 ≤ l_e.toFinsupp (e i)
    rw [Multiset.toFinsupp_apply]
    exact Multiset.one_le_count_iff_mem.mpr h_mem_l_e
  -- phiT (e i) = φ₀ (μ.symm (e i)).
  have h_phiT_at_i :
      phiT (e i) = Sparse.φ₀ hSparse ((muEquiv hS hf2).symm (e i)) := by
    have := congrFun hphiT_eq (e i)
    simpa [Function.comp_apply] using this
  refine ⟨(muEquiv hS hf2).symm (e i), ?_, ?_⟩
  · -- φ₀ (μ.symm (e i)) ≠ 0.
    intro h_phi_zero
    have h_phiT_zero : phiT (e i) = 0 := by rw [h_phiT_at_i, h_phi_zero]
    omega
  · -- (e i).val = muQ hf2 (μ.symm (e i)).
    have h_apply : (muEquiv hS hf2) ((muEquiv hS hf2).symm (e i)) = e i :=
      Equiv.apply_symm_apply (muEquiv hS hf2) (e i)
    -- ((muEquiv hS hf2) d).val = muQ hf2 d by definition of muEquiv / muToStilde.
    have h_val_at_symm :
        ((muEquiv hS hf2) ((muEquiv hS hf2).symm (e i)) : ↥(Stilde hf2)).val
        = muQ hf2 ((muEquiv hS hf2).symm (e i)) := rfl
    have h_val_eq_ei : ((muEquiv hS hf2) ((muEquiv hS hf2).symm (e i)) : ↥(Stilde hf2)).val
        = (e i).val := by rw [h_apply]
    exact h_val_eq_ei.symm.trans h_val_at_symm

/-! ### closure-lemma truncation — Sub-lemma 2 and the truncation `fhatAOf`.

The truncation of `fhat` to support contained in `μ(supp φ₀)`, used in
Sub-lemma 2 (`coeff_pow_truncate_eq`).
The definition uses an explicit finite sum of `HahnSeries.single`. -/
private noncomputable def fhatAOf
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    (fhat : TLiftedPAdicHahnSeries p (T : ℕ))
    (hφ₀_finite : (Function.support (Sparse.φ₀ hSparse)).Finite) :
    TLiftedPAdicHahnSeries p (T : ℕ) :=
  -- Explicit truncation: sum HahnSeries.single (muQ hf2 d) (fhat.coeff (muQ hf2 d))
  -- over d ∈ supp φ₀. The support of the result is contained in μ(supp φ₀),
  -- so A4a applies after this truncation.
  ∑ d ∈ hφ₀_finite.toFinset,
    HahnSeries.single (muQ hf2 d) (fhat.coeff (muQ hf2 d))

/-- Sub-lemma 2 (`coeff_pow_truncate_eq`).

Proves `(fhat^n).coeff q0 = (fhatAOf)^n.coeff q0`. The proof goes by induction on
`n`, expanding via `HahnSeries.coeff_mul_left'` (from
`Mathlib.RingTheory.HahnSeries.Multiplication`) on each side; every contributing
pair `(a, b)` with `a + b = q0` and `fhat.coeff a ≠ 0`, `(fhat^(k))(b) ≠ 0`,
forces `a ∈ μ(supp φ₀)` via Sub-lemma 1 applied to the (k+1)-tuple obtained
from `b`'s multiset decomposition extended by `a`. The induction terminates at
`n` because every n-tuple summing to q0 has count function `φ₀ ∘ μ.symm`,
whose support is `μ(supp φ₀)`. -/
private lemma coeff_pow_truncate_eq
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    {Cs : ↥(Stilde hf2) → ℤᵘⁿ_[p,(T : ℕ)]}
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (h_supp : Function.support fhat.coeff ⊆ Stilde hf2)
    (_h_coeff_eq : ∀ (s : ↥(Stilde hf2)), fhat.coeff s.val = Cs s)
    (_hCs_ne : ∀ s : ↥(Stilde hf2), Cs s ≠ 0)
    (hφ₀_finite : (Function.support (Sparse.φ₀ hSparse)).Finite) :
    (fhat ^ (n : ℕ)).coeff
        (-(r0 hSparse) / T +
          ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
            (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num : ℚ) / T) =
      (fhatAOf hf2 hSparse fhat hφ₀_finite ^ (n : ℕ)).coeff
        (-(r0 hSparse) / T +
          ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
            (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num : ℚ) / T) := by
  classical
  -- Setup: name fhatA, q0, and the set A := μ(supp φ₀).
  set fhatA := fhatAOf hf2 hSparse fhat hφ₀_finite with hfhatA_def
  set q0 : ℚ := -(r0 hSparse) / T +
        ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
          (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num : ℚ) / T
        with hq0_def
  -- A := image of supp φ₀ under muQ.
  set A : Set ℚ := {a | ∃ d : S, Sparse.φ₀ hSparse d ≠ 0 ∧ a = muQ hf2 d}
        with hA_def
  -- (A0) A ⊆ Stilde hf2.
  have hA_sub_Stilde : A ⊆ Stilde hf2 := by
    rintro a ⟨d, _, rfl⟩
    exact ⟨d, rfl⟩
  -- (A1) For a ∈ A, fhatA.coeff a = fhat.coeff a — sum collapses to one term.
  have h_fhatA_in_A : ∀ a ∈ A, fhatA.coeff a = fhat.coeff a := by
    rintro a ⟨d₀, hd₀_ne, rfl⟩
    change (∑ d ∈ hφ₀_finite.toFinset,
        HahnSeries.single (muQ hf2 d) (fhat.coeff (muQ hf2 d))).coeff (muQ hf2 d₀) = _
    rw [HahnSeries.coeff_sum]
    have hd₀_mem : d₀ ∈ hφ₀_finite.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact hd₀_ne
    rw [Finset.sum_eq_single d₀]
    · exact HahnSeries.coeff_single_same _ _
    · intro d _ hne
      exact HahnSeries.coeff_single_of_ne (fun h => hne (muQ_injective hS hf2 h.symm))
    · intro h; exact absurd hd₀_mem h
  -- (A2) For a ∉ A, fhatA.coeff a = 0 — all summands vanish.
  have h_fhatA_not_A : ∀ a, a ∉ A → fhatA.coeff a = 0 := by
    intro a ha_notA
    change (∑ d ∈ hφ₀_finite.toFinset,
        HahnSeries.single (muQ hf2 d) (fhat.coeff (muQ hf2 d))).coeff a = 0
    rw [HahnSeries.coeff_sum]
    apply Finset.sum_eq_zero
    intro d hd
    apply HahnSeries.coeff_single_of_ne
    intro h
    refine ha_notA ⟨d, ?_, h⟩
    rw [Set.Finite.mem_toFinset] at hd
    exact hd
  -- (A3) fhatA.support ⊆ A ⊆ Stilde hf2.
  have h_fhatA_supp_A : fhatA.support ⊆ A := by
    intro a ha_mem
    by_contra ha_notA
    exact ((HahnSeries.mem_support _ _).mp ha_mem) (h_fhatA_not_A a ha_notA)
  have h_fhatA_supp_Stilde : fhatA.support ⊆ Stilde hf2 :=
    h_fhatA_supp_A.trans hA_sub_Stilde
  -- (B) Witness propagation lemma — passing from W(k+1, q) to W(k, q-i) for i ∈ A.
  have h_propagate : ∀ (k : ℕ) (q i : ℚ), i ∈ A →
      (∀ l : Multiset ↥(Stilde hf2),
        l.card = k + 1 → (l.map (fun s => (s.val : ℚ))).sum = q →
        ∀ s ∈ l, s.val ∈ A) →
      (∀ l : Multiset ↥(Stilde hf2),
        l.card = k → (l.map (fun s => (s.val : ℚ))).sum = q - i →
        ∀ s ∈ l, s.val ∈ A) := by
    intros k q i hi_A hwit l hl_card hl_sum s hs_mem
    let s_i : ↥(Stilde hf2) := ⟨i, hA_sub_Stilde hi_A⟩
    let l' : Multiset ↥(Stilde hf2) := s_i ::ₘ l
    have hl'_card : l'.card = k + 1 := by
      change (s_i ::ₘ l).card = k + 1
      rw [Multiset.card_cons, hl_card]
    have hl'_sum : (l'.map (fun s => (s.val : ℚ))).sum = q := by
      change ((s_i ::ₘ l).map (fun s => (s.val : ℚ))).sum = q
      rw [Multiset.map_cons, Multiset.sum_cons]
      change (i + (l.map (fun s => (s.val : ℚ))).sum) = q
      rw [hl_sum]; ring
    exact hwit l' hl'_card hl'_sum s (Multiset.mem_cons.mpr (Or.inr hs_mem))
  -- (C) Strengthened claim — proved by induction on k.
  suffices H : ∀ (k : ℕ) (q : ℚ),
      (∀ l : Multiset (↥(Stilde hf2)),
        l.card = k → (l.map (fun s => (s.val : ℚ))).sum = q →
        ∀ s ∈ l, s.val ∈ A) →
      (fhat^k).coeff q = (fhatA^k).coeff q by
    -- Apply at (n, q0). Witness W(n, q0) follows from Sub-lemma 1.
    apply H (n : ℕ) q0
    intro l hl_card hl_sum s hs_mem
    -- Convert multiset l (of size n) to Fin n → ↥(Stilde hf2) tuple.
    have hl_length : l.toList.length = (n : ℕ) := by
      rw [Multiset.length_toList]; exact hl_card
    let e : Fin (n : ℕ) → ↥(Stilde hf2) :=
      fun i => l.toList.get (Fin.cast hl_length.symm i)
    -- Sum identity: ∑ i : Fin n, (e i).val = q0.
    have he_sum : (∑ i : Fin (n : ℕ), ((e i).val : ℚ)) = q0 := by
      have h1 : (∑ i : Fin (n : ℕ), ((e i).val : ℚ)) =
          (l.toList.map (fun s : ↥(Stilde hf2) => (s.val : ℚ))).sum := by
        rw [← List.ofFn_getElem_eq_map l.toList (fun s : ↥(Stilde hf2) => (s.val : ℚ)),
            List.sum_ofFn]
        exact Fintype.sum_equiv (finCongr hl_length.symm)
          (fun i => ((e i).val : ℚ))
          (fun j => ((l.toList[(j : ℕ)] : ↥(Stilde hf2)).val : ℚ))
          (fun _ => rfl)
      have h2 : (l.toList.map (fun s : ↥(Stilde hf2) => (s.val : ℚ))).sum =
          (l.map (fun s : ↥(Stilde hf2) => (s.val : ℚ))).sum := by
        rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList]
      rw [h1, h2]; exact hl_sum
    -- Residue condition: (T·q0 + r0).isInt = true.
    have hq0_residue : ((T : ℚ) * q0 + r0 hSparse).isInt = true := by
      have hT_ne : (T : ℚ) ≠ 0 := by exact_mod_cast PNat.ne_zero T
      have hk_eq : (T : ℚ) * q0 + r0 hSparse =
          ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
            (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num : ℚ) := by
        rw [hq0_def]; field_simp; ring
      rw [hk_eq]; exact isInt_intCast' _
    have he_residue : ((T : ℚ) * (∑ i : Fin (n : ℕ), ((e i).val : ℚ)) + r0 hSparse).isInt
        = true := by rw [he_sum]; exact hq0_residue
    -- Apply Sub-lemma 1.
    have h_sub1 := tuple_summing_to_q0_lies_in_A hSparse hφ₀_finite e he_residue
    -- s ∈ l, so s ∈ l.toList, so ∃ idx with l.toList.get idx = s.
    have hs_in_list : s ∈ l.toList := Multiset.mem_toList.mpr hs_mem
    obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp hs_in_list
    -- Map idx through hl_length to a Fin n.
    let i_n : Fin (n : ℕ) := Fin.cast hl_length idx
    have he_at_in : e i_n = s := by
      change l.toList.get (Fin.cast hl_length.symm i_n) = s
      have h_cast : Fin.cast hl_length.symm i_n = idx := by
        change Fin.cast hl_length.symm (Fin.cast hl_length idx) = idx
        ext; rfl
      rw [h_cast]; exact hidx
    obtain ⟨d, hd_ne, hd_eq⟩ := h_sub1 i_n
    refine ⟨d, hd_ne, ?_⟩
    rw [← he_at_in]; exact hd_eq
  -- Main induction proof.
  intro k
  induction k with
  | zero =>
    intro q _
    show (fhat^0).coeff q = (fhatA^0).coeff q
    rw [pow_zero, pow_zero]
  | succ k ih =>
    intro q hwit
    -- Strategy: show (fhat^(k+1) - fhatA^(k+1)).coeff q = 0 via decomposition
    -- fhat^(k+1) - fhatA^(k+1) = (fhat - fhatA) * fhat^k + fhatA * (fhat^k - fhatA^k)
    -- and prove each piece's coefficient is zero at q.
    have h_decomp : fhat^(k+1) - fhatA^(k+1) =
        (fhat - fhatA) * fhat^k + fhatA * (fhat^k - fhatA^k) := by
      rw [pow_succ' fhat k, pow_succ' fhatA k]; ring
    -- PIECE 1: ((fhat - fhatA) * fhat^k).coeff q = 0.
    have h_piece1 : ((fhat - fhatA) * fhat^k).coeff q = 0 := by
      have h_fmA_supp : (fhat - fhatA).support ⊆ Stilde hf2 :=
        (HahnSeries.support_sub_subset fhat fhatA).trans
          (Set.union_subset h_supp h_fhatA_supp_Stilde)
      rw [HahnSeries.coeff_mul_left' (Stilde_isPWO hf2) h_fmA_supp]
      apply Finset.sum_eq_zero
      intro ij hij
      rw [Finset.mem_antidiagonal] at hij
      obtain ⟨hi_Stilde, _, hij_sum⟩ := hij
      -- Case split on ij.1 ∈ A.
      by_cases h_inA : ij.1 ∈ A
      · -- (fhat - fhatA).coeff ij.1 = fhat.coeff ij.1 - fhat.coeff ij.1 = 0.
        have : (fhat - fhatA).coeff ij.1 = 0 := by
          rw [HahnSeries.coeff_sub, h_fhatA_in_A ij.1 h_inA, sub_self]
        rw [this, zero_mul]
      · -- ij.1 ∉ A. Show (fhat^k).coeff ij.2 = 0 (contradicting witness if not).
        have h_fA_zero : fhatA.coeff ij.1 = 0 := h_fhatA_not_A ij.1 h_inA
        have h_sub_eq : (fhat - fhatA).coeff ij.1 = fhat.coeff ij.1 := by
          rw [HahnSeries.coeff_sub, h_fA_zero, sub_zero]
        rw [h_sub_eq]
        -- Now show fhat.coeff ij.1 * (fhat^k).coeff ij.2 = 0.
        by_cases h_fhat_zero : fhat.coeff ij.1 = 0
        · rw [h_fhat_zero, zero_mul]
        · -- fhat.coeff ij.1 ≠ 0. Show (fhat^k).coeff ij.2 = 0.
          have h_pwk_zero : (fhat^k).coeff ij.2 = 0 := by
            by_contra h_pwk_ne
            have hj_mem_supp : ij.2 ∈ (fhat^k).support :=
              (HahnSeries.mem_support _ _).mpr h_pwk_ne
            obtain ⟨l, hl_card, hl_sum⟩ :=
              fhat_pow_support_multiset_decomp (hf2 := hf2)
                (fhat := fhat) h_supp k hj_mem_supp
            have hi_in_supp : ij.1 ∈ Function.support fhat.coeff := h_fhat_zero
            have hi_in_Stilde : ij.1 ∈ Stilde hf2 := h_supp hi_in_supp
            let s_i : ↥(Stilde hf2) := ⟨ij.1, hi_in_Stilde⟩
            let l' : Multiset ↥(Stilde hf2) := s_i ::ₘ l
            have hl'_card : l'.card = k + 1 := by
              change (s_i ::ₘ l).card = k + 1
              rw [Multiset.card_cons, hl_card]
            have hl'_sum : (l'.map (fun s => (s.val : ℚ))).sum = q := by
              change ((s_i ::ₘ l).map (fun s => (s.val : ℚ))).sum = q
              rw [Multiset.map_cons, Multiset.sum_cons]
              change (ij.1 + (l.map (fun s => (s.val : ℚ))).sum) = q
              rw [hl_sum]; exact hij_sum
            have h_si_in_A := hwit l' hl'_card hl'_sum s_i (Multiset.mem_cons_self _ _)
            exact h_inA h_si_in_A
          rw [h_pwk_zero, mul_zero]
    -- PIECE 2: (fhatA * (fhat^k - fhatA^k)).coeff q = 0.
    have h_piece2 : (fhatA * (fhat^k - fhatA^k)).coeff q = 0 := by
      rw [HahnSeries.coeff_mul_left' (Stilde_isPWO hf2) h_fhatA_supp_Stilde]
      apply Finset.sum_eq_zero
      intro ij hij
      rw [Finset.mem_antidiagonal] at hij
      obtain ⟨_, _, hij_sum⟩ := hij
      by_cases h_fA_zero : fhatA.coeff ij.1 = 0
      · rw [h_fA_zero, zero_mul]
      · -- fhatA.coeff ij.1 ≠ 0, so ij.1 ∈ fhatA.support ⊆ A.
        have hi_in_A : ij.1 ∈ A :=
          h_fhatA_supp_A ((HahnSeries.mem_support _ _).mpr h_fA_zero)
        -- Use witness propagation to get W(k, ij.2), where ij.2 = q - ij.1.
        have hj_eq : ij.2 = q - ij.1 := by linarith
        have hwit_j : ∀ l : Multiset ↥(Stilde hf2),
            l.card = k → (l.map (fun s => (s.val : ℚ))).sum = ij.2 →
            ∀ s ∈ l, s.val ∈ A := by
          rw [hj_eq]; exact h_propagate k q ij.1 hi_in_A hwit
        -- Apply IH at (k, ij.2).
        have h_ih_eq : (fhat^k).coeff ij.2 = (fhatA^k).coeff ij.2 := ih ij.2 hwit_j
        have h_diff_zero : (fhat^k - fhatA^k).coeff ij.2 = 0 := by
          rw [HahnSeries.coeff_sub, h_ih_eq, sub_self]
        rw [h_diff_zero, mul_zero]
    -- Combine: (fhat^(k+1) - fhatA^(k+1)).coeff q = 0.
    have h_total : (fhat^(k+1) - fhatA^(k+1)).coeff q = 0 := by
      rw [h_decomp, HahnSeries.coeff_add, h_piece1, h_piece2, add_zero]
    -- Conclude: (fhat^(k+1)).coeff q = (fhatA^(k+1)).coeff q.
    have h_sub_zero : (fhat^(k+1)).coeff q - (fhatA^(k+1)).coeff q = 0 := by
      rw [← HahnSeries.coeff_sub]; exact h_total
    exact sub_eq_zero.mp h_sub_zero

/-! ### auxiliary combinatorics.

The next group of lemmas develops the finite combinatorics needed for the
collapse of the coefficient at the distinguished exponent. -/

/-- Coefficient of a HahnSeries power as a finite sum over n-tuples. For a HahnSeries
`f` with support contained in a finite set `A`, the coefficient of `f^n` at `q`
equals a finite sum over `Fin n → ↥A` of the product of coefficients, subject to
a sum-of-coordinates condition. This is the Cauchy-product unfolded n times. -/
private lemma coeff_pow_eq_sum_over_pi
    {Γ : Type*} [DecidableEq Γ] [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ]
    {R : Type*} [CommSemiring R]
    (f : HahnSeries Γ R) (A : Finset Γ)
    (hsupp : (Function.support f.coeff : Set Γ) ⊆ (A : Set Γ))
    (n : ℕ) (q : Γ) :
    (f ^ n).coeff q =
      ∑ e : Fin n → ↥A,
        if (∑ i : Fin n, ((e i : Γ))) = q
        then ∏ i : Fin n, f.coeff ((e i : Γ))
        else 0 := by
  classical
  -- Helper 1: product of singles = single of (sum-of-exponents, product-of-coefficients).
  have prod_single :
      ∀ (s : Finset (Fin n)) (a : Fin n → Γ) (r : Fin n → R),
        ∏ i ∈ s, HahnSeries.single (a i) (r i)
          = HahnSeries.single (∑ i ∈ s, a i) (∏ i ∈ s, r i) := by
    intro s a r
    classical
    induction s using Finset.induction with
    | empty => simp
    | insert i s hni ih =>
      rw [Finset.prod_insert hni, ih, Finset.sum_insert hni, Finset.prod_insert hni]
      exact HahnSeries.single_mul_single
  -- Helper 2: decomposition `f = ∑ a : ↥A, single a.val (f.coeff a.val)` using `hsupp`.
  have h_decomp : f = ∑ a : ↥A, HahnSeries.single (a.val) (f.coeff a.val) := by
    apply HahnSeries.ext
    funext q'
    rw [HahnSeries.coeff_sum]
    by_cases hq' : q' ∈ A
    · rw [Finset.sum_eq_single (⟨q', hq'⟩ : ↥A)]
      · rw [HahnSeries.coeff_single_same]
      · intro a _ ha
        rw [HahnSeries.coeff_single]; rw [if_neg]
        intro heq; apply ha; ext; exact heq.symm
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hf0 : f.coeff q' = 0 := by
        by_contra h; exact hq' (hsupp h)
      rw [hf0]
      symm
      apply Finset.sum_eq_zero
      intro a _
      rw [HahnSeries.coeff_single]; rw [if_neg]
      intro h; rw [h] at hq'; exact hq' a.property
  -- Main step: expand f^n via Fintype.sum_pow and `prod_single`.
  have h_pow : (f^n).coeff q
      = ∑ p : Fin n → ↥A,
          (HahnSeries.single (∑ i : Fin n, ((p i).val : Γ))
             (∏ i : Fin n, f.coeff ((p i).val : Γ))).coeff q := by
    have hpow_eq : f^n = (∑ a : ↥A, HahnSeries.single (a.val) (f.coeff a.val))^n := by
      rw [← h_decomp]
    rw [hpow_eq, Fintype.sum_pow, HahnSeries.coeff_sum]
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    exact prod_single Finset.univ (fun i => (p i).val) (fun i => f.coeff (p i).val)
  rw [h_pow]
  -- Final: convert `(single x r).coeff q` into the ite form.
  apply Finset.sum_congr rfl
  intro p _
  rw [HahnSeries.coeff_single]
  by_cases h : (∑ i : Fin n, ((p i).val : Γ)) = q
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

/- Fiber-cardinality via orbit-stabilizer.

The fiber-cardinality identity: the number of functions `Fin n → A` with
prescribed multiplicities `m0 : A → ℕ` is the multinomial coefficient
`n! / (∏ m0 a !)`. This is the standard combinatorial fact (Concrete
Mathematics §5.2, Stanley EC1 §1.2), proved here using
`DomMulAct.stabilizerMulEquiv` + orbit-stabilizer theorem.

The proof is split into 3 named auxiliaries:
- `exists_function_with_count_vector_aux` (witness construction).
- `orbit_perm_dom_eq_count_fiber_aux` (orbit = count-fiber set equality).
- `stabilizer_perm_dom_card_aux` (stabilizer cardinality = ∏ a, (m0 a)!).

The final assembly combines these with
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group` and
`Nat.multinomial_spec`. -/

/-- Fintype instance for `Mᵐᵒᵖ` when `M` is a Fintype.
Local helper for the orbit-stabilizer route to the fiber-cardinality lemma. -/
private instance opFintype' (M : Type*) [Fintype M] : Fintype Mᵐᵒᵖ :=
  Fintype.ofEquiv _ MulOpposite.opEquiv

/-- Fintype instance for `(Equiv.Perm (Fin n))ᵈᵐᵃ`.
Local helper for the orbit-stabilizer route to the fiber-cardinality lemma. -/
private instance permDomMulActFintype' (n : ℕ) :
    Fintype (Equiv.Perm (Fin n))ᵈᵐᵃ :=
  Fintype.ofEquiv _ DomMulAct.mk

/-- Witness construction `e₀ : Fin n → A` with prescribed counts.
Given `∑ a, m0 a = n`, exhibit `e₀ : Fin n → A` whose fiber over each `a` has
cardinality `m0 a`. Uses the σ-construction `Σ a : A, Fin (m0 a) ≃ Fin n`. -/
private lemma exists_function_with_count_vector_aux
    {A : Type*} [DecidableEq A] [Fintype A]
    (n : ℕ) (m0 : A → ℕ) (hm0 : ∑ a, m0 a = n) :
    ∃ e₀ : Fin n → A, ∀ a, Fintype.card {i : Fin n | e₀ i = a} = m0 a := by
  classical
  let B : Type _ := Σ a : A, Fin (m0 a)
  have hcardB : Fintype.card B = n := by
    rw [Fintype.card_sigma]; simp only [Fintype.card_fin]; exact hm0
  let θ : Fin n ≃ B := (Fintype.equivFinOfCardEq hcardB).symm
  refine ⟨fun i => (θ i).1, ?_⟩
  intro a
  have h_card : Fintype.card { i : Fin n // (θ i).1 = a } = m0 a := by
    have e1 : { i : Fin n // (θ i).1 = a } ≃ { b : B // b.1 = a } :=
      { toFun := fun ⟨i, hi⟩ => ⟨θ i, hi⟩
        invFun := fun ⟨b, hb⟩ => ⟨θ.symm b, by rw [θ.apply_symm_apply]; exact hb⟩
        left_inv := fun ⟨i, _⟩ => Subtype.ext (θ.symm_apply_apply i)
        right_inv := fun ⟨b, _⟩ => Subtype.ext (θ.apply_symm_apply b) }
    rw [Fintype.card_congr e1]
    have e2 : { b : B // b.1 = a } ≃ Fin (m0 a) :=
      { toFun := fun ⟨⟨_, k⟩, hb⟩ => k.cast (congrArg m0 hb)
        invFun := fun k => ⟨⟨a, k⟩, rfl⟩
        left_inv := fun ⟨⟨_, k⟩, hb⟩ => by subst hb; rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e2, Fintype.card_fin]
  exact h_card

/-- Stabilizer cardinality for orbit-stabilizer on `Fin n → A`.
The stabilizer of `e₀` under the `DomMulAct` (right-composition) action of
`Equiv.Perm (Fin n)` has cardinality `∏ a : A, (m0 a)!`. Uses
`DomMulAct.stabilizerMulEquiv` to identify the stabilizer with
`Π a : A, Equiv.Perm {i // e₀ i = a}`. -/
private lemma stabilizer_perm_dom_card_aux
    {A : Type*} [DecidableEq A] [Fintype A] {n : ℕ}
    (m0 : A → ℕ) (e₀ : Fin n → A)
    (he₀ : ∀ a, Fintype.card {i : Fin n | e₀ i = a} = m0 a) :
    Fintype.card (MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ e₀)
    = ∏ a : A, (m0 a).factorial := by
  classical
  have h_equiv := (DomMulAct.stabilizerMulEquiv (α := Fin n) (ι := A) e₀).toEquiv
  have : Fintype (↥(MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ e₀))ᵐᵒᵖ :=
    Fintype.ofEquiv _ MulOpposite.opEquiv
  rw [show Fintype.card ↥(MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ e₀)
      = Fintype.card (↥(MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ e₀))ᵐᵒᵖ from
    Fintype.card_congr MulOpposite.opEquiv]
  rw [Fintype.card_congr h_equiv, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro a _
  rw [Fintype.card_perm]
  have : Fintype.card { i : Fin n // e₀ i = a } = m0 a := by
    rw [← he₀ a]; exact Fintype.card_congr (Equiv.setCongr rfl).symm
  rw [this]

/-- Orbit = count-vector fiber under `DomMulAct` action.
The orbit of `e₀ : Fin n → A` under right-composition by `Equiv.Perm (Fin n)`
equals the set of functions with the same count vector as `e₀`. The forward
direction (orbit ⊆ fiber) is direct (precomposition preserves counts); the
reverse direction (fiber ⊆ orbit) uses the σ-construction with packing equivs
`pack_e : Fin n ≃ Σ a, {i // e i = a}` and `pack_e0`. -/
private lemma orbit_perm_dom_eq_count_fiber_aux
    {A : Type*} [DecidableEq A] {n : ℕ} (m0 : A → ℕ)
    (e₀ : Fin n → A) (he₀ : ∀ a, Fintype.card {i : Fin n | e₀ i = a} = m0 a) :
    MulAction.orbit (Equiv.Perm (Fin n))ᵈᵐᵃ e₀
    = {e : Fin n → A | ∀ a, Fintype.card {i : Fin n | e i = a} = m0 a} := by
  classical
  ext e
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hg⟩
    obtain ⟨g₀, rfl⟩ := DomMulAct.mk.surjective g
    intro a
    have hg' : DomMulAct.mk g₀ • e₀ = e := hg
    have key : Fintype.card {i : Fin n // (DomMulAct.mk g₀ • e₀) i = a}
        = Fintype.card {j : Fin n // e₀ j = a} := by
      refine Fintype.card_congr ?_
      refine ⟨fun ⟨i, hi⟩ => ⟨g₀ i, hi⟩, fun ⟨j, hj⟩ => ⟨g₀.symm j, ?_⟩, ?_, ?_⟩
      · change e₀ (g₀ (g₀.symm j)) = a; rw [g₀.apply_symm_apply]; exact hj
      · intro ⟨i, _⟩; apply Subtype.ext; exact g₀.symm_apply_apply i
      · intro ⟨j, _⟩; apply Subtype.ext; exact g₀.apply_symm_apply j
    rw [← hg']
    rw [show Fintype.card ↑{i : Fin n | (DomMulAct.mk g₀ • e₀) i = a}
        = Fintype.card { i : Fin n // (DomMulAct.mk g₀ • e₀) i = a } from
      Fintype.card_congr (Equiv.refl _)]
    rw [key]
    rw [← he₀ a]; exact Fintype.card_congr (Equiv.setCongr rfl).symm
  · intro he
    have h_count_eq : ∀ a, Fintype.card {i : Fin n // e i = a}
                      = Fintype.card {i : Fin n // e₀ i = a} := by
      intro a
      have h1 : Fintype.card { i : Fin n // e i = a } = m0 a := by
        rw [← he a]; exact Fintype.card_congr (Equiv.setCongr rfl).symm
      have h2 : Fintype.card { i : Fin n // e₀ i = a } = m0 a := by
        rw [← he₀ a]; exact Fintype.card_congr (Equiv.setCongr rfl).symm
      omega
    let βa : (a : A) → {i : Fin n // e i = a} ≃ {i : Fin n // e₀ i = a} := fun a =>
      Fintype.equivOfCardEq (h_count_eq a)
    let pack_e : Fin n ≃ Σ a : A, {i : Fin n // e i = a} :=
      { toFun := fun i => ⟨e i, ⟨i, rfl⟩⟩
        invFun := fun ⟨_, ⟨i, _⟩⟩ => i
        left_inv := fun _ => rfl
        right_inv := fun ⟨a, ⟨i, h⟩⟩ => by subst h; rfl }
    let pack_e0 : Fin n ≃ Σ a : A, {i : Fin n // e₀ i = a} :=
      { toFun := fun i => ⟨e₀ i, ⟨i, rfl⟩⟩
        invFun := fun ⟨_, ⟨i, _⟩⟩ => i
        left_inv := fun _ => rfl
        right_inv := fun ⟨a, ⟨i, h⟩⟩ => by subst h; rfl }
    let g : Equiv.Perm (Fin n) :=
      pack_e.trans ((Equiv.sigmaCongrRight βa).trans pack_e0.symm)
    refine ⟨DomMulAct.mk g, ?_⟩
    funext i
    change e₀ (g i) = e i
    exact (βa (e i) ⟨i, rfl⟩).2

private lemma sum_over_functions_with_fixed_counts'
    {A : Type*} [DecidableEq A] [Fintype A]
    (n : ℕ) (m0 : A → ℕ) :
    ∑ a, m0 a = n →
    ((Finset.univ : Finset (Fin n → A)).filter
        (fun e => ∀ a : A, Fintype.card {i : Fin n | e i = a} = m0 a)).card
    = Nat.multinomial (Finset.univ : Finset A) m0 := by
  -- Orbit-stabilizer computation: choose a witness `e₀`, compute the stabilizer,
  -- identify the orbit with the count-vector fiber, and apply `Nat.multinomial_spec`.
  intro hm0
  classical
  obtain ⟨e₀, he₀⟩ := exists_function_with_count_vector_aux n m0 hm0
  have h_stab := stabilizer_perm_dom_card_aux m0 e₀ he₀
  have h_orbit_eq := orbit_perm_dom_eq_count_fiber_aux m0 e₀ he₀
  have h_OS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (Equiv.Perm (Fin n))ᵈᵐᵃ e₀
  have h_G_card : Fintype.card (Equiv.Perm (Fin n))ᵈᵐᵃ = n.factorial := by
    rw [show Fintype.card (Equiv.Perm (Fin n))ᵈᵐᵃ
        = Fintype.card (Equiv.Perm (Fin n)) from
      (Fintype.card_congr DomMulAct.mk).symm]
    rw [Fintype.card_perm, Fintype.card_fin]
  rw [h_stab, h_G_card] at h_OS
  have h_mult_spec :
      (∏ a : A, (m0 a).factorial) * Nat.multinomial (Finset.univ : Finset A) m0
      = n.factorial := by
    have := Nat.multinomial_spec (Finset.univ : Finset A) m0
    rw [this, hm0]
  have h_pos : 0 < ∏ a : A, (m0 a).factorial :=
    Finset.prod_pos (fun _ _ => Nat.factorial_pos _)
  have h_orbit_card :
      Fintype.card (MulAction.orbit (Equiv.Perm (Fin n))ᵈᵐᵃ e₀)
      = Nat.multinomial (Finset.univ : Finset A) m0 := by
    apply Nat.mul_right_cancel h_pos
    rw [h_OS, ← h_mult_spec, Nat.mul_comm]
  rw [show ((Finset.univ : Finset (Fin n → A)).filter
        (fun e => ∀ a : A, Fintype.card {i : Fin n | e i = a} = m0 a)).card
      = Fintype.card (MulAction.orbit (Equiv.Perm (Fin n))ᵈᵐᵃ e₀) from ?_]
  · exact h_orbit_card
  · have h1 : ((Finset.univ : Finset (Fin n → A)).filter
        (fun e => ∀ a : A, Fintype.card {i : Fin n | e i = a} = m0 a)).card
        = Fintype.card {e : Fin n → A //
            ∀ a : A, Fintype.card {i : Fin n | e i = a} = m0 a} :=
      (Fintype.subtype_card _ (fun x => by simp [Finset.mem_filter])).symm
    rw [h1]
    apply Fintype.card_congr
    refine ⟨fun ⟨x, hx⟩ => ⟨x, ?_⟩, fun ⟨e, he⟩ => ⟨e, ?_⟩, ?_, ?_⟩
    · rw [h_orbit_eq]; exact hx
    · rw [h_orbit_eq] at he; exact he
    · intro ⟨x, _⟩; rfl
    · intro ⟨e, _⟩; rfl

/-- Sum over functions with fixed multiplicity equals multinomial × power product.
If `e : Fin n → A` is restricted to have prescribed multiplicities `m0 : A → ℕ`,
then the sum of `∏ i w(e i)` over the resulting fiber equals
`(Nat.multinomial univ m0 : R) * ∏ a w(a)^(m0 a)`. -/
private lemma sum_over_functions_with_fixed_counts
    {A : Type*} [DecidableEq A] [Fintype A]
    {R : Type*} [CommSemiring R]
    (w : A → R) (n : ℕ) (m0 : A → ℕ)
    (hm0 : ∑ a, m0 a = n) :
    ∑ e ∈
        ((Finset.univ : Finset (Fin n → A)).filter
          (fun e => ∀ a : A, Fintype.card {i : Fin n | e i = a} = m0 a)),
      ∏ i : Fin n, w (e i)
    =
      (Nat.cast (Nat.multinomial (Finset.univ : Finset A) m0) : R) *
        ∏ a, (w a) ^ (m0 a) := by
  classical
  -- Step 1: the weight is constant on each count fiber.
  have h_step1 : ∀ e ∈ ((Finset.univ : Finset (Fin n → A)).filter
      (fun e => ∀ a : A, Fintype.card {i : Fin n | e i = a} = m0 a)),
      ∏ i : Fin n, w (e i) = ∏ a, w a ^ m0 a := by
    intro e he_filter
    rw [Finset.mem_filter] at he_filter
    obtain ⟨_, he⟩ := he_filter
    rw [← Finset.prod_fiberwise_of_maps_to (t := (Finset.univ : Finset A))
         (g := e) (f := fun i => w (e i)) (fun _ _ => Finset.mem_univ _)]
    apply Finset.prod_congr rfl
    intro a _
    have h_const : ∀ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => e i = a),
        w (e i) = w a := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [hi.2]
    rw [Finset.prod_congr rfl h_const, Finset.prod_const]
    congr 1
    rw [← he a, Fintype.card_subtype]
    rfl
  rw [Finset.sum_congr rfl h_step1, Finset.sum_const, nsmul_eq_mul]
  -- Step 2: identify the cardinality of the count fiber.
  --   ((Finset.univ : Finset (Fin n → A)).filter (...)).card * (∏ a, w a ^ m0 a)
  --   = (Nat.cast (Nat.multinomial univ m0) : R) * (∏ a, w a ^ m0 a)
  -- It suffices to prove the cardinality identity and then push the cast.
  congr 1
  have hcard := sum_over_functions_with_fixed_counts' (A := A) n m0 hm0
  exact_mod_cast congrArg (fun k : ℕ => (k : R)) hcard

/-- Coefficient-collapse step: combines A4a + A4b under a `hCollapse` hypothesis
(the q0-contributors are exactly those with fixed count vector `m0`). -/
private lemma coeff_pow_collapse_to_multinomial_prod
    {Γ : Type*} [DecidableEq Γ] [AddCommMonoid Γ] [PartialOrder Γ]
    [IsOrderedCancelAddMonoid Γ]
    {R : Type*} [CommSemiring R]
    (f : HahnSeries Γ R) (A : Finset Γ)
    (hsupp : (Function.support f.coeff : Set Γ) ⊆ (A : Set Γ))
    (n : ℕ) (q0 : Γ) (m0 : ↥A → ℕ) (hm0 : ∑ a, m0 a = n)
    (hCollapse :
      ((Finset.univ : Finset (Fin n → ↥A)).filter
          (fun e => (∑ i : Fin n, ((e i : Γ))) = q0))
      =
      ((Finset.univ : Finset (Fin n → ↥A)).filter
          (fun e => ∀ a : ↥A, Fintype.card {i : Fin n | e i = a} = m0 a))) :
    (f ^ n).coeff q0 =
      (Nat.cast (Nat.multinomial (Finset.univ : Finset ↥A) m0) : R) *
        ∏ a : ↥A, f.coeff (a : Γ) ^ m0 a := by
  classical
  -- Step 1: A4a expands (f^n).coeff q0 as ∑ e : Fin n → ↥A, ite(...).
  rw [coeff_pow_eq_sum_over_pi (Γ := Γ) (R := R) f A hsupp n q0]
  -- Step 2: rewrite the indicator sum as a filtered sum.
  -- (Finset.sum_filter says ∑ x ∈ s.filter p, f x = ∑ x ∈ s, ite (p x) (f x) 0)
  rw [← Finset.sum_filter]
  -- Step 3: apply hCollapse to switch from q0-condition to fixed-count condition.
  rw [hCollapse]
  -- Step 4: apply A4b with weight w := fun a : ↥A => f.coeff (a : Γ).
  exact sum_over_functions_with_fixed_counts
    (A := ↥A) (R := R) (fun a : ↥A => f.coeff (a : Γ)) n m0 hm0

/-- Trivial product rewrite: from `g` to `Cs` using pointwise equality. -/
private lemma product_rewrite_with_coeff_eq
    {R : Type*} [CommMonoid R]
    {A : Type*} [Fintype A]
    {g Cs : A → R}
    (h : ∀ a, g a = Cs a) (m0 : A → ℕ) :
    ∏ a, g a ^ m0 a = ∏ a, Cs a ^ m0 a := by
  classical
  refine Finset.prod_congr rfl ?_
  intro a _
  simp [h a]

/-- The `hCollapse` hypothesis required by `coeff_pow_collapse_to_multinomial_prod`: at the
surviving residue `q0`, the q0-contributors among `Fin n → ↥A` are exactly those with the fixed
count vector `m0 a = φ₀ (μ.symm a)`.

The proof proceeds by `Finset.Subset.antisymm`:

  RHS ⊆ LHS direction (~30-40 ll, EASIER):
    Given e with `count e a = m0 a`, show `∑ i, (e i : ℚ) = q0`.
    Step 1. Fiber-wise grouping (same pattern as A4b Step 1):
            `∑ i, (e i : ℚ) = ∑ a : ↥A, (m0 a) * (a.val : ℚ)`
            via `Finset.prod_fiberwise_of_maps_to` (sum variant).
    Step 2. Substitute `hm0_def` to rewrite `m0 a = φ₀ ((muEquiv).symm ⟨a.val, ...⟩)`:
            `= ∑ a : ↥A, (φ₀ ((muEquiv hS hf2).symm ⟨a.val, ...⟩) : ℕ) * (a.val : ℚ)`
    Step 3. Convert sum-over-↥A to finsum-over-↥(Stilde hf2) via
            `finsum_mem_finset` + `Finset.sum_subtype` (or extend m0 by zero
            outside A). Use that `support fhat.coeff ⊆ A ⊆ Stilde`.
    Step 4. Change variables via `finsum_comp_equiv (muEquiv hS hf2)`
            to get `∑ᶠ d : S, (φ₀ d : ℕ) * (muQ hf2 d : ℚ)`.
    Step 5. Use `w0_rat_isInt` to identify
            `(...).num = ...` (integer cast back) and conclude
            `q0 = -r0/T + (r0/T + ∑ᶠ d, ...) = ∑ᶠ d, φ₀ d * muQ d`.
    Key Mathlib helpers: `Rat.den_eq_one_iff` (gives `(x.num : ℚ) = x` when `x.isInt`),
    `Finset.sum_const_nat`, `Finset.sum_subtype`, `finsum_eq_sum_of_support_subset`.

  LHS ⊆ RHS direction (depends on Helpers A1+A2):
    Given e with `(∑ i, (e i : ℚ)) = q0`, show `∀ a, count e a = m0 a`.
    Step 1. Form multiset `l_e` lifting e through hA_sub_Stilde:
            `l_e := (Finset.univ : Finset (Fin n)).val.map
                       (fun i => ⟨(e i : ℚ), hA_sub_Stilde (e i).property⟩)`
    Step 2. Witness `q0 ∈ (fhat^n).support` via `fhat_pow_support_multiset_decomp`
            (multiset decomposition of `(fhat^n).support`).
    Step 3. Apply `fhat_pow_coeff_residue_collapse` with
            `i := n`, `q := q0`, `hi_le := le_refl n`, `hq_residue := hq0_residue`:
            yields uniqueness of `phiT = φ₀ ∘ (muEquiv hS hf2).symm`.
        Step 4. Identify the multiset's count function with phiT, deduce
          `count e a = φ₀ ((muEquiv hS hf2).symm ⟨a.val, ...⟩) = m0 a`. -/
private lemma pi_filter_q0_eq_count_fiber
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    (A : Finset ℚ) (hA_sub_Stilde : (A : Set ℚ) ⊆ Stilde hf2)
    (hA_covers_phi : ∀ d : S, Sparse.φ₀ hSparse d ≠ 0 → (muQ hf2 d) ∈ A)
    (q0 : ℚ) (hq0_residue : ((T : ℚ) * q0 + r0 hSparse).isInt = true)
    (hq0_value : q0 = ∑ᶠ d : S, (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ))
    (m0 : ↥A → ℕ)
    (hm0_def : ∀ a : ↥A, m0 a =
      Sparse.φ₀ hSparse ((muEquiv hS hf2).symm ⟨a.val, hA_sub_Stilde a.property⟩))
    --(hm0_sum : ∑ a, m0 a = (n : ℕ))
    :
    ((Finset.univ : Finset (Fin (n : ℕ) → ↥A)).filter
        (fun e => (∑ i : Fin (n : ℕ), ((e i : ℚ))) = q0))
    =
    ((Finset.univ : Finset (Fin (n : ℕ) → ↥A)).filter
        (fun e => ∀ a : ↥A, Fintype.card {i : Fin (n : ℕ) | e i = a} = m0 a)) := by
  -- The proof is via `Finset.Subset.antisymm`:
  --   * LHS ⊆ RHS: use `phi_tilde_constraint_at_phi0` on the multiset
  --     count function induced by `e`.
  --   * RHS ⊆ LHS: fiber-wise grouping + finsum re-indexing + `hq0_value`.
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · -- LHS ⊆ RHS direction.
    intro e he_filter
    rw [Finset.mem_filter] at he_filter
    rw [Finset.mem_filter]
    refine ⟨he_filter.1, ?_⟩
    obtain ⟨_, he_sum⟩ := he_filter
    -- Form the multiset l_e of (e i).val lifted into Stilde via hA_sub_Stilde.
    let l_e : Multiset (↥(Stilde hf2)) :=
      (Finset.univ : Finset (Fin n)).val.map
        (fun i : Fin n => (⟨((e i).val : ℚ), hA_sub_Stilde (e i).property⟩ : ↥(Stilde hf2)))
    -- The count function on Stilde.
    let phiT : ↥(Stilde hf2) → ℕ := (l_e.toFinsupp : _ →₀ ℕ)
    -- card l_e = n.
    have hl_e_card : l_e.card = (n : ℕ) := by
      simp [l_e]
    -- (l_e.map val).sum = q0 (using he_sum).
    have hl_e_sum : (l_e.map (fun s => (s.val : ℚ))).sum = q0 := by
      have h_eq : (l_e.map (fun s => (s.val : ℚ))).sum
          = ∑ i ∈ (Finset.univ : Finset (Fin n)), ((e i).val : ℚ) := by
        simp [l_e, Function.comp_def, Finset.sum]
      rw [h_eq]
      simpa using he_sum
    -- Finite support of phiT.
    have hphiT_finite : (Function.support phiT).Finite := by
      simp [phiT]-- using (Finsupp.finite_support l_e.toFinsupp)
    -- Bridge: ∑ᶠ phiT = l_e.card.
    have h_count_bridge : (∑ᶠ s : ↥(Stilde hf2), phiT s) = l_e.card := by
      have h_supp_subset :
          Function.support phiT ⊆ ((l_e.toFinsupp).support : Set (↥(Stilde hf2))) := by
        intro s hs
        simp only [Function.mem_support, ne_eq] at hs
        exact Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hs)
      rw [finsum_eq_sum_of_support_subset (s := (l_e.toFinsupp).support) phiT
        h_supp_subset]
      have hsum_eq : ∑ s ∈ (l_e.toFinsupp).support, phiT s
          = ∑ s ∈ (l_e.toFinsupp).support, l_e.count s := by
        apply Finset.sum_congr rfl
        intro s _
        simp [phiT, Multiset.toFinsupp_apply]
      rw [hsum_eq]
      have h_supp_eq_toFinset : (l_e.toFinsupp).support = l_e.toFinset := by
        ext s
        simp [Multiset.mem_toFinset]
      rw [h_supp_eq_toFinset]
      exact Multiset.toFinset_sum_count_eq l_e
    have hphiT_sum : ∑ᶠ s : ↥(Stilde hf2), phiT s ≤ n := by
      rw [h_count_bridge, hl_e_card]
    -- Bridge: ∑ᶠ s, (s.val : ℚ) * (phiT s : ℚ) = q0.
    have h_residue_bridge :
        (∑ᶠ s : ↥(Stilde hf2), (s.val : ℚ) * (phiT s : ℚ)) = q0 := by
      have h_supp_subset :
          Function.support (fun s : ↥(Stilde hf2) => (s.val : ℚ) * (phiT s : ℚ))
            ⊆ ((l_e.toFinsupp).support : Set (↥(Stilde hf2))) := by
        intro s hs
        simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hs
        have hphi_ne : (phiT s : ℚ) ≠ 0 := hs.2
        have hphi_ne_nat : phiT s ≠ 0 := by exact_mod_cast hphi_ne
        exact Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hphi_ne_nat)
      rw [finsum_eq_sum_of_support_subset
        (fun s : ↥(Stilde hf2) => (s.val : ℚ) * (phiT s : ℚ))
        (s := (l_e.toFinsupp).support) h_supp_subset]
      have h_supp_eq_toFinset : (l_e.toFinsupp).support = l_e.toFinset := by
        ext s
        simp [Multiset.mem_toFinset]
      rw [h_supp_eq_toFinset]
      have h_each : ∀ s ∈ l_e.toFinset,
          (s.val : ℚ) * (phiT s : ℚ) = (s.val : ℚ) * (l_e.count s : ℚ) := by
        intro s _
        simp [phiT, Multiset.toFinsupp_apply]
      rw [Finset.sum_congr rfl h_each]
      have h_count_form :
          ∑ s ∈ l_e.toFinset, (s.val : ℚ) * (l_e.count s : ℚ) =
          ∑ s ∈ l_e.toFinset, (l_e.count s : ℕ) • (s.val : ℚ) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [nsmul_eq_mul]; ring
      rw [h_count_form]
      rw [← Finset.sum_multiset_map_count l_e (fun s : ↥(Stilde hf2) => (s.val : ℚ))]
      exact hl_e_sum
    have hphiT_residue :
        ((T : ℚ) * (∑ᶠ s : ↥(Stilde hf2), (s.val : ℚ) * (phiT s : ℚ))
          + r0 hSparse).isInt = true := by
      rw [h_residue_bridge]; exact hq0_residue
    have hphiT_eq :
        phiT = Sparse.φ₀ hSparse ∘ (muEquiv hS hf2).symm :=
      phi_tilde_constraint_at_phi0 hS hf2 hSparse phiT hphiT_finite hphiT_sum hphiT_residue
    -- Now pull back to A-indexing: count e a = phiT ⟨a.val, ...⟩ = m0 a.
    intro a
    -- Step 1: identify count e a with multiset count of `⟨a.val, hA_sub_Stilde a.property⟩`.
    have h_count_card_eq :
        Fintype.card {i : Fin n | e i = a}
        = l_e.count (⟨a.val, hA_sub_Stilde a.property⟩ : ↥(Stilde hf2)) := by
      classical
      -- Build an Equiv between {i | e i = a} and matching multiset indices.
      have h_iff : ∀ i : Fin n,
          ((⟨a.val, hA_sub_Stilde a.property⟩ : ↥(Stilde hf2))
            = ⟨((e i).val : ℚ), hA_sub_Stilde (e i).property⟩)
          ↔ e i = a := by
        intro i
        constructor
        · intro h
          have hval : a.val = (e i).val := by
            have := congrArg Subtype.val h
            exact this
          exact Subtype.ext hval.symm
        · intro h
          rw [h]
      -- Build Equiv.
      have h_eq : ({i : Fin n | e i = a} : Type _)
          ≃ {i : Fin n //
              ((⟨a.val, hA_sub_Stilde a.property⟩ : ↥(Stilde hf2))
                = ⟨((e i).val : ℚ), hA_sub_Stilde (e i).property⟩)} :=
        { toFun := fun ⟨i, hi⟩ => ⟨i, (h_iff i).mpr hi⟩
          invFun := fun ⟨i, hi⟩ => ⟨i, (h_iff i).mp hi⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr h_eq, Fintype.card_subtype]
      -- Goal: ({i ∈ Finset.univ | ⟨a.val,...⟩ = ⟨(e i).val,...⟩}).card
      --       = l_e.count ⟨a.val, hA_sub_Stilde a.property⟩
      have h_l_e_unfold :
          l_e = Multiset.map (fun i : Fin n =>
                (⟨((e i).val : ℚ), hA_sub_Stilde (e i).property⟩ : ↥(Stilde hf2)))
              (Finset.univ : Finset (Fin n)).val := rfl
      rw [h_l_e_unfold, Multiset.count_map]
      -- Goal: {x | predicate x}.card = (Multiset.filter predicate Finset.univ.val).card.
      -- The Finset notation {x | p x} desugars to Finset.filter p Finset.univ.
      -- Their cards are equal: (Finset.filter p s).val = Multiset.filter p s.val.
      change ((Finset.univ : Finset (Fin n)).filter
                (fun i : Fin n =>
                  (⟨a.val, hA_sub_Stilde a.property⟩ : ↥(Stilde hf2))
                    = ⟨((e i).val : ℚ), hA_sub_Stilde (e i).property⟩)).card
              = (Multiset.filter
                  (fun i : Fin n =>
                    (⟨a.val, hA_sub_Stilde a.property⟩ : ↥(Stilde hf2))
                      = ⟨((e i).val : ℚ), hA_sub_Stilde (e i).property⟩)
                  (Finset.univ : Finset (Fin n)).val).card
      rw [show ((Finset.univ : Finset (Fin n)).filter
                (fun i : Fin n =>
                  (⟨a.val, hA_sub_Stilde a.property⟩ : ↥(Stilde hf2))
                    = ⟨((e i).val : ℚ), hA_sub_Stilde (e i).property⟩)).card
              = Multiset.card
                  ((Finset.univ : Finset (Fin n)).filter
                    (fun i : Fin n =>
                      (⟨a.val, hA_sub_Stilde a.property⟩ : ↥(Stilde hf2))
                        = ⟨((e i).val : ℚ), hA_sub_Stilde (e i).property⟩)).val
            from rfl]
      rw [Finset.filter_val]
    -- Step 2: by hphiT_eq, phiT s = (φ₀ ∘ μ.symm) s.
    have h_phiT_val :
        phiT (⟨a.val, hA_sub_Stilde a.property⟩ : ↥(Stilde hf2))
        = Sparse.φ₀ hSparse ((muEquiv hS hf2).symm
            ⟨a.val, hA_sub_Stilde a.property⟩) :=
      congrFun hphiT_eq ⟨a.val, hA_sub_Stilde a.property⟩
    -- Step 3: combine using hm0_def.
    rw [h_count_card_eq]
    have h_phiT_count :
        phiT (⟨a.val, hA_sub_Stilde a.property⟩ : ↥(Stilde hf2))
        = l_e.count (⟨a.val, hA_sub_Stilde a.property⟩ : ↥(Stilde hf2)) := by
      simp [phiT, Multiset.toFinsupp_apply]
    rw [← h_phiT_count, h_phiT_val, ← hm0_def]
  · -- RHS ⊆ LHS direction.
    intro e he_filter
    rw [Finset.mem_filter] at he_filter
    rw [Finset.mem_filter]
    refine ⟨he_filter.1, ?_⟩
    obtain ⟨_, he_count⟩ := he_filter
    -- Step 1: fiber-wise grouping.
    -- ∑ i, (e i : ℚ) = ∑ a : ↥A, ∑ i ∈ (filter e i = a), (e i : ℚ)
    --                = ∑ a : ↥A, (m0 a : ℕ) • (a.val : ℚ)
    --                = ∑ a : ↥A, (m0 a : ℚ) * (a.val : ℚ)
    have h_fiber : ∑ i : Fin n, ((e i).val : ℚ)
        = ∑ a : ↥A, (m0 a : ℚ) * (a.val : ℚ) := by
      rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset ↥A))
            (g := e) (f := fun i => ((e i).val : ℚ))
            (fun i _ => Finset.mem_univ _)]
      apply Finset.sum_congr rfl
      intro a _
      have h_const : ∀ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => e i = a),
          ((e i).val : ℚ) = (a.val : ℚ) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [hi.2]
      rw [Finset.sum_congr rfl h_const, Finset.sum_const]
      rw [nsmul_eq_mul]
      congr 1
      have h1 : ((Finset.univ.filter (fun i : Fin n => e i = a)).card : ℚ)
          = (Fintype.card {i : Fin n | e i = a} : ℚ) := by
        rw [Fintype.subtype_card]
        rfl
      rw [h1, he_count a]
    -- Step 2: substitute hm0_def.
    have h_m0_phi : ∀ a : ↥A,
        (m0 a : ℚ)
        = ((Sparse.φ₀ hSparse ((muEquiv hS hf2).symm
            ⟨a.val, hA_sub_Stilde a.property⟩) : ℕ) : ℚ) := by
      intro a; rw [hm0_def]
    have h_sum_phi : ∑ a : ↥A, (m0 a : ℚ) * (a.val : ℚ)
        = ∑ a : ↥A, ((Sparse.φ₀ hSparse ((muEquiv hS hf2).symm
            ⟨a.val, hA_sub_Stilde a.property⟩) : ℕ) : ℚ) * (a.val : ℚ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [h_m0_phi a]
    -- Step 3: extend m0' to all of Stilde hf2 by zero, then re-express as finsum.
    -- Define G : ↥(Stilde hf2) → ℚ such that G ⟨a.val, _⟩ = m0 a * a.val and 0 elsewhere.
    -- Use that on A ⊆ Stilde the map a ↦ ⟨a.val, hA_sub_Stilde a.property⟩ is injective
    -- (since the val maps coincide); on the complement we use finsum_eq_sum_of_support_subset.
    -- Strategy: lift m0 to all of Stilde via subtype lifting.
    set G : ↥(Stilde hf2) → ℚ := fun s : ↥(Stilde hf2) =>
        ((Sparse.φ₀ hSparse ((muEquiv hS hf2).symm s) : ℕ) : ℚ) * (s.val : ℚ) with hG_def
    -- Each summand in the A-sum equals G ⟨a.val, hA_sub_Stilde a.property⟩.
    have h_G_match : ∀ a : ↥A,
        ((Sparse.φ₀ hSparse ((muEquiv hS hf2).symm
            ⟨a.val, hA_sub_Stilde a.property⟩) : ℕ) : ℚ) * (a.val : ℚ)
        = G ⟨a.val, hA_sub_Stilde a.property⟩ := by
      intro a; rfl
    have h_sum_via_G :
        ∑ a : ↥A, ((Sparse.φ₀ hSparse ((muEquiv hS hf2).symm
            ⟨a.val, hA_sub_Stilde a.property⟩) : ℕ) : ℚ) * (a.val : ℚ)
        = ∑ a : ↥A, G ⟨a.val, hA_sub_Stilde a.property⟩ := by
      apply Finset.sum_congr rfl
      intro a _
      exact h_G_match a
    -- Step 4: convert ∑ a : ↥A, G ⟨a.val, hA_sub_Stilde a.property⟩
    -- to ∑ᶠ s : ↥(Stilde hf2), G s using that the embedding A → Stilde is injective
    -- and G is zero on Stilde \ image(A).
    -- Since on Stilde \ μ(S) the term phiT is zero (G uses φ₀ ∘ μ.symm which is φ₀ on S),
    -- and φ₀ has support in some hφ₀_finite, we need to handle this carefully.
    -- We use that ∑ a : ↥A, G ⟨a.val, ...⟩ = ∑ᶠ s : ↥(Stilde hf2), G s
    -- iff the support of G is contained in the image of A in Stilde, plus
    -- the embedding is injective.
    -- Simpler approach: compute ∑ᶠ d : S, (φ₀ d : ℚ) * (muQ hf2 d : ℚ) directly.
    -- The key: change variable along (muEquiv hS hf2).symm:
    --   ∑ᶠ d : S, (φ₀ d : ℚ) * (muQ hf2 d : ℚ)
    --   = ∑ᶠ s : ↥(Stilde hf2), (φ₀ ((muEquiv hS hf2).symm s) : ℚ) * (s.val : ℚ)
    -- (since muQ hf2 d = (muToStilde hf2 d).val = ((muEquiv hS hf2) d).val).
    -- That gives ∑ᶠ s, G s.
    -- Then it remains to show ∑ a : ↥A, G ⟨a.val, ...⟩ = ∑ᶠ s, G s.
    -- Since G's support is among s where φ₀ ((muEquiv hS hf2).symm s) ≠ 0,
    -- and m0 a = φ₀ (μ.symm ⟨a.val, ...⟩) ≠ 0 implies the corresponding a contributes,
    -- AND A ⊆ Stilde via hA_sub_Stilde, the embedding is a Finset-image equiv.
    -- We use Finset.sum_subtype + extension.
    -- Concretely, we use:
    --   ∑ a : ↥A, G ⟨a.val, hA_sub_Stilde a.property⟩
    --   = ∑ s ∈ (A.attach.image (fun a => ⟨a.val, hA_sub_Stilde a.property⟩)), G s
    -- after handling injectivity.
    -- ----- Strategy: bypass A-to-Stilde issue by computing directly. -----
    -- We have hq0_value: q0 = ∑ᶠ d : S, (φ₀ d : ℚ) * (muQ hf2 d : ℚ).
    -- Express the RHS of hq0_value via muEquiv.
    -- For each d : S, muQ hf2 d = (muEquiv hS hf2 d).val (by definition).
    have h_mu_eq_val : ∀ d : S, (muQ hf2 d : ℚ) = ((muEquiv hS hf2 d).val : ℚ) := by
      intro d; rfl
    have h_q0_expand :
        q0 = ∑ᶠ d : S, ((Sparse.φ₀ hSparse d : ℕ) : ℚ) * ((muEquiv hS hf2 d).val : ℚ) := by
      rw [hq0_value]
      apply finsum_congr
      intro d
      rw [h_mu_eq_val]
    -- Now express this via change of variable along muEquiv:
    --   ∑ᶠ d : S, (φ₀ d : ℚ) * ((muEquiv hS hf2 d).val : ℚ)
    --   = ∑ᶠ s : ↥(Stilde hf2), (φ₀ ((muEquiv hS hf2).symm s) : ℚ) * (s.val : ℚ)
    -- via finsum_comp_equiv.
    have h_q0_via_Stilde :
        q0 = ∑ᶠ s : ↥(Stilde hf2), G s := by
      rw [h_q0_expand]
      -- We apply finsum_comp_equiv with e := (muEquiv hS hf2).
      have h_change := finsum_comp_equiv (muEquiv hS hf2)
        (f := fun s : ↥(Stilde hf2) =>
          ((Sparse.φ₀ hSparse ((muEquiv hS hf2).symm s) : ℕ) : ℚ) * (s.val : ℚ))
      -- h_change : ∑ᶠ (d : S), (fun s => ...) (muEquiv hS hf2 d)
      --          = ∑ᶠ (s : ↥(Stilde hf2)), (fun s => ...) s
      -- Simplify LHS of h_change.
      have hcomp_eq :
          (fun d : S =>
            ((Sparse.φ₀ hSparse
              ((muEquiv hS hf2).symm ((muEquiv hS hf2) d)) : ℕ) : ℚ)
            * (((muEquiv hS hf2) d).val : ℚ))
          = (fun d : S =>
            ((Sparse.φ₀ hSparse d : ℕ) : ℚ) * ((muEquiv hS hf2 d).val : ℚ)) := by
        funext d
        simp [Equiv.symm_apply_apply]
      rw [hcomp_eq] at h_change
      rw [h_change, hG_def]
    -- Step 5: show ∑ a : ↥A, G ⟨a.val, hA_sub_Stilde a.property⟩ = ∑ᶠ s : ↥(Stilde hf2), G s.
    -- The embedding A.attach → Stilde hf2 via a ↦ ⟨a.val, hA_sub_Stilde a.property⟩
    -- has injective image. Off the image (i.e., on s : Stilde with s.val ∉ A),
    -- we claim G s = 0.
    -- Why? Because if G s ≠ 0, then (φ₀ ((muEquiv hS hf2).symm s) : ℕ) ≠ 0,
    -- i.e., (muEquiv hS hf2).symm s ∈ Function.support (Sparse.φ₀ hSparse) ⊆ S.
    -- We have hA_supp : Function.support fhat.coeff ⊆ A.
    -- We need: (s : Stilde hf2 with φ₀ ((muEquiv hS hf2).symm s) ≠ 0) → s.val ∈ A.
    -- This needs that fhat.coeff is non-zero at every such s, which is NOT given here.
    -- BUT the lemma's intended use has m0 supported on A and m0 a = φ₀ (μ.symm ⟨a.val, ...⟩),
    -- so if a "phantom" s : Stilde with s.val ∉ A has φ₀ (μ.symm s) ≠ 0, it cannot
    -- be reached from A. Such s is NOT in our sum.
    -- Approach: convert ∑ a : ↥A, G ⟨a.val, hA_sub_Stilde a.property⟩ to a finset-image
    -- sum over Stilde, then use that G's support outside the image is empty IF
    -- hA_supp (Function.support fhat.coeff ⊆ A) gives us what we need.
    --
    -- Actually, since we have the call-site responsibility for the right A
    -- (it covers φ₀'s support image), the prover can assume that ∑ᶠ over Stilde
    -- of G coincides with the A-sum. We make this precise via support_subset.
    have h_finset_to_finsum : ∑ a : ↥A, G ⟨a.val, hA_sub_Stilde a.property⟩
        = ∑ᶠ s : ↥(Stilde hf2), G s := by
      -- The map A.attach → Stilde via toStilde is injective with image
      -- = {s : ↥(Stilde hf2) | s.val ∈ A}.
      let toStilde : ↥A → ↥(Stilde hf2) :=
        fun a => ⟨a.val, hA_sub_Stilde a.property⟩
      have h_inj : Function.Injective toStilde := by
        intro a b h
        apply Subtype.ext
        have hval : (toStilde a).val = (toStilde b).val := congrArg Subtype.val h
        -- (toStilde a).val = a.val by definition.
        exact hval
      -- Express the A-sum as a Finset.sum over the image.
      have h_image_sum :
          ∑ a : ↥A, G (toStilde a)
          = ∑ s ∈ ((Finset.univ : Finset ↥A).image toStilde), G s := by
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact h_inj hab
      rw [show (fun (a : ↥A) => G ⟨a.val, hA_sub_Stilde a.property⟩) = G ∘ toStilde from rfl]
      simp only [Function.comp_apply]
      rw [h_image_sum]
      -- Show: ∑ s ∈ image, G s = ∑ᶠ s, G s.
      -- Need: Function.support G ⊆ image.
      symm
      apply finsum_eq_sum_of_support_subset G
      -- Goal: Function.support G ⊆ ↑((Finset.univ.image toStilde))
      intro s hs
      simp only [Function.mem_support, ne_eq, hG_def] at hs
      have h_phi_ne : (Sparse.φ₀ hSparse ((muEquiv hS hf2).symm s) : ℕ) ≠ 0 := by
        intro h
        apply hs
        rw [show ((Sparse.φ₀ hSparse ((muEquiv hS hf2).symm s) : ℕ) : ℚ) = 0 from by
          exact_mod_cast h]
        ring
      have h_phi_ne_nat : Sparse.φ₀ hSparse ((muEquiv hS hf2).symm s) ≠ 0 := h_phi_ne
      -- By hA_covers_phi, muQ hf2 ((muEquiv hS hf2).symm s) ∈ A.
      have h_cover := hA_covers_phi ((muEquiv hS hf2).symm s) h_phi_ne_nat
      -- muQ hf2 ((muEquiv hS hf2).symm s) = s.val (since muEquiv applies inverse).
      have h_mu_inv : muQ hf2 ((muEquiv hS hf2).symm s) = s.val := by
        have : (muEquiv hS hf2 ((muEquiv hS hf2).symm s)) = s :=
          (muEquiv hS hf2).apply_symm_apply s
        have := congrArg Subtype.val this
        exact this
      rw [h_mu_inv] at h_cover
      -- Now s.val ∈ A, so s = toStilde ⟨s.val, h_cover⟩ ∈ image.
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and]
      refine ⟨⟨s.val, h_cover⟩, ?_⟩
      apply Subtype.ext
      rfl
    -- Combine: q0 = ∑ᶠ s, G s = ∑ a : ↥A, G ⟨a.val, _⟩
    --            = ∑ a, (m0 a : ℚ) * (a.val : ℚ) = ∑ i, (e i : ℚ).
    rw [h_fiber, h_sum_phi, h_sum_via_G, h_finset_to_finsum, ← h_q0_via_Stilde]

/-! ### extracted helpers for the closure lemma. -/

/-- Coefficient and support properties of `fhatAOf`. Bundles three
facts used by the closure lemma:

  * `coeff_in_A`  — at `a ∈ A_F`, `(fhatAOf).coeff a = fhat.coeff a`.
  * `coeff_not_in_A` — at `a ∉ A_F`, `(fhatAOf).coeff a = 0`.
  * `support_subset` — `support (fhatAOf).coeff ⊆ A_F`.

The `A_F := image muQ (supp φ₀)` is the image set used in the closure lemma. -/
private lemma fhatAOf_coeff_props
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    (fhat : TLiftedPAdicHahnSeries p (T : ℕ))
    (hφ₀_finite : (Function.support (Sparse.φ₀ hSparse)).Finite) :
    (∀ a ∈ hφ₀_finite.toFinset.image (fun d : S => muQ hf2 d),
        (fhatAOf hf2 hSparse fhat hφ₀_finite).coeff a = fhat.coeff a) ∧
    (∀ a, a ∉ hφ₀_finite.toFinset.image (fun d : S => muQ hf2 d) →
        (fhatAOf hf2 hSparse fhat hφ₀_finite).coeff a = 0) ∧
    ((Function.support (fhatAOf hf2 hSparse fhat hφ₀_finite).coeff : Set ℚ) ⊆
        (hφ₀_finite.toFinset.image (fun d : S => muQ hf2 d) : Set ℚ)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨d₀, hd₀_mem, rfl⟩ := ha
    change (∑ d ∈ hφ₀_finite.toFinset,
        HahnSeries.single (muQ hf2 d) (fhat.coeff (muQ hf2 d))).coeff (muQ hf2 d₀) = _
    rw [HahnSeries.coeff_sum]
    rw [Finset.sum_eq_single d₀]
    · exact HahnSeries.coeff_single_same _ _
    · intro d _ hne
      exact HahnSeries.coeff_single_of_ne (fun h => hne (muQ_injective hS hf2 h.symm))
    · intro h; exact absurd hd₀_mem h
  · intro a ha
    change (∑ d ∈ hφ₀_finite.toFinset,
        HahnSeries.single (muQ hf2 d) (fhat.coeff (muQ hf2 d))).coeff a = 0
    rw [HahnSeries.coeff_sum]
    apply Finset.sum_eq_zero
    intro d hd
    apply HahnSeries.coeff_single_of_ne
    intro h
    exact ha (Finset.mem_image.mpr ⟨d, hd, h.symm⟩)
  · intro a ha_supp
    by_contra ha_notA
    have ha_notin : a ∉ hφ₀_finite.toFinset.image (fun d : S => muQ hf2 d) :=
      fun h => ha_notA (Finset.mem_coe.mpr h)
    apply ha_supp
    change (∑ d ∈ hφ₀_finite.toFinset,
        HahnSeries.single (muQ hf2 d) (fhat.coeff (muQ hf2 d))).coeff a = 0
    rw [HahnSeries.coeff_sum]
    apply Finset.sum_eq_zero
    intro d hd
    apply HahnSeries.coeff_single_of_ne
    intro h
    exact ha_notin (Finset.mem_image.mpr ⟨d, hd, h.symm⟩)

/-- `Finset.sum_bij` along `(muEquiv hS hf2).symm` between
`Finset.univ : Finset ↥A_F` and `hφ₀_finite.toFinset : Finset S`, for any commutative
monoid-valued function `g` satisfying the `hg` compatibility condition. This packages
the `muEquiv`-bijection bookkeeping used in three separate inline `Finset.sum_bij` /
`Finset.prod_bij` invocations in the closure lemma. -/
private lemma muEquiv_prod_reindex
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    (hφ₀_finite : (Function.support (Sparse.φ₀ hSparse)).Finite)
    {M : Type*} [CommMonoid M]
    (A_F : Finset ℚ)
    (hA_F_def : A_F = hφ₀_finite.toFinset.image (fun d : S => muQ hf2 d))
    (hA_F_sub_Stilde : (A_F : Set ℚ) ⊆ Stilde hf2)
    (g_A : ↥A_F → M) (g_S : S → M)
    (hg : ∀ a : ↥A_F,
        g_A a =
          g_S ((muEquiv hS hf2).symm ⟨a.val, hA_F_sub_Stilde a.property⟩)) :
    ∏ a : ↥A_F, g_A a = ∏ d ∈ hφ₀_finite.toFinset, g_S d := by
  classical
  refine Finset.prod_bij
    (fun (a : ↥A_F) _ =>
      (muEquiv hS hf2).symm ⟨a.val, hA_F_sub_Stilde a.property⟩)
    ?_ ?_ ?_ ?_
  · intro a _
    have ha_image : a.val ∈
        Finset.image (fun d : S => muQ hf2 d) hφ₀_finite.toFinset := by
      rw [← hA_F_def]; exact a.property
    obtain ⟨d, hd_mem, hd_eq⟩ := Finset.mem_image.mp ha_image
    have hd_supp : d ∈ Function.support (Sparse.φ₀ hSparse) :=
      (hφ₀_finite.mem_toFinset).mp hd_mem
    have h_eq_d : (muEquiv hS hf2).symm ⟨a.val, hA_F_sub_Stilde a.property⟩ = d := by
      apply (muEquiv hS hf2).injective
      rw [Equiv.apply_symm_apply]
      apply Subtype.ext
      exact hd_eq.symm
    rw [h_eq_d]
    exact (hφ₀_finite.mem_toFinset).mpr hd_supp
  · intro a₁ _ a₂ _ heq
    have h1 := congrArg (muEquiv hS hf2) heq
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    have h2 : a₁.val = a₂.val := by
      have := congrArg Subtype.val h1
      exact this
    exact Subtype.ext h2
  · intro d hd
    have hd_supp : d ∈ Function.support (Sparse.φ₀ hSparse) :=
      (hφ₀_finite.mem_toFinset).mp hd
    have h_mem : muQ hf2 d ∈
        Finset.image (fun d : S => muQ hf2 d) hφ₀_finite.toFinset :=
      Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have h_mem' : muQ hf2 d ∈ A_F := by
      rw [hA_F_def]; exact h_mem
    refine ⟨⟨muQ hf2 d, h_mem'⟩, Finset.mem_univ _, ?_⟩
    change (muEquiv hS hf2).symm ⟨muQ hf2 d, hA_F_sub_Stilde h_mem'⟩ = d
    apply (muEquiv hS hf2).injective
    rw [Equiv.apply_symm_apply]; apply Subtype.ext; rfl
  · intro a _
    exact hg a

/-- Additive variant of `muEquiv_prod_reindex` for `Finset.sum_bij`.
Used by step (12) of the closure lemma (`hm0_sum`). -/
private lemma muEquiv_sum_reindex
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    (hφ₀_finite : (Function.support (Sparse.φ₀ hSparse)).Finite)
    {M : Type*} [AddCommMonoid M]
    (A_F : Finset ℚ)
    (hA_F_def : A_F = hφ₀_finite.toFinset.image (fun d : S => muQ hf2 d))
    (hA_F_sub_Stilde : (A_F : Set ℚ) ⊆ Stilde hf2)
    (g_A : ↥A_F → M) (g_S : S → M)
    (hg : ∀ a : ↥A_F,
        g_A a =
          g_S ((muEquiv hS hf2).symm ⟨a.val, hA_F_sub_Stilde a.property⟩)) :
    ∑ a : ↥A_F, g_A a = ∑ d ∈ hφ₀_finite.toFinset, g_S d := by
  classical
  refine Finset.sum_bij
    (fun (a : ↥A_F) _ =>
      (muEquiv hS hf2).symm ⟨a.val, hA_F_sub_Stilde a.property⟩)
    ?_ ?_ ?_ ?_
  · intro a _
    have ha_image : a.val ∈
        Finset.image (fun d : S => muQ hf2 d) hφ₀_finite.toFinset := by
      rw [← hA_F_def]; exact a.property
    obtain ⟨d, hd_mem, hd_eq⟩ := Finset.mem_image.mp ha_image
    have hd_supp : d ∈ Function.support (Sparse.φ₀ hSparse) :=
      (hφ₀_finite.mem_toFinset).mp hd_mem
    have h_eq_d : (muEquiv hS hf2).symm ⟨a.val, hA_F_sub_Stilde a.property⟩ = d := by
      apply (muEquiv hS hf2).injective
      rw [Equiv.apply_symm_apply]
      apply Subtype.ext
      exact hd_eq.symm
    rw [h_eq_d]
    exact (hφ₀_finite.mem_toFinset).mpr hd_supp
  · intro a₁ _ a₂ _ heq
    have h1 := congrArg (muEquiv hS hf2) heq
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
    have h2 : a₁.val = a₂.val := by
      have := congrArg Subtype.val h1
      exact this
    exact Subtype.ext h2
  · intro d hd
    have hd_supp : d ∈ Function.support (Sparse.φ₀ hSparse) :=
      (hφ₀_finite.mem_toFinset).mp hd
    have h_mem : muQ hf2 d ∈
        Finset.image (fun d : S => muQ hf2 d) hφ₀_finite.toFinset :=
      Finset.mem_image.mpr ⟨d, hd, rfl⟩
    have h_mem' : muQ hf2 d ∈ A_F := by
      rw [hA_F_def]; exact h_mem
    refine ⟨⟨muQ hf2 d, h_mem'⟩, Finset.mem_univ _, ?_⟩
    change (muEquiv hS hf2).symm ⟨muQ hf2 d, hA_F_sub_Stilde h_mem'⟩ = d
    apply (muEquiv hS hf2).injective
    rw [Equiv.apply_symm_apply]; apply Subtype.ext; rfl
  · intro a _
    exact hg a

/-- Closure lemma for the multinomial collapse.

1. `coeff_pow_truncate_eq` truncates LHS to `(fhatAOf)^n.coeff q0`.
2. `pi_filter_q0_eq_count_fiber` gives the q0-filter / count-fiber
   equality (the `hCollapse` hypothesis).
3. `coeff_pow_collapse_to_multinomial_prod` wraps the sum-over-tuples and
   fiber-cardinality steps under that collapse to produce
   `multinomial × ∏ a, fhatA.coeff a.val^(m0 a)`.
4. Coefficient rewrite via `h_fhatA_in_A_F` + `h_coeff_eq`, then product
   re-indexing through the `muEquiv` bijection.
-/
private lemma fhat_pow_collapse_to_beta_P_prod
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    {Cs : ↥(Stilde hf2) → ℤᵘⁿ_[p,(T : ℕ)]}
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (h_supp : Function.support fhat.coeff ⊆ Stilde hf2)
    (h_coeff_eq : ∀ (s : ↥(Stilde hf2)), fhat.coeff s.val = Cs s)
    (hCs_ne : ∀ s : ↥(Stilde hf2), Cs s ≠ 0)
    (hφ₀_finite : (Function.support (Sparse.φ₀ hSparse)).Finite) :
    (fhat ^ (n : ℕ)).coeff
        (-(r0 hSparse) / T +
          ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
            (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num : ℚ) / T) =
      ((Nat.multinomial hφ₀_finite.toFinset (Sparse.φ₀ hSparse) :
          ℤᵘⁿ_[p,(T : ℕ)]) *
        (∏ᶠ d : S, Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d))) := by
  classical
  -- ====== Setup: q0, fhatA, A_F. ======
  set fhatA := fhatAOf hf2 hSparse fhat hφ₀_finite with hfhatA_def
  set q0 : ℚ := -(r0 hSparse) / T +
        ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
          (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num : ℚ) / T
        with hq0_def
  set A_F : Finset ℚ := hφ₀_finite.toFinset.image (fun d : S => muQ hf2 d)
        with hA_F_def
  -- (1) A_F ⊆ Stilde hf2.
  have hA_F_sub_Stilde : (A_F : Set ℚ) ⊆ Stilde hf2 := by
    intro a ha
    rw [hA_F_def, Finset.coe_image] at ha
    obtain ⟨d, _, rfl⟩ := ha
    exact ⟨d, rfl⟩
  -- (2-4) Coefficient and support properties of fhatAOf, via `fhatAOf_coeff_props`.
  obtain ⟨h_fhatA_in_A_F, h_fhatA_not_A_F, h_fhatA_supp_A_F⟩ :=
    fhatAOf_coeff_props hf2 hSparse fhat hφ₀_finite
  -- (5) Function.support fhatA.coeff ⊆ Stilde hf2.
  have h_fhatA_supp_Stilde : Function.support fhatA.coeff ⊆ Stilde hf2 :=
    h_fhatA_supp_A_F.trans hA_F_sub_Stilde
  -- (6) A_F covers φ₀: every d with φ₀ d ≠ 0 has muQ hf2 d ∈ A_F.
  have hA_F_covers_phi : ∀ d : S, Sparse.φ₀ hSparse d ≠ 0 → (muQ hf2 d) ∈ A_F := by
    intro d hd
    rw [hA_F_def, Finset.mem_image]
    exact ⟨d, by rw [Set.Finite.mem_toFinset]; exact hd, rfl⟩
  -- (7) q0 residue.
  have hT_ne : (T : ℚ) ≠ 0 := by exact_mod_cast PNat.ne_zero T
  have hq0_residue : ((T : ℚ) * q0 + r0 hSparse).isInt = true := by
    have hk_eq : (T : ℚ) * q0 + r0 hSparse =
        ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S, (Sparse.φ₀ hSparse d : ℚ) *
          (muQ hf2 d : ℚ)).num : ℚ) := by
      rw [hq0_def]; field_simp; ring
    rw [hk_eq]; exact isInt_intCast' _
  -- (8) q0 value (mirrors the inline `_hq0_value` derivation from
  -- `fhat_pow_coeff_at_phi0_nonzero_form` below).
  have hq0_value : q0 = ∑ᶠ d : S,
      (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ) := by
    have h_isInt := w0_rat_isInt hf2 hSparse
    have h_num_eq : ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
                      (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num : ℚ)
                 = r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
                      (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ) :=
      (Rat.eq_num_of_isInt h_isInt).symm
    rw [hq0_def, h_num_eq]; field_simp; ring
  -- (9) m0 : ↥A_F → ℕ, the count function pulled back from φ₀ via muEquiv.
  set m0 : ↥A_F → ℕ := fun a =>
    Sparse.φ₀ hSparse ((muEquiv hS hf2).symm ⟨a.val, hA_F_sub_Stilde a.property⟩)
    with hm0_def
  -- (10) ∑ᶠ d : S, φ₀ d = n.
  have h_sum_phi_eq_n :
      (∑ᶠ d : S, Sparse.φ₀ hSparse d) = (n : ℕ) := by
    classical
    set witness := hSparse.2.choose with hwit_def
    have h_supp_subset :
        Function.support (Sparse.φ₀ hSparse) ⊆ (hφ₀_finite.toFinset : Set S) := by
      intro d hd; simpa using hd
    rw [finsum_eq_sum_of_support_subset (Sparse.φ₀ hSparse)
          (s := hφ₀_finite.toFinset) h_supp_subset]
    simp only [Sparse.φ₀]
    have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        witness i ∈ hφ₀_finite.toFinset := by
      intro i _
      simp only [Set.Finite.mem_toFinset, Function.mem_support, Sparse.φ₀, ne_eq]
      rw [← hwit_def]
      intro h_card_zero
      have hmem : i ∈ (witness ⁻¹' ({witness i} : Set ↑S)) := by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
      have h_nonempty : (witness ⁻¹' ({witness i} : Set ↑S)).Nonempty := ⟨i, hmem⟩
      rw [Nat.card_eq_zero] at h_card_zero
      cases h_card_zero with
      | inl h_empty =>
        have : Nonempty ↑(witness ⁻¹' ({witness i} : Set ↑S)) := h_nonempty.to_subtype
        exact not_nonempty_iff.mpr h_empty this
      | inr h_inf =>
        have : Finite ↑(witness ⁻¹' ({witness i} : Set ↑S)) := by infer_instance
        exact absurd this (not_finite_iff_infinite.mpr h_inf)
    have h_card_eq : ∀ x : S,
        Nat.card ↑(witness ⁻¹' {x}) =
        (Finset.univ.filter (fun i : Fin n => witness i = x)).card := by
      intro x
      rw [show ↑(witness ⁻¹' {x}) = {i : Fin n // witness i = x} from rfl]
      exact Nat.subtype_card _ (fun i => by simp)
    have h_rhs :
        ∑ d ∈ hφ₀_finite.toFinset, Nat.card ↑(witness ⁻¹' {d}) =
        ∑ d ∈ hφ₀_finite.toFinset,
          (Finset.univ.filter (fun i : Fin n => witness i = d)).card := by
      apply Finset.sum_congr rfl; intro d _; exact h_card_eq d
    have h_maps_to : Set.MapsTo witness
        ((Finset.univ : Finset (Fin n)) : Set (Fin n))
        (hφ₀_finite.toFinset : Set S) :=
      fun i _ => Finset.mem_coe.mpr (h_maps i (Finset.mem_univ i))
    rw [h_rhs]
    rw [← Finset.card_eq_sum_card_fiberwise (f := witness) h_maps_to]
    simp
  -- (12) ∑ a : ↥A_F, m0 a = n. Bijection muQ : supp φ₀ ↔ A_F.
  have hm0_sum : ∑ a, m0 a = (n : ℕ) := by
    rw [← h_sum_phi_eq_n]
    rw [finsum_eq_sum_of_support_subset (Sparse.φ₀ hSparse) (s := hφ₀_finite.toFinset)
      (by intro d hd; simpa using hd)]
    exact muEquiv_sum_reindex hf2 hSparse hφ₀_finite A_F hA_F_def
      hA_F_sub_Stilde m0 (Sparse.φ₀ hSparse)
      (fun a => by simp only [hm0_def])
  -- (13) Apply Sub-lemma 2 to truncate.
  rw [coeff_pow_truncate_eq (hf2 := hf2) hSparse h_supp h_coeff_eq hCs_ne hφ₀_finite]
  -- (14) Apply `pi_filter_q0_eq_count_fiber` to get hCollapse.
  have hCollapse :=
    pi_filter_q0_eq_count_fiber (hf2 := hf2) hSparse
      A_F hA_F_sub_Stilde hA_F_covers_phi q0 hq0_residue hq0_value m0 (fun _ => rfl)
  -- (15) Apply `coeff_pow_collapse_to_multinomial_prod`.
  rw [coeff_pow_collapse_to_multinomial_prod (Γ := ℚ) (R := ℤᵘⁿ_[p,(T : ℕ)])
        fhatA A_F h_fhatA_supp_A_F (n : ℕ) q0 m0 hm0_sum hCollapse]
  -- (16) Identify the multinomial.
  have h_mult :
      Nat.multinomial (Finset.univ : Finset ↥A_F) m0 =
      Nat.multinomial hφ₀_finite.toFinset (Sparse.φ₀ hSparse) := by
    have h_sum_m0 : ∑ a : ↥A_F, m0 a = ∑ d ∈ hφ₀_finite.toFinset, Sparse.φ₀ hSparse d := by
      rw [hm0_sum]; rw [← h_sum_phi_eq_n,
        finsum_eq_sum_of_support_subset (Sparse.φ₀ hSparse) (s := hφ₀_finite.toFinset)
        (by intro d hd; simpa using hd)]
    have h_prodfact :
        ∏ a : ↥A_F, (m0 a).factorial
        = ∏ d ∈ hφ₀_finite.toFinset, (Sparse.φ₀ hSparse d).factorial :=
      muEquiv_prod_reindex hf2 hSparse hφ₀_finite A_F hA_F_def hA_F_sub_Stilde
        (fun a => (m0 a).factorial)
        (fun d => (Sparse.φ₀ hSparse d).factorial)
        (fun a => by simp only [hm0_def])
    have h1 := Nat.multinomial_spec (Finset.univ : Finset ↥A_F) m0
    have h2 := Nat.multinomial_spec hφ₀_finite.toFinset (Sparse.φ₀ hSparse)
    have hpos1 : 0 < ∏ a : ↥A_F, (m0 a).factorial :=
      Finset.prod_pos (fun _ _ => Nat.factorial_pos _)
    apply Nat.mul_left_cancel hpos1
    rw [h1, h_sum_m0, ← h2, h_prodfact]
  -- (17) Identify the product.
  have h_prod :
      (∏ a : ↥A_F, fhatA.coeff a.val ^ m0 a) =
      (∏ᶠ d : S, Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d)) := by
    -- Step (i): ∏ a : ↥A_F, fhatA.coeff a.val ^ m0 a
    --        = ∏ d ∈ supp_finset, Cs (muToStilde d) ^ φ₀ d (Finset.prod_bij)
    have h_step1 :
        (∏ a : ↥A_F, fhatA.coeff a.val ^ m0 a)
        = ∏ d ∈ hφ₀_finite.toFinset,
            Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d) :=
      muEquiv_prod_reindex hf2 hSparse hφ₀_finite A_F hA_F_def hA_F_sub_Stilde
        (fun a => fhatA.coeff a.val ^ m0 a)
        (fun d => Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d))
        (fun a => by
          have h_a_in : a.val ∈ A_F := a.property
          have h_in : fhatA.coeff a.val = fhat.coeff a.val :=
            h_fhatA_in_A_F a.val h_a_in
          have h_mu_to_S :
              muToStilde hf2 ((muEquiv hS hf2).symm
                ⟨a.val, hA_F_sub_Stilde a.property⟩)
              = ⟨a.val, hA_F_sub_Stilde a.property⟩ := by
            change (muEquiv hS hf2) ((muEquiv hS hf2).symm
              ⟨a.val, hA_F_sub_Stilde a.property⟩) = _
            exact (muEquiv hS hf2).apply_symm_apply _
          rw [h_in, h_mu_to_S]
          rw [show fhat.coeff a.val =
              Cs ⟨a.val, hA_F_sub_Stilde a.property⟩ from
            h_coeff_eq ⟨a.val, hA_F_sub_Stilde a.property⟩])
    -- Step (ii): ∏ d ∈ supp_finset, ... = ∏ᶠ d : S, ... via mulSupport subset.
    rw [h_step1]
    symm
    apply finprod_eq_finsetProd_of_mulSupport_subset
    intro d hd
    rw [Function.mem_mulSupport] at hd
    rw [Finset.mem_coe, hφ₀_finite.mem_toFinset, Function.mem_support]
    intro h_phi_zero
    apply hd
    rw [h_phi_zero, pow_zero]
  -- (18) Combine.
  rw [h_mult, h_prod]

/-- The multinomial-value identity at `(i, q) = (n, q0)`: the surviving coefficient
`(fhat ^ n).coeff q0` equals `β · ∏ Cs(μd)^φ₀(d)` for some non-zero β. The β
is the multinomial coefficient `Nat.multinomial(n; φ₀)` cast into `ℤᵘⁿ_[p,T]`,
which is non-zero via `CharZero` (instance `instCharZeroQpUnT`). -/
private lemma fhat_pow_coeff_at_phi0_nonzero_form
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    {hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}}
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    {Cs : ↥(Stilde hf2) → ℤᵘⁿ_[p,(T : ℕ)]}
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (h_supp : Function.support fhat.coeff ⊆ Stilde hf2)
    (h_coeff_eq : ∀ (s : ↥(Stilde hf2)), fhat.coeff s.val = Cs s)
    (hCs_ne : ∀ s : ↥(Stilde hf2), Cs s ≠ 0)
    (hφ₀_finite : (Function.support (Sparse.φ₀ hSparse)).Finite) :
    ∃ (β : ℤᵘⁿ_[p,(T : ℕ)]), β ≠ 0 ∧
      (fhat ^ (n : ℕ)).coeff
          (-(r0 hSparse) / T +
            ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
              (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num : ℚ) / T) =
        β * ∏ᶠ d : S, Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d) := by
  classical
  -- Notation for q0 and the canonical product P_prod.
  set q0 : ℚ := -(r0 hSparse) / T +
    ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
      (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num : ℚ) / T with hq0_def
  set P_prod : ℤᵘⁿ_[p,(T : ℕ)] :=
    ∏ᶠ d : S, Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d) with hP_prod_def
  -- k := the multinomial coefficient; β := its image in the coefficient ring.
  set k : ℕ := Nat.multinomial hφ₀_finite.toFinset (Sparse.φ₀ hSparse) with hk_def
  set β : ℤᵘⁿ_[p,(T : ℕ)] := (k : ℤᵘⁿ_[p,(T : ℕ)]) with hβ_def
  -- Derive the canonical value of `q0` from `w0_rat_isInt`.
  have _hq0_value : q0 = ∑ᶠ d : S,
      (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ) := by
    have h_isInt := w0_rat_isInt hf2 hSparse
    have h_num_eq : ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
                      (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num : ℚ)
                 = r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
                      (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ) :=
      (Rat.eq_num_of_isInt h_isInt).symm
    have hT_ne : (T : ℚ) ≠ 0 := by exact_mod_cast PNat.ne_zero T
    rw [hq0_def, h_num_eq]; field_simp; ring
  -- The residue at `q0` is integral.
  have _hq0_residue : ((T : ℚ) * q0 + r0 hSparse).isInt = true := by
    have hT_ne : (T : ℚ) ≠ 0 := by exact_mod_cast PNat.ne_zero T
    have hk_eq : (T : ℚ) * q0 + r0 hSparse =
        ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S, (Sparse.φ₀ hSparse d : ℚ) *
          (muQ hf2 d : ℚ)).num : ℚ) := by
      rw [hq0_def]; field_simp; ring
    rw [hk_eq]; exact isInt_intCast' _
  -- Apply the combinatorial collapse.
  have hcoeff_eq :
      (fhat ^ (n : ℕ)).coeff q0 = β * P_prod := by
    have h_axiom := fhat_pow_collapse_to_beta_P_prod (hf2 := hf2)
      hSparse h_supp h_coeff_eq hCs_ne hφ₀_finite
    change (fhat ^ (n : ℕ)).coeff q0 = β * P_prod
    rw [show β * P_prod
        = ((Nat.multinomial hφ₀_finite.toFinset (Sparse.φ₀ hSparse) :
              ℤᵘⁿ_[p,(T : ℕ)]) *
          (∏ᶠ d : S, Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d))) from by
        rfl]
    exact h_axiom
  -- `β` is nonzero by `CharZero`.
  have hβ_ne : β ≠ 0 := by
    have hk_pos : 0 < k := Nat.multinomial_pos _ _
    have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk_pos
    rw [hβ_def]
    intro h
    apply hk_ne
    have h_inj : Function.Injective (algebraMap ℤᵘⁿ_[p,(T : ℕ)] ℚᵘⁿ_[p, (T : ℕ)]) :=
      IsFractionRing.injective (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
    have h_alg :
        (algebraMap ℤᵘⁿ_[p,(T : ℕ)] ℚᵘⁿ_[p, (T : ℕ)])
            ((k : ℤᵘⁿ_[p,(T : ℕ)])) = 0 := by
      rw [h]; exact map_zero _
    have h_nat : ((k : ℕ) : ℚᵘⁿ_[p, (T : ℕ)]) = 0 := by
      have h_cast :
          (algebraMap ℤᵘⁿ_[p,(T : ℕ)] ℚᵘⁿ_[p, (T : ℕ)]) ((k : ℤᵘⁿ_[p,(T : ℕ)]))
            = ((k : ℕ) : ℚᵘⁿ_[p, (T : ℕ)]) := by
        push_cast; rfl
      rw [← h_cast]; exact h_alg
    exact_mod_cast h_nat
  refine ⟨β, hβ_ne, ?_⟩
  simpa [hP_prod_def] using hcoeff_eq

/-- the support of `Sparse.φ₀ hSparse` is finite (a structural
fact: `φ₀` is the count of `d ∈ S` covered by the witness function, and `hSparse`
provides a witness function whose range is finite). -/
private lemma phi0_support_finite
    {p : ℕ} [Fact (Nat.Prime p)]
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    {C n : ℕ+} (hSparse : IsCNSparse p C n S hS) :
    (Function.support (Sparse.φ₀ hSparse)).Finite := by
  refine Set.Finite.subset (Set.finite_range hSparse.2.choose) ?_
  intro d hd
  simp only [Function.mem_support, Sparse.φ₀, Set.mem_range] at hd ⊢
  by_contra h
  have hempty : hSparse.2.choose ⁻¹' {d} = ∅ := by
    ext i
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hi; exact h ⟨i, hi⟩
  rw [hempty] at hd; simp at hd

/-- the scaling factor `α := algebraMap c.val · algebraMap β` is
nonzero, given `c ∈ nonZeroDivisors ℤᵘⁿ_[p]` and `β ≠ 0` in `ℤᵘⁿ_[p,T]`. The
proof goes through the injectivity chain
`algebraMap ℤᵘⁿ_[p] → ℚᵘⁿ_[p] → ℚᵘⁿ_[p,T]` (via `IsFractionRing.injective` plus
the algebraMap-extension), so `algebraMap c.val ≠ 0`. Combined with
`algebraMap β ≠ 0` via the analogous injection
`algebraMap ℤᵘⁿ_[p,T] → ℚᵘⁿ_[p,T]`, the product is nonzero. -/
private lemma alpha_ne_zero_of_c_β
    {p : ℕ} [Fact (Nat.Prime p)] {T : ℕ+}
    (c : nonZeroDivisors ℤᵘⁿ_[p]) {β : ℤᵘⁿ_[p,(T : ℕ)]} (hβ_ne : β ≠ 0) :
    (algebraMap ℤᵘⁿ_[p] (ℚᵘⁿ_[p, (T : ℕ)])) c.val *
      (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])) β ≠ 0 := by
  have hc_ne_zero : c.val ≠ 0 := nonZeroDivisors.coe_ne_zero c
  have h_inj1 : Function.Injective (algebraMap ℤᵘⁿ_[p] ℚᵘⁿ_[p]) :=
    IsFractionRing.injective ℤᵘⁿ_[p] ℚᵘⁿ_[p]
  have h_inj2 : Function.Injective (algebraMap ℚᵘⁿ_[p] (ℚᵘⁿ_[p, (T : ℕ)])) :=
    (algebraMap ℚᵘⁿ_[p] (ℚᵘⁿ_[p, (T : ℕ)])).injective
  have h_inj_total :
      Function.Injective (algebraMap ℤᵘⁿ_[p] (ℚᵘⁿ_[p, (T : ℕ)])) := by
    intro x y hxy
    apply h_inj1
    apply h_inj2
    have hx := IsScalarTower.algebraMap_apply ℤᵘⁿ_[p] ℚᵘⁿ_[p]
      (ℚᵘⁿ_[p, (T : ℕ)]) x
    have hy := IsScalarTower.algebraMap_apply ℤᵘⁿ_[p] ℚᵘⁿ_[p]
      (ℚᵘⁿ_[p, (T : ℕ)]) y
    rw [hx, hy] at hxy
    exact hxy
  have h_alg_c_ne : (algebraMap ℤᵘⁿ_[p] (ℚᵘⁿ_[p, (T : ℕ)])) c.val ≠ 0 := by
    intro h
    apply hc_ne_zero
    exact h_inj_total (h.trans (map_zero _).symm)
  have h_inj_OQ :
      Function.Injective (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])) :=
    IsFractionRing.injective (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
  have h_alg_β_ne :
      (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])) β ≠ 0 := by
    intro h
    apply hβ_ne
    exact h_inj_OQ (h.trans (map_zero _).symm)
  exact mul_ne_zero h_alg_c_ne h_alg_β_ne

/-- Combinatorial existential.

Captures the multinomial-collapse content as a single existential at the
fixed integer exponent `w₀ := (r₀ + T·∑_{d∈S} φ₀(d)·μ(d)).num` (real by
`w0_rat_isInt`). The conclusion is:

1. ∃ α : ℚᵘⁿ_[p,T], α ≠ 0.
2. `algebraMap (Pfhat.coeff (-r0/T + w₀/T)) =
α · (algebraMap (P.coeff n) · ∏ᶠ algebraMap (Cs(μd)^φ₀(d)))`.
3. ∀ k : ℤ, k ≠ w₀, `Pfhat.coeff (-r0/T + k/T) = 0`.

Mathematical content (paper, Section 5):
* α is constructed as `algebraMap c.val · multinomial(n; φ₀)`, where
  - `c ∈ nonZeroDivisors ℤᵘⁿ_[p]` is the denominator from
    `IsLocalization.integerNormalization_spec` applied to `P`.
  - `multinomial(n; φ₀) = n!/∏ φ₀(d)!` is the multinomial coefficient
    (well-defined since `(support φ₀).Finite`).
  α ≠ 0 by `nonZeroDivisors.coe_ne_zero`, injective algebraMap, and
  `Nat.multinomial_pos` + `instCharZeroQpUnT`.
* Equation (1) at `w = w₀` follows from `Pfhat_TLifted_coeff_eq` (per-i sum) +
  multinomial expansion of `(fhat^i).coeff q` (via `pow_succ` +
  `HahnSeries.coeff_mul` + induction) + `phi_tilde_constraint_at_phi0`
  identifying the surviving index `(i, φ̃) = (n, φ₀ ∘ μ.symm)`.
* Equation (2) at `k ≠ w₀` follows from the same setup: the residue constraint
  for `q = -r0/T + k/T` paired with `phi_tilde_constraint_at_phi0` is infeasible
  for `k ≠ w₀`, so every contributing `(fhat^i).coeff q` summand has empty index
  set and vanishes.

This helper isolates the combinatorial heart so that `Pfhat_TLifted_collapse_witness`
can construct `(w₀, M₀)` and prove the eventually-constant claim without re-entering
the multinomial expansion. -/
private lemma Pfhat_TLifted_collapse_combinatorial
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    {hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}}
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    {Cs : ↥(Stilde hf2) → ℤᵘⁿ_[p,(T : ℕ)]}
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (_h_supp : Function.support fhat.coeff ⊆ Stilde hf2)
    (_h_coeff_eq : ∀ (s : ↥(Stilde hf2)), fhat.coeff s.val = Cs s)
    (hCs_ne : ∀ s : ↥(Stilde hf2), Cs s ≠ 0)
    (_h_mk_eq : Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) fhat = σ p (T : ℕ) f)
    {P : Polynomial ℚᵘⁿ_[p]} (_hP_aeval : (Polynomial.aeval f) P = 0)
    (_hP_natDegree : P.natDegree = n) :
    ∃ α : ℚᵘⁿ_[p, (T : ℕ)],
      α ≠ 0 ∧
      (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
          ((Pfhat_TLifted T P fhat).coeff
            (-(r0 hSparse) / T +
              ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
                (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num : ℚ) / T)) =
        α * ((algebraMap ℚᵘⁿ_[p] (ℚᵘⁿ_[p, (T : ℕ)])) (P.coeff n) *
          ∏ᶠ d : S, (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
                      (Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d))) ∧
      ∀ k : ℤ, k ≠ (r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
                    (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num →
        (Pfhat_TLifted T P fhat).coeff (-(r0 hSparse) / T + (k : ℚ) / T) = 0 := by
  -- Extract the denominator-clearing factor and the multinomial term, then
  -- package the surviving coefficient and the vanishing of the other terms.
  --
  -- Step 1: extract c ∈ nonZeroDivisors ℤᵘⁿ_[p] from IsLocalization.integerNormalization_spec.
  -- (In v4.31 the spec is `∃ b ∈ M, map = b • p` with `c` the bare element; we reconstruct the
  -- coefficient-wise statement `hc` used below.)
  obtain ⟨c, hc_mem, hc_eq⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤᵘⁿ_[p]) P
  have hc : ∀ i : ℕ, (algebraMap ℤᵘⁿ_[p] ℚᵘⁿ_[p])
      ((IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).coeff i) =
        c • P.coeff i := by
    intro i
    have := congrArg (fun q : Polynomial ℚᵘⁿ_[p] => q.coeff i) hc_eq
    simpa [Polynomial.coeff_map, Polynomial.coeff_smul] using this
  -- hc : ∀ (i : ℕ), (algebraMap ℤᵘⁿ_[p] ℚᵘⁿ_[p]) ((P_int P).coeff i) = c • P.coeff i
  -- Step 2: extract finite support of φ₀ (for `Nat.multinomial` argument).
  have hφ₀_finite : (Function.support (Sparse.φ₀ hSparse)).Finite :=
    phi0_support_finite hSparse
  -- Step 3: Apply `exists_FhatData` to obtain β ∈ ℤᵘⁿ_[p,T] with β ≠ 0 and
  -- the multinomial-value identity `(fhat^n).coeff q0 = β · ∏ Cs^φ₀`.
  obtain ⟨β, hβ_ne, hβ_coeff⟩ :=
    fhat_pow_coeff_at_phi0_nonzero_form (hS := hS) (hf2 := hf2) (Cs := Cs)
      (fhat := fhat) hSparse _h_supp _h_coeff_eq hCs_ne hφ₀_finite
  -- Step 4: define α := (algebraMap c.val : ℚᵘⁿ_[p,T]) * (algebraMap β : ℚᵘⁿ_[p,T]).
  set α : ℚᵘⁿ_[p, (T : ℕ)] :=
    (algebraMap ℤᵘⁿ_[p] (ℚᵘⁿ_[p, (T : ℕ)])) c *
    (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])) β with hα_def
  refine ⟨α, ?_, ?_⟩
  · -- Step 5: α ≠ 0 via `alpha_ne_zero_of_c_β`.
    exact alpha_ne_zero_of_c_β ⟨c, hc_mem⟩ hβ_ne
  · -- Set abbreviations for the surviving rational value `q0` and the inner sum index range.
    set q0 : ℚ := -(r0 hSparse) / T +
      ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
        (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num : ℚ) / T with hq0_def
    -- The combinatorial heart of the argument, packaged as a single inner claim. This
    -- captures the multinomial expansion of `(fhat^i).coeff q`) + the
    -- Constraint (`phi_tilde_constraint_at_phi0`):
    --
    -- (a) At `q = q0` (the surviving exponent), the per-`i` sum collapses to
    --     `i = n` with value `algebraMap (OQpUn_embd ((P_int P).coeff n)) * (mult · ∏ Cs^φ₀)`.
    --     (Proved by the multinomial expansion forcing `φ̃ = φ₀∘μ.symm`.)
    --     This, combined with `hc n` (`algebraMap (P_int.coeff n) = c.val · P.coeff n`)
    --     and the algebraMap chain `algebraMap ∘ OQpUn_embd = algebraMap ∘ algebraMap`
    --     (via IsScalarTower), gives equation 1.
    --
    -- (b) At `q = -r0/T + k/T` for `k ≠ w0_rat.num`, the per-`i` sum is identically
    --     `0` because no `φ̃` satisfies the residue constraint.
    --
    -- The combined claim:
    have h_collapse :
        ((algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
            ((Pfhat_TLifted T P fhat).coeff q0) =
          α * ((algebraMap ℚᵘⁿ_[p] (ℚᵘⁿ_[p, (T : ℕ)])) (P.coeff n) *
            ∏ᶠ d : S, (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
                        (Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d))))
        ∧
        (∀ k : ℤ, k ≠ (r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
                       (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num →
          ∀ i ∈ Finset.range
                  (((P_int P).map (OQpUn_embd p T)).natDegree + 1),
            (fhat ^ i).coeff (-(r0 hSparse) / T + (k : ℚ) / T) = 0) := by
      -- Discharge requires: multinomial expansion of `(fhat^i).coeff q`
      -- via `pow_succ` + `HahnSeries.coeff_mul` + induction; combined with
      -- `phi_tilde_constraint_at_phi0` to identify the unique φ̃ = φ₀ ∘ μ.symm.
      -- For (a): at q = q0, φ̃ = φ₀∘μ.symm is the unique surviving multi-index,
      -- with `i = n` and value `mult · ∏ Cs^φ₀`. Then use `hc n` to bridge to
      -- `algebraMap (P.coeff n)`. For (b): at q = -r0/T + k/T with k ≠ w0_rat.num,
      -- the residue constraint is infeasible, so the sum is empty.
      refine ⟨?_, ?_⟩
      · -- Conjunct (a): the surviving-coefficient identification at q0.
        -- Strategy: expand Pfhat.coeff q0 via Pfhat_TLifted_coeff_eq, collapse the
        -- sum to i = n using the degree bound + residue-collapse lemmas,
        -- then apply `exists_FhatData` to compute (fhat^n).coeff q0 and chain via hc n +
        -- IsScalarTower to express the LHS in α form.
        --
        -- Step 0: residue at q0 is integral (for invoking `fhat_pow_coeff_residue_collapse`).
        have hq0_residue : ((T : ℚ) * q0 + r0 hSparse).isInt = true := by
          have hT_ne : (T : ℚ) ≠ 0 := by exact_mod_cast PNat.ne_zero T
          have hk_eq : (T : ℚ) * q0 + r0 hSparse =
              ((r0 hSparse + (T : ℚ) * ∑ᶠ d : S, (Sparse.φ₀ hSparse d : ℚ) *
                (muQ hf2 d : ℚ)).num : ℚ) := by
            rw [hq0_def]; field_simp; ring
          rw [hk_eq]; exact isInt_intCast' _
        -- Step 1: sum-collapse via the degree bound + residue-collapse lemmas — extract i = n.
        have h_sum := Pfhat_TLifted_coeff_eq T P fhat q0
        have h_natDeg_le : ((P_int P).map (OQpUn_embd p T)).natDegree ≤ (n : ℕ) :=
          Pfhat_map_natDegree_bound T _hP_natDegree
        have h_sum_collapse :
            (∑ i ∈ Finset.range (((P_int P).map (OQpUn_embd p T)).natDegree + 1),
              OQpUn_embd p T ((P_int P).coeff i) * (fhat ^ i).coeff q0) =
            OQpUn_embd p T ((P_int P).coeff n) * (fhat ^ (n : ℕ)).coeff q0 := by
          apply Finset.sum_eq_single (n : ℕ)
          · intro i hi_mem hi_ne
            have hi_lt : i < ((P_int P).map (OQpUn_embd p T)).natDegree + 1 :=
              Finset.mem_range.mp hi_mem
            have hi_le : i ≤ (n : ℕ) := by omega
            by_cases h_coeff_zero : (fhat ^ i).coeff q0 = 0
            · rw [h_coeff_zero, mul_zero]
            · exfalso
              obtain ⟨hi_eq, _⟩ :=
                fhat_pow_coeff_residue_collapse (hS := hS) hf2 hSparse _h_supp
                  i hi_le q0 hq0_residue h_coeff_zero
              exact hi_ne hi_eq
          · intro hn_notmem
            have h_n_gt : ((P_int P).map (OQpUn_embd p T)).natDegree < (n : ℕ) := by
              by_contra hge
              push Not at hge
              exact hn_notmem (Finset.mem_range.mpr (Nat.lt_succ_of_le hge))
            have h_coeff_zero :
                OQpUn_embd p T ((P_int P).coeff n) = 0 := by
              have hP_map : ((P_int P).map (OQpUn_embd p T)).coeff n = 0 :=
                Polynomial.coeff_eq_zero_of_natDegree_lt h_n_gt
              rw [Polynomial.coeff_map] at hP_map
              exact hP_map
            rw [h_coeff_zero, zero_mul]
        -- Step 2: Rewrite Pfhat.coeff q0 to the collapsed form.
        rw [h_sum, h_sum_collapse, map_mul]
        -- Step 3: Apply `exists_FhatData` (hβ_coeff already has q0 in scope).
        rw [hβ_coeff, map_mul]
        -- Goal: algebraMap (OQpUn_embd ((P_int P).coeff n)) *
        -- (algebraMap β * algebraMap (∏ᶠ Cs^φ₀))
        --       = α * (algebraMap (P.coeff n) * ∏ᶠ algebraMap (Cs^φ₀))
        -- Step 4: distribute algebraMap over ∏ᶠ.
        have h_mulSup_finite :
            (Function.mulSupport (fun d : S =>
              Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d))).Finite := by
          refine hφ₀_finite.subset ?_
          intro d hd
          simp only [Function.mem_mulSupport, ne_eq] at hd
          simp only [Function.mem_support, ne_eq]
          intro hφ_zero
          apply hd
          rw [hφ_zero, pow_zero]
        rw [map_finprod _ h_mulSup_finite]
        -- Step 5: express algebraMap (OQpUn_embd ((P_int P).coeff n)) = algebraMap c.val *
        -- algebraMap (P.coeff n) via hc n + IsScalarTower.
        have h_OQpUn_step :
            (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
                (OQpUn_embd p T ((P_int P).coeff n))
              = (algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p, (T : ℕ)])) ((P_int P).coeff n) := by
          change (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
              ((algebraMap (ℤᵘⁿ_[p]) (ℤᵘⁿ_[p,(T : ℕ)])) ((P_int P).coeff n))
              = (algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p, (T : ℕ)])) ((P_int P).coeff n)
          exact (IsScalarTower.algebraMap_apply (ℤᵘⁿ_[p]) (ℤᵘⁿ_[p,(T : ℕ)])
            (ℚᵘⁿ_[p, (T : ℕ)]) ((P_int P).coeff n)).symm
        rw [h_OQpUn_step]
        have h_OQpUn_to_QpUn_step :
            (algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p, (T : ℕ)])) ((P_int P).coeff n)
              = (algebraMap (ℚᵘⁿ_[p]) (ℚᵘⁿ_[p, (T : ℕ)]))
                  ((algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p])) ((P_int P).coeff n)) :=
          IsScalarTower.algebraMap_apply (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p])
            (ℚᵘⁿ_[p, (T : ℕ)]) ((P_int P).coeff n)
        rw [h_OQpUn_to_QpUn_step]
        -- Unfold `P_int` so that hc applies (hc has the unfolded form).
        change (algebraMap (ℚᵘⁿ_[p]) (ℚᵘⁿ_[p, (T : ℕ)]))
              ((algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p]))
                ((IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).coeff n))
            * ((algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])) β *
              ∏ᶠ d : S, (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
                          (Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d)))
            = α * ((algebraMap ℚᵘⁿ_[p] (ℚᵘⁿ_[p, (T : ℕ)])) (P.coeff n) *
              ∏ᶠ d : S, (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
                          (Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d)))
        rw [hc n, Algebra.smul_def, map_mul]
        -- Goal: (algebraMap_ℚᵘⁿ_p_to_ℚᵘⁿ_p_T (algebraMap_ℤᵘⁿ_p_to_ℚᵘⁿ_p c.val)
        --        * algebraMap_ℚᵘⁿ_p_to_ℚᵘⁿ_p_T (P.coeff n))
        --       * (algebraMap β * ∏ᶠ algebraMap (Cs^φ₀))
        --       = α * (algebraMap (P.coeff n) * ∏ᶠ algebraMap (Cs^φ₀))
        have h_c_step :
            (algebraMap (ℚᵘⁿ_[p]) (ℚᵘⁿ_[p, (T : ℕ)]))
                ((algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p])) c)
              = (algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p, (T : ℕ)])) c :=
          (IsScalarTower.algebraMap_apply (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p])
            (ℚᵘⁿ_[p, (T : ℕ)]) c).symm
        rw [h_c_step, hα_def]
        ring
      · -- Conjunct (b): per-`i` vanishing for `k ≠ w0_rat.num`.
        -- per-`i` vanishing for `k ≠ w0_rat.num`, by contradiction via the residue-collapse lemma.
        intro k hk_ne i _hi_range
        by_contra h_coeff_ne
        -- Step 1: i ≤ n. From hi_range : i ∈ Finset.range (..natDegree + 1)
        -- and natDegree of (P_int P).map (OQpUn_embd p T) bounded by natDegree (P_int P)
        -- bounded by natDegree P = n. Use the strong form: factor through any i ≤ n
        -- by passing to a clean upper bound. `fhat_pow_coeff_residue_collapse`
        -- only required `i ≤ n`, but for `i > n` the coefficient is automatically
        -- zero by polynomial-degree considerations, so we never reach the residue-collapse lemma
        -- and can therefore safely assume the worst case `i ≤ n`. We bypass the
        -- degree-bound argument by splitting on `i ≤ n` vs `i > n`.
        by_cases hi_le : i ≤ (n : ℕ)
        · -- Apply `fhat_pow_coeff_residue_collapse` to extract i = n and force phiT = φ₀ ∘ μ.symm.
          set q : ℚ := -(r0 hSparse) / T + (k : ℚ) / T with hq_def
          -- Step 2: the residue clause T * q + r0 = k is an integer.
          have hT_ne_zero : (T : ℚ) ≠ 0 := by
            have : (T : ℕ) ≠ 0 := PNat.ne_zero T
            exact_mod_cast this
          have hq_residue : ((T : ℚ) * q + r0 hSparse).isInt = true := by
            have hk_eq : (T : ℚ) * q + r0 hSparse = (k : ℚ) := by
              rw [hq_def]; field_simp; ring
            rw [hk_eq]
            exact isInt_intCast' k
          obtain ⟨_hi_eq, hphi_unique⟩ :=
            fhat_pow_coeff_residue_collapse (hS := hS) hf2 hSparse _h_supp
              i hi_le q hq_residue h_coeff_ne
          -- Step 3: extract phiT and rewrite the residue identity to derive k = w0_rat.num.
          -- The residue bridge inside the residue-collapse lemma gives ∑ᶠ s, s.val * phiT s = q;
          -- combined with phiT = φ₀ ∘ μ.symm and change-of-variable, we get
          -- ∑ᶠ d : S, d.val * φ₀ d via μ. But the value of q is -r0/T + k/T,
          -- so T * q + r0 = T * ∑ᶠ s, s.val * phiT s + r0 = w0_rat = k, giving k = w0_rat.num.
          -- We extract the unique phiT to access the inner conjuncts of the residue-collapse lemma.
          rcases hphi_unique with ⟨phiT, ⟨_hphiT_finite, _hphiT_sum, hphiT_eq⟩, _⟩
          -- Derive the residue identity by re-using its residue clause.
          have hq_mem : q ∈ (fhat ^ i).support := by
            simpa [HahnSeries.mem_support] using h_coeff_ne
          obtain ⟨l, _hl_card, hl_sum⟩ :=
            fhat_pow_support_multiset_decomp (hf2 := hf2) (fhat := fhat)
              _h_supp i hq_mem
          -- The PDF argument: with phiT = φ₀ ∘ μ.symm we get
          --   ∑ᶠ s, s.val * phiT s = ∑ᶠ d : S, μ(d) * φ₀(d).
          -- So T * q + r0 = w0_rat ∈ ℤ. Combined with T * q + r0 = k, we get k = w0_rat.num.
          -- But the strict identity ∑ᶠ s, s.val * phiT s = ∑ᶠ d : S, μ(d).val * φ₀(d)
          -- requires invoking phi_tilde and the count/residue bridges from the
          -- residue-collapse lemma.
          -- The cleanest path: re-state w0_rat from hphiT_eq via finsum_comp_equiv.
          -- Use its `i = n` conclusion together with the residue identity
          -- `T * q + r0 = w0_rat` to derive `k = w0_rat.num`, contradicting `hk_ne`.
          -- We compute the integer equality directly:
          have h_phiT_sum :
              (∑ᶠ s : ↥(Stilde hf2), (s.val : ℚ) * (phiT s : ℚ)) =
              ∑ᶠ d : S, (muQ hf2 d : ℚ) * (Sparse.φ₀ hSparse d : ℚ) := by
            -- Apply phiT = φ₀ ∘ μ.symm, then change of variable along μ.
            have h1 : ∀ s : ↥(Stilde hf2),
                (s.val : ℚ) * (phiT s : ℚ) =
                (s.val : ℚ) *
                  ((Sparse.φ₀ hSparse ((muEquiv hS hf2).symm s) : ℕ) : ℚ) := by
              intro s
              rw [hphiT_eq]; rfl
            rw [finsum_congr h1]
            -- Now change variables along μ : S ≃ ↥(Stilde hf2).
            have h2 := finsum_comp_equiv (muEquiv hS hf2)
              (f := fun s : ↥(Stilde hf2) =>
                (s.val : ℚ) *
                  ((Sparse.φ₀ hSparse ((muEquiv hS hf2).symm s) : ℕ) : ℚ))
            -- h2 : ∑ᶠ d : S, ((μ d).val : ℚ) * (φ₀ (μ.symm (μ d)) : ℚ) = ∑ᶠ s, ...
            -- LHS of h2 simplifies via Equiv.symm_apply_apply.
            rw [← h2]
            apply finsum_congr; intro d
            have h_simp : (muEquiv hS hf2).symm ((muEquiv hS hf2) d) = d := by
              exact Equiv.symm_apply_apply _ _
            rw [h_simp]
            -- ((μ d : ↥(Stilde hf2)).val : ℚ) = muQ hf2 d, by def of muEquiv / muToStilde.
            rfl
          -- We now have T * q + r0 = k (from hq_residue) and want T * q + r0 = w0_rat.num
          -- as an integer. The bridge: T * (∑ᶠ s, s.val * phiT s) + r0 = w0_rat
          -- (this is the definition of w0_rat).
          have hw0_def :
              r0 hSparse + (T : ℚ) * (∑ᶠ d : S,
                (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)) =
              (T : ℚ) * (∑ᶠ s : ↥(Stilde hf2), (s.val : ℚ) * (phiT s : ℚ)) + r0 hSparse := by
            rw [h_phiT_sum]
            rw [show (∑ᶠ d : S, (muQ hf2 d : ℚ) * (Sparse.φ₀ hSparse d : ℚ)) =
                  (∑ᶠ d : S, (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)) by
              apply finsum_congr; intro d; ring]
            ring
          -- Pull q from the residue identity in `fhat_pow_coeff_residue_collapse`.
          have hq_phiT :
              (T : ℚ) * (∑ᶠ s : ↥(Stilde hf2), (s.val : ℚ) * (phiT s : ℚ)) = (T : ℚ) * q := by
            -- We need ∑ᶠ s, s.val * phiT s = q. This requires the residue-bridge
            -- (an internal step of `fhat_pow_coeff_residue_collapse`). Re-derive it inline:
            -- but since we have phiT chosen via hphiT_eq, we can re-invoke the same
            -- count-bridge / residue-bridge using l and hphiT_eq.
            -- A cleaner approach: re-state h_residue_bridge using the same definition
            -- l.toFinsupp = phiT, namely phiT = l.toFinsupp.
            -- But here, phiT was extracted from an ExistsUnique, not equated to l.toFinsupp.
            -- Use uniqueness: define phiT' as l.toFinsupp; show it satisfies the conditions;
            -- conclude phiT' = phiT.
            classical
            let phiT' : ↥(Stilde hf2) → ℕ := (l.toFinsupp : _ →₀ ℕ)
            have hphiT'_finite : (Function.support phiT').Finite := by
              simp [phiT']
            -- Count-bridge for phiT'.
            have h_supp_subset_pT :
                Function.support phiT' ⊆ ((l.toFinsupp).support : Set (↥(Stilde hf2))) := by
              intro s hs
              simp only [Function.mem_support, ne_eq] at hs
              exact Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hs)
            have hphiT'_count : (∑ᶠ s : ↥(Stilde hf2), phiT' s) = l.card := by
              rw [finsum_eq_sum_of_support_subset (s := (l.toFinsupp).support) phiT'
                h_supp_subset_pT]
              have hsum_eq : ∑ s ∈ (l.toFinsupp).support, phiT' s
                  = ∑ s ∈ (l.toFinsupp).support, l.count s := by
                apply Finset.sum_congr rfl
                intro s _
                simp [phiT', Multiset.toFinsupp_apply]
              rw [hsum_eq]
              have h_supp_eq_toFinset : (l.toFinsupp).support = l.toFinset := by
                ext s
                simp [Multiset.mem_toFinset]
              rw [h_supp_eq_toFinset]
              exact Multiset.toFinset_sum_count_eq l
            -- Residue-bridge for phiT'.
            have h_pT_residue :
                (∑ᶠ s : ↥(Stilde hf2), (s.val : ℚ) * (phiT' s : ℚ)) = q := by
              have h_supp_subset_pT' :
                  Function.support (fun s : ↥(Stilde hf2) => (s.val : ℚ) * (phiT' s : ℚ))
                    ⊆ ((l.toFinsupp).support : Set (↥(Stilde hf2))) := by
                intro s hs
                simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hs
                have hphi_ne : (phiT' s : ℚ) ≠ 0 := hs.2
                have hphi_ne_nat : phiT' s ≠ 0 := by exact_mod_cast hphi_ne
                exact Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hphi_ne_nat)
              rw [finsum_eq_sum_of_support_subset
                (fun s : ↥(Stilde hf2) => (s.val : ℚ) * (phiT' s : ℚ))
                (s := (l.toFinsupp).support) h_supp_subset_pT']
              have h_supp_eq_toFinset : (l.toFinsupp).support = l.toFinset := by
                ext s
                simp [Multiset.mem_toFinset]
              rw [h_supp_eq_toFinset]
              have h_each : ∀ s ∈ l.toFinset,
                  (s.val : ℚ) * (phiT' s : ℚ) = (s.val : ℚ) * (l.count s : ℚ) := by
                intro s _
                simp [phiT', Multiset.toFinsupp_apply]
              rw [Finset.sum_congr rfl h_each]
              have h_count_form :
                  ∑ s ∈ l.toFinset, (s.val : ℚ) * (l.count s : ℚ) =
                  ∑ s ∈ l.toFinset, (l.count s : ℕ) • (s.val : ℚ) := by
                apply Finset.sum_congr rfl
                intro s _
                rw [nsmul_eq_mul]; ring
              rw [h_count_form]
              rw [← Finset.sum_multiset_map_count l (fun s : ↥(Stilde hf2) => (s.val : ℚ))]
              exact hl_sum
            -- We also need phiT' = phiT (by uniqueness of its ExistsUnique).
            -- Both satisfy:
            --   * finite support
            --   * sum ≤ n
            --   * = φ₀ ∘ μ.symm
            -- For phiT', we need to verify these. The residue clause + sum bound need
            -- to be checked against `phi_tilde_constraint_at_phi0`, which gives
            -- phiT' = φ₀ ∘ μ.symm.
            -- BUT — uniqueness in `fhat_pow_coeff_residue_collapse`'s ExistsUnique only constrains
            -- the conjunction (finite ∧ sum ≤ n ∧ = φ₀ ∘ μ.symm). So both phiT and phiT'
            -- end up as φ₀ ∘ μ.symm — making them equal directly.
            have h_pT_le : ∑ᶠ s : ↥(Stilde hf2), phiT' s ≤ (n : ℕ) := by
              rw [hphiT'_count]
              rw [_hl_card] at *
              exact hi_le
            have hpT_residue_isInt :
                ((T : ℚ) * (∑ᶠ s : ↥(Stilde hf2), (s.val : ℚ) * (phiT' s : ℚ))
                  + r0 hSparse).isInt = true := by
              rw [h_pT_residue]; exact hq_residue
            have h_pT_eq : phiT' = Sparse.φ₀ hSparse ∘ (muEquiv hS hf2).symm :=
              phi_tilde_constraint_at_phi0 hS hf2 hSparse phiT' hphiT'_finite
                h_pT_le hpT_residue_isInt
            have h_eq_phiT_phiT' : phiT' = phiT := by
              rw [hphiT_eq, h_pT_eq]
            -- Conclude T * (∑ᶠ s, s.val * phiT s) = T * q.
            rw [← h_eq_phiT_phiT', h_pT_residue]
          -- Combine: r0 + T·∑φ₀(d)·μ(d) = T*q + r0.
          have hw0_eq_Tq_r0 :
              r0 hSparse + (T : ℚ) * (∑ᶠ d : S,
                (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)) =
              (T : ℚ) * q + r0 hSparse := by
            rw [hw0_def, hq_phiT]
          -- Now: T*q + r0 = k. So w0_rat = k. So k = w0_rat.num.
          have hk_eq : (T : ℚ) * q + r0 hSparse = (k : ℚ) := by
            rw [hq_def]; field_simp; ring
          have hw0_eq_k : (r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
                (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)) = (k : ℚ) := by
            rw [hw0_eq_Tq_r0, hk_eq]
          have hw0_num_eq_k : (r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
                (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ)).num = k := by
            rw [hw0_eq_k]
            exact Rat.num_intCast k
          exact hk_ne hw0_num_eq_k.symm
        · -- Case i > n: discharge via polynomial-degree bound on (P_int P).map (OQpUn_embd).
          exfalso
          apply hi_le
          have h_bound : ((P_int P).map (OQpUn_embd p T)).natDegree ≤ (n : ℕ) :=
            Pfhat_map_natDegree_bound T _hP_natDegree
          have h_in : i < ((P_int P).map (OQpUn_embd p T)).natDegree + 1 :=
            Finset.mem_range.mp _hi_range
          omega
    refine ⟨h_collapse.1, ?_⟩
    -- Equation 2: derived from `h_collapse.2` via `Finset.sum_eq_zero`.
    intro k hk_ne
    rw [Pfhat_TLifted_coeff_eq]
    apply Finset.sum_eq_zero
    intro i hi_mem
    have h_inner_zero :
        (fhat ^ i).coeff (-(r0 hSparse) / T + (k : ℚ) / T) = 0 :=
      h_collapse.2 k hk_ne i hi_mem
    rw [h_inner_zero, mul_zero]

/-- ceiling bound for sums of two fractions.

If `M ≥ ⌈((a + b) / T)⌉₊`, then `a / T + b / T ≤ (M : ℚ)`. This is the
arithmetic step used to verify that the chosen threshold `M₀` makes the
witness exponent `w₀` fall within the partial-sum cut-off. -/
private lemma ceil_div_add_div_le {T : ℚ} (a b : ℚ) {M : ℕ}
    (hM : M ≥ ⌈((a + b) / T)⌉₊) :
    a / T + b / T ≤ (M : ℚ) := by
  have h1 : (a + b) / T ≤ (M : ℚ) := Nat.ceil_le.mp hM
  linarith [show a / T + b / T = (a + b) / T from by ring]

/-- Combinatorial collapse witness.

Encapsulates the multinomial-expansion + φ̃-collapse content of the collapse argument
into a single existential. Returns a unique surviving integer exponent `w₀`,
a non-zero scaling factor `α : ℚᵘⁿ_[p,T]`, and a threshold `M₀ : ℕ` such that:

1. All "other" coefficients vanish: for every `w ≠ w₀`,
   `(Pfhat_TLifted T P fhat).coeff (-r0/T + w/T) = 0`.
2. The surviving coefficient identifies the LHS-goal up to scaling by `α`:
   `algebraMap (Pfhat.coeff (-r0/T + w₀/T)) = α · (LHS-goal expression)`.
3. The partial-sum sequence appearing in `IsTNullSeries` eventually stabilises:
   for every `M ≥ M₀`, the partial sum equals
   `(pInvTQ)^w₀ · algebraMap (Pfhat.coeff (-r0/T + w₀/T))`.

Mathematical content (paper, Section 5):
* `w₀ := r₀ + T·∑_{d∈S} φ₀(d)·μ(d) ∈ ℤ` (integer by `muQ_residue`).
* `α := (algebraMap (P_int.coeff n)) · multinomial(n; φ₀)`, where the multinomial
  coefficient `n!/∏_{d∈S} φ₀(d)!` is non-zero.
* The other-vanishing claim (1) is by `phi_tilde_constraint_at_phi0`: only the
  `φ̃ = φ₀ ∘ μ.symm` summand survives, and that forces `w = w₀`.
* The eventually-constant claim (3) is because `Pfhat_TLifted` has PWO support,
  so only finitely many integer `w` give non-zero `Pfhat.coeff (-r0/T + w/T)`;
  for `M` large enough, all such `w` satisfy the `≤ M` cut-off.

This helper isolates the combinatorial content from the analytic chaining in
`identity_c_collapsed`. -/
private lemma Pfhat_TLifted_collapse_witness
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    {hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}}
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    {Cs : ↥(Stilde hf2) → ℤᵘⁿ_[p,(T : ℕ)]}
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (_h_supp : Function.support fhat.coeff ⊆ Stilde hf2)
    (h_coeff_eq : ∀ (s : ↥(Stilde hf2)), fhat.coeff s.val = Cs s)
    (hCs_ne : ∀ s : ↥(Stilde hf2), Cs s ≠ 0)
    (_h_mk_eq : Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) fhat = σ p (T : ℕ) f)
    {P : Polynomial ℚᵘⁿ_[p]} (_hP_aeval : (Polynomial.aeval f) P = 0)
    (_hP_natDegree : P.natDegree = n) :
    ∃ (w₀ : ℤ) (α : ℚᵘⁿ_[p, (T : ℕ)]) (M₀ : ℕ),
      α ≠ 0 ∧
      (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
          ((Pfhat_TLifted T P fhat).coeff (-(r0 hSparse) / T + (w₀ : ℚ) / T)) =
        α * ((algebraMap ℚᵘⁿ_[p] (ℚᵘⁿ_[p, (T : ℕ)])) (P.coeff n) *
          ∏ᶠ d : S, (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
                      (Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d))) ∧
      ∀ M : ℕ, M ≥ M₀ →
        (∑ k : Set.Finite.toFinset
                (TfiniteBelow p (T : ℕ) (Pfhat_TLifted T P fhat) (-(r0 hSparse) / T) M),
            (pInvTQ p (T : ℕ)) ^ (k.val : ℤ) *
              (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
                ((Pfhat_TLifted T P fhat).coeff
                  (-(r0 hSparse) / T + (k.val : ℚ) / T))) =
          (pInvTQ p (T : ℕ)) ^ w₀ *
            (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
              ((Pfhat_TLifted T P fhat).coeff
                (-(r0 hSparse) / T + (w₀ : ℚ) / T)) := by
  -- Package the combinatorial heart into a single sub-existential, then derive
  -- the witness `M₀` and the eventually-constant claim from it.
  --
  -- Concrete witness for `w₀`: the rational `r₀ + T · ∑φ₀(d)·μ(d) ∈ ℤ` (real,
  -- via `w0_rat_isInt`); take its integer numerator.
  set w0_rat : ℚ :=
    r0 hSparse + (T : ℚ) * ∑ᶠ d : S,
      (Sparse.φ₀ hSparse d : ℚ) * (muQ hf2 d : ℚ) with hw0_rat_def
  have hw0_isInt : w0_rat.isInt = true := w0_rat_isInt hf2 hSparse
  refine ⟨w0_rat.num, ?_⟩
  -- The combinatorial heart of the argument, packaged as a sub-existential. The
  -- existential captures both (a) the coefficient identification at the
  -- surviving exponent `w₀ = w0_rat.num`, and (b) the vanishing of
  -- `Pfhat.coeff` at all OTHER points of the `(-r0/T + ℤ/T)` coset. Both
  -- conclusions follow from the multinomial collapse:
  -- (1) `fhat_pow_coeff_eq_multinomial` (multinomial expansion of `(fhat^i).coeff q`
  --     via `pow_succ` + `HahnSeries.coeff_mul` + induction);
  -- (2) `Pfhat_TLifted_coeff_at_q_collapse` (combine Helper 1 with
  --     `Pfhat_TLifted_coeff_eq` and `phi_tilde_constraint_at_phi0` to identify
  --     the surviving `(i, w) = (n, w₀)` summand and the vanishing of others);
  -- (3) integer-normalization scaling `IsLocalization.integerNormalization_spec`
  --     to construct `α := algebraMap c * multinomial(n; φ₀)` with `α ≠ 0`.
  have h_combinatorial :
      ∃ α : ℚᵘⁿ_[p, (T : ℕ)],
        α ≠ 0 ∧
        (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
            ((Pfhat_TLifted T P fhat).coeff (-(r0 hSparse) / T + (w0_rat.num : ℚ) / T)) =
          α * ((algebraMap ℚᵘⁿ_[p] (ℚᵘⁿ_[p, (T : ℕ)])) (P.coeff n) *
            ∏ᶠ d : S, (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
                        (Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d))) ∧
        ∀ k : ℤ, k ≠ w0_rat.num →
          (Pfhat_TLifted T P fhat).coeff (-(r0 hSparse) / T + (k : ℚ) / T) = 0 := by
    -- Delegate the combinatorial heart of the collapse argument to
    -- `Pfhat_TLifted_collapse_combinatorial`.
    exact Pfhat_TLifted_collapse_combinatorial hSparse _h_supp h_coeff_eq hCs_ne
      _h_mk_eq _hP_aeval _hP_natDegree
  obtain ⟨α, hα_ne, hα_eq, h_other_zero⟩ := h_combinatorial
  -- Define `M₀` as the natural ceiling of `(-r0 + w0_rat.num) / T`, so that
  -- `M ≥ M₀ ⟹ -r0/T + w0_rat.num/T ≤ M`.
  set M₀ : ℕ := ⌈((-(r0 hSparse) + (w0_rat.num : ℚ)) / T)⌉₊ with hM₀_def
  refine ⟨α, M₀, hα_ne, hα_eq, ?_⟩
  intro M hM
  -- Bound: `-r0/T + w0_rat.num/T ≤ M` for `M ≥ M₀`.
  have h_M_bound : -(r0 hSparse) / T + (w0_rat.num : ℚ) / T ≤ (M : ℚ) :=
    ceil_div_add_div_le _ _ hM
  -- Notation: `tFin` for the partial-sum Finset.
  set tFin : Finset ℤ :=
    Set.Finite.toFinset (TfiniteBelow p (T : ℕ) (Pfhat_TLifted T P fhat) (-(r0 hSparse) / T) M)
    with htFin_def
  -- Convert the subtype-style sum `∑ k : tFin, term k.val` to the
  -- membership-style sum `∑ k ∈ tFin, term k`.
  rw [show (∑ k : tFin,
        (pInvTQ p (T : ℕ)) ^ (k.val : ℤ) *
          (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
            ((Pfhat_TLifted T P fhat).coeff
              (-(r0 hSparse) / T + (k.val : ℚ) / T))) =
      ∑ k ∈ tFin,
        (pInvTQ p (T : ℕ)) ^ (k : ℤ) *
          (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
            ((Pfhat_TLifted T P fhat).coeff
              (-(r0 hSparse) / T + (k : ℚ) / T)) from
    Finset.sum_attach (s := tFin)
      (f := fun k : ℤ => (pInvTQ p (T : ℕ)) ^ k *
        (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
          ((Pfhat_TLifted T P fhat).coeff (-(r0 hSparse) / T + (k : ℚ) / T)))]
  -- Case-split on whether `w0_rat.num` is in the Finset.
  by_cases hw0_mem : w0_rat.num ∈ tFin
  · -- Case: `w0_rat.num ∈ tFin`. Use `Finset.sum_eq_single_of_mem`: all other
    -- terms vanish by `h_other_zero`.
    rw [Finset.sum_eq_single_of_mem w0_rat.num hw0_mem]
    intro b _hb_mem hb_ne
    rw [h_other_zero b hb_ne, map_zero, mul_zero]
  · -- Case: `w0_rat.num ∉ tFin`. Every `k ∈ tFin` has `k ≠ w0_rat.num`, so each
    -- term vanishes (`Finset.sum_eq_zero`). The RHS also vanishes because
    -- `Pfhat.coeff (-r0/T + w0_rat.num/T) = 0` (from the not-membership
    -- combined with `h_M_bound`).
    rw [show (∑ k ∈ tFin,
            (pInvTQ p (T : ℕ)) ^ (k : ℤ) *
              (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
                ((Pfhat_TLifted T P fhat).coeff
                  (-(r0 hSparse) / T + (k : ℚ) / T))) = 0 from by
      apply Finset.sum_eq_zero
      intro k hk_mem
      have hk_ne : k ≠ w0_rat.num := fun h_eq => hw0_mem (h_eq ▸ hk_mem)
      rw [h_other_zero k hk_ne, map_zero, mul_zero]]
    have h_coeff_zero :
        (Pfhat_TLifted T P fhat).coeff (-(r0 hSparse) / T + (w0_rat.num : ℚ) / T) = 0 := by
      by_contra h_ne
      apply hw0_mem
      rw [Set.Finite.mem_toFinset]
      exact ⟨h_M_bound, h_ne⟩
    rw [h_coeff_zero, map_zero, mul_zero]

/-- Collapsed form of equation (c): only the `φ̃ = φ₀ ∘ μ⁻¹` summand survives.

PDF reasoning: by `phi_tilde_constraint_at_phi0`, every nonzero summand of (c) has
`φ̃ = φ₀ ∘ μ⁻¹`, with the
single surviving `w` equal to `r₀ + T·∑φ₀(d)·μ(d) ∈ ℤ`. Equation (c) collapses to
`p^{r₀ + T·∑φ₀(d)·μ(d)} · a_n · (n!/∏φ₀(d)!) · ∏ Cs(μd)^{φ₀(d)} = 0`
in `ℤᵘⁿ_[p,T]` (or its embedding, depending on the natural ambient ring used by `identity_c`).

The statement here is presented as a `(... = 0)` in `ℤᵘⁿ_[p,T]`, abstracting over the
algebraMap and exponent conventions. -/
private lemma identity_c_collapsed
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    {hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}}
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    {Cs : ↥(Stilde hf2) → ℤᵘⁿ_[p,(T : ℕ)]}
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (h_supp : Function.support fhat.coeff ⊆ Stilde hf2)
    (h_coeff_eq : ∀ (s : ↥(Stilde hf2)), fhat.coeff s.val = Cs s)
    (hCs_ne : ∀ s : ↥(Stilde hf2), Cs s ≠ 0)
    (h_mk_eq : Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) fhat = σ p (T : ℕ) f)
    {P : Polynomial ℚᵘⁿ_[p]} (hP_aeval : (Polynomial.aeval f) P = 0)
    (hP_natDegree : P.natDegree = n) :
    (algebraMap ℚᵘⁿ_[p] ℚᵘⁿ_[p, (T : ℕ)]) (P.coeff n) *
        (∏ᶠ d : S, algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                     (Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d))) = 0 := by
  -- Chain through `Pfhat_TLifted_collapse_witness`.
  -- Step 1: get `Pfhat_TLifted ∈ TNullSeriesIdeal`.
  have hPfhat_null : Pfhat_TLifted T P fhat ∈ TNullSeriesIdeal p (T : ℕ) :=
    Pfhat_TLifted_isTNullSeries T hP_aeval h_mk_eq
  -- Step 2: Unwrap to IsTNullSeries (carrier definition of the ideal).
  have hPfhat_TNS : IsTNullSeries p (T : ℕ) (Pfhat_TLifted T P fhat) := hPfhat_null
  -- Step 3: specialize at g = -r0/T. Partial sums tend to 0.
  have h_at_r0 := hPfhat_TNS (- (r0 hSparse) / T)
  -- Step 4: extract the combinatorial witness.
  obtain ⟨w₀, α, M₀, hα_ne, h_coeff_eq', h_eventually⟩ :=
    Pfhat_TLifted_collapse_witness hSparse h_supp h_coeff_eq hCs_ne h_mk_eq hP_aeval hP_natDegree
  -- Step 5: from h_at_r0 + h_eventually, the eventually-constant value = 0.
  set surviving : ℚᵘⁿ_[p, (T : ℕ)] :=
    (pInvTQ p (T : ℕ)) ^ w₀ *
      (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
        ((Pfhat_TLifted T P fhat).coeff (-(r0 hSparse) / T + (w₀ : ℚ) / T)) with hsurv_def
  have h_surv_zero : surviving = 0 := by
    -- The partial sums equal `surviving` eventually, and they tend to 0.
    -- By uniqueness of limit, `surviving = 0`.
    have h_const_tendsto : Filter.Tendsto (fun _ : ℕ => surviving) Filter.atTop (nhds surviving) :=
      tendsto_const_nhds
    have h_partial_tendsto_surv : Filter.Tendsto
        (fun M : ℕ =>
          ∑ k : Set.Finite.toFinset
                  (TfiniteBelow p (T : ℕ) (Pfhat_TLifted T P fhat) (-(r0 hSparse) / T) M),
              (pInvTQ p (T : ℕ)) ^ (k.val : ℤ) *
                (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
                  ((Pfhat_TLifted T P fhat).coeff
                    (-(r0 hSparse) / T + (k.val : ℚ) / T)))
        Filter.atTop (nhds surviving) := by
      apply h_const_tendsto.congr'
      filter_upwards [Filter.eventually_ge_atTop M₀] with M hM_ge
      exact (h_eventually M hM_ge).symm
    exact tendsto_nhds_unique h_partial_tendsto_surv h_at_r0
  -- Step 6: substitute h_coeff_eq' to rewrite `surviving` in terms of the LHS-goal.
  have h_surv_eq : surviving =
      (pInvTQ p (T : ℕ)) ^ w₀ * (α *
        ((algebraMap ℚᵘⁿ_[p] (ℚᵘⁿ_[p, (T : ℕ)])) (P.coeff n) *
          ∏ᶠ d : S, (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
                      (Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d)))) := by
    rw [hsurv_def, h_coeff_eq']
  rw [h_surv_eq] at h_surv_zero
  -- Step 7: divide by non-zero factors `(pInvTQ)^w₀` and `α` to extract the LHS-goal.
  have h_pInvTQ_ne_zero : pInvTQ p (T : ℕ) ≠ 0 := by
    have := valued_v_pInvT (p := p) (T := T)
    intro h
    rw [h] at this
    simp at this
  have h_pInvTQ_pow_ne_zero : (pInvTQ p (T : ℕ)) ^ w₀ ≠ 0 := zpow_ne_zero w₀ h_pInvTQ_ne_zero
  -- From `(pInvTQ)^w₀ * (α * LHS) = 0` and `(pInvTQ)^w₀ ≠ 0`, get `α * LHS = 0`.
  have h_α_lhs_zero : α *
      ((algebraMap ℚᵘⁿ_[p] (ℚᵘⁿ_[p, (T : ℕ)])) (P.coeff n) *
        ∏ᶠ d : S, (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]))
                    (Cs (muToStilde hf2 d) ^ (Sparse.φ₀ hSparse d))) = 0 := by
    rcases mul_eq_zero.mp h_surv_zero with hp_zero | h_rest
    · exact absurd hp_zero h_pInvTQ_pow_ne_zero
    · exact h_rest
  -- From `α * LHS = 0` and `α ≠ 0`, get `LHS = 0`.
  rcases mul_eq_zero.mp h_α_lhs_zero with hα_zero | h_lhs_zero
  · exact absurd hα_zero hα_ne
  · exact h_lhs_zero

/-- The "final disjunction" emerging from Steps 4-5: either the leading coefficient
of `P` vanishes, or some `Cs (μ d)` vanishes. Both alternatives contradict
hypotheses (`P` has degree `n` so its leading coefficient is non-zero; `Cs` is
provably non-zero on `Stilde` by the data).

Proof: factor `identity_c_collapsed` in the integral domain `ℤᵘⁿ_[p,T]`. The two
non-trivial factors are `algebraMap (P.coeff n)` and `∏ᶠ algebraMap (Cs(μd)^φ₀(d))`.
At least one of them vanishes. `algebraMap` is injective (it's the inclusion of
`ℚᵘⁿ_[p]` into a field extension), so `P.coeff n = 0` from the first. From the second,
some `Cs(μd)^φ₀(d) = 0` (and `algebraMap` injective again), hence some
`Cs(μd) = 0` (in an integral domain, a power is zero iff the base is). -/
private lemma final_disjunction
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    {hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}}
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    {Cs : ↥(Stilde hf2) → ℤᵘⁿ_[p,(T : ℕ)]}
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (h_supp : Function.support fhat.coeff ⊆ Stilde hf2)
    (h_coeff_eq : ∀ (s : ↥(Stilde hf2)), fhat.coeff s.val = Cs s)
    (hCs_ne : ∀ s : ↥(Stilde hf2), Cs s ≠ 0)
    (h_mk_eq : Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) fhat = σ p (T : ℕ) f)
    {P : Polynomial ℚᵘⁿ_[p]} (hP_aeval : (Polynomial.aeval f) P = 0)
    (hP_natDegree : P.natDegree = n) :
    P.coeff n = 0 ∨ ∃ d : S, Cs (muToStilde hf2 d) = 0 := by
  have hCollapse :=
    identity_c_collapsed hSparse h_supp h_coeff_eq hCs_ne h_mk_eq hP_aeval hP_natDegree
  -- Factor in the field ℚᵘⁿ_[p,T].
  rcases mul_eq_zero.mp hCollapse with h_anQ | h_prodQ
  · -- Case 1: (algebraMap ℚᵘⁿ_[p] ℚᵘⁿ_[p,T]) (P.coeff n) = 0.
    -- Since ℚᵘⁿ_[p] is a field, the algebraMap is injective ⇒ P.coeff n = 0.
    left
    have h_inj : Function.Injective (algebraMap ℚᵘⁿ_[p] ℚᵘⁿ_[p, (T : ℕ)]) :=
      (algebraMap ℚᵘⁿ_[p] ℚᵘⁿ_[p, (T : ℕ)]).injective
    have := h_inj (h_anQ.trans (map_zero _).symm)
    exact this
  · -- Case 2: ∏ᶠ d : S, algebraMap (Cs (μd) ^ φ₀ d) = 0 in ℚᵘⁿ_[p,T].
    right
    -- The finprod's mulSupport sits inside `Function.support φ₀`, which is finite.
    have hφ₀_finite : (Function.support (Sparse.φ₀ hSparse)).Finite := by
      refine Set.Finite.subset (Set.finite_range hSparse.2.choose) ?_
      intro d hd
      simp only [Function.mem_support, Sparse.φ₀, Set.mem_range] at hd ⊢
      by_contra h
      have hempty : hSparse.2.choose ⁻¹' {d} = ∅ := by
        ext i
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro hi
        exact h ⟨i, hi⟩
      rw [hempty] at hd
      simp at hd
    have h_mulSup_sub :
        Function.mulSupport (fun d : S =>
          algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
            (Cs (muToStilde hf2 d) ^ Sparse.φ₀ hSparse d)) ⊆
        Function.support (Sparse.φ₀ hSparse) := by
      intro d hd
      simp only [Function.mem_mulSupport, ne_eq] at hd
      simp only [Function.mem_support, ne_eq]
      intro hφ₀_zero
      apply hd
      rw [hφ₀_zero, pow_zero, map_one]
    rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ h_mulSup_sub hφ₀_finite] at h_prodQ
    -- Now we have a Finset.prod = 0. Extract a vanishing factor.
    rcases Finset.prod_eq_zero_iff.mp h_prodQ with ⟨d, hd_mem, hd_zero⟩
    refine ⟨d, ?_⟩
    -- hd_zero : (algebraMap …) (Cs(μd)^φ₀ d) = 0 in ℚᵘⁿ_[p,T].
    -- Use injectivity of `algebraMap ℤᵘⁿ_[p,T] → ℚᵘⁿ_[p,T]` (IsFractionRing).
    have h_inj₂ : Function.Injective
        (algebraMap (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])) :=
      IsFractionRing.injective (ℤᵘⁿ_[p,(T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
    have h_powZ : Cs (muToStilde hf2 d) ^ Sparse.φ₀ hSparse d = 0 :=
      h_inj₂ (hd_zero.trans (map_zero _).symm)
    -- `ℤᵘⁿ_[p,T]` is an integral domain (`instIsDomainOQpUnT`). Use pow_eq_zero_iff.
    have hφ₀_pos : Sparse.φ₀ hSparse d ≠ 0 := by
      have hd_mem' : d ∈ Function.support (Sparse.φ₀ hSparse) :=
        (Set.Finite.mem_toFinset hφ₀_finite).mp hd_mem
      exact hd_mem'
    exact (pow_eq_zero_iff hφ₀_pos).mp h_powZ

/-! ### Step 6 — final assembly using the disjunction.

The engine that derives False from the FhatData + IsCNSparse + the polynomial setup. -/
private lemma sparse_contradiction_engine
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    {hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}}
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    (hd : FhatData f T hf2)
    {P : Polynomial ℚᵘⁿ_[p]} (hP_aeval : (Polynomial.aeval f) P = 0)
    (hP_natDegree : P.natDegree = n)
    (hP_lead_ne : P.coeff n ≠ 0) : False := by
  obtain ⟨Cs, fhat, hCs_ne, h_supp, h_coeff_eq, h_mk_eq⟩ := hd
  rcases final_disjunction (Cs := Cs) (fhat := fhat) hSparse h_supp h_coeff_eq hCs_ne
      h_mk_eq hP_aeval hP_natDegree with hP_zero | ⟨d, hCs_zero⟩
  · exact hP_lead_ne hP_zero
  · exact hCs_ne _ hCs_zero

end MainTheorem

open MainTheorem in
/-- Internal form of the main theorem, phrased with the combinatorial `IsCNSparse` hypothesis on a
set `S` of digit series (rather than the analytic `IsSparse` on a set of rationals). The user-facing
`main_theorem` is obtained by translating `IsSparse` into this form via
`IsSparse_iff_IsCNSparse`. -/
theorem main_theorem₀ (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+)
(S : Set (DigitSeries)) (hS : ∀ f ∈ S, f.IsP p)
(hS : ∃ c : PNat, ∃ D : Set ℕ+, D.Infinite ∧ ∀ n ∈ D, IsCNSparse p c n S hS)
(hf2 : IsRepModZ ((DigitSeries.norm p) '' S) {-1 * T * q | q ∈ f.support}) :
  ¬ IsAlgebraic ℚᵘⁿ_[p] f := by
  by_contra hc
  rcases hc with ⟨P', hP₀, hP⟩
  rcases hS with ⟨C,D,hD1,hcD⟩
  have hnel : ∃ n ∈ D, n > P'.natDegree := by
    contrapose hD1
    simp only [neg_mul, one_mul, ne_eq, gt_iff_lt, not_exists, not_and, not_lt,
      Set.not_infinite] at *
    rw [Set.finite_iff_bddAbove]
    refine ⟨⟨P'.natDegree + 1, Nat.zero_lt_succ P'.natDegree⟩,mem_upperBounds.mpr <| fun x hx => ?_⟩
    refine (PNat.coe_le_coe x ⟨P'.natDegree + 1, Nat.zero_lt_succ P'.natDegree⟩).mp ?_
    exact Nat.le_succ_of_le <| hD1 x hx
  rcases hnel with ⟨n, hnD, hn⟩
  let P := P' * Polynomial.X ^ (n - P'.natDegree)
  have hP1 : P.natDegree = n := by
    unfold P
    rw [Polynomial.natDegree_mul hP₀]
    · simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
      exact Nat.add_sub_of_le <| by linarith
    · simp only [ne_eq, pow_eq_zero_iff', Polynomial.X_ne_zero, false_and, not_false_eq_true]
  have hP2 : P.aeval f = 0 := by simp [P, hP]
  have hP_ne : P ≠ 0 := by
    intro hP_zero
    have hP'_zero : P' = 0 := by
      apply mul_left_cancel₀ (a := (Polynomial.X (R := ℚᵘⁿ_[p]) ^ ((n : ℕ) - P'.natDegree)))
      · exact pow_ne_zero _ Polynomial.X_ne_zero
      · rw [mul_zero, mul_comm]; exact hP_zero
    exact hP₀ hP'_zero
  have hP3 : P.coeff n ≠ 0 := by
    rw [← hP1, Polynomial.coeff_natDegree]
    exact (Polynomial.leadingCoeff_ne_zero).mpr hP_ne
  -- Build the lift data and apply the engine.
  have lift_data := exists_FhatData f T hf2
  exact sparse_contradiction_engine (hcD n hnD) lift_data hP2 hP1 hP3

/-- **Theorem 1.7 / 5.3 (transcendence over `ℚᵘⁿ_[p]`).** Let `f : 𝕃_[p]` be a `p`-adic Hahn series
and `T ≥ 1` an integer. If `−T · Supp(f)` admits a nonzero **sparse** set `W` of representatives
modulo `ℤ`, then `f` is transcendental over the completed maximal unramified extension `ℚᵘⁿ_[p]`.

This is the main theorem of the paper. The proof assumes `f` is algebraic and expands the resulting
polynomial relation via the multinomial theorem; the sparseness of `W` isolates a single surviving
nonzero coefficient, contradicting the relation. -/
theorem main_theorem (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+)
(W : Set ℚ) (hW1 : W ≠ {0}) (hW2 : IsSparse p W)
(hf2 : IsRepModZ W {-1 * T * q | q ∈ f.support}) :
  ¬ IsAlgebraic ℚᵘⁿ_[p] f := by
  rw [IsSparse_iff_IsCNSparse] at hW2
  · rcases hW2 with ⟨S, hSP, hS, c, D, hD1, hD2⟩
    apply main_theorem₀ p f T S hSP ⟨c, D, hD1, hD2⟩
    rwa [hS]
  · exact hW1

/-- **Theorem 1.7 / 5.3 (transcendence over `ℚ_[p]`).** The `ℚ_[p]`-version of `main_theorem`: under
the same sparseness hypothesis, `f` is transcendental over `ℚ_[p]`. Immediate from the `ℚᵘⁿ_[p]`
version, since transcendence over the larger field `ℚᵘⁿ_[p]` implies transcendence over `ℚ_[p]`. -/
theorem main_theorem' (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+)
(W : Set ℚ) (hW1 : W ≠ {0}) (hW2 : IsSparse p W)
(hf2 : IsRepModZ W {-1 * T * q | q ∈ f.support}) :
  ¬ IsAlgebraic ℚ_[p] f := by
  have := main_theorem p f T W hW1 hW2 hf2
  contrapose this
  exact pAdicHahnSeries.alg_QpUn_of_alg_Qp p f this

end FormalizedSparse




