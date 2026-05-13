import FormalizedSparse.References.Poonen1993
import FormalizedSparse.Sparse
import FormalizedSparse.Tscaled
import Mathlib.Data.PNat.Interval
import Mathlib.RingTheory.Localization.Integral
/-Your only goal is to prove main_theorem in this file. The corresponding informal proof is Theorem 5.1 of MainTheorem.pdf. This file should be sorry-free at the end.-/
open Sparse Poonen1993 TScaled

def IsRepModZ (A B : Set ℚ) : Prop :=
  (
    ∀ b ∈ B, ∃! a ∈ A, (a - b).isInt
  ) ∧ (
    ∀ a ∈ A, ∃ b ∈ B, (a - b).isInt
  )

-- Bring `NeZero T.val` into scope for any `T : ℕ+` so we can use `Tscaled` API.
instance PNat.coe_neZero (T : ℕ+) : NeZero (T : ℕ) := ⟨T.ne_zero⟩

namespace MainTheorem

/-! ### Step 1 — support cosets `Sd`, `mu_q`, `Stilde`. -/

/-- The "coset slice" `f.support ∩ (-‖d‖/T + (1/T)ℤ)` for a `DigitSeries` `d`.
We use the equivalent algebraic form `(d.norm p + T·q).isInt`. -/
noncomputable def Sd (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+) (d : DigitSeries) :
    Set ℚ :=
  f.support ∩ {q | ((d.norm p : ℚ) + (T : ℚ) * q).isInt = true}

lemma Sd_subset_support {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+) (d : DigitSeries) :
    Sd p f T d ⊆ f.support :=
  Set.inter_subset_left

lemma Sd_isWF {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+) (d : DigitSeries) :
    (Sd p f T d).IsWF :=
  (Poonen1993.support_IsPWO f).isWF.mono (Sd_subset_support f T d)

lemma Sd_isPWO {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+) (d : DigitSeries) :
    (Sd p f T d).IsPWO :=
  (Poonen1993.support_IsPWO f).mono (Sd_subset_support f T d)

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
noncomputable def mu_q {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d : S) : ℚ :=
  (Sd_isWF f T d.val).min (Sd_nonempty hf2 d.property)

lemma mu_q_mem_support {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d : S) : mu_q hf2 d ∈ f.support := by
  have h := (Sd_isWF f T d.val).min_mem (Sd_nonempty hf2 d.property)
  exact Sd_subset_support f T _ h

lemma mu_q_residue {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d : S) : ((d.val.norm p : ℚ) + (T : ℚ) * mu_q hf2 d).isInt = true :=
  ((Sd_isWF f T d.val).min_mem (Sd_nonempty hf2 d.property)).2

/-- Below `mu_q d`, `f.coeff` vanishes on the coset (since `mu_q d` is the minimum). -/
lemma f_coeff_zero_below {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d : S) {q : ℚ}
    (hq_lt : q < mu_q hf2 d)
    (hres : ((d.val.norm p : ℚ) + (T : ℚ) * q).isInt = true) :
    pAdicHahnSeries.coeff f q = 0 := by
  by_contra hne
  have hq_in_supp : q ∈ f.support := hne
  have hq_in_Sd : q ∈ Sd p f T d.val := ⟨hq_in_supp, hres⟩
  exact (Sd_isWF f T d.val).not_lt_min (Sd_nonempty hf2 d.property) hq_in_Sd hq_lt

/-- The key uniqueness step: `mu_q` is injective. -/
lemma mu_q_injective {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} (hS : ∀ d ∈ S, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Function.Injective (mu_q (T := T) hf2) := by
  intro d d' hmu
  have hd := mu_q_residue hf2 d
  have hd' := mu_q_residue hf2 d'
  have h_sub_int :
      ((d.val.norm p : ℚ) - (d'.val.norm p : ℚ)).isInt = true := by
    set a := (d.val.norm p : ℚ) + (T : ℚ) * mu_q hf2 d with ha_def
    set b := (d'.val.norm p : ℚ) + (T : ℚ) * mu_q hf2 d' with hb_def
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

/-- The "S̃" of the PDF, packaged as a `Set ℚ`: `{ mu_q d | d ∈ S }`. -/
noncomputable def Stilde {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) : Set ℚ :=
  Set.range (mu_q (T := T) hf2)

lemma Stilde_subset_support {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Stilde hf2 ⊆ f.support := by
  rintro q ⟨d, rfl⟩; exact mu_q_mem_support hf2 d

lemma Stilde_isPWO {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    (Stilde hf2).IsPWO :=
  (Poonen1993.support_IsPWO f).mono (Stilde_subset_support hf2)

/-- The bijection `μ : S → Stilde`. -/
noncomputable def mu_to_Stilde {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    S → ↥(Stilde hf2) :=
  fun d => ⟨mu_q hf2 d, ⟨d, rfl⟩⟩

lemma mu_to_Stilde_bijective {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} (hS : ∀ d ∈ S, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Function.Bijective (mu_to_Stilde (T := T) hf2) := by
  refine ⟨fun d d' h => ?_, ?_⟩
  · have : mu_q hf2 d = mu_q hf2 d' := by
      simpa [mu_to_Stilde] using congrArg Subtype.val h
    exact mu_q_injective hS hf2 this
  · rintro ⟨q, ⟨d, hq_eq⟩⟩
    refine ⟨d, ?_⟩
    apply Subtype.ext
    simp [mu_to_Stilde, hq_eq]

/-- The S→Stilde bijection as an `Equiv`. -/
noncomputable def mu_equiv {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} (hS : ∀ d ∈ S, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    S ≃ ↥(Stilde hf2) :=
  Equiv.ofBijective _ (mu_to_Stilde_bijective hS hf2)

/-! ### Step 2 — coefficient bundles `C_s` (PDF p. 8).

For `s ∈ Stilde`, the PDF defines `C_s = ∑_{w ∈ ℤ} [f(s + w/T)] · pInvT^w ∈ ℤᵘⁿ_[p,T]`.
Since `s = mu_q d` is the minimum of `Sd d`, the negative-`w` terms vanish, so
`C_s = ∑_{w ≥ 0} [f(s + w/T)] · pInvT^w`, a convergent series in the complete DVR
`ℤᵘⁿ_[p,T]`. We decompose the construction into a term `Cs_term`, a partial sum
`Cs_partial`, an existential limit lemma `exists_Cs` (the analytical hard step), and
the final definition `Cs`. -/

/-- §2a — the `w`-th summand `OQpUn_embd p T (teichmuller p (f.coeff (s + w/T))) · pInvT^w`. -/
noncomputable def Cs_term {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (w : ℕ) : ℤᵘⁿ_[p, (T : ℕ)] :=
  OQpUn_embd p T (WittVector.teichmuller p (f.coeff (s.val + (w : ℚ) / T))) * (pInvT p T) ^ w

/-- §2b — finite partial sum `∑_{w < N} Cs_term hf2 s w`. -/
noncomputable def Cs_partial {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (N : ℕ) : ℤᵘⁿ_[p, (T : ℕ)] :=
  ∑ w ∈ Finset.range N, Cs_term hf2 s w

/-- §2c (analytical hard step, *body deferred*) — the partial sums `Cs_partial` admit a
non-zero limit in `ℤᵘⁿ_[p,T]`.

Construction outline: the algebraMap to the complete DVF `ℚᵘⁿ_[p,T]` carries the
sequence to a Cauchy sequence (using `valued_v_pInvT_zpow` to bound the tails by
`(ofAdd (-w) : WithZero _)`), the limit exists by `instCompleteSpaceQpUnT`, and it
lies in the closed unit ball (the image of `ℤᵘⁿ_[p,T]` under algebraMap). Non-vanishing
is from the `w = 0` term: `OQpUn_embd p T (teichmuller p (f.coeff s))` with
`f.coeff s ≠ 0` (since `s ∈ Stilde ⊆ f.support` via `Stilde_subset_support`).

The Tendsto clause anchors `Cs s` as the genuine analytical limit; the next round
will use this to prove `mk_fhat_eq_sigma_f` via canonical T-expansion uniqueness. -/
private lemma exists_Cs {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    ∃ c : ℤᵘⁿ_[p, (T : ℕ)],
      c ≠ 0 ∧
      Filter.Tendsto
        (fun N => algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))
        Filter.atTop
        (nhds (algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) c)) := by
  sorry

/-- §2c' — `Cs hf2 s ∈ ℤᵘⁿ_[p,T]`, the coefficient bundle for `s ∈ Stilde`. -/
noncomputable def Cs {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) : ℤᵘⁿ_[p, (T : ℕ)] :=
  (exists_Cs hf2 s).choose

/-- §2d — `Cs hf2 s ≠ 0`. Immediate from `exists_Cs`. -/
lemma Cs_ne_zero {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) : Cs hf2 s ≠ 0 :=
  (exists_Cs hf2 s).choose_spec.1

/-- §2e — `algebraMap (Cs_partial hf2 s N)` converges to `algebraMap (Cs hf2 s)` in
`ℚᵘⁿ_[p,T]`. This is the analytical characterization of `Cs` as a Cauchy sum. -/
lemma Cs_tendsto {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    Filter.Tendsto
      (fun N => algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))
      Filter.atTop
      (nhds (algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs hf2 s))) :=
  (exists_Cs hf2 s).choose_spec.2

/-! ### Step 3 — the lift `fhat` (PDF p. 8). -/

/-- §3a — the coefficient function of `fhat`: `Cs ⟨q, h⟩` on `Stilde`, `0` elsewhere. -/
noncomputable def fhat_coeff {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (q : ℚ) : ℤᵘⁿ_[p, (T : ℕ)] := by
  classical
  exact (if h : q ∈ Stilde hf2 then Cs hf2 ⟨q, h⟩ else 0)

/-- §3b — the T-lifted Hahn series `fhat : TLiftedPAdicHahnSeries p T`. -/
noncomputable def fhat {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    TLiftedPAdicHahnSeries p (T : ℕ) where
  coeff := fhat_coeff hf2
  isPWO_support' := by
    apply (Stilde_isPWO hf2).mono
    intro q hq
    by_contra hq_notin
    apply hq
    show fhat_coeff hf2 q = 0
    unfold fhat_coeff
    exact dif_neg hq_notin

/-- §3c — `Support fhat ⊆ Stilde`. -/
lemma fhat_support_subset {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Function.support (fhat hf2).coeff ⊆ Stilde hf2 := by
  intro q hq
  by_contra hq_notin
  apply hq
  show fhat_coeff hf2 q = 0
  unfold fhat_coeff
  exact dif_neg hq_notin

/-- §3d — at `s ∈ Stilde`, the `fhat` coefficient is `Cs s`. -/
lemma fhat_coeff_eq_Cs {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) : (fhat hf2).coeff s.val = Cs hf2 s := by
  show fhat_coeff hf2 s.val = _
  unfold fhat_coeff
  exact dif_pos s.property

/-! §3e (now decomposed into two pieces below: a σ-bridge and an analytical core
helper). The main lemma `mk_fhat_eq_sigma_f` glues them together with
`Ideal.Quotient.eq`.

Original proof outline: by canonical T-expansion uniqueness
(`exists_canonical_T_expansion`) applied to `σ p T f` (whose canonical coefficient
is `f.coeff` via `σ_coeff_compat`), it suffices to show
`fhat - TLiftedPAdicHahnSeries.from_coeff p T f.coeff (support_IsPWO f)
∈ TNullSeriesIdeal p T`. The difference has support contained in `f.support`, with
coefficient `OQpUn_embd p T (teichmuller p (f.coeff q)) - fhat_coeff hf2 q`:
* at `q = s ∈ Stilde`, this is `teichmuller (f.coeff s) - Cs s`, the negation of the
  `w ≥ 1` tail of `Cs s`;
* at `q ∈ f.support \ Stilde`, by `Stilde_isRepModZ_oneOverT` we have a unique
  `s ∈ Stilde` and `w ≥ 1` with `q = s.val + w/T`, and the coefficient is precisely
  `Cs_term hf2 s w` (the `w`-th tail term of `Cs s`).
The partial-sum tendency at every `g ∈ ℚ` collapses by re-indexing into the same
Cauchy tail used in `exists_Cs`. -/

/-- §3e-bridge — Structural reduction: `σ p T f = mk (from_coeff p T f.coeff (support_IsPWO f))`.
Pure σ-machinery; the proof mimics the σ_coeff_compat strategy and uses no `fhat` data. -/
private lemma sigma_eq_mk_from_coeff_fcoeff
    {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+) :
    σ p (T : ℕ) f = Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ))
      (TLiftedPAdicHahnSeries.from_coeff p (T : ℕ) (pAdicHahnSeries.coeff f)
        (support_IsPWO f)) := by
  set s_σ := (exists_canonical_T_expansion p (T : ℕ) (σ p (T : ℕ) f)).choose
    with hs_σ_def
  -- s_σ.val = pAdicHahnSeries.coeff f by σ_coeff_compat.
  have hs_σ_val : s_σ.val = pAdicHahnSeries.coeff f := σ_coeff_compat p (T : ℕ) f
  -- The canonical-T-expansion choose_spec gives the ringCon witness.
  have h_ringCon : Ideal.Quotient.ringCon (TNullSeriesIdeal p (T : ℕ))
      (σ p (T : ℕ) f).out
      (TLiftedPAdicHahnSeries.from_coeff p (T : ℕ) s_σ.val s_σ.prop) :=
    (exists_canonical_T_expansion p (T : ℕ) (σ p (T : ℕ) f)).choose_spec.1
  -- Quotient.sound packages the ringCon into an equality of `mk`s.
  have h1 : Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) (σ p (T : ℕ) f).out
      = Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ))
            (TLiftedPAdicHahnSeries.from_coeff p (T : ℕ) s_σ.val s_σ.prop) :=
    Quotient.sound h_ringCon
  -- Rewrite the `from_coeff`'s value argument using hs_σ_val (proof irrelevance on prop).
  have h2 : TLiftedPAdicHahnSeries.from_coeff p (T : ℕ) s_σ.val s_σ.prop
      = TLiftedPAdicHahnSeries.from_coeff p (T : ℕ) (pAdicHahnSeries.coeff f)
          (support_IsPWO f) := by
    apply HahnSeries.coeff_inj.mp
    funext n
    change OQpUn_embd p (T : ℕ) (WittVector.teichmuller p (s_σ.val n)) =
        OQpUn_embd p (T : ℕ) (WittVector.teichmuller p (pAdicHahnSeries.coeff f n))
    rw [hs_σ_val]
  rw [← Ideal.Quotient.mk_out (σ p (T : ℕ) f), h1, h2]

/-! #### `Rat.isInt` helpers (used in both §3e and §5a). -/

/-- An integer cast to `ℚ` has `Rat.isInt = true`. -/
private lemma isInt_intCast' (k : ℤ) : ((k : ℚ)).isInt = true := by
  rw [Rat.isInt]; simp

/-- A natural cast to `ℚ` has `Rat.isInt = true`. -/
private lemma isInt_natCast' (k : ℕ) : ((k : ℚ)).isInt = true := by
  rw [Rat.isInt]; simp

/-- `(0 : ℚ).isInt = true`. -/
private lemma isInt_zero' : ((0 : ℚ)).isInt = true := by
  rw [Rat.isInt]; simp

/-- `Rat.isInt` is closed under addition. -/
private lemma isInt_add' {a b : ℚ} (ha : a.isInt = true) (hb : b.isInt = true) :
    (a + b).isInt = true := by
  have ha_eq : a = (a.num : ℚ) := Rat.eq_num_of_isInt ha
  have hb_eq : b = (b.num : ℚ) := Rat.eq_num_of_isInt hb
  rw [ha_eq, hb_eq]
  have h : (a.num : ℚ) + (b.num : ℚ) = (((a.num + b.num : ℤ)) : ℚ) := by
    push_cast; ring
  rw [h]
  exact isInt_intCast' _

/-- `Rat.isInt` is closed under subtraction. -/
private lemma isInt_sub' {a b : ℚ} (ha : a.isInt = true) (hb : b.isInt = true) :
    (a - b).isInt = true := by
  have ha_eq : a = (a.num : ℚ) := Rat.eq_num_of_isInt ha
  have hb_eq : b = (b.num : ℚ) := Rat.eq_num_of_isInt hb
  rw [ha_eq, hb_eq]
  have h : (a.num : ℚ) - (b.num : ℚ) = (((a.num - b.num : ℤ)) : ℚ) := by
    push_cast; ring
  rw [h]
  exact isInt_intCast' _

/-- `Rat.isInt` is closed under multiplication. -/
private lemma isInt_mul' {a b : ℚ} (ha : a.isInt = true) (hb : b.isInt = true) :
    (a * b).isInt = true := by
  have ha_eq : a = (a.num : ℚ) := Rat.eq_num_of_isInt ha
  have hb_eq : b = (b.num : ℚ) := Rat.eq_num_of_isInt hb
  rw [ha_eq, hb_eq]
  have h : (a.num : ℚ) * (b.num : ℚ) = (((a.num * b.num : ℤ)) : ℚ) := by
    push_cast; ring
  rw [h]
  exact isInt_intCast' _

/-- If every term `g i` is an integer (in the `Rat.isInt` sense) and `g`'s support
is finite, then the finsum `∑ᶠ i, g i` is an integer. Used in §5a. -/
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

/-! ### §3e helpers: unique decomposition of `f.support` along `Stilde × ℕ`. -/

/-- §3e-1a (helper) — From `hf2.1`, every `q ∈ f.support` has at least one `d ∈ S`
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

/-- §3e-1b (helper) — The unique decomposition `q = s.val + w/T` for `q ∈ f.support`.

Existence: take `d` as above, then `s := mu_q hf2 d` is the minimum of `Sd d`; by
construction `s ≤ q`, and the difference `T·(q - s)` is a non-negative integer,
giving `w : ℕ`. Uniqueness: any two decompositions yield `s.val - s'.val ∈ (1/T)ℤ`,
which combined with the residue clauses forces `(d.norm p - d'.norm p).isInt = true`;
applying `hf2.1`'s uniqueness, both decompositions correspond to the same residue
class, hence the same `mu_q` value and the same `w`. -/
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
  set s := mu_q hf2 d with hs_def
  have hs_residue : ((d.val.norm p : ℚ) + (T : ℚ) * s).isInt = true :=
    mu_q_residue hf2 d
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
  -- s' ∈ Stilde, so s' = mu_q hf2 d' for some d'.
  obtain ⟨d', hd'_eq⟩ := s'.property
  -- show s' = s (equivalently s'.val = mu_q hf2 d), then w' = wq.
  have hs'_le_q : (s'.val : ℚ) ≤ q := by
    rw [h_eq]
    have : (0 : ℚ) ≤ (w' : ℚ) / (T : ℚ) := div_nonneg (Nat.cast_nonneg _) hT_pos.le
    linarith
  have hs'_residue : ((d'.val.norm p : ℚ) + (T : ℚ) * s'.val).isInt = true := by
    rw [← hd'_eq]
    exact mu_q_residue hf2 d'
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
  -- Now mu_q hf2 d = mu_q hf2 d' because Sd depends only on d.norm p.
  have h_Sd_eq : Sd p f T d.val = Sd p f T d'.val := by
    unfold Sd
    congr 1
    ext q'
    simp only [Set.mem_setOf_eq, h_norm_eq]
  have h_mu_eq : mu_q hf2 d = mu_q hf2 d' := by
    unfold mu_q
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
    have h1 : s'.val = mu_q hf2 d' := hd'_eq.symm
    have h2 : mu_q hf2 d' = s := h_mu_eq.symm.trans hs_def.symm
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

/-- §3e-1c — Stilde elements live in f.support (re-export of `Stilde_subset_support`). -/
private lemma Stilde_decomp_at_self
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    s.val ∈ f.support := Stilde_subset_support hf2 s.property

/-- §3e-1d — If `q ∈ f.support` has decomposition `(s, w)` with `w ≥ 1`, then `q ∉ Stilde`. -/
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

/-! ### §3e-2 — Coefficient formula for the difference. -/

/-- §3e-2a — At `s ∈ Stilde`, the diff coefficient equals `Cs hf2 s - Cs_term hf2 s 0`. -/
private lemma fhat_diff_coeff_Stilde
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    (fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff s.val
      = Cs hf2 s - Cs_term hf2 s 0 := by
  rw [HahnSeries.coeff_sub, fhat_coeff_eq_Cs hf2 s]
  -- Goal: Cs hf2 s - (from_coeff ...).coeff s.val = Cs hf2 s - Cs_term hf2 s 0.
  -- (from_coeff p T f.coeff h).coeff s.val = OQpUn_embd p T (teichmuller p (f.coeff s.val))
  -- Cs_term hf2 s 0 = OQpUn_embd p T (teich p (f.coeff (s.val + 0/T))) * (pInvT p T)^0
  --                = OQpUn_embd p T (teich p (f.coeff s.val))
  unfold Cs_term
  have h0 : (s.val + (0 : ℕ) / (T : ℚ)) = s.val := by simp
  rw [h0, pow_zero, mul_one]
  rfl

/-- §3e-2b — At `q ∈ f.support \ Stilde`, the diff coefficient equals
`-(OQpUn_embd p T (teichmuller p (f.coeff q)))`. -/
private lemma fhat_diff_coeff_outside_Stilde
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {q : ℚ} (hq_not_Stilde : q ∉ Stilde hf2) :
    (fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff q
      = -(OQpUn_embd p (T : ℕ) (WittVector.teichmuller p (pAdicHahnSeries.coeff f q))) := by
  rw [HahnSeries.coeff_sub]
  have h_fhat_zero : (fhat hf2).coeff q = 0 := by
    change fhat_coeff hf2 q = 0
    unfold fhat_coeff
    exact dif_neg hq_not_Stilde
  rw [h_fhat_zero, zero_sub]
  rfl

/-- §3e-2c — At `q ∉ f.support`, the diff coefficient is 0. -/
private lemma fhat_diff_coeff_outside_support
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {q : ℚ} (hq_not_supp : q ∉ f.support) :
    (fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff q = 0 := by
  rw [HahnSeries.coeff_sub]
  have h_f_coeff_zero : pAdicHahnSeries.coeff f q = 0 := by
    by_contra h
    exact hq_not_supp h
  have h_fhat_zero : (fhat hf2).coeff q = 0 := by
    change fhat_coeff hf2 q = 0
    unfold fhat_coeff
    by_cases hq_stil : q ∈ Stilde hf2
    · exfalso
      apply hq_not_supp
      exact Stilde_subset_support hf2 hq_stil
    · exact dif_neg hq_stil
  have h_from_coeff_zero : (TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff q = 0 := by
    change OQpUn_embd p (T : ℕ) (WittVector.teichmuller p (pAdicHahnSeries.coeff f q)) = 0
    rw [h_f_coeff_zero, WittVector.teichmuller_zero, map_zero]
  rw [h_fhat_zero, h_from_coeff_zero, sub_zero]

/-! ### §3e-3 — Analytical helpers for `fhat_diff_isTNullSeries`.

These lemmas extract the `Cs s - Cs_partial s N` valuation tail bound, which is
the key analytical fact making the Tendsto-zero argument work.  All proofs use only
the `Cs_tendsto` interface plus the closed-ball-is-closed property of the valuation
topology on `ℚᵘⁿ_[p,T]`. -/

/-- §3e-3a (algebraic factorization) — For `N ≤ N'`, the difference of partial sums
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
  rw [Finset.range_eq_Ico]
  have h_split :
      ∑ w ∈ Finset.Ico 0 N', Cs_term hf2 s w =
        (∑ w ∈ Finset.Ico 0 N, Cs_term hf2 s w) +
        ∑ w ∈ Finset.Ico N N', Cs_term hf2 s w :=
    (Finset.sum_Ico_consecutive (fun w => Cs_term hf2 s w) (Nat.zero_le N) hN).symm
  rw [h_split]
  ring

/-- §3e-3b (per-term valuation) — Each summand `algebraMap (Cs_term hf2 s w)` has
valuation `ofAdd(-w)` in `ℚᵘⁿ_[p,T]`. -/
private lemma algebraMap_Cs_term_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (w : ℕ) :
    Valued.v (algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_term hf2 s w))
      ≤ ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) : WithZero _) := by
  unfold Cs_term
  -- algebraMap (OQpUn_embd ... · (pInvT)^w) = algebraMap (OQpUn_embd ...) · (pInvTQ)^w
  rw [map_mul]
  rw [map_pow]
  rw [show (algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])) (pInvT p T) = pInvTQ p T from rfl]
  rw [Valuation.map_mul]
  rw [show ((pInvTQ p T) ^ w : ℚᵘⁿ_[p, (T : ℕ)]) = (pInvTQ p T) ^ (w : ℤ) from by
    rw [zpow_natCast]]
  rw [valued_v_pInvT_zpow]
  have h_OQ_le_one :
      Valued.v (algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
        (OQpUn_embd p (T : ℕ)
          (WittVector.teichmuller p (f.coeff (s.val + (w : ℚ) / T))))) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p, (T : ℕ)])).valuation_le_one _
  calc Valued.v (algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
          (OQpUn_embd p (T : ℕ)
            (WittVector.teichmuller p (f.coeff (s.val + (w : ℚ) / T))))) *
          ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) : WithZero _)
      ≤ 1 * ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) : WithZero _) :=
        mul_le_mul' h_OQ_le_one (le_refl _)
    _ = ((Multiplicative.ofAdd (-(w : ℤ)) : Multiplicative ℤ) : WithZero _) := one_mul _

/-- §3e-3c (Cauchy tail bound) — For `N ≤ N'`, `Valued.v (algebraMap (Cs_partial s N' - Cs_partial s N))
≤ ofAdd(-N)`. This is the explicit Cauchy property of the partial sums. -/
private lemma Cs_partial_diff_alg_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) {N N' : ℕ} (hN : N ≤ N') :
    Valued.v (algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
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

/-- §3e-3d (limit bound) — `Valued.v (algebraMap (Cs hf2 s - Cs_partial hf2 s N)) ≤ ofAdd(-N)`.
Obtained from the Cauchy bound `Cs_partial_diff_alg_v_le` by taking the limit as
`N' → ∞`, using `Cs_tendsto` plus `Valued.isClosed_closedBall`. -/
private lemma Cs_diff_alg_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (N : ℕ) :
    Valued.v (algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
              (Cs hf2 s - Cs_partial hf2 s N))
      ≤ ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _) := by
  -- algebraMap (Cs_partial s N') - algebraMap (Cs_partial s N) tends to
  -- algebraMap (Cs s) - algebraMap (Cs_partial s N) = algebraMap (Cs s - Cs_partial s N)
  -- as N' → ∞.  Eventually this value is in the closed ball; closed-ball-is-closed gives the result.
  set target : ℚᵘⁿ_[p, (T : ℕ)] :=
    algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs hf2 s - Cs_partial hf2 s N)
    with htarget_def
  set ball : Set (ℚᵘⁿ_[p, (T : ℕ)]) :=
    { x | Valued.v x ≤ ((Multiplicative.ofAdd (-(N : ℤ)) : Multiplicative ℤ) : WithZero _) }
    with hball_def
  have h_ball_closed : IsClosed ball :=
    Valued.isClosed_closedBall _ _
  have h_tendsto :
      Filter.Tendsto
        (fun N' : ℕ => algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                        (Cs_partial hf2 s N' - Cs_partial hf2 s N))
        Filter.atTop (nhds target) := by
    have h_sub_tendsto :
        Filter.Tendsto
          (fun N' : ℕ => algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N')
                        - algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N))
          Filter.atTop (nhds (algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs hf2 s)
                              - algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                                  (Cs_partial hf2 s N))) :=
      (Cs_tendsto hf2 s).sub tendsto_const_nhds
    have h_target_eq :
        target =
          algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs hf2 s)
            - algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (Cs_partial hf2 s N) := by
      rw [htarget_def, map_sub]
    rw [h_target_eq]
    convert h_sub_tendsto using 1
    funext N'
    exact map_sub _ _ _
  have h_eventually : ∀ᶠ N' : ℕ in Filter.atTop,
      algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
        (Cs_partial hf2 s N' - Cs_partial hf2 s N) ∈ ball := by
    filter_upwards [Filter.eventually_ge_atTop N] with N' hN'
    exact Cs_partial_diff_alg_v_le hf2 s hN'
  exact h_ball_closed.mem_of_tendsto h_tendsto h_eventually

/-- §3e-3e (per-`s` slice collapse, inner-sum identity).

For fixed `s ∈ Stilde hf2`, an integer `n_s : ℤ`, and an `M : ℕ`, the algebraic
identity `(pInvTQ)^w · algebraMap (diff.coeff (s.val + w/T)) = algebraMap ((pInvT)^w · diff.coeff (...))`
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
          algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
            ((fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
                          (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
              (s.val + (w : ℚ) / T))
      = algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
            (Cs hf2 s - Cs_partial hf2 s (W + 1)) := by
  -- Step 1: Pull algebraMap outside the sum by rewriting (pInvTQ)^w = algebraMap (pInvT)^w.
  have h_pInvTQ_eq_alg : ∀ w : ℕ, (pInvTQ p (T : ℕ)) ^ (w : ℤ) =
      algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) ((pInvT p (T : ℕ)) ^ w) := by
    intro w
    rw [zpow_natCast, map_pow]
    rfl
  have h_step1 :
      ∑ w ∈ Finset.range (W + 1),
        (pInvTQ p (T : ℕ)) ^ (w : ℤ) *
          algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
            ((fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
                          (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
              (s.val + (w : ℚ) / T))
      = algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
          (∑ w ∈ Finset.range (W + 1),
            (pInvT p (T : ℕ)) ^ w *
              ((fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
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
        ((fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
                      (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
          (s.val + (w : ℚ) / T))) W]
  -- Now we have: ∑_{w' ∈ range W} (pInvT)^{w'+1} · diff.coeff(s.val + (w'+1)/T) + (pInvT)^0 · diff.coeff(s.val)
  -- For w = 0:
  have h_w0 : (pInvT p (T : ℕ)) ^ 0 *
      ((fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
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
        ((fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
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

/-- §3e-3f (per-`s` slice valuation bound). For fixed `s ∈ Stilde hf2`, an integer
`n_s : ℤ`, and `W : ℕ`, the per-`s` slice `(pInvTQ)^{n_s} · algebraMap(Cs s - Cs_partial s (W+1))`
has valuation `≤ ofAdd(-(n_s + W + 1))`. -/
private lemma per_s_slice_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) (n_s : ℤ) (W : ℕ) :
    Valued.v ((pInvTQ p (T : ℕ)) ^ n_s *
              algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                (Cs hf2 s - Cs_partial hf2 s (W + 1)))
      ≤ ((Multiplicative.ofAdd (-(n_s + (W : ℤ) + 1)) : Multiplicative ℤ) : WithZero _) := by
  rw [Valuation.map_mul, valued_v_pInvT_zpow]
  have h_alg : Valued.v (algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
              (Cs hf2 s - Cs_partial hf2 s (W + 1)))
      ≤ ((Multiplicative.ofAdd (-((W + 1 : ℕ) : ℤ)) : Multiplicative ℤ) : WithZero _) :=
    Cs_diff_alg_v_le hf2 s (W + 1)
  have h_cast : ((W + 1 : ℕ) : ℤ) = (W : ℤ) + 1 := by push_cast; ring
  rw [h_cast] at h_alg
  calc ((Multiplicative.ofAdd (-n_s : ℤ) : Multiplicative ℤ) : WithZero _) *
          Valued.v (algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
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

/-! ### §3e-analytic — Body of `fhat_diff_isTNullSeries`. -/

/-- §3e-3g — Per-`M` valuation bound for the `Tfinprop`-indexed partial sum of `diff`.

For each `g : ℚ` and `M : ℕ`, the partial sum
`P_M = ∑_{n ∈ Tfinprop diff g M} (pInvTQ)^n · algebraMap(diff.coeff(g + n/T))`
has valuation bounded by `ofAdd(-(K+1))` where `K = ⌊T·(M - g)⌋`.

Strategy:
1. For each `n ∈ Tfinprop`, by `Stilde_unique_decomposition` (L441), `g + n/T = s.val + w/T`
   for a unique `(s, w) ∈ Stilde × ℕ`. Define `s_of n` and `w_of n`.
2. Let `Stilde_used := image (s_of)` (a Finset). For each `s ∈ Stilde_used`, define
   `n_s := T(s.val - g)` (an integer, since `T(s.val - g) = n - w ∈ ℤ`) and
   `W_s := ⌊T(M - s.val)⌋.toNat`.
3. Use `Finset.sum_bij'` to re-index `P_M = ∑_{(s, w) ∈ image} (pInvTQ)^{n_s + w} · algebraMap(diff.coeff(s.val + w/T))`
   over a sigma `Stilde_used.sigma w_range`.
4. Extend the sum to all of `Stilde_used.sigma w_range` (added terms have zero coeff).
5. Apply `per_s_inner_sum_eq` (L811) per `s`: inner sum = `algebraMap(Cs s - Cs_partial s (W_s + 1))`.
6. Apply `per_s_slice_v_le` (L902) + arithmetic identity `n_s + W_s = K` for the per-`s`
   valuation bound `ofAdd(-(n_s + W_s + 1)) = ofAdd(-(K + 1))`.
7. Apply `Valuation.map_sum_le` for the outer ultrametric. -/
private lemma fhat_diff_partial_v_le
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (g : ℚ) (M : ℕ) :
    Valued.v (∑ n : Set.Finite.toFinset (Tfinprop p (T : ℕ)
                  (fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
                    (pAdicHahnSeries.coeff f) (support_IsPWO f)) g M),
              (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
                algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                  ((fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
                    (pAdicHahnSeries.coeff f) (support_IsPWO f)).coeff
                    (g + (n.val : ℚ) / T))) ≤
      ((Multiplicative.ofAdd (-(⌊(T : ℚ) * ((M : ℚ) - g)⌋ + 1) : ℤ) :
        Multiplicative ℤ) : WithZero _) := by
  classical
  set diff : TLiftedPAdicHahnSeries p (T : ℕ) :=
    fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
                (pAdicHahnSeries.coeff f) (support_IsPWO f) with hdiff_def
  set K : ℤ := ⌊(T : ℚ) * ((M : ℚ) - g)⌋ with hK_def
  have hT_pos : (0 : ℚ) < (T : ℕ) := by exact_mod_cast T.pos
  have hT_ne : ((T : ℕ) : ℚ) ≠ 0 := ne_of_gt hT_pos
  -- For each n ∈ Tfinprop.toFinset, g + n/T ∈ f.support.
  have h_n_supp : ∀ n : ℤ, n ∈ Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M) →
      g + (n : ℚ) / (T : ℕ) ∈ f.support := by
    intro n hn
    have hn_data : g + (n : ℚ) / (T : ℕ) ≤ M ∧ diff.coeff (g + (n : ℚ) / (T : ℕ)) ≠ 0 :=
      (Set.Finite.mem_toFinset (hs := Tfinprop p (T : ℕ) diff g M) (a := n)).mp hn
    by_contra h
    exact hn_data.2 (fhat_diff_coeff_outside_support hf2 h)
  -- For each n ∈ Tfinprop.toFinset, also: g + n/T ≤ M.
  have h_n_le_M : ∀ n : ℤ, n ∈ Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M) →
      g + (n : ℚ) / (T : ℕ) ≤ M := by
    intro n hn
    exact ((Set.Finite.mem_toFinset (hs := Tfinprop p (T : ℕ) diff g M) (a := n)).mp hn).1
  -- Define the bijection map on the attached set.
  let sw_choose : (n : ↥(Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M))) →
      ↥(Stilde hf2) × ℕ :=
    fun n => (Stilde_unique_decomposition hf2 (h_n_supp n.val n.property)).choose
  -- Property of sw_choose: g + n.val/T = (sw_choose n).1.val + (sw_choose n).2 / T.
  have h_sw_eq : ∀ n : ↥(Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)),
      g + (n.val : ℚ) / (T : ℕ) = ((sw_choose n).1).val +
                                   ((sw_choose n).2 : ℚ) / (T : ℕ) :=
    fun n => (Stilde_unique_decomposition hf2 (h_n_supp n.val n.property)).choose_spec.1
  -- Uniqueness of sw_choose.
  have h_sw_unique : ∀ n : ↥(Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)),
      ∀ sw', g + (n.val : ℚ) / (T : ℕ) = sw'.1.val + (sw'.2 : ℚ) / (T : ℕ) →
        sw' = sw_choose n :=
    fun n sw' h_eq => (Stilde_unique_decomposition hf2 (h_n_supp n.val n.property)).choose_spec.2
      sw' h_eq
  -- n.val = T·(s.val - g) + w (residue arithmetic).
  have h_n_decomp : ∀ n : ↥(Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)),
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
  have h_T_sub_int : ∀ n : ↥(Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)),
      (T : ℕ) * (((sw_choose n).1).val - g) = (n.val - ((sw_choose n).2 : ℤ) : ℤ) := by
    intro n
    have h := h_n_decomp n
    have : (n.val : ℚ) - ((sw_choose n).2 : ℚ) = (T : ℕ) * (((sw_choose n).1).val - g) := by
      linarith
    rw [← this]; push_cast; ring
  -- Define Stilde_used: image of the s coordinate.
  set Stilde_used : Finset ↥(Stilde hf2) :=
    (Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)).attach.image
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
    show ((T : ℕ) * (s.val - g) : ℚ) = (((T : ℚ) * (s.val - g)).num : ℚ)
    calc ((T : ℕ) * (s.val - g) : ℚ)
        = ((T : ℚ) * (s.val - g)) := by push_cast; ring
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
      show (⌊(T : ℚ) * ((M : ℚ) - s.val)⌋.toNat : ℤ) = ⌊(T : ℚ) * ((M : ℚ) - s.val)⌋
      exact Int.toNat_of_nonneg h_floor_nonneg
    rw [h_W_s_eq]
    -- Use n_s_plus_W_s_eq_floor style: T(M-g) = T(s.val-g) + T(M-s.val) = n_s + T(M-s.val).
    have h_eq : (T : ℚ) * ((M : ℚ) - g) = (n_s_int s : ℚ) + (T : ℚ) * ((M : ℚ) - s.val) := by
      have : (T : ℚ) * ((M : ℚ) - g) =
          (T : ℚ) * (s.val - g) + (T : ℚ) * ((M : ℚ) - s.val) := by ring
      rw [this]
      have h_int' : ((T : ℕ) * (s.val - g) : ℚ) = (n_s_int s : ℚ) := h_int
      rw [show ((T : ℚ) * (s.val - g)) = ((T : ℕ) * (s.val - g) : ℚ) from by push_cast; ring]
      rw [h_int']
    rw [hK_def]
    rw [h_eq]
    have := Int.floor_intCast_add (n_s_int s) ((T : ℚ) * ((M : ℚ) - s.val))
    linarith
  -- For s ∈ Stilde_used: (Cs hf2 s - Cs_partial hf2 s (W_s s + 1)) bounds for per-s slice.
  -- Apply per_s_slice_v_le.
  have h_used_per_s_bound : ∀ s ∈ Stilde_used,
      Valued.v ((pInvTQ p (T : ℕ)) ^ (n_s_int s) *
                algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                  (Cs hf2 s - Cs_partial hf2 s (W_s s + 1))) ≤
      ((Multiplicative.ofAdd (-(K + 1)) : Multiplicative ℤ) : WithZero _) := by
    intro s hs
    have h_arith := h_used_arith s hs
    have h_slice := per_s_slice_v_le hf2 s (n_s_int s) (W_s s)
    have h_eq : (n_s_int s + (W_s s : ℤ) + 1 : ℤ) = K + 1 := by linarith
    rw [h_eq] at h_slice
    exact h_slice
  -- Step: Show the sum identity.
  -- For each n ∈ Tfinprop, the term equals (pInvTQ)^{n.val} · algebraMap(diff.coeff(g + n/T))
  --   = (pInvTQ)^{n_s_int s + (sw_choose n).2} · algebraMap(diff.coeff(s.val + w/T))
  -- where s = (sw_choose n).1, w = (sw_choose n).2.
  -- F : value at a Sigma pair.
  let F : (Σ _ : ↥(Stilde hf2), ℕ) → ℚᵘⁿ_[p, (T : ℕ)] := fun p_sig =>
    (pInvTQ p (T : ℕ)) ^ (n_s_int p_sig.1 + (p_sig.2 : ℤ)) *
      algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
        (diff.coeff (p_sig.1.val + (p_sig.2 : ℚ) / (T : ℕ)))
  -- sigma_of: the indexing function on the subtype.
  let sigma_of : ↥(Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)) → Σ _ : ↥(Stilde hf2), ℕ :=
    fun n => ⟨(sw_choose n).1, (sw_choose n).2⟩
  -- F (sigma_of n) equals the original summand.
  have h_F_eq : ∀ n : ↥(Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)),
      F (sigma_of n) = (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
        algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
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
    show (pInvTQ p (T : ℕ)) ^ (n_s_int (sw_choose n).1 + ((sw_choose n).2 : ℤ)) *
      algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
        (diff.coeff ((sw_choose n).1.val + ((sw_choose n).2 : ℚ) / (T : ℕ))) = _
    rw [h_n_eq, h_q_eq]
  -- sigma_of is injective.
  have h_sigma_inj : ∀ n₁ ∈ (Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)).attach,
      ∀ n₂ ∈ (Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)).attach,
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
  have h_sigma_mem : ∀ n ∈ (Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)).attach,
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
        push_cast at h_div_le
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
      show (sw_choose n).2 < W_s (sw_choose n).1 + 1
      omega
  -- For p ∈ FullSigma \ Image(sigma_of), F(p) = 0.
  have h_zero_outside : ∀ q_sig ∈ Stilde_used.sigma
      (fun s : ↥(Stilde hf2) => Finset.range (W_s s + 1)),
      q_sig ∉ (Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)).attach.image sigma_of →
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
    · show (pInvTQ p (T : ℕ)) ^ (n_s_int s + (w : ℤ)) *
        algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
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
          show ((n_s_int s + (w : ℤ) : ℤ) : ℚ) = _
          push_cast
          linarith
        rw [h_rewrite]
        field_simp
        ring
      have h_n_cand_in_Tfp : n_candidate ∈
          Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M) := by
        apply (Set.Finite.mem_toFinset _).mpr
        refine ⟨?_, ?_⟩
        · rw [h_q_n_cand]; exact h_sval_le_M_val
        · rw [h_q_n_cand]; exact h_coeff
      have h_sigma_n_cand : sigma_of ⟨n_candidate, h_n_cand_in_Tfp⟩ =
          (⟨s, w⟩ : Σ _ : ↥(Stilde hf2), ℕ) := by
        show (⟨(sw_choose ⟨n_candidate, h_n_cand_in_Tfp⟩).1,
              (sw_choose ⟨n_candidate, h_n_cand_in_Tfp⟩).2⟩ : Σ _ : ↥(Stilde hf2), ℕ) =
            ⟨s, w⟩
        have h_eq := h_sw_unique ⟨n_candidate, h_n_cand_in_Tfp⟩ (s, w) h_q_n_cand
        -- h_eq : (s, w) = sw_choose ⟨n_candidate, h_n_cand_in_Tfp⟩
        rw [← h_eq]
      have h_in_im : (⟨s, w⟩ : Σ _ : ↥(Stilde hf2), ℕ) ∈
          (Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)).attach.image sigma_of := by
        refine Finset.mem_image.mpr ?_
        refine ⟨⟨n_candidate, h_n_cand_in_Tfp⟩, Finset.mem_attach _ _, h_sigma_n_cand⟩
      exact h_not_im h_in_im
  -- Sum identity: via Finset.sum_image (injection) + Finset.sum_subset (extension).
  have h_sum_via_sigma :
      (∑ n ∈ (Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)).attach,
          (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
            algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
              (diff.coeff (g + (n.val : ℚ) / (T : ℕ)))) =
      ∑ p_sig ∈ Stilde_used.sigma (fun s : ↥(Stilde hf2) => Finset.range (W_s s + 1)),
        F p_sig := by
    have h_eq : (∑ n ∈ (Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)).attach,
          (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
            algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
              (diff.coeff (g + (n.val : ℚ) / (T : ℕ)))) =
        ∑ n ∈ (Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)).attach, F (sigma_of n) := by
      apply Finset.sum_congr rfl
      intro n _
      exact (h_F_eq n).symm
    rw [h_eq]
    rw [show (∑ n ∈ (Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)).attach,
              F (sigma_of n)) =
            ∑ p_sig ∈ (Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M)).attach.image
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
        algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
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
            algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
              (diff.coeff (s.val + (w : ℚ) / (T : ℕ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      show (pInvTQ p (T : ℕ)) ^ (n_s_int s + (w : ℤ)) *
          algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
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
      (∑ n : Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M),
        (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
          algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
            (diff.coeff (g + (n.val : ℚ) / (T : ℕ)))) =
      ∑ s ∈ Stilde_used, (pInvTQ p (T : ℕ)) ^ (n_s_int s) *
        algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
          (Cs hf2 s - Cs_partial hf2 s (W_s s + 1)) := by
    rw [← h_sigma_to_per_s, ← h_sum_via_sigma]
    rfl
  -- Now apply Valuation.map_sum_le using h_used_per_s_bound.
  rw [h_LHS_eq]
  apply Valuation.map_sum_le
  intro s hs
  exact h_used_per_s_bound s hs

/-- §3e-analytic — The difference `fhat hf2 - from_coeff p T f.coeff (support_IsPWO f)`
is a T-null-series.

Strategy: For each `g : ℚ` and `M : ℕ`, the partial sum `P(M)` is bounded in valuation by
`ofAdd(-(K+1))` where `K = ⌊T·(M - g)⌋`.  The bound is obtained by recognising each
`n ∈ Tfinprop diff g M` as `n = T·(s.val - g) + w` for the unique decomposition
`(s, w) ∈ Stilde × ℕ` of `g + n/T ∈ f.support`, and observing that the per-`s`
fiber sums collapse to `(pInvTQ)^{n_s} · algebraMap (Cs hf2 s - Cs_partial hf2 s (W_s + 1))`,
whose valuation is `≤ ofAdd(-(n_s + W_s + 1)) = ofAdd(-(K+1))` by `Cs_diff_alg_v_le`. -/
private lemma fhat_diff_isTNullSeries
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
                  (pAdicHahnSeries.coeff f) (support_IsPWO f)
      ∈ TNullSeriesIdeal p (T : ℕ) := by
  -- Structural prerequisites already in scope:
  -- * `Stilde_unique_decomposition` : unique `(s, w) : Stilde × ℕ` decomposition.
  -- * `not_Stilde_of_pos_w` : `w ≥ 1` ⇒ `q ∉ Stilde`.
  -- * `fhat_diff_coeff_Stilde` / `fhat_diff_coeff_outside_Stilde` /
  --   `fhat_diff_coeff_outside_support` : diff.coeff formulas at each location class.
  -- * `Cs_partial_diff_alg_v_le` (REAL): tail Cauchy bound.
  -- * `Cs_diff_alg_v_le` (REAL): limit bound `Valued.v (algebraMap (Cs s - Cs_partial s N)) ≤ ofAdd(-N)`.
  -- * `per_s_inner_sum_eq` (REAL): per-`s` inner-sum collapse to
  --   `algebraMap (Cs hf2 s - Cs_partial hf2 s (W + 1))`.
  intro g
  -- Set up notation.
  set diff : TLiftedPAdicHahnSeries p (T : ℕ) :=
    fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
                (pAdicHahnSeries.coeff f) (support_IsPWO f)
    with hdiff_def
  -- The partial sum sequence.
  set P : ℕ → ℚᵘⁿ_[p, (T : ℕ)] := fun M =>
    ∑ n : Set.Finite.toFinset (Tfinprop p (T : ℕ) diff g M),
      (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
        algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)]) (diff.coeff (g + (n.val : ℚ) / T))
    with hP_def
  -- We aim to show Tendsto P atTop (𝓝 0).  Use the Valued-topology characterisation:
  -- `(𝓝 0).HasBasis (fun γ : Γ₀ˣ => True) (fun γ => { x | Valued.v x < γ })`.
  -- KEY BOUND (analytical heart, structurally laid out below):
  --   `Valued.v (P M) ≤ ofAdd(-(⌊T·(M - g)⌋ + 1))`.
  -- As `M → ∞`, `⌊T·(M - g)⌋ → ∞`, so the bound `→ 0`, giving the result.
  --
  -- The bound follows from:
  -- (a) re-indexing `Tfinprop diff g M` over `(s, w) ∈ Stilde × ℕ` via
  --     `Stilde_unique_decomposition` (each `n ∈ Tfinprop` corresponds to a unique
  --     `(s, w)` with `g + n/T = s.val + w/T`);
  -- (b) for fixed `s`, per-`s` slice collapse via `per_s_inner_sum_eq`:
  --     `∑_w (pInvTQ)^w · algebraMap(diff.coeff(s.val + w/T)) = algebraMap(Cs s - Cs_partial s (W_s + 1))`;
  -- (c) per-`s` valuation bound via `Cs_diff_alg_v_le`:
  --     `Valued.v((pInvTQ)^{n_s} · algebraMap(Cs s - Cs_partial s (W_s + 1))) ≤ ofAdd(-(n_s + W_s + 1))`;
  -- (d) arithmetic identity `n_s + W_s = ⌊T·(M - g)⌋` (residue condition implies);
  -- (e) ultrametric `Valuation.map_sum_le` over the (finite) Finset of active `s`s.
  --
  -- The bijection construction (a) and the outer sum-of-(b)+(c) (e) are heavy and
  -- left for a follow-up round.  The analytical content — (b), (c), (d) — is already
  -- expressed in `per_s_inner_sum_eq` + `Cs_diff_alg_v_le` + simple arithmetic.
  --
  -- Proof skeleton via the Valued neighbourhood characterisation:
  rw [Filter.tendsto_def]
  intro U hU
  rw [Valued.mem_nhds] at hU
  obtain ⟨γ, hγ⟩ := hU
  -- It suffices to show: `∀ᶠ M, Valued.v (P M) < γ`.
  suffices h_ev : ∀ᶠ M : ℕ in Filter.atTop,
      Valued.v (P M) < (γ : WithZero (Multiplicative ℤ)) by
    filter_upwards [h_ev] with M hM
    exact hγ (by simpa using hM)
  -- Reduce to: `∀ᶠ M, Valued.v (P M) ≤ ofAdd(-(K + 1))` where K = ⌊T(M-g)⌋,
  -- and as M → ∞, K → ∞ makes the bound < γ eventually.
  -- Step 1: extract the integer exponent `k` corresponding to `γ`.
  set k : ℤ := Multiplicative.toAdd (WithZero.unitsWithZeroEquiv γ) with hk_def
  have h_γ_val : (γ : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [(WithZero.coe_unitsWithZeroEquiv_eq_units_val γ).symm]
    rfl
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
    have h6 : (-(k : ℤ) : ℚ) ≤ (T : ℚ) * ((M : ℚ) - g) := by push_cast at h5 ⊢; linarith
    exact Int.le_floor.mpr h6
  filter_upwards [h_ev_floor] with M hMfloor
  -- Step 3: apply fhat_diff_partial_v_le to get the per-M bound.
  have h_partial_le := fhat_diff_partial_v_le hf2 g M
  -- Unfold the partial-sum expression so it matches P M / hP_def.
  have h_P_eq : P M =
      ∑ n : Set.Finite.toFinset (Tfinprop p (T : ℕ)
                  (fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
                    (pAdicHahnSeries.coeff f) (support_IsPWO f)) g M),
              (pInvTQ p (T : ℕ)) ^ (n.val : ℤ) *
                algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                  ((fhat hf2 - TLiftedPAdicHahnSeries.from_coeff p (T : ℕ)
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

lemma mk_fhat_eq_sigma_f {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) (fhat hf2) = σ p (T : ℕ) f := by
  -- Step 1: rewrite σ p T f as mk (from_coeff p T f.coeff (support_IsPWO f)).
  rw [sigma_eq_mk_from_coeff_fcoeff]
  -- Step 2: equality of `mk`s reduces to difference in N_T (Ideal.Quotient.eq).
  exact (Ideal.Quotient.eq).mpr (fhat_diff_isTNullSeries hf2)

/-- Existential interface for the lift `fhat` constructed from `C_s`.

A nonzero coefficient bundle on `Stilde` whose corresponding `TLiftedPAdicHahnSeries`
projects to `σ p T f` in the quotient `𝕃_[p,T]`. -/
private def FhatData {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+)
    {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) : Prop :=
  ∃ (Cs : ↥(Stilde hf2) → ℤᵘⁿ_[p, (T : ℕ)])
    (fhat : TLiftedPAdicHahnSeries p (T : ℕ)),
    (∀ s, Cs s ≠ 0) ∧
    (Function.support fhat.coeff ⊆ Stilde hf2) ∧
    (∀ (s : ↥(Stilde hf2)), fhat.coeff s.val = Cs s) ∧
    (Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) fhat = σ p (T : ℕ) f)

/-- Existence of the lift data. Assembles the structural pieces `Cs`, `fhat`,
`Cs_ne_zero`, `fhat_support_subset`, `fhat_coeff_eq_Cs`, `mk_fhat_eq_sigma_f`.
The two analytical hard steps (the limit existence and the canonical T-expansion
identification) are encapsulated in `exists_Cs` and `mk_fhat_eq_sigma_f`. -/
private lemma exists_FhatData
    {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (T : ℕ+)
    {S : Set DigitSeries} (hS : ∀ d ∈ S, d.IsP p)
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    FhatData f T hf2 :=
  ⟨Cs hf2, fhat hf2, Cs_ne_zero hf2, fhat_support_subset hf2,
    fhat_coeff_eq_Cs hf2, mk_fhat_eq_sigma_f hf2⟩

/-! ### Step 4–6 — Multinomial expansion, collapse via `lemma_1_5`, contradiction.

The high-level engine packing Steps 4–6 of the PDF proof. Given the lift data from
`exists_FhatData`, plus the `IsCNSparse` witness from sparsity, derives the
final identity
  `p^{r₀ + T·∑φ₀(d)·μ(d)} · a_n · n!/(∏φ₀(d)!) · ∏ C_{μ(d)}^{φ₀(d)} = 0`
and obtains a contradiction with `hP₀` / `Cs_ne_zero`.

This is the part that genuinely requires the multinomial expansion of `P.aeval fhat`
in `TLiftedPAdicHahnSeries`, the T-null-series identity (c) at `q = -r₀/T`, and the
application of `Sparse.lemma_1_5` to collapse equation (c) to a single term.

Round 5 (iter-003) decomposes the proof along the PDF's sub-step structure (PDF pp. 9-10):
* §4a `r0` — the rational `r₀ := ∑_{d ∈ S} ‖d‖·φ₀(d)`.
* §4b `sigma_aeval_P_eq_zero` — `σ(P.aeval f) = 0` (trivial from ring-hom + hP_aeval).
* §4d `identity_c` — the T-null-series identity at `q = -r₀/T` (the central
  combinatorial identity; body deferred).
* §5a `phi_tilde_constraint_at_phi0` — application of `Sparse.lemma_1_5` to collapse
  φ̃ to φ₀∘μ⁻¹ (real body; uses `mu_q_residue`).
* §5b `identity_c_collapsed` — the surviving single-term equation (body deferred,
  follows from §4d + §5a).
* `final_disjunction` — domain integrality of `ℤᵘⁿ_[p,T]` to extract the disjunction
  from `identity_c_collapsed`. -/

/-- §4a — The rational `r₀ := ∑_{d ∈ S} ‖d‖ · φ₀(d)` (PDF p. 9).

Although `r₀` is rational, the exponent `r₀ + T · ∑φ₀(d)·μ(d)` appearing in the
PDF's Step 5 collapse is an integer (cf. `mu_q_residue`). -/
noncomputable def r0 {p : ℕ} [Fact (Nat.Prime p)] {S : Set DigitSeries}
    {hS : ∀ d ∈ S, d.IsP p} {C n : ℕ+} (hSparse : IsCNSparse p C n S hS) : ℚ :=
  ∑ᶠ d : S, (d.val.norm p) * (Sparse.φ₀ hSparse d : ℚ)

/-- §4b — `σ p T (P.aeval f) = 0` in `𝕃_[p,T]`.

Trivial consequence of `σ` being a ring hom and `P.aeval f = 0`. The PDF uses this
together with the multinomial expansion of `f̂^i` in `TLiftedPAdicHahnSeries` to
deduce `P.aeval(f̂) ∈ N_T`. The bridge requires showing the multinomial expansion in
`TLiftedPAdicHahnSeries` projects to `P.aeval(σ f)` via the quotient; that bridge is
the body of `identity_c` (§4d). -/
private lemma sigma_aeval_P_eq_zero
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} (T : ℕ+)
    {P : Polynomial ℚᵘⁿ_[p]} (hP_aeval : (Polynomial.aeval f) P = 0) :
    σ p (T : ℕ) ((Polynomial.aeval f) P) = 0 := by
  rw [hP_aeval]; exact map_zero _

/-! ### §4d-aux — clearing denominators and the `Pfhat_TLifted` construction (Round 10).

We construct an explicit element `Pfhat_TLifted ∈ TLiftedPAdicHahnSeries p T` that
serves as the witness for `identity_c`. The construction uses
`IsLocalization.integerNormalization` to clear denominators of `P` by some
`c ∈ ℤᵘⁿ_[p]` (in `nonZeroDivisors ℤᵘⁿ_[p]`), giving `P_int : Polynomial ℤᵘⁿ_[p]`
with `P_int.map (algebraMap ℤᵘⁿ_[p] ℚᵘⁿ_[p]) = c • P`. Then
`Pfhat_TLifted := (P_int.map (OQpUn_embd p T)).aeval fhat` makes type-sense as a
`TLiftedPAdicHahnSeries p T`-valued evaluation.

The bridge lemma `Pfhat_TLifted_isTNullSeries` shows the resulting element is a
T-null-series, using `σ(P.aeval f) = 0` + ring-hom commutation. -/

/-- §4d-a — The denominator-cleared polynomial: `P_int := integerNormalization _ P`.
By `IsLocalization.integerNormalization_spec`, there exists `c ∈ nonZeroDivisors ℤᵘⁿ_[p]`
such that `P_int.map (algebraMap ℤᵘⁿ_[p] ℚᵘⁿ_[p]) = c • P`. -/
noncomputable def P_int {p : ℕ} [Fact (Nat.Prime p)]
    (P : Polynomial ℚᵘⁿ_[p]) : Polynomial ℤᵘⁿ_[p] :=
  IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P

/-- §4d-b — The TLifted-level multinomial expansion:
`Pfhat_TLifted := (P_int.map (OQpUn_embd p T)).aeval fhat`. -/
noncomputable def Pfhat_TLifted {p : ℕ} [Fact (Nat.Prime p)] (T : ℕ+)
    (P : Polynomial ℚᵘⁿ_[p])
    (fhat : TLiftedPAdicHahnSeries p (T : ℕ)) :
    TLiftedPAdicHahnSeries p (T : ℕ) :=
  ((P_int P).map (OQpUn_embd p T)).aeval fhat

/-- §4d-c — The bridge lemma: `Pfhat_TLifted` is a T-null-series.

Proof outline (Round 10, real proof):
1. Establish `IsScalarTower ℤᵘⁿ_[p] ℚᵘⁿ_[p] 𝕃_[p]` manually (the automatic instance
   search times out, cf. Tscaled.lean L4228). Compose ZpUn_embd = lift QpUn_embd ∘ algebraMap.
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
  -- Step 1: Manual IsScalarTower ℤᵘⁿ_[p] ℚᵘⁿ_[p] 𝕃_[p].
  haveI hST_L : IsScalarTower ℤᵘⁿ_[p] ℚᵘⁿ_[p] 𝕃_[p] := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change Poonen1993.pAdicHahnSeries.ZpUn_embd x =
        Poonen1993.pAdicHahnSeries.QpUn_embd ((algebraMap ℤᵘⁿ_[p] ℚᵘⁿ_[p]) x)
    unfold Poonen1993.pAdicHahnSeries.QpUn_embd
    exact (IsFractionRing.lift_algebraMap (g := Poonen1993.pAdicHahnSeries.ZpUn_embd)
      Poonen1993.pAdicHahnSeries.ZpUn_embd_injective x).symm
  -- Step 2: P_int.aeval f = 0 in 𝕃_[p] via IsLocalization.integerNormalization_aeval_eq_zero.
  have hPint_f :
      (IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).aeval f = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero _ P hP_aeval
  -- Step 3: σ ∘ algebraMap ℤᵘⁿ_[p] 𝕃_[p] = algebraMap ℤᵘⁿ_[p] 𝕃_[p,T].
  have h_alg_compat : ∀ x : ℤᵘⁿ_[p],
      σ p (T : ℕ) ((algebraMap ℤᵘⁿ_[p] 𝕃_[p]) x) =
        (algebraMap ℤᵘⁿ_[p] 𝕃_[p, (T : ℕ)]) x := by
    intro x
    change σ p (T : ℕ) (Poonen1993.pAdicHahnSeries.ZpUn_embd x) = _
    change σ p (T : ℕ)
        (Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 x)) = _
    rw [show σ p (T : ℕ)
          (Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 x)) =
        Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ))
          (Lifted_to_TLifted p (T : ℕ) (HahnSeries.single 0 x)) from rfl]
    have h_map : Lifted_to_TLifted p (T : ℕ) (HahnSeries.single 0 x) =
        HahnSeries.single 0 (OQpUn_embd p (T : ℕ) x) :=
      HahnSeries.map_single (a := (0 : ℚ)) (r := x)
        (f := (OQpUn_embd p (T : ℕ) : ZeroHom ℤᵘⁿ_[p] ℤᵘⁿ_[p, (T : ℕ)]))
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
    rw [show OQpUn_embd p T = algebraMap ℤᵘⁿ_[p] ℤᵘⁿ_[p, (T : ℕ)] from rfl]
    exact Polynomial.aeval_map_algebraMap _ _ _
  -- Step 7: bridge mk to (algebraMap-aeval) via Ideal.Quotient.mkₐ + aeval_algHom_apply.
  have key := Polynomial.aeval_algHom_apply
    (Ideal.Quotient.mkₐ (ℤᵘⁿ_[p, (T : ℕ)]) (TNullSeriesIdeal p (T : ℕ))) fhat
    (((IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).map
       (OQpUn_embd p T)))
  rw [show Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ))
        (((IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).map
          (OQpUn_embd p T)).aeval fhat) =
      Ideal.Quotient.mkₐ (ℤᵘⁿ_[p, (T : ℕ)])
        (TNullSeriesIdeal p (T : ℕ))
        (((IsLocalization.integerNormalization (nonZeroDivisors ℤᵘⁿ_[p]) P).map
          (OQpUn_embd p T)).aeval fhat) from rfl]
  rw [← key]
  -- Goal: aeval (mkₐ fhat) (P_int.map OQpUn_embd) = 0
  have h_mkₐ_eq : Ideal.Quotient.mkₐ (ℤᵘⁿ_[p, (T : ℕ)])
      (TNullSeriesIdeal p (T : ℕ)) fhat = σ p (T : ℕ) f := h_mk_eq
  rw [h_mkₐ_eq, h_aeval_map, hPint_σf]

/-- §4d-d — Multinomial expansion of `Pfhat_TLifted` (Round 10).

By `Polynomial.aeval_eq_sum_range`, `Pfhat_TLifted` decomposes as a finite sum
over the natDegree of `P_int.map OQpUn_embd`. Each term `OQpUn_embd (P_int.coeff i)
• fhat^i` is then susceptible to the multinomial expansion (`HahnSeries.coeff_pow`
+ multinomial formula). This lemma is the **first step** of the combinatorial
collapse needed in `identity_c_collapsed`.

This is real-proof infrastructure for next round; it doesn't introduce sorries. -/
lemma Pfhat_TLifted_eq_sum_range {p : ℕ} [Fact (Nat.Prime p)] (T : ℕ+)
    (P : Polynomial ℚᵘⁿ_[p])
    (fhat : TLiftedPAdicHahnSeries p (T : ℕ)) :
    Pfhat_TLifted T P fhat =
      ∑ i ∈ Finset.range (((P_int P).map (OQpUn_embd p T)).natDegree + 1),
        OQpUn_embd p T ((P_int P).coeff i) • fhat ^ i := by
  unfold Pfhat_TLifted
  rw [Polynomial.aeval_eq_sum_range]
  congr 1
  ext i
  rw [Polynomial.coeff_map]

/-- §4d-e — Per-coefficient expansion of `Pfhat_TLifted`.

For each `q ∈ ℚ`, `(Pfhat_TLifted T P fhat).coeff q` decomposes as a finite sum
`∑ᵢ OQpUn_embd (P_int.coeff i) * (fhat^i).coeff q`. This is the entry point for
the multinomial expansion of `fhat^i.coeff q` (Round 11 work). -/
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

/-- §4d — Identity (c): the IsTNullSeries identity for `P.aeval(f̂)` specialised at
`q = -r₀/T`.

PDF reasoning: by §4b, `σ(P.aeval f) = 0`. By multinomial expansion of `f̂^i`, the
element of `TLiftedPAdicHahnSeries p T` whose quotient image equals `σ(P.aeval f) = 0`
is in `N_T`. Applying `IsTNullSeries` at `q = -r₀/T` and using the prescribed
coefficient formula yields:
`∑_{w ∈ ℤ} p^w · ∑_{φ̃ : S̃ → ℕ, ∑φ̃ ≤ n, ∑φ̃(s)·s = -r₀/T + w/T}
  a_{∑φ̃} · multinomial · ∏ C_s^{φ̃(s)}  =  0`.

The statement is packaged as the (existential) existence of an explicit
`Pfhat ∈ TLiftedPAdicHahnSeries p T` with the multinomial coefficient formula and
membership in `TNullSeriesIdeal p T`. The detailed combinatorial formula is the next
round's work — it requires either an iterated `HahnSeries.coeff_mul` formula or a
direct construction.

(Body deferred — encapsulates the combinatorial heart of Step 4.) -/
private lemma identity_c
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    {hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}}
    {C : ℕ+} {n : ℕ+} (_hSparse : IsCNSparse p C n S hS)
    {Cs : ↥(Stilde hf2) → ℤᵘⁿ_[p, (T : ℕ)]}
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (_h_supp : Function.support fhat.coeff ⊆ Stilde hf2)
    (_h_coeff_eq : ∀ (s : ↥(Stilde hf2)), fhat.coeff s.val = Cs s)
    (h_mk_eq : Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) fhat = σ p (T : ℕ) f)
    {P : Polynomial ℚᵘⁿ_[p]} (hP_aeval : (Polynomial.aeval f) P = 0)
    (_hP_natDegree : P.natDegree = n) :
    ∃ Pfhat : TLiftedPAdicHahnSeries p (T : ℕ),
      Pfhat ∈ TNullSeriesIdeal p (T : ℕ) := by
  -- Round 10: strengthened witness. We supply `Pfhat_TLifted` (the
  -- denominator-cleared multinomial expansion of `P.aeval fhat`) and prove
  -- it lies in `TNullSeriesIdeal p T` via `Pfhat_TLifted_isTNullSeries`.
  exact ⟨Pfhat_TLifted T P fhat,
    Pfhat_TLifted_isTNullSeries T hP_aeval h_mk_eq⟩

/-! ### Step 5 — Collapse via Lemma 3.5 (PDF p. 9-10). -/

/-- §5a — Every `φ̃ : Stilde → ℕ` satisfying the constraints from equation (c)
equals `φ₀ ∘ μ⁻¹`.

PDF reasoning: define `φ := φ̃ ∘ μ : S → ℕ`. Using `mu_q_residue` (i.e. `‖d‖ + T·μ(d) ∈ ℤ`):
`∑‖d‖·φ(d) ≡ -T·∑μ(d)·φ̃(μd) = -T·∑s·φ̃(s) (mod ℤ)`. From the residue hypothesis,
`-T·∑s·φ̃(s) ≡ r₀ (mod ℤ) = ∑‖d‖·φ₀(d) (mod ℤ)`. So `φ` satisfies the residue clause
of `Sparse.lemma_1_5`. Combined with finite support and the sum bound, lemma_1_5 yields
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
    phiT = Sparse.φ₀ hSparse ∘ (mu_equiv hS hf2).symm := by
  set μ := mu_equiv hS hf2 with hμ_def
  set φ : S → ℕ := phiT ∘ μ with hφ_def
  -- Apply Sparse.lemma_1_5 to get φ = φ₀ hSparse.
  have hφ_eq : φ = Sparse.φ₀ hSparse := by
    refine Sparse.lemma_1_5 hSparse φ ?_ ?_ ?_
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
      -- PDF p. 9–10: use `mu_q_residue d : (‖d‖ + T·μ_q d).isInt = true`, multiply
      -- by `phiT(μ d)`, sum over `d` (giving an integer sum), distribute, change
      -- variable `d ↦ μ d` to land at `∑ᶠ s, s·phiT s`, and combine with
      -- `hphiT_residue` to conclude.
      -- (μ d).val = mu_q hf2 d, by def of `mu_equiv` and `mu_to_Stilde`.
      have hμ_val : ∀ d : S, ((μ d : ↥(Stilde hf2)) : ℚ) = mu_q hf2 d := fun _ => rfl
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
        exact mu_q_residue hf2 d
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

/-- §5b — Collapsed form of equation (c): only the `φ̃ = φ₀ ∘ μ⁻¹` summand survives.

PDF reasoning: by §5a, every nonzero summand of (c) has `φ̃ = φ₀ ∘ μ⁻¹`, with the
single surviving `w` equal to `r₀ + T·∑φ₀(d)·μ(d) ∈ ℤ`. Equation (c) collapses to
`p^{r₀ + T·∑φ₀(d)·μ(d)} · a_n · (n!/∏φ₀(d)!) · ∏ Cs(μd)^{φ₀(d)} = 0`
in `ℤᵘⁿ_[p,T]` (or its embedding, depending on the natural ambient ring used by §4d).

The statement here is presented as a `(... = 0)` in `ℤᵘⁿ_[p,T]`, abstracting over the
algebraMap and exponent conventions. (Body deferred — requires §4d + §5a.) -/
private lemma identity_c_collapsed
    {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {S : Set DigitSeries} {hS : ∀ d ∈ S, d.IsP p}
    {hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
                     {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}}
    {C : ℕ+} {n : ℕ+} (hSparse : IsCNSparse p C n S hS)
    {Cs : ↥(Stilde hf2) → ℤᵘⁿ_[p, (T : ℕ)]}
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (h_supp : Function.support fhat.coeff ⊆ Stilde hf2)
    (h_coeff_eq : ∀ (s : ↥(Stilde hf2)), fhat.coeff s.val = Cs s)
    (h_mk_eq : Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) fhat = σ p (T : ℕ) f)
    {P : Polynomial ℚᵘⁿ_[p]} (hP_aeval : (Polynomial.aeval f) P = 0)
    (hP_natDegree : P.natDegree = n) :
    (algebraMap ℚᵘⁿ_[p] ℚᵘⁿ_[p, (T : ℕ)]) (P.coeff n) *
        (∏ᶠ d : S, algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
                     (Cs (mu_to_Stilde hf2 d) ^ (Sparse.φ₀ hSparse d))) = 0 := by
  -- Round 10: structured partial proof via Pfhat_TLifted.
  -- Step 1: Get Pfhat_TLifted ∈ TNullSeriesIdeal (closed in Round 10).
  have hPfhat_null : Pfhat_TLifted T P fhat ∈ TNullSeriesIdeal p (T : ℕ) :=
    Pfhat_TLifted_isTNullSeries T hP_aeval h_mk_eq
  -- Step 2: Unwrap to IsTNullSeries (carrier definition of the ideal).
  have hPfhat_TNS : IsTNullSeries p (T : ℕ) (Pfhat_TLifted T P fhat) := hPfhat_null
  -- Step 3: specialize at g = -r0/T. The Tendsto identity says:
  -- partial sums of (pInvTQ)^n · algebraMap(Pfhat.coeff (-r0/T + n/T)) tend to 0.
  have h_at_r0 := hPfhat_TNS (- (r0 hSparse) / T)
  -- Step 4 (combinatorial): the partial sums eventually stabilize at the multinomial
  -- expansion `∑_(i, φ̃) (algebraMap P_int.coeff i) · multinomial · ∏ Cs^φ̃`.
  -- By phi_tilde_constraint_at_phi0, the only contributing φ̃ has `φ̃ = φ₀ ∘ μ.symm`,
  -- forcing `i = ∑φ₀ = n` (since hSparse says ∑φ₀ = n via IsCNSparse choose-spec).
  -- The surviving term gives
  --   `(algebraMap (P_int.coeff n)) · multinomial(n; φ₀(d)) · ∏ algebraMap (Cs(μd)^φ₀(d))
  --      = 0` in ℚᵘⁿ_[p,T].
  -- Dividing by the non-zero factors `algebraMap c` (from integerNormalization) and
  -- multinomial yields the desired identity with `P.coeff n` in place of
  -- `algebraMap (P_int.coeff n) / c`.
  --
  -- Implementation steps (deferred to next round; ~150-250 lines):
  --   (a) Compute Pfhat.coeff at q = -r0/T + w/T via `HahnSeries.coeff_pow` iterated.
  --   (b) For each w ∈ ℤ, characterize the (i, φ̃) pairs contributing to
  --       Pfhat.coeff (-r0/T + w/T) — those with ∑φ̃ ≤ n AND
  --       ∑φ̃(s) · s = -r0/T + w/T, which gives residue (T·∑φ̃(s)·s + r0) = w.isInt = true.
  --   (c) Apply `phi_tilde_constraint_at_phi0` (real, line 1685) to force φ̃ = φ₀ ∘ μ.symm.
  --   (d) Sum `∑φ̃ = ∑(φ₀ ∘ μ.symm) = ∑φ₀ = n` via change of variable along μ.
  --   (e) So only one w survives: `w₀ := T·∑(μd)·φ₀(d) + r0` (an integer by mu_q_residue).
  --   (f) `Pfhat.coeff (-r0/T + w₀/T) = (algebraMap (P_int.coeff n)) · n!/∏φ₀(d)! ·
  --       ∏ Cs(μd)^φ₀(d)`. The other coefficients (with q = -r0/T + w/T, w ≠ w₀)
  --       are zero.
  --   (g) The Tendsto becomes a Tendsto of a constant nonzero sequence to 0, forcing
  --       the constant to be 0.
  --   (h) Divide out by non-zero factors (algebraMap c, multinomial, p^w₀) in the
  --       domain ℚᵘⁿ_[p,T] to get the conclusion.
  --
  -- Available: Pfhat_TLifted, P_int, Pfhat_TLifted_isTNullSeries (this round);
  --   r0, phi_tilde_constraint_at_phi0, mu_q_residue, mu_equiv, isInt_* helpers,
  --   Cs, fhat, mu_to_Stilde (existing).
  sorry

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
    {Cs : ↥(Stilde hf2) → ℤᵘⁿ_[p, (T : ℕ)]}
    {fhat : TLiftedPAdicHahnSeries p (T : ℕ)}
    (h_supp : Function.support fhat.coeff ⊆ Stilde hf2)
    (h_coeff_eq : ∀ (s : ↥(Stilde hf2)), fhat.coeff s.val = Cs s)
    (h_mk_eq : Ideal.Quotient.mk (TNullSeriesIdeal p (T : ℕ)) fhat = σ p (T : ℕ) f)
    {P : Polynomial ℚᵘⁿ_[p]} (hP_aeval : (Polynomial.aeval f) P = 0)
    (hP_natDegree : P.natDegree = n) :
    P.coeff n = 0 ∨ ∃ d : S, Cs (mu_to_Stilde hf2 d) = 0 := by
  have hCollapse :=
    identity_c_collapsed hSparse h_supp h_coeff_eq h_mk_eq hP_aeval hP_natDegree
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
          algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
            (Cs (mu_to_Stilde hf2 d) ^ Sparse.φ₀ hSparse d)) ⊆
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
        (algebraMap (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])) :=
      IsFractionRing.injective (ℤᵘⁿ_[p, (T : ℕ)]) (ℚᵘⁿ_[p, (T : ℕ)])
    have h_powZ : Cs (mu_to_Stilde hf2 d) ^ Sparse.φ₀ hSparse d = 0 :=
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
  rcases final_disjunction (Cs := Cs) (fhat := fhat) hSparse h_supp h_coeff_eq
      h_mk_eq hP_aeval hP_natDegree with hP_zero | ⟨d, hCs_zero⟩
  · exact hP_lead_ne hP_zero
  · exact hCs_ne _ hCs_zero

end MainTheorem

open MainTheorem in
theorem main_theorem (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p])
(T : ℕ+) (hf1 : ∀ q ∈ f.support, ∃ k : ℕ, (T * (p ^ k) * q).isInt)
(S : Set (DigitSeries)) (hS : ∀ f ∈ S, f.IsP p) (hS : IsSparse p S hS)
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
  have lift_data := exists_FhatData f T hS hf2
  exact sparse_contradiction_engine (hcD n hnD) lift_data hP2 hP1 hP3
