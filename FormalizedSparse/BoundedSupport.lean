import FormalizedSparse.MainTheorem
import FormalizedSparse.RayDecomposition
import Mathlib.Topology.DerivedSet

/- USER: This file corresponds to the subsection
`Sparse representatives and finiteness of bounded QTR supports`. You need to formalize every thing
in this subsection in this file. I have already formalized the statement of the main theorem
`thm:29057` as follows (``). You should not change the statement of it.
-/

namespace FormalizedSparse

/-! ## Infrastructure for `isSparse_deltas` (lem:57121)

The sparseness proof builds an explicit witness sequence whose elements are a
single digit *block* placed in pairwise-disjoint *islands* far apart along the
`p`-adic digit line. We need two operations on `Sparse.DigitSeries`:

* `ofFinsupp d` — turn the §6 finsupp digit model `d : ℕ →₀ ℕ` (`d j` = digit at
  position `j+1`) into a `DigitSeries`.
* `shiftBy f m` — move every digit of `f` right by `m` positions, i.e. multiply
  the value by `p^{-m}`.

The key algebraic facts (`norm_shiftBy`, `Psi_shiftBy`, `ofFinsupp_norm`) let us
recognise each element `δ_l · p^{-Nk}` of `W` as a shifted block, which is the
backbone of both the no-carry and the rigidity halves of `IsSparse`. -/

namespace Sparse.DigitSeries

open Sparse

/-- Add a `ℕ` offset to a `ℕ+` index. -/
def pAdd (i : ℕ+) (m : ℕ) : ℕ+ := ⟨(i : ℕ) + m, by have h := i.pos; omega⟩

@[simp] lemma pAdd_coe (i : ℕ+) (m : ℕ) : ((pAdd i m : ℕ+) : ℕ) = (i : ℕ) + m := rfl

lemma pAdd_inj (m : ℕ) : Function.Injective (fun i => pAdd i m) := by
  intro a b h
  have h2 : ((pAdd a m : ℕ+) : ℕ) = ((pAdd b m : ℕ+) : ℕ) := congrArg (fun x : ℕ+ => (x : ℕ)) h
  rw [pAdd_coe, pAdd_coe] at h2
  exact PNat.coe_injective (by omega)

/-- Build a `DigitSeries` from the §6 finsupp digit model `d : ℕ →₀ ℕ`
(`d j` = digit at position `j+1`, i.e. coefficient of `p^{-(j+1)}`). -/
def ofFinsupp (d : ℕ →₀ ℕ) : DigitSeries where
  toFun := fun q => d q.natPred
  fin_supp := by
    apply Set.Finite.subset (d.support.finite_toSet.image (fun j => Nat.succPNat j))
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    exact ⟨q.natPred, by simpa [Finsupp.mem_support_iff] using hq, PNat.succPNat_natPred q⟩

@[simp] lemma ofFinsupp_apply (d : ℕ →₀ ℕ) (q : ℕ+) : (ofFinsupp d) q = d q.natPred := rfl

lemma ofFinsupp_isP (p : ℕ) [Fact (Nat.Prime p)] (d : ℕ →₀ ℕ) (hd : ∀ j, d j < p) :
    (ofFinsupp d).IsP p := fun _q => hd _

/-- Reindex a sum over `(ofFinsupp d)`'s support (`ℕ+`-indexed) as a `Finsupp.sum`
over `d` (`ℕ`-indexed), via the bijection `q ↦ q.natPred`. The caller supplies only
the per-point value identity; the structural bijection is shared. -/
private lemma ofFinsupp_sum_reindex {M : Type*} [AddCommMonoid M] (d : ℕ →₀ ℕ)
    (F : ℕ+ → M) (H : ℕ → ℕ → M)
    (hFH : ∀ q ∈ (ofFinsupp d).fin_supp.toFinset, F q = H q.natPred (d q.natPred)) :
    ∑ q ∈ (ofFinsupp d).fin_supp.toFinset, F q = d.sum H := by
  classical
  rw [Finsupp.sum]
  refine Finset.sum_bij (fun (q : ℕ+) _ => q.natPred) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq] at hq
    simpa [Finsupp.mem_support_iff] using hq
  · intro a _ b _ hab
    have : Nat.succPNat a.natPred = Nat.succPNat b.natPred := by rw [hab]
    rwa [PNat.succPNat_natPred, PNat.succPNat_natPred] at this
  · intro j hj
    refine ⟨Nat.succPNat j, ?_, ?_⟩
    · simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq]
      simpa [Finsupp.mem_support_iff] using hj
    · simp [Nat.natPred_succPNat]
  · intro q hq
    exact hFH q hq

/-- `ofFinsupp` recovers the §6 finsupp value via `norm`. -/
lemma ofFinsupp_norm (p : ℕ) [Fact (Nat.Prime p)] (d : ℕ →₀ ℕ) :
    (ofFinsupp d).norm p = d.sum (fun j v => (v : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ))) := by
  classical
  change ∑ q ∈ (ofFinsupp d).fin_supp.toFinset, ((ofFinsupp d) q : ℚ) * (p : ℚ) ^ (-(q : ℤ))
       = d.sum (fun j v => (v : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ)))
  apply ofFinsupp_sum_reindex
  intro q hq
  simp only [ofFinsupp_apply]
  congr 2
  have hq' : (q : ℕ) = q.natPred + 1 := (PNat.natPred_add_one q).symm
  rw [show ((q : ℕ) : ℤ) = ((q.natPred : ℕ) : ℤ) + 1 by rw [hq']; push_cast; ring]

/-- The `Psi` (digit sum) of `ofFinsupp d` is the total of the finsupp values. -/
lemma Psi_ofFinsupp (d : ℕ →₀ ℕ) : (ofFinsupp d).Psi = d.sum (fun _ v => v) := by
  classical
  change ∑ q ∈ (ofFinsupp d).fin_supp.toFinset, (ofFinsupp d) q = d.sum (fun _ v => v)
  apply ofFinsupp_sum_reindex
  intro q hq
  simp only [ofFinsupp_apply]

/-- `ofFinsupp d` vanishes beyond position `s` once `d` is supported on `[0, s)`. -/
lemma ofFinsupp_eq_zero_of_lt (d : ℕ →₀ ℕ) (s : ℕ) (hs : ∀ j, s ≤ j → d j = 0)
    (q : ℕ+) (hq : s < (q : ℕ)) : (ofFinsupp d) q = 0 := by
  rw [ofFinsupp_apply]
  apply hs
  have := PNat.natPred_add_one q
  omega

/-- Shift a digit series right by `m` positions (multiply value by `p^{-m}`). -/
def shiftBy (f : DigitSeries) (m : ℕ) : DigitSeries where
  toFun := fun q => if h : m < (q : ℕ) then f ⟨(q : ℕ) - m, by omega⟩ else 0
  fin_supp := by
    apply Set.Finite.subset (f.fin_supp.image (fun i => pAdd i m))
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    split_ifs at hq with h
    · refine ⟨⟨(q : ℕ) - m, by omega⟩, ?_, ?_⟩
      · simpa [Function.mem_support] using hq
      · apply Subtype.ext; change ((q : ℕ) - m) + m = (q : ℕ); omega
    · exact absurd rfl hq

lemma shiftBy_apply_pAdd (f : DigitSeries) (m : ℕ) (i : ℕ+) :
    (shiftBy f m) (pAdd i m) = f i := by
  change (if h : m < ((pAdd i m : ℕ+) : ℕ) then f ⟨((pAdd i m : ℕ+) : ℕ) - m, by omega⟩ else 0)
    = f i
  have hp := i.pos
  rw [dif_pos (by rw [pAdd_coe]; omega)]
  congr 1
  apply Subtype.ext
  change ((pAdd i m : ℕ+) : ℕ) - m = (i : ℕ)
  rw [pAdd_coe]; omega

/-- Where `shiftBy f m` is nonzero: exactly the `m`-translates of `f`'s support. -/
lemma shiftBy_ne_zero_iff (f : DigitSeries) (m : ℕ) (q : ℕ+) :
    (shiftBy f m) q ≠ 0 ↔ ∃ i : ℕ+, f i ≠ 0 ∧ q = pAdd i m := by
  constructor
  · intro hq
    have hmq : m < (q : ℕ) := by
      by_contra hle
      push Not at hle
      apply hq
      change (if h : m < (q : ℕ) then f ⟨(q : ℕ) - m, by omega⟩ else 0) = 0
      rw [dif_neg (by omega)]
    refine ⟨⟨(q : ℕ) - m, by omega⟩, ?_, ?_⟩
    · have hval : (shiftBy f m) q = f ⟨(q : ℕ) - m, by omega⟩ := by
        change (if h : m < (q : ℕ) then f ⟨(q : ℕ) - m, by omega⟩ else 0) = _
        rw [dif_pos hmq]
      rwa [hval] at hq
    · apply PNat.coe_injective
      rw [pAdd_coe]; change (q : ℕ) = (q : ℕ) - m + m; omega
  · rintro ⟨i, hi, rfl⟩
    rw [shiftBy_apply_pAdd]; exact hi

/-- Membership in the support `Finset` of `shiftBy f m`, as a translate. -/
lemma mem_shiftBy_support_iff (f : DigitSeries) (m : ℕ) (q : ℕ+) :
    q ∈ (shiftBy f m).fin_supp.toFinset ↔ ∃ i : ℕ+, f i ≠ 0 ∧ q = pAdd i m := by
  rw [Set.Finite.mem_toFinset, Function.mem_support]
  exact shiftBy_ne_zero_iff f m q

/-- `pAdd i m` lands in the support `Finset` of `shiftBy f m` whenever `i` is in `f`'s support. -/
lemma pAdd_mem_shiftBy_support (f : DigitSeries) (m : ℕ) (i : ℕ+) (hi : f i ≠ 0) :
    pAdd i m ∈ (shiftBy f m).fin_supp.toFinset :=
  (mem_shiftBy_support_iff f m _).mpr ⟨i, hi, rfl⟩

/-- The support of `shiftBy f m` lives strictly above position `m`. -/
lemma shiftBy_eq_zero_of_le (f : DigitSeries) (m : ℕ) (q : ℕ+) (hq : (q : ℕ) ≤ m) :
    (shiftBy f m) q = 0 := by
  by_contra hne
  obtain ⟨i, _, rfl⟩ := (shiftBy_ne_zero_iff f m q).mp hne
  rw [pAdd_coe] at hq
  have := i.pos; omega

lemma shiftBy_isP (p : ℕ) [Fact (Nat.Prime p)] (f : DigitSeries) (m : ℕ) (hf : f.IsP p) :
    (shiftBy f m).IsP p := by
  intro q
  by_cases h : (shiftBy f m) q = 0
  · rw [h]; exact (Fact.out : Nat.Prime p).pos
  · obtain ⟨i, _, rfl⟩ := (shiftBy_ne_zero_iff f m q).mp h
    rw [shiftBy_apply_pAdd]; exact hf i

/-- Reindex a sum over `shiftBy f m`'s support back onto `f`'s support, via the
forward bijection `i ↦ pAdd i m`. Oriented to match the post-`symm` goal
(`∑ over f.support = ∑ over (shiftBy f m).support`); the caller supplies only the
per-point value identity, the structural bijection is shared. -/
private lemma shiftBy_sum_reindex {M : Type*} [AddCommMonoid M] (f : DigitSeries) (m : ℕ)
    (F : ℕ+ → M) (G : ℕ+ → M)
    (hFG : ∀ i ∈ f.fin_supp.toFinset, F i = G (pAdd i m)) :
    ∑ i ∈ f.fin_supp.toFinset, F i = ∑ q ∈ (shiftBy f m).fin_supp.toFinset, G q := by
  classical
  refine Finset.sum_bij (fun (i : ℕ+) _ => pAdd i m) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hi
    exact pAdd_mem_shiftBy_support f m i hi
  · intro a _ b _ hab; exact pAdd_inj m hab
  · intro q hq
    rw [mem_shiftBy_support_iff] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact ⟨i, by rw [Set.Finite.mem_toFinset, Function.mem_support]; exact hi, rfl⟩
  · intro i hi
    exact hFG i hi

/-- `norm` of a shifted series scales by `p^{-m}`. -/
lemma norm_shiftBy (p : ℕ) [Fact (Nat.Prime p)] (f : DigitSeries) (m : ℕ) :
    (shiftBy f m).norm p = f.norm p * (p : ℚ) ^ (-(m : ℤ)) := by
  classical
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  change ∑ q ∈ (shiftBy f m).fin_supp.toFinset, ((shiftBy f m) q : ℚ) * (p : ℚ) ^ (-(q : ℤ))
       = (∑ i ∈ f.fin_supp.toFinset, (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ))) * (p : ℚ) ^ (-(m : ℤ))
  rw [Finset.sum_mul]
  symm
  apply shiftBy_sum_reindex
  intro i _
  rw [shiftBy_apply_pAdd, pAdd_coe, mul_assoc]
  congr 1
  rw [← zpow_add₀ hpne]
  congr 1; push_cast; ring

/-- `Psi` (digit sum) is invariant under shifting. -/
lemma Psi_shiftBy (f : DigitSeries) (m : ℕ) : (shiftBy f m).Psi = f.Psi := by
  classical
  change ∑ q ∈ (shiftBy f m).fin_supp.toFinset, (shiftBy f m) q
       = ∑ i ∈ f.fin_supp.toFinset, f i
  symm
  apply shiftBy_sum_reindex
  intro i _
  rw [shiftBy_apply_pAdd]

/-- Support upper bound after shifting: if `f` vanishes above position `s`, then
`shiftBy f m` vanishes above position `m + s`. -/
lemma shiftBy_eq_zero_of_gt (f : DigitSeries) (m s : ℕ)
    (hf : ∀ q : ℕ+, s < (q : ℕ) → f q = 0)
    (q : ℕ+) (hq : m + s < (q : ℕ)) : (shiftBy f m) q = 0 := by
  by_contra hne
  obtain ⟨i, hi, rfl⟩ := (shiftBy_ne_zero_iff f m q).mp hne
  rw [pAdd_coe] at hq
  exact hi (hf i (by omega))

/-- The support of `shiftBy f m` lives strictly above `m`: if nonzero at `q` then `m < q`. -/
lemma shiftBy_pos_of_ne_zero (f : DigitSeries) (m : ℕ) (q : ℕ+)
    (hq : (shiftBy f m) q ≠ 0) : m < (q : ℕ) := by
  by_contra hle
  exact hq (shiftBy_eq_zero_of_le f m q (by omega))

end Sparse.DigitSeries

/-- Window separation (raw `ℕ` arithmetic): with spacing `Q ≥ 2s+1`, a point `q`
lies in at most one window `(Q·i, Q·i + s]`. -/
private lemma window_index_unique {Q s : ℕ} (hQ : 2 * s + 1 ≤ Q) {i i' q : ℕ}
    (h1 : Q * i < q ∧ q ≤ Q * i + s) (h2 : Q * i' < q ∧ q ≤ Q * i' + s) : i = i' := by
  rcases lt_trichotomy i i' with h | h | h
  · exfalso
    have hle : Q * (i + 1) ≤ Q * i' := Nat.mul_le_mul_left Q h
    have he : Q * (i + 1) = Q * i + Q := by ring
    omega
  · exact h
  · exfalso
    have hle : Q * (i' + 1) ≤ Q * i := Nat.mul_le_mul_left Q h
    have he : Q * (i' + 1) = Q * i' + Q := by ring
    omega

/-- Window separation, two-point version: if `q` and `q'` both lie in a common
width-`s` interval `(a, a+s]`, then any windows containing `q` resp. `q'` (with
spacing `Q ≥ 2s+1`) have the same index. -/
private lemma window_index_unique' {Q s a q q' : ℕ} (hQ : 2 * s + 1 ≤ Q) {j j' : ℕ}
    (ha_q : a < q ∧ q ≤ a + s) (ha_q' : a < q' ∧ q' ≤ a + s)
    (hwj : Q * j < q ∧ q ≤ Q * j + s) (hwj' : Q * j' < q' ∧ q' ≤ Q * j' + s) : j = j' := by
  rcases lt_trichotomy j j' with h | h | h
  · exfalso
    have hle : Q * (j + 1) ≤ Q * j' := Nat.mul_le_mul_left Q h
    have he : Q * (j + 1) = Q * j + Q := by ring
    omega
  · exact h
  · exfalso
    have hle : Q * (j' + 1) ≤ Q * j := Nat.mul_le_mul_left Q h
    have he : Q * (j' + 1) = Q * j' + Q := by ring
    omega

/-- Pointwise `≤` with equal digit sums forces equality of digit series. -/
private lemma Sparse.DigitSeries.eq_of_le_of_Psi_eq {g h : Sparse.DigitSeries}
    (hgh : ∀ q, g q ≤ h q) (hPsi : g.Psi = h.Psi) : g = h := by
  classical
  -- Work on the (finite) support of `h`, which contains that of `g`.
  have hsub : g.fin_supp.toFinset ⊆ h.fin_supp.toFinset := by
    intro q hq
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hq ⊢
    intro hzero
    exact hq (Nat.le_zero.mp (by rw [← hzero]; exact hgh q))
  have hsum_g : g.Psi = ∑ q ∈ h.fin_supp.toFinset, g q := by
    change ∑ q ∈ g.fin_supp.toFinset, g q = _
    refine Finset.sum_subset hsub ?_
    intro q _ hq
    rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hq
    exact hq
  have hsum_h : h.Psi = ∑ q ∈ h.fin_supp.toFinset, h q := rfl
  -- Each pointwise gap is zero.
  have hpt : ∀ q ∈ h.fin_supp.toFinset, g q = h q := by
    have hle' : ∀ q ∈ h.fin_supp.toFinset, g q ≤ h q := fun q _ => hgh q
    have heq : ∑ q ∈ h.fin_supp.toFinset, g q = ∑ q ∈ h.fin_supp.toFinset, h q := by
      rw [← hsum_g, ← hsum_h]; exact hPsi
    exact (Finset.sum_eq_sum_iff_of_le hle').mp heq
  ext q
  by_cases hq : q ∈ h.fin_supp.toFinset
  · exact hpt q hq
  · rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hq
    have hg0 : g q = 0 := Nat.le_zero.mp (by rw [← hq]; exact hgh q)
    change g q = h q
    rw [hg0]; exact hq.symm

open Sparse in
/-- `lem:57121`: the δ-set is sparse.
Let `N ≥ 1`, `r`, and `δ : Fin r → ℚ` with each `δ i` a nonzero rational in `[0,1)`
having a finite base-`p` expansion (the §6 finsupp digit model `d : ℕ →₀ ℕ`, where
`d j` = digit `q_{j+1}`, `d j < p`, value `∑ d j · p^{-(j+1)}` — same model as
`Kedlaya.Sabc` / `RayDecomposition.Sabc_m`). Then
`W = { δ i · p^{-N·k} : i, k ≥ 0 }` is `IsSparse p`. -/
theorem isSparse_deltas {p : ℕ} [Fact (Nat.Prime p)] (N : ℕ+) (r : ℕ) (hr : 0 < r)
    (δ : Fin r → ℚ)
    (_hδ_mem : ∀ i, δ i ∈ Set.Ico (0 : ℚ) 1) (hδ_ne : ∀ i, δ i ≠ 0)
    (hδ_fin : ∀ i, ∃ d : ℕ →₀ ℕ, (∀ j, d j < p) ∧
      δ i = d.sum fun j v => (v : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ))) :
    IsSparse p { w : ℚ | ∃ (i : Fin r) (k : ℕ),
      w = δ i * (p : ℚ) ^ (-(N : ℤ) * k) } := by
  classical
  -- Choose, for each `i`, the finsupp digit model `D i` of `δ i`.
  choose D hD_lt hD_val using hδ_fin
  -- Package each as a `DigitSeries` block `B i := ofFinsupp (D i)`.
  set B : Fin r → Sparse.DigitSeries := fun i => Sparse.DigitSeries.ofFinsupp (D i) with hB_def
  have hB_isP : ∀ i, (B i).IsP p := fun i => Sparse.DigitSeries.ofFinsupp_isP p (D i) (hD_lt i)
  -- `norm (B i) = δ i`.
  have hB_norm : ∀ i, (B i).norm p = δ i := by
    intro i; rw [hB_def]; simp only; rw [Sparse.DigitSeries.ofFinsupp_norm, ← hD_val i]
  -- `Psi (B i) = total digit sum of `D i``.
  have hB_psi : ∀ i, (B i).Psi = (D i).sum (fun _ v => v) := fun i => by
    rw [hB_def]; simp only; rw [Sparse.DigitSeries.Psi_ofFinsupp]
  -- Each digit sum is positive (since `δ i ≠ 0` ⇒ `D i ≠ 0`).
  have hB_psi_pos : ∀ i, 0 < (B i).Psi := by
    intro i
    rw [hB_psi i]
    have hDne : D i ≠ 0 := by
      intro h0
      apply hδ_ne i
      rw [hD_val i, h0]; simp
    rw [Finsupp.sum]
    refine Finset.sum_pos (fun a ha => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ha)) ?_
    exact Finsupp.support_nonempty_iff.mpr hDne
  -- A uniform support bound `s` for every block: each `D i` is supported on `[0, s)`,
  -- so `B i` vanishes above position `s`.
  obtain ⟨s, hs⟩ : ∃ s : ℕ, ∀ i, ∀ q : ℕ+, s < (q : ℕ) → (B i) q = 0 := by
    refine ⟨(Finset.univ.sup fun i => (D i).support.sup id) + 1, ?_⟩
    intro i q hq
    rw [hB_def]; simp only
    refine Sparse.DigitSeries.ofFinsupp_eq_zero_of_lt (D i)
      ((Finset.univ.sup fun i => (D i).support.sup id) + 1) ?_ q hq
    intro j hj
    by_contra hjne
    have hj_mem : j ∈ (D i).support := Finsupp.mem_support_iff.mpr hjne
    have hj_le : j ≤ (D i).support.sup id := Finset.le_sup (f := id) hj_mem
    have hsup_le : (D i).support.sup id ≤ Finset.univ.sup fun i => (D i).support.sup id :=
      Finset.le_sup (f := fun i => (D i).support.sup id) (Finset.mem_univ i)
    omega
  -- The maximal digit-sum index `i₀` (argmax of `Psi (B ·)`); `C := Psi (B i₀)`.
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, (Finset.univ.sup fun i => (B i).Psi) = (B i₀).Psi := by
    have hne : (Finset.univ : Finset (Fin r)).Nonempty := by
      rw [Finset.univ_nonempty_iff]; exact Fin.pos_iff_nonempty.mp hr
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup _ hne (fun i => (B i).Psi)
    exact ⟨i, hi⟩
  set C : ℕ := (B i₀).Psi with hC_def
  have hC_pos : 0 < C := hB_psi_pos i₀
  have hC_max : ∀ i, (B i).Psi ≤ C := by
    intro i; rw [← hi₀]
    exact Finset.le_sup (f := fun i => (B i).Psi) (Finset.mem_univ i)
  -- Window spacing.
  set Q : ℕ := (N : ℕ) * (2 * s + 1) with hQ_def
  have hQ_ge : 2 * s + 1 ≤ Q := by
    rw [hQ_def]; exact Nat.le_mul_of_pos_left _ N.pos
  -- The blocks of the witness sequence (all the maximal block, widely spaced).
  set blk : Fin r → ℕ → Sparse.DigitSeries := fun i k => Sparse.DigitSeries.shiftBy (B i) ((N:ℕ)*k)
    with hblk_def
  -- The candidate digit-series set `S`.
  set S : Set Sparse.DigitSeries := { f | ∃ (i : Fin r) (k : ℕ), f = blk i k } with hS_def
  -- Every element of `S` is `IsP`.
  have hS_isP : ∀ f ∈ S, f.IsP p := by
    rintro f ⟨i, k, rfl⟩
    exact Sparse.DigitSeries.shiftBy_isP p (B i) _ (hB_isP i)
  -- The norm of `blk i k` is exactly the corresponding element of `W`.
  have hblk_norm : ∀ i k, (blk i k).norm p = δ i * (p : ℚ) ^ (-(N : ℤ) * (k : ℤ)) := by
    intro i k
    rw [hblk_def]; simp only
    rw [Sparse.DigitSeries.norm_shiftBy, hB_norm]
    congr 1
    rw [show (-(N : ℤ) * (k : ℤ)) = (-(((N : ℕ) * k : ℕ) : ℤ)) by push_cast; ring]
  -- Abbreviation for the target set `W`.
  set W : Set ℚ := { w : ℚ | ∃ (i : Fin r) (k : ℕ), w = δ i * (p : ℚ) ^ (-(N : ℤ) * k) } with hW_def
  -- `W ≠ {0}` (it contains the nonzero `δ i₀`).
  have hW_ne : W ≠ {0} := by
    intro hEq
    have hmem : δ i₀ ∈ W := ⟨i₀, 0, by simp⟩
    rw [hEq, Set.mem_singleton_iff] at hmem
    exact hδ_ne i₀ hmem
  rw [Sparse.IsSparse_iff_IsCNSparse p W hW_ne]
  refine ⟨S, hS_isP, ?_, ?_⟩
  · -- `norm '' S = W`.
    ext w
    simp only [Set.mem_image, hS_def, Set.mem_setOf_eq, hW_def]
    constructor
    · rintro ⟨f, ⟨i, k, rfl⟩, rfl⟩
      exact ⟨i, k, (hblk_norm i k)⟩
    · rintro ⟨i, k, rfl⟩
      exact ⟨blk i k, ⟨i, k, rfl⟩, (hblk_norm i k)⟩
  · -- The `IsCNSparse` witness data: `c = C`, `D = univ` (all `n : ℕ+`).
    refine ⟨⟨C, hC_pos⟩, Set.univ, Set.infinite_univ, ?_⟩
    intro n _
    -- The witness sequence: `n` copies of the maximal block `B i₀`, with
    -- left-edges at `Q·j` (`j = 0,…,n-1`).  `wit j = blk i₀ ((2s+1)·j)`.
    refine ⟨?_, ?_⟩
    · -- First clause: every `f ∈ S` has digit sum `≤ C`.
      rintro f ⟨i, k, rfl⟩
      change (Sparse.DigitSeries.shiftBy (B i) ((N:ℕ)*k)).Psi ≤ C
      rw [Sparse.DigitSeries.Psi_shiftBy]
      exact hC_max i
    · -- The witness map and its three properties.
      set wit : Fin (n : ℕ) → S := fun j =>
        ⟨blk i₀ ((2 * s + 1) * j), ⟨i₀, (2 * s + 1) * j, rfl⟩⟩ with hwit_def
      -- Left-edge of the `j`-th window.
      have hwit_val : ∀ j : Fin (n : ℕ),
          (wit j).val = Sparse.DigitSeries.shiftBy (B i₀) (Q * j) := by
        intro j
        rw [hwit_def]; simp only [hblk_def]
        congr 1
        rw [hQ_def]; ring
      -- Support facts: the `j`-th block lives in the window `(Q·j, Q·j + s]`.
      have hwit_lo : ∀ (j : Fin (n : ℕ)) (q : ℕ+), (wit j).val q ≠ 0 → Q * (j : ℕ) < (q : ℕ) := by
        intro j q hq
        rw [hwit_val j] at hq
        exact Sparse.DigitSeries.shiftBy_pos_of_ne_zero (B i₀) (Q * j) q hq
      have hwit_hi : ∀ (j : Fin (n : ℕ)) (q : ℕ+),
          (wit j).val q ≠ 0 → (q : ℕ) ≤ Q * (j : ℕ) + s := by
        intro j q hq
        by_contra hgt
        push Not at hgt
        rw [hwit_val j] at hq
        exact hq (Sparse.DigitSeries.shiftBy_eq_zero_of_gt (B i₀) (Q * j) s (hs i₀) q (by omega))
      -- Disjointness of distinct windows.
      have hwit_disj : ∀ (j j' : Fin (n : ℕ)) (q : ℕ+),
          (wit j).val q ≠ 0 → (wit j').val q ≠ 0 → j = j' := by
        intro j j' q hj hj'
        have h1 : Q * (j : ℕ) < (q : ℕ) ∧ (q : ℕ) ≤ Q * (j : ℕ) + s :=
          ⟨hwit_lo j q hj, hwit_hi j q hj⟩
        have h2 : Q * (j' : ℕ) < (q : ℕ) ∧ (q : ℕ) ≤ Q * (j' : ℕ) + s :=
          ⟨hwit_lo j' q hj', hwit_hi j' q hj'⟩
        exact Fin.ext (window_index_unique hQ_ge h1 h2)
      -- `∑ wit` is `IsP` (digit-disjoint witness blocks never carry). Proved once, used by
      -- clause (2) directly and by clause (3)'s `hDsum_isP`.
      have hSumWit_isP : (∑ i : Fin (n : ℕ), (wit i).val).IsP p := by
        intro q
        rw [Sparse.DigitSeries.sum_apply]
        by_cases hex : ∃ j₀ : Fin (n : ℕ), (wit j₀).val q ≠ 0
        · obtain ⟨j₀, hj₀⟩ := hex
          have hsingle : ∑ j : Fin (n : ℕ), (wit j).val q = (wit j₀).val q := by
            rw [Finset.sum_eq_single j₀]
            · intro j _ hjne
              by_contra hjnz
              exact hjne (hwit_disj j j₀ q hjnz hj₀)
            · intro h; exact absurd (Finset.mem_univ _) h
          rw [hsingle]
          exact hS_isP (wit j₀).val (wit j₀).property q
        · push Not at hex
          rw [Finset.sum_eq_zero (fun j _ => hex j)]
          exact (Fact.out : Nat.Prime p).pos
      refine ⟨wit, ?_, ?_, ?_⟩
      · -- Clause (1): each witness has digit sum `C`.
        intro j
        rw [hwit_val j, Sparse.DigitSeries.Psi_shiftBy]
        rfl
      · -- Clause (2): no carry — disjoint witness supports (see `hSumWit_isP`).
        exact hSumWit_isP
      · -- Clause (3): rigidity.
        intro e he_isInt
        -- Abbreviations for the two digit-series sums.
        set Dsum : Sparse.DigitSeries := ∑ i : Fin (n : ℕ), (wit i).val with hDsum_def
        set Esum : Sparse.DigitSeries := ∑ i : Fin (n : ℕ), (e i).val with hEsum_def
        -- `∑ wit` is `IsP` — reuse the hoisted `hSumWit_isP` (was copy-pasted before).
        have hDsum_isP : Dsum.IsP p := by rw [hDsum_def]; exact hSumWit_isP
        -- Each witness / each `e l` has digit sum `C` resp. `≤ C`.
        have hwit_psi : ∀ j, (wit j).val.Psi = C := by
          intro j; rw [hwit_val j, Sparse.DigitSeries.Psi_shiftBy]
        have he_psi_le : ∀ l, (e l).val.Psi ≤ C := by
          intro l
          obtain ⟨i, k, hik⟩ := (e l).property
          rw [hik]
          change (Sparse.DigitSeries.shiftBy (B i) ((N:ℕ)*k)).Psi ≤ C
          rw [Sparse.DigitSeries.Psi_shiftBy]; exact hC_max i
        -- `Psi Dsum = n·C`.
        have hDsum_psi : Dsum.Psi = (n : ℕ) * C := by
          rw [hDsum_def, map_sum]
          simp_rw [hwit_psi]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        -- `Psi Esum ≤ n·C`.
        have hEsum_psi_le : Esum.Psi ≤ (n : ℕ) * C := by
          rw [hEsum_def, map_sum]
          calc ∑ l : Fin (n : ℕ), (e l).val.Psi
              ≤ ∑ _l : Fin (n : ℕ), C := Finset.sum_le_sum (fun l _ => he_psi_le l)
            _ = (n : ℕ) * C := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        -- τ-equivalence from the integrality hypothesis.
        have hτ_eq : Dsum.tau p = Esum.tau p :=
          (Sparse.lemma_3_3₂ p _ _).mpr he_isInt
        have hτ_Dself : Dsum.tau p = Dsum := (Sparse.lemma_3_3₃ p _).mpr hDsum_isP
        -- `Psi Esum = n·C` (squeeze).
        have hEsum_psi : Esum.Psi = (n : ℕ) * C := by
          have hle1 : (n : ℕ) * C ≤ Esum.Psi := by
            calc (n : ℕ) * C = Dsum.Psi := hDsum_psi.symm
              _ = (Dsum.tau p).Psi := by rw [hτ_Dself]
              _ = (Esum.tau p).Psi := by rw [hτ_eq]
              _ ≤ Esum.Psi := Sparse.Psi_tau_le_Psi p _
          exact le_antisymm hEsum_psi_le hle1
        -- Each `Psi (e l) = C`.
        have he_psi : ∀ l, (e l).val.Psi = C := by
          intro l
          by_contra hne
          have hlt : (e l).val.Psi < C := lt_of_le_of_ne (he_psi_le l) hne
          have hstrict : Esum.Psi < (n : ℕ) * C := by
            rw [hEsum_def, map_sum]
            calc ∑ l' : Fin (n : ℕ), (e l').val.Psi
                < ∑ _l' : Fin (n : ℕ), C :=
                  Finset.sum_lt_sum (fun l' _ => he_psi_le l') ⟨l, Finset.mem_univ l, hlt⟩
              _ = (n : ℕ) * C := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          omega
        -- `Esum` is also `IsP` (digit sums of τ and itself agree).
        have hEsum_isP : Esum.IsP p := by
          apply (Sparse.lemma_3_3₄ p Esum).mp
          refine ⟨Sparse.Psi_tau_le_Psi p _, ?_⟩
          calc (Esum.tau p).Psi
              = (Dsum.tau p).Psi := by rw [hτ_eq]
            _ = Dsum.Psi := by rw [hτ_Dself]
            _ = (n : ℕ) * C := hDsum_psi
            _ = Esum.Psi := hEsum_psi.symm
        -- The two IsP sums are equal (equal τ).
        have hsum_eq : Dsum = Esum := by
          have hτ_Eself : Esum.tau p = Esum := (Sparse.lemma_3_3₃ p _).mpr hEsum_isP
          rw [← hτ_Dself, hτ_eq, hτ_Eself]
        -- Pointwise equality of the two sums.
        have hsum_pt : ∀ q : ℕ+,
            ∑ j : Fin (n : ℕ), (wit j).val q = ∑ l : Fin (n : ℕ), (e l).val q := by
          intro q
          have := congrArg (fun (g : Sparse.DigitSeries) => (g : ℕ+ → ℕ) q) hsum_eq
          rw [hDsum_def, hEsum_def] at this
          rwa [Sparse.DigitSeries.sum_apply, Sparse.DigitSeries.sum_apply] at this
        -- Each `e l` is nonzero (its digit sum is `C > 0`).
        have he_ne : ∀ l, ∃ q : ℕ+, (e l).val q ≠ 0 := by
          intro l
          by_contra hall
          push Not at hall
          have : (e l).val.Psi = 0 := by
            change ∑ q ∈ (e l).val.fin_supp.toFinset, (e l).val q = 0
            refine Finset.sum_eq_zero (fun q _ => hall q)
          rw [he_psi l] at this; omega
        -- Each `e l` lives in a width-`s` window: its support is in `(a_l, a_l + s]`.
        have he_window : ∀ l, ∃ a : ℕ, ∀ q : ℕ+,
            (e l).val q ≠ 0 → a < (q : ℕ) ∧ (q : ℕ) ≤ a + s := by
          intro l
          obtain ⟨i, k, hik⟩ := (e l).property
          refine ⟨(N : ℕ) * k, ?_⟩
          intro q hq
          rw [hik] at hq
          refine ⟨Sparse.DigitSeries.shiftBy_pos_of_ne_zero (B i) _ q hq, ?_⟩
          by_contra hgt
          push Not at hgt
          exact hq (Sparse.DigitSeries.shiftBy_eq_zero_of_gt (B i) ((N:ℕ)*k) s (hs i) q (by omega))
        -- CRUX: each `e l` equals exactly one witness block `wit (σ l)`.
        have he_eq_wit : ∀ l, ∃ j : Fin (n : ℕ), (e l).val = (wit j).val := by
          intro l
          obtain ⟨q_l, hq_l⟩ := he_ne l
          obtain ⟨a_l, ha_l⟩ := he_window l
          -- `q_l` is a nonzero position of `Dsum`, so it lands in some window `j`.
          have hDsum_ql : ∑ j : Fin (n : ℕ), (wit j).val q_l ≠ 0 := by
            rw [hsum_pt q_l]
            intro hzero
            have : (e l).val q_l = 0 := by
              have hle : (e l).val q_l ≤ ∑ l' : Fin (n : ℕ), (e l').val q_l :=
                Finset.single_le_sum (f := fun l' => (e l').val q_l)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
              omega
            exact hq_l this
          obtain ⟨j, _, hj⟩ : ∃ j ∈ (Finset.univ : Finset (Fin (n:ℕ))), (wit j).val q_l ≠ 0 := by
            by_contra hnone
            push Not at hnone
            exact hDsum_ql (Finset.sum_eq_zero (fun j hj => hnone j hj))
          -- `q_l` window membership facts.
          have hql_w : Q * (j : ℕ) < (q_l : ℕ) ∧ (q_l : ℕ) ≤ Q * (j : ℕ) + s :=
            ⟨hwit_lo j q_l hj, hwit_hi j q_l hj⟩
          have hql_a : a_l < (q_l : ℕ) ∧ (q_l : ℕ) ≤ a_l + s := ha_l q_l hq_l
          refine ⟨j, ?_⟩
          -- Pointwise `e l ≤ wit j`.
          have hle_pt : ∀ q : ℕ+, (e l).val q ≤ (wit j).val q := by
            intro q
            by_cases hq0 : (e l).val q = 0
            · rw [hq0]; exact Nat.zero_le _
            -- `q` is in the same width-`s` window as `q_l`.
            have hq_a : a_l < (q : ℕ) ∧ (q : ℕ) ≤ a_l + s := ha_l q hq0
            -- The only nonzero witness at `q` is `wit j`.
            have hsingle : ∑ j' : Fin (n : ℕ), (wit j').val q = (wit j).val q := by
              rw [Finset.sum_eq_single j]
              · intro j' _ hj'ne
                by_contra hj'nz
                have hq_w : Q * (j' : ℕ) < (q : ℕ) ∧ (q : ℕ) ≤ Q * (j' : ℕ) + s :=
                  ⟨hwit_lo j' q hj'nz, hwit_hi j' q hj'nz⟩
                exact hj'ne (Fin.ext (window_index_unique' hQ_ge hq_a hql_a hq_w hql_w))
              · intro hjuniv; exact absurd (Finset.mem_univ _) hjuniv
            -- `e l q ≤ Esum q = Dsum q = wit j q`.
            have hle1 : (e l).val q ≤ ∑ l' : Fin (n : ℕ), (e l').val q :=
              Finset.single_le_sum (f := fun l' => (e l').val q)
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
            calc (e l).val q ≤ ∑ l' : Fin (n : ℕ), (e l').val q := hle1
              _ = ∑ j' : Fin (n : ℕ), (wit j').val q := (hsum_pt q).symm
              _ = (wit j).val q := hsingle
          -- Equal digit sums + pointwise `≤` ⟹ equality.
          exact Sparse.DigitSeries.eq_of_le_of_Psi_eq hle_pt (by rw [he_psi l, hwit_psi j])
        -- Extract the window map `σ`.
        choose σ hσ using he_eq_wit
        -- `σ` is surjective: every window is covered by some `e l`.
        have hσ_surj : Function.Surjective σ := by
          intro j
          by_contra hnot
          push Not at hnot
          -- A nonzero position of `wit j`.
          obtain ⟨q_j, hq_j⟩ : ∃ q : ℕ+, (wit j).val q ≠ 0 := by
            by_contra hall
            push Not at hall
            have : (wit j).val.Psi = 0 := by
              change ∑ q ∈ (wit j).val.fin_supp.toFinset, (wit j).val q = 0
              exact Finset.sum_eq_zero (fun q _ => hall q)
            rw [hwit_psi j] at this; omega
          -- `Esum` vanishes at `q_j` (no `e l` lives in window `j`).
          have hEsum0 : ∑ l : Fin (n : ℕ), (e l).val q_j = 0 := by
            refine Finset.sum_eq_zero (fun l _ => ?_)
            rw [hσ l]
            by_contra hne
            exact hnot l (hwit_disj (σ l) j q_j hne hq_j)
          -- `Dsum` does not vanish at `q_j` (window `j` is nonzero there).
          have hDsum_ne : ∑ j' : Fin (n : ℕ), (wit j').val q_j ≠ 0 := by
            intro hzero
            have hle : (wit j).val q_j ≤ ∑ j' : Fin (n : ℕ), (wit j').val q_j :=
              Finset.single_le_sum (f := fun j' => (wit j').val q_j)
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
            exact hq_j (Nat.le_zero.mp (by omega))
          rw [hsum_pt q_j, hEsum0] at hDsum_ne
          exact hDsum_ne rfl
        -- A surjective endofunction of `Fin n` is bijective.
        have hσ_bij : Function.Bijective σ :=
          (Fintype.bijective_iff_surjective_and_card σ).mpr ⟨hσ_surj, rfl⟩
        let eσ : Equiv.Perm (Fin (n : ℕ)) := Equiv.ofBijective σ hσ_bij
        refine ⟨eσ.symm, ?_⟩
        intro i
        apply Subtype.ext
        change (wit i).val = (e (eσ.symm i)).val
        rw [hσ (eσ.symm i)]
        have hi : σ (eσ.symm i) = i := by
          change eσ (eσ.symm i) = i
          rw [Equiv.apply_symm_apply]
        rw [hi]

/-! ## The ℚ/ℝ derived-set bridge (`lem:derivedset-rat-real`, `lem:infinite-support-has-real-accpt`)

The protected §6.3 statements read accumulation points **in ℝ** (via the inclusion
`ι : ℚ → ℝ`), which is the faithful/sound reading: a bounded infinite well-ordered
`S ⊆ ℚ` can have empty ℚ-derived set (rationals ↑ √2), so only the ℝ-derived set
carries Bolzano–Weierstrass content. These two helpers connect the ℝ-derived set
used in the protected statements to the ℚ-internal ray-decomposition machinery. -/

/-- `lem:derivedset-rat-real`: finiteness of the ℝ-derived set of `ι '' S` (where
`ι = Rat.cast : ℚ → ℝ`) implies finiteness of the ℚ-derived set of `S`. The
inclusion `ι` is a continuous injection, so it sends each ℚ-accumulation point of
`S` to an ℝ-accumulation point of `ι '' S` (`Continuous.image_derivedSet`), giving
an injection `derivedSet S ↪ derivedSet (ι '' S)`; a finite target forces a finite
source. -/
theorem derivedSet_rat_finite_of_real_finite {S : Set ℚ}
    (h : (derivedSet ((Rat.cast : ℚ → ℝ) '' S)).Finite) : (derivedSet S).Finite := by
  have hsub : (Rat.cast : ℚ → ℝ) '' derivedSet S ⊆ derivedSet ((Rat.cast : ℚ → ℝ) '' S) :=
    Continuous.image_derivedSet Rat.continuous_coe_real Rat.cast_injective
  have hfin : ((Rat.cast : ℚ → ℝ) '' derivedSet S).Finite := h.subset hsub
  exact (Set.finite_image_iff (Rat.cast_injective.injOn)).mp hfin

/-- `lem:infinite-support-has-real-accpt`: an infinite bounded `S ⊆ ℚ` has a
nonempty ℝ-derived set of its image `ι '' S` (`ι = Rat.cast`). Boundedness puts
`ι '' S` inside a compact closed ball of ℝ; injectivity keeps the image infinite;
Bolzano–Weierstrass (`Set.Infinite.exists_accPt_of_subset_isCompact`) then yields
an ℝ-accumulation point. -/
theorem real_derivedSet_nonempty_of_infinite_bounded {S : Set ℚ}
    (hinf : S.Infinite) (hbdd : Bornology.IsBounded S) :
    (derivedSet ((Rat.cast : ℚ → ℝ) '' S)).Nonempty := by
  -- `S` sits in a ℚ-closed ball of radius `r`; cast it into ℝ.
  obtain ⟨r, hr⟩ := hbdd.subset_closedBall (0 : ℚ)
  have hsub : (Rat.cast : ℚ → ℝ) '' S ⊆ Metric.closedBall (0 : ℝ) r := by
    rintro _ ⟨q, hq, rfl⟩
    have hq' : dist q (0 : ℚ) ≤ r := by
      have := hr hq; rwa [Metric.mem_closedBall] at this
    rw [Metric.mem_closedBall]
    calc dist (q : ℝ) (0 : ℝ)
        = dist (q : ℝ) ((0 : ℚ) : ℝ) := by norm_num
      _ = dist q (0 : ℚ) := Rat.dist_cast q 0
      _ ≤ r := hq'
  -- The image is infinite (injective cast) and lies in a compact set.
  have hinf' : ((Rat.cast : ℚ → ℝ) '' S).Infinite :=
    (Set.infinite_image_iff (Rat.cast_injective.injOn)).mpr hinf
  obtain ⟨x, _, hx⟩ := hinf'.exists_accPt_of_subset_isCompact
    (ProperSpace.isCompact_closedBall (0 : ℝ) r) hsub
  exact ⟨x, mem_derivedSet.mpr hx⟩

/-! ## Arithmetic helpers for `exists_sparse_rep` (lem:42556)

The sparse-representative construction needs four elementary facts:

* `isInt_eq_zero_of_bounded` — a bounded `Rat.isInt` rational is `0` (uniqueness side of
  `IsRepModZ`);
* `isInt_pow_mul_digitSum` — `p^E` times a finite head digit-value sum is an integer once `E`
  dominates all indices (clears denominators in `T·(q − λ)`);
* `digitSeries_finsupp_model` — a `p`-digit `DigitSeries` is the §6 finsupp digit model that
  `isSparse_deltas`'s `hδ_fin` consumes;
* `ray_pos_slope_of_infinite` — an infinite explicit ray has positive slope (so its `δ` is
  nonzero). -/

/-- A `Rat.isInt` rational strictly between `-1` and `1` is `0`. -/
private lemma isInt_eq_zero_of_bounded {x : ℚ} (hx : x.isInt = true)
    (h1 : (-1 : ℚ) < x) (h2 : x < 1) : x = 0 := by
  have hnum : x = (x.num : ℚ) := Rat.eq_num_of_isInt hx
  rw [hnum] at h1 h2 ⊢
  have h1' : (-1 : ℤ) < x.num := by exact_mod_cast h1
  have h2' : x.num < (1 : ℤ) := by exact_mod_cast h2
  rw [show x.num = 0 by omega]; simp

/-- `Rat.isInt` of an integer cast. -/
private lemma isInt_intCast' (k : ℤ) : ((k : ℚ)).isInt = true := by rw [Rat.isInt]; simp

/-- `Rat.isInt` is closed under addition. -/
private lemma isInt_add' {a b : ℚ} (ha : a.isInt = true) (hb : b.isInt = true) :
    (a + b).isInt = true := by
  have ha' := Rat.eq_num_of_isInt ha; have hb' := Rat.eq_num_of_isInt hb
  rw [ha', hb', show (a.num : ℚ) + (b.num : ℚ) = ((a.num + b.num : ℤ) : ℚ) by push_cast; ring]
  exact isInt_intCast' _

/-- `Rat.isInt` is closed under subtraction. -/
private lemma isInt_sub' {a b : ℚ} (ha : a.isInt = true) (hb : b.isInt = true) :
    (a - b).isInt = true := by
  have ha' := Rat.eq_num_of_isInt ha; have hb' := Rat.eq_num_of_isInt hb
  rw [ha', hb', show (a.num : ℚ) - (b.num : ℚ) = ((a.num - b.num : ℤ) : ℚ) by push_cast; ring]
  exact isInt_intCast' _

/-- `p^E · ∑ᵢ cᵢ·p^{-(i+1)}` is an integer once `E` dominates every index `i` (i.e. `i+1 ≤ E`).
This clears the finite-expansion denominators when multiplying `q − λ` by `T = a·p^E`. -/
private lemma isInt_pow_mul_digitSum {p : ℕ} [Fact (Nat.Prime p)] (F : Finset ℕ)
    (c : ℕ → ℕ) (E : ℕ) (hE : ∀ i ∈ F, i + 1 ≤ E) :
    ((p : ℚ) ^ E * ∑ i ∈ F, (c i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))).isInt = true := by
  rw [Finset.mul_sum]
  refine Finset.sum_induction _ (fun y : ℚ => y.isInt = true) (fun _ _ => isInt_add') ?_ ?_
  · rw [show (0 : ℚ) = ((0 : ℤ) : ℚ) by simp]; exact isInt_intCast' 0
  · intro i hi
    have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have hEi : i + 1 ≤ E := hE i hi
    have hkey : (p : ℚ) ^ E * ((c i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
        = (c i : ℚ) * (p : ℚ) ^ ((E : ℤ) - (i + 1 : ℤ)) := by
      rw [← zpow_natCast (p : ℚ) E, ← mul_assoc, mul_comm ((p : ℚ) ^ (E : ℤ)) (c i : ℚ), mul_assoc,
          ← zpow_add₀ hpne]
      ring_nf
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (E : ℤ) - (i + 1 : ℤ) = (k : ℤ) := by
      refine ⟨(E - (i + 1) : ℕ), ?_⟩
      have : (i + 1 : ℕ) ≤ E := hEi
      omega
    rw [hkey, hk, zpow_natCast,
      show (c i : ℚ) * (p : ℚ) ^ k = (((c i * p ^ k : ℕ) : ℤ) : ℚ) by push_cast; ring]
    exact isInt_intCast' _

/-- A `p`-digit `DigitSeries` `g` is the §6 finsupp digit model: there is `d : ℕ →₀ ℕ` with
`d j < p` for all `j` and `g.norm p = ∑ⱼ d j · p^{-(j+1)}` — the exact shape `isSparse_deltas`'s
`hδ_fin` consumes. -/
private lemma digitSeries_finsupp_model {p : ℕ} [Fact (Nat.Prime p)] (g : Sparse.DigitSeries)
    (hg : g.IsP p) :
    ∃ d : ℕ →₀ ℕ, (∀ j, d j < p) ∧
      g.norm p = d.sum fun j v => (v : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ)) := by
  classical
  set d : ℕ →₀ ℕ := Finsupp.onFinset (g.fin_supp.toFinset.image PNat.natPred)
    (fun j => g (Nat.succPNat j)) (by
      intro j hj
      simp only [Finset.mem_image, Set.Finite.mem_toFinset, Function.mem_support, ne_eq]
      exact ⟨Nat.succPNat j, by simpa using hj, by simp⟩) with hd_def
  have hd_apply : ∀ j, d j = g (Nat.succPNat j) := fun j => Finsupp.onFinset_apply
  have hg_eq : g = Sparse.DigitSeries.ofFinsupp d := by
    apply DFunLike.ext
    intro q
    rw [Sparse.DigitSeries.ofFinsupp_apply, hd_apply, PNat.succPNat_natPred]
  refine ⟨d, fun j => by rw [hd_apply]; exact hg _, ?_⟩
  conv_lhs => rw [hg_eq]
  rw [Sparse.DigitSeries.ofFinsupp_norm]

open Sparse in
/-- An infinite explicit base-`P` ray has positive slope `(1/a)·tail`.  If the tail digit-value mass
at or above `P` were zero, every ray element would equal the single limit point `α`
(`ray_enc_affine`), making the ray a singleton — contradicting infiniteness. -/
private lemma ray_pos_slope_of_infinite {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {m : ℤ} {N : ℕ+}
    (d_base : ℕ →₀ ℕ) (P : ℕ) (R : Set ℚ)
    (hReq : R = { q : ℚ | ∃ k : ℕ, q = (1 / (a : ℚ)) * ((m : ℚ) -
        (Finsupp.mapDomain (fun i => if i < P then i else i + k * (N : ℕ)) d_base).sum
          fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) })
    (hinf : R.Infinite) :
    (0 : ℚ) < (1 / (a : ℚ)) *
      ∑ i ∈ d_base.support.filter (fun i => P ≤ i), (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
  set lam : ℚ := (1 / (a : ℚ)) *
    ∑ i ∈ d_base.support.filter (fun i => P ≤ i),
      (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) with hlamdef
  rcases eq_or_lt_of_le (show (0 : ℚ) ≤ lam by
    rw [hlamdef]
    have hinva : (0 : ℚ) < 1 / (a : ℚ) := by
      have : (0 : ℚ) < a := by exact_mod_cast a.pos
      positivity
    have hsum_nonneg : 0 ≤ ∑ i ∈ d_base.support.filter (fun i => P ≤ i),
        (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
      apply Finset.sum_nonneg; intro i _; positivity
    positivity) with hlam0 | hlampos
  · -- `lam = 0` ⟹ `R = {α}`, contradicting infinite.
    exfalso
    set α : ℚ := (1 / (a : ℚ)) * ((m : ℚ) -
      ∑ i ∈ d_base.support.filter (fun i => i < P), (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      with hαdef
    have hR_eq : R = {α} := by
      rw [hReq]; ext q
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨k, rfl⟩
        rw [ray_enc_affine d_base P k, ← hαdef, ← hlamdef, ← hlam0, mul_zero, sub_zero]
      · rintro rfl
        exact ⟨0, by
          rw [ray_enc_affine d_base P 0, ← hαdef, ← hlamdef, ← hlam0, mul_zero, sub_zero]⟩
    rw [hR_eq] at hinf
    exact hinf (Set.finite_singleton α)
  · exact hlampos

/-- The residue identity at the heart of `lem:42556` (`lam = 0`).  With `T = a·p^E` and shift
`N·K − E ≥ 0`, the `j`-th survivor `q = enc(j+K)` of an explicit ray satisfies
`−1·T·(q − 0) − δ·p^{−Nj} = −p^E·(m − head)`, manifestly an integer (`head` = the below-`P`
digit-value mass, `δ = tail·p^{−(NK−E)}`).  This is `ray_enc_affine` plus `p`-power bookkeeping. -/
private lemma residue_identity {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {m : ℤ} {N : ℕ+}
    (d_base : ℕ →₀ ℕ) (E K j : ℕ) (P : ℕ) (hNKge : E ≤ (N : ℕ) * K) :
    -1 * ((a : ℚ) * (p : ℚ) ^ E) *
        ((1 / (a : ℚ)) * ((m : ℚ) -
          (Finsupp.mapDomain (fun ii => if ii < P then ii else ii + (j + K) * (N : ℕ)) d_base).sum
            fun ii v => (v : ℚ) * (p : ℚ) ^ (-(ii + 1 : ℤ))) - 0)
      - (∑ i ∈ d_base.support.filter (fun i => P ≤ i), (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
          * (p : ℚ) ^ (-(((N : ℕ) * K - E : ℕ)) : ℤ) * (p : ℚ) ^ (-(N : ℤ) * j)
      = -((p : ℚ) ^ E * ((m : ℚ) -
          ∑ i ∈ d_base.support.filter (fun i => i < P),
            (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))) := by
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hane : (a : ℚ) ≠ 0 := by exact_mod_cast a.pos.ne'
  set head : ℚ := ∑ i ∈ d_base.support.filter (fun i => i < P),
    (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) with hh
  set tail : ℚ := ∑ i ∈ d_base.support.filter (fun i => P ≤ i),
    (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) with ht
  rw [ray_enc_affine d_base P (j + K), ← hh, ← ht]
  rw [show ((p : ℚ) ^ (-(N : ℤ))) ^ (j + K) = (p : ℚ) ^ (-(N : ℤ) * ((j : ℤ) + (K : ℤ))) by
        rw [← zpow_natCast ((p : ℚ) ^ (-(N : ℤ))) (j + K), ← zpow_mul]; push_cast; ring_nf]
  rw [show (-(((N : ℕ) * K - E : ℕ)) : ℤ) = (E : ℤ) - (N : ℤ) * K by
        push_cast [Nat.cast_sub hNKge]; ring]
  rw [← zpow_natCast (p : ℚ) E]
  -- The single power-merge fact; the rest is a pure `ring`/`linear_combination` identity.
  have hmerge : (p : ℚ) ^ (E : ℤ) * (p : ℚ) ^ (-(N : ℤ) * ((j : ℤ) + (K : ℤ)))
      = (p : ℚ) ^ ((E : ℤ) - (N : ℤ) * K) * (p : ℚ) ^ (-(N : ℤ) * j) := by
    rw [← zpow_add₀ hpne, ← zpow_add₀ hpne]; congr 1; ring
  rw [eq_neg_iff_add_eq_zero]
  field_simp
  linear_combination (tail) * hmerge

open Sparse in
/-- `lem:42556`: bounded QTR support has a sparse representative set mod ℤ.
Let `f : 𝕃_[p]` be `ℚᵘⁿ_[p]`-algebraic with bounded support admitting finitely many
but at least one accumulation point. Then there exist `S' ⊆ f.support`, `lam : ℚ`,
`T : ℕ+`, and a set `W` such that `f.support \ S'` is finite and `-T(S'-lam)` has a
sparse nonzero set `W` of representatives mod ℤ.

P4 ALIGNMENT (do not reshape the representative set): the argument
`{ -1·T·(q-lam) | q ∈ S' }` is exactly `-T(S'-lam)`, and equals
`{ -1·T·q' | q' ∈ (S'-lam) }` — the shape `main_theorem`'s
`hf2 : IsRepModZ W {-1*T*q | q ∈ f.support}` expects when applied to the shifted
series `f₁·p^{-lam}` (whose support is `S'-lam`). Keep this exact set-builder so the
prover plugs into `main_theorem` without a rewrite. -/
theorem exists_sparse_rep {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p])
    (halg : IsAlgebraic ℚᵘⁿ_[p] f) (hbdd : Bornology.IsBounded f.support)
    (hacc_fin : (derivedSet ((Rat.cast : ℚ → ℝ) '' f.support)).Finite)
    (hacc_ne : (derivedSet ((Rat.cast : ℚ → ℝ) '' f.support)).Nonempty) :
    ∃ (S' : Set ℚ) (lam : ℚ) (T : ℕ+) (W : Set ℚ),
      S' ⊆ f.support ∧ (f.support \ S').Finite ∧
      W ≠ {0} ∧ IsSparse p W ∧
      IsRepModZ W { x : ℚ | ∃ q ∈ S', x = -1 * (T : ℚ) * (q - lam) } := by
  -- Bridge the ℝ-derived-set hypotheses to the ℚ-internal form the ray layer
  -- consumes: `hacc_fin` (ℝ) ⟹ ℚ-derived set finite (`lem:derivedset-rat-real`).
  have hacc_fin_Q : (derivedSet f.support).Finite :=
    derivedSet_rat_finite_of_real_finite hacc_fin
  -- By prop:167 (`isQTR_of_isAlgebraic_of_bddSupport`), `f.coeff` is QTR for some
  -- `a,b,c,M,N`.
  obtain ⟨a, b, c, M, N, hqtr⟩ := isQTR_of_isAlgebraic_of_bddSupport f halg hbdd
  -- `qtr_ray_decomposition` (coro:48108) writes `f.support = E ⊔ ⨆ rays` with `E` finite
  -- and finitely many pairwise-disjoint rays, each carrying its admissibility data.
  obtain ⟨E, rays, hrays_data, hrays_disj, hsupp_eq⟩ :=
    qtr_ray_decomposition hqtr hbdd hacc_fin_Q
  -- REMAINING (deep §6.3 core, blueprint `lem:42556`): from the ray decomposition build the
  -- sparse representative set.  We take `lam = 0`: since `T = a·p^E` clears every finite-expansion
  -- denominator, `T·α_l` is already an integer, so the residue `-T·q ≡ δ_l p^{-Nj} (mod ℤ)` needs
  -- no reference point.  Each *infinite* ray `R_l` has positive slope
  -- (`ray_pos_slope_of_infinite`),
  -- giving a nonzero `δ_l = tail_l·p^{-(NK-E)} ∈ (0,1)` with a finite base-`p` expansion; deleting
  -- the first `K = E` points of each infinite ray gives `S'` (a finite deletion plus the finite/
  -- degenerate rays and `↑E`), and `isSparse_deltas` (lem:57121) yields the sparse `W`.
  classical
  -- `f.support` is infinite (the ℝ-derived set is nonempty ⟹ image infinite ⟹ support infinite).
  have hsupp_inf : f.support.Infinite := by
    obtain ⟨x, hx⟩ := hacc_ne
    rw [mem_derivedSet] at hx
    exact (Set.Infinite.of_accPt hx).of_image _
  -- The *infinite* rays; index them by `Fin s`.
  set infRays : Finset (Set ℚ) := rays.filter (fun R => R.Infinite) with hinfRays
  set s : ℕ := infRays.card with hs_def
  set e : Fin s ≃ infRays := (infRays.equivFin).symm with he_def
  -- At least one infinite ray (since `f.support = ↑E ∪ rays.sup id` is infinite, `↑E` finite).
  have hs_pos : 0 < s := by
    rw [hs_def, Finset.card_pos]
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, hinfRays] at hcon
    have hfin : (rays.sup id).Finite := by
      rw [Finset.sup_set_eq_biUnion]
      apply Set.Finite.biUnion rays.finite_toSet
      intro R hR
      by_contra hRinf
      have : R ∈ rays.filter (fun R => R.Infinite) := Finset.mem_filter.mpr ⟨hR, hRinf⟩
      rw [hcon] at this; exact absurd this (Finset.notMem_empty R)
    exact hsupp_inf (by
      change (Function.support f.coeff).Finite
      rw [hsupp_eq]; exact E.finite_toSet.union hfin)
  -- Per-ray explicit data (base finsupp, threshold, digit/sum bounds, explicit set form).
  have hdata : ∀ i : Fin s, ∃ (m : ℤ) (d_base : ℕ →₀ ℕ) (P : ℕ),
      (∀ j, d_base j < p) ∧ (d_base.sum fun _ v => v) ≤ c ∧
      (e i).val = { q : ℚ | ∃ k : ℕ, q = (1 / (a : ℚ)) * ((m : ℚ) -
        (Finsupp.mapDomain (fun ii => if ii < P then ii else ii + k * (N : ℕ)) d_base).sum
          fun ii v => (v : ℚ) * (p : ℚ) ^ (-(ii + 1 : ℤ))) } := by
    intro i
    have hmem : (e i).val ∈ rays ∧ (e i).val.Infinite := Finset.mem_filter.mp (e i).property
    obtain ⟨m, hm, hray, _hadm⟩ := hrays_data (e i).val hmem.1
    obtain ⟨_hRS, d_base, P, hdig, hsum, hReq⟩ := hray
    exact ⟨m, d_base, P, hdig, hsum, hReq⟩
  choose mR dR PR hdigR _hsumR hReqR using hdata
  -- Each infinite ray has positive slope `(1/a)·tail_l`.
  have hslopeR : ∀ i : Fin s, (0 : ℚ) < (1 / (a : ℚ)) *
      ∑ j ∈ (dR i).support.filter (fun j => PR i ≤ j),
        (dR i j : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ)) := by
    intro i
    have hmem : (e i).val ∈ rays ∧ (e i).val.Infinite := Finset.mem_filter.mp (e i).property
    exact ray_pos_slope_of_infinite (dR i) (PR i) (e i).val (hReqR i) hmem.2
  -- The exponent `E` dominating every digit index of every ray (clears all denominators).
  set Edeg : ℕ := (Finset.univ.sup fun i : Fin s => (dR i).support.sup id) + 1 with hEdeg_def
  have hEdom : ∀ i : Fin s, ∀ j ∈ (dR i).support, j + 1 ≤ Edeg := by
    intro i j hj
    have h1 : j ≤ (dR i).support.sup id := Finset.le_sup (f := id) hj
    have h2 : (dR i).support.sup id ≤ Finset.univ.sup fun i : Fin s => (dR i).support.sup id :=
      Finset.le_sup (f := fun i : Fin s => (dR i).support.sup id) (Finset.mem_univ i)
    omega
  -- `T = a · p^{Edeg}` and `K = Edeg` (so the shift `N·K − E = (N−1)·E ≥ 0`).
  set pp : ℕ+ := ⟨p, (Fact.out : Nat.Prime p).pos⟩ with hpp_def
  set T : ℕ+ := a * pp ^ Edeg with hT_def
  have hT_val : (T : ℚ) = (a : ℚ) * (p : ℚ) ^ Edeg := by
    rw [hT_def]
    have hcp : ((pp : ℕ) : ℚ) = (p : ℚ) := by rw [hpp_def]; rfl
    push_cast [hcp]
    ring
  set Kdel : ℕ := Edeg with hKdel_def
  have hNKge : Edeg ≤ (N : ℕ) * Kdel := by
    rw [hKdel_def]; nlinarith [N.pos, Edeg]
  -- The shift amount per ray (constant here: `N·K − E`).
  set msh : ℕ := (N : ℕ) * Kdel - Edeg with hmsh_def
  -- The tail digit block `B_l` and the deltas `δ_l = tail_l · p^{-msh}`.
  set BR : Fin s → Sparse.DigitSeries := fun i =>
    Sparse.DigitSeries.ofFinsupp (Finsupp.filter (fun j => PR i ≤ j) (dR i)) with hBR_def
  have hBR_isP : ∀ i, (BR i).IsP p := by
    intro i; apply Sparse.DigitSeries.ofFinsupp_isP
    intro j; rw [Finsupp.filter_apply]; split_ifs
    · exact hdigR i j
    · exact (Fact.out : Nat.Prime p).pos
  have hBR_norm : ∀ i, (BR i).norm p =
      ∑ j ∈ (dR i).support.filter (fun j => PR i ≤ j),
        (dR i j : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ)) := by
    intro i; rw [hBR_def]; simp only
    rw [Sparse.DigitSeries.ofFinsupp_norm, Finsupp.sum, Finsupp.support_filter]
    apply Finset.sum_congr rfl
    intro j hj; rw [Finset.mem_filter] at hj; rw [Finsupp.filter_apply, if_pos hj.2]
  have hBR_norm_pos : ∀ i, 0 < (BR i).norm p := by
    intro i; rw [hBR_norm i]
    have hane : (0 : ℚ) < 1 / (a : ℚ) := by
      have : (0 : ℚ) < a := by exact_mod_cast a.pos
      positivity
    nlinarith [hslopeR i]
  set gR : Fin s → Sparse.DigitSeries := fun i => Sparse.DigitSeries.shiftBy (BR i) msh with hgR_def
  have hgR_isP : ∀ i, (gR i).IsP p :=
    fun i => Sparse.DigitSeries.shiftBy_isP p (BR i) msh (hBR_isP i)
  set δ : Fin s → ℚ := fun i => (gR i).norm p with hδ_def
  have hδ_val : ∀ i, δ i = (BR i).norm p * (p : ℚ) ^ (-(msh : ℤ)) :=
    fun i => Sparse.DigitSeries.norm_shiftBy p (BR i) msh
  have hδ_mem : ∀ i, δ i ∈ Set.Ico (0 : ℚ) 1 :=
    fun i => Sparse.DigitSeries.norm_mem_Ico p (gR i) (hgR_isP i)
  have hδ_ne : ∀ i, δ i ≠ 0 := by
    intro i; rw [hδ_val i]
    have h1 := hBR_norm_pos i
    have h2 : (0 : ℚ) < (p : ℚ) ^ (-(msh : ℤ)) := by
      have : (0 : ℚ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).pos
      positivity
    positivity
  have hδ_fin : ∀ i, ∃ d : ℕ →₀ ℕ, (∀ j, d j < p) ∧
      δ i = d.sum fun j v => (v : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ)) :=
    fun i => digitSeries_finsupp_model (gR i) (hgR_isP i)
  -- The sparse set `W` and its sparseness (`isSparse_deltas`, lem:57121).
  set W : Set ℚ := { w : ℚ | ∃ (i : Fin s) (k : ℕ), w = δ i * (p : ℚ) ^ (-(N : ℤ) * k) } with hW_def
  have hW_sparse : IsSparse p W := isSparse_deltas N s hs_pos δ hδ_mem hδ_ne hδ_fin
  have hW_ne : W ≠ {0} := by
    intro hEq
    have hmem : δ ⟨0, hs_pos⟩ ∈ W := ⟨⟨0, hs_pos⟩, 0, by simp⟩
    rw [hEq, Set.mem_singleton_iff] at hmem
    exact hδ_ne ⟨0, hs_pos⟩ hmem
  -- The encoding map and the survivor set `S'` (delete the first `Kdel` points of each ray).
  set enc : Fin s → ℕ → ℚ := fun i k => (1 / (a : ℚ)) * ((mR i : ℚ) -
      (Finsupp.mapDomain (fun ii => if ii < PR i then ii else ii + k * (N : ℕ)) (dR i)).sum
        fun ii v => (v : ℚ) * (p : ℚ) ^ (-(ii + 1 : ℤ))) with henc_def
  set S' : Set ℚ := { x : ℚ | ∃ (i : Fin s) (j : ℕ), x = enc i (j + Kdel) } with hS'_def
  -- `S' ⊆ f.support` (each survivor lies in its ray, hence in the support).
  have hS'sub : S' ⊆ f.support := by
    rw [hS'_def]
    rintro x ⟨i, j, rfl⟩
    have hxR : enc i (j + Kdel) ∈ (e i).val := by rw [hReqR i]; exact ⟨j + Kdel, rfl⟩
    have hRmem : (e i).val ∈ rays := (Finset.mem_filter.mp (e i).property).1
    change enc i (j + Kdel) ∈ Function.support f.coeff
    rw [hsupp_eq]; right
    rw [Finset.sup_set_eq_biUnion]; simp only [Set.mem_iUnion, id_eq]
    exact ⟨(e i).val, hRmem, hxR⟩
  -- `f.support \ S'` is finite (`↑E` ∪ finite/degenerate rays ∪ the deleted heads).
  have hdiff_fin : (f.support \ S').Finite := by
    set finRaysU : Set ℚ := (rays.filter (fun R => ¬ R.Infinite)).sup id with hfinRaysU
    have hfinRaysU_fin : finRaysU.Finite := by
      rw [hfinRaysU, Finset.sup_set_eq_biUnion]
      apply Set.Finite.biUnion (Finset.finite_toSet _)
      intro R hR; rw [Finset.mem_coe, Finset.mem_filter] at hR
      exact Set.not_infinite.mp hR.2
    set heads : Set ℚ := { x : ℚ | ∃ (i : Fin s) (k : ℕ), k < Kdel ∧ x = enc i k } with hheads
    have hheads_fin : heads.Finite := by
      apply Set.Finite.subset
        (Set.finite_iUnion (fun i : Fin s =>
          (Finset.finite_toSet ((Finset.range Kdel).image (enc i)))))
      rintro x ⟨i, k, hk, rfl⟩
      simp only [Set.mem_iUnion, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      exact ⟨i, k, hk, rfl⟩
    apply Set.Finite.subset (((E.finite_toSet).union hfinRaysU_fin).union hheads_fin)
    intro x hx
    obtain ⟨hxsupp, hxnS'⟩ := hx
    change x ∈ Function.support f.coeff at hxsupp
    rw [hsupp_eq] at hxsupp
    rcases hxsupp with hxE | hxray
    · exact Or.inl (Or.inl hxE)
    · rw [Finset.sup_set_eq_biUnion] at hxray
      simp only [Set.mem_iUnion, id_eq] at hxray
      obtain ⟨R, hRmem, hxR⟩ := hxray
      by_cases hRinf : R.Infinite
      · obtain ⟨i, hi⟩ : ∃ i : Fin s, (e i).val = R := by
          have hRinfRays : R ∈ infRays := Finset.mem_filter.mpr ⟨hRmem, hRinf⟩
          exact ⟨e.symm ⟨R, hRinfRays⟩, by rw [Equiv.apply_symm_apply]⟩
        rw [← hi, hReqR i] at hxR
        obtain ⟨k, hk⟩ := hxR
        change x = enc i k at hk
        by_cases hkK : Kdel ≤ k
        · exact absurd ⟨i, k - Kdel, by rw [hk]; congr 1; omega⟩ hxnS'
        · exact Or.inr ⟨i, k, by omega, hk⟩
      · refine Or.inl (Or.inr ?_)
        rw [hfinRaysU, Finset.sup_set_eq_biUnion]
        simp only [Set.mem_iUnion, id_eq]
        exact ⟨R, Finset.mem_filter.mpr ⟨hRmem, hRinf⟩, hxR⟩
  -- The residue identity: `-1·T·(enc i (j+K) − 0) − δ_i p^{-Nj}` is an integer
  -- (`= -p^E(m_i − head_i)`).
  have hres : ∀ (i : Fin s) (j : ℕ),
      (-1 * (T : ℚ) * (enc i (j + Kdel) - 0) - δ i * (p : ℚ) ^ (-(N : ℤ) * j)).isInt = true := by
    intro i j
    set head : ℚ := ∑ ii ∈ (dR i).support.filter (fun ii => ii < PR i),
      (dR i ii : ℚ) * (p : ℚ) ^ (-(ii + 1 : ℤ)) with hhead_def
    have hkey : -1 * (T : ℚ) * (enc i (j + Kdel) - 0) - δ i * (p : ℚ) ^ (-(N : ℤ) * j)
        = -((p : ℚ) ^ Edeg * ((mR i : ℚ) - head)) := by
      rw [hT_val, hδ_val i, hBR_norm i, henc_def, hmsh_def, hhead_def]
      exact residue_identity (dR i) Edeg Kdel j (PR i) hNKge
    rw [hkey]
    rw [show ∀ x : ℚ, (-x).isInt = x.isInt from fun x => by
          rw [Rat.isInt, Rat.isInt, Rat.neg_den]]
    rw [mul_sub]
    apply isInt_sub'
    · rw [show (p : ℚ) ^ Edeg * (mR i : ℚ) = (((p ^ Edeg : ℕ) : ℤ) * mR i : ℤ) by push_cast; ring]
      exact isInt_intCast' _
    · rw [hhead_def]
      apply isInt_pow_mul_digitSum
      intro ii hii
      rw [Finset.mem_filter] at hii
      exact hEdom i ii hii.1
  -- Assemble `IsRepModZ W { -1·T·(q − 0) | q ∈ S' }`, with `lam = 0`.
  refine ⟨S', 0, T, W, hS'sub, hdiff_fin, hW_ne, hW_sparse, ?_⟩
  have hp1 : (1 : ℚ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hppos : (0 : ℚ) < p := by linarith
  -- Each `W`-element lies in `[0,1)` (uniqueness side of `IsRepModZ`).
  have hW_Ico : ∀ w ∈ W, w ∈ Set.Ico (0 : ℚ) 1 := by
    rintro w ⟨i, k, rfl⟩
    have hδm := hδ_mem i
    have hpk_pos : (0 : ℚ) < (p : ℚ) ^ (-(N : ℤ) * k) := by positivity
    have hpk_le : (p : ℚ) ^ (-(N : ℤ) * k) ≤ 1 := by
      apply zpow_le_one_of_nonpos₀ (by linarith)
      have : (0 : ℤ) ≤ (N : ℤ) * k := by positivity
      linarith [this]
    refine ⟨by have := hδm.1; positivity, ?_⟩
    calc δ i * (p : ℚ) ^ (-(N : ℤ) * k) ≤ δ i * 1 := mul_le_mul_of_nonneg_left hpk_le hδm.1
      _ = δ i := by ring
      _ < 1 := hδm.2
  constructor
  · -- `∀ b ∈ B, ∃! a ∈ W, (a − b).isInt`.
    rintro b ⟨q, ⟨i, j, rfl⟩, rfl⟩
    refine ⟨δ i * (p : ℚ) ^ (-(N : ℤ) * j), ⟨⟨i, j, rfl⟩, ?_⟩, ?_⟩
    · rw [show δ i * (p : ℚ) ^ (-(N : ℤ) * j) - (-1 * (T : ℚ) * (enc i (j + Kdel) - 0))
            = -((-1 * (T : ℚ) * (enc i (j + Kdel) - 0)) - δ i * (p : ℚ) ^ (-(N : ℤ) * j)) by ring]
      rw [show ∀ x : ℚ, (-x).isInt = x.isInt from fun x => by
            rw [Rat.isInt, Rat.isInt, Rat.neg_den]]
      exact hres i j
    · rintro a' ⟨⟨i', k', rfl⟩, ha'⟩
      have ha : (δ i * (p : ℚ) ^ (-(N : ℤ) * j)
          - (-1 * (T : ℚ) * (enc i (j + Kdel) - 0))).isInt = true := by
        rw [show δ i * (p : ℚ) ^ (-(N : ℤ) * j) - (-1 * (T : ℚ) * (enc i (j + Kdel) - 0))
              = -((-1 * (T : ℚ) * (enc i (j + Kdel) - 0)) - δ i * (p : ℚ) ^ (-(N : ℤ) * j)) by ring]
        rw [show ∀ x : ℚ, (-x).isInt = x.isInt from fun x => by
              rw [Rat.isInt, Rat.isInt, Rat.neg_den]]
        exact hres i j
      have hdiff : (δ i' * (p : ℚ) ^ (-(N : ℤ) * k') - δ i * (p : ℚ) ^ (-(N : ℤ) * j)).isInt
          = true := by
        rw [show δ i' * (p : ℚ) ^ (-(N : ℤ) * k') - δ i * (p : ℚ) ^ (-(N : ℤ) * j)
              = (δ i' * (p : ℚ) ^ (-(N : ℤ) * k') - (-1 * (T : ℚ) * (enc i (j + Kdel) - 0)))
                - (δ i * (p : ℚ) ^ (-(N : ℤ) * j) - (-1 * (T : ℚ) * (enc i (j + Kdel) - 0)))
              by ring]
        exact isInt_sub' ha' ha
      have hm1 := hW_Ico _ (⟨i', k', rfl⟩ : δ i' * (p : ℚ) ^ (-(N : ℤ) * k') ∈ W)
      have hm2 := hW_Ico _ (⟨i, j, rfl⟩ : δ i * (p : ℚ) ^ (-(N : ℤ) * j) ∈ W)
      have hz := isInt_eq_zero_of_bounded hdiff
        (by linarith [hm1.1, hm2.2]) (by linarith [hm1.2, hm2.1])
      linarith [hz]
  · -- `∀ a ∈ W, ∃ b ∈ B, (a − b).isInt`.
    rintro a ⟨i, k, rfl⟩
    refine ⟨-1 * (T : ℚ) * (enc i (k + Kdel) - 0), ⟨enc i (k + Kdel), ⟨i, k, rfl⟩, rfl⟩, ?_⟩
    rw [show δ i * (p : ℚ) ^ (-(N : ℤ) * k) - (-1 * (T : ℚ) * (enc i (k + Kdel) - 0))
          = -((-1 * (T : ℚ) * (enc i (k + Kdel) - 0)) - δ i * (p : ℚ) ^ (-(N : ℤ) * k)) by ring]
    rw [show ∀ x : ℚ, (-x).isInt = x.isInt from fun x => by
          rw [Rat.isInt, Rat.isInt, Rat.neg_den]]
    exact hres i k

-- thm:29075
open Bornology in
/-- Support-split helper for `thm:29075`.  Given `f : 𝕃_[p]` and a set `S' ⊆ f.support`
whose complement `f.support \ S'` is finite, splits `f = f_good + f_bad` along the
partition, where `f_good` carries the coefficients on `f.support ∩ S'` (its support is
exactly `f.support ∩ S' = S'`, since `S' ⊆ f.support`) and `f_bad` carries the finite
remainder.  Built at the lift level (`LiftedPAdicHahnSeries.from_coeff` + the quotient
map by `NullSeriesIdeal`) since the canonical-expansion `coeff` is not additive — this
mirrors the (now-archived) `Application.lean` decomposition but uses only public API. -/
private theorem support_split_decomp {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p])
    (S' : Set ℚ) (hS'sub : S' ⊆ f.support) (hdiff_fin : (f.support \ S').Finite) :
    ∃ (f_good f_bad : 𝕃_[p]),
      f = f_good + f_bad ∧ f_good.support = S' ∧ f_bad.support.Finite := by
  classical
  -- The "good" (sparse) part lives on `S'`, the "bad" (finite) part on `f.support \ S'`.
  set Gset : Set ℚ := S' with hGset_def
  set Bset : Set ℚ := f.support \ S' with hBset_def
  -- Coefficient functions of the two parts.
  set s_good : ℚ → Fpbar p := fun q => if q ∈ Gset then f.coeff q else 0 with hsgood
  set s_bad : ℚ → Fpbar p := fun q => if q ∈ Bset then f.coeff q else 0 with hsbad
  -- Support containments.
  have hs_good_sub : Function.support s_good ⊆ Gset := by
    intro q hq
    simp only [Function.mem_support, ne_eq, s_good] at hq
    by_contra hnot; rw [if_neg hnot] at hq; exact hq rfl
  have hs_bad_sub : Function.support s_bad ⊆ Bset := by
    intro q hq
    simp only [Function.mem_support, ne_eq, s_bad] at hq
    by_contra hnot; rw [if_neg hnot] at hq; exact hq rfl
  -- PWO-ness of the two coefficient supports.
  have hG_pwo : Gset.IsPWO := by
    have : Gset ⊆ f.support := hS'sub
    exact (support_IsPWO f).mono this
  have hB_pwo : Bset.IsPWO := hdiff_fin.isPWO
  have hs_good_pwo : (Function.support s_good).IsPWO := hG_pwo.mono hs_good_sub
  have hs_bad_pwo : (Function.support s_bad).IsPWO := hB_pwo.mono hs_bad_sub
  -- The two parts.
  set f_good : 𝕃_[p] := pAdicHahnSeries.from_coeff s_good hs_good_pwo with hfgood
  set f_bad : 𝕃_[p] := pAdicHahnSeries.from_coeff s_bad hs_bad_pwo with hfbad
  have hf_good_coeff : f_good.coeff = s_good :=
    pAdicHahnSeries.coeff_of_from_coeff_eq_self s_good hs_good_pwo
  have hf_bad_coeff : f_bad.coeff = s_bad :=
    pAdicHahnSeries.coeff_of_from_coeff_eq_self s_bad hs_bad_pwo
  -- `f_bad` has finite support.
  have hf_bad_supp : f_bad.support ⊆ Bset := by
    change Function.support f_bad.coeff ⊆ Bset
    rw [hf_bad_coeff]; exact hs_bad_sub
  have hf_bad_supp_fin : f_bad.support.Finite := hdiff_fin.subset hf_bad_supp
  -- `f_good` has support exactly `S'` (since `S' ⊆ f.support`, every point of `S'`
  -- carries a nonzero coefficient of `f`).
  have hf_good_supp : f_good.support = S' := by
    change Function.support f_good.coeff = S'
    rw [hf_good_coeff]
    ext q
    simp only [Function.mem_support, ne_eq, s_good]
    by_cases hq : q ∈ Gset
    · rw [if_pos hq]
      refine ⟨fun _ => hq, fun _ hc => ?_⟩
      -- `q ∈ S' ⊆ f.support`, so `f.coeff q ≠ 0`.
      have : q ∈ f.support := hS'sub hq
      exact this hc
    · rw [if_neg hq]
      simp only [not_true_eq_false, false_iff]
      exact fun h => hq h
  -- Decomposition `f = f_good + f_bad`, proved at the lift level then projected.
  have hf_decomp : f = f_good + f_bad := by
    have hL_eq :
        LiftedPAdicHahnSeries.from_coeff s_good hs_good_pwo +
          LiftedPAdicHahnSeries.from_coeff s_bad hs_bad_pwo =
        LiftedPAdicHahnSeries.from_coeff f.coeff (support_IsPWO f) := by
      apply HahnSeries.ext
      funext q
      change (WittVector.teichmuller p) (s_good q) + (WittVector.teichmuller p) (s_bad q) =
        (WittVector.teichmuller p) (f.coeff q)
      by_cases hq_good : q ∈ Gset
      · have hq_bad : q ∉ Bset := by
          rw [hBset_def]; intro hb; exact hb.2 hq_good
        have hs_g : s_good q = f.coeff q := by simp [s_good, hq_good]
        have hs_b : s_bad q = 0 := by simp [s_bad, hq_bad]
        rw [hs_g, hs_b, WittVector.teichmuller_zero]; ring
      · by_cases hq_bad : q ∈ Bset
        · have hs_g : s_good q = 0 := by simp [s_good, hq_good]
          have hs_b : s_bad q = f.coeff q := by simp [s_bad, hq_bad]
          rw [hs_g, hs_b, WittVector.teichmuller_zero]; ring
        · have hs_g : s_good q = 0 := by simp [s_good, hq_good]
          have hs_b : s_bad q = 0 := by simp [s_bad, hq_bad]
          have hq_notin : q ∉ f.support := by
            intro hq_in
            -- `q ∈ f.support` is either in `S' = Gset` or in `f.support \ S' = Bset`.
            by_cases hqS' : q ∈ S'
            · exact hq_good hqS'
            · exact hq_bad ⟨hq_in, hqS'⟩
          have hfc : f.coeff q = 0 := by
            by_contra hc; exact hq_notin hc
          rw [hs_g, hs_b, hfc, WittVector.teichmuller_zero]; ring
    -- Project the lift-level equality through the quotient map.
    have hproj :
        f_good + f_bad = pAdicHahnSeries.from_coeff f.coeff (support_IsPWO f) := by
      change
        (Ideal.Quotient.mk (NullSeriesIdeal p))
            (LiftedPAdicHahnSeries.from_coeff s_good hs_good_pwo) +
          (Ideal.Quotient.mk (NullSeriesIdeal p))
            (LiftedPAdicHahnSeries.from_coeff s_bad hs_bad_pwo) = _
      rw [← (Ideal.Quotient.mk (NullSeriesIdeal p)).map_add, hL_eq]
      rfl
    rw [hproj, pAdicHahnSeries.from_coeff_of_coeff_eq_self f]
  exact ⟨f_good, f_bad, hf_decomp, hf_good_supp, hf_bad_supp_fin⟩

open Bornology in
/-- Monomial-shift of the canonical-expansion support.  For `c : ℚ` and `x : 𝕃_[p]`,
multiplying by the monomial `single c 1` (a unit of `𝕃_[p]`, equal to `p`-power when
`c ∈ ℤ` but valid for any rational shift) translates the canonical-expansion support by
`c`:  `support (single c 1 · x) = (· + c) '' x.support`.

PROOF IDEA (canonical-expansion uniqueness).  Write `x = from_coeff s` with `s = x.coeff`
its (unique, Teichmüller-rep) canonical coefficients.  At the lift level, the HahnSeries
coefficient of `single c 1 * (Lifted.from_coeff s)` at `a` is `s (a - c)`
(`HahnSeries.coeff_single_mul`, `one_mul`), i.e. the lift equals `Lifted.from_coeff
(fun a => s (a - c))`.  The shifted coefficient function `fun a => s (a-c)` has the same
*values* as `s` (just reindexed), so it is still a valid canonical (Teichmüller-rep)
coefficient family, and its support is `(· + c) '' (Function.support s) = (·+c) '' x.support`,
PWO because translation is an order-iso.  By uniqueness of the canonical expansion
(`exists_canonical_expansion`), this shifted family *is* the canonical coefficient of the
product, so its support computes the product's `support`. -/
private theorem support_single_mul_shift {p : ℕ} [Fact (Nat.Prime p)] (c : ℚ) (x : 𝕃_[p]) :
    pAdicHahnSeries.support
        ((Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single c (1 : ℤᵘⁿ_[p]))) * x)
      = (fun q => q + c) '' x.support := by
  classical
  -- The shifted canonical coefficient family of `x`.
  set s : ℚ → Fpbar p := x.coeff with hs_def
  have hs_pwo : (Function.support s).IsPWO := support_IsPWO x
  -- Translation `(· - c)` is an order embedding, so the shifted support is PWO.
  set sShift : ℚ → Fpbar p := fun a => s (a - c) with hsShift_def
  have hsupp_shift : Function.support sShift = (fun q => q + c) '' Function.support s := by
    ext a
    simp only [Function.mem_support, ne_eq, sShift, Set.mem_image]
    constructor
    · intro ha
      exact ⟨a - c, ha, by ring⟩
    · rintro ⟨q, hq, rfl⟩
      simpa [add_sub_cancel_right] using hq
  have hsShift_pwo : (Function.support sShift).IsPWO := by
    rw [hsupp_shift]
    -- image of a PWO set under the monotone `(· + c)` is PWO
    apply hs_pwo.image_of_monotone
    intro a b hab; simpa using add_le_add_right hab c
  -- The lift of `single c 1 * x` equals `Lifted.from_coeff sShift`.
  have hlift_eq :
      HahnSeries.single c (1 : ℤᵘⁿ_[p]) *
          LiftedPAdicHahnSeries.from_coeff s hs_pwo
        = LiftedPAdicHahnSeries.from_coeff sShift hsShift_pwo := by
    apply HahnSeries.ext
    funext a
    rw [HahnSeries.coeff_single_mul, one_mul]
    rfl
  -- `x = mkLp (Lifted.from_coeff s)` since `s = x.coeff` is the canonical family.
  have hx_eq : x = pAdicHahnSeries.from_coeff s hs_pwo :=
    (pAdicHahnSeries.from_coeff_of_coeff_eq_self x).symm
  -- Multiply through the quotient ring-hom and identify the product's canonical family.
  have hprod_eq :
      (Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single c (1 : ℤᵘⁿ_[p]))) * x
        = pAdicHahnSeries.from_coeff sShift hsShift_pwo := by
    rw [hx_eq]
    change
      (Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single c (1 : ℤᵘⁿ_[p]))) *
          (Ideal.Quotient.mk (NullSeriesIdeal p)) (LiftedPAdicHahnSeries.from_coeff s hs_pwo)
        = (Ideal.Quotient.mk (NullSeriesIdeal p))
            (LiftedPAdicHahnSeries.from_coeff sShift hsShift_pwo)
    rw [← (Ideal.Quotient.mk (NullSeriesIdeal p)).map_mul, hlift_eq]
  -- Conclude on supports.
  rw [hprod_eq]
  change Function.support (pAdicHahnSeries.from_coeff sShift hsShift_pwo).coeff = _
  rw [pAdicHahnSeries.coeff_of_from_coeff_eq_self sShift hsShift_pwo, hsupp_shift]
  rfl

open Bornology in
/-- The monomial `single c 1` (image in `𝕃_[p]`) is algebraic over `ℚᵘⁿ_[p]`.  Its
canonical-expansion support is the singleton `{c}` (its lift `single c 1` already has
Teichmüller-rep coefficients — the value `1 = teichmuller 1`), hence finite, so
`alg_of_fin_supp` + `alg_QpUn_of_alg_Qp` apply. -/
private theorem single_one_isAlgebraic {p : ℕ} [Fact (Nat.Prime p)] (c : ℚ) :
    IsAlgebraic ℚᵘⁿ_[p]
      (Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single c (1 : ℤᵘⁿ_[p]))) := by
  classical
  -- The canonical coefficient family of the monomial is `Pi.single c 1`, supported on `{c}`.
  set t : ℚ → Fpbar p := Pi.single c (1 : Fpbar p) with ht_def
  have ht_supp : Function.support t ⊆ {c} := by
    rw [ht_def]; exact Pi.support_single_subset
  have ht_pwo : (Function.support t).IsPWO := (Set.finite_singleton c).subset ht_supp |>.isPWO
  -- The lift `single c 1` equals `Lifted.from_coeff t` (`teichmuller p 1 = 1`).
  have hlift : HahnSeries.single c (1 : ℤᵘⁿ_[p]) = LiftedPAdicHahnSeries.from_coeff t ht_pwo := by
    apply HahnSeries.ext
    funext a
    change (HahnSeries.single c (1 : ℤᵘⁿ_[p])).coeff a = (WittVector.teichmuller p) (t a)
    by_cases hac : a = c
    · subst hac
      rw [HahnSeries.coeff_single_same, ht_def, Pi.single_eq_same, map_one]
    · rw [HahnSeries.coeff_single_of_ne hac, ht_def, Pi.single_eq_of_ne hac,
        WittVector.teichmuller_zero]
  -- Hence the monomial `= from_coeff t`, whose support is `Function.support t ⊆ {c}`, finite.
  have hmono_eq :
      Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single c (1 : ℤᵘⁿ_[p]))
        = pAdicHahnSeries.from_coeff t ht_pwo := by
    rw [hlift]; rfl
  have hfin : (pAdicHahnSeries.support (Ideal.Quotient.mk (NullSeriesIdeal p)
      (HahnSeries.single c (1 : ℤᵘⁿ_[p])))).Finite := by
    rw [hmono_eq]
    change (Function.support (pAdicHahnSeries.from_coeff t ht_pwo).coeff).Finite
    rw [pAdicHahnSeries.coeff_of_from_coeff_eq_self t ht_pwo]
    exact (Set.finite_singleton c).subset ht_supp
  -- Finite support ⟹ algebraic over ℚ_[p] ⟹ algebraic over ℚᵘⁿ_[p].
  exact pAdicHahnSeries.alg_QpUn_of_alg_Qp p _ (pAdicHahnSeries.alg_of_fin_supp p _ hfin)

open Bornology in
theorem fintie_support_of_qpun_algebraic_of_bounded_support {p : ℕ} [Fact (Nat.Prime p)]
  (f : 𝕃_[p]) (hf1 : IsAlgebraic ℚᵘⁿ_[p] f) (hf2 : IsBounded f.support)
  (hf3 : (derivedSet ((Rat.cast : ℚ → ℝ) '' f.support)).Finite) :
  f.support.Finite := by
  -- Suppose, for contradiction, that the support is infinite.
  by_contra hinf
  rw [Set.not_finite] at hinf
  -- Bolzano–Weierstrass over ℝ: an infinite bounded support has an ℝ-accumulation point.
  have hne : (derivedSet ((Rat.cast : ℚ → ℝ) '' f.support)).Nonempty :=
    real_derivedSet_nonempty_of_infinite_bounded hinf hf2
  -- The sparse-representative reduction (lem:42556).
  obtain ⟨S', lam, T, W, hS'sub, hdiff_fin, hW_ne, hW_sparse, hRep⟩ :=
    exists_sparse_rep f hf1 hf2 hf3 hne
  -- Split `f = f_good + f_bad` along `support = S' ⊔ (support \ S')`.
  obtain ⟨f_good, f_bad, hf_decomp, hf_good_supp, hf_bad_supp_fin⟩ :=
    support_split_decomp f S' hS'sub hdiff_fin
  -- `f_bad` (finite support) is algebraic over ℚ_p, hence over ℚᵘⁿ_p.
  have hf_bad_alg : IsAlgebraic ℚᵘⁿ_[p] f_bad :=
    pAdicHahnSeries.alg_QpUn_of_alg_Qp p f_bad
      (pAdicHahnSeries.alg_of_fin_supp p f_bad hf_bad_supp_fin)
  -- Hence `f_good = f - f_bad` is algebraic over ℚᵘⁿ_p.
  have hf_good_alg : IsAlgebraic ℚᵘⁿ_[p] f_good := by
    have hfg : f_good = f - f_bad := by rw [hf_decomp]; ring
    rw [hfg]; exact hf1.sub hf_bad_alg
  -- The shifted series `g = single (-lam) 1 · f_good` has support `S' - lam`.
  set mono : 𝕃_[p] := Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single (-lam) (1 : ℤᵘⁿ_[p]))
    with hmono
  set g : 𝕃_[p] := mono * f_good with hg
  have hg_supp : g.support = (fun q => q + (-lam)) '' f_good.support :=
    support_single_mul_shift (-lam) f_good
  -- `g` is algebraic over ℚᵘⁿ_p (product of two algebraics).
  have hg_alg : IsAlgebraic ℚᵘⁿ_[p] g :=
    (single_one_isAlgebraic (-lam)).mul hf_good_alg
  -- The `IsRepModZ` set of `g.support` matches the one produced by `exists_sparse_rep`.
  have hRep' : IsRepModZ W {x : ℚ | ∃ q ∈ g.support, -1 * (T : ℚ) * q = x} := by
    -- `{-1*T*q' | q' ∈ g.support} = {-1*T*(q-lam) | q ∈ S'}` since `g.support = {q-lam | q∈S'}`.
    have hset_eq :
        {x : ℚ | ∃ q ∈ g.support, -1 * (T : ℚ) * q = x}
          = {x : ℚ | ∃ q ∈ S', x = -1 * (T : ℚ) * (q - lam)} := by
      ext x
      simp only [Set.mem_setOf_eq, hg_supp, hf_good_supp, Set.mem_image]
      constructor
      · rintro ⟨q', ⟨q, hq, rfl⟩, rfl⟩
        exact ⟨q, hq, by ring⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q + (-lam), ⟨q, hq, rfl⟩, by ring⟩
    rw [hset_eq]; exact hRep
  -- `main_theorem` makes `g` transcendental over ℚᵘⁿ_p — contradiction.
  exact (main_theorem p g T W hW_ne hW_sparse hRep') hg_alg

-- coro:11594
open Bornology in
theorem support_accpt_empty_or_infinite_of_qp_algebraic_of_bounded_support
  {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (hf1 : IsAlgebraic ℚ_[p] f) (hf2 : IsBounded f.support) :
  (derivedSet ((Rat.cast : ℚ → ℝ) '' f.support)) = ∅ ∨
  (derivedSet ((Rat.cast : ℚ → ℝ) '' f.support)).Infinite
  := by
  -- Contrapositive of thm:29075 over ℝ.  If the ℝ-derived set is nonempty and finite,
  -- then `f` (being ℚ_p-algebraic, hence ℚᵘⁿ_p-algebraic) has bounded support with
  -- finitely many ℝ-accumulation points, so thm:29075 makes `f.support` finite; then
  -- its image is finite and has empty ℝ-derived set (ℝ is T₁) — contradicting nonempty.
  rcases Set.eq_empty_or_nonempty (derivedSet ((Rat.cast : ℚ → ℝ) '' f.support)) with hempty | hne
  · exact Or.inl hempty
  · refine Or.inr ?_
    by_contra hnotinf
    rw [Set.not_infinite] at hnotinf
    -- ℚ_p-algebraic ⟹ ℚᵘⁿ_p-algebraic, feed thm:29075.
    have halg_un : IsAlgebraic ℚᵘⁿ_[p] f := pAdicHahnSeries.alg_QpUn_of_alg_Qp p f hf1
    have hsupp_fin : f.support.Finite :=
      fintie_support_of_qpun_algebraic_of_bounded_support f halg_un hf2 hnotinf
    -- A finite support has finite image; a finite set has empty ℝ-derived set.
    have himg_fin : ((Rat.cast : ℚ → ℝ) '' f.support).Finite := hsupp_fin.image _
    obtain ⟨x, hx⟩ := hne
    rw [mem_derivedSet] at hx
    exact absurd (Set.Infinite.of_accPt hx) (Set.not_infinite.mpr himg_fin)

-- coro:11594
open Bornology Ordinal in
/-- `lem:ordertype-bridge` (forward Cantor–Bendixson direction).  For a support set
`S = f.support ⊆ ℚ`, a small intrinsic order type forces few ℝ-accumulation points:
if `typeLT S < ω²` then the ℝ-derived set `derivedSet (ι '' S)` is finite.

The proof assigns to each `a : ℝ` the order type `o a = typeLT {s ∈ S | ι s < a}` of its
*down-set* (a subtype of the well-ordered `↥f.support`), and runs the five atomic steps of
the blueprint:

* **Step 1** (forbidden gap): for every `a` there is `δ>0` with `(a, a+δ) ∩ T = ∅`, taken as
  the least rational of `S` strictly above `a` (`Set.IsWF.min`).
* **Step 2** (one-sided accumulation): for `a ∈ derivedSet T` and `b<a` there is `s∈S` with
  `b<ι s<a`, combining Step 1 with `accPt_iff_nhds`.
* **Step 3** (`o a ≤ typeLT S`): the down-set inclusion is an `InitialSeg`
  (`InitialSeg.ordinal_type_le`).
* **Step 4** (`ω ∣ o a`): on `derivedSet T` the down-set has no greatest element (Step 2), so
  `o a` is a successor-prelimit (`isSuccPrelimit_type_lt`), i.e. `ω ∣ o a`
  (`isSuccPrelimit_iff_omega0_dvd`).
* **Step 5** (`o` injective): for `a<a'` in `derivedSet T`, a separating point (Step 2) makes
  the down-set inclusion a proper `InitialSeg`, i.e. a `PrincipalSeg`, so `o a < o a'`.

Then `typeLT S < ω² = ω^(succ 1)` gives `n` with `typeLT S < ω·n`
(`lt_omega0_opow_succ`); Steps 3–4 put `o '' derivedSet T ⊆ {ω·k | k<n}`, finite, and with
Step 5 injective `Set.Finite.of_finite_image` finishes. -/
private theorem derivedSet_real_finite_of_typeLT_lt_omega0_sq {p : ℕ} [Fact (Nat.Prime p)]
    (f : 𝕃_[p]) (hf : typeLT f.support < omega0 ^ 2) :
    (derivedSet ((Rat.cast : ℚ → ℝ) '' f.support)).Finite := by
  -- `S = f.support` is well-founded in ℚ; the subtype `↥f.support` carries the
  -- `WellFoundedLT` instance `wellFoundedLT_support`, so `typeLT` and the down-set order
  -- types below are well-defined ordinals.
  set S : Set ℚ := f.support with hS
  have hSwf : S.IsWF := (support_IsPWO f).isWF
  set T : Set ℝ := (Rat.cast : ℚ → ℝ) '' S with hT
  -- `o a` = order type of the down-set `{s ∈ S | ι s < a}` (a subtype of `↥S`).
  set o : ℝ → Ordinal := fun a => typeLT (Subtype (fun s : ↥S => ((s : ℚ) : ℝ) < a)) with ho
  -- STEP 1 — a forbidden gap above each point: the least rational of `S` strictly above `a`.
  have step1 : ∀ a : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ T, a < y → a + δ ≤ y := by
    intro a
    set U : Set ℚ := {s : ℚ | s ∈ S ∧ a < (s : ℝ)} with hU
    rcases U.eq_empty_or_nonempty with hempty | hne
    · -- no rational of `S` above `a`: any `δ` works vacuously.
      refine ⟨1, one_pos, ?_⟩
      intro y hy hay
      obtain ⟨s, hs, rfl⟩ := hy
      exact absurd (show s ∈ U from ⟨hs, hay⟩) (by rw [hempty]; exact id)
    · -- otherwise `δ = min U - a > 0` and nothing of `T` lands in `(a, a+δ)`.
      have hUwf : U.IsWF := hSwf.mono (fun x hx => hx.1)
      have hs0mem : hUwf.min hne ∈ U := hUwf.min_mem hne
      refine ⟨(hUwf.min hne : ℝ) - a, by linarith [hs0mem.2], ?_⟩
      intro y hy hay
      obtain ⟨s, hs, rfl⟩ := hy
      have hle : hUwf.min hne ≤ s := hUwf.min_le hne ⟨hs, hay⟩
      have : (hUwf.min hne : ℝ) ≤ (s : ℝ) := by exact_mod_cast hle
      linarith
  -- STEP 2 — accumulation is one-sided: below any `b<a` there is a support point in `(b,a)`.
  have step2 : ∀ a ∈ derivedSet T, ∀ b : ℝ, b < a → ∃ s ∈ S, b < (s : ℝ) ∧ (s : ℝ) < a := by
    intro a ha b hb
    obtain ⟨δ, hδ, hgap⟩ := step1 a
    rw [mem_derivedSet, accPt_iff_nhds] at ha
    set ε : ℝ := min δ (a - b) with hε
    have hεpos : 0 < ε := lt_min hδ (by linarith)
    have hεle1 : ε ≤ δ := min_le_left _ _
    have hεle2 : ε ≤ a - b := min_le_right _ _
    have hnhds : Set.Ioo (a - ε) (a + ε) ∈ nhds a := Ioo_mem_nhds (by linarith) (by linarith)
    obtain ⟨y, ⟨hyIoo, hyT⟩, hyne⟩ := ha _ hnhds
    obtain ⟨s, hs, rfl⟩ := hyT
    refine ⟨s, hs, ?_, ?_⟩
    · -- `s > a - ε ≥ b`.
      have hble : b ≤ a - ε := by linarith
      exact lt_of_le_of_lt hble hyIoo.1
    · -- `s ≠ a`, and `s` cannot exceed `a` (gap from Step 1), so `s < a`.
      rcases lt_trichotomy ((s : ℝ)) a with h | h | h
      · exact h
      · exact absurd h hyne
      · exfalso
        have hle : a + δ ≤ (s : ℝ) := hgap _ ⟨s, hs, rfl⟩ h
        have hub : (s : ℝ) < a + ε := hyIoo.2
        linarith
  -- STEP 3 — the down-set inclusion is an `InitialSeg`, so `o a ≤ typeLT S`.
  have step3 : ∀ a : ℝ, o a ≤ typeLT ↥S := by
    intro a
    let g : @InitialSeg (Subtype (fun s : ↥S => ((s : ℚ) : ℝ) < a)) (↥S) (· < ·) (· < ·) :=
      { toFun := Subtype.val
        inj' := Subtype.val_injective
        map_rel_iff' := Iff.rfl
        mem_range_of_rel' := by
          rintro x bb (hbb : bb < x.val)
          refine ⟨⟨bb, ?_⟩, rfl⟩
          have hx : ((x.val.val : ℚ) : ℝ) < a := x.property
          have : ((bb.val : ℚ) : ℝ) < ((x.val.val : ℚ) : ℝ) := by exact_mod_cast hbb
          exact lt_trans this hx }
    exact g.ordinal_type_le
  -- STEP 4 — on `derivedSet T` the down-set has no top (Step 2), so `o a` is a
  -- successor-prelimit, i.e. `ω ∣ o a`.
  have step4 : ∀ a ∈ derivedSet T, ω ∣ o a := by
    intro a ha
    have hnomax : NoMaxOrder (Subtype (fun s : ↥S => ((s : ℚ) : ℝ) < a)) := by
      constructor
      intro x
      have hxa : ((x.val.val : ℚ) : ℝ) < a := x.property
      obtain ⟨s, hs, hxs, hsa⟩ := step2 a ha ((x.val.val : ℚ) : ℝ) hxa
      refine ⟨⟨⟨s, hs⟩, hsa⟩, ?_⟩
      show x < (⟨⟨s, hs⟩, hsa⟩ : Subtype (fun s : ↥S => ((s : ℚ) : ℝ) < a))
      rw [Subtype.mk_lt_mk]
      show x.val < (⟨s, hs⟩ : ↥S)
      rw [Subtype.mk_lt_mk]
      exact_mod_cast hxs
    have h1 : Order.IsSuccPrelimit (o a) := isSuccPrelimit_type_lt
    exact (isSuccPrelimit_iff_omega0_dvd).mp h1
  -- STEP 5 — for `a<a'` in `derivedSet T`, a separating point makes the down-set inclusion a
  -- *proper* initial segment (a `PrincipalSeg`), so `o a < o a'`.
  have step5 : ∀ a ∈ derivedSet T, ∀ a' ∈ derivedSet T, a < a' → o a < o a' := by
    intro a _ha a' ha' haa'
    obtain ⟨sstar, hsstar, h1, h2⟩ := step2 a' ha' a haa'
    let g : @InitialSeg (Subtype (fun s : ↥S => ((s : ℚ) : ℝ) < a))
        (Subtype (fun s : ↥S => ((s : ℚ) : ℝ) < a')) (· < ·) (· < ·) :=
      { toFun := fun s => ⟨s.val, by
          have : ((s.val.val : ℚ) : ℝ) < a := s.property
          exact lt_trans this haa'⟩
        inj' := by rintro ⟨x, hx⟩ ⟨y, hy⟩ h; simpa using h
        map_rel_iff' := Iff.rfl
        mem_range_of_rel' := by
          rintro x bb (hbb : bb < _)
          refine ⟨⟨bb.val, ?_⟩, by rfl⟩
          have hxP : ((x.val.val : ℚ) : ℝ) < a := x.property
          have : ((bb.val.val : ℚ) : ℝ) < ((x.val.val : ℚ) : ℝ) := by exact_mod_cast hbb
          exact lt_trans this hxP }
    -- `sstar` is in `D_{a'}` but not in the range of `g` (it is `≥ a`), so `g` is not onto.
    have hns : ¬ Function.Surjective g := by
      intro hsurj
      have hsP' : ((sstar : ℚ) : ℝ) < a' := h2
      obtain ⟨y, hy⟩ := hsurj ⟨⟨sstar, hsstar⟩, hsP'⟩
      have hval : (g y).val = (⟨sstar, hsstar⟩ : ↥S) := congrArg Subtype.val hy
      have hgy : (g y).val = y.val := rfl
      rw [hgy] at hval
      have hyP : ((y.val.val : ℚ) : ℝ) < a := y.property
      rw [hval] at hyP
      exact absurd hyP (not_lt.mpr (le_of_lt h1))
    let g' := g.toPrincipalSeg hns
    exact g'.ordinal_type_lt
  -- CONCLUSION — `typeLT S < ω² = ω^(succ 1)` gives `n` with `typeLT S < ω·n`.
  rw [← opow_natCast ω 2] at hf
  have hsucc : ((2 : ℕ) : Ordinal) = Order.succ (1 : Ordinal) := by
    rw [Order.succ_eq_add_one]; norm_num
  rw [hsucc] at hf
  obtain ⟨n, hn⟩ := lt_omega0_opow_succ.mp hf
  rw [opow_one] at hn
  -- `o` is injective on `derivedSet T` (Step 5 strict monotonicity).
  have hinj : Set.InjOn o (derivedSet T) := by
    intro a ha a' ha' heq
    rcases lt_trichotomy a a' with h | h | h
    · exact absurd heq (ne_of_lt (step5 a ha a' ha' h))
    · exact h
    · exact absurd heq.symm (ne_of_lt (step5 a' ha' a ha h))
  -- Each `o a` is `ω·k` with `k<n` (Steps 3–4 + the cancellation `o a < ω·n`).
  have himg : ∀ a ∈ derivedSet T, ∃ k : ℕ, k < n ∧ o a = ω * (k : Ordinal) := by
    intro a ha
    have hdvd : ω ∣ o a := step4 a ha
    have hmod : o a % ω = 0 := Ordinal.dvd_iff_mod_eq_zero.mp hdvd
    have hoeq : o a = ω * (o a / ω) := by
      have := Ordinal.div_add_mod (o a) ω
      rw [hmod, add_zero] at this; exact this.symm
    have ho_lt : o a < ω * (n : Ordinal) := lt_of_le_of_lt (step3 a) hn
    have hdiv_lt : o a / ω < (n : Ordinal) :=
      (Ordinal.lt_mul_iff_div_lt omega0_ne_zero).mp ho_lt
    have hdiv_omega : o a / ω < ω := hdiv_lt.trans (natCast_lt_omega0 n)
    obtain ⟨k, hk⟩ := lt_omega0.mp hdiv_omega
    refine ⟨k, ?_, ?_⟩
    · have : (k : Ordinal) < (n : Ordinal) := hk ▸ hdiv_lt
      exact_mod_cast this
    · rw [hoeq, hk]
  -- `o '' derivedSet T ⊆ {ω·k | k<n}` finite, `o` injective ⟹ `derivedSet T` finite.
  apply Set.Finite.of_finite_image (f := o) _ hinj
  apply Set.Finite.subset (Set.finite_range (fun k : Fin n => ω * (k : Ordinal)))
  rintro x ⟨a, ha, rfl⟩
  obtain ⟨k, hk, hok⟩ := himg a ha
  exact ⟨⟨k, hk⟩, by rw [hok]⟩

open Bornology Ordinal in
theorem order_type_of_qp_algebraic_of_bounded_support {p : ℕ} [Fact (Nat.Prime p)]
  (f : 𝕃_[p]) (hf1 : IsAlgebraic ℚ_[p] f) (hf2 : IsBounded f.support) :
  typeLT f.support < omega0 ∨ typeLT f.support ≥ omega0^2 := by
  -- Dichotomy on whether the intrinsic order type is `< ω²`.
  rcases lt_or_ge (typeLT f.support) (omega0 ^ 2) with hlt | hge
  · -- `typeLT < ω²`: the forward bridge gives finitely many ℝ-accumulation points, so by
    -- thm:29075 (via ℚᵘⁿ) the support is finite, hence `typeLT < ω`.
    refine Or.inl ?_
    have hfin_acc : (derivedSet ((Rat.cast : ℚ → ℝ) '' f.support)).Finite :=
      derivedSet_real_finite_of_typeLT_lt_omega0_sq f hlt
    have halg_un : IsAlgebraic ℚᵘⁿ_[p] f := pAdicHahnSeries.alg_QpUn_of_alg_Qp p f hf1
    have hsupp_fin : f.support.Finite :=
      fintie_support_of_qpun_algebraic_of_bounded_support f halg_un hf2 hfin_acc
    -- A finite linear order has order type `< ω`.
    have : Finite f.support := hsupp_fin
    exact Ordinal.card_lt_aleph0.mp
      (by rw [Ordinal.card_type]; exact Cardinal.lt_aleph0_of_finite _)
  · -- Otherwise `typeLT ≥ ω²` directly.
    exact Or.inr hge

end FormalizedSparse
