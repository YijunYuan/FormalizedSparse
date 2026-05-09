import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Fin
import Mathlib.SetTheory.Cardinal.Finite

namespace Sparse

@[ext]
structure DigitSeries where
  toFun : ℕ+ → ℕ
  fin_supp : toFun.support.Finite

instance : FunLike (DigitSeries) ℕ+ ℕ where
  coe := DigitSeries.toFun
  coe_injective' := by
    rintro ⟨f, _⟩ ⟨g, _⟩ hfg
    simp only at hfg
    congr

instance : AddCommMonoid DigitSeries where
  add a b := {
    toFun := fun n => a n + b n
    fin_supp := by
      refine Set.Finite.subset (a.fin_supp.union b.fin_supp) ?_
      intro n hn
      simp only [Function.mem_support, Set.mem_union] at hn ⊢
      by_cases han : a n = 0
      · right
        intro hbn
        exact hn <| by simpa [han, hbn]
      · exact Or.inl han
  }
  add_assoc := by
    intro a b c
    ext n
    exact Nat.add_assoc (a n) (b n) (c n)
  zero := {
    toFun := fun _ => 0
    fin_supp := by simp }
  zero_add := by
    intro a
    ext n
    apply Nat.zero_add
  add_zero := by
    intro a
    ext n
    apply Nat.add_zero
  nsmul n f := {
    toFun := fun m => n * f m
    fin_supp := by
      refine Set.Finite.subset f.fin_supp ?_
      intro m hm
      simp only [Function.mem_support] at hm ⊢
      by_cases hnm : n = 0
      · simp [hnm] at hm
      · simpa [hnm] using hm }
  add_comm a b := by
    ext n
    exact Nat.add_comm (a n) (b n)
  nsmul_zero f := by
    ext n
    simp only [zero_mul]
    rfl
  nsmul_succ n f := by
    ext s
    exact Nat.succ_mul n (f s)

namespace DigitSeries

noncomputable def Sigma : DigitSeries →+ ℕ where
  toFun f := ∑ i ∈ f.fin_supp.toFinset, f i
  map_zero' := by
    classical
    change Finset.sum ((0 : DigitSeries).fin_supp.toFinset) (fun _ : ℕ+ => 0) = 0
    simp
  map_add' a b := by
    classical
  let s : Finset ℕ+ := (a.fin_supp.union b.fin_supp).toFinset
  have hsum_add :
      ∑ i ∈ (a + b).fin_supp.toFinset, (a + b) i = Finset.sum s (fun i => (a + b) i) := by
    unfold s
    refine Finset.sum_subset ?_ ?_
    · intro i hi
      have hi' : (a + b) i ≠ 0 := by
        simpa [Function.mem_support] using hi
      have hi_union : i ∈ Function.support a ∪ Function.support b := by
        simp only [Function.mem_support, Set.mem_union]
        by_cases hai : a i = 0
        · right
          intro hbi
          have habi : (a + b) i = 0 := by
            change a i + b i = 0
            simp [hai, hbi]
          exact hi' habi
        · exact Or.inl hai
      simpa using hi_union
    · intro i _ hi
      simpa [Function.mem_support] using hi
  have hsum_a : ∑ i ∈ a.fin_supp.toFinset, a i = Finset.sum s (fun i => a i) := by
    unfold s
    refine Finset.sum_subset ?_ ?_
    · intro i hi
      have hi' : a i ≠ 0 := by
        simpa [Function.mem_support] using hi
      have hi_union : i ∈ Function.support a ∪ Function.support b := by
        simp [Function.mem_support, Set.mem_union, hi']
      simpa using hi_union
    · intro i _ hi
      simpa [Function.mem_support] using hi
  have hsum_b : ∑ i ∈ b.fin_supp.toFinset, b i = Finset.sum s (fun i => b i) := by
    unfold s
    refine Finset.sum_subset ?_ ?_
    · intro i hi
      have hi' : b i ≠ 0 := by
        simpa [Function.mem_support] using hi
      have hi_union : i ∈ Function.support a ∪ Function.support b := by
        simp [Function.mem_support, Set.mem_union, hi']
      simpa using hi_union
    · intro i _ hi
      simpa [Function.mem_support] using hi
  calc
    ∑ i ∈ (a + b).fin_supp.toFinset, (a + b) i = Finset.sum s (fun i => (a + b) i) := hsum_add
    _ = Finset.sum s (fun i => a i + b i) := by rfl
    _ = Finset.sum s (fun i => a i) + Finset.sum s (fun i => b i) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i ∈ a.fin_supp.toFinset, a i) + ∑ i ∈ b.fin_supp.toFinset, b i := by
      rw [← hsum_a, ← hsum_b]

noncomputable def maxIndex (f : DigitSeries) : ℕ :=
  f.fin_supp.toFinset.sup fun i => (i : ℕ)

def coeffs (f : ℕ+ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => f (Nat.succPNat n) :: coeffs f n

noncomputable def value (p : ℕ) (f : DigitSeries) (n : ℕ) : ℕ :=
  Nat.ofDigits p (coeffs f n)

def indices (n : ℕ) : Finset ℕ+ :=
  (Finset.range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩

@[simp] lemma coeffs_length (f : ℕ+ → ℕ) (n : ℕ) :
    (coeffs f n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [coeffs, ih]

@[simp] lemma coeffs_sum (f : ℕ+ → ℕ) (n : ℕ) :
    (coeffs f n).sum = Finset.sum (indices n) f := by
  induction n with
  | zero => simp [coeffs, indices]
  | succ n ih =>
      rw [coeffs, List.sum_cons]
      rw [show indices (n + 1) = insert (Nat.succPNat n) (indices n) by
        ext i
        simp [indices, Finset.range_add_one, eq_comm]]
      rw [Finset.sum_insert]
      · simp [ih]
      · simp [indices]

@[simp] lemma mem_indices (n k : ℕ) :
    Nat.succPNat k ∈ indices n ↔ k < n := by
  simp [indices]

@[simp] lemma indices_succ (n : ℕ) :
    indices (n + 1) = insert (Nat.succPNat n) (indices n) := by
  ext i
  simp [indices, Finset.range_add_one, eq_comm]

lemma le_maxIndex_of_mem_support (f : DigitSeries) {n : ℕ+} (hn : f n ≠ 0) :
    (n : ℕ) ≤ f.maxIndex := by
  classical
  refine Finset.le_sup ?_
  simpa using hn

lemma eq_zero_of_maxIndex_lt (f : DigitSeries) {n : ℕ} (hn : f.maxIndex < n + 1) :
    f (Nat.succPNat n) = 0 := by
  by_contra hne
  exact (not_lt_of_ge (f.le_maxIndex_of_mem_support hne)) hn

lemma cast_mul_zpow_neg_succ (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    (p : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ)) = (p : ℚ) ^ (-(n : ℤ)) := by
  have hp0 : (p : ℚ) ≠ 0 := by
    exact_mod_cast (show p ≠ 0 from (Fact.out : Nat.Prime p).ne_zero)
  rw [zpow_neg, zpow_neg]
  norm_num
  field_simp [hp0]
  have hpow : (p : ℚ) ^ (↑n + 1) = (p : ℚ) * (p : ℚ) ^ n := by simpa using (pow_succ' (p : ℚ) n)
  exact hpow.symm

lemma cast_pow_mul_zpow_neg (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    ((p : ℚ) ^ n) * (p : ℚ) ^ (-(n : ℤ)) = 1 := by
  have hp0 : (p : ℚ) ≠ 0 := by
    exact_mod_cast (show p ≠ 0 from (Fact.out : Nat.Prime p).ne_zero)
  rw [zpow_neg, zpow_natCast]
  field_simp [hp0]

noncomputable def norm (p : ℕ) [Fact (Nat.Prime p)] : DigitSeries →+ ℚ where
  toFun f := ∑ i ∈ f.fin_supp.toFinset, (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ))
  map_zero' := by
    classical
    simp
  map_add' a b := by
    classical
    have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
    let s : Finset ℕ+ := (a.fin_supp.union b.fin_supp).toFinset
    have hsum_add :
        ∑ i ∈ (a + b).fin_supp.toFinset, ((a + b) i : ℚ) * (p : ℚ) ^ (-(i : ℤ)) =
          Finset.sum s (fun i => ((a + b) i : ℚ) * (p : ℚ) ^ (-(i : ℤ))) := by
      unfold s
      refine Finset.sum_subset ?_ ?_
      · intro i hi
        have hi' : (a + b) i ≠ 0 := by
          simpa [Function.mem_support] using hi
        have hi_union : i ∈ Function.support a ∪ Function.support b := by
          simp only [Function.mem_support, Set.mem_union]
          by_cases hai : a i = 0
          · right
            intro hbi
            have habi : (a + b) i = 0 := by
              change a i + b i = 0
              simp [hai, hbi]
            exact hi' habi
          · exact Or.inl hai
        simpa using hi_union
      · intro i _ hi
        have hi' : (a + b) i = 0 := by
          simpa [Function.mem_support] using hi
        rw [hi']
        simp
    have hsum_a :
        ∑ i ∈ a.fin_supp.toFinset, (a i : ℚ) * (p : ℚ) ^ (-(i : ℤ)) =
          Finset.sum s (fun i => (a i : ℚ) * (p : ℚ) ^ (-(i : ℤ))) := by
      unfold s
      refine Finset.sum_subset ?_ ?_
      · intro i hi
        have hi' : a i ≠ 0 := by
          simpa [Function.mem_support] using hi
        have hi_union : i ∈ Function.support a ∪ Function.support b := by
          simp [Function.mem_support, Set.mem_union, hi']
        simpa using hi_union
      · intro i _ hi
        have hi' : a i = 0 := by
          simpa [Function.mem_support] using hi
        rw [hi']
        simp
    have hsum_b :
        ∑ i ∈ b.fin_supp.toFinset, (b i : ℚ) * (p : ℚ) ^ (-(i : ℤ)) =
          Finset.sum s (fun i => (b i : ℚ) * (p : ℚ) ^ (-(i : ℤ))) := by
      unfold s
      refine Finset.sum_subset ?_ ?_
      · intro i hi
        have hi' : b i ≠ 0 := by
          simpa [Function.mem_support] using hi
        have hi_union : i ∈ Function.support a ∪ Function.support b := by
          simp [Function.mem_support, Set.mem_union, hi']
        simpa using hi_union
      · intro i _ hi
        have hi' : b i = 0 := by
          simpa [Function.mem_support] using hi
        rw [hi']
        simp
    calc
      ∑ i ∈ (a + b).fin_supp.toFinset, ((a + b) i : ℚ) * (p : ℚ) ^ (-(i : ℤ)) =
          Finset.sum s (fun i => ((a + b) i : ℚ) * (p : ℚ) ^ (-(i : ℤ))) := hsum_add
      _ = Finset.sum s (fun i =>
            (((a i : ℚ) + (b i : ℚ)) * (p : ℚ) ^ (-(i : ℤ)))) := by
          congr with i
          change (((a i + b i : ℕ) : ℚ) * (p : ℚ) ^ (-(i : ℤ)) =
            ((a i : ℚ) + (b i : ℚ)) * (p : ℚ) ^ (-(i : ℤ)))
          congr 1
          norm_num
      _ = Finset.sum s (fun i => (a i : ℚ) * (p : ℚ) ^ (-(i : ℤ)) +
            ((b i : ℚ) * (p : ℚ) ^ (-(i : ℤ)))) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
      _ = Finset.sum s (fun i => (a i : ℚ) * (p : ℚ) ^ (-(i : ℤ))) +
            Finset.sum s (fun i => (b i : ℚ) * (p : ℚ) ^ (-(i : ℤ))) := by
          rw [Finset.sum_add_distrib]
      _ = (∑ i ∈ a.fin_supp.toFinset, (a i : ℚ) * (p : ℚ) ^ (-(i : ℤ))) +
            ∑ i ∈ b.fin_supp.toFinset, (b i : ℚ) * (p : ℚ) ^ (-(i : ℤ)) := by
          rw [← hsum_a, ← hsum_b]

lemma norm_additive (p : ℕ) [Fact (Nat.Prime p)] (a b : DigitSeries) :
    (a + b).norm p = a.norm p + b.norm p := by
  exact (norm p).map_add a b

lemma value_eq_sum_indices (f : DigitSeries) (p : ℕ) [Fact (Nat.Prime p)] :
    ∀ n,
      ((f.value p n : ℚ) * (p : ℚ) ^ (-(n : ℤ))) =
        Finset.sum (indices n) fun i => (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ))
  | 0 => by simp [DigitSeries.value, DigitSeries.indices]
  | n + 1 => by
      rw [DigitSeries.value, DigitSeries.coeffs, Nat.ofDigits_cons, DigitSeries.indices_succ,
        Finset.sum_insert]
      · calc
          (((f (Nat.succPNat n) + p * f.value p n : ℕ) : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ)))
              = (f (Nat.succPNat n) : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ))
                + ((f.value p n : ℚ) * (p : ℚ)) * (p : ℚ) ^ (-(n + 1 : ℤ)) := by norm_num; ring
          _ = (f (Nat.succPNat n) : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ))
                + (f.value p n : ℚ) * (p : ℚ) ^ (-(n : ℤ)) := by
                  rw [mul_assoc, DigitSeries.cast_mul_zpow_neg_succ]
          _ = (f (Nat.succPNat n) : ℚ) * (p : ℚ) ^ (-(Nat.succPNat n : ℤ))
                + Finset.sum (indices n) (fun i => (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ))) := by
                  rw [value_eq_sum_indices (f := f) (p := p) n]
                  simp
      · simp

lemma norm_eq_sum_indices (f : DigitSeries) (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ}
    (hn : f.maxIndex < n) :
    f.norm p = Finset.sum (indices n) fun i => (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ)) := by
  classical
  change ∑ i ∈ f.fin_supp.toFinset, (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ)) =
      Finset.sum (indices n) (fun i => (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ)))
  refine Finset.sum_subset ?_ ?_
  · intro i hi
    have hne : f i ≠ 0 := by simpa using hi
    have hi_lt : (i.natPred : ℕ) < n := by
      have hi_lt' : (i : ℕ) < n := lt_of_le_of_lt (f.le_maxIndex_of_mem_support hne) hn
      have hi_succ : i.natPred + 1 < n := by simpa [PNat.natPred_add_one] using hi_lt'
      exact Nat.lt_trans (Nat.lt_succ_self _) hi_succ
    simpa [PNat.succPNat_natPred] using (DigitSeries.mem_indices n i.natPred).2 hi_lt
  · intro i hi his
    have hzero : f i = 0 := by
      by_contra hne
      exact his (by simpa using hne)
    simp [hzero]

lemma norm_eq_value (f : DigitSeries) (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ}
    (hn : f.maxIndex < n) :
    f.norm p = ((f.value p n : ℚ) * (p : ℚ) ^ (-(n : ℤ))) := by
  rw [f.norm_eq_sum_indices p hn, ← f.value_eq_sum_indices p n]

lemma Sigma_eq_sum_indices (f : DigitSeries) {n : ℕ} (hn : f.maxIndex < n) :
    f.Sigma = Finset.sum (indices n) f := by
  classical
  change ∑ i ∈ f.fin_supp.toFinset, f i = Finset.sum (indices n) f
  refine Finset.sum_subset ?_ ?_
  · intro i hi
    have hne : f i ≠ 0 := by simpa using hi
    have hi_lt : (i.natPred : ℕ) < n := by
      have hi_lt' : (i : ℕ) < n := lt_of_le_of_lt (f.le_maxIndex_of_mem_support hne) hn
      have hi_succ : i.natPred + 1 < n := by simpa [PNat.natPred_add_one] using hi_lt'
      exact Nat.lt_trans (Nat.lt_succ_self _) hi_succ
    simpa [PNat.succPNat_natPred] using (DigitSeries.mem_indices n i.natPred).2 hi_lt
  · intro i hi his
    have hzero : f i = 0 := by
      by_contra hne
      exact his (by simpa using hne)
    simp [hzero]

lemma Sigma_eq_coeffs_sum (f : DigitSeries) {n : ℕ} (hn : f.maxIndex < n) :
    f.Sigma = (coeffs f n).sum := by
  rw [Sigma_eq_sum_indices f hn, ← coeffs_sum f n]

lemma coeffs_update_above (f : ℕ+ → ℕ) (n m : ℕ) (hm : m ≤ n) (a : ℕ) :
    coeffs (Function.update f (Nat.succPNat n) a) m = coeffs f m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hm' : m ≤ n := Nat.le_trans (Nat.le_succ m) hm
      have hne : Nat.succPNat m ≠ Nat.succPNat n := by
        exact fun h => (Nat.lt_of_succ_le hm).ne (Nat.succPNat_injective h)
      simp [coeffs, Function.update, hne, ih hm']

noncomputable def ofCoeffs : List ℕ → DigitSeries
  | [] =>
      { toFun := 0
        fin_supp := by simp }
  | a :: L =>
      let f := ofCoeffs L
      { toFun := Function.update f (Nat.succPNat L.length) a
        fin_supp := by
          classical
          refine Set.Finite.subset (f.fin_supp.insert (Nat.succPNat L.length)) ?_
          intro i hi
          by_cases h : i = Nat.succPNat L.length
          · simp [h]
          · right; simpa [Function.update, h] using hi }

@[simp] lemma coeffs_ofCoeffs : ∀ L : List ℕ, coeffs (ofCoeffs L) L.length = L
  | [] => rfl
  | a :: L => by
      simp only [ofCoeffs, coeffs, List.length_cons]
      rw [List.cons.injEq]
      constructor
      · change Function.update (ofCoeffs L) (Nat.succPNat L.length) a (Nat.succPNat L.length) = a
        simp
      · change coeffs (Function.update (ofCoeffs L) (Nat.succPNat L.length) a) L.length = L
        rw [coeffs_update_above (f := ofCoeffs L) (n := L.length) (m := L.length) le_rfl (a := a)]
        rw [coeffs_ofCoeffs L]

lemma ofCoeffs_lt {p : ℕ} [Fact (Nat.Prime p)] :
    ∀ {L : List ℕ}, (∀ x ∈ L, x < p) → ∀ i, ofCoeffs L i < p
  | [], h, i => by
      simpa [ofCoeffs] using (Fact.out : Nat.Prime p).pos
  | a :: L, h, i => by
      by_cases hi : i = Nat.succPNat L.length
      · subst hi
        change Function.update (ofCoeffs L) (Nat.succPNat L.length) a (Nat.succPNat L.length) < p
        simpa using h a List.mem_cons_self
      · change Function.update (ofCoeffs L) (Nat.succPNat L.length) a i < p
        simpa [Function.update, hi] using
          ofCoeffs_lt (p := p) (L := L) (fun x hx => h x (List.mem_cons_of_mem _ hx)) i

lemma le_length_of_mem_support_ofCoeffs : ∀ {L : List ℕ} {i : ℕ+},
    ofCoeffs L i ≠ 0 → (i : ℕ) ≤ L.length
  | [], i, hi => by cases hi rfl
  | a :: L, i, hi => by
      by_cases htop : i = Nat.succPNat L.length
      · subst htop
        simp
      · have hi' : ofCoeffs L i ≠ 0 := by
          change Function.update (ofCoeffs L) (Nat.succPNat L.length) a i ≠ 0 at hi
          simpa [Function.update, htop] using hi
        exact Nat.le_trans (le_length_of_mem_support_ofCoeffs hi') (Nat.le_succ _)

lemma maxIndex_ofCoeffs_lt (L : List ℕ) : (ofCoeffs L).maxIndex < L.length + 1 := by
  classical
  have hle : (ofCoeffs L).maxIndex ≤ L.length := by
    refine Finset.sup_le ?_
    intro i hi
    exact le_length_of_mem_support_ofCoeffs (by simpa using hi)
  exact Nat.lt_succ_of_le hle

lemma maxIndex_ofCoeffs_zero_cons_lt (L : List ℕ) :
    (ofCoeffs (0 :: L)).maxIndex < L.length + 1 := by
  classical
  have hle : (ofCoeffs (0 :: L)).maxIndex ≤ L.length := by
    refine Finset.sup_le ?_
    intro i hi
    have hne : ofCoeffs (0 :: L) i ≠ 0 := by
      simpa using hi
    by_cases htop : i = Nat.succPNat L.length
    · subst htop
      exfalso
      change
        Function.update (ofCoeffs L) (Nat.succPNat L.length) 0 (Nat.succPNat L.length) ≠ 0 at hne
      exact hne (by simp)
    · have hi' : ofCoeffs L i ≠ 0 := by
        change Function.update (ofCoeffs L) (Nat.succPNat L.length) 0 i ≠ 0 at hne
        simpa [Function.update, htop] using hne
      exact le_length_of_mem_support_ofCoeffs hi'
  exact Nat.lt_succ_of_le hle

lemma eq_on_of_coeffs_eq : ∀ {f g : ℕ+ → ℕ} {n : ℕ}, coeffs f n = coeffs g n →
    ∀ i : ℕ+, (i : ℕ) ≤ n → f i = g i
  | f, g, 0, h, i, hi => by
      exfalso
      exact (Nat.not_lt_of_ge hi) i.2
  | f, g, n + 1, h, i, hi => by
      have h' : f (Nat.succPNat n) = g (Nat.succPNat n) ∧ coeffs f n = coeffs g n := by
        simpa [coeffs] using h
      rcases Nat.lt_or_eq_of_le hi with hi_lt | hi_eq
      · exact eq_on_of_coeffs_eq h'.2 i (Nat.le_of_lt_succ hi_lt)
      · have : i = Nat.succPNat n := by
          apply Subtype.ext
          simpa using hi_eq
        simpa [this] using h'.1

@[simp] lemma Sigma_ofCoeffs (L : List ℕ) : (ofCoeffs L).Sigma = L.sum := by
  have hsigma : (ofCoeffs L).Sigma = (coeffs (ofCoeffs L) (L.length + 1)).sum := by
    exact Sigma_eq_coeffs_sum (f := ofCoeffs L) (n := L.length + 1) (maxIndex_ofCoeffs_lt L)
  have htop : ofCoeffs L (Nat.succPNat L.length) = 0 := by
    exact eq_zero_of_maxIndex_lt (f := ofCoeffs L) (n := L.length) (maxIndex_ofCoeffs_lt L)
  simpa [coeffs, htop, coeffs_ofCoeffs] using hsigma
end DigitSeries

namespace DigitSeries

def IsP (f : DigitSeries) (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∀ n, f n < p

end DigitSeries

lemma ofDigits_carry_last_eq (p x : ℕ) :
    Nat.ofDigits p [x] = Nat.ofDigits p [x % p, x / p] := by
  simp [Nat.ofDigits_cons, Nat.mod_add_div]

lemma ofDigits_carry_eq (p x y : ℕ) (L : List ℕ) :
    Nat.ofDigits p (x :: y :: L) = Nat.ofDigits p (x % p :: (x / p + y) :: L) := by
  calc
    Nat.ofDigits p (x :: y :: L) = x + p * y + p * (p * Nat.ofDigits p L) := by
      simp [Nat.ofDigits_cons, Nat.mul_add, Nat.add_assoc]
    _ = x % p + p * (x / p) + p * y + p * (p * Nat.ofDigits p L) := by
      rw [Nat.mod_add_div]
    _ = Nat.ofDigits p (x % p :: (x / p + y) :: L) := by
      simp [Nat.ofDigits_cons, Nat.mul_add, Nat.add_assoc]

lemma ofDigits_eq_zero_of_sum_eq_zero (p : ℕ) {L : List ℕ} (hsum : L.sum = 0) :
    Nat.ofDigits p L = 0 := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
      have hsum' : x + xs.sum = 0 := by simpa [List.sum_cons] using hsum
      have hx : x = 0 := Nat.eq_zero_of_add_eq_zero_right hsum'
      have hxs : xs.sum = 0 := Nat.eq_zero_of_add_eq_zero_left hsum'
      simp [Nat.ofDigits_cons, hx, ih hxs]

lemma exists_small_sum_ofDigits_eq_of_exists_ge (p : ℕ) (hp : 1 < p) :
    ∀ {L : List ℕ}, (∃ x ∈ L, p ≤ x) →
      ∃ E : List ℕ, Nat.ofDigits p E = Nat.ofDigits p L ∧ E.sum < L.sum
  | [] => by
      intro hbad
      rcases hbad with ⟨x, hx, _⟩
      cases hx
  | x :: [] => by
      intro hbad
      rcases hbad with ⟨w, hw, hwge⟩
      have hwx : w = x := by simpa using hw
      subst w
      have hx0 : 0 < x / p := Nat.div_pos hwge (Nat.zero_lt_of_lt hp)
      have hdecrease : x % p + x / p < x := by
        have hmul : x / p < p * (x / p) := by
          simpa [one_mul] using Nat.mul_lt_mul_of_pos_right hp hx0
        calc
          x % p + (x / p) < x % p + p * (x / p) := by exact Nat.add_lt_add_left hmul _
          _ = x := by simpa [Nat.add_comm] using (Nat.mod_add_div x p)
      refine ⟨[x % p, x / p], (ofDigits_carry_last_eq p x).symm, ?_⟩
      simp only [List.sum_cons, List.sum_nil]
      exact hdecrease
  | x :: y :: L => by
      intro hbad
      by_cases hx : p ≤ x
      · have hx0 : 0 < x / p := Nat.div_pos hx (Nat.zero_lt_of_lt hp)
        have hdecrease : x % p + x / p < x := by
          have hmul : x / p < p * (x / p) := by
            simpa [one_mul] using Nat.mul_lt_mul_of_pos_right hp hx0
          calc
            x % p + (x / p) < x % p + p * (x / p) := by exact Nat.add_lt_add_left hmul _
            _ = x := by simpa [Nat.add_comm] using (Nat.mod_add_div x p)
        refine ⟨x % p :: (x / p + y) :: L, (ofDigits_carry_eq p x y L).symm, ?_⟩
        simpa [List.sum_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.add_lt_add_right hdecrease (y + L.sum)
      · have hybad : ∃ z ∈ y :: L, p ≤ z := by
          rcases hbad with ⟨z, hz, hzp⟩
          have hz' : z = x ∨ z ∈ y :: L := by simpa [List.mem_cons] using hz
          rcases hz' with rfl | hzL
          · exact (hx hzp).elim
          · exact ⟨z, hzL, hzp⟩
        rcases exists_small_sum_ofDigits_eq_of_exists_ge (p := p) hp hybad with ⟨E, hEeq, hEsum⟩
        refine ⟨x :: E, ?_, ?_⟩
        · simp [Nat.ofDigits_cons, hEeq]
        · simpa [List.sum_cons] using Nat.add_lt_add_left hEsum x

lemma digit_sum_ofDigits_le_sum (p : ℕ) (hp : 1 < p) :
    ∀ L : List ℕ, (Nat.digits p (Nat.ofDigits p L)).sum ≤ L.sum := by
  intro L
  suffices hmain :
      ∀ n : ℕ, ∀ K : List ℕ, K.sum ≤ n → (Nat.digits p (Nat.ofDigits p K)).sum ≤ K.sum by
    exact hmain L.sum L le_rfl
  intro n
  induction n with
  | zero =>
      intro K hK
      have hsum0 : K.sum = 0 := Nat.eq_zero_of_le_zero hK
      have hof0 : Nat.ofDigits p K = 0 := ofDigits_eq_zero_of_sum_eq_zero p hsum0
      simp [hof0]
  | succ n ih =>
      intro K hK
      by_cases hbad : ∃ x ∈ K, p ≤ x
      · rcases exists_small_sum_ofDigits_eq_of_exists_ge p hp hbad with ⟨E, hEeq, hEsum⟩
        have hEn : E.sum ≤ n := Nat.lt_succ_iff.mp (lt_of_lt_of_le hEsum hK)
        have hEle : (Nat.digits p (Nat.ofDigits p E)).sum ≤ E.sum := ih E hEn
        rw [hEeq] at hEle
        exact le_trans hEle (Nat.le_of_lt hEsum)
      · have hlt : ∀ x ∈ K, x < p := by
          intro x hx
          exact lt_of_not_ge fun hxp => hbad ⟨x, hx, hxp⟩
        have hdigits : (Nat.digits p (Nat.ofDigits p K)).sum = K.sum := by
          simpa using Nat.sum_digits_ofDigits_eq_sum hp ⟨rfl, hlt⟩
        exact hdigits.le

lemma digit_sum_ofDigits_lt_sum_of_exists_ge (p : ℕ) (hp : 1 < p) {L : List ℕ}
    (hbad : ∃ x ∈ L, p ≤ x) :
    (Nat.digits p (Nat.ofDigits p L)).sum < L.sum := by
  rcases exists_small_sum_ofDigits_eq_of_exists_ge p hp hbad with ⟨E, hEeq, hEsum⟩
  have hEle : (Nat.digits p (Nat.ofDigits p E)).sum ≤ E.sum := digit_sum_ofDigits_le_sum p hp E
  rw [hEeq] at hEle
  exact lt_of_le_of_lt hEle hEsum

lemma forall_lt_of_digit_sum_ofDigits_eq_sum (p : ℕ) (hp : 1 < p) {L : List ℕ}
    (hEq : (Nat.digits p (Nat.ofDigits p L)).sum = L.sum) :
    ∀ x ∈ L, x < p := by
  intro x hx
  by_contra hxp
  have hbad : ∃ y ∈ L, p ≤ y := ⟨x, hx, Nat.not_lt.mp hxp⟩
  have hlt := digit_sum_ofDigits_lt_sum_of_exists_ge p hp hbad
  rw [hEq] at hlt
  exact Nat.lt_irrefl _ hlt

namespace DigitSeries

lemma coeffs_lt {p : ℕ} [Fact (Nat.Prime p)] (f : DigitSeries) (hf : f.IsP p) (n : ℕ) :
    ∀ x ∈ DigitSeries.coeffs f n, x < p := by
  intro x hx
  induction n generalizing x with
  | zero => cases hx
  | succ n ih =>
      simp only [DigitSeries.coeffs, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa using hf (Nat.succPNat n)
      · exact ih _ hx

lemma value_lt_pow {p : ℕ} [Fact (Nat.Prime p)] (f : DigitSeries) (hf : f.IsP p) (n : ℕ) :
    f.value p n < p ^ n := by
  unfold DigitSeries.value
  simpa [DigitSeries.coeffs_length] using
    Nat.ofDigits_lt_base_pow_length ((Fact.out : Nat.Prime p).one_lt) (f.coeffs_lt hf n)

lemma eq_of_norm_sub_isInt {p : ℕ} [Fact (Nat.Prime p)] {f g : DigitSeries}
    (hf : f.IsP p) (hg : g.IsP p) (hfg : (f.norm p - g.norm p).isInt) : f = g := by
  let n := max f.maxIndex g.maxIndex + 1
  have hfN : f.maxIndex < n := by simp [n]
  have hgN : g.maxIndex < n := by simp [n]
  let q : ℚ := f.norm p - g.norm p
  have hq : q.isInt := by simpa [q] using hfg
  have hq_expr : q = (((f.value p n : ℚ) - g.value p n) * (p : ℚ) ^ (-(n : ℤ))) := by
    simp [q, f.norm_eq_value p hfN, g.norm_eq_value p hgN]
    ring
  have hq_lt : q < 1 := by
    rw [hq_expr]
    have hvf_lt : (f.value p n : ℚ) < (p : ℚ) ^ n := by
      exact_mod_cast f.value_lt_pow hf n
    have hp_pow_pos : 0 < (p : ℚ) ^ n := pow_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos) _
    have hdiff_lt : (f.value p n : ℚ) - g.value p n < (p : ℚ) ^ n := by nlinarith
    rw [show (p : ℚ) ^ (-(n : ℤ)) = ((p : ℚ) ^ n)⁻¹ by rw [zpow_neg, zpow_natCast]]
    simpa using mul_lt_mul_of_pos_right hdiff_lt (inv_pos.mpr hp_pow_pos)
  have hq_gt : (-1 : ℚ) < q := by
    rw [hq_expr]
    have hvg_lt : (g.value p n : ℚ) < (p : ℚ) ^ n := by
      exact_mod_cast g.value_lt_pow hg n
    have hp_pow_pos : 0 < (p : ℚ) ^ n := pow_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos) _
    have hdiff_gt :
        -((p : ℚ) ^ n) < (f.value p n : ℚ) - g.value p n := by
      nlinarith
    rw [show (p : ℚ) ^ (-(n : ℤ)) = ((p : ℚ) ^ n)⁻¹ by rw [zpow_neg, zpow_natCast]]
    simpa using mul_lt_mul_of_pos_right hdiff_gt (inv_pos.mpr hp_pow_pos)
  rw [Rat.eq_num_of_isInt hq] at hq_gt hq_lt
  have hnum_zero : q.num = 0 := by
    have : (-1 : ℤ) < q.num ∧ q.num < 1 := by exact_mod_cast And.intro hq_gt hq_lt
    omega
  have hq_zero : q = 0 := by
    rw [Rat.eq_num_of_isInt hq, hnum_zero]
    simp
  have hpz : (p : ℚ) ^ (-(n : ℤ)) ≠ 0 := by
    exact zpow_ne_zero _ (by exact_mod_cast (show p ≠ 0 from (Fact.out : Nat.Prime p).ne_zero))
  have hval_eq : (f.value p n : ℚ) = g.value p n := by
    apply sub_eq_zero.mp
    apply mul_right_cancel₀ hpz
    simpa [hq_expr] using hq_zero
  have hcoeffs :
      DigitSeries.coeffs f n = DigitSeries.coeffs g n := by
    apply Nat.ofDigits_inj_of_len_eq ((Fact.out : Nat.Prime p).one_lt)
    · simp [DigitSeries.coeffs_length]
    · exact f.coeffs_lt hf n
    · exact g.coeffs_lt hg n
    · exact_mod_cast hval_eq
  ext i
  by_cases hi : (i : ℕ) ≤ n
  · exact DigitSeries.eq_on_of_coeffs_eq hcoeffs i hi
  · have hfi : f i = 0 := by
      by_contra hne
      exact hi (le_trans (f.le_maxIndex_of_mem_support hne) (Nat.le_of_lt hfN))
    have hgi : g i = 0 := by
      by_contra hne
      exact hi (le_trans (g.le_maxIndex_of_mem_support hne) (Nat.le_of_lt hgN))
    simpa using hfi.trans hgi.symm

end DigitSeries

variable (p : ℕ) [Fact (Nat.Prime p)]

lemma lemma_1_2 (d : DigitSeries) :
    ∃! f : DigitSeries, f.IsP p ∧ (f.norm p - d.norm p).isInt := by
  let n := d.maxIndex + 1
  let a := d.value p n
  let r := a % p ^ n
  let L := Nat.digits p r ++ List.replicate (n - (Nat.digits p r).length) 0
  have hdn : d.maxIndex < n := by simp [n]
  have hr_lt : r < p ^ n := Nat.mod_lt _ (pow_pos ((Fact.out : Nat.Prime p).pos) _)
  have hLlen : L.length = n := by
    simp [L, (Nat.digits_length_le_iff ((Fact.out : Nat.Prime p).one_lt) r).2 hr_lt]
  have hLdigits : Nat.ofDigits p L = r := by
    unfold L
    rw [Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
  have hLlt : ∀ x ∈ L, x < p := by
    intro x hx
    unfold L at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Nat.digits_lt_base ((Fact.out : Nat.Prime p).one_lt) hx
    · rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
      simpa using (Fact.out : Nat.Prime p).pos
  let f := DigitSeries.ofCoeffs (0 :: L)
  have hfIsP : f.IsP p := by
    intro i
    exact DigitSeries.ofCoeffs_lt (p := p) (L := 0 :: L) (by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · subst x
        simpa using (Fact.out : Nat.Prime p).pos
      · exact hLlt x hx) i
  have hfmax : f.maxIndex < n + 1 := by
    simpa [f, hLlen] using DigitSeries.maxIndex_ofCoeffs_zero_cons_lt (L := L)
  have hfval : f.value p (n + 1) = p * r := by
    have htmp :
        Nat.ofDigits p
          (DigitSeries.coeffs (DigitSeries.ofCoeffs (0 :: L)) ((0 :: L).length)) = p * r := by
      rw [DigitSeries.coeffs_ofCoeffs]
      simp [Nat.ofDigits_cons, hLdigits]
    simpa [DigitSeries.value, f, hLlen] using htmp
  have hfnorm : f.norm p = (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) := by
    rw [f.norm_eq_value p hfmax, hfval, Nat.cast_mul]
    calc
      (↑p * ↑r) * (p : ℚ) ^ (-(n + 1 : ℤ)) = (↑r : ℚ) * ((p : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ))) := by
          ring
      _ = (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) := by
          rw [DigitSeries.cast_mul_zpow_neg_succ]
  have hfint : (f.norm p - d.norm p).isInt := by
    let qn : ℕ := a / p ^ n
    rw [hfnorm, d.norm_eq_value p hdn]
    have hmod_nat : r + p ^ n * qn = a := by
      simpa [r, qn] using Nat.mod_add_div a (p ^ n)
    have hmod : (r : ℚ) + ((p : ℚ) ^ n) * (qn : ℚ) = a := by exact_mod_cast hmod_nat
    have hdiff :
        (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) - (a : ℚ) * (p : ℚ) ^ (-(n : ℤ)) = -(qn : ℚ) := by
      calc
        (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) - (a : ℚ) * (p : ℚ) ^ (-(n : ℤ)) =
            (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) -
              ((r : ℚ) + ((p : ℚ) ^ n) * (qn : ℚ)) * (p : ℚ) ^ (-(n : ℤ)) := by
            rw [hmod]
        _ = -(((p : ℚ) ^ n) * (qn : ℚ)) * (p : ℚ) ^ (-(n : ℤ)) := by ring
        _ = -(qn : ℚ) := by
            calc
              -(((p : ℚ) ^ n) * (qn : ℚ)) * (p : ℚ) ^ (-(n : ℤ)) =
                  -((qn : ℚ) * (((p : ℚ) ^ n) * (p : ℚ) ^ (-(n : ℤ)))) := by ring
              _ = -(qn : ℚ) := by
                  rw [DigitSeries.cast_pow_mul_zpow_neg]
                  ring
    rw [hdiff]
    simp [(by norm_num : (-↑qn : ℚ) = (((-(qn : ℤ)) : ℚ))), Rat.isInt]
  refine ⟨f, ⟨hfIsP, hfint⟩, fun g hg => ?_⟩
  rcases hg with ⟨hgIsP, hgInt⟩
  have hgf : (g.norm p - f.norm p).isInt := by
    have hcast :
        (((g.norm p - d.norm p).num : ℚ) - ((f.norm p - d.norm p).num : ℚ)) =
          (((g.norm p - d.norm p).num - (f.norm p - d.norm p).num : ℤ) : ℚ) := by
      norm_num
    have hgf_eq :
        g.norm p - f.norm p =
          (((g.norm p - d.norm p).num : ℚ) - ((f.norm p - d.norm p).num : ℚ)) := by
      calc
        g.norm p - f.norm p = (g.norm p - d.norm p) - (f.norm p - d.norm p) := by ring
        _ = (((g.norm p - d.norm p).num : ℚ) - ((f.norm p - d.norm p).num : ℚ)) := by
              rw [Rat.eq_num_of_isInt hgInt, Rat.eq_num_of_isInt hfint]
              simp [Rat.num_intCast]
    rw [hgf_eq, hcast, Rat.isInt]
    simp [Rat.den_intCast]
  exact DigitSeries.eq_of_norm_sub_isInt hgIsP hfIsP hgf

namespace DigitSeries

noncomputable def tau (p : ℕ) [Fact (Nat.Prime p)] (f : DigitSeries) : DigitSeries :=
  (lemma_1_2 p f).choose

lemma tau_isP (p : ℕ) [Fact (Nat.Prime p)] (f : DigitSeries) : (f.tau p).IsP p :=
  (lemma_1_2 p f).choose_spec.1.1

end DigitSeries

lemma lemma_1_3₂ (p : ℕ) [Fact (Nat.Prime p)] (f g : DigitSeries) :
  f.tau p = g.tau p ↔ (f.norm p - g.norm p).isInt := by
    constructor
    · intro htau
      have hf : ((f.tau p).norm p - f.norm p).isInt := (lemma_1_2 p f).choose_spec.1.2
      have hg : ((g.tau p).norm p - g.norm p).isInt := (lemma_1_2 p g).choose_spec.1.2
      have hg' : ((f.tau p).norm p - g.norm p).isInt := by
        simpa [htau] using hg
      have hEq :
          f.norm p - g.norm p =
            ((f.tau p).norm p - g.norm p) - ((f.tau p).norm p - f.norm p) := by
        ring
      rw [Rat.isInt, Nat.beq_eq_true_eq] at hf hg'
      lift ((f.tau p).norm p - g.norm p) to ℤ using hg' with a ha
      lift ((f.tau p).norm p - f.norm p) to ℤ using hf with b hb
      have hmain : f.norm p - g.norm p = ((a - b : ℤ) : ℚ) := by
        calc
          f.norm p - g.norm p = (a : ℚ) - b := by simpa using hEq
          _ = ((a - b : ℤ) : ℚ) := by norm_num
      rw [hmain]
      simp [Rat.isInt]
    · intro hfg
      apply ((lemma_1_2 p g).choose_spec.2 (f.tau p))
      refine ⟨DigitSeries.tau_isP p f, ?_⟩
      have hf : ((f.tau p).norm p - f.norm p).isInt := (lemma_1_2 p f).choose_spec.1.2
      have hEq :
          (f.tau p).norm p - g.norm p =
            ((f.tau p).norm p - f.norm p) + (f.norm p - g.norm p) := by
        ring
      rw [Rat.isInt, Nat.beq_eq_true_eq] at hf hfg
      lift ((f.tau p).norm p - f.norm p) to ℤ using hf with a ha
      lift (f.norm p - g.norm p) to ℤ using hfg with b hb
      have hmain : (f.tau p).norm p - g.norm p = ((a + b : ℤ) : ℚ) := by
        calc
          (f.tau p).norm p - g.norm p = (a : ℚ) + b := by simpa using hEq
          _ = ((a + b : ℤ) : ℚ) := by norm_num
      rw [hmain]
      simp [Rat.isInt]

lemma lemma_1_3₃ (p : ℕ) [Fact (Nat.Prime p)] (d : DigitSeries) :
  (d.tau p) = d ↔ d.IsP p := by
  constructor
  · intro htau
    simpa [htau] using DigitSeries.tau_isP p d
  · intro hdIsP
    simpa [DigitSeries.tau] using
      (((lemma_1_2 p d).choose_spec.2 d) ⟨hdIsP, by simp [Rat.isInt]⟩).symm

lemma lemma_1_3₄ (p : ℕ) [Fact (Nat.Prime p)] (d : DigitSeries) :
  (d.tau p).Sigma ≤ d.Sigma ∧ (d.tau p).Sigma = d.Sigma ↔
      d.IsP p := by
  constructor
  · rintro ⟨_, hsigma⟩
    let n := d.maxIndex + 1
    let a := d.value p n
    let r := a % p ^ n
    let Ld := DigitSeries.coeffs d n
    let Lt := Nat.digits p r ++ List.replicate (n - (Nat.digits p r).length) 0
    have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
    have hp2 : 2 ≤ p := Nat.succ_le_of_lt hp1
    have hdn : d.maxIndex < n := by simp [n]
    have hr_lt : r < p ^ n := Nat.mod_lt _ (pow_pos ((Fact.out : Nat.Prime p).pos) _)
    have hLdSigma : d.Sigma = Ld.sum := by
      simpa [Ld, n] using DigitSeries.Sigma_eq_coeffs_sum (f := d) (n := n) hdn
    have hLtlen : Lt.length = n := by
      simp [Lt, (Nat.digits_length_le_iff hp1 r).2 hr_lt]
    have hLdigits : Nat.ofDigits p Lt = r := by
      unfold Lt
      rw [Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
    have hLlt : ∀ x ∈ Lt, x < p := by
      intro x hx
      unfold Lt at hx
      rw [List.mem_append, List.mem_replicate] at hx
      rcases hx with hx | hx
      · exact Nat.digits_lt_base hp1 hx
      · rcases hx with ⟨_, rfl⟩
        simpa using (Fact.out : Nat.Prime p).pos
    let f := DigitSeries.ofCoeffs (0 :: Lt)
    have hfIsP : f.IsP p := by
      intro i
      exact DigitSeries.ofCoeffs_lt (p := p) (L := 0 :: Lt) (by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simpa using (Fact.out : Nat.Prime p).pos
        · exact hLlt x hx) i
    have hfmax : f.maxIndex < n + 1 := by
      simpa [f, hLtlen] using DigitSeries.maxIndex_ofCoeffs_zero_cons_lt (L := Lt)
    have hfval : f.value p (n + 1) = p * r := by
      have htmp :
          Nat.ofDigits p
              (DigitSeries.coeffs (DigitSeries.ofCoeffs (0 :: Lt)) ((0 :: Lt).length)) =
            p * r := by
        rw [DigitSeries.coeffs_ofCoeffs]
        simp [Nat.ofDigits_cons, hLdigits]
      simpa [DigitSeries.value, f, hLtlen] using htmp
    have hfnorm : f.norm p = (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) := by
      rw [f.norm_eq_value p hfmax, hfval, Nat.cast_mul]
      calc
        (↑p * ↑r) * (p : ℚ) ^ (-(n + 1 : ℤ)) =
            (↑r : ℚ) * ((p : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ))) := by ring
        _ = (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) := by
            rw [DigitSeries.cast_mul_zpow_neg_succ]
    have hfint : (f.norm p - d.norm p).isInt := by
      let qn : ℕ := a / p ^ n
      rw [hfnorm, d.norm_eq_value p hdn]
      have hmod_nat : r + p ^ n * qn = a := by
        simpa [r, qn] using Nat.mod_add_div a (p ^ n)
      have hmod : (r : ℚ) + ((p : ℚ) ^ n) * (qn : ℚ) = a := by exact_mod_cast hmod_nat
      have hdiff :
          (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) - (a : ℚ) * (p : ℚ) ^ (-(n : ℤ)) = -(qn : ℚ) := by
        calc
          (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) - (a : ℚ) * (p : ℚ) ^ (-(n : ℤ)) =
              (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) -
                ((r : ℚ) + ((p : ℚ) ^ n) * (qn : ℚ)) * (p : ℚ) ^ (-(n : ℤ)) := by
              rw [hmod]
          _ = -(((p : ℚ) ^ n) * (qn : ℚ)) * (p : ℚ) ^ (-(n : ℤ)) := by ring
          _ = -(qn : ℚ) := by
              calc
                -(((p : ℚ) ^ n) * (qn : ℚ)) * (p : ℚ) ^ (-(n : ℤ)) =
                    -((qn : ℚ) * (((p : ℚ) ^ n) * (p : ℚ) ^ (-(n : ℤ)))) := by ring
                _ = -(qn : ℚ) := by
                    rw [DigitSeries.cast_pow_mul_zpow_neg]
                    ring
      rw [hdiff]
      simp [(by norm_num : (-↑qn : ℚ) = (((-(qn : ℤ)) : ℚ))), Rat.isInt]
    have htau : d.tau p = f := by
      exact (((lemma_1_2 p d).choose_spec.2 f) ⟨hfIsP, hfint⟩).symm
    have htauSigma : (d.tau p).Sigma = Lt.sum := by
      rw [htau]
      have hSigmaCoeffs : f.Sigma = (0 :: Lt).sum := by
        change (DigitSeries.ofCoeffs (0 :: Lt)).Sigma = (0 :: Lt).sum
        exact DigitSeries.Sigma_ofCoeffs (0 :: Lt)
      rw [List.sum_cons, zero_add] at hSigmaCoeffs
      exact hSigmaCoeffs
    have hdigits_r : (Nat.digits p r).sum = ((Nat.digits p a).take n).sum := by
      rw [show r = Nat.ofDigits p ((Nat.digits p a).take n) by
        simpa [r] using (Nat.self_mod_pow_eq_ofDigits_take n a hp2)]
      refine Nat.sum_digits_ofDigits_eq_sum hp1 (l := ((Nat.digits p a).take n).length) ?_
      constructor
      · rfl
      · intro x hx
        exact Nat.digits_lt_base hp1 (List.mem_of_mem_take hx)
    have htake_le : ((Nat.digits p a).take n).sum ≤ (Nat.digits p a).sum := by
      have := Nat.le_add_right ((Nat.digits p a).take n).sum ((Nat.digits p a).drop n).sum
      simpa [List.take_append_drop, List.sum_append] using this
    have hdigits_le : (Nat.digits p a).sum ≤ Ld.sum := by
      simpa [a, Ld, n, DigitSeries.value] using digit_sum_ofDigits_le_sum p hp1 Ld
    have htake_eq : ((Nat.digits p a).take n).sum = Ld.sum := by
      calc
        ((Nat.digits p a).take n).sum = (Nat.digits p r).sum := by simpa using hdigits_r.symm
        _ = Lt.sum := by simp [Lt, List.sum_append]
        _ = (d.tau p).Sigma := by simpa using htauSigma.symm
        _ = d.Sigma := hsigma
        _ = Ld.sum := hLdSigma
    have hdigits_eq : (Nat.digits p a).sum = Ld.sum := by
      apply le_antisymm hdigits_le
      calc
        Ld.sum = ((Nat.digits p a).take n).sum := htake_eq.symm
        _ ≤ (Nat.digits p a).sum := htake_le
    have hLdlt : ∀ x ∈ Ld, x < p := by
      simpa [a, Ld, n, DigitSeries.value] using
        forall_lt_of_digit_sum_ofDigits_eq_sum p hp1 hdigits_eq
    have hcoeff_eq :
        DigitSeries.coeffs (DigitSeries.ofCoeffs Ld) n = DigitSeries.coeffs d n := by
      simpa [Ld] using (DigitSeries.coeffs_ofCoeffs Ld)
    intro i
    by_cases hi : (i : ℕ) ≤ n
    · have hdi : DigitSeries.ofCoeffs Ld i = d i :=
        DigitSeries.eq_on_of_coeffs_eq hcoeff_eq i hi
      have hof_lt : DigitSeries.ofCoeffs Ld i < p := by
        exact DigitSeries.ofCoeffs_lt (p := p) (L := Ld) hLdlt i
      simpa [hdi] using hof_lt
    · have hzero : d i = 0 := by
        by_contra hne
        exact hi (le_trans (d.le_maxIndex_of_mem_support hne) (Nat.le_of_lt hdn))
      rw [hzero]
      exact (Fact.out : Nat.Prime p).pos
  · intro hdIsP
    repeat simp [(lemma_1_3₃ p d).2 hdIsP]

-- Unconditional version of the inequality from `lemma_1_3₄`.
-- Mirrors the construction in `lemma_1_3₄`'s forward direction but stops at the
-- ≤ chain (without requiring Sigma equality / IsP).
lemma Sigma_tau_le_Sigma (p : ℕ) [Fact (Nat.Prime p)] (d : DigitSeries) :
    (d.tau p).Sigma ≤ d.Sigma := by
  let n := d.maxIndex + 1
  let a := d.value p n
  let r := a % p ^ n
  let Ld := DigitSeries.coeffs d n
  let Lt := Nat.digits p r ++ List.replicate (n - (Nat.digits p r).length) 0
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hp2 : 2 ≤ p := Nat.succ_le_of_lt hp1
  have hdn : d.maxIndex < n := by simp [n]
  have hr_lt : r < p ^ n := Nat.mod_lt _ (pow_pos ((Fact.out : Nat.Prime p).pos) _)
  have hLdSigma : d.Sigma = Ld.sum := by
    simpa [Ld, n] using DigitSeries.Sigma_eq_coeffs_sum (f := d) (n := n) hdn
  have hLtlen : Lt.length = n := by
    simp [Lt, (Nat.digits_length_le_iff hp1 r).2 hr_lt]
  have hLdigits : Nat.ofDigits p Lt = r := by
    unfold Lt
    rw [Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
  have hLlt : ∀ x ∈ Lt, x < p := by
    intro x hx
    unfold Lt at hx
    rw [List.mem_append, List.mem_replicate] at hx
    rcases hx with hx | hx
    · exact Nat.digits_lt_base hp1 hx
    · rcases hx with ⟨_, rfl⟩
      simpa using (Fact.out : Nat.Prime p).pos
  let f := DigitSeries.ofCoeffs (0 :: Lt)
  have hfIsP : f.IsP p := by
    intro i
    exact DigitSeries.ofCoeffs_lt (p := p) (L := 0 :: Lt) (by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa using (Fact.out : Nat.Prime p).pos
      · exact hLlt x hx) i
  have hfmax : f.maxIndex < n + 1 := by
    simpa [f, hLtlen] using DigitSeries.maxIndex_ofCoeffs_zero_cons_lt (L := Lt)
  have hfval : f.value p (n + 1) = p * r := by
    have htmp :
        Nat.ofDigits p
            (DigitSeries.coeffs (DigitSeries.ofCoeffs (0 :: Lt)) ((0 :: Lt).length)) =
          p * r := by
      rw [DigitSeries.coeffs_ofCoeffs]
      simp [Nat.ofDigits_cons, hLdigits]
    simpa [DigitSeries.value, f, hLtlen] using htmp
  have hfnorm : f.norm p = (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) := by
    rw [f.norm_eq_value p hfmax, hfval, Nat.cast_mul]
    calc
      (↑p * ↑r) * (p : ℚ) ^ (-(n + 1 : ℤ)) =
          (↑r : ℚ) * ((p : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ))) := by ring
      _ = (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) := by
          rw [DigitSeries.cast_mul_zpow_neg_succ]
  have hfint : (f.norm p - d.norm p).isInt := by
    let qn : ℕ := a / p ^ n
    rw [hfnorm, d.norm_eq_value p hdn]
    have hmod_nat : r + p ^ n * qn = a := by
      simpa [r, qn] using Nat.mod_add_div a (p ^ n)
    have hmod : (r : ℚ) + ((p : ℚ) ^ n) * (qn : ℚ) = a := by exact_mod_cast hmod_nat
    have hdiff :
        (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) - (a : ℚ) * (p : ℚ) ^ (-(n : ℤ)) = -(qn : ℚ) := by
      calc
        (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) - (a : ℚ) * (p : ℚ) ^ (-(n : ℤ)) =
            (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) -
              ((r : ℚ) + ((p : ℚ) ^ n) * (qn : ℚ)) * (p : ℚ) ^ (-(n : ℤ)) := by
            rw [hmod]
        _ = -(((p : ℚ) ^ n) * (qn : ℚ)) * (p : ℚ) ^ (-(n : ℤ)) := by ring
        _ = -(qn : ℚ) := by
            calc
              -(((p : ℚ) ^ n) * (qn : ℚ)) * (p : ℚ) ^ (-(n : ℤ)) =
                  -((qn : ℚ) * (((p : ℚ) ^ n) * (p : ℚ) ^ (-(n : ℤ)))) := by ring
              _ = -(qn : ℚ) := by
                  rw [DigitSeries.cast_pow_mul_zpow_neg]
                  ring
    rw [hdiff]
    simp [(by norm_num : (-↑qn : ℚ) = (((-(qn : ℤ)) : ℚ))), Rat.isInt]
  have htau : d.tau p = f := by
    exact (((lemma_1_2 p d).choose_spec.2 f) ⟨hfIsP, hfint⟩).symm
  have htauSigma : (d.tau p).Sigma = Lt.sum := by
    rw [htau]
    have hSigmaCoeffs : f.Sigma = (0 :: Lt).sum := by
      change (DigitSeries.ofCoeffs (0 :: Lt)).Sigma = (0 :: Lt).sum
      exact DigitSeries.Sigma_ofCoeffs (0 :: Lt)
    rw [List.sum_cons, zero_add] at hSigmaCoeffs
    exact hSigmaCoeffs
  have hdigits_r : (Nat.digits p r).sum = ((Nat.digits p a).take n).sum := by
    rw [show r = Nat.ofDigits p ((Nat.digits p a).take n) by
      simpa [r] using (Nat.self_mod_pow_eq_ofDigits_take n a hp2)]
    refine Nat.sum_digits_ofDigits_eq_sum hp1 (l := ((Nat.digits p a).take n).length) ?_
    constructor
    · rfl
    · intro x hx
      exact Nat.digits_lt_base hp1 (List.mem_of_mem_take hx)
  have htake_le : ((Nat.digits p a).take n).sum ≤ (Nat.digits p a).sum := by
    have := Nat.le_add_right ((Nat.digits p a).take n).sum ((Nat.digits p a).drop n).sum
    simpa [List.take_append_drop, List.sum_append] using this
  have hdigits_le : (Nat.digits p a).sum ≤ Ld.sum := by
    simpa [a, Ld, n, DigitSeries.value] using digit_sum_ofDigits_le_sum p hp1 Ld
  have hLt_sum : Lt.sum = (Nat.digits p r).sum := by
    simp [Lt, List.sum_append]
  calc
    (d.tau p).Sigma = Lt.sum := htauSigma
    _ = (Nat.digits p r).sum := hLt_sum
    _ = ((Nat.digits p a).take n).sum := hdigits_r
    _ ≤ (Nat.digits p a).sum := htake_le
    _ ≤ Ld.sum := hdigits_le
    _ = d.Sigma := hLdSigma.symm

lemma lemma_1_3₁ (p : ℕ) [Fact (Nat.Prime p)] (d e : DigitSeries)
    (hd : d.IsP p) (he : e.IsP p) (h : d.norm p = e.norm p) : d = e := by
  have hsub : (d.norm p - e.norm p).isInt := by
    rw [h, sub_self]
    simp [Rat.isInt]
  exact DigitSeries.eq_of_norm_sub_isInt hd he hsub

set_option linter.unusedVariables false in
def IsCNSparse (p : ℕ) [Fact (Nat.Prime p)]
(c n : PNat) (S : Set (DigitSeries)) (hS : ∀ f ∈ S, f.IsP p) : Prop :=
  (
    ∀ d, d ∈ S → d.Sigma ≤ c
  ) ∧ (
    ∃ d : Fin n → S,
      (
        ∀ i : Fin n, (d i).val.Sigma = c
      ) ∧ (
        (∑ i, (d i).val).IsP p
      ) ∧ (
        ∀ e : Fin n → S, ((∑ i, (d i).val).norm p - (∑ i, (e i).val).norm p).isInt →
          ∃ perm : Equiv.Perm (Fin n), ∀ i, d i = e (perm i)
      )
  )

def IsSparse (p : ℕ) [Fact (Nat.Prime p)] (S : Set (DigitSeries)) (hS : ∀ f ∈ S, f.IsP p) : Prop :=
  ∃ c : PNat, ∃ D : Set ℕ+, D.Infinite ∧ ∀ n ∈ D, IsCNSparse p c n S hS

noncomputable def φ₀ {p : ℕ} [Fact (Nat.Prime p)] {S : Set (DigitSeries)} {hS : ∀ f ∈ S, f.IsP p}
  {c n : ℕ+} (hSparse : IsCNSparse p c n S hS) : S → ℕ :=
  fun d => Nat.card <| hSparse.2.choose⁻¹' {d}

/- USER: You need to formalize Lemma 1.5 of Sparse.pdf here.
   I have already formalized φ₀ above. You can use that.
-/

lemma lemma_1_5 {p : ℕ} [Fact (Nat.Prime p)] {S : Set (DigitSeries)}
    {hS : ∀ f ∈ S, f.IsP p} {c n : ℕ+} (hSparse : IsCNSparse p c n S hS)
    (φ : S → ℕ)
    (hφ_finite : (Function.support φ).Finite)
    (hφ_sum : ∑ᶠ d : S, φ d ≤ n)
    (hφ_norm : ((∑ᶠ d : S, (d.val.norm p) * (φ d : ℚ)) -
                (∑ᶠ d : S, (d.val.norm p) * (φ₀ hSparse d : ℚ))).isInt) :
    φ = φ₀ hSparse := by
  -- Goal: prove φ = φ₀ hSparse
  -- Strategy: Use uniqueness property of IsCNSparse

  -- Step 1: Establish that φ₀ has finite support
  have hφ₀_finite : (Function.support (φ₀ hSparse)).Finite := by
    -- φ₀ is non-zero only on the range of the witness sequence
    refine Set.Finite.subset (Set.finite_range hSparse.2.choose) ?_
    intro d hd
    simp only [Function.mem_support, φ₀, Set.mem_range] at hd ⊢
    by_contra h
    have : hSparse.2.choose ⁻¹' {d} = ∅ := by
      ext i
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hi
      exact h ⟨i, hi⟩
    rw [this] at hd
    simp at hd
  -- Step 2: Extract the witness sequence and its properties
  -- Note: We use hSparse.2.choose directly to keep the definitional link with φ₀
  set witness := hSparse.2.choose with hwitness_def
  have hwitness_prop := hSparse.2.choose_spec
  have hwitness_IsP : (∑ i : Fin n, (witness i).val).IsP p := hwitness_prop.2.1
  have hwitness_unique := hwitness_prop.2.2
  -- Step 3: Bridge φ₀ finsum to witness sequence sum
  -- This uses the fact that φ₀ counts preimages: φ₀(d) = |witness⁻¹({d})|
  -- So ∑ᶠ d, norm(d) * φ₀(d) = ∑ᶠ d, norm(d) * |witness⁻¹({d})|
  --                           = ∑ i, norm(witness(i))  (by regrouping)
  --                           = norm(∑ i, witness(i))  (by norm additivity)
  have hφ₀_norm_eq : (∑ᶠ d : S, (d.val.norm p) * (φ₀ hSparse d : ℚ)) =
                      (∑ i : Fin n, (witness i).val).norm p := by
    -- Step 1: Convert finsum to finset sum
    have h_support_subset : Function.support (fun d : S => (d.val.norm p) * (φ₀ hSparse d : ℚ)) ⊆
                            ↑hφ₀_finite.toFinset := by
      intro d hd
      simp only [Function.mem_support] at hd
      simp only [Set.Finite.coe_toFinset, Function.mem_support]
      intro h_eq
      apply hd
      rw [show (φ₀ hSparse d : ℚ) = ((φ₀ hSparse d : ℕ) : ℚ) from rfl, h_eq]
      simp
    rw [finsum_eq_sum_of_support_subset _ h_support_subset]
    -- Step 2: Unfold φ₀ definition and regroup
    simp only [φ₀]
    -- Step 3: Regroup sum from "sum over d" to "sum over i"
    -- Key: ∑ d, norm(d) * |witness⁻¹({d})| = ∑ i, norm(witness(i))
    -- We'll show both sides equal ∑ i : Fin n, norm(witness(i))
    have h_regroup : ∑ x ∈ hφ₀_finite.toFinset, (DigitSeries.norm p) ↑x *
                       ↑(Nat.card ↑(witness ⁻¹' {x})) =
                     ∑ i : Fin n, (witness i).val.norm p := by
      classical
      -- For each x : S, witness⁻¹({x}) viewed as a subtype of Fin n has card
      -- equal to the filter {i : Fin n | witness i = x}.card
      have h_card_eq : ∀ x : S,
          Nat.card ↑(witness ⁻¹' {x}) =
          (Finset.univ.filter (fun i : Fin n => witness i = x)).card := by
        intro x
        rw [show ↑(witness ⁻¹' {x}) = {i : Fin n // witness i = x} from rfl]
        exact Nat.subtype_card _ (fun i => by simp)
      -- Rewrite each term: norm(x) * |fiber| = ∑ i in fiber, norm(witness i)
      have h_term : ∀ x ∈ hφ₀_finite.toFinset,
          (DigitSeries.norm p) ↑x * ↑(Nat.card ↑(witness ⁻¹' {x})) =
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => witness i = x),
            (witness i).val.norm p := by
        intro x _
        rw [h_card_eq x]
        rw [Finset.sum_filter]
        -- Goal: norm(x) * (filter card : ℚ) = ∑ i, if witness i = x then norm(witness i) else 0
        rw [Finset.card_filter]
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : witness i = x
        · simp [hi]
        · simp [hi]
      rw [Finset.sum_congr rfl h_term]
      -- Apply sum_fiberwise: need ∀ i, witness i ∈ hφ₀_finite.toFinset
      have h_maps_to : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          witness i ∈ hφ₀_finite.toFinset := by
        intro i _
        simp only [Set.Finite.mem_toFinset, Function.mem_support, φ₀, ne_eq]
        rw [← hwitness_def]
        intro h_card_zero
        -- witness i is in the preimage of {witness i}, so the preimage is nonempty
        have hmem : i ∈ (witness ⁻¹' ({witness i} : Set ↑S)) := by
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
        have h_nonempty : (witness ⁻¹' ({witness i} : Set ↑S)).Nonempty := ⟨i, hmem⟩
        -- But Nat.card = 0 means either empty or infinite
        rw [Nat.card_eq_zero] at h_card_zero
        cases h_card_zero with
        | inl h_empty =>
          -- If empty, contradiction with nonempty
          have : Nonempty ↑(witness ⁻¹' ({witness i} : Set ↑S)) := h_nonempty.to_subtype
          exact not_nonempty_iff.mpr h_empty this
        | inr h_inf =>
          -- If infinite, contradiction with finiteness (Fin n is finite)
          have : Finite ↑(witness ⁻¹' ({witness i} : Set ↑S)) :=
            Set.Finite.to_subtype (Set.toFinite _)
          exact Finite.not_infinite this h_inf
      exact Finset.sum_fiberwise_of_maps_to h_maps_to (fun i => (witness i).val.norm p)
    rw [h_regroup]
    -- Step 4: Apply norm additivity (norm p is an AddMonoidHom)
    rw [map_sum (DigitSeries.norm p) (fun i => (witness i).val) Finset.univ]
  -- Step 3b: Strengthen the hypothesis ∑ᶠ φ d ≤ n to equality
  -- This is needed to construct a clean sequence e : Fin n → S from φ
  -- Idea: if ∑ᶠ φ d < n, we could pad to a sequence and use hwitness_unique
  -- to reach a contradiction with the cardinality of witness
  have hφ_sum_eq_n : ∑ᶠ d : S, φ d = n := by
    classical
    apply le_antisymm hφ_sum
    -- Strategy: prove (n : ℕ) * c.val ≤ (∑ᶠ d, φ d) * c.val, then cancel.
    -- Define T := hφ_finite.toFinset and convert finsums to Finset.sums.
    set T : Finset S := hφ_finite.toFinset with hT_def
    have hsupp_φ_subset : Function.support φ ⊆ ↑T := by
      intro d hd
      simpa [T, hT_def] using hd
    have hsum_φ_eq : ∑ᶠ d : S, φ d = ∑ d ∈ T, φ d :=
      finsum_eq_sum_of_support_subset _ hsupp_φ_subset
    have hsupp_smul_subset : Function.support (fun d : S => φ d • d.val) ⊆ ↑T := by
      intro d hd
      simp only [Function.mem_support] at hd
      apply hsupp_φ_subset
      intro hφd
      apply hd
      simp [hφd]
    -- (∑ d ∈ T, φ d • d.val).norm p = ∑ d ∈ T, (d.val.norm p) * (φ d : ℚ)
    have hLHS_φ_norm :
        (∑ d ∈ T, (φ d) • d.val).norm p = ∑ d ∈ T, (d.val.norm p) * (φ d : ℚ) := by
      rw [map_sum (DigitSeries.norm p) (fun d : S => φ d • d.val) T]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [(DigitSeries.norm p).map_nsmul]
      ring
    -- ∑ᶠ d, (d.val.norm p) * (φ d : ℚ) = ∑ d ∈ T, ...
    have hsupp_norm_subset :
        Function.support (fun d : S => (d.val.norm p) * (φ d : ℚ)) ⊆ ↑T := by
      intro d hd
      simp only [Function.mem_support] at hd
      apply hsupp_φ_subset
      intro hφd
      apply hd
      rw [show (φ d : ℚ) = ((φ d : ℕ) : ℚ) from rfl, hφd]
      simp
    have hfinsum_norm_eq_sum :
        ∑ᶠ d : S, (d.val.norm p) * (φ d : ℚ) = ∑ d ∈ T, (d.val.norm p) * (φ d : ℚ) :=
      finsum_eq_sum_of_support_subset _ hsupp_norm_subset
    -- Σ(witness sum) = (n : ℕ) * c.val
    have hwit_sigma : (∑ i : Fin n, (witness i).val).Sigma = (n : ℕ) * c.val := by
      rw [map_sum DigitSeries.Sigma (fun i : Fin n => (witness i).val) Finset.univ]
      simp_rw [show ∀ i : Fin n, DigitSeries.Sigma (witness i).val = c.val from
        fun i => hwitness_prop.1 i]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rfl
    -- ((LHS_φ).norm p - (Σwitness).norm p).isInt
    have hisInt : ((∑ d ∈ T, (φ d) • d.val).norm p -
                   (∑ i : Fin n, (witness i).val).norm p).isInt := by
      rw [hLHS_φ_norm, ← hfinsum_norm_eq_sum, ← hφ₀_norm_eq]
      exact hφ_norm
    -- (LHS_φ).tau p = ∑ i, (witness i).val
    have htau_eq :
        (∑ d ∈ T, (φ d) • d.val).tau p = ∑ i : Fin n, (witness i).val := by
      have h1 : (∑ d ∈ T, (φ d) • d.val).tau p =
                  (∑ i : Fin n, (witness i).val).tau p :=
        (lemma_1_3₂ p _ _).mpr hisInt
      have h2 : (∑ i : Fin n, (witness i).val).tau p = ∑ i : Fin n, (witness i).val :=
        (lemma_1_3₃ p _).mpr hwitness_IsP
      rw [h1, h2]
    -- Σ(LHS_φ) ≤ (∑ d ∈ T, φ d) * c.val
    have hSigma_bound :
        (∑ d ∈ T, (φ d) • d.val).Sigma ≤ (∑ d ∈ T, φ d) * c.val := by
      rw [map_sum DigitSeries.Sigma (fun d : S => (φ d) • d.val) T]
      have hstep : ∀ d : S,
          DigitSeries.Sigma ((φ d) • d.val) = (φ d) * DigitSeries.Sigma d.val := by
        intro d
        rw [DigitSeries.Sigma.map_nsmul]
        rfl
      simp_rw [hstep]
      calc
        ∑ d ∈ T, φ d * DigitSeries.Sigma d.val
            ≤ ∑ d ∈ T, φ d * c.val :=
              Finset.sum_le_sum (fun d _ =>
                Nat.mul_le_mul_left _ (hSparse.1 d.val d.property))
        _ = (∑ d ∈ T, φ d) * c.val := by rw [← Finset.sum_mul]
    -- Chain inequalities to get n * c.val ≤ (∑ᶠ φ d) * c.val
    have hchain : (n : ℕ) * c.val ≤ (∑ᶠ d : S, φ d) * c.val := by
      calc
        (n : ℕ) * c.val
            = (∑ i : Fin n, (witness i).val).Sigma := hwit_sigma.symm
        _ = ((∑ d ∈ T, (φ d) • d.val).tau p).Sigma := by rw [htau_eq]
        _ ≤ (∑ d ∈ T, (φ d) • d.val).Sigma :=
              Sigma_tau_le_Sigma p _
        _ ≤ (∑ d ∈ T, φ d) * c.val := hSigma_bound
        _ = (∑ᶠ d : S, φ d) * c.val := by rw [hsum_φ_eq]
    exact Nat.le_of_mul_le_mul_right hchain c.pos
  -- Step 4: Main uniqueness argument (Stage 2 of informal proof)
  classical
  -- Reuse the support-set T from Step 3b
  set T : Finset S := hφ_finite.toFinset with hT_def
  have hsupp_φ_subset : Function.support φ ⊆ ↑T := by
    intro d hd; simpa [T, hT_def] using hd
  have hsum_φ_eq : ∑ᶠ d : S, φ d = ∑ d ∈ T, φ d :=
    finsum_eq_sum_of_support_subset _ hsupp_φ_subset
  -- A1: Define f : S →₀ ℕ
  have hf_mem : ∀ d, φ d ≠ 0 → d ∈ T := by
    intro d hd; exact hsupp_φ_subset hd
  let f : S →₀ ℕ := Finsupp.onFinset T φ hf_mem
  have hf_apply : ∀ d, f d = φ d := fun d => rfl
  -- A2: m : Multiset S; show m.card = n
  let m : Multiset S := f.toMultiset
  have hm_card : m.card = n := by
    have h1 : m.card = f.sum (fun _ x => x) := Finsupp.card_toMultiset f
    have h2 : f.sum (fun _ x => x) = ∑ d ∈ T, φ d := by
      unfold Finsupp.sum
      apply Finset.sum_subset (Finsupp.support_onFinset_subset)
      intro d _hdT hdsupp
      simp only [Finsupp.mem_support_iff, not_not] at hdsupp
      change f d = 0 at hdsupp
      exact hdsupp
    rw [h1, h2, ← hsum_φ_eq, hφ_sum_eq_n]
  -- A3: Build e : Fin n → S
  have hlen : m.toList.length = n := by
    rw [Multiset.length_toList]; exact hm_card
  let e : Fin n → S := fun i => m.toList.get (Fin.cast hlen.symm i)
  -- A4: count_eq_φ : Multiset.count d m = φ d
  have hA4 : ∀ d : S, Multiset.count d m = φ d := by
    intro d
    rw [Finsupp.count_toMultiset]
    rfl
  -- A5: Nat.card (e ⁻¹' {d}) = φ d
  have hA5 : ∀ d : S, Nat.card ↑(e ⁻¹' {d}) = φ d := by
    intro d
    have hcardEq : Nat.card ↑(e ⁻¹' {d}) =
        (Finset.univ.filter (fun i : Fin n => e i = d)).card := by
      rw [show ↑(e ⁻¹' {d}) = {i : Fin n // e i = d} from rfl]
      exact Nat.subtype_card _ (fun i => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    rw [hcardEq]
    -- Reindex via Fin.cast
    have hperm_filter :
        (Finset.univ.filter (fun i : Fin n => e i = d)).card =
        (Finset.univ.filter
          (fun j : Fin m.toList.length => m.toList.get j = d)).card := by
      apply Finset.card_bij (fun (i : Fin n) _ => Fin.cast hlen.symm i)
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hi
      · intros _ _ _ _; intro h; exact Fin.cast_injective _ h
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        refine ⟨Fin.cast hlen j, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          change m.toList.get (Fin.cast hlen.symm (Fin.cast hlen j)) = d
          have : Fin.cast hlen.symm (Fin.cast hlen j) = j := by ext; rfl
          rw [this]; exact hj
        · ext; rfl
    rw [hperm_filter]
    -- Connect filter card to multiset count via List.Vector
    have hcount_eq : (Finset.univ.filter (fun j : Fin m.toList.length => m.toList.get j = d)).card =
                     Multiset.count d m := by
      let hv : List.Vector S m.toList.length := ⟨m.toList, rfl⟩
      have key := Fin.card_filter_univ_eq_vector_get_eq_count d hv
      have hvtoList : hv.toList = m.toList := rfl
      -- Both BEq instances on Subtype S agree (both reduce to underlying decidable equality)
      have hBEq_inst : (Subtype.instBEq : BEq S) = (instBEqOfDecidableEq : BEq S) := by
        ext x y
        rcases x with ⟨xv, hx⟩
        rcases y with ⟨yv, hy⟩
        simp [Subtype.instBEq, instBEqOfDecidableEq]
      have hbridge : @List.count S Subtype.instBEq d m.toList = Multiset.count d m := by
        rw [hBEq_inst, ← Multiset.coe_count, Multiset.coe_toList]
      rw [← hbridge, ← hvtoList]
      convert key using 2
    rw [hcount_eq]
    exact hA4 d
  -- B: ∑ i, (e i).val = (something) — but actually we need norm version directly
  -- C: Compute (∑ i, (e i).val).norm p via fiberwise reorganisation
  --    Mirror the hφ₀_norm_eq pattern with e/φ instead of witness/φ₀
  have hsupp_norm_subset :
      Function.support (fun d : S => (d.val.norm p) * (φ d : ℚ)) ⊆ ↑T := by
    intro d hd
    simp only [Function.mem_support] at hd
    apply hsupp_φ_subset
    intro hφd
    apply hd
    rw [show (φ d : ℚ) = ((φ d : ℕ) : ℚ) from rfl, hφd]
    simp
  have hφ_norm_eq : (∑ᶠ d : S, (d.val.norm p) * (φ d : ℚ)) =
                    (∑ i : Fin n, (e i).val).norm p := by
    rw [finsum_eq_sum_of_support_subset _ hsupp_norm_subset]
    -- Substitute φ d = Nat.card (e ⁻¹' {d}) via hA5
    have h_rewrite : ∀ d ∈ T,
        (d.val.norm p) * (φ d : ℚ) =
        (d.val.norm p) * ((Nat.card ↑(e ⁻¹' {d}) : ℕ) : ℚ) := by
      intro d _; rw [hA5 d]
    rw [Finset.sum_congr rfl h_rewrite]
    -- Now mirror the hφ₀_norm_eq pattern: regroup via fiberwise
    have h_card_eq : ∀ x : S,
        Nat.card ↑(e ⁻¹' {x}) =
        (Finset.univ.filter (fun i : Fin n => e i = x)).card := by
      intro x
      rw [show ↑(e ⁻¹' {x}) = {i : Fin n // e i = x} from rfl]
      exact Nat.subtype_card _ (fun i => by simp)
    have h_term : ∀ x ∈ T,
        (DigitSeries.norm p) ↑x * ((Nat.card ↑(e ⁻¹' {x}) : ℕ) : ℚ) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => e i = x),
          (e i).val.norm p := by
      intro x _
      rw [h_card_eq x]
      rw [Finset.sum_filter, Finset.card_filter]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : e i = x
      · simp [hi]
      · simp [hi]
    rw [Finset.sum_congr rfl h_term]
    -- Apply sum_fiberwise: need ∀ i, e i ∈ T
    have h_maps_to : ∀ i ∈ (Finset.univ : Finset (Fin n)), e i ∈ T := by
      intro i _
      -- Show φ (e i) ≠ 0 using hA5: Nat.card (e ⁻¹' {e i}) = φ (e i),
      -- and that preimage contains i.
      simp only [T, Set.Finite.mem_toFinset, Function.mem_support, ne_eq]
      intro hφei
      have hcard_zero : Nat.card ↑(e ⁻¹' ({e i} : Set ↑S)) = 0 := by
        rw [hA5]; exact hφei
      have hmem : i ∈ (e ⁻¹' ({e i} : Set ↑S)) := by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
      have h_nonempty : (e ⁻¹' ({e i} : Set ↑S)).Nonempty := ⟨i, hmem⟩
      rw [Nat.card_eq_zero] at hcard_zero
      cases hcard_zero with
      | inl h_empty =>
        have : Nonempty ↑(e ⁻¹' ({e i} : Set ↑S)) := h_nonempty.to_subtype
        exact not_nonempty_iff.mpr h_empty this
      | inr h_inf =>
        have : Finite ↑(e ⁻¹' ({e i} : Set ↑S)) :=
          Set.Finite.to_subtype (Set.toFinite _)
        exact Finite.not_infinite this h_inf
    rw [Finset.sum_fiberwise_of_maps_to h_maps_to (fun i => (e i).val.norm p)]
    -- Apply norm additivity
    rw [map_sum (DigitSeries.norm p) (fun i => (e i).val) Finset.univ]
  -- C: derive (∑ witness).norm p − (∑ e).norm p .isInt
  have hediff : ((∑ i : Fin n, (witness i).val).norm p -
                 (∑ i : Fin n, (e i).val).norm p).isInt := by
    rw [← hφ₀_norm_eq, ← hφ_norm_eq]
    -- hφ_norm: (∑ᶠ φ - ∑ᶠ φ₀).isInt; we need (∑ᶠ φ₀ - ∑ᶠ φ).isInt
    -- Actually hφ_norm has form (φ-finsum - φ₀-finsum).isInt
    -- We need (φ₀-finsum - φ-finsum).isInt; by symmetry of isInt under negation
    have h := hφ_norm
    -- hφ_norm: ((∑ᶠ d, norm d * φ d) - (∑ᶠ d, norm d * φ₀ d)).isInt
    -- We want: ((∑ᶠ d, norm d * φ₀ d) - (∑ᶠ d, norm d * φ d)).isInt
    have hneg : ∀ x : ℚ, x.isInt → (-x).isInt := fun x hx => by
      rw [Rat.isInt] at hx ⊢; rw [Rat.neg_den]; exact hx
    have := hneg _ h
    rw [neg_sub] at this
    exact this
  -- D: Apply hwitness_unique
  obtain ⟨perm, hperm⟩ := hwitness_unique e hediff
  -- E: Conclude φ = φ₀ hSparse
  funext d
  -- φ₀ hSparse d = Nat.card (witness ⁻¹' {d})
  change φ d = Nat.card (witness ⁻¹' {d})
  -- witness = e ∘ perm  ⇒  witness ⁻¹' {d} = perm ⁻¹' (e ⁻¹' {d})
  have hwit_eq : witness = e ∘ perm := by
    funext i; exact hperm i
  rw [hwit_eq, Set.preimage_comp]
  -- Nat.card (perm ⁻¹' (e ⁻¹' {d})) = Nat.card (e ⁻¹' {d})
  have hperm_card : Nat.card ↑(⇑perm ⁻¹' (e ⁻¹' {d})) = Nat.card ↑(e ⁻¹' {d}) :=
    Nat.card_preimage_of_injective perm.injective (by
      intro x _; exact ⟨perm.symm x, by simp⟩)
  rw [hperm_card, hA5]

end Sparse
