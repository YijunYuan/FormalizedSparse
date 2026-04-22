import Mathlib
namespace Sparse

@[ext]
structure AdmissibleFun where
  toFun : ℕ+ → ℕ
  fin_supp : toFun.support.Finite

instance : FunLike (AdmissibleFun) ℕ+ ℕ where
  coe := AdmissibleFun.toFun
  coe_injective' := by
    rintro ⟨f, _⟩ ⟨g, _⟩ hfg
    simp only at hfg
    congr

@[ext]
structure PAdmissibleFun (p : ℕ) [Fact (Nat.Prime p)] extends AdmissibleFun where
  range_p : ∀ n, toFun n < p

instance {p : ℕ} [Fact (Nat.Prime p)] : FunLike (PAdmissibleFun p) ℕ+ ℕ where
  coe := fun f => f.toFun
  coe_injective' := by
    rintro ⟨f, _⟩ ⟨g, _⟩ hfg
    simp only at hfg
    congr
    exact DFunLike.ext' hfg

instance (p : ℕ) [Fact (Nat.Prime p)] : CoeOut (PAdmissibleFun p) AdmissibleFun where
  coe := PAdmissibleFun.toAdmissibleFun

instance : AddCommMonoid AdmissibleFun where
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

namespace AdmissibleFun

noncomputable def Sigma : AdmissibleFun →+ ℕ where
  toFun f := ∑ i ∈ f.fin_supp.toFinset, f i
  map_zero' := by
    classical
    change Finset.sum ((0 : AdmissibleFun).fin_supp.toFinset) (fun _ : ℕ+ => 0) = 0
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

noncomputable def maxIndex (f : AdmissibleFun) : ℕ :=
  f.fin_supp.toFinset.sup fun i => (i : ℕ)

def coeffs (f : ℕ+ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => f (Nat.succPNat n) :: coeffs f n

noncomputable def value (p : ℕ) (f : AdmissibleFun) (n : ℕ) : ℕ :=
  Nat.ofDigits p (coeffs f n)

def indices (n : ℕ) : Finset ℕ+ :=
  (Finset.range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩

@[simp] lemma coeffs_length (f : ℕ+ → ℕ) (n : ℕ) :
    (coeffs f n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [coeffs, ih]

@[simp] lemma mem_indices (n k : ℕ) :
    Nat.succPNat k ∈ indices n ↔ k < n := by
  simp [indices]

@[simp] lemma indices_succ (n : ℕ) :
    indices (n + 1) = insert (Nat.succPNat n) (indices n) := by
  ext i
  simp [indices, Finset.range_add_one, eq_comm]

lemma le_maxIndex_of_mem_support (f : AdmissibleFun) {n : ℕ+} (hn : f n ≠ 0) :
    (n : ℕ) ≤ f.maxIndex := by
  classical
  refine Finset.le_sup ?_
  simpa using hn

lemma eq_zero_of_maxIndex_lt (f : AdmissibleFun) {n : ℕ} (hn : f.maxIndex < n + 1) :
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

noncomputable def norm (p : ℕ) [Fact (Nat.Prime p)] : AdmissibleFun →+ ℚ where
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

lemma norm_additive (p : ℕ) [Fact (Nat.Prime p)] (a b : AdmissibleFun) :
    (a + b).norm p = a.norm p + b.norm p := by
  exact (norm p).map_add a b

lemma value_eq_sum_indices (f : AdmissibleFun) (p : ℕ) [Fact (Nat.Prime p)] :
    ∀ n,
      ((f.value p n : ℚ) * (p : ℚ) ^ (-(n : ℤ))) =
        Finset.sum (indices n) fun i => (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ))
  | 0 => by simp [AdmissibleFun.value, AdmissibleFun.indices]
  | n + 1 => by
      rw [AdmissibleFun.value, AdmissibleFun.coeffs, Nat.ofDigits_cons, AdmissibleFun.indices_succ,
        Finset.sum_insert]
      · calc
          (((f (Nat.succPNat n) + p * f.value p n : ℕ) : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ)))
              = (f (Nat.succPNat n) : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ))
                + ((f.value p n : ℚ) * (p : ℚ)) * (p : ℚ) ^ (-(n + 1 : ℤ)) := by norm_num; ring
          _ = (f (Nat.succPNat n) : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ))
                + (f.value p n : ℚ) * (p : ℚ) ^ (-(n : ℤ)) := by
                  rw [mul_assoc, AdmissibleFun.cast_mul_zpow_neg_succ]
          _ = (f (Nat.succPNat n) : ℚ) * (p : ℚ) ^ (-(Nat.succPNat n : ℤ))
                + Finset.sum (indices n) (fun i => (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ))) := by
                  rw [value_eq_sum_indices (f := f) (p := p) n]
                  simp
      · simp

lemma norm_eq_sum_indices (f : AdmissibleFun) (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ}
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
    simpa [PNat.succPNat_natPred] using (AdmissibleFun.mem_indices n i.natPred).2 hi_lt
  · intro i hi his
    have hzero : f i = 0 := by
      by_contra hne
      exact his (by simpa using hne)
    simp [hzero]

lemma norm_eq_value (f : AdmissibleFun) (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ}
    (hn : f.maxIndex < n) :
    f.norm p = ((f.value p n : ℚ) * (p : ℚ) ^ (-(n : ℤ))) := by
  rw [f.norm_eq_sum_indices p hn, ← f.value_eq_sum_indices p n]

lemma coeffs_update_above (f : ℕ+ → ℕ) (n m : ℕ) (hm : m ≤ n) (a : ℕ) :
    coeffs (Function.update f (Nat.succPNat n) a) m = coeffs f m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hm' : m ≤ n := Nat.le_trans (Nat.le_succ m) hm
      have hne : Nat.succPNat m ≠ Nat.succPNat n := by
        exact fun h => (Nat.lt_of_succ_le hm).ne (Nat.succPNat_injective h)
      simp [coeffs, Function.update, hne, ih hm']

noncomputable def ofCoeffs : List ℕ → AdmissibleFun
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
end AdmissibleFun

namespace PAdmissibleFun
noncomputable def norm {p : ℕ} [Fact (Nat.Prime p)] (f : PAdmissibleFun p) : ℚ :=
  f.toAdmissibleFun.norm p

lemma coeffs_lt {p : ℕ} [Fact (Nat.Prime p)] (f : PAdmissibleFun p) (n : ℕ) :
    ∀ x ∈ AdmissibleFun.coeffs f n, x < p := by
  intro x hx
  induction n generalizing x with
  | zero => cases hx
  | succ n ih =>
      simp only [AdmissibleFun.coeffs, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa using f.range_p (Nat.succPNat n)
      · exact ih _ hx

lemma value_lt_pow {p : ℕ} [Fact (Nat.Prime p)] (f : PAdmissibleFun p) (n : ℕ) :
    f.value p n < p ^ n := by
  unfold AdmissibleFun.value
  simpa [AdmissibleFun.coeffs_length] using
    Nat.ofDigits_lt_base_pow_length ((Fact.out : Nat.Prime p).one_lt) (f.coeffs_lt n)

lemma eq_of_norm_sub_isInt {p : ℕ} [Fact (Nat.Prime p)] {f g : PAdmissibleFun p}
    (hfg : (f.norm - g.norm).isInt) : f = g := by
  let n := max f.maxIndex g.maxIndex + 1
  have hfN : f.maxIndex < n := by simp [n]
  have hgN : g.maxIndex < n := by simp [n]
  let q : ℚ := f.norm - g.norm
  have hq : q.isInt := by simpa [q] using hfg
  have hq_expr : q = (((f.value p n : ℚ) - g.value p n) * (p : ℚ) ^ (-(n : ℤ))) := by
    simp [q, PAdmissibleFun.norm, f.norm_eq_value p hfN, g.norm_eq_value p hgN]
    ring
  have hq_lt : q < 1 := by
    rw [hq_expr]
    have hvf_lt : (f.value p n : ℚ) < (p : ℚ) ^ n := by
      exact_mod_cast f.value_lt_pow n
    have hp_pow_pos : 0 < (p : ℚ) ^ n := pow_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos) _
    have hdiff_lt : (f.value p n : ℚ) - g.value p n < (p : ℚ) ^ n := by nlinarith
    rw [show (p : ℚ) ^ (-(n : ℤ)) = ((p : ℚ) ^ n)⁻¹ by rw [zpow_neg, zpow_natCast]]
    simpa using mul_lt_mul_of_pos_right hdiff_lt (inv_pos.mpr hp_pow_pos)
  have hq_gt : (-1 : ℚ) < q := by
    rw [hq_expr]
    have hvg_lt : (g.value p n : ℚ) < (p : ℚ) ^ n := by
      exact_mod_cast g.value_lt_pow n
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
      AdmissibleFun.coeffs f n = AdmissibleFun.coeffs g n := by
    apply Nat.ofDigits_inj_of_len_eq ((Fact.out : Nat.Prime p).one_lt)
    · simp [AdmissibleFun.coeffs_length]
    · exact f.coeffs_lt n
    · exact g.coeffs_lt n
    · exact_mod_cast hval_eq
  ext i
  by_cases hi : (i : ℕ) ≤ n
  · exact AdmissibleFun.eq_on_of_coeffs_eq hcoeffs i hi
  · have hfi : f i = 0 := by
      by_contra hne
      exact hi (le_trans (f.le_maxIndex_of_mem_support hne) (Nat.le_of_lt hfN))
    have hgi : g i = 0 := by
      by_contra hne
      exact hi (le_trans (g.le_maxIndex_of_mem_support hne) (Nat.le_of_lt hgN))
    simpa using hfi.trans hgi.symm
end PAdmissibleFun

variable (p : ℕ) [Fact (Nat.Prime p)]

lemma lemma_1_2 (d : AdmissibleFun) :
    ∃! f : PAdmissibleFun p, (f.norm - d.norm p).isInt := by
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
  let fA := AdmissibleFun.ofCoeffs (0 :: L)
  let f : PAdmissibleFun p :=
    { toAdmissibleFun := fA
      range_p := AdmissibleFun.ofCoeffs_lt (p := p) (L := 0 :: L) (by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with hx | hx
        · subst x
          simpa using (Fact.out : Nat.Prime p).pos
        · exact hLlt x hx) }
  have hfmax : f.maxIndex < n + 1 := by
    simpa [f, fA, hLlen] using AdmissibleFun.maxIndex_ofCoeffs_zero_cons_lt (L := L)
  have hfval : f.value p (n + 1) = p * r := by
    have htmp :
        Nat.ofDigits p
          (AdmissibleFun.coeffs (AdmissibleFun.ofCoeffs (0 :: L)) ((0 :: L).length)) = p * r := by
      rw [AdmissibleFun.coeffs_ofCoeffs]
      simp [Nat.ofDigits_cons, hLdigits]
    simpa [AdmissibleFun.value, f, fA, hLlen] using htmp
  have hfnorm : f.norm = (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) := by
    rw [PAdmissibleFun.norm, f.norm_eq_value p hfmax, hfval, Nat.cast_mul]
    calc
      (↑p * ↑r) * (p : ℚ) ^ (-(n + 1 : ℤ)) = (↑r : ℚ) * ((p : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ))) := by
          ring
      _ = (r : ℚ) * (p : ℚ) ^ (-(n : ℤ)) := by
          rw [AdmissibleFun.cast_mul_zpow_neg_succ]
  have hfint : (f.norm - d.norm p).isInt := by
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
                  rw [AdmissibleFun.cast_pow_mul_zpow_neg]
                  ring
    rw [hdiff]
    simp [(by norm_num : (-↑qn : ℚ) = (((-(qn : ℤ)) : ℚ))), Rat.isInt]
  refine ⟨f, hfint, fun g hg => ?_⟩
  have hgf : (g.norm - f.norm).isInt := by
    have hcast :
        (((g.norm - d.norm p).num : ℚ) - ((f.norm - d.norm p).num : ℚ)) =
          (((g.norm - d.norm p).num - (f.norm - d.norm p).num : ℤ) : ℚ) := by
      norm_num
    have hgf_eq :
        g.norm - f.norm = (((g.norm - d.norm p).num : ℚ) - ((f.norm - d.norm p).num : ℚ)) := by
      calc
        g.norm - f.norm = (g.norm - d.norm p) - (f.norm - d.norm p) := by ring
        _ = (((g.norm - d.norm p).num : ℚ) - ((f.norm - d.norm p).num : ℚ)) := by
              rw [Rat.eq_num_of_isInt hg, Rat.eq_num_of_isInt hfint]
              simp [Rat.num_intCast]
    rw [hgf_eq, hcast, Rat.isInt]
    simp [Rat.den_intCast]
  exact PAdmissibleFun.eq_of_norm_sub_isInt hgf

namespace AdmissibleFun

noncomputable def tau (p : ℕ) [Fact (Nat.Prime p)] (f : AdmissibleFun) : PAdmissibleFun p :=
  (lemma_1_2 p f).choose

end AdmissibleFun

lemma lemma_1_3₂ (p : ℕ) [Fact (Nat.Prime p)] (f g : AdmissibleFun) :
  f.tau p = g.tau p ↔ (f.norm p - g.norm p).isInt := by
    constructor
    · intro htau
      have hf : ((f.tau p).norm - f.norm p).isInt := (lemma_1_2 p f).choose_spec.1
      have hg : ((g.tau p).norm - g.norm p).isInt := (lemma_1_2 p g).choose_spec.1
      have hg' : ((f.tau p).norm - g.norm p).isInt := by
        simpa [htau] using hg
      have hEq :
          f.norm p - g.norm p =
            ((f.tau p).norm - g.norm p) - ((f.tau p).norm - f.norm p) := by
        ring
      rw [Rat.isInt, Nat.beq_eq_true_eq] at hf hg'
      lift ((f.tau p).norm - g.norm p) to ℤ using hg' with a ha
      lift ((f.tau p).norm - f.norm p) to ℤ using hf with b hb
      have hmain : f.norm p - g.norm p = ((a - b : ℤ) : ℚ) := by
        calc
          f.norm p - g.norm p = (a : ℚ) - b := by simpa using hEq
          _ = ((a - b : ℤ) : ℚ) := by norm_num
      rw [hmain]
      simp [Rat.isInt]
    · intro hfg
      apply ((lemma_1_2 p g).choose_spec.2 (f.tau p))
      have hf : ((f.tau p).norm - f.norm p).isInt := (lemma_1_2 p f).choose_spec.1
      have hEq :
          (f.tau p).norm - g.norm p =
            ((f.tau p).norm - f.norm p) + (f.norm p - g.norm p) := by
        ring
      rw [Rat.isInt, Nat.beq_eq_true_eq] at hf hfg
      lift ((f.tau p).norm - f.norm p) to ℤ using hf with a ha
      lift (f.norm p - g.norm p) to ℤ using hfg with b hb
      have hmain : (f.tau p).norm - g.norm p = ((a + b : ℤ) : ℚ) := by
        calc
          (f.tau p).norm - g.norm p = (a : ℚ) + b := by simpa using hEq
          _ = ((a + b : ℤ) : ℚ) := by norm_num
      rw [hmain]
      simp [Rat.isInt]

end Sparse
