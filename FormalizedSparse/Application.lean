import FormalizedSparse.MainTheorem

open Sparse Poonen1993 Poonen1993.pAdicHahnSeries WittVector

theorem trans_of_digit_disjoint (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p]) (A : ℕ → Set ℕ)
(hA1 : ∀ n, (A n).Nonempty) (hA2 : ∀ i j, (A i) ∩ (A j) ≠ ∅ → i = j)
(hA3 : ∀ n, (A n).Finite)
(hAsup : ∃ K : ℕ, (∀ n, (hA3 n).toFinset.card ≤ K))
(c : ℕ → ℤ) (T : ℕ+)
(hf : f.support = {(c i - ∑ r ∈ (hA3 i).toFinset, (p : ℚ) ^ (-(r : ℤ))) / T | i : ℕ}) :
  ¬ IsAlgebraic ℚᵘⁿ_[p] f := by
  classical
  -- σ i := ∑_{r ∈ A_i} p^{-r}, γ i := (c i - σ i) / T.
  set σ : ℕ → ℚ := fun i => ∑ r ∈ (hA3 i).toFinset, (p : ℚ) ^ (-(r : ℤ)) with hσ_def
  set γ : ℕ → ℚ := fun i => ((c i : ℚ) - σ i) / T with hγ_def
  have hf_supp : f.support = Set.range γ := by
    rw [hf]
    ext q
    simp only [σ, γ, Set.mem_setOf_eq, Set.mem_range]
  -- Basic positivity facts.
  have hp_prime : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := hp_prime.pos
  have hp_two : 2 ≤ p := hp_prime.two_le
  have hp_pos_Q : (0 : ℚ) < p := by exact_mod_cast hp_pos
  have hp_one_lt_Q : (1 : ℚ) < p := by exact_mod_cast hp_prime.one_lt
  -- σ n ≥ 0.
  have hσ_nonneg : ∀ n, 0 ≤ σ n := by
    intro n
    apply Finset.sum_nonneg
    intro r _
    positivity
  -- σ n = indicatorSeries.norm when 0 ∉ A n.
  have hσ_eq_norm : ∀ n, 0 ∉ A n →
      (Sparse.indicatorSeries (A n) (hA3 n)).norm p = σ n := by
    intro n h0
    classical
    set fn : Sparse.DigitSeries := Sparse.indicatorSeries (A n) (hA3 n) with hfn_def
    change ∑ k ∈ fn.fin_supp.toFinset,
        ((fn : ℕ+ → ℕ) k : ℚ) * (p : ℚ) ^ (-(k : ℤ)) = σ n
    have hsupp : fn.fin_supp.toFinset =
        ((hA3 n).preimage (PNat.coe_injective.injOn)).toFinset := by
      ext k
      simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, Set.mem_preimage]
      change (fn : ℕ+ → ℕ) k ≠ 0 ↔ (k : ℕ) ∈ A n
      have hval : (fn : ℕ+ → ℕ) k =
          (haveI := Classical.propDecidable ((k : ℕ) ∈ A n);
            if (k : ℕ) ∈ A n then (1 : ℕ) else 0) := rfl
      rw [hval]
      by_cases hin : (k : ℕ) ∈ A n
      · simp [hin]
      · simp [hin]
    have hval_eq : ∀ k ∈ ((hA3 n).preimage (PNat.coe_injective.injOn)).toFinset,
        ((fn : ℕ+ → ℕ) k : ℚ) * (p : ℚ) ^ (-(k : ℤ)) = (p : ℚ) ^ (-(k : ℤ)) := by
      intro k hk
      simp only [Set.Finite.mem_toFinset, Set.mem_preimage] at hk
      have hval : (fn : ℕ+ → ℕ) k =
          (haveI := Classical.propDecidable ((k : ℕ) ∈ A n);
            if (k : ℕ) ∈ A n then (1 : ℕ) else 0) := rfl
      rw [hval]
      simp [hk]
    rw [hsupp, Finset.sum_congr rfl hval_eq]
    change ∑ k ∈ ((hA3 n).preimage (PNat.coe_injective.injOn)).toFinset,
        (p : ℚ) ^ (-((k : ℕ) : ℤ)) = ∑ r ∈ (hA3 n).toFinset, (p : ℚ) ^ (-(r : ℤ))
    refine Finset.sum_bij (fun (k : ℕ+) _ => (k : ℕ)) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Set.Finite.mem_toFinset, Set.mem_preimage] at hk
      simpa [Set.Finite.mem_toFinset] using hk
    · intro k₁ _ k₂ _ heq; exact PNat.coe_injective heq
    · intro r hr
      simp only [Set.Finite.mem_toFinset] at hr
      have hr_ne : r ≠ 0 := fun heq => h0 (heq ▸ hr)
      refine ⟨⟨r, Nat.pos_of_ne_zero hr_ne⟩, ?_, rfl⟩
      simp only [Set.Finite.mem_toFinset, Set.mem_preimage]
      exact hr
    · intro k _; rfl
  -- σ n < 1 when 0 ∉ A n.
  have hσ_lt_one : ∀ n, 0 ∉ A n → σ n < 1 := by
    intro n h0
    rw [← hσ_eq_norm n h0]
    exact (DigitSeries.norm_mem_Ico p _ (Sparse.indicatorSeries_IsP p _ _)).2
  -- σ n ≥ 1 when 0 ∈ A n.
  have hσ_ge_one : ∀ n, 0 ∈ A n → 1 ≤ σ n := by
    intro n hn
    have h0_in : (0 : ℕ) ∈ (hA3 n).toFinset := by simpa using hn
    calc (1 : ℚ) = (p : ℚ) ^ (-((0 : ℕ) : ℤ)) := by simp
      _ ≤ ∑ r ∈ (hA3 n).toFinset, (p : ℚ) ^ (-((r : ℕ) : ℤ)) := by
          refine Finset.single_le_sum
            (f := fun (r : ℕ) => (p : ℚ) ^ (-(r : ℤ)))
            (s := (hA3 n).toFinset) (fun r _ => ?_) h0_in
          positivity
      _ = σ n := rfl
  -- Digit uniqueness.
  have hσ_inj_good : ∀ i j, 0 ∉ A i → 0 ∉ A j → σ i = σ j → A i = A j := by
    intro i j hi hj hij
    have hf_i := Sparse.indicatorSeries_IsP p (A i) (hA3 i)
    have hf_j := Sparse.indicatorSeries_IsP p (A j) (hA3 j)
    have hni := hσ_eq_norm i hi
    have hnj := hσ_eq_norm j hj
    have hsub : ((Sparse.indicatorSeries (A i) (hA3 i)).norm p -
        (Sparse.indicatorSeries (A j) (hA3 j)).norm p).isInt := by
      rw [hni, hnj, hij, sub_self, Rat.isInt]; simp
    have heq := Sparse.DigitSeries.eq_of_norm_sub_isInt hf_i hf_j hsub
    ext r
    by_cases hr0 : r = 0
    · subst hr0
      exact ⟨fun h => absurd h hi, fun h => absurd h hj⟩
    set r' : ℕ+ := ⟨r, Nat.pos_of_ne_zero hr0⟩ with hr'_def
    have hri_iff : r ∈ A i ↔ (Sparse.indicatorSeries (A i) (hA3 i) : ℕ+ → ℕ) r' = 1 := by
      change r ∈ A i ↔ (haveI := Classical.propDecidable (r ∈ A i);
        if r ∈ A i then (1 : ℕ) else 0) = 1
      by_cases hi' : r ∈ A i
      · simp [hi']
      · simp [hi']
    have hrj_iff : r ∈ A j ↔ (Sparse.indicatorSeries (A j) (hA3 j) : ℕ+ → ℕ) r' = 1 := by
      change r ∈ A j ↔ (haveI := Classical.propDecidable (r ∈ A j);
        if r ∈ A j then (1 : ℕ) else 0) = 1
      by_cases hj' : r ∈ A j
      · simp [hj']
      · simp [hj']
    rw [hri_iff, hrj_iff, heq]
  -- Indicator norm in [0, 1) regardless of whether 0 ∈ A n.
  have hindicator_norm_lt : ∀ n,
      (Sparse.indicatorSeries (A n) (hA3 n)).norm p < 1 :=
    fun n => (DigitSeries.norm_mem_Ico p _ (Sparse.indicatorSeries_IsP p _ _)).2
  have hindicator_norm_nn : ∀ n,
      0 ≤ (Sparse.indicatorSeries (A n) (hA3 n)).norm p :=
    fun n => (DigitSeries.norm_mem_Ico p _ (Sparse.indicatorSeries_IsP p _ _)).1
  -- For each k : ℕ+, indicator at k counts membership in A n at k.val.
  have hindicator_mem_iff : ∀ n (k : ℕ+),
      (Sparse.indicatorSeries (A n) (hA3 n) : ℕ+ → ℕ) k = 1 ↔ (k : ℕ) ∈ A n := by
    intro n k
    change (haveI := Classical.propDecidable ((k : ℕ) ∈ A n);
      if (k : ℕ) ∈ A n then (1 : ℕ) else 0) = 1 ↔ (k : ℕ) ∈ A n
    by_cases hin : (k : ℕ) ∈ A n
    · simp [hin]
    · simp [hin]
  -- From indicator series equality, conclude A's are equal except possibly at 0.
  have hindicator_eq_membership :
      ∀ S T : Set ℕ, ∀ hS : S.Finite, ∀ hT : T.Finite,
      Sparse.indicatorSeries S hS = Sparse.indicatorSeries T hT →
      ∀ r ≥ 1, r ∈ S ↔ r ∈ T := by
    intro S T hS hT heq r hr
    have hr_ne : r ≠ 0 := Nat.one_le_iff_ne_zero.mp hr
    set r' : ℕ+ := ⟨r, Nat.pos_of_ne_zero hr_ne⟩
    have hri : (Sparse.indicatorSeries S hS : ℕ+ → ℕ) r' =
        (Sparse.indicatorSeries T hT : ℕ+ → ℕ) r' :=
      by rw [heq]
    have hSi : (Sparse.indicatorSeries S hS : ℕ+ → ℕ) r' = 1 ↔ r ∈ S := by
      change (haveI := Classical.propDecidable (r ∈ S);
        if r ∈ S then (1 : ℕ) else 0) = 1 ↔ r ∈ S
      by_cases h : r ∈ S
      · simp [h]
      · simp [h]
    have hTi : (Sparse.indicatorSeries T hT : ℕ+ → ℕ) r' = 1 ↔ r ∈ T := by
      change (haveI := Classical.propDecidable (r ∈ T);
        if r ∈ T then (1 : ℕ) else 0) = 1 ↔ r ∈ T
      by_cases h : r ∈ T
      · simp [h]
      · simp [h]
    rw [← hSi, ← hTi, hri]
  -- σ-decomposition: σ n = (if 0 ∈ A n then 1 else 0) + (indicator A n).norm.
  have hσ_decomp : ∀ n, σ n = (if 0 ∈ A n then 1 else 0 : ℚ) +
      (Sparse.indicatorSeries (A n) (hA3 n)).norm p := by
    intro n
    classical
    -- Use the fact that indicator.norm = sum over r ∈ (toFinset).filter (· ≠ 0).
    -- Prove: σ n = (0-contribution) + indicator.norm.
    -- (0-contribution) = if 0 ∈ A n then 1 else 0.
    -- Step 1: indicator.norm = ∑_{r ∈ (hA3 n).toFinset.filter (·≠0)} p^{-r}.
    have hindicator_filter :
        (Sparse.indicatorSeries (A n) (hA3 n)).norm p =
          ∑ r ∈ (hA3 n).toFinset.filter (· ≠ 0), (p : ℚ) ^ (-(r : ℤ)) := by
      set fn : Sparse.DigitSeries := Sparse.indicatorSeries (A n) (hA3 n) with hfn_def
      change ∑ k ∈ fn.fin_supp.toFinset,
          ((fn : ℕ+ → ℕ) k : ℚ) * (p : ℚ) ^ (-(k : ℤ)) = _
      have hsupp : fn.fin_supp.toFinset =
          ((hA3 n).preimage (PNat.coe_injective.injOn)).toFinset := by
        ext k
        simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, Set.mem_preimage]
        change (fn : ℕ+ → ℕ) k ≠ 0 ↔ (k : ℕ) ∈ A n
        have hval : (fn : ℕ+ → ℕ) k =
            (haveI := Classical.propDecidable ((k : ℕ) ∈ A n);
              if (k : ℕ) ∈ A n then (1 : ℕ) else 0) := rfl
        rw [hval]
        by_cases hin : (k : ℕ) ∈ A n
        · simp [hin]
        · simp [hin]
      have hval_eq : ∀ k ∈ ((hA3 n).preimage (PNat.coe_injective.injOn)).toFinset,
          ((fn : ℕ+ → ℕ) k : ℚ) * (p : ℚ) ^ (-(k : ℤ)) = (p : ℚ) ^ (-(k : ℤ)) := by
        intro k hk
        simp only [Set.Finite.mem_toFinset, Set.mem_preimage] at hk
        have hval : (fn : ℕ+ → ℕ) k =
            (haveI := Classical.propDecidable ((k : ℕ) ∈ A n);
              if (k : ℕ) ∈ A n then (1 : ℕ) else 0) := rfl
        rw [hval]
        simp [hk]
      rw [hsupp, Finset.sum_congr rfl hval_eq]
      refine Finset.sum_bij (fun (k : ℕ+) _ => (k : ℕ)) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Set.Finite.mem_toFinset, Set.mem_preimage] at hk
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨hk, k.ne_zero⟩
      · intro k₁ _ k₂ _ heq; exact PNat.coe_injective heq
      · intro r hr
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hr
        refine ⟨⟨r, Nat.pos_of_ne_zero hr.2⟩, ?_, rfl⟩
        simp only [Set.Finite.mem_toFinset, Set.mem_preimage]
        exact hr.1
      · intro k _; rfl
    rw [hindicator_filter]
    -- Step 2: σ n = ∑ filter (=0) + ∑ filter (≠ 0).
    have hsum_split :
        ∑ r ∈ (hA3 n).toFinset, (p : ℚ) ^ (-(r : ℤ)) =
          (∑ r ∈ (hA3 n).toFinset.filter (· = 0), (p : ℚ) ^ (-(r : ℤ))) +
          (∑ r ∈ (hA3 n).toFinset.filter (· ≠ 0), (p : ℚ) ^ (-(r : ℤ))) := by
      have htotal := Finset.sum_filter_add_sum_filter_not (hA3 n).toFinset (· = 0)
        (fun r => (p : ℚ) ^ (-(r : ℤ)))
      -- htotal : ∑ filter (=0) + ∑ filter (¬(=0)) = ∑ over all.
      -- The filter (¬ (·=0)) and filter (· ≠ 0) are the same; coerce by congr.
      have : (∑ r ∈ (hA3 n).toFinset.filter (fun r => ¬ r = 0), (p : ℚ) ^ (-(r : ℤ))) =
          (∑ r ∈ (hA3 n).toFinset.filter (· ≠ 0), (p : ℚ) ^ (-(r : ℤ))) := by
        congr 1
      linarith
    change ∑ r ∈ (hA3 n).toFinset, (p : ℚ) ^ (-(r : ℤ)) =
        (if 0 ∈ A n then (1 : ℚ) else 0) +
        ∑ r ∈ (hA3 n).toFinset.filter (· ≠ 0), (p : ℚ) ^ (-(r : ℤ))
    rw [hsum_split]
    -- Step 3: ∑ filter (=0) = if 0 ∈ A n then 1 else 0.
    have hsum_zero : ∑ r ∈ (hA3 n).toFinset.filter (· = 0), (p : ℚ) ^ (-(r : ℤ)) =
        (if 0 ∈ A n then 1 else 0 : ℚ) := by
      by_cases h0 : 0 ∈ A n
      · rw [if_pos h0]
        have hfilter_eq : (hA3 n).toFinset.filter (· = 0) = {0} := by
          ext r
          simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_singleton]
          refine ⟨fun ⟨_, h⟩ => h, fun h => ?_⟩
          rw [h]; exact ⟨h0, rfl⟩
        rw [hfilter_eq, Finset.sum_singleton]
        simp
      · rw [if_neg h0]
        have hfilter_eq : (hA3 n).toFinset.filter (· = 0) = ∅ := by
          ext r
          simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.notMem_empty, iff_false]
          rintro ⟨hr, rfl⟩
          exact h0 hr
        rw [hfilter_eq, Finset.sum_empty]
    rw [hsum_zero]
  -- γ injectivity.
  have hγ_inj : Function.Injective γ := by
    intro i j hij
    have hT_pos : (0 : ℚ) < T := by exact_mod_cast T.pos
    have hT_ne : (T : ℚ) ≠ 0 := ne_of_gt hT_pos
    have h1 : (c i : ℚ) - σ i = (c j : ℚ) - σ j := by
      have h := hij
      change ((c i : ℚ) - σ i) = ((c j : ℚ) - σ j)
      have hh : ((c i : ℚ) - σ i) / (T : ℚ) = ((c j : ℚ) - σ j) / (T : ℚ) := h
      exact (div_left_inj' hT_ne).mp hh
    -- Combined approach: use hσ_decomp.
    -- σ i = α_i + ind_i where α_i = if 0 ∈ A i then 1 else 0, ind_i = (ind A i).norm.
    -- σ i - σ j = α_i - α_j + ind_i - ind_j.
    -- This is c_j - c_i ∈ ℤ.
    -- ind_i - ind_j ∈ (-1, 1).
    -- α_i - α_j ∈ {-1, 0, 1}.
    -- α_i - α_j + ind_i - ind_j ∈ (-2, 2). Integer.
    -- Three integer values: -1, 0, 1. (Cannot be -2 or 2 strictly.)
    -- Each forces specific values of α and ind.
    -- Most useful: α_i - α_j + ind_i - ind_j = α_i - α_j
    --   (since ind_i = ind_j when this is integer).
    -- Hmm, this might not be directly useful. Let's case-split on α_i and α_j.
    by_cases hi : 0 ∈ A i
    · by_cases hj : 0 ∈ A j
      · -- α_i = 1, α_j = 1. σ i - σ j = ind_i - ind_j ∈ (-1, 1) ∩ ℤ = {0}.
        -- So ind_i = ind_j, indicator series equal, conclude membership ≥ 1 equal.
        apply hA2 i j
        intro hcontra
        have h0in : (0 : ℕ) ∈ A i ∩ A j := ⟨hi, hj⟩
        rw [hcontra] at h0in
        exact Set.notMem_empty _ h0in
      · -- α_i = 1, α_j = 0. σ i - σ j = 1 + ind_i - ind_j ∈ (0, 2) ∩ ℤ = {1}.
        -- σ i - σ j = c_i - c_j.
        exfalso
        have hdσ : σ i - σ j = (c i - c j : ℤ) := by push_cast; linarith
        have hsi_decomp : σ i = 1 + (Sparse.indicatorSeries (A i) (hA3 i)).norm p := by
          have := hσ_decomp i; rw [if_pos hi] at this; linarith
        have hsj_decomp : σ j = (Sparse.indicatorSeries (A j) (hA3 j)).norm p := by
          have := hσ_decomp j; rw [if_neg hj] at this; linarith
        set ind_i := (Sparse.indicatorSeries (A i) (hA3 i)).norm p with hindi_def
        set ind_j := (Sparse.indicatorSeries (A j) (hA3 j)).norm p with hindj_def
        have hdiff_eq : 1 + ind_i - ind_j = ((c i - c j : ℤ) : ℚ) := by
          rw [hsi_decomp, hsj_decomp] at hdσ
          push_cast at hdσ ⊢; linarith
        have hind_i_lt : ind_i < 1 := hindicator_norm_lt i
        have hind_i_nn : 0 ≤ ind_i := hindicator_norm_nn i
        have hind_j_lt : ind_j < 1 := hindicator_norm_lt j
        have hind_j_nn : 0 ≤ ind_j := hindicator_norm_nn j
        have hint_val : c i - c j = 1 := by
          have h_lt : (((c i - c j : ℤ) : ℚ)) < 2 := by linarith
          have h_gt : (0 : ℚ) < ((c i - c j : ℤ) : ℚ) := by linarith
          have h1' : c i - c j < 2 := by exact_mod_cast h_lt
          have h2' : 0 < c i - c j := by exact_mod_cast h_gt
          omega
        have hind_eq : ind_i = ind_j := by
          have : ((c i - c j : ℤ) : ℚ) = 1 := by rw [hint_val]; push_cast; ring
          rw [this] at hdiff_eq
          linarith
        have hsub_int : (ind_i - ind_j).isInt := by
          rw [hind_eq, sub_self, Rat.isInt]; simp
        have heq_indicator := Sparse.DigitSeries.eq_of_norm_sub_isInt
          (Sparse.indicatorSeries_IsP p _ _)
          (Sparse.indicatorSeries_IsP p _ _)
          hsub_int
        have hmem_eq := hindicator_eq_membership (A i) (A j) (hA3 i) (hA3 j) heq_indicator
        -- A_j ⊆ ℕ_{≥1} since 0 ∉ A_j. And A_i ∩ ℕ_{≥1} = A_j.
        -- So A_j ⊆ A_i. Then A_i ∩ A_j = A_j, and A_j is nonempty.
        obtain ⟨a, ha⟩ := hA1 j
        have ha_pos : 1 ≤ a := by
          rcases Nat.eq_zero_or_pos a with h | h
          · exact absurd (h ▸ ha) hj
          · exact h
        have ha_in_i : a ∈ A i := (hmem_eq a ha_pos).mpr ha
        have habs : A i ∩ A j ≠ ∅ := by
          intro hcontra
          have : a ∈ A i ∩ A j := ⟨ha_in_i, ha⟩
          rw [hcontra] at this
          exact Set.notMem_empty _ this
        have hi_eq_j : i = j := hA2 i j habs
        rw [← hi_eq_j] at hj
        exact hj hi
    · by_cases hj : 0 ∈ A j
      · -- α_i = 0, α_j = 1. Symmetric to above.
        -- σ i - σ j = ind_i - 1 - ind_j = c_i - c_j ∈ ℤ.
        -- ind_i, ind_j ∈ [0, 1), so ind_i - 1 - ind_j ∈ (-2, 0). Integer iff -1.
        -- So c_i - c_j = -1, and ind_i = ind_j.
        exfalso
        have hdσ : σ i - σ j = (c i - c j : ℤ) := by push_cast; linarith
        have hsi_decomp : σ i = (Sparse.indicatorSeries (A i) (hA3 i)).norm p := by
          have := hσ_decomp i; rw [if_neg hi] at this; linarith
        have hsj_decomp : σ j = 1 + (Sparse.indicatorSeries (A j) (hA3 j)).norm p := by
          have := hσ_decomp j; rw [if_pos hj] at this; linarith
        set ind_i := (Sparse.indicatorSeries (A i) (hA3 i)).norm p with hindi_def
        set ind_j := (Sparse.indicatorSeries (A j) (hA3 j)).norm p with hindj_def
        have hdiff_eq : ind_i - 1 - ind_j = ((c i - c j : ℤ) : ℚ) := by
          rw [hsi_decomp, hsj_decomp] at hdσ
          push_cast at hdσ ⊢; linarith
        have hind_i_lt : ind_i < 1 := hindicator_norm_lt i
        have hind_i_nn : 0 ≤ ind_i := hindicator_norm_nn i
        have hind_j_lt : ind_j < 1 := hindicator_norm_lt j
        have hind_j_nn : 0 ≤ ind_j := hindicator_norm_nn j
        have hint_val : c i - c j = -1 := by
          have h_lt : (((c i - c j : ℤ) : ℚ)) < 0 := by linarith
          have h_gt : (-2 : ℚ) < ((c i - c j : ℤ) : ℚ) := by linarith
          have h1' : c i - c j < 0 := by exact_mod_cast h_lt
          have h2' : -2 < c i - c j := by exact_mod_cast h_gt
          omega
        have hind_eq : ind_i = ind_j := by
          have : ((c i - c j : ℤ) : ℚ) = -1 := by rw [hint_val]; push_cast; ring
          rw [this] at hdiff_eq
          linarith
        have hsub_int : (ind_i - ind_j).isInt := by
          rw [hind_eq, sub_self, Rat.isInt]; simp
        have heq_indicator := Sparse.DigitSeries.eq_of_norm_sub_isInt
          (Sparse.indicatorSeries_IsP p _ _)
          (Sparse.indicatorSeries_IsP p _ _)
          hsub_int
        have hmem_eq := hindicator_eq_membership (A i) (A j) (hA3 i) (hA3 j) heq_indicator
        obtain ⟨a, ha⟩ := hA1 i
        have ha_pos : 1 ≤ a := by
          rcases Nat.eq_zero_or_pos a with h | h
          · exact absurd (h ▸ ha) hi
          · exact h
        have ha_in_j : a ∈ A j := (hmem_eq a ha_pos).mp ha
        have habs : A i ∩ A j ≠ ∅ := by
          intro hcontra
          have : a ∈ A i ∩ A j := ⟨ha, ha_in_j⟩
          rw [hcontra] at this
          exact Set.notMem_empty _ this
        have hi_eq_j : i = j := hA2 i j habs
        rw [hi_eq_j] at hi
        exact hi hj
      · -- Neither has 0.
        have hσi : σ i < 1 := hσ_lt_one i hi
        have hσj : σ j < 1 := hσ_lt_one j hj
        have hd_lt : σ i - σ j < 1 := by linarith [hσ_nonneg j]
        have hd_gt : (-1 : ℚ) < σ i - σ j := by linarith [hσ_nonneg i]
        have hd_int : ∃ z : ℤ, (z : ℚ) = σ i - σ j := ⟨c i - c j, by push_cast; linarith⟩
        obtain ⟨z, hz⟩ := hd_int
        have hz_zero : z = 0 := by
          have hz_lt : (z : ℚ) < 1 := hz.symm ▸ hd_lt
          have hz_gt : (-1 : ℚ) < (z : ℚ) := hz.symm ▸ hd_gt
          have hz1 : z < 1 := by exact_mod_cast hz_lt
          have hz2 : -1 < z := by exact_mod_cast hz_gt
          omega
        rw [hz_zero] at hz
        have hσ_eq : σ i = σ j := by push_cast at hz; linarith
        have hA_eq : A i = A j := hσ_inj_good i j hi hj hσ_eq
        apply hA2 i j
        intro hcontra
        obtain ⟨a, ha⟩ := hA1 i
        have : a ∈ A i ∩ A j := ⟨ha, hA_eq ▸ ha⟩
        rw [hcontra] at this
        exact Set.notMem_empty _ this
  -- Extract K.
  obtain ⟨K, hK_bound⟩ := hAsup
  -- Pigeonhole.
  have hExistsInfN : ∃ k, k ≤ K ∧ Set.Infinite {n | (hA3 n).toFinset.card = k} := by
    by_contra hcontra
    push_neg at hcontra
    apply Set.infinite_univ (α := ℕ)
    have hsub : (Set.univ : Set ℕ) ⊆
        ⋃ k : Fin (K+1), {n | (hA3 n).toFinset.card = k.val} := by
      intro n _
      refine Set.mem_iUnion.mpr ⟨⟨(hA3 n).toFinset.card, Nat.lt_succ_of_le (hK_bound n)⟩, rfl⟩
    have hfin : (⋃ k : Fin (K+1), {n | (hA3 n).toFinset.card = k.val}).Finite := by
      apply Set.finite_iUnion
      intro k
      exact hcontra k.val (Nat.le_of_lt_succ k.isLt)
    exact hfin.subset hsub
  let candidates : Finset ℕ := (Finset.range (K+1)).filter
    (fun k => Set.Infinite {n | (hA3 n).toFinset.card = k})
  have hCand_nonempty : candidates.Nonempty := by
    rcases hExistsInfN with ⟨k, hk_le, hk_inf⟩
    refine ⟨k, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hk_le, hk_inf⟩
  let K_max := candidates.max' hCand_nonempty
  have hK_max_mem : K_max ∈ candidates := candidates.max'_mem hCand_nonempty
  have hK_max_le_K : K_max ≤ K := by
    have h : K_max ∈ Finset.range (K+1) := (Finset.mem_filter.mp hK_max_mem).1
    exact Nat.le_of_lt_succ (Finset.mem_range.mp h)
  have hK_max_inf : Set.Infinite {n | (hA3 n).toFinset.card = K_max} :=
    (Finset.mem_filter.mp hK_max_mem).2
  have hK_max_max : ∀ k > K_max, Set.Finite {n | (hA3 n).toFinset.card = k} := by
    intro k hk
    by_contra hinf
    have hinf' : Set.Infinite {n | (hA3 n).toFinset.card = k} := Set.not_finite.mp hinf
    have hk_le : k ≤ K := by
      by_contra hkK
      push_neg at hkK
      apply hinf'
      have hempty : {n | (hA3 n).toFinset.card = k} = ∅ := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hn
        have := hK_bound n
        omega
      rw [hempty]
      exact Set.finite_empty
    have : k ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hk_le, hinf'⟩
    have hle := candidates.le_max' k this
    omega
  -- Finiteness of {n | 0 ∈ A_n}.
  have h0_set_fin : {n | 0 ∈ A n}.Finite := by
    by_cases h_exists : ∃ n, 0 ∈ A n
    · rcases h_exists with ⟨n0, hn0⟩
      have hsub : {n | 0 ∈ A n} ⊆ {n0} := by
        intro n hn
        simp only [Set.mem_setOf_eq] at hn
        simp only [Set.mem_singleton_iff]
        apply hA2 n n0
        intro hcontra
        have : (0 : ℕ) ∈ A n ∩ A n0 := ⟨hn, hn0⟩
        rw [hcontra] at this
        exact Set.notMem_empty _ this
      exact (Set.finite_singleton n0).subset hsub
    · push_neg at h_exists
      have : {n | 0 ∈ A n} = ∅ := by ext n; simpa using h_exists n
      rw [this]; exact Set.finite_empty
  -- Define bad and good indices.
  let bad_indices : Set ℕ := {n | 0 ∈ A n} ∪ {n | (hA3 n).toFinset.card > K_max}
  have hbad_fin : bad_indices.Finite := by
    refine Set.Finite.union h0_set_fin ?_
    have hsub : {n | (hA3 n).toFinset.card > K_max} ⊆
        ⋃ k : Fin (K+1), (if K_max < k.val
          then {n | (hA3 n).toFinset.card = k.val} else (∅ : Set ℕ)) := by
      intro n hn
      simp only [Set.mem_setOf_eq] at hn
      refine Set.mem_iUnion.mpr ⟨⟨(hA3 n).toFinset.card, Nat.lt_succ_of_le (hK_bound n)⟩, ?_⟩
      rw [if_pos hn]
      rfl
    refine Set.Finite.subset ?_ hsub
    apply Set.finite_iUnion
    intro k
    by_cases hkmax : K_max < k.val
    · rw [if_pos hkmax]
      exact hK_max_max k.val hkmax
    · rw [if_neg hkmax]
      exact Set.finite_empty
  let good_indices : Set ℕ := (bad_indices)ᶜ
  have hgood_inf : good_indices.Infinite := by
    have hdiff : good_indices = (Set.univ : Set ℕ) \ bad_indices := by
      ext n
      constructor
      · intro hn; exact ⟨Set.mem_univ _, hn⟩
      · intro hn; exact hn.2
    rw [hdiff]
    exact Set.Infinite.diff Set.infinite_univ hbad_fin
  -- Build bijection ℕ ≃ good_indices.
  haveI : Infinite good_indices := Set.infinite_coe_iff.mpr hgood_inf
  let enumIso : ℕ ≃o good_indices := Nat.Subtype.orderIsoOfNat good_indices
  let enum : ℕ → ℕ := fun n => (enumIso n).val
  have henum_inj : Function.Injective enum := by
    intro a b hab
    exact enumIso.injective (Subtype.ext hab)
  have henum_mem : ∀ n, enum n ∈ good_indices := fun n => (enumIso n).property
  have henum_surj : ∀ m ∈ good_indices, ∃ n, enum n = m := by
    intro m hm
    refine ⟨enumIso.symm ⟨m, hm⟩, ?_⟩
    change ((enumIso (enumIso.symm ⟨m, hm⟩))).val = m
    rw [enumIso.apply_symm_apply]
  -- B = A ∘ enum.
  let B : ℕ → Set ℕ := fun n => A (enum n)
  have hB1 : ∀ n, (B n).Nonempty := fun n => hA1 (enum n)
  have hB2 : ∀ i j, B i ∩ B j ≠ ∅ → i = j := by
    intro i j hij; exact henum_inj (hA2 (enum i) (enum j) hij)
  have hB3 : ∀ n, (B n).Finite := fun n => hA3 (enum n)
  have hB0 : ∀ n, 0 ∉ B n := by
    intro n h0
    have henum_good : enum n ∈ good_indices := henum_mem n
    exact henum_good (Or.inl h0)
  have hBcard : ∀ n, (hB3 n).toFinset.card = (hA3 (enum n)).toFinset.card := fun _ => rfl
  -- Strong supremum.
  have hBsup : ∃ K' : ℕ, (∀ n, (hB3 n).toFinset.card ≤ K') ∧
      {n | (hB3 n).toFinset.card = K'}.Infinite := by
    refine ⟨K_max, ?_, ?_⟩
    · intro n
      rw [hBcard n]
      have henum_good : enum n ∈ good_indices := henum_mem n
      by_contra hcard
      push_neg at hcard
      exact henum_good (Or.inr hcard)
    · -- enum bijects {n | |B_n| = K_max} ↔ {m | card = K_max} ∩ good_indices.
      have hinf_int : ({m | (hA3 m).toFinset.card = K_max} ∩ good_indices : Set ℕ).Infinite := by
        have heq : ({m | (hA3 m).toFinset.card = K_max} ∩ good_indices : Set ℕ) =
            {m | (hA3 m).toFinset.card = K_max} \ {n | 0 ∈ A n} := by
          ext m
          simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_setOf_eq, good_indices,
            Set.mem_compl_iff, bad_indices, Set.mem_union]
          refine ⟨fun h => ⟨h.1, fun h0 => h.2 (Or.inl h0)⟩, fun h => ⟨h.1, fun hbad => ?_⟩⟩
          rcases hbad with h0 | hk
          · exact h.2 h0
          · omega
        rw [heq]
        exact hK_max_inf.diff h0_set_fin
      apply Set.Infinite.mono (s := enum ⁻¹' ({m | (hA3 m).toFinset.card = K_max} ∩ good_indices))
      · intro n hn
        simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq] at hn
        change (hB3 n).toFinset.card = K_max
        rw [hBcard n]; exact hn.1
      · apply Set.Infinite.preimage hinf_int
        intro m hm
        rcases henum_surj m hm.2 with ⟨n, hn⟩
        exact ⟨n, hn⟩
  -- Apply IsSparse_of_digit_disjoint₀ to B.
  have hSparse_W : IsSparse p {∑ r ∈ (hB3 i).toFinset, (p : ℚ) ^ (-(r : ℤ)) | i : ℕ} :=
    Sparse.IsSparse_of_digit_disjoint₀ p B hB1 hB2 hB3 hB0 hBsup
  set W : Set ℚ := {∑ r ∈ (hB3 i).toFinset, (p : ℚ) ^ (-(r : ℤ)) | i : ℕ} with hW_def
  -- W = σ '' good_indices.
  have hW_eq : W = σ '' good_indices := by
    ext q
    simp only [hW_def, σ, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨enum n, henum_mem n, ?_⟩
      -- hn : ∑ r ∈ (hB3 n).toFinset, _ = q
      -- Goal: ∑ r ∈ (hA3 (enum n)).toFinset, _ = q
      -- (hB3 n).toFinset = (hA3 (enum n)).toFinset by def.
      exact hn
    · rintro ⟨m, hm, hmq⟩
      rcases henum_surj m hm with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      -- Goal: ∑ r ∈ (hB3 n).toFinset, _ = q
      -- (hB3 n).toFinset = (hA3 (enum n)).toFinset = (hA3 m).toFinset (using hn).
      change ∑ r ∈ (hA3 (enum n)).toFinset, (p : ℚ) ^ (-(r : ℤ)) = q
      rw [hn]; exact hmq
  have hSparse_W' : IsSparse p W := hW_eq ▸ hSparse_W
  -- bad_support = γ '' bad_indices, finite.
  let bad_support : Set ℚ := γ '' bad_indices
  have hbad_supp_fin : bad_support.Finite := hbad_fin.image γ
  have hbad_supp_subset : bad_support ⊆ f.support := by
    rw [hf_supp]
    intro q hq
    rcases hq with ⟨n, _, rfl⟩
    exact ⟨n, rfl⟩
  have hbad_supp_pwo : bad_support.IsPWO := hbad_supp_fin.isPWO
  -- good_support = γ '' good_indices.
  let good_support : Set ℚ := γ '' good_indices
  have hgood_supp_eq : good_support = f.support \ bad_support := by
    change γ '' good_indices = f.support \ (γ '' bad_indices)
    rw [hf_supp]
    ext q
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨n, rfl⟩, ?_⟩
      rintro ⟨m, hm, heq⟩
      have : m = n := hγ_inj heq
      rw [← this] at hn
      exact hn hm
    · rintro ⟨⟨n, rfl⟩, hne⟩
      refine ⟨n, ?_, rfl⟩
      intro hbad
      apply hne
      exact ⟨n, hbad, rfl⟩
  have hgood_supp_subset : good_support ⊆ f.support := by
    rw [hgood_supp_eq]; exact Set.diff_subset
  have hgood_supp_pwo : good_support.IsPWO := by
    rw [hgood_supp_eq]
    exact (Poonen1993.support_IsPWO f).mono Set.diff_subset
  -- f_bad := from_coeff (q ↦ if q ∈ bad_support then f.coeff q else 0).
  let s_bad : ℚ → Fpbar p := fun q => if q ∈ bad_support then f.coeff q else 0
  have hs_bad_supp_sub : Function.support s_bad ⊆ bad_support := by
    intro q hq
    simp only [Function.mem_support, ne_eq, s_bad] at hq
    by_contra hnot
    rw [if_neg hnot] at hq
    exact hq rfl
  have hs_bad_pwo : (Function.support s_bad).IsPWO :=
    hbad_supp_pwo.mono hs_bad_supp_sub
  let f_bad : 𝕃_[p] := from_coeff s_bad hs_bad_pwo
  have hf_bad_coeff : f_bad.coeff = s_bad := coeff_of_from_coeff_eq_self s_bad hs_bad_pwo
  have hf_bad_supp : f_bad.support ⊆ bad_support := by
    change Function.support f_bad.coeff ⊆ bad_support
    rw [hf_bad_coeff]; exact hs_bad_supp_sub
  have hf_bad_supp_fin : f_bad.support.Finite := hbad_supp_fin.subset hf_bad_supp
  -- f_good := from_coeff (q ↦ if q ∈ good_support then f.coeff q else 0).
  let s_good : ℚ → Fpbar p := fun q => if q ∈ good_support then f.coeff q else 0
  have hs_good_supp_sub : Function.support s_good ⊆ good_support := by
    intro q hq
    simp only [Function.mem_support, ne_eq, s_good] at hq
    by_contra hnot
    rw [if_neg hnot] at hq
    exact hq rfl
  have hs_good_pwo : (Function.support s_good).IsPWO :=
    hgood_supp_pwo.mono hs_good_supp_sub
  let f_good : 𝕃_[p] := from_coeff s_good hs_good_pwo
  have hf_good_coeff : f_good.coeff = s_good := coeff_of_from_coeff_eq_self s_good hs_good_pwo
  have hf_good_supp : f_good.support = good_support := by
    change Function.support f_good.coeff = good_support
    rw [hf_good_coeff]
    ext q
    simp only [Function.mem_support, ne_eq, s_good]
    by_cases hq : q ∈ good_support
    · rw [if_pos hq]
      refine ⟨fun _ => hq, fun _ hc => ?_⟩
      have : q ∈ f.support := hgood_supp_subset hq
      exact this hc
    · rw [if_neg hq]
      simp [hq]
  -- f = f_good + f_bad.
  have hf_decomp : f = f_good + f_bad := by
    -- Lift to LPHS, equate, then quotient.
    have hL_eq :
        Poonen1993.LiftedPAdicHahnSeries.from_coeff s_good hs_good_pwo +
        Poonen1993.LiftedPAdicHahnSeries.from_coeff s_bad hs_bad_pwo =
        Poonen1993.LiftedPAdicHahnSeries.from_coeff f.coeff
          (Poonen1993.support_IsPWO f) := by
      apply HahnSeries.ext
      funext q
      change (teichmuller p) (s_good q) + (teichmuller p) (s_bad q) =
        (teichmuller p) (f.coeff q)
      by_cases hq_good : q ∈ good_support
      · -- q ∈ good, q ∉ bad (disjoint).
        have hq_bad : q ∉ bad_support := by
          intro hq_bad
          rw [hgood_supp_eq] at hq_good
          exact hq_good.2 hq_bad
        have hs_g : s_good q = f.coeff q := by simp [s_good, hq_good]
        have hs_b : s_bad q = 0 := by simp [s_bad, hq_bad]
        rw [hs_g, hs_b, WittVector.teichmuller_zero]; ring
      · by_cases hq_bad : q ∈ bad_support
        · have hs_g : s_good q = 0 := by simp [s_good, hq_good]
          have hs_b : s_bad q = f.coeff q := by simp [s_bad, hq_bad]
          rw [hs_g, hs_b, WittVector.teichmuller_zero]; ring
        · have hs_g : s_good q = 0 := by simp [s_good, hq_good]
          have hs_b : s_bad q = 0 := by simp [s_bad, hq_bad]
          have hq_notin : q ∉ f.support := by
            rw [hgood_supp_eq] at hq_good
            intro hq_in
            exact hq_good ⟨hq_in, hq_bad⟩
          have hfc : f.coeff q = 0 := by
            by_contra hc
            exact hq_notin hc
          rw [hs_g, hs_b, hfc, WittVector.teichmuller_zero]; ring
    -- Now project.
    have hfg_eq :
        (Ideal.Quotient.mk (Poonen1993.NullSeriesIdeal p))
          (Poonen1993.LiftedPAdicHahnSeries.from_coeff s_good hs_good_pwo) +
        (Ideal.Quotient.mk (Poonen1993.NullSeriesIdeal p))
          (Poonen1993.LiftedPAdicHahnSeries.from_coeff s_bad hs_bad_pwo) =
        (Ideal.Quotient.mk (Poonen1993.NullSeriesIdeal p))
          (Poonen1993.LiftedPAdicHahnSeries.from_coeff f.coeff
            (Poonen1993.support_IsPWO f)) := by
      rw [← (Ideal.Quotient.mk (Poonen1993.NullSeriesIdeal p)).map_add]
      exact congrArg _ hL_eq
    have hfeq : f = from_coeff f.coeff (Poonen1993.support_IsPWO f) :=
      (Poonen1993.pAdicHahnSeries.from_coeff_of_coeff_eq_self f).symm
    rw [hfeq]
    exact hfg_eq.symm
  -- W ≠ {0}.
  have hW_ne : W ≠ {0} := by
    intro hW_zero
    have h_in : σ (enum 0) ∈ W := by
      rw [hW_eq]; exact ⟨enum 0, henum_mem 0, rfl⟩
    rw [hW_zero] at h_in
    simp only [Set.mem_singleton_iff] at h_in
    have henum_good : enum 0 ∈ good_indices := henum_mem 0
    have h0_notin : 0 ∉ A (enum 0) := fun h => henum_good (Or.inl h)
    have h_pos : 0 < σ (enum 0) := by
      obtain ⟨a, ha⟩ := hA1 (enum 0)
      have ha_pos : a ≥ 1 := by
        rcases Nat.eq_zero_or_pos a with h | h
        · exact absurd (h ▸ ha) h0_notin
        · exact h
      have ha_in : a ∈ (hA3 (enum 0)).toFinset := by simpa using ha
      calc (0 : ℚ) < (p : ℚ) ^ (-((a : ℕ) : ℤ)) := by positivity
        _ ≤ ∑ r ∈ (hA3 (enum 0)).toFinset, (p : ℚ) ^ (-((r : ℕ) : ℤ)) := by
            refine Finset.single_le_sum (f := fun (r : ℕ) => (p : ℚ) ^ (-(r : ℤ)))
              (s := (hA3 (enum 0)).toFinset) (fun r _ => ?_) ha_in
            positivity
        _ = σ (enum 0) := rfl
    linarith
  -- IsRepModZ.
  have hRep : IsRepModZ W {x | ∃ q ∈ f_good.support, -1 * T * q = x} := by
    refine ⟨?_, ?_⟩
    · intro b hb
      rcases hb with ⟨q, hq, hbq⟩
      rw [hf_good_supp] at hq
      rcases hq with ⟨n, hn, rfl⟩
      have hT_ne : (T : ℚ) ≠ 0 := by
        have : (0 : ℚ) < T := by exact_mod_cast T.pos
        exact ne_of_gt this
      have hb_eq : b = σ n - c n := by
        rw [← hbq]
        change (-1 : ℚ) * (T : ℚ) * (((c n : ℚ) - σ n) / T) = σ n - c n
        field_simp; ring
      have hn_good : n ∈ good_indices := hn
      have h0_notin : 0 ∉ A n := fun h => hn_good (Or.inl h)
      refine ⟨σ n, ⟨?_, ?_⟩, ?_⟩
      · rw [hW_eq]; exact ⟨n, hn, rfl⟩
      · rw [hb_eq]
        have hint : σ n - (σ n - (c n : ℚ)) = ((c n : ℤ) : ℚ) := by ring
        rw [hint, Rat.isInt]; simp
      · rintro a ⟨ha_in, ha_int⟩
        rw [hW_eq] at ha_in
        rcases ha_in with ⟨m, hm, rfl⟩
        have hm_good : m ∈ good_indices := hm
        have hm_notin : 0 ∉ A m := fun h => hm_good (Or.inl h)
        have hσm : σ m < 1 := hσ_lt_one m hm_notin
        have hσn : σ n < 1 := hσ_lt_one n h0_notin
        -- ha_int : (σ m - (σ n - c n)).isInt = true.
        have ha_int' : (σ m - σ n + c n).isInt = true := by
          have : σ m - (σ n - (c n : ℚ)) = σ m - σ n + (c n : ℚ) := by ring
          rw [hb_eq] at ha_int
          have ha_int'' : (σ m - (σ n - (c n : ℚ))).isInt = true := ha_int
          rw [this] at ha_int''
          exact ha_int''
        -- σ m - σ n + c n ∈ ℤ. Let z = (this).num. Then σ m - σ n = z - c n.
        have hz_eq : σ m - σ n + (c n : ℚ) = (((σ m - σ n + c n : ℚ).num : ℤ) : ℚ) :=
          Rat.eq_num_of_isInt ha_int'
        set z : ℤ := (σ m - σ n + (c n : ℚ)).num with hz_def
        have hd_lt : σ m - σ n < 1 := by linarith [hσ_nonneg n]
        have hd_gt : (-1 : ℚ) < σ m - σ n := by linarith [hσ_nonneg m]
        have hzc : (z : ℚ) - (c n : ℚ) = σ m - σ n := by
          have := hz_eq
          push_cast at this
          linarith
        have hzc_lt : ((z - c n : ℤ) : ℚ) < 1 := by push_cast; linarith
        have hzc_gt : (-1 : ℚ) < ((z - c n : ℤ) : ℚ) := by push_cast; linarith
        have hzc_lt' : z - c n < 1 := by exact_mod_cast hzc_lt
        have hzc_gt' : -1 < z - c n := by exact_mod_cast hzc_gt
        have hz_eq2 : z - c n = 0 := by omega
        have hσ_eq : σ m = σ n := by
          have : (z : ℚ) - (c n : ℚ) = 0 := by
            have : ((z - c n : ℤ) : ℚ) = 0 := by exact_mod_cast hz_eq2
            push_cast at this; linarith
          linarith [hzc]
        have hA_eq : A m = A n := hσ_inj_good m n hm_notin h0_notin hσ_eq
        have hmn : m = n := by
          apply hA2 m n
          intro hcontra
          obtain ⟨a, ha⟩ := hA1 m
          have : a ∈ A m ∩ A n := ⟨ha, hA_eq ▸ ha⟩
          rw [hcontra] at this
          exact Set.notMem_empty _ this
        rw [hmn]
    · intro a ha
      rw [hW_eq] at ha
      rcases ha with ⟨n, hn, rfl⟩
      have hT_ne : (T : ℚ) ≠ 0 := by
        have : (0 : ℚ) < T := by exact_mod_cast T.pos
        exact ne_of_gt this
      refine ⟨(-1 : ℚ) * T * γ n, ⟨γ n, ?_, rfl⟩, ?_⟩
      · rw [hf_good_supp]; exact ⟨n, hn, rfl⟩
      · -- (σ n - (-1 * T * γ n)).isInt = true.
        have hint : σ n - ((-1 : ℚ) * T * γ n) = ((c n : ℤ) : ℚ) := by
          change σ n - (-1 : ℚ) * (T : ℚ) * (((c n : ℚ) - σ n) / T) = ((c n : ℤ) : ℚ)
          field_simp; ring
        rw [hint, Rat.isInt]; simp
  -- Apply main_theorem.
  have hf_good_not_alg : ¬ IsAlgebraic ℚᵘⁿ_[p] f_good :=
    main_theorem p f_good T W hW_ne hSparse_W' hRep
  -- f_bad is algebraic.
  have hf_bad_alg : IsAlgebraic ℚᵘⁿ_[p] f_bad :=
    alg_QpUn_of_alg_Qp p f_bad (alg_of_fin_supp p f_bad hf_bad_supp_fin)
  -- Conclude.
  intro hf_alg
  apply hf_good_not_alg
  have hf_good_eq : f_good = f - f_bad := by
    have h := hf_decomp
    linear_combination -h
  rw [hf_good_eq]
  exact hf_alg.sub hf_bad_alg

/- Proof of (2 ⇒ 1), contrapositive: infinite support ⇒ not algebraic.
We have hDenum : Denumerable f.support (L826). Enumerate f.support = {q n | n : ℕ}.
Since hf says each support element has form -(p)^(-i) for i : ℕ+, use Classical.choose
to pick k_n : ℕ+ such that q n = -(p)^(-(k_n : ℤ)). Injectivity of i ↦ -(p)^(-i) (p > 1)
gives that k_i = k_j ⇒ q_i = q_j ⇒ i = j (by Denumerable bijection).
Apply trans_of_digit_disjoint p f A hA1 hA2 hA3 hAsup c T hf_eq with:
  A n := {(k_n : ℕ)}  (singletons → pairwise disjoint, hA2 trivial),
  c n := 0, T := 1.
Then (0 - p^(-k_n)) / 1 = -(p)^(-k_n) = q n,
  so hf_eq : f.support = {(c i - Σ_{r∈A_i} p^(-r)) / T | i}.
trans_of_digit_disjoint yields ¬ IsAlgebraic ℚᵘⁿ_[p] f, closing the contraposed goal.
Discard the partial-application skeleton L829-832; write a self-contained have chain + refine.
-/
theorem pAdicHuangStefanescu (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p])
(hf : f.support ⊆ {-(p : ℚ) ^ (-(i : ℤ)) | i : ℕ+}) :
List.TFAE [
  f.support.Finite,
  IsAlgebraic ℚᵘⁿ_[p] f,
  IsAlgebraic ℚ_[p] f
] := by
  tfae_have 3 → 2 := fun a ↦ alg_QpUn_of_alg_Qp p f a
  tfae_have 1 → 3 := fun a ↦ alg_of_fin_supp p f a
  tfae_have 2 → 1 := by
    intro h
    contrapose h
    have hDenum : Denumerable f.support := by
      refine (Set.countable_infinite_iff_nonempty_denumerable.1 ?_).some
      exact ⟨Set.Countable.mono hf <| Set.to_countable _, Set.not_finite.mp h⟩
    -- Enumerate f.support via Denumerable.
    set e : f.support ≃ ℕ := Denumerable.eqv f.support with he_def
    set q : ℕ → ℚ := fun n => (e.symm n).val with hq_def
    have hq_inj : Function.Injective q := by
      intro i j hij
      have hsub : e.symm i = e.symm j := Subtype.ext hij
      exact e.symm.injective hsub
    have hq_mem : ∀ n, q n ∈ f.support := fun n => (e.symm n).property
    have hq_range : Set.range q = f.support := by
      ext x
      refine ⟨?_, ?_⟩
      · rintro ⟨n, rfl⟩
        exact hq_mem n
      · intro hx
        refine ⟨e ⟨x, hx⟩, ?_⟩
        simp [q]
    -- Each q n has the form -(p)^(-(k n : ℕ)) for some k n : ℕ+.
    have hq_form : ∀ n, ∃ k : ℕ+, q n = -((p : ℚ) ^ (-((k : ℕ) : ℤ))) := by
      intro n
      have hmem : q n ∈ {x : ℚ | ∃ i : ℕ+, -((p : ℚ) ^ (-((i : ℕ) : ℤ))) = x} := hf (hq_mem n)
      rcases hmem with ⟨k, hk⟩
      exact ⟨k, hk.symm⟩
    set k : ℕ → ℕ+ := fun n => Classical.choose (hq_form n) with hk_def
    have hk_eq : ∀ n, q n = -((p : ℚ) ^ (-((k n : ℕ) : ℤ))) :=
      fun n => Classical.choose_spec (hq_form n)
    -- Injectivity of i ↦ -(p:ℚ)^(-(i:ℤ)) implies k is injective.
    have hp_pos_Q : (0 : ℚ) < p := by
      have hp := (Fact.out : Nat.Prime p).pos
      exact_mod_cast hp
    have hp_ne_one : (p : ℚ) ≠ 1 := by
      have hp1 := (Fact.out : Nat.Prime p).one_lt
      have hpQ_gt : (1 : ℚ) < p := by exact_mod_cast hp1
      exact (ne_of_lt hpQ_gt).symm
    have hzpow_inj : Function.Injective (fun n : ℤ => (p : ℚ) ^ n) :=
      zpow_right_injective₀ hp_pos_Q hp_ne_one
    have hk_inj : Function.Injective k := by
      intro i j hij
      apply hq_inj
      rw [hk_eq i, hk_eq j, hij]
    -- Singleton support sets A n = {(k n : ℕ)}.
    set A : ℕ → Set ℕ := fun n => {(k n : ℕ)} with hA_def
    have hA1 : ∀ n, (A n).Nonempty := fun n => ⟨(k n : ℕ), rfl⟩
    have hA3 : ∀ n, (A n).Finite := fun n => Set.finite_singleton _
    have hA2 : ∀ i j, A i ∩ A j ≠ ∅ → i = j := by
      intro i j hne
      rcases Set.nonempty_iff_ne_empty.mpr hne with ⟨x, hxi, hxj⟩
      simp only [A, Set.mem_singleton_iff] at hxi hxj
      have hknat : (k i : ℕ) = (k j : ℕ) := hxi.symm.trans hxj
      exact hk_inj (PNat.coe_injective hknat)
    have hAsup : ∃ K : ℕ, ∀ n, (hA3 n).toFinset.card ≤ K := by
      refine ⟨1, fun n => ?_⟩
      rw [Set.Finite.toFinset_singleton]
      simp
    -- Apply trans_of_digit_disjoint.
    refine trans_of_digit_disjoint p f A hA1 hA2 hA3 hAsup (fun _ => 0) 1 ?_
    rw [← hq_range]
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨n, ?_⟩
      have hFin : (hA3 n).toFinset = ({(k n : ℕ)} : Finset ℕ) :=
        Set.Finite.toFinset_singleton _
      rw [hFin, Finset.sum_singleton]
      rw [hk_eq n]
      push_cast
      ring
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have hFin : (hA3 n).toFinset = ({(k n : ℕ)} : Finset ℕ) :=
        Set.Finite.toFinset_singleton _
      rw [hFin, Finset.sum_singleton] at hn
      rw [hk_eq n]
      push_cast at hn
      linarith
  tfae_finish
