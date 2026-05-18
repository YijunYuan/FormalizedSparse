import FormalizedSparse.MainTheorem

/- USER: This corresponds to Proposition 5.3 of Sparse.pdf. You need to formalize the proof. Please follow the informal proof in Sparse.pdf.

Basically, this is an application of `main_theorem` in MainTheorem.lean, and `IsSparse_of_digit_disjoint₀` in Sparse.lean. The tricky part is to remove finitely many terms from the support of `f` to make it fit the condition of `IsSparse_of_digit_disjoint₀`. The saying `removing finitely many terms does not change algebraicity` is reflected in `alg_of_fin_supp` in Poonen1993.lean, which states that a p-adic Hahn series with finite support is algebraic over ℚ_[p] (which, consequently, is algebraic over ℚᵘⁿ_[p] by `alg_QpUn_of_alg_Qp` in Poonen1993.lean). This lemma is not proved yet, you should also formalize that.
-/
theorem trans_of_digit_disjoint (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p]) (A : ℕ → Set ℕ)
(hA1 : ∀ n, (A n).Nonempty) (hA2 : ∀ i j, (A i) ∩ (A j) ≠ ∅ → i = j)
(hA3 : ∀ n, (A n).Finite)
(hAsup : ∃ K : ℕ, (∀ n, (hA3 n).toFinset.card ≤ K))
(c : ℕ → ℤ) (T : ℕ+)
(hf : f.support = {(c i - ∑ r ∈ (hA3 i).toFinset, (p : ℚ) ^ (-(r : ℤ))) / T | i : ℕ}) :
  ¬ IsAlgebraic ℚᵘⁿ_[p] f := by

  sorry
