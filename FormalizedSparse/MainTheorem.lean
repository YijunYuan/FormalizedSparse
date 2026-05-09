import FormalizedSparse.References.Poonen1993
import FormalizedSparse.Sparse
import Mathlib.Data.PNat.Interval

open Sparse

def IsRepModZ (A B : Set ℚ) : Prop :=
  (
    ∀ b ∈ B, ∃! a ∈ A, (a - b).isInt
  ) ∧ (
    ∀ a ∈ A, ∃ b ∈ B, (a - b).isInt
  )

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
  rcases hcD n hnD with ⟨hc, d, hd1, hdP, hd2⟩

  sorry
