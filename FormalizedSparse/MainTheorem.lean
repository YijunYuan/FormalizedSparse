import FormalizedSparse.References.Poonen1993
import FormalizedSparse.Sparse

open Sparse

def IsRepModZ (A B : Set ℚ) : Prop :=
  (
    ∀ b ∈ B, ∃! a ∈ A, (a - b).isInt
  ) ∧ (
    ∀ a ∈ A, ∃ b ∈ B, (a - b).isInt
  )



theorem main_theorem (p : ℕ) [Fact (Nat.Prime p)] (f : 𝕃_[p])
(T : ℕ+) (hf1 : ∀ q ∈ f.support, ∃ k : ℕ, (T * (p ^ k) * q).isInt)
(S : Set (DigitSeries)) (hS : IsSparse p S)
(hf2 : IsRepModZ ((DigitSeries.norm p) '' S) {-1 * T * q | q ∈ f.support}) :
  ¬ IsAlgebraic ℚᵘⁿ_[p] f := by
  by_contra hc
  rcases hc with ⟨P', hP₀, hP⟩
  let P := P' * Polynomial.C P'.leadingCoeff⁻¹
  replace hP₀ : P.Monic := Polynomial.monic_mul_leadingCoeff_inv hP₀
  replace hP : (Polynomial.aeval f) P = 0 := by
    unfold P
    simp [hP]

  sorry
