import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.WittVector.Basic
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Int.Interval
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Valuation.ValuationSubring


namespace WithZeroRat

open Multiplicative WithZero
open scoped NNReal

/-- Send `WithZero (Multiplicative ℚ)` to `ℝ≥0` by `0 ↦ 0` and `q ↦ e ^ q`. -/
noncomputable def toNNReal {e : ℝ≥0} (he : e ≠ 0) : WithZero (Multiplicative ℚ) →*₀ ℝ≥0 where
  toFun := fun x ↦ if hx : x = 0 then 0 else e ^ (((WithZero.unzero hx).toAdd : ℚ) : ℝ)
  map_zero' := by simp
  map_one' := by
    simp only [dif_neg one_ne_zero]
    have hunzero_one : WithZero.unzero (α := Multiplicative ℚ) one_ne_zero = 1 := by
      apply WithZero.coe_inj.mp
      rfl
    rw [hunzero_one, toAdd_one]
    simp
  map_mul' x y := by
    by_cases hxy : x * y = 0
    · rcases mul_eq_zero.mp hxy with hx | hy
      · simp [hx]
      · simp [hy]
    · obtain ⟨hx, hy⟩ := mul_ne_zero_iff.mp hxy
      suffices
          e ^ (((WithZero.unzero hxy).toAdd : ℚ) : ℝ) =
            e ^ (((WithZero.unzero hx).toAdd : ℚ) : ℝ) *
              e ^ (((WithZero.unzero hy).toAdd : ℚ) : ℝ) by
        simpa [hxy, hx, hy]
      rw [← NNReal.rpow_add he]
      congr 1
      rw [← Rat.cast_add]
      have hunzero_mul : WithZero.unzero hxy = WithZero.unzero hx * WithZero.unzero hy := by
        apply WithZero.coe_inj.mp
        simp [coe_unzero hx, coe_unzero hy, coe_unzero hxy]
      exact congrArg Rat.cast <| by
        simpa [toAdd_mul] using congrArg Multiplicative.toAdd hunzero_mul

end WithZeroRat

@[simp]
lemma pInv_ne_zero (p : ℕ) [Fact (Nat.Prime p)] : (1 / (p : NNReal)) ≠ 0 := by
  simpa using NeZero.ne p
