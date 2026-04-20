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
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.NumberTheory.Padics.Complex

open WittVector

-- The algebraic closure of F_p
abbrev Fpbar (p : ℕ) [Fact (Nat.Prime p)] := AlgebraicClosure (ZMod p)
notation "𝔽ᵃ_[" p "]" => Fpbar p

-- The ring of integers of the completion of the maximal unramified extension of Q_p,
-- which is the same as W(𝔽ₚ^⁻)((t^ℚ)).
abbrev OQpUn (p : ℕ) [Fact (Nat.Prime p)] := WittVector p (Fpbar p)
notation "ℤᵘⁿ_[" p "]" => OQpUn p

-- Equip RawQpUn p with the topology induced by the valuation QpUnVal p.
abbrev QpUn (p : ℕ) [Fact (Nat.Prime p)] :=
  WithVal ((IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation ((FractionRing (OQpUn p))))
notation "ℚᵘⁿ_[" p "]" => QpUn p

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
  Valued (ℚᵘⁿ_[p]) (WithZero (Multiplicative ℤ)) := inferInstance

instance (p : ℕ) [Fact (Nat.Prime p)] : CompleteSpace (ℚᵘⁿ_[p]) := by admit

-- The Teichmuller lift is injective.
theorem injective_teichmuller (p : ℕ) [Fact (Nat.Prime p)] :
  Function.Injective (teichmuller p : 𝔽ᵃ_[p] → ℤᵘⁿ_[p]) := by
  intro a b hab
  simp only [teichmuller, MonoidHom.coe_mk, OneHom.coe_mk, teichmullerFun, mk'.injEq] at hab
  apply_fun (fun x => x 0) at hab
  simpa

noncomputable def Qp_emd_QpUn (p : ℕ) [Fact (Nat.Prime p)] : ℚ_[p] →+* ℚᵘⁿ_[p] :=
  @IsFractionRing.map ℤ_[p] ℤᵘⁿ_[p] ℚ_[p] ℚᵘⁿ_[p] _ _ _ _ _ _ _ _ _
    ((WittVector.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).comp
      (WittVector.fromPadicInt p)) (by
  simp only [RingHom.coe_comp]
  refine Function.Injective.comp ?_ ?_
  · exact WittVector.map_injective _ (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective
  · refine Function.injective_iff_hasLeftInverse.mpr ?_
    use (WittVector.toPadicInt p)
    rw [Function.leftInverse_iff_comp]; ext r
    have := toPadicInt_comp_fromPadicInt_ext p r
    simpa
  )

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Coe ℚ_[p] ℚᵘⁿ_[p] := ⟨Qp_emd_QpUn p⟩

lemma Qp_emd_QpUn_keep_val (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ x : ℚ_[p], Padic.mulValuation x = Valued.v (x : ℚᵘⁿ_[p]) := by
  sorry

variable (p : ℕ) [Fact (Nat.Prime p)]
noncomputable instance : Algebra ℚ_[p] (ℚᵘⁿ_[p]) := (Qp_emd_QpUn p).toAlgebra

--theorem QpUn_emd_Cp (p : ℕ) [Fact (Nat.Prime p)] : ∃! f : ℚᵘⁿ_[p] →+* ℂ_[p], ∀ x : ℚ_[p], f (x : ℚᵘⁿ_[p]) = (x : ℂ_[p]) ∧ ∀ y : ℚᵘⁿ_[p], Valued.v y = Valued.v (f y) := by
  --admit
