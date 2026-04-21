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
import Mathlib.Analysis.Normed.Field.WithAbs

import FormalizedSparse.References.Miscellaneous

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
  WithVal ((IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).valuation ((FractionRing (ℤᵘⁿ_[p]))))
notation "ℚᵘⁿ_[" p "]" => QpUn p

-- The Teichmuller lift is injective.
theorem injective_teichmuller (p : ℕ) [Fact (Nat.Prime p)] :
  Function.Injective (teichmuller p : 𝔽ᵃ_[p] → ℤᵘⁿ_[p]) := by
  intro a b hab
  simp only [teichmuller, MonoidHom.coe_mk, OneHom.coe_mk, teichmullerFun, mk'.injEq] at hab
  apply_fun (fun x => x 0) at hab
  simpa

namespace QpUn

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
  Valued (ℚᵘⁿ_[p]) (WithZero (Multiplicative ℤ)) := inferInstance

open Classical in
noncomputable def abs (p : ℕ) [Fact (Nat.Prime p)] : AbsoluteValue ℚᵘⁿ_[p] ℝ := {
  toFun a := WithZeroMulInt.toNNReal (pInv_ne_zero p) (Valued.v a)
  map_mul' := sorry
  nonneg' := sorry
  eq_zero' := sorry
  add_le' := sorry
}

open Classical in
lemma abs_def (p : ℕ) [Fact (Nat.Prime p)] (a : ℚᵘⁿ_[p]) :
  abs p a = WithZeroMulInt.toNNReal (pInv_ne_zero p)
      (Valued.v a) := by
  unfold abs
  aesop

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : NormedField ℚᵘⁿ_[p] :=
  WithAbs.normedField (abs p)

-- ℚᵘⁿ_[p] is complete with respect to the p-adic valuation defined above.
instance (p : ℕ) [Fact (Nat.Prime p)] : CompleteSpace (ℚᵘⁿ_[p]) := by admit

-- The embedding from ℚ_[p] to ℚᵘⁿ_[p].
noncomputable def Qp_embd {p : ℕ} [Fact (Nat.Prime p)] : ℚ_[p] →+* ℚᵘⁿ_[p] :=
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

-- The embedding from ℚ_[p] to ℚᵘⁿ_[p] keeps the valuation.
lemma Qp_embd_keep_val (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ x : ℚ_[p], Padic.mulValuation x = Valued.v (Qp_embd x) := by
  sorry

lemma Qp_embd_keep_norm (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ x : ℚ_[p], ‖x‖ = ‖(Qp_embd x)‖ := by
  admit

-- View ℚᵘⁿ_[p] as an algebra over ℚ_[p] via the embedding defined above.
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Algebra ℚ_[p] (ℚᵘⁿ_[p]) := (Qp_embd).toAlgebra

-- There exists ℚ_[p]-embeddings from ℚᵘⁿ_[p] to ℂ_[p], which is defined as the morphism of
-- ℚ_[p]-algebras.
def alg_embd_Cp (p : ℕ) [Fact (Nat.Prime p)] : ℚᵘⁿ_[p] →ₐ[ℚ_[p]] ℂ_[p] := by admit

-- The embedding from ℚᵘⁿ_[p] to ℂ_[p] as a field homomorphism.
abbrev embd_Cp {p : ℕ} [Fact (Nat.Prime p)] : ℚᵘⁿ_[p] →+* ℂ_[p] := (alg_embd_Cp p).toRingHom

-- ℂ_[p] as ℚᵘⁿ_[p]-algebra via the embedding defined above.
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Algebra ℚᵘⁿ_[p] ℂ_[p] := (embd_Cp).toAlgebra

-- ℂ_[p] is an algebraic closure of ℚᵘⁿ_[p].
instance (p : ℕ) [Fact (Nat.Prime p)] : IsAlgClosure ℚᵘⁿ_[p] ℂ_[p] := by admit

-- The composition of the embedding from ℚ_[p] to ℚᵘⁿ_[p] and that from ℚᵘⁿ_[p] to ℂ_[p] is
-- exactly the embedding from ℚ_[p] to ℂ_[p] that defined in `Mathlib.NumberTheory.Padics.Complex`
theorem embd_compatible (p : ℕ) [Fact (Nat.Prime p)] :
  algebraMap ℚ_[p] ℂ_[p] = embd_Cp.comp Qp_embd := by admit

-- The embedding from ℚᵘⁿ_[p] to ℂ_[p] keeps the valuation.
lemma embd_Cp_keep_val (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ y : ℚᵘⁿ_[p], WithZeroMulInt.toNNReal (pInv_ne_zero p)
    (Valued.v y) = Valued.v (embd_Cp y) := by admit

lemma embd_Cp_keep_norm (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ y : ℚᵘⁿ_[p], ‖y‖ = ‖(embd_Cp y)‖ := by admit

end QpUn
