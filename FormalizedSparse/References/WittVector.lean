import FormalizedSparse.References.Miscellaneous
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.WittVector.Teichmuller

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

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
  Valued (ℚᵘⁿ_[p]) (WithZero (Multiplicative ℤ)) := inferInstance

open Classical in
noncomputable def abs (p : ℕ) [Fact (Nat.Prime p)] : AbsoluteValue ℚᵘⁿ_[p] ℝ := {
  toFun a := WithZeroMulInt.toNNReal (p_ne_zero p) (Valued.v a)
  map_mul' := by
    intro a b
    simp
  nonneg' := by
    intro a
    positivity
  eq_zero' := by
    intro a
    simp
  add_le' := by
    intro a b
    have hp1 : (1 : NNReal) < p := by
      exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    have hmono : Monotone (fun x => ((WithZeroMulInt.toNNReal (p_ne_zero p) x : NNReal) : ℝ)) := by
      intro x y hxy
      exact_mod_cast (WithZeroMulInt.toNNReal_strictMono hp1).monotone hxy
    refine le_trans ?_ (max_le_add_of_nonneg ?_ ?_)
    · simpa [hmono.map_max] using hmono (Valued.v.map_add a b)
    · positivity
    · positivity
}

open Classical in
lemma abs_def (p : ℕ) [Fact (Nat.Prime p)] (a : ℚᵘⁿ_[p]) :
  abs p a = WithZeroMulInt.toNNReal (p_ne_zero p)
      (Valued.v a) := by
  unfold abs
  aesop

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : NormedField ℚᵘⁿ_[p] :=
  WithAbs.normedField (abs p)

/- USER: This is a consequence of the general fact that the fraction field of of a complete discrete valuation ring is still complete. You should try this approach.

Another approach is to use `dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff` in Mathlib, which, roughly speaking, says that every element in the ring of Wiit vectors can be expanded into the form ∑_{i=0}^∞ [x_i]p^i. Although the uniqueness of such expansion is not available yet, but we do not nned it for the proof. Now, as the fraction field of the ring of Witt vectors, every element in ℚᵘⁿ_[p] can be written as ∑_{i=N}^∞[x_i]p^i for some N ∈ ℤ. Then the Cauchy sequence of partial sums of this series converges to the element, which shows that ℚᵘⁿ_[p] is complete. This proof shold be similar to the proof of completeness of the field of formal laurent series k((T)) with respect to the T-adic valuation.

-/
instance (p : ℕ) [Fact (Nat.Prime p)] : CompleteSpace (ℚᵘⁿ_[p]) := by
  unfold QpUn OQpUn

  admit

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
set_option maxHeartbeats 1000000 in
lemma Qp_embd_keep_val (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ x : ℚ_[p], Padic.mulValuation x = Valued.v (Qp_embd x) := by
  intro x
  by_cases hx : x = 0
  · simp [hx, Qp_embd, map_zero]
  · rw [Padic.mulValuation_toFun, if_neg hx]
    have hp_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
    have hp_norm : ‖(p : ℚ_[p])‖ = (p : ℝ)^(-(1 : ℤ)) := by
      rw [show ((p : ℚ_[p])) = ((p : ℚ_[p]))^(1 : ℕ) by simp]
      rw [Padic.norm_p_pow]; push_cast; rfl
    set y := x * (p : ℚ_[p])^(-x.valuation) with hy_def
    have hy_norm : ‖y‖ = 1 := by
      rw [hy_def, norm_mul, norm_zpow, Padic.norm_eq_zpow_neg_valuation hx, hp_norm]
      rw [← zpow_mul]
      rw [show (-(1 : ℤ)) * (-x.valuation) = x.valuation from by ring]
      rw [← zpow_add₀ (by exact_mod_cast (Fact.out : Nat.Prime p).pos.ne' : (p : ℝ) ≠ 0)]
      simp
    obtain ⟨u, hu_eq⟩ : ∃ u : ℤ_[p]ˣ, x = (u : ℚ_[p]) * (p : ℚ_[p])^x.valuation := by
      refine ⟨PadicInt.mkUnits hy_norm, ?_⟩
      have h1 : (PadicInt.mkUnits hy_norm : ℚ_[p]) = y := by
        rw [PadicInt.val_mkUnits]
      rw [h1, hy_def, mul_assoc, ← zpow_add₀ hp_ne]; simp
    set vx := x.valuation with hvx
    change ((Multiplicative.ofAdd (-vx : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) = _
    rw [hu_eq, map_mul, map_zpow₀, Valuation.map_mul, map_zpow₀]
    have hQp : Qp_embd ((p : ℚ_[p])) = ((p : ℕ) : ℚᵘⁿ_[p]) := by simp [Qp_embd]
    rw [hQp]
    have hp_val : Valued.v ((p : ℚᵘⁿ_[p])) =
        ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
      rw [show ((p : ℚᵘⁿ_[p])) = algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p]) (p : ℤᵘⁿ_[p]) from by
        push_cast; rfl]
      rw [show (Valued.v : ℚᵘⁿ_[p] → _) =
          (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).valuation _ from rfl]
      rw [(IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).valuation_of_algebraMap]
      have hirr : Irreducible (p : ℤᵘⁿ_[p]) := WittVector.irreducible p
      have hpe : (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).asIdeal =
          Ideal.span {(p : ℤᵘⁿ_[p])} := hirr.maximalIdeal_eq
      rw [IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
        (WittVector.p_nonzero p _) hpe]
      rfl
    rw [hp_val]
    have hu_val : Valued.v (Qp_embd ((u : ℤ_[p]) : ℚ_[p])) = 1 := by
      have hQpu : Qp_embd ((u : ℤ_[p]) : ℚ_[p]) =
          (algebraMap (ℤᵘⁿ_[p]) (ℚᵘⁿ_[p]))
            (((WittVector.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).comp
              (WittVector.fromPadicInt p)) (u : ℤ_[p])) := by
        change (Qp_embd : ℚ_[p] →+* ℚᵘⁿ_[p]) ((algebraMap ℤ_[p] ℚ_[p]) (u : ℤ_[p])) = _
        change (IsFractionRing.map _ : ℚ_[p] →+* ℚᵘⁿ_[p])
          ((algebraMap ℤ_[p] ℚ_[p]) (u : ℤ_[p])) = _
        rw [IsFractionRing.map]
        rw [IsLocalization.map_eq]
      rw [hQpu]
      rw [show (Valued.v : ℚᵘⁿ_[p] → _) =
          (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).valuation _ from rfl]
      rw [(IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).valuation_of_algebraMap]
      refine (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).mpr ?_
      intro hmem
      have hu_unit : IsUnit
          (((WittVector.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).comp
            (WittVector.fromPadicInt p)) (u : ℤ_[p])) :=
        ((WittVector.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).comp
          (WittVector.fromPadicInt p)).isUnit_map u.isUnit
      rw [show (IsDiscreteValuationRing.maximalIdeal (ℤᵘⁿ_[p])).asIdeal =
          IsLocalRing.maximalIdeal (ℤᵘⁿ_[p]) from rfl] at hmem
      exact (IsLocalRing.notMem_maximalIdeal.mpr hu_unit) hmem
    rw [hu_val, one_mul]
    rw [← WithZero.coe_zpow]
    congr 1
    rw [← ofAdd_zsmul vx (-1 : ℤ)]
    congr 1; ring

lemma Qp_embd_keep_norm (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ x : ℚ_[p], ‖x‖ = ‖(Qp_embd x)‖ := by
  intro x
  have hnorm :
      ‖x‖ = ((WithZeroMulInt.toNNReal (p_ne_zero p) (Padic.mulValuation x) : NNReal) : ℝ) := by
    by_cases hx : x = 0
    · simp [hx, Padic.mulValuation]
    · rw [Padic.norm_eq_zpow_log_mulValuation (p := p) hx]
      simp [Padic.mulValuation, hx, WithZeroMulInt.toNNReal_neg_apply]
  rw [hnorm]
  rw [show ‖(Qp_embd x : ℚᵘⁿ_[p])‖ = QpUn.abs p (Qp_embd x) by rfl]
  simp [QpUn.abs_def, Qp_embd_keep_val p x]

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
  Valuation.RankOne (Valued.v : Valuation ℚᵘⁿ_[p] (WithZero (Multiplicative ℤ))) := {
    hom := WithZeroMulInt.toNNReal (p_ne_zero p)
    strictMono' := by
      have hp1 : (1 : NNReal) < p := by
        exact_mod_cast (Fact.out : Nat.Prime p).one_lt
      exact WithZeroMulInt.toNNReal_strictMono hp1
    exists_val_nontrivial := by
      refine ⟨QpUn.Qp_embd (p : ℚ_[p]), ?_, ?_⟩
      · rw [← QpUn.Qp_embd_keep_val p (p : ℚ_[p])]
        have hp_ne : (p : ℚ_[p]) ≠ 0 := by
          exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
        simp [Padic.mulValuation_toFun, hp_ne]
      · rw [← QpUn.Qp_embd_keep_val p (p : ℚ_[p])]
        have hp_ne : (p : ℚ_[p]) ≠ 0 := by
          exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
        simp [Padic.mulValuation_toFun, hp_ne]
    }

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : NontriviallyNormedField ℚᵘⁿ_[p] :=
  Valued.toNontriviallyNormedField

-- View ℚᵘⁿ_[p] as an algebra over ℚ_[p] via the embedding defined above.
noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Algebra ℚ_[p] (ℚᵘⁿ_[p]) := (Qp_embd).toAlgebra

end QpUn

namespace Padic
noncomputable abbrev to_QpUn {p : ℕ} [Fact (Nat.Prime p)] : ℚ_[p] →+* ℚᵘⁿ_[p] := QpUn.Qp_embd
end Padic
