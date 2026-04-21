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

import FormalizedSparse.References.WittVector

open WittVector

namespace Poonen1993
-- W(𝔽ₚ^⁻)((t^ℚ))
abbrev LiftedPAdicHahnSeries (p : ℕ) [Fact (Nat.Prime p)] := HahnSeries ℚ (ℤᵘⁿ_[p])

namespace LiftedPAdicHahnSeries
-- Define an element of W(𝔽ₚ^⁻)((t^ℚ)) from a function ℚ → 𝔽ₚ^⁻ with well-ordered support
-- by the formula f ↦ ∑ₖ [f(k)]tᵏ
noncomputable def from_coeff {p : ℕ} [Fact (Nat.Prime p)]
(s : ℚ → Fpbar p) (hspwo : (Function.support s).IsPWO) :
LiftedPAdicHahnSeries p where
  coeff := fun n => teichmuller p (s n)
  isPWO_support' := by
    suffices h : (Function.support fun n ↦ (teichmuller p) (s n)) = Function.support s by rwa [h]
    ext z
    simp only [Function.mem_support]
    refine Function.Injective.ne_iff' ?_ ?_
    · exact injective_teichmuller p
    · simp
end LiftedPAdicHahnSeries

-- The set {n : ℤ | g + n ≤ N ∧ x.coeff (g + n) ≠ 0} is finite for any g and N.
def finprop {p : ℕ} [Fact (Nat.Prime p)] (x : LiftedPAdicHahnSeries p) (g : ℚ) (N : ℕ) :
  Finite {n : ℤ | g + n ≤ N ∧ x.coeff (g + n) ≠ 0} := by
  by_cases hs : Set.Nonempty x.support
  · let m : ℚ := x.isWF_support.min hs
    have hsubset :
        {n : ℤ | g + n ≤ N ∧ x.coeff (g + n) ≠ 0} ⊆
          Set.Icc (⌈m - g⌉ : ℤ) ⌊(N : ℚ) - g⌋ := by
      intro n hn
      have hm_le : m ≤ g + n := by
        exact x.isWF_support.min_le hs <| (HahnSeries.mem_support x (g + n)).2 hn.2
      have hlower : (⌈m - g⌉ : ℤ) ≤ n := by
        apply Int.ceil_le.mpr
        rw [sub_le_iff_le_add]
        simpa [add_comm, add_left_comm, add_assoc] using hm_le
      have hupper : n ≤ ⌊(N : ℚ) - g⌋ := by
        apply Int.le_floor.mpr
        rw [le_sub_iff_add_le]
        simpa [add_comm, add_left_comm, add_assoc] using hn.1
      exact ⟨hlower, hupper⟩
    exact ((Set.finite_Icc (⌈m - g⌉ : ℤ) ⌊(N : ℚ) - g⌋).subset hsubset).to_subtype
  · have hcoeff : ∀ q : ℚ, x.coeff q = 0 := by
      intro q
      by_contra hq
      exact hs ⟨q, (HahnSeries.mem_support x q).2 hq⟩
    have hset : {n : ℤ | g + n ≤ N ∧ x.coeff (g + n) ≠ 0} = ∅ := by
      ext n
      simp [hcoeff (g + n)]
    simpa [hset] using (Set.finite_empty : (∅ : Set ℤ).Finite).to_subtype

-- An element ∑ₖ aₖ tᵏof W(𝔽ₚ^⁻)((t^ℚ)) called a `null series` if ∀ g ∈ ℚ, ∑ₙ a_{g+n}pⁿ = 0
open Topology Filter in
def IsNullSeries {p : ℕ} [Fact (Nat.Prime p)] (x : LiftedPAdicHahnSeries p) : Prop :=
  ∀ g : ℚ, Filter.Tendsto (fun M => (∑ n : Set.Finite.toFinset (finprop x g M),
      (p : QpUn p) ^ n.val * algebraMap (OQpUn p) (QpUn p) (x.coeff (g + n)))) atTop (𝓝 0)

-- [Proposition 3, Poonen1993] : The null series form an ideal of W(𝔽ₚ^⁻)((t^ℚ)).
def NullSeriesIdeal (p : ℕ) [Fact (Nat.Prime p)] : Ideal (LiftedPAdicHahnSeries p) where
  carrier := {x | IsNullSeries x}
  add_mem' := by admit
  zero_mem' := by simp [IsNullSeries]
  smul_mem' := by admit

-- [Corollary 3, Poonen1993] : The ideal of null series is maximal, so pAdicHahnSeries p is a field.
instance (p : ℕ) [Fact (Nat.Prime p)] : (NullSeriesIdeal p).IsMaximal := by admit

-- [Proposition 4, Poonen1993] : Every element of pAdicHahnSeries p has a unique representative
-- in W(𝔽ₚ^⁻)((t^ℚ)) of the form ∑ₖ [aₖ] tᵏ
theorem exists_canonical_expansion {p : ℕ} [Fact (Nat.Prime p)] :
  ∀ A : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p),
    ∃! (s : {f : ℚ → Fpbar p // (Function.support f).IsPWO}),
      Ideal.Quotient.ringCon (NullSeriesIdeal p)
      A.out (LiftedPAdicHahnSeries.from_coeff s.val s.prop) := by
  admit

-- The support of a p-adic Hahn series is well-ordered.
theorem support_IsPWO {p : ℕ} [Fact (Nat.Prime p)]
  (x : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) :
  (exists_canonical_expansion x).choose.val.support.IsPWO := by
  simp only [Subtype.forall]
  convert (exists_canonical_expansion x).choose.prop
  simp

-- When p-adic Hahn series x ≠ 0, its support is nonempty.
theorem support_nonempty_of_nonzero
    (p : ℕ) [inst : Fact (Nat.Prime p)]
    (x : (LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) (h : ¬x = 0) :
    (exists_canonical_expansion x).choose.val.support.Nonempty := by
  contrapose h
  simp only [Subtype.forall, Function.support_nonempty_iff, ne_eq, not_not] at h
  have := (exists_canonical_expansion x).choose_spec.1
  simp only [Subtype.forall, h] at this
  suffices h' : (@LiftedPAdicHahnSeries.from_coeff p _ 0 (by simp)) = 0 by
    simp only [h'] at this
    rw [← Quotient.out_eq x]
    exact Quotient.sound this
  simpa [LiftedPAdicHahnSeries.from_coeff] using Eq.symm Pi.zero_def

-- The valuation of a p-adic Hahn series x is defined to be the minimum of the support of x.
open Classical in
noncomputable def val
  (p : ℕ) [Fact (Nat.Prime p)] :
  AddValuation ((LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) (WithTop ℚ) := {
  toFun x :=
    if h : x = 0 then (⊤ : WithTop ℚ)
    else ((support_IsPWO x).isWF.min (support_nonempty_of_nonzero p x h) : WithTop ℚ)
  map_zero' := by admit
  map_one' := by admit
  map_mul' := by admit
  map_add_le_max' := by admit
}

def pAdicHahnSeries (p : ℕ) [Fact (Nat.Prime p)] : Type _ := WithVal (val p)

notation "𝕃_[" p "]" => pAdicHahnSeries p

namespace pAdicHahnSeries
-- Given a p-adic Hahn series x, write x = ∑ₖ [aₖ] pᵏ where aₖ ∈ 𝔽ₚ^⁻, then the `coefficients` of x
-- is defined to be the function k ↦ aₖ, where k∈ 𝔽ₚ^-.
noncomputable def coeff {p : ℕ} [Fact (Nat.Prime p)] (x : 𝕃_[p]) :
  ℚ → Fpbar p := (exists_canonical_expansion x).choose.val

-- The `support` of a p-adic Hahn series x is defined to be the support of the coefficients function
-- of x.
noncomputable def support {p : ℕ} [Fact (Nat.Prime p)] (x : 𝕃_[p]) : Set ℚ :=
  (exists_canonical_expansion x).choose.val.support

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Field (𝕃_[p]) := by
  apply Ideal.Quotient.field

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
  Valued (𝕃_[p]) (Multiplicative (WithTop ℚ)ᵒᵈ) := by
  unfold pAdicHahnSeries
  infer_instance

-- The field of p-adic Hahn series is complete with respect to the valuation defined above.
instance instCompleteSpace {p : ℕ} [Fact (Nat.Prime p)] :
    CompleteSpace (𝕃_[p]) := by admit

-- Define an element of W(𝔽ₚ^⁻)((p^ℚ)) from a function ℚ → 𝔽ₚ^⁻ with well-ordered support by the
-- formula f ↦ ∑ₖ [f(k)]pᵏ
noncomputable def from_coeff {p : ℕ} [Fact (Nat.Prime p)]
    (s : ℚ → Fpbar p) (hspwo : (Function.support s).IsPWO) :
    (𝕃_[p]) :=
  Ideal.Quotient.mk (NullSeriesIdeal p) (LiftedPAdicHahnSeries.from_coeff s hspwo)

-- The `coefficients` of the p-adic Hahn series obtained from a function ℚ → 𝔽ₚ^⁻ by
-- the `from_coeff` construction is the original function.
theorem coeff_of_from_coeff_eq_self {p : ℕ} [Fact (Nat.Prime p)]
    (s : ℚ → Fpbar p) (hspwo : s.support.IsPWO) :
    (from_coeff s hspwo).coeff = s := by
  have hEq :
      ⟨s, hspwo⟩ = (exists_canonical_expansion (from_coeff s hspwo)).choose := by
    apply (exists_canonical_expansion (from_coeff s hspwo)).choose_spec.2
    simpa [from_coeff] using
      (Quotient.exact (Quotient.out_eq (from_coeff s hspwo)))
  exact (congrArg Subtype.val hEq).symm

-- The converse of the above theorem.
theorem from_coeff_of_coeff_eq_self {p : ℕ} [Fact (Nat.Prime p)]
    (x : 𝕃_[p]) :
    from_coeff x.coeff (support_IsPWO x) = x := by
  simp only [from_coeff, coeff]
  set s := (exists_canonical_expansion x).choose
  have h := (exists_canonical_expansion x).choose_spec.1
  dsimp at h
  obtain ⟨y, hy⟩ := h
  have : Ideal.Quotient.mk (NullSeriesIdeal p)
      (LiftedPAdicHahnSeries.from_coeff s.val s.prop) =
    Ideal.Quotient.mk (NullSeriesIdeal p) x.out := by
    apply Quotient.sound
    change (Ideal.Quotient.ringCon (NullSeriesIdeal p))
      (LiftedPAdicHahnSeries.from_coeff s.val s.prop) x.out
    exact ⟨-y, by dsimp; rw [neg_vadd_eq_iff]; dsimp at hy; exact hy.symm⟩
  rw [this]; exact Quotient.out_eq x

def QpUn_embd (p : ℕ) [Fact (Nat.Prime p)] : ℚᵘⁿ_[p] →+* 𝕃_[p] where
  toFun a := sorry
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-
noncomputable def residue_RingEquiv (p : ℕ) [Fact (Nat.Prime p)] :
    Fpbar p →+* Valued.ResidueField (𝕃_[p]) where
  toFun a := by
    let atei : pAdicHahnSeries p :=
      Ideal.Quotient.mk (NullSeriesIdeal p) <|
        HahnSeries.single 0 (teichmuller p a)
    have : atei ∈ Valued.integer (pAdicHahnSeries p) := sorry
    exact IsLocalRing.residue
      (Valued.integer (pAdicHahnSeries p)) ⟨atei, this⟩
  map_one' := by
    simpa [pAdicHahnSeries,val] using MonoidHom.mem_mker.mp rfl
  map_mul' := by
    intro a b
    simp only [map_mul (teichmuller p),
      ← map_mul (IsLocalRing.residue (Valued.integer (pAdicHahnSeries p)))]
    congr 1; ext
    simp only [MulMemClass.mk_mul_mk,
      ← map_mul (Ideal.Quotient.mk (NullSeriesIdeal p)),
      HahnSeries.single_mul_single, zero_add]
  map_zero' := by
    simp only [teichmuller_zero, map_zero, IsLocalRing.residue_eq_zero_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    refine Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr ?_
    unfold Valued.v instValuedMultiplicativeOrderDualWithTopRat
    simp
  map_add' := by
    intro a b
    rw [← sub_eq_zero]
    simp only [← map_add (IsLocalRing.residue (Valued.integer (pAdicHahnSeries p))),
      ← map_sub (IsLocalRing.residue (Valued.integer (pAdicHahnSeries p)))]
    rw [IsLocalRing.residue_eq_zero_iff]
    simp only [AddMemClass.mk_add_mk]
    conv_lhs => simp [*]


    sorry


theorem residue_field_iso_Fpbar (p : ℕ) [Fact (Nat.Prime p)] :
  Function.Bijective (residue_RingEquiv p) := by admit
-/

theorem isAlgClosed (p : ℕ) [Fact (Nat.Prime p)] : IsAlgClosed (𝕃_[p]) := by admit

end pAdicHahnSeries

end Poonen1993
