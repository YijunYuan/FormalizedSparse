import FormalizedSparse.References.WittVector
import Mathlib.RingTheory.HahnSeries.Multiplication

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
  Valuation ((LiftedPAdicHahnSeries p) ⧸ (NullSeriesIdeal p)) (WithZero (Multiplicative ℚ)) := {
  toFun x :=
    if h : x = 0 then 0
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
  Valued (𝕃_[p]) (WithZero (Multiplicative ℚ)) := by
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

noncomputable def ZpUn_embd {p : ℕ} [Fact (Nat.Prime p)] : ℤᵘⁿ_[p] →+* 𝕃_[p] where
  toFun a := Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 a)
  map_one' := by simp
  map_mul' := by
    intro a b
    change Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 (a * b)) =
      Ideal.Quotient.mk (NullSeriesIdeal p) ((HahnSeries.single 0 a) * (HahnSeries.single 0 b))
    rw [HahnSeries.single_mul_single]
    simp
  map_zero' := by simp
  map_add' := by
    intro a b
    change Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 (a + b)) =
      Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 a + HahnSeries.single 0 b)
    rw [HahnSeries.single_add]

lemma ZpUn_embd_injective {p : ℕ} [Fact (Nat.Prime p)] :
  Function.Injective (ZpUn_embd (p := p)) := by
  intro a b hab
  have hmem0 : IsNullSeries (HahnSeries.single (0 : ℚ) a - HahnSeries.single (0 : ℚ) b) := by
    simpa [NullSeriesIdeal, ZpUn_embd, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] using
      (Ideal.Quotient.eq.mp hab)
  have hsingle : HahnSeries.single (0 : ℚ) a - HahnSeries.single (0 : ℚ) b =
    HahnSeries.single (0 : ℚ) (a - b) := by
    ext q
    by_cases hq : q = 0
    · simp only [HahnSeries.coeff_sub', Pi.sub_apply, HahnSeries.single_sub]
    · simp [HahnSeries.coeff_single_of_ne hq]
  have hmem := hmem0
  rw [hsingle] at hmem
  let s : ℕ → Finset ℤ := fun M =>
    Set.Finite.toFinset (finprop (HahnSeries.single (0 : ℚ) (a - b)) 0 M)
  let f : ℕ → QpUn p := fun M =>
    Finset.sum (s M).attach fun n =>
      (p : QpUn p) ^ n.val *
        algebraMap (OQpUn p) (QpUn p) ((HahnSeries.single (0 : ℚ) (a - b)).coeff (0 + n))
  have h0 : Filter.Tendsto f Filter.atTop (nhds 0) := by
    simpa [f, s] using hmem 0
  have hconst : f = fun _ : ℕ => algebraMap (OQpUn p) (QpUn p) (a - b) := by
    funext M
    classical
    unfold f
    by_cases hsub : a - b = 0
    · simp [hsub, s]
    · have hset : {n : ℤ | (0 : ℚ) + n ≤ M ∧
        (HahnSeries.single (0 : ℚ) (a - b)).coeff ((0 : ℚ) + n) ≠ 0} = {0} := by
        ext n
        constructor
        · intro hn
          have hz := HahnSeries.eq_of_mem_support_single <| (HahnSeries.mem_support _ _).2 hn.2
          have hn0 : n = 0 := by exact_mod_cast (by simpa using hz : (n : ℚ) = 0)
          simp [hn0]
        · intro hn
          rcases Set.mem_singleton_iff.mp hn with rfl
          simp [hsub]
      have hs : s M = ({0} : Finset ℤ) := by
        have hs' := (Set.Finite.toFinset_inj (hs := finprop (HahnSeries.single (0 : ℚ) (a - b)) 0 M)
          (ht := Set.finite_singleton (0 : ℤ))).2 hset
        simpa [s] using hs'
      rw [hs]
      have hatt : ({0} : Finset ℤ).attach = {⟨0, by simp⟩} := by
        ext x
        rcases x with ⟨x, hx⟩
        simp at hx
        simp [hx]
      simp [hatt]
  have ht : Filter.Tendsto (fun _ : ℕ => algebraMap (OQpUn p) (QpUn p) (a - b))
    Filter.atTop (nhds 0) := by
    simpa [hconst] using h0
  have hmap : algebraMap (OQpUn p) (QpUn p) (a - b) = 0 := by
    simpa using (tendsto_const_nhds_iff.mp ht)
  exact sub_eq_zero.mp <|
    (IsFractionRing.injective (R := OQpUn p) (K := QpUn p)) (by simpa using hmap)

noncomputable def QpUn_embd {p : ℕ} [Fact (Nat.Prime p)] : ℚᵘⁿ_[p] →+* 𝕃_[p] :=
  IsFractionRing.map (j := ZpUn_embd (p := p)) ZpUn_embd_injective

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : Algebra ℚᵘⁿ_[p] 𝕃_[p] := QpUn_embd.toAlgebra

end pAdicHahnSeries
end Poonen1993

namespace QpUn

noncomputable abbrev to_Lp {p : ℕ} [Fact (Nat.Prime p)] : ℚᵘⁿ_[p] →+* 𝕃_[p] :=
  Poonen1993.pAdicHahnSeries.QpUn_embd

end QpUn

namespace Poonen1993
namespace pAdicHahnSeries

instance (p : ℕ) [Fact (Nat.Prime p)] : IsAlgClosed (𝕃_[p]) := by admit

variable (p : ℕ) [Fact (Nat.Prime p)]

noncomputable def alg_Cp_embd {p : ℕ} [Fact (Nat.Prime p)] : ℂ_[p] →ₐ[ℚᵘⁿ_[p]] 𝕃_[p] :=
  @IsAlgClosed.lift 𝕃_[p] _ _ ℚᵘⁿ_[p] _ _ ℂ_[p] _ _ _ _ _ _ _

noncomputable def Cp_embd {p : ℕ} [Fact (Nat.Prime p)] : ℂ_[p] →+* 𝕃_[p] :=
  alg_Cp_embd.toRingHom

open Classical in
noncomputable def abs {p : ℕ} [Fact (Nat.Prime p)] : AbsoluteValue 𝕃_[p] ℝ where
  toFun a := WithZeroRat.toNNReal (pInv_ne_zero p) (Valued.v a)
  map_mul' := by admit
  nonneg' := by admit
  eq_zero' := by admit
  add_le' := by admit

open Classical in
lemma abs_def (p : ℕ) [Fact (Nat.Prime p)] (a : 𝕃_[p]) :
  abs a = WithZeroRat.toNNReal (pInv_ne_zero p) (Valued.v a) := rfl

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] : NormedField 𝕃_[p] :=
  WithAbs.normedField abs

theorem QpUn_embd_keep_val (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ x : ℚᵘⁿ_[p],
    WithZero.map' (AddMonoidHom.toMultiplicative (Int.castAddHom ℚ)) (Valued.v x) =
      Valued.v (QpUn_embd x) := by
  admit

theorem QpUn_embd_keep_norm (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ x : ℚᵘⁿ_[p], ‖x‖ = ‖(QpUn_embd x)‖ := by
  admit

theorem Cp_embd_keep_val (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ y : ℂ_[p],
    Valued.v y =
      WithZeroRat.toNNReal (pInv_ne_zero p) (Valued.v (Cp_embd y)) := by
  sorry

theorem Cp_embd_keep_norm (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ y : ℂ_[p], ‖y‖ = ‖(Cp_embd y)‖ := by
  admit

def IsHyperAlgebraic {p : ℕ} [Fact (Nat.Prime p)] (x : 𝕃_[p]) : Prop :=
  (∃ T : ℕ, ∀ q ∈ x.support, ∃ k : ℕ, (T * (p ^ k) * q).isInt) ∧
  (Set.image x.coeff x.support).Finite

def HyperAlgebraicSubfield (p : ℕ) [Fact (Nat.Prime p)] : Subfield (𝕃_[p]) where
  carrier := {x | IsHyperAlgebraic x}
  zero_mem' := by admit
  one_mem' := by admit
  add_mem' := by admit
  mul_mem' := by admit
  neg_mem' := by admit
  inv_mem' := by admit

theorem HyperAlgebraicSubfield_isAlgClosed (p : ℕ) [Fact (Nat.Prime p)] :
  IsAlgClosed (HyperAlgebraicSubfield p) := by
  admit

theorem HyperAlgebraicSubfield_include_Qp (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ x : ℚ_[p], IsHyperAlgebraic x.to_QpUn.to_Lp := by
  admit

theorem HyperAlgebraicSubfield_include_PadicAlgCl (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ x : (PadicAlgCl p), IsHyperAlgebraic (Cp_embd (p := p) x) := by
  admit

end pAdicHahnSeries
end Poonen1993
