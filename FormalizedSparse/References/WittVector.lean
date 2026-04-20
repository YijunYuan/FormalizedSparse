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

open WittVector

-- The algebraic closure of F_p
abbrev Fpbar (p : ℕ) [Fact (Nat.Prime p)] := AlgebraicClosure (GaloisField p 1)

-- The ring of integers of the completion of the maximal unramified extension of Q_p,
-- which is the same as W(𝔽ₚ^⁻)((t^ℚ)).
abbrev OQpUn (p : ℕ) [Fact (Nat.Prime p)] := WittVector p (Fpbar p)

-- Equip RawQpUn p with the topology induced by the valuation QpUnVal p.
abbrev QpUn (p : ℕ) [Fact (Nat.Prime p)] :=
  WithVal ((IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation ((FractionRing (OQpUn p))))

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
  Valued (QpUn p) (WithZero (Multiplicative ℤ)) := inferInstance

-- The Teichmuller lift is injective.
theorem injective_teichmuller (p : ℕ) [Fact (Nat.Prime p)] :
  Function.Injective (teichmuller p : Fpbar p → OQpUn p) := by
  intro a b hab
  simp only [teichmuller, MonoidHom.coe_mk, OneHom.coe_mk, teichmullerFun, mk'.injEq] at hab
  apply_fun (fun x => x 0) at hab
  simpa using hab

variable {p : ℕ} [Fact (Nat.Prime p)]

--#check WittVector.map (Field.Emb (GaloisField p 1) (GaloisField p 1))
