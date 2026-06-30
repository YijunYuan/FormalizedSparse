import FormalizedSparse.MainTheorem
import FormalizedSparse.RayDecomposition
import Mathlib.Topology.DerivedSet

/- USER: This file corresponds to the subsection
`Sparse representatives and finiteness of bounded QTR supports`. You need to formalize every thing
in this subsection in this file. I have already formalized the statement of the main theorem
`thm:29057` as follows (``). You should not change the statement of it.
-/

namespace FormalizedSparse

-- thm:29075
open Bornology in
theorem fintie_support_of_qpun_algebraic_of_bounded_support {p : ℕ} [Fact (Nat.Prime p)]
  (f : 𝕃_[p]) (hf1 : IsAlgebraic ℚᵘⁿ_[p] f) (hf2 : IsBounded f.support)
  (hf3 : (derivedSet f.support).Finite) :
  f.support.Finite := by
  sorry

-- coro:11594
open Bornology in
theorem support_accpt_empty_or_infinite_of_qp_algebraic_of_bounded_support
  {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (hf1 : IsAlgebraic ℚ_[p] f) (hf2 : IsBounded f.support) :
  (derivedSet f.support) = ∅ ∨ (derivedSet f.support).Infinite
  := by
  sorry

-- coro:11594
open Bornology Ordinal in
theorem order_type_of_qp_algebraic_of_bounded_support {p : ℕ} [Fact (Nat.Prime p)]
  (f : 𝕃_[p]) (hf1 : IsAlgebraic ℚ_[p] f) (hf2 : IsBounded f.support) :
  typeLT f.support < omega0 ∨ typeLT f.support ≥ omega0^2 := sorry

end FormalizedSparse
