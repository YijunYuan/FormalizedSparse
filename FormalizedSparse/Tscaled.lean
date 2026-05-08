import FormalizedSparse.References.Poonen1993

/-!
# T-scaled realization of p-adic Hahn series
-/

/- USER:
This file corresponds to the full formalization of Section 2 of the file Tscaled.pdf in the same folder.

As you can see, formalization of Section 1 of Tscaled.pdf (p-adic Hahn series) is contained in the file Poonen1993.lean (the detained informal proof is contained in Poonen1003.pdf in References subfolder), and Section 2 (T-scaled variant) is a generalization of the results in Section 1. So it is expected that the (formalized proof) of this section will be similar to the one in Poonen1993.lean, but with some modifications to accommodate the T-scaling.

Let me tell you what should be formalized and the hint.

1. You should first think about how to define the ring W(F_p^bar)[p^(1/T)] and its fraction field. You should know that p^(1/T) is a root of the polynomial X^T-p. The ring W(F_p^bar) is already defined in WittVector.lean as `ℤᵘⁿ_[p]`. You should use the notation `ℤᵘⁿ_[p,T]` for the ring W(F_p^bar)[p^(1/T)] and `ℚᵘⁿ_[p,T]` for its fraction field.

2. You should prove Lemma 2.1. I'm not sure if you have Eisenstein criterion for general discrete valuation fields in the Mathlib. If not, you should try to formalize it in this file.

3. You should prove Lemma 2.2. This depends on Lemma 2.1 and the `TODO` result in Mathlib that every element in the ring of Witt vectors can be written as a series in p with coefficients be the Teichmüller representatives. There might already some related efforts in Poonen1993.lean. You should take a look .

4. Now you should be readly to define the equal-characteristic Hahn series in this setting.
In Poonen1993.lean, W(𝔽ₚ^⁻)((t^ℚ)) is called `LiftedPAdicHahnSeries`. In our Tscaled variant W(𝔽ₚ^⁻)(p^(1/T))((t^ℚ)), it should be called `TLiftedPAdicHahnSeries`.
Notice that W(𝔽ₚ^⁻)((t^ℚ)) is a subring of W(𝔽ₚ^⁻)(p^(1/T))((t^ℚ)). This should be reflected in the code (maybe as an inclusion ring morphism)

5. Now you need to define the T-null-series (Definition 2.4) and the related results.

In Poonen1993.lean, the null-series are defined via the predicate `IsNullSeries`. In our T-scaled variant, the T-null-series should be defined via the predicate `IsTNullSeries`.

You need to show that the T-null-series form an ideal ((1) of Lemma 2.6). This is an analogue of the definition `NullSeriesIdeal` in Poonen1993.lean, and the proof strategy should be similar to the one in Poonen1993.lean. In current T-scaled setting, the ideal should be called `TNullSeriesIdeal`.

Lemma 2.6 (2) is an analogue of `exists_canonical_expansion` in Poonen1993.lean. You should state and prove this result. The proof strategy should be similar to the one in Poonen1993.lean.

Lemma 2.6 (3) is to show that `TNullSeriesIdeal` is a maximal ideal, which is an analogue of the instance
`instance (p : ℕ) [Fact (Nat.Prime p)] : (NullSeriesIdeal p).IsMaximal`
in Poonen1993.lean. You should state and prove this result as well. The proof strategy should be similar to the one in Poonen1993.lean.

6. With these results, we define the T-scaled p-adic Hahn series as the quotient of `TLiftedPAdicHahnSeries` by `TNullSeriesIdeal`. This should be defined as `TScaledPAdicHahnSeries`, which is an analogue of `pAdicHahnSeries` in Poonen1993.lean. Its notation should be `𝕃_[p,T]`. The support and the coefficients should be defined correspondingly. See Poonen1993.lean for the details.

7. Now you need to prove Lemma 2.8 and Lemma 2.9. There is not much I want to say about the proof strategy, you should just follow the informal proof in Tscaled.pdf and be aware of the fact that in the informal proof, the embedding from W(𝔽ₚ^⁻)((t^ℚ)) to W(𝔽ₚ^⁻)(p^(1/T))((t^ℚ)) is implicitly used.

8. Finally, you need to prove Proposition 2.10. The isomorphism `σ` between `𝕃_[p]` and `𝕃_[p,T]` should not be hard to prove, just follows the informal proof in Tscaled.pdf.

You will see a commutative diagram in Proposition 2.10, which basically says the same thing as remark 2.11:
If `(f : 𝕃_[p])`, then `f.coeff` is a function `ℚ → (Fpbar p)`.
Similarly, if `(g : 𝕃_[p,T])`, then `g.coeff`, which you should have formalized above, is also a function `ℚ → (Fpbar p)`. Then the remark just says that `(σ f).coeff` and `f.coeff` are the same function.

I want to emphasize that you may find Poonen1993.lean and the corresponding informal proof in Poonen1993.pdf very helpful for this formalization.
 -/
