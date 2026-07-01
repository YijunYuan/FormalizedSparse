import FormalizedSparse.References.Kedlaya

/- USER: This file corresponds to the subsection `Quasi-twist-recurrent functions` in section
`Application: $p$-adic Hahn series with bounded support`. You need to formalize every thing in this
subsection in this file. I will give you several hints on the formalization:
1. `thm:28713` is exactly `kedlaya_2001a_theorem15` in `FormalizedSparse.References.Kedlaya`.
2. `thm:47` is exactly `kedlaya_2017_theorem13_4` in `FormalizedSparse.References.Kedlaya`.
3. The above two results are literal translation of the original results in Kedlaya's papers. In his
paper, Kedlaya prefers to use the phrase `integral`, but you shold note that integral over a field
is the same as algebraic over a field.
4. The above results are admitted. You can use them directly without proving them.
-/

namespace FormalizedSparse

open LaurentSeries

/-- **Definition `def:16557`: quasi-twist-recurrent (QTR) functions.**

A function `x : ℚ → 𝔽ᵃ_[p]` is *quasi-twist-recurrent* with respect to the data
`(a, b, c, M, N) ∈ ℤ>0 × ℕ × ℕ × ℤ>0 × ℤ>0` if its support is a well-ordered subset of `ℚ`
satisfying two conditions.

The base-`p` digit string `0.q₁⋯qₙ⋯ = ∑_{i≥1} qᵢ p^{-i}` is modelled exactly as in
`Kedlaya.Sabc`: a finitely-supported `d : ℕ →₀ ℕ` with `d i` the digit `q_{i+1}`, value
`∑ i, d i * p^{-(i+1)}`, digit bound `∑ i, d i ≤ c` and `d i < p`.

1. (support bound) The support is contained in `S_{a,b,c} = Kedlaya.Sabc p a b c`. This is the
   condition that for every `q ∈ Supp x`, writing `a q = w - 0.q₁⋯qₙ⋯`, one has `w ≥ -b` and
   `∑ qₙ ≤ c`.

2. (recurrence) For every integer `w ≥ -b` and every rational `q = (1/a)(w - ∑ d i p^{-(i+1)})`
   with `d i < p` and `∑ d i ≤ c`, if the digit string has `M` consecutive zeros — i.e.
   `d i = 0` for all `k ≤ i < k + M` for some `k ≥ 0` (so `q_{k+1} = ⋯ = q_{k+M} = 0`) — then
   `x q = x q'`, where `q'` inserts `N` further zeros at that gap. The insertion is the reindexing
   `Finsupp.mapDomain (fun i => if i < k + M then i else i + N) d`: digits below the gap stay put,
   digits at or beyond `k + M` shift right by `N`, leaving an `M + N`-zero block. -/
def IsQTR {p : ℕ} [Fact (Nat.Prime p)] (x : ℚ → 𝔽ᵃ_[p])
    (a : ℕ+) (b c : ℕ) (M N : ℕ+) : Prop :=
  -- The support is a well-ordered subset of `ℚ`.
  (Function.support x).IsWF ∧
  -- Condition (1): the support is contained in `S_{a,b,c}`.
  (Function.support x ⊆ Kedlaya.Sabc p a b c) ∧
  -- Condition (2): the `M`-zero-run ⇒ `N`-zero-insertion recurrence.
  ∀ (w : ℤ), -(b : ℤ) ≤ w → ∀ (d : ℕ →₀ ℕ), (∀ i, d i < p) →
      (d.sum fun _ v => v) ≤ c →
    ∀ (k : ℕ), (∀ i, k ≤ i → i < k + (M : ℕ) → d i = 0) →
      x ((1 / (a : ℚ)) * ((w : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))))
        = x ((1 / (a : ℚ)) * ((w : ℚ) -
            (Finsupp.mapDomain (fun i => if i < k + (M : ℕ) then i else i + (N : ℕ)) d).sum
              fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))))

/-- **Key computational bridge for `prop:54845`.** Kedlaya's twist value `twistSeq` (built from
the coefficient function `f_m(z) = x_{(m+z)/a}`) equals the coefficient of `x` at the digit-point
obtained from `dig` by shifting its tail (positions `≥ j-1`) right by `n`. Concretely, with the
reindexing `s_{j-1,n} i = if i < j-1 then i else i+n`,
`twistSeq p f_m j dig n = x.coeff ((1/a)(m - ∑ᵢ (mapDomain s_{j-1,n} dig)ᵢ p^{-(i+1)}))`.
This is what lets Kedlaya's twist-sequence periodicity be read off as the QTR digit-insertion
recurrence (and vice versa). -/
lemma twistSeq_eq_coeff {p : ℕ} [Fact (Nat.Prime p)] (x : HahnSeries ℚ (𝔽ᵃ_[p]))
    (m : ℤ) (a : ℕ+) (j : ℕ) (dig : ℕ →₀ ℕ) (n : ℕ) :
    Kedlaya.twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig n
      = x.coeff ((1 / (a : ℚ)) * ((m : ℚ) -
          (Finsupp.mapDomain (fun i => if i < j - 1 then i else i + n) dig).sum
            fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))) := by
  have hppos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hppos.ne'
  set s : ℕ → ℕ := fun i => if i < j - 1 then i else i + n with hs
  have hinj : Function.Injective s := by
    intro u v huv; simp only [hs] at huv; split_ifs at huv <;> omega
  have hDV : (Finsupp.mapDomain s dig).sum (fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      = (∑ i ∈ Finset.range (j - 1), (dig i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
        + (p : ℚ) ^ (-(n : ℤ)) *
          ∑ i ∈ dig.support.filter (fun i => j - 1 ≤ i),
            (dig i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
    rw [Finsupp.sum_mapDomain_index_inj hinj]
    simp only [Finsupp.sum]
    rw [← Finset.sum_filter_add_sum_filter_not dig.support (fun i => i < j - 1)]
    congr 1
    · -- head: positions `< j-1` are fixed, fill in the zero digits to get `range (j-1)`
      trans (∑ i ∈ dig.support.filter (fun i => i < j - 1),
          (dig i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      · apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_filter] at hi
        have hsi : s i = i := by simp only [hs]; exact if_pos hi.2
        rw [hsi]
      · apply Finset.sum_subset
        · intro i hi
          rw [Finset.mem_filter] at hi; rw [Finset.mem_range]; exact hi.2
        · intro i hi hni
          rw [Finset.mem_range] at hi
          simp only [Finset.mem_filter, not_and, not_lt] at hni
          have hd0 : dig i = 0 := by
            by_contra h
            have := hni (Finsupp.mem_support_iff.mpr h); omega
          rw [hd0]; simp
    · -- tail: positions `≥ j-1` are shifted right by `n`, factoring out `p^{-n}`
      simp only [not_lt]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨_, hi2⟩ := hi
      have hsi : s i = i + n := by simp only [hs]; exact if_neg (by omega)
      have hpow : (p : ℚ) ^ (-(((i + n : ℕ) : ℤ)) + -1)
          = (p : ℚ) ^ (-(n : ℤ)) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
        rw [← zpow_add₀ hp0]; congr 1; push_cast; ring
      rw [hsi]
      rw [show (-(((i + n : ℕ) : ℤ) + 1)) = (-(((i + n : ℕ) : ℤ)) + -1) by ring, hpow]
      ring
  simp only [Kedlaya.twistSeq]
  congr 1
  rw [hDV]; ring

/-- Helper: the tail-shift reindexing `i ↦ if i < k then i else i + t` is injective. Used to
turn `Finsupp.mapDomain` along it into a pointwise statement (digit bound, digit sum, gap). -/
lemma shift_injective (k t : ℕ) :
    Function.Injective (fun i : ℕ => if i < k then i else i + t) := by
  intro a b hab; simp only at hab; split_ifs at hab <;> omega

/-- Helper: composition of two tail-shift reindexings collapses to a single shift, provided the
second shift amount `n` is at least the gap length `M`. Precomposing the "insert `N` zeros at the
length-`M` gap starting at `k`" map `i ↦ if i < k+M then i else i+N` with the "shift the tail past
`k` right by `n`" map `i ↦ if i < k then i else i+n` yields the single shift
`i ↦ if i < k then i else i+(n+N)`. This is the function-level identity behind the QTR
recurrence ⟷ Kedlaya twist-periodicity bridge (`prop:54845`). -/
lemma shift_comp_shift {k M N n : ℕ} (hMn : M ≤ n) (i : ℕ) :
    (fun i => if i < k + M then i else i + N) ((fun i => if i < k then i else i + n) i)
      = (if i < k then i else i + (n + N)) := by
  simp only
  split_ifs <;> omega

/-- Helper: the QTR `N`-zero insertion applied to a tail-shift collapses to a longer tail-shift,
at the `Finsupp.mapDomain` level. For `M ≤ n`,
`mapDomain t_{k,M,N} (mapDomain s_{k,n} dig) = mapDomain s_{k,n+N} dig`, where
`t_{k,M,N} i = if i < k+M then i else i+N` is the QTR insertion and
`s_{k,t} i = if i < k then i else i+t` is the tail-shift. This bridges Kedlaya's twist
period `N` (a single extra shift) with the QTR `M+N`-zero block. -/
lemma mapDomain_insert_shift {k M N n : ℕ} (hMn : M ≤ n) (dig : ℕ →₀ ℕ) :
    Finsupp.mapDomain (fun i => if i < k + M then i else i + N)
        (Finsupp.mapDomain (fun i => if i < k then i else i + n) dig)
      = Finsupp.mapDomain (fun i => if i < k then i else i + (n + N)) dig := by
  rw [← Finsupp.mapDomain_comp]
  exact Finsupp.mapDomain_congr (fun i _ => shift_comp_shift hMn i)

/-- Helper: the digit bound `dig i < p` is preserved by the tail-shift reindexing `s_{k,t}`.
Every value of `mapDomain s_{k,t} dig` is either an old digit (`< p`) or `0` (`< p`, using
`0 < p`). Side condition for both directions of `prop:54845`. -/
lemma shift_mapDomain_lt {p : ℕ} (hp : 0 < p) (k t : ℕ) (dig : ℕ →₀ ℕ)
    (hdig : ∀ i, dig i < p) (i : ℕ) :
    (Finsupp.mapDomain (fun i => if i < k then i else i + t) dig) i < p := by
  by_cases h : i ∈ Set.range (fun i : ℕ => if i < k then i else i + t)
  · obtain ⟨j, hj⟩ := h
    rw [← hj, Finsupp.mapDomain_apply (shift_injective k t)]; exact hdig j
  · rw [Finsupp.mapDomain_notin_range _ _ h]; exact hp

/-- Helper: the digit sum `∑ dig i` is preserved by the tail-shift reindexing `s_{k,t}` (it is
injective). Side condition for both directions of `prop:54845`. -/
lemma shift_mapDomain_sum (k t : ℕ) (dig : ℕ →₀ ℕ) :
    (Finsupp.mapDomain (fun i => if i < k then i else i + t) dig).sum (fun _ v => v)
      = dig.sum (fun _ v => v) := by
  rw [Finsupp.sum_mapDomain_index_inj (shift_injective k t)]

/-- Helper: the tail-shift `s_{k,t}` leaves a length-`t` zero gap at position `k`, hence a
length-`m` gap for any `m ≤ t`. Concretely, positions `k ≤ i < k+m` are not in the range of
`s_{k,t}`, so `mapDomain s_{k,t} dig` vanishes there. This is the gap hypothesis fed to the QTR
recurrence in the backward direction of `prop:54845`. -/
lemma shift_mapDomain_gap (k t : ℕ) (dig : ℕ →₀ ℕ) {m : ℕ} (hm : m ≤ t) :
    ∀ i, k ≤ i → i < k + m →
      (Finsupp.mapDomain (fun i => if i < k then i else i + t) dig) i = 0 := by
  intro i hi1 hi2
  apply Finsupp.mapDomain_notin_range
  rintro ⟨j, hj⟩
  simp only at hj
  split_ifs at hj <;> omega

/-- **Bridge (forward): QTR recurrence from Kedlaya twist-periodicity.** Given the twist-period-`N`
condition of `kedlaya_2001a_theorem15` for `x` with data `(a,b,c,M,N)`, the QTR digit-insertion
recurrence (clause (2) of `IsQTR`) holds with the same data. For a digit string `d` with a
length-`M` zero gap at position `k`, collapse the gap to `dig = comapDomain s_{k,M} d`, so that
`mapDomain s_{k,M} dig = d`; the twist values at shift `M` and `M+N` are then the two QTR
coefficients (via `twistSeq_eq_coeff`), and the period identity equates them. -/
lemma recurrence_of_twist {p : ℕ} [Fact (Nat.Prime p)] (x : HahnSeries ℚ (𝔽ᵃ_[p]))
    (a : ℕ+) (b c : ℕ) (M N : ℕ+)
    (htwist : ∀ m : ℤ, m ≥ -(b : ℤ) →
        ∀ (j : ℕ) (dig : ℕ →₀ ℕ), 0 < j → (∀ i, dig i < p) → (dig.sum fun _ v => v) ≤ c →
          ∀ n : ℕ, (M : ℕ) ≤ n →
            Kedlaya.twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig (n + (N : ℕ))
              = Kedlaya.twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig n) :
    ∀ (w : ℤ), -(b : ℤ) ≤ w → ∀ (d : ℕ →₀ ℕ), (∀ i, d i < p) → (d.sum fun _ v => v) ≤ c →
      ∀ (k : ℕ), (∀ i, k ≤ i → i < k + (M : ℕ) → d i = 0) →
        x.coeff ((1 / (a : ℚ)) * ((w : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))))
          = x.coeff ((1 / (a : ℚ)) * ((w : ℚ) -
              (Finsupp.mapDomain (fun i => if i < k + (M : ℕ) then i else i + (N : ℕ)) d).sum
                fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))) := by
  intro w hw d hdp hdc k hgap
  have hppos : 0 < p := (Fact.out : Nat.Prime p).pos
  -- The tail-shift collapsing the length-`M` gap at `k`.
  have hsinj : Function.Injective (fun i : ℕ => if i < k then i else i + (M : ℕ)) :=
    shift_injective k (M : ℕ)
  -- `d` is supported in the range of the shift, because it vanishes on the gap `[k, k+M)`.
  have hrange : ↑d.support ⊆ Set.range (fun i : ℕ => if i < k then i else i + (M : ℕ)) := by
    intro i hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
    rcases lt_or_ge i k with hik | hik
    · exact ⟨i, by simp only [if_pos hik]⟩
    · rcases lt_or_ge i (k + (M : ℕ)) with hik2 | hik2
      · exact absurd (hgap i hik hik2) hi
      · exact ⟨i - (M : ℕ), by simp only [if_neg (show ¬ i - (M:ℕ) < k by omega)]; omega⟩
  -- Collapse the gap.
  set dig : ℕ →₀ ℕ :=
    Finsupp.comapDomain (fun i : ℕ => if i < k then i else i + (M : ℕ)) d hsinj.injOn with hdigdef
  have hmap : Finsupp.mapDomain (fun i : ℕ => if i < k then i else i + (M : ℕ)) dig = d :=
    Finsupp.mapDomain_comapDomain _ hsinj d hrange
  -- Side conditions for `htwist`.
  have hdig_lt : ∀ i, dig i < p := by
    intro i; rw [hdigdef, Finsupp.comapDomain_apply]; exact hdp _
  have hdig_sum : (dig.sum fun _ v => v) ≤ c := by
    have h := shift_mapDomain_sum k (M : ℕ) dig
    rw [hmap] at h; rw [← h]; exact hdc
  -- Apply the twist period at shift `M`.
  have key := htwist w hw (k + 1) dig (Nat.succ_pos k) hdig_lt hdig_sum (M : ℕ) le_rfl
  -- Rewrite both twist values as coefficients via the bridge lemma `twistSeq_eq_coeff`.
  rw [twistSeq_eq_coeff x w a (k + 1) dig ((M : ℕ) + (N : ℕ)),
      twistSeq_eq_coeff x w a (k + 1) dig (M : ℕ)] at key
  simp only [Nat.add_sub_cancel] at key
  -- `mapDomain s_{k,M} dig = d` and `mapDomain s_{k,M+N} dig = mapDomain t_{k,M,N} d`.
  rw [hmap] at key
  have hcollapse :
      Finsupp.mapDomain (fun i => if i < k then i else i + ((M : ℕ) + (N : ℕ))) dig
        = Finsupp.mapDomain (fun i => if i < k + (M : ℕ) then i else i + (N : ℕ)) d := by
    rw [← hmap]; exact (mapDomain_insert_shift (le_refl (M : ℕ)) dig).symm
  rw [hcollapse] at key
  exact key.symm

/-- **Bridge (backward): Kedlaya twist-periodicity from the QTR recurrence.** Given the QTR
digit-insertion recurrence (clause (2) of `IsQTR`) for `x` with data `(a,b,c,M,N)`, the
twist-period-`N` condition of `kedlaya_2001a_theorem15` holds with the same data. For each twist
input `dig` and shift `n ≥ M`, set `d = mapDomain s_{j-1,n} dig`: it has a length-`n ≥ M` zero
gap at `j-1`, so the recurrence applies, and `mapDomain t_{j-1,M,N} d = mapDomain s_{j-1,n+N} dig`
reconciles its conclusion with the twist period (via `twistSeq_eq_coeff`). -/
lemma twist_of_recurrence {p : ℕ} [Fact (Nat.Prime p)] (x : HahnSeries ℚ (𝔽ᵃ_[p]))
    (a : ℕ+) (b c : ℕ) (M N : ℕ+)
    (hrec : ∀ (w : ℤ), -(b : ℤ) ≤ w → ∀ (d : ℕ →₀ ℕ), (∀ i, d i < p) → (d.sum fun _ v => v) ≤ c →
      ∀ (k : ℕ), (∀ i, k ≤ i → i < k + (M : ℕ) → d i = 0) →
        x.coeff ((1 / (a : ℚ)) * ((w : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))))
          = x.coeff ((1 / (a : ℚ)) * ((w : ℚ) -
              (Finsupp.mapDomain (fun i => if i < k + (M : ℕ) then i else i + (N : ℕ)) d).sum
                fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))))) :
    ∀ m : ℤ, m ≥ -(b : ℤ) →
        ∀ (j : ℕ) (dig : ℕ →₀ ℕ), 0 < j → (∀ i, dig i < p) → (dig.sum fun _ v => v) ≤ c →
          ∀ n : ℕ, (M : ℕ) ≤ n →
            Kedlaya.twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig (n + (N : ℕ))
              = Kedlaya.twistSeq p (fun z => x.coeff (((m : ℚ) + z) / (a : ℚ))) j dig n := by
  intro m hm j dig hj hdp hdc n hn
  have hppos : 0 < p := (Fact.out : Nat.Prime p).pos
  -- The digit string `d` whose gap drives the recurrence.
  set d : ℕ →₀ ℕ := Finsupp.mapDomain (fun i => if i < j - 1 then i else i + n) dig with hddef
  -- Side conditions for `hrec`.
  have hd_lt : ∀ i, d i < p := by
    rw [hddef]; exact shift_mapDomain_lt hppos (j - 1) n dig hdp
  have hd_sum : (d.sum fun _ v => v) ≤ c := by
    rw [hddef, shift_mapDomain_sum (j - 1) n dig]; exact hdc
  have hd_gap : ∀ i, (j - 1) ≤ i → i < (j - 1) + (M : ℕ) → d i = 0 := by
    rw [hddef]; exact shift_mapDomain_gap (j - 1) n dig hn
  -- Apply the recurrence.
  have key := hrec m hm d hd_lt hd_sum (j - 1) hd_gap
  -- Reconcile the inserted-zero string with the longer tail-shift.
  have hcollapse :
      Finsupp.mapDomain (fun i => if i < (j - 1) + (M : ℕ) then i else i + (N : ℕ)) d
        = Finsupp.mapDomain (fun i => if i < j - 1 then i else i + (n + (N : ℕ))) dig := by
    rw [hddef]; exact mapDomain_insert_shift hn dig
  rw [hcollapse] at key
  -- Rewrite both twist values as coefficients via `twistSeq_eq_coeff`.
  rw [twistSeq_eq_coeff x m a j dig (n + (N : ℕ)), twistSeq_eq_coeff x m a j dig n]
  rw [hddef] at key
  exact key.symm

/-- **Proposition `prop:54845`: Kedlaya's characterisation through QTR.**

A Hahn series `x = ∑ x_q t^q ∈ 𝔽ᵃ_[p]((t^ℚ))` is algebraic over `𝔽ᵃ_[p]((t))` if and only if the
coefficient function `F_x = x.coeff` is QTR. This is the rephrasing of `kedlaya_2001a_theorem15`
(`thm:28713`) via the remark that integrality over a field is the same as algebraicity. -/
theorem isAlgebraic_iff_isQTR {p : ℕ} [Fact (Nat.Prime p)] (x : HahnSeries ℚ (𝔽ᵃ_[p])) :
    IsAlgebraic (𝔽ᵃ_[p])⸨X⸩ x ↔
      ∃ (a : ℕ+) (b c : ℕ) (M N : ℕ+), IsQTR x.coeff a b c M N := by
  -- Over the field `𝔽ᵃ_[p]((t))`, algebraic = integral, then apply Kedlaya's `theorem15`.
  rw [isAlgebraic_iff_isIntegral, Kedlaya.kedlaya_2001a_theorem15]
  constructor
  · -- Forward: Kedlaya's (support-bound ∧ twist-periodicity) ⟹ QTR.
    rintro ⟨a, b, c, hsupp, M, N, htwist⟩
    exact ⟨a, b, c, M, N, x.isWF_support, hsupp, recurrence_of_twist x a b c M N htwist⟩
  · -- Backward: QTR ⟹ Kedlaya's (support-bound ∧ twist-periodicity).
    rintro ⟨a, b, c, M, N, _hwf, hsupp, hrec⟩
    exact ⟨a, b, c, hsupp, M, N, twist_of_recurrence x a b c M N hrec⟩

/-- Helper: a base-`p` fractional digit string `∑ᵢ dᵢ p^{-(i+1)}` with all digits `dᵢ < p`
has value `< 1` (the standard "`0.q₁q₂⋯ < 1`" bound). Used in `isQTR_restrict` to recover the
integer part `w` from `aq = w - 0.q₁⋯`. -/
lemma digitValue_lt_one {p : ℕ} (hp : 1 < p) (d : ℕ →₀ ℕ) (hd : ∀ i, d i < p) :
    (d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) < 1 := by
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (show 0 < p by omega)
  obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range d.support
  rw [Finsupp.sum_of_support_subset d hn _ (by intro i _; simp)]
  -- Bound the partial sum over `range m` by `1 - p^{-m}` by induction on `m`.
  have hbound : ∀ m, (∑ i ∈ Finset.range m, (d i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      ≤ 1 - (p : ℚ) ^ (-(m : ℤ)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have ht : (0 : ℚ) < (p : ℚ) ^ (-((m : ℤ) + 1)) := zpow_pos hp0 _
      have hdm : (d m : ℚ) ≤ (p : ℚ) - 1 := by
        have : (d m : ℚ) + 1 ≤ (p : ℚ) := by exact_mod_cast hd m
        linarith
      have hrel : (p : ℚ) ^ (-((m : ℤ) + 1)) * (p : ℚ) = (p : ℚ) ^ (-(m : ℤ)) := by
        rw [← zpow_add_one₀ (ne_of_gt hp0)]; congr 1; ring
      have key : (d m : ℚ) * (p : ℚ) ^ (-((m : ℤ) + 1))
          ≤ (p : ℚ) ^ (-(m : ℤ)) - (p : ℚ) ^ (-((m : ℤ) + 1)) := by
        rw [← hrel]
        calc (d m : ℚ) * (p : ℚ) ^ (-((m : ℤ) + 1))
            ≤ ((p : ℚ) - 1) * (p : ℚ) ^ (-((m : ℤ) + 1)) :=
              mul_le_mul_of_nonneg_right hdm ht.le
          _ = (p : ℚ) ^ (-((m : ℤ) + 1)) * (p : ℚ) - (p : ℚ) ^ (-((m : ℤ) + 1)) := by ring
      have hcast : (-(((m + 1 : ℕ)) : ℤ)) = (-((m : ℤ) + 1)) := by push_cast; ring
      rw [hcast]
      linarith [ih, key]
  calc (∑ i ∈ Finset.range n, (d i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      ≤ 1 - (p : ℚ) ^ (-(n : ℤ)) := hbound n
    _ < 1 := by have := zpow_pos hp0 (-(n : ℤ)); linarith

/-- Helper: inserting zeros into the base-`p` digit string (the QTR `N`-zero insertion,
realized as `Finsupp.mapDomain` along `i ↦ if i < k+M then i else i+N`) does not increase its
value `∑ᵢ dᵢ p^{-(i+1)}`, since every digit is shifted to a position `≥` its original one. -/
lemma digitValue_mapDomain_le {p : ℕ} (hp : 1 ≤ (p : ℚ)) (d : ℕ →₀ ℕ) (k M N : ℕ) :
    ((Finsupp.mapDomain (fun i => if i < k + M then i else i + N) d).sum
        fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      ≤ d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
  have hinj : Function.Injective (fun i : ℕ => if i < k + M then i else i + N) := by
    intro a b hab
    simp only at hab
    split_ifs at hab <;> omega
  rw [Finsupp.sum_mapDomain_index_inj hinj]
  apply Finsupp.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply zpow_le_zpow_right₀ hp
  split_ifs <;> push_cast <;> omega

/-- **Lemma `lem:36014`: QTR is preserved under restriction to `(-∞, r]`.**

For any QTR function `φ : ℚ → 𝔽ᵃ_[p]` and any integer `r`, the restriction `φ_r` of `φ` to
`(-∞, r]` (i.e. `φ_r q = φ q` for `q ≤ r` and `φ_r q = 0` for `q > r`) is still QTR with the same
data `(a, b, c, M, N)`. -/
theorem isQTR_restrict {p : ℕ} [Fact (Nat.Prime p)] {x : ℚ → 𝔽ᵃ_[p]}
    {a : ℕ+} {b c : ℕ} {M N : ℕ+} (h : IsQTR x a b c M N) (r : ℤ) :
    IsQTR (fun q => if q ≤ (r : ℚ) then x q else 0) a b c M N := by
  obtain ⟨hwf, hsupp, hrec⟩ := h
  have hpp : Nat.Prime p := Fact.out
  have hp1' : 1 < p := hpp.one_lt
  have hp1 : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp1'.le
  have a_pos : (0 : ℚ) < (a : ℚ) := by exact_mod_cast a.pos
  -- support of the restriction is contained in support of `x`
  have hsub : Function.support (fun q => if q ≤ (r : ℚ) then x q else 0) ⊆ Function.support x := by
    intro q hq
    rw [Function.mem_support] at hq ⊢
    intro hx0
    apply hq
    simp only [hx0, ite_self]
  refine ⟨hwf.mono hsub, subset_trans hsub hsupp, ?_⟩
  intro w hw d hdp hdc k hk
  dsimp only
  -- abbreviations for the two digit-string values
  set Vd : ℚ := d.sum (fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) with hVdeq
  set Vd' : ℚ := (Finsupp.mapDomain (fun i => if i < k + (M : ℕ) then i else i + (N : ℕ)) d).sum
      (fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) with hVd'eq
  -- value facts: `Vd' ≤ Vd` (insertion shrinks), `Vd < 1` (digit bound), `0 ≤ Vd'`.
  have hmono : Vd' ≤ Vd := by
    rw [hVdeq, hVd'eq]; exact digitValue_mapDomain_le hp1 d k (M : ℕ) (N : ℕ)
  have hVd_lt : Vd < 1 := by rw [hVdeq]; exact digitValue_lt_one hp1' d hdp
  have hVd'_nonneg : (0 : ℚ) ≤ Vd' := by
    rw [hVd'eq]; apply Finsupp.sum_nonneg; intro i _; positivity
  -- `q ≤ q'`: inserting zeros pushes the point to the right.
  have hqq' : (1 / (a : ℚ)) * ((w : ℚ) - Vd) ≤ (1 / (a : ℚ)) * ((w : ℚ) - Vd') :=
    mul_le_mul_of_nonneg_left (by linarith [hmono]) (one_div_pos.mpr a_pos).le
  by_cases hqr : (1 / (a : ℚ)) * ((w : ℚ) - Vd) ≤ (r : ℚ)
  · -- Case `q ≤ r`. Show `q' ≤ r` too, then reduce to clause (2) for `x`.
    -- From `q ≤ r`: `w - Vd ≤ a r`.
    have h1 : (w : ℚ) - Vd ≤ (a : ℚ) * (r : ℚ) := by
      have h0 := mul_le_mul_of_nonneg_left hqr a_pos.le
      rwa [← mul_assoc, mul_one_div, div_self (ne_of_gt a_pos), one_mul] at h0
    -- Integer rounding: `w - Vd ≤ a r` with `0 ≤ Vd < 1` and `a r ∈ ℤ` give `w ≤ a r`.
    have h2 : (w : ℚ) ≤ (a : ℚ) * (r : ℚ) := by
      have h3 : (w : ℚ) < (a : ℚ) * (r : ℚ) + 1 := by linarith [hVd_lt]
      have hcast : (a : ℚ) * (r : ℚ) = (((a : ℕ) : ℤ) * r : ℤ) := by push_cast; ring
      rw [hcast] at h3 ⊢
      have h4 : w < ((a : ℕ) : ℤ) * r + 1 := by exact_mod_cast h3
      exact_mod_cast (show w ≤ ((a : ℕ) : ℤ) * r by omega)
    -- Hence `aq' = w - Vd' ≤ w ≤ a r`, so `q' ≤ r`.
    have hq'r : (1 / (a : ℚ)) * ((w : ℚ) - Vd') ≤ (r : ℚ) := by
      have h5 : (w : ℚ) - Vd' ≤ (a : ℚ) * (r : ℚ) := by linarith [hVd'_nonneg, h2]
      calc (1 / (a : ℚ)) * ((w : ℚ) - Vd')
          ≤ (1 / (a : ℚ)) * ((a : ℚ) * (r : ℚ)) :=
            mul_le_mul_of_nonneg_left h5 (one_div_pos.mpr a_pos).le
        _ = (r : ℚ) := by
            rw [← mul_assoc, one_div_mul_cancel (ne_of_gt a_pos), one_mul]
    rw [if_pos hqr, if_pos hq'r, hVdeq, hVd'eq]
    exact hrec w hw d hdp hdc k hk
  · -- Case `q > r`. Then `q' ≥ q > r`, so both restricted values vanish.
    have hq'r : ¬ (1 / (a : ℚ)) * ((w : ℚ) - Vd') ≤ (r : ℚ) := fun hle => hqr (le_trans hqq' hle)
    rw [if_neg hqr, if_neg hq'r]

/-- **Scalar tower `𝔽ᵃ_[p] → 𝔽ᵃ_[p]⸨X⸩ → 𝔽ᵃ_[p]((t^ℚ))`.** The constant-field algebra map into the
big Hahn-series ring `HahnSeries ℚ 𝔽ᵃ_[p]` factors through the Laurent series `𝔽ᵃ_[p]⸨X⸩`
(which sits inside via `Kedlaya.intHahnEmbedding`). This makes `IsAlgebraic 𝔽ᵃ_[p] g` upgrade to
`IsAlgebraic 𝔽ᵃ_[p]⸨X⸩ g` (`isAlgebraic_LaurentSeries_of_isAlgebraic_constants`).

The instance is stated with the algebra `SMul`s explicit (`@IsScalarTower … Algebra.toSMul …`)
because the default `𝔽ᵃ_[p]`-action on `HahnSeries ℚ 𝔽ᵃ_[p]` is the *module* `SMul`
(`HahnSeries.instSMul`), which is not defeq to the algebra `SMul` of the canonical
`HahnSeries.powerSeriesAlgebra`; `IsAlgebraic.tower_top` needs the algebra-`SMul` version. -/
instance instIsScalarTowerLaurentHahn {p : ℕ} [Fact (Nat.Prime p)] :
    @IsScalarTower (𝔽ᵃ_[p]) ((𝔽ᵃ_[p])⸨X⸩) (HahnSeries ℚ (𝔽ᵃ_[p]))
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
  apply IsScalarTower.of_algebraMap_eq'
  refine RingHom.ext (fun a => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply]
  -- Both base maps send `a` to the constant `HahnSeries.C a`; the inclusion fixes it.
  have hL : (algebraMap (𝔽ᵃ_[p]) (HahnSeries ℚ (𝔽ᵃ_[p]))) a = HahnSeries.C a := by
    rw [HahnSeries.algebraMap_apply']
    simp only [PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]
  have hRin : (algebraMap (𝔽ᵃ_[p]) ((𝔽ᵃ_[p])⸨X⸩)) a = HahnSeries.C a := by
    rw [HahnSeries.algebraMap_apply']
    simp only [PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]
  have hEmb : Kedlaya.intHahnEmbedding p (HahnSeries.C a) = HahnSeries.C a := by
    unfold Kedlaya.intHahnEmbedding
    rw [HahnSeries.embDomainRingHom_apply, HahnSeries.C_apply, HahnSeries.embDomain_single]
    simp
  rw [hL, hRin]; exact hEmb.symm

/-- A Hahn series algebraic over the constant field `𝔽ᵃ_[p]` is a fortiori algebraic over the
Laurent-series field `𝔽ᵃ_[p]⸨X⸩` (tower top). This is the bridge that lets
`kedlaya_2017_theorem13_4` (which produces algebraicity over the *constants*) feed
`isAlgebraic_iff_isQTR` (which needs
algebraicity over `𝔽ᵃ_[p]⸨X⸩`). -/
lemma isAlgebraic_LaurentSeries_of_isAlgebraic_constants {p : ℕ} [Fact (Nat.Prime p)]
    {g : HahnSeries ℚ (𝔽ᵃ_[p])} (h : IsAlgebraic (𝔽ᵃ_[p]) g) :
    IsAlgebraic (𝔽ᵃ_[p])⸨X⸩ g :=
  h.tower_top _

/-- A `p`-adic Hahn series in `𝕃_[p]` has vanishing coefficient at every rational strictly below
its valuation `val p x` (the minimal support point). This is the elementary half of the
valuation–coefficient dictionary: `val p x` is, by definition, `⊤` for `x = 0` and the
`IsWF.min` of the support otherwise, so anything strictly below it is off the support. -/
theorem coeff_eq_zero_of_lt_val {p : ℕ} [Fact (Nat.Prime p)] (x : 𝕃_[p]) (q : ℚ)
    (hq : ((q : ℚ) : WithTop ℚ) < FormalizedSparse.val p x) : x.coeff q = 0 := by
  classical
  by_contra hne
  have hmem : q ∈ x.support := by
    simp only [pAdicHahnSeries.support, Function.mem_support]; exact hne
  have hx0 : x ≠ 0 := fun h => hne (by
    rw [h]; exact (pAdicHahnSeries.eq_zero_iff_coeff_zero 0).mp rfl q (h ▸ hmem))
  have hval : FormalizedSparse.val p x = (((FormalizedSparse.support_IsPWO x).isWF.min
      (support_nonempty_of_nonzero p x hx0) : ℚ) : WithTop ℚ) := by
    rw [FormalizedSparse.val]
    change (if h : x = 0 then (⊤ : WithTop ℚ) else _) = _
    rw [dif_neg hx0]
  rw [hval, WithTop.coe_lt_coe] at hq
  exact absurd ((FormalizedSparse.support_IsPWO x).isWF.min_le _ hmem) (not_le.mpr hq)

/-- Valuation of `p ^ n` in `ℚᵘⁿ_[p]` is `ofAdd(-n)`. Local reproof of the (private) reference
fact `valued_v_p_zpow`, needed to reprove `nullSeries_no_unit_leading` below. -/
private lemma valued_v_p_zpow' {p : ℕ} [Fact (Nat.Prime p)] (n : ℤ) :
    Valued.v ((p : QpUn p) ^ n) =
      ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := by
  have hvp : Valued.v ((p : QpUn p)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
    rw [show ((p : QpUn p)) = algebraMap (OQpUn p) (QpUn p) (p : OQpUn p) from by push_cast; rfl]
    rw [QpUn.valued_algebraMap]
    have hpe : (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).asIdeal =
        Ideal.span {(p : OQpUn p)} := (WittVector.irreducible p).maximalIdeal_eq
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _
      (WittVector.p_nonzero p _) hpe]
    rfl
  have hzpow : Valued.v ((p : QpUn p) ^ n) = (Valued.v ((p : QpUn p))) ^ n := map_zpow₀ Valued.v _ _
  rw [hzpow, hvp, ← WithZero.coe_zpow]
  congr 1; rw [← ofAdd_zsmul n (-1 : ℤ)]; congr 1; ring

/-- The image of a unit of `ℤᵘⁿ_[p]` under `algebraMap` to `ℚᵘⁿ_[p]` has valuation `1`. Local
reproof of the (private) reference fact `valued_v_algebraMap_unit_one`. -/
private lemma valued_v_algebraMap_unit_one' {p : ℕ} [Fact (Nat.Prime p)] (u : (OQpUn p)ˣ) :
    Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) = 1 := by
  have h1 : Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation_le_one u.val
  have h2 : Valued.v (algebraMap (OQpUn p) (QpUn p) u.inv) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation_le_one u.inv
  have h3 : Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) *
            Valued.v (algebraMap (OQpUn p) (QpUn p) u.inv) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, u.val_inv]; simp
  by_contra h_ne_one
  have h1_lt : Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) < 1 := lt_of_le_of_ne h1 h_ne_one
  have h_lt : Valued.v (algebraMap (OQpUn p) (QpUn p) u.val) *
            Valued.v (algebraMap (OQpUn p) (QpUn p) u.inv) < 1 :=
    lt_of_le_of_lt (le_trans (mul_le_mul' (le_refl _) h2) (le_of_eq (mul_one _))) h1_lt
  rw [h3] at h_lt; exact lt_irrefl _ h_lt

/-- **Local reproof of the (private) reference lemma `null_series_no_unit_leading`.** A lifted
`p`-adic Hahn series `Δ ∈ NullSeriesIdeal` cannot have a unit coefficient at the minimum of its
support. Proof: the partial sum of the `IsNullSeries` net at the leading point `q` has its `n = 0`
term of valuation `ofAdd 0` (a unit, valuation `1`), strictly dominating the tail (each later term
has valuation `≤ ofAdd(-1)`); by the strict ultrametric the partial sum has valuation `ofAdd 0`,
contradicting convergence to `0`. The reference proof is `private`; this is a faithful local
reproof from the public `IsNullSeries`/`finprop`/`mem_nhds_zero_v_lt` API plus the two helpers
above. -/
private lemma nullSeries_no_unit_leading {p : ℕ} [Fact (Nat.Prime p)]
    {Δ : LiftedPAdicHahnSeries p} (hΔ : Δ ∈ NullSeriesIdeal p)
    {q : ℚ} (hq_unit : IsUnit (Δ.coeff q))
    (hq_lead : ∀ q' < q, Δ.coeff q' = 0) : False := by
  change IsNullSeries Δ at hΔ
  have htend := hΔ q
  have hpn_val := valued_v_p_zpow' (p := p)
  have h_lead_val : Valued.v ((p : QpUn p) ^ (0 : ℤ) *
      algebraMap (OQpUn p) (QpUn p) (Δ.coeff q)) =
      ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _) := by
    rw [Valuation.map_mul, hpn_val 0]
    have hval : Valued.v (algebraMap (OQpUn p) (QpUn p) (Δ.coeff q)) = 1 := by
      rcases hq_unit with ⟨u, hu⟩
      rw [← hu, valued_v_algebraMap_unit_one' u]
    rw [hval, mul_one]; rfl
  have hq_ne : Δ.coeff q ≠ 0 := by
    intro h; rw [h] at hq_unit; exact not_isUnit_zero hq_unit
  have h_zero_in : ∀ M : ℕ, q ≤ (M : ℚ) →
      (0 : ℤ) ∈ Set.Finite.toFinset (finprop Δ q M) := by
    intro M hMq
    apply (Set.Finite.mem_toFinset (hs := finprop Δ q M) (a := 0)).2
    exact ⟨by simpa using hMq, by simpa using hq_ne⟩
  have h_sum_eq : ∀ M : ℕ, q ≤ (M : ℚ) →
      Valued.v (∑ n : Set.Finite.toFinset (finprop Δ q M),
          (p : QpUn p) ^ n.val * algebraMap (OQpUn p) (QpUn p) (Δ.coeff (q + n))) =
        ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _) := by
    intro M hMq
    rw [show (∑ n : Set.Finite.toFinset (finprop Δ q M),
            (p : QpUn p) ^ n.val * algebraMap (OQpUn p) (QpUn p) (Δ.coeff (q + n))) =
        ∑ n ∈ Set.Finite.toFinset (finprop Δ q M),
          (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (Δ.coeff (q + n)) from
        Finset.sum_attach (s := Set.Finite.toFinset (finprop Δ q M))
          (f := fun n : ℤ => (p : QpUn p) ^ n *
            algebraMap (OQpUn p) (QpUn p) (Δ.coeff (q + n)))]
    have h_in : (0 : ℤ) ∈ Set.Finite.toFinset (finprop Δ q M) := h_zero_in M hMq
    rw [show Set.Finite.toFinset (finprop Δ q M) =
        insert (0 : ℤ) ((Set.Finite.toFinset (finprop Δ q M)).erase 0) from
        (Finset.insert_erase h_in).symm]
    rw [Finset.sum_insert (Finset.notMem_erase _ _), Valuation.map_add_eq_of_lt_left]
    · have h_eq_zero : (q + ((0 : ℤ) : ℚ)) = q := by push_cast; ring
      rw [h_eq_zero]; exact h_lead_val
    · have h_bound : Valued.v (∑ n ∈ (Set.Finite.toFinset (finprop Δ q M)).erase 0,
            (p : QpUn p) ^ n * algebraMap (OQpUn p) (QpUn p) (Δ.coeff (q + n))) ≤
          ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
        apply Valuation.map_sum_le
        intro n hn_mem
        have hn_in_finset : n ∈ Set.Finite.toFinset (finprop Δ q M) :=
          (Finset.mem_erase.mp hn_mem).2
        have hn_data : q + (n : ℚ) ≤ (M : ℚ) ∧ Δ.coeff (q + n) ≠ 0 :=
          (Set.Finite.mem_toFinset (hs := finprop Δ q M) (a := n)).1 hn_in_finset
        have hn_pos : 1 ≤ n := by
          rcases Int.lt_or_le n 0 with hlt | hle
          · exfalso; apply hn_data.2; apply hq_lead
            have hncast : ((n : ℚ)) < 0 := by exact_mod_cast hlt
            linarith
          · have hn_ne_zero : n ≠ 0 := Finset.ne_of_mem_erase hn_mem
            omega
        rw [Valuation.map_mul, hpn_val n]
        have h_alg_le : Valued.v (algebraMap (OQpUn p) (QpUn p) (Δ.coeff (q + n))) ≤ 1 :=
          (IsDiscreteValuationRing.maximalIdeal (OQpUn p)).valuation_le_one (Δ.coeff (q + n))
        calc ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) *
                Valued.v (algebraMap (OQpUn p) (QpUn p) (Δ.coeff (q + n)))
            ≤ ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) * 1 :=
              mul_le_mul' (le_refl _) h_alg_le
          _ = ((Multiplicative.ofAdd (-n : ℤ) : Multiplicative ℤ) : WithZero _) := mul_one _
          _ ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero _) := by
              rw [WithZero.coe_le_coe]; exact Multiplicative.ofAdd_le.mpr (by omega)
      apply lt_of_le_of_lt h_bound
      have h_eq_zero : (q + ((0 : ℤ) : ℚ)) = q := by push_cast; ring
      rw [h_eq_zero, h_lead_val, WithZero.coe_lt_coe]
      exact Multiplicative.ofAdd_lt.mpr (by omega)
  have h_nhds :
      {x : QpUn p | Valued.v x <
          ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _)} ∈
        nhds (0 : QpUn p) :=
    mem_nhds_zero_v_lt WithZero.coe_ne_zero
  have h_evtl_close : ∀ᶠ M : ℕ in Filter.atTop,
      Valued.v (∑ n : Set.Finite.toFinset (finprop Δ q M),
          (p : QpUn p) ^ n.val * algebraMap (OQpUn p) (QpUn p) (Δ.coeff (q + n))) <
        ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero _) :=
    htend h_nhds
  have h_evtl_M_ge : ∀ᶠ M : ℕ in Filter.atTop, q ≤ (M : ℚ) := by
    filter_upwards [Filter.eventually_ge_atTop ⌈q⌉₊] with M hM
    have h1 : (q : ℚ) ≤ (⌈q⌉₊ : ℚ) := Nat.le_ceil q
    have h2 : ((⌈q⌉₊ : ℕ) : ℚ) ≤ ((M : ℕ) : ℚ) := by exact_mod_cast hM
    linarith
  obtain ⟨M, hMge, hMclose⟩ := (h_evtl_M_ge.and h_evtl_close).exists
  rw [h_sum_eq M hMge] at hMclose
  exact lt_irrefl _ hMclose

/-- A Teichmüller difference `teich a - teich b` (`a ≠ b`) is a unit of `ℤᵘⁿ_[p]`. Local reproof of
the (private) reference fact `teich_sub_isUnit`, used to certify the leading coefficient of the
canonical difference in `coeff_agree_of_lt_val`. -/
private lemma teich_sub_isUnit' {p : ℕ} [Fact (Nat.Prime p)] {a b : Fpbar p} (h : a ≠ b) :
    IsUnit (WittVector.teichmuller p a - WittVector.teichmuller p b) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  intro h0
  have h_imp : ∀ i < 1,
      ((WittVector.teichmuller p) a - (WittVector.teichmuller p) b).coeff i = 0 := by
    intro i hi; interval_cases i; exact h0
  have h_eq : ((WittVector.teichmuller p) a).coeff 0 = ((WittVector.teichmuller p) b).coeff 0 :=
    (WittVector.le_coeff_eq_iff_le_sub_coeff_eq_zero (n := 1)).mpr h_imp 0 (by omega)
  rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at h_eq
  exact h h_eq

/-- **Obligation (B) of `prop:167`'s Step 4.** If `val (f - h) > u`, then `F_f` and `F_h` agree on
`(-∞, u]`. Contrapositive: take the minimal disagreement point `q₀ ≤ u`. The lifted canonical
difference `Δ = from_coeff F_f - from_coeff F_h` and the canonical representative `C = canon (f-h)`
both reduce to `f - h`, so `Δ - C` is a null series. Below `q₀` both `F_f, F_h` agree (so `Δ`
vanishes) and `C` vanishes (since `q' ≤ q₀ < val (f - h)` via `coeff_eq_zero_of_lt_val`); at `q₀`,
`(Δ - C).coeff q₀ = teich (F_f q₀) - teich (F_h q₀)` is a unit. This contradicts
`nullSeries_no_unit_leading`. -/
lemma coeff_agree_of_lt_val {p : ℕ} [Fact (Nat.Prime p)] (f h : 𝕃_[p]) (u : ℤ)
    (hval : (((u : ℚ) : WithTop ℚ)) < FormalizedSparse.val p (f - h)) :
    ∀ q : ℚ, q ≤ (u : ℚ) → f.coeff q = h.coeff q := by
  classical
  by_contra hcon
  push Not at hcon
  -- Extract the minimal disagreement point `q₀ ≤ u`.
  obtain ⟨q₀, hq₀u, hq₀ne, hq₀min⟩ :
      ∃ q₀ : ℚ, q₀ ≤ (u : ℚ) ∧ f.coeff q₀ ≠ h.coeff q₀ ∧ ∀ q' < q₀, f.coeff q' = h.coeff q' := by
    set D : Set ℚ := {q | q ≤ (u : ℚ) ∧ f.coeff q ≠ h.coeff q} with hD
    have hDsub : D ⊆ f.support ∪ h.support := by
      intro q hq
      by_contra hc
      rw [Set.mem_union] at hc; push Not at hc
      obtain ⟨hf, hh⟩ := hc
      simp only [pAdicHahnSeries.support, Function.mem_support, not_not] at hf hh
      exact hq.2 (hf.trans hh.symm)
    have hDwf : D.IsWF := ((FormalizedSparse.support_IsPWO f).isWF.union
      (FormalizedSparse.support_IsPWO h).isWF).mono hDsub
    obtain ⟨q₀, hq₀u, hq₀ne⟩ := hcon
    have hDne : D.Nonempty := ⟨q₀, hq₀u, hq₀ne⟩
    refine ⟨hDwf.min hDne, (hDwf.min_mem hDne).1, (hDwf.min_mem hDne).2, fun q' hq' => ?_⟩
    by_contra hne'
    exact absurd (hDwf.min_le hDne ⟨le_of_lt (lt_of_lt_of_le hq' (hDwf.min_mem hDne).1), hne'⟩)
      (not_le.mpr hq')
  -- The lifted canonical difference `Δ` and the canonical representative `C` of `f - h`.
  set Δ : LiftedPAdicHahnSeries p :=
    LiftedPAdicHahnSeries.from_coeff f.coeff (FormalizedSparse.support_IsPWO f)
      - LiftedPAdicHahnSeries.from_coeff h.coeff (FormalizedSparse.support_IsPWO h) with hΔdef
  set C : LiftedPAdicHahnSeries p :=
    LiftedPAdicHahnSeries.from_coeff (f - h).coeff (FormalizedSparse.support_IsPWO (f - h))
    with hCdef
  -- Coefficient formulas: `Δ.coeff = teich∘f.coeff - teich∘h.coeff`, `C.coeff = teich∘(f-h).coeff`.
  have hΔcoeff : ∀ q : ℚ, Δ.coeff q
      = WittVector.teichmuller p (f.coeff q) - WittVector.teichmuller p (h.coeff q) := by
    intro q; rw [hΔdef]; rfl
  have hCcoeff : ∀ q : ℚ, C.coeff q = WittVector.teichmuller p ((f - h).coeff q) := fun q => rfl
  -- `mkLp Δ = mkLp C = f - h`, so `Δ - C` is a null series.
  have hmkΔ : Ideal.Quotient.mk (NullSeriesIdeal p) Δ = f - h := by
    rw [hΔdef, map_sub]
    change pAdicHahnSeries.from_coeff f.coeff _ - pAdicHahnSeries.from_coeff h.coeff _ = f - h
    rw [pAdicHahnSeries.from_coeff_of_coeff_eq_self, pAdicHahnSeries.from_coeff_of_coeff_eq_self]
  have hmkC : Ideal.Quotient.mk (NullSeriesIdeal p) C = f - h := by
    rw [hCdef]
    change pAdicHahnSeries.from_coeff (f - h).coeff _ = f - h
    rw [pAdicHahnSeries.from_coeff_of_coeff_eq_self]
  have hnull : Δ - C ∈ NullSeriesIdeal p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hmkΔ, hmkC, sub_self]
  -- `C` vanishes at and below `q₀`: each such point is `< val (f - h)`.
  have hCvanish : ∀ q' : ℚ, q' ≤ q₀ → C.coeff q' = 0 := by
    intro q' hq'
    have hlt : ((q' : ℚ) : WithTop ℚ) < FormalizedSparse.val p (f - h) :=
      lt_of_le_of_lt (by exact_mod_cast le_trans hq' hq₀u) hval
    rw [hCcoeff, coeff_eq_zero_of_lt_val (f - h) q' hlt, WittVector.teichmuller_zero]
  -- `(Δ - C).coeff q₀` is a unit (the Teichmüller difference at the disagreement point).
  have hunit : IsUnit ((Δ - C).coeff q₀) := by
    have : (Δ - C).coeff q₀
        = WittVector.teichmuller p (f.coeff q₀) - WittVector.teichmuller p (h.coeff q₀) := by
      rw [HahnSeries.coeff_sub', Pi.sub_apply, hΔcoeff, hCvanish q₀ le_rfl, sub_zero]
    rw [this]; exact teich_sub_isUnit' hq₀ne
  -- `(Δ - C).coeff` vanishes strictly below `q₀` (agreement of `Δ` + vanishing of `C`).
  have hlead : ∀ q' < q₀, (Δ - C).coeff q' = 0 := by
    intro q' hq'
    rw [HahnSeries.coeff_sub', Pi.sub_apply, hCvanish q' (le_of_lt hq'), sub_zero,
      hΔcoeff, hq₀min q' hq', sub_self]
  exact nullSeries_no_unit_leading hnull hunit hlead

/-- A single-point witness `δ_u ∈ 𝕃_[p]` with support `{u}` and unit leading coefficient: the
canonical Teichmüller series of the indicator of `{u}`. It realises the value `val(δ_u) = u`,
used to exhibit the valuation ball `{h | u < val(f - h)}` as a neighbourhood of `f`. -/
noncomputable def singleWitness {p : ℕ} [Fact (Nat.Prime p)] (u : ℚ) : 𝕃_[p] :=
  pAdicHahnSeries.from_coeff (fun q => if q = u then 1 else 0) (by
    apply Set.Finite.isPWO; apply Set.Finite.subset (Set.finite_singleton u)
    intro q hq
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hq
    simp [hq.1])

/-- The coefficient function of `singleWitness u` is the indicator of `{u}`. -/
lemma singleWitness_coeff {p : ℕ} [Fact (Nat.Prime p)] (u : ℚ) :
    (singleWitness (p := p) u).coeff = fun q => if q = u then 1 else 0 := by
  unfold singleWitness; rw [pAdicHahnSeries.coeff_of_from_coeff_eq_self]

/-- The support of `singleWitness u` is exactly `{u}`. -/
lemma singleWitness_support {p : ℕ} [Fact (Nat.Prime p)] (u : ℚ) :
    (singleWitness (p := p) u).support = {u} := by
  rw [pAdicHahnSeries.support, show (Exists.choose
      (exists_canonical_expansion (singleWitness (p := p) u))).val
      = (singleWitness (p := p) u).coeff from rfl, singleWitness_coeff]
  ext q
  simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp,
    Set.mem_singleton_iff]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, one_ne_zero⟩⟩

/-- `singleWitness u` is nonzero (its coefficient at `u` is `1`). -/
lemma singleWitness_ne {p : ℕ} [Fact (Nat.Prime p)] (u : ℚ) : singleWitness (p := p) u ≠ 0 := by
  intro h0
  have h1 : (singleWitness (p := p) u).coeff u = (1 : Fpbar p) := by rw [singleWitness_coeff]; simp
  rw [h0] at h1
  have hz : (0 : 𝕃_[p]).coeff u = 0 := by
    have hco := pAdicHahnSeries.coeff_of_from_coeff_eq_self (p := p) (0 : ℚ → Fpbar p) (by simp)
    have h0eq : pAdicHahnSeries.from_coeff (0 : ℚ → Fpbar p) (by simp) = (0 : 𝕃_[p]) := by
      have hlift : LiftedPAdicHahnSeries.from_coeff (p := p) 0 (by simp) = 0 := by
        simpa [LiftedPAdicHahnSeries.from_coeff] using
          Eq.symm (Pi.zero_def : (0 : ℚ → ℤᵘⁿ_[p]) = 0)
      simpa [pAdicHahnSeries.from_coeff] using
        congrArg (Ideal.Quotient.mk (NullSeriesIdeal p)) hlift
    rw [← h0eq, hco]; rfl
  rw [hz] at h1; exact one_ne_zero h1.symm

/-- The valuation of `singleWitness u` is `u` (its unique support point). -/
lemma singleWitness_val {p : ℕ} [Fact (Nat.Prime p)] (u : ℚ) :
    FormalizedSparse.val p (singleWitness (p := p) u) = ((u : ℚ) : WithTop ℚ) := by
  classical
  rw [FormalizedSparse.val]
  change (if h : singleWitness (p := p) u = 0 then (⊤ : WithTop ℚ) else _) = _
  rw [dif_neg (singleWitness_ne u)]
  congr 1
  have hmem : (FormalizedSparse.support_IsPWO (singleWitness (p := p) u)).isWF.min
      (support_nonempty_of_nonzero p _ (singleWitness_ne u)) ∈ (singleWitness (p := p) u).support :=
    (FormalizedSparse.support_IsPWO (singleWitness (p := p) u)).isWF.min_mem _
  rw [singleWitness_support] at hmem
  exact Set.mem_singleton_iff.mp hmem

/-- **Obligation (A) of `prop:167`'s Step 4.** The valuation ball `{h | u < val(f - h)}` is a
neighbourhood of `f` in `𝕃_[p]`. Proof: `singleWitness u` realises the value group element
`γ₀ = ofAdd(toDual u)`, so the standard valuation-ball-is-a-neighbourhood argument (the
`Valued.mem_nhds`/`Valued.v.restrict` apparatus) applies, and the order-dual encoding turns
`Valued.v (f - h) < γ₀` back into `u < val (f - h)`. -/
lemma ball_val_mem_nhds {p : ℕ} [Fact (Nat.Prime p)] (f : 𝕃_[p]) (u : ℤ) :
    {h : 𝕃_[p] | (((u : ℚ) : WithTop ℚ)) < FormalizedSparse.val p (f - h)} ∈ nhds f := by
  set γ₀ : Multiplicative (WithTop ℚ)ᵒᵈ :=
    Multiplicative.ofAdd (OrderDual.toDual (((u : ℚ)) : WithTop ℚ)) with hγ₀
  have hγ_ne : γ₀ ≠ 0 := by
    rw [hγ₀, show (0 : Multiplicative (WithTop ℚ)ᵒᵈ)
        = Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℚ)) from rfl]
    intro h
    exact WithTop.coe_ne_top
      (OrderDual.toDual.injective (Multiplicative.ofAdd.injective h))
  have hwv : Valued.v (singleWitness (p := p) (u : ℚ)) = γ₀ := by
    rw [show Valued.v (singleWitness (p := p) (u : ℚ))
        = Multiplicative.ofAdd (OrderDual.toDual
            (FormalizedSparse.val p (singleWitness (p := p) (u : ℚ)))) from rfl,
      singleWitness_val, hγ₀]
  rw [Valued.mem_nhds]
  have hane : Valued.v.restrict (singleWitness (p := p) (u : ℚ)) ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hwv]; exact hγ_ne
  refine ⟨Units.mk0 (Valued.v.restrict (singleWitness (p := p) (u : ℚ))) hane, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq] at hy ⊢
  rw [Valuation.restrict_lt_iff_lt_embedding, Units.val_mk0, Valuation.embedding_restrict, hwv]
    at hy
  rw [show Valued.v (y - f) = Valued.v (f - y) from by rw [← Valuation.map_neg]; ring_nf] at hy
  rwa [show Valued.v (f - y)
      = Multiplicative.ofAdd (OrderDual.toDual (FormalizedSparse.val p (f - y))) from rfl,
    hγ₀, Multiplicative.ofAdd_lt, OrderDual.toDual_lt_toDual] at hy

/-- **Proposition `prop:167`: the necessary condition for bounded `p`-adic Hahn series.**

Let `f = ∑_{q∈ℚ} [f q] p^q ∈ 𝕃_[p]` be a `p`-adic Hahn series with bounded support. If `f` is
algebraic over `ℚᵘⁿ_[p]`, then the coefficient function `F_f = f.coeff` is QTR. The proof goes
through `kedlaya_2017_theorem13_4` (`thm:47`), `isAlgebraic_iff_isQTR` (`prop:54845`) and
`isQTR_restrict` (`lem:36014`). -/
theorem isQTR_of_isAlgebraic_of_bddSupport {p : ℕ} [Fact (Nat.Prime p)]
    (f : 𝕃_[p]) (halg : IsAlgebraic ℚᵘⁿ_[p] f) (hbdd : Bornology.IsBounded f.support) :
    ∃ (a : ℕ+) (b c : ℕ) (M N : ℕ+), IsQTR f.coeff a b c M N := by
  -- Step 1: `f` lies in the integral closure of `ℚᵘⁿ_[p]` in `𝕃_[p]`.
  have hf_int : f ∈ integralClosure ℚᵘⁿ_[p] 𝕃_[p] := by
    rw [mem_integralClosure_iff, ← isAlgebraic_iff_isIntegral]; exact halg
  -- Step 2: hence `f` is in the closure of the set of algebraic approximants (Kedlaya thm:47).
  have hf_clos : f ∈ closure { g : 𝕃_[p] | ∃ g' : HahnSeries ℚ (𝔽ᵃ_[p]),
      IsAlgebraic 𝔽ᵃ_[p] g' ∧ (exists_canonical_expansion g).choose.val = g'.coeff} := by
    rw [← Kedlaya.kedlaya_2017_theorem13_4 p]
    exact subset_closure hf_int
  -- Step 3: bounded support gives an integer ceiling `u` with `Supp(f) ⊆ (-∞, u]`.
  obtain ⟨u, hu⟩ : ∃ u : ℤ, ∀ q ∈ f.support, q ≤ (u : ℚ) := by
    obtain ⟨r, hr⟩ := hbdd.subset_closedBall (0 : ℚ)
    refine ⟨⌈r⌉, fun q hq => ?_⟩
    have hdist := hr hq
    rw [Metric.mem_closedBall, Rat.dist_eq] at hdist
    have h2 : (q : ℝ) ≤ r := by
      have := le_trans (le_abs_self ((q : ℝ) - (0 : ℚ))) hdist
      push_cast at this ⊢; linarith
    exact_mod_cast le_trans h2 (Int.le_ceil r)
  -- `f.coeff` vanishes strictly above `u` (its support lies in `(-∞, u]`).
  have hvanish : ∀ q : ℚ, (u : ℚ) < q → f.coeff q = 0 := by
    intro q hq
    by_contra hne
    have hmem : q ∈ f.support := by
      simp only [pAdicHahnSeries.support, Function.mem_support]; exact hne
    exact absurd (hu q hmem) (not_le.mpr hq)
  -- Step 4 (Kedlaya thm:47, the topological heart): from `f ∈ closure {approximants}` and the
  -- support bound, extract an approximant `g` whose canonical coefficients `g'.coeff` (with `g'`
  -- algebraic over `𝔽ᵃ_[p]`) agree with `F_f` on `(-∞, u]`. It splits into two facts about the
  -- valuation topology on `𝕃_[p]`, each a consequence of the (private) canonical isometry
  -- `val (x - y) = orderTop (canon x - canon y)` of `PAdicHahnSeries.lean`:
  --   (A) the open ball `{h | u < val (f - h)}` is a neighbourhood of `f`;
  --   (B) `u < val (f - h)` forces `F_f` and `F_h` to agree on `(-∞, u]` (the minimal point of
  --       the canonical difference exceeds `u`, and the leading Teichmüller coefficient is a unit).
  -- Given (A) and (B), the closure membership yields the approximant by `mem_closure_iff_nhds`.
  obtain ⟨g', hg'alg, hagree⟩ : ∃ (g' : HahnSeries ℚ (𝔽ᵃ_[p])), IsAlgebraic 𝔽ᵃ_[p] g' ∧
      ∀ q : ℚ, q ≤ (u : ℚ) → f.coeff q = g'.coeff q := by
    -- (A) the valuation ball is a neighbourhood of `f` (proved via the `singleWitness` element).
    have hnhds : {h : 𝕃_[p] | (((u : ℚ) : WithTop ℚ)) < FormalizedSparse.val p (f - h)} ∈ nhds f :=
      ball_val_mem_nhds f u
    -- (B) high valuation of the difference ⇒ coefficient agreement on `(-∞, u]`.
    have hbridge : ∀ h : 𝕃_[p], (((u : ℚ) : WithTop ℚ)) < FormalizedSparse.val p (f - h) →
        ∀ q : ℚ, q ≤ (u : ℚ) → f.coeff q = h.coeff q :=
      fun h hh => coeff_agree_of_lt_val f h u hh
    -- Plumbing: extract the approximant from the closure membership inside the ball.
    rw [mem_closure_iff_nhds] at hf_clos
    obtain ⟨g, hg_nhds, hg_mem⟩ := hf_clos _ hnhds
    obtain ⟨g', hg'alg, hg'coeff⟩ := hg_mem
    refine ⟨g', hg'alg, fun q hq => ?_⟩
    have h1 : f.coeff q = g.coeff q := hbridge g hg_nhds q hq
    have h2 : g.coeff q = g'.coeff q := by
      rw [show g.coeff = (exists_canonical_expansion g).choose.val from rfl, hg'coeff]
    rw [h1, h2]
  -- Step 5 (final assembly): `g'.coeff` is QTR by `prop:54845` (after lifting algebraicity to
  -- `𝔽ᵃ_[p]⸨X⸩`); its restriction to `(-∞, u]` is QTR by `lem:36014`; and that restriction is
  -- exactly `F_f` since `F_f` agrees with `g'.coeff` below `u` and vanishes above it.
  obtain ⟨a, b, c, M, N, hg'QTR⟩ :=
    (isAlgebraic_iff_isQTR g').mp (isAlgebraic_LaurentSeries_of_isAlgebraic_constants hg'alg)
  have hrestr := isQTR_restrict hg'QTR u
  have hfeq : f.coeff = fun q => if q ≤ (u : ℚ) then g'.coeff q else 0 := by
    funext q
    by_cases hq : q ≤ (u : ℚ)
    · rw [if_pos hq, hagree q hq]
    · rw [if_neg hq, hvanish q (not_le.mp hq)]
  rw [hfeq]
  exact ⟨a, b, c, M, N, hrestr⟩

end FormalizedSparse
