import FormalizedSparse.QuasiTwistRecurrent
import Mathlib.Topology.DerivedSet
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Set.Finite.List

/- USER: This file corresponds to the subsection `Ray decomposition of the QTR sets` in section
`Application: $p$-adic Hahn series with bounded support`. You need to formalize every thing in this
subsection in this file. I will give you several hints on the formalization:
-/

namespace FormalizedSparse

open Kedlaya

/-!
## §6.2 — Ray decomposition of QTR sets

Throughout this section we fix `p` prime, `a : ℕ+`, `b : ℤ`, `c : ℕ`, `m : ℤ` with `m ≥ -b`,
`M N : ℕ+`, and a set `S ⊆ Sabc p a b c`.

The main goal is `qtr_ray_decomposition` (`coro:48108`): a bounded QTR set with finitely many
accumulation points decomposes as a finite set plus finitely many pairwise disjoint rays.
-/

/-!
### Helper: the `m`-slice `S_{a,b,c,m}`

This is the subset of `Sabc p a b c` whose elements have integer part `m` (i.e. the value is
`(1/a)(m - 0.q₁q₂⋯)` for fixed `m`). It is used in conditions (S1) and (S3) and in the
decomposition of `U` into slices.
-/

/-- The slice `S_{a,b,c,m}` of `Sabc p a b c` at integer part `m : ℤ`.

```
S_{a,b,c,m} = { (1/a)(m - ∑_{i≥1} qᵢ p^{-i}) | qᵢ ∈ {0,…,p-1}, ∑ qᵢ ≤ c }
```

Modelled as elements of `Sabc` arising from the fixed integer `m` and a finitely-supported digit
sequence `d : ℕ →₀ ℕ` (with `d i` the digit `q_{i+1}`). -/
noncomputable def Sabc_m (p : ℕ) [Fact (Nat.Prime p)] (a : ℕ+) (c : ℕ) (m : ℤ) : Set ℚ :=
  { s : ℚ | ∃ (d : ℕ →₀ ℕ),
      (∀ i, d i < p) ∧ (d.sum fun _ v => v) ≤ c ∧
      s = (1 / (a : ℚ)) *
        ((m : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) }

/-!
### Admissible sets (`def:admissible`)
-/

/-- **Definition `def:admissible`**: `(a,b,c,m,M,N)`-admissible sets.

A set `S ⊆ Sabc p a b c` is **`(a,b,c,m,M,N)`-admissible** if it satisfies the three conditions:

- **(S1)** `S ⊆ Sabc_m p a c m` (the slice with fixed integer part `m`, where `m ≥ -b`);

- **(S2)** For every `q ∈ S` written as `q = (1/a)(m - ∑ᵢ dᵢ p^{-(i+1)})` (with `dᵢ < p`,
  `∑ dᵢ ≤ c`), if the digit sequence has `M` consecutive zeros starting at position `k`
  (i.e. `d i = 0` for `k ≤ i < k + M`), then the `N`-zero insertion
  `(1/a)(m - ∑ᵢ dᵢ' p^{-(i+1)})`, where `d'` shifts digits at index `≥ k+M` rightward by `N`,
  also lies in `S`.

- **(S3)** `S` has only finitely many accumulation points: `(derivedSet S).Finite`.

Note: (S2) is strictly weaker than the QTR recurrence (Def `def:16557`) because it only requires
the single element `q ∈ S` itself (not all `w ≥ -b`). -/
def IsAdmissible (p : ℕ) [Fact (Nat.Prime p)] (a : ℕ+) (b : ℤ) (c : ℕ)
    (m : ℤ) (_hm : -b ≤ m) (M N : ℕ+) (S : Set ℚ) : Prop :=
  -- (S1) S is contained in the m-slice
  (S ⊆ Sabc_m p a c m) ∧
  -- (S2) M-zero-run closure under N-zero insertion
  (∀ (d : ℕ →₀ ℕ), (∀ i, d i < p) → (d.sum fun _ v => v) ≤ c →
    let q := (1 / (a : ℚ)) *
      ((m : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
    q ∈ S →
    ∀ (k : ℕ), (∀ i, k ≤ i → i < k + (M : ℕ) → d i = 0) →
      let d' := Finsupp.mapDomain
        (fun i => if i < k + (M : ℕ) then i else i + (N : ℕ)) d
      (1 / (a : ℚ)) *
        ((m : ℚ) - d'.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∈ S) ∧
  -- (S3) finitely many accumulation points
  (derivedSet S).Finite

/-!
### Words and gap vectors (`def:word-gap`)
-/

/-- **Definition `def:word-gap` (word part)**: the word of an element of `Sabc`.

Given an element of `Sabc p a b c` encoded by a finsupp `d : ℕ →₀ ℕ` (with `d i` the digit
`q_{i+1}`), the **word** of `q` is the list of nonzero digit values, read in increasing order of
position.

More precisely: sort the support of `d` in increasing order, then map each position to its digit
value. This gives the tuple of nonzero digits of `0.q₁q₂⋯` in left-to-right order. -/
noncomputable def word (d : ℕ →₀ ℕ) : List ℕ :=
  (d.support.sort (· ≤ ·)).map (fun i => d i)

/-- **Definition `def:word-gap` (gap vector part)**: the gap vector of an element of `Sabc`.

The **gap vector** of `q` (encoded by `d : ℕ →₀ ℕ`) is the list of zero-gaps between consecutive
nonzero digits. The `i`-th entry counts the number of zero digits between the `(i-1)`-th and
`i`-th nonzero digits (the 0-th entry counts leading zeros before the first nonzero digit).

Concretely: let `pos = (d.support.sort (· ≤ ·))` be the sorted positions of nonzero digits.
- Entry 0 = `pos[0]` (0-indexed leading zeros before the first nonzero digit).
- Entry `i` (for `i ≥ 1`) = `pos[i] - pos[i-1] - 1` (zeros strictly between positions `i-1` and `i`).
-/
noncomputable def gapVector (d : ℕ →₀ ℕ) : List ℕ :=
  let pos := d.support.sort (· ≤ ·)
  match pos with
  | [] => []
  | hd :: tl =>
    -- Leading zeros before the first nonzero digit
    hd :: (List.zipWith (fun a b => b - a - 1) (hd :: tl).dropLast tl)

/-!
### Structural lemmas
-/

/-- **Lemma `lem:5966`**: word length is bounded by `c`.

For every element of `S` (encoded by `d : ℕ →₀ ℕ` with `∑ d ≤ c`), the word of `q` has length
at most `c`. In particular, only finitely many words occur among elements of `S`.

*Proof sketch*: by (S1), `S ⊆ Sabc_m p a c m`, so every element has digit sum `∑ dᵢ ≤ c`.
Each nonzero digit is `≥ 1`, so the word length = number of nonzero digits ≤ `∑ dᵢ ≤ c`. -/
theorem word_length_le {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {b : ℤ} {c : ℕ}
    {m : ℤ} {hm : -b ≤ m} {M N : ℕ+} {S : Set ℚ}
    (_hS : IsAdmissible p a b c m hm M N S)
    (d : ℕ →₀ ℕ) (hd_sum : d.sum (fun _ v => v) ≤ c) :
    (word d).length ≤ c := by
  -- `word d` has length = number of nonzero digits = `d.support.card`; each nonzero
  -- digit is `≥ 1`, so the card is `≤ ∑ d i = d.sum (fun _ v => v) ≤ c`.
  unfold word
  rw [List.length_map, Finset.length_sort]
  calc d.support.card
      = ∑ _i ∈ d.support, 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ i ∈ d.support, d i :=
        Finset.sum_le_sum (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
    _ ≤ c := hd_sum

/-!
### Reindexing helpers

The digit-insertion of condition (S2) is a `Finsupp.mapDomain` along the strictly monotone
reindexing `φ = fun j => if j < k + M then j else j + N`. These helpers record that such a
reindexing preserves the word, the digit sum and the digit bound.
-/

/-- The digit-insertion reindexing `fun j => if j < s then j else j + N` is strictly monotone. -/
theorem strictMono_insertZeros (s N : ℕ) :
    StrictMono (fun j => if j < s then j else j + N) := by
  intro i j hij
  by_cases hi : i < s
  · by_cases hj : j < s
    · simp only [hi, hj, if_true]; exact hij
    · simp only [hi, hj, if_true, if_false]; omega
  · have hj : ¬ j < s := by omega
    simp only [hi, hj, if_false]; omega

/-- A strictly monotone reindexing preserves the word (sorted list of nonzero digit values). -/
theorem word_mapDomain_strictMono (d : ℕ →₀ ℕ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    word (Finsupp.mapDomain φ d) = word d := by
  have hinj : Function.Injective φ := hφ.injective
  have he : (Finsupp.mapDomain φ d).support = Finset.map ⟨φ, hinj⟩ d.support := by
    rw [Finsupp.mapDomain_support_of_injective hinj d]
    exact (Finset.map_eq_image ⟨φ, hinj⟩ d.support).symm
  unfold word
  rw [he, ← StrictMonoOn.map_finsetSort ⟨φ, hinj⟩ d.support (hφ.strictMonoOn _), List.map_map]
  apply List.map_congr_left
  intro i _
  change (Finsupp.mapDomain φ d) (φ i) = d i
  exact Finsupp.mapDomain_apply hinj d i

/-- A injective reindexing preserves the digit sum. -/
theorem sum_mapDomain_inj (d : ℕ →₀ ℕ) {φ : ℕ → ℕ} (hinj : Function.Injective φ) :
    (Finsupp.mapDomain φ d).sum (fun _ v => v) = d.sum (fun _ v => v) :=
  Finsupp.sum_mapDomain_index_inj hinj

/-- An injective reindexing keeps all digits `< p`. -/
theorem mapDomain_digit_lt {p : ℕ} [Fact (Nat.Prime p)] (d : ℕ →₀ ℕ)
    {φ : ℕ → ℕ} (hinj : Function.Injective φ) (hd : ∀ i, d i < p) :
    ∀ j, (Finsupp.mapDomain φ d) j < p := by
  intro j
  by_cases hj : j ∈ (Finsupp.mapDomain φ d).support
  · rw [Finsupp.mapDomain_support_of_injective hinj d] at hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    rw [Finsupp.mapDomain_apply hinj]
    exact hd i
  · rw [Finsupp.notMem_support_iff.mp hj]
    exact (Fact.out (p := Nat.Prime p)).pos

/-!
### Gap-vector computation helpers

`gapVector d` has length `d.support.card` (one entry per nonzero digit), and its `j`-th entry is
computed from the sorted support positions: entry `0` is the first position, entry `j ≥ 1` is the
gap `pos[j] - pos[j-1] - 1` between consecutive nonzero positions. These two facts drive every
combinatorial argument in this section.
-/

/-- `gapVector d` unfolded to a pattern match on the sorted support (a `rfl`-lemma that
sidesteps the fragile `let` in the definition). -/
theorem gapVector_eq (d : ℕ →₀ ℕ) :
    gapVector d = (match d.support.sort (· ≤ ·) with
      | [] => []
      | hd :: tl => hd :: (List.zipWith (fun a b => b - a - 1) (hd :: tl).dropLast tl)) := rfl

/-- The gap operation as a pure list function: leading entry plus consecutive-difference-minus-one.
`gapVector` is this applied to the sorted support, so all the combinatorics is proved here by
plain list induction, free of the fragile `Finset.sort` unfolding. -/
def gapOfList (pos : List ℕ) : List ℕ :=
  match pos with
  | [] => []
  | hd :: tl => hd :: (List.zipWith (fun a b => b - a - 1) (hd :: tl).dropLast tl)

/-- `gapVector d = gapOfList (sorted support of d)`. -/
theorem gapVector_eq_gapOfList (d : ℕ →₀ ℕ) :
    gapVector d = gapOfList (d.support.sort (· ≤ ·)) := rfl

/-- `gapOfList` preserves length. -/
theorem gapOfList_length (pos : List ℕ) : (gapOfList pos).length = pos.length := by
  cases pos with
  | nil => rfl
  | cons hd tl =>
    simp only [gapOfList, List.length_cons, List.length_zipWith, List.length_dropLast]; simp

/-- The `j`-th entry of `gapOfList pos`: `pos.getI 0` for `j = 0`, and `pos.getI j - pos.getI (j-1)
- 1` for `j ≥ 1`. -/
theorem gapOfList_getI (pos : List ℕ) (j : ℕ) (hj : j < pos.length) :
    (gapOfList pos).getI j =
      pos.getI j - (if j = 0 then 0 else pos.getI (j-1) + 1) := by
  cases pos with
  | nil => simp at hj
  | cons hd tl =>
    cases j with
    | zero => simp [gapOfList]
    | succ i =>
      simp only [gapOfList, Nat.succ_ne_zero, if_false, List.getI_cons_succ, Nat.add_sub_cancel]
      have hilt : i < tl.length := by simp at hj; omega
      rw [List.getI_eq_getElem (l := List.zipWith (fun a b => b - a - 1) (hd :: tl).dropLast tl)
            (by simp [List.length_zipWith, List.length_dropLast]; omega),
          List.getElem_zipWith, List.getElem_dropLast,
          List.getI_eq_getElem (l := tl) hilt,
          List.getI_eq_getElem (l := hd :: tl) (by simp; omega)]
      omega

/-- `gapVector d` has one entry per nonzero digit of `d`. -/
theorem gapVector_length (d : ℕ →₀ ℕ) : (gapVector d).length = d.support.card := by
  rw [gapVector_eq_gapOfList, gapOfList_length, Finset.length_sort]

/-- The `j`-th entry of `gapVector d` (via `getI`, total) in terms of the sorted support
positions: `pos.getI 0` for `j = 0`, and `pos.getI j - pos.getI (j-1) - 1` for `j ≥ 1`. -/
theorem gapVector_getI (d : ℕ →₀ ℕ) (j : ℕ) (hj : j < (gapVector d).length) :
    (gapVector d).getI j =
      (d.support.sort (· ≤ ·)).getI j
        - (if j = 0 then 0 else (d.support.sort (· ≤ ·)).getI (j-1) + 1) := by
  rw [gapVector_eq_gapOfList]
  apply gapOfList_getI
  rw [Finset.length_sort, ← gapVector_length]; exact hj

/-- `getI` commutes with `List.map` on in-range indices. -/
theorem map_getI (l : List ℕ) (f : ℕ → ℕ) (j : ℕ) (hj : j < l.length) :
    (l.map f).getI j = f (l.getI j) := by
  rw [List.getI_eq_getElem (l := l.map f) (by simpa using hj), List.getElem_map,
      List.getI_eq_getElem (l := l) hj]

/-- `getI` of a `List.set` on in-range indices. -/
theorem set_getI (l : List ℕ) (i : ℕ) (v : ℕ) (j : ℕ) (hj : j < l.length) :
    (l.set i v).getI j = if i = j then v else l.getI j := by
  rw [List.getI_eq_getElem (l := l.set i v) (by simpa using hj), List.getElem_set,
      List.getI_eq_getElem (l := l) hj]

/-- `getI` of a `List.set` at the set index. -/
theorem set_getI_self (l : List ℕ) (i v : ℕ) (hi : i < l.length) :
    (l.set i v).getI i = v := by
  rw [List.getI_eq_getElem (l := l.set i v) (by simpa using hi), List.getElem_set_self]

/-- **The pure-list core of `gap_add_mem`.** Inserting `N` extra zeros at the `i`-th gap is the
reindexing `φ = fun x => if x < pos.getI i then x else x + N` of the sorted support `pos`; this
adds exactly `N` to the `i`-th coordinate of the gap vector and leaves the rest untouched.
Stated as a fact about `gapOfList` and a strictly-increasing list `pos`. -/
theorem gapOfList_map_insertZeros (pos : List ℕ)
    (hmono : ∀ j₁ j₂, j₁ < j₂ → j₂ < pos.length → pos.getI j₁ < pos.getI j₂)
    (i N : ℕ) (hi : i < pos.length) :
    gapOfList (pos.map (fun x => if x < pos.getI i then x else x + N))
      = (gapOfList pos).set i ((gapOfList pos).getI i + N) := by
  set φ : ℕ → ℕ := fun x => if x < pos.getI i then x else x + N with hφ
  have hlen : (pos.map φ).length = pos.length := by rw [List.length_map]
  have hφval : ∀ l, l < pos.length →
      φ (pos.getI l) = if l < i then pos.getI l else pos.getI l + N := by
    intro l hl
    simp only [hφ]
    by_cases hli : l < i
    · have : pos.getI l < pos.getI i := hmono l i hli hi
      simp [hli, this]
    · have hge : ¬ pos.getI l < pos.getI i := by
        rcases Nat.lt_or_ge i l with h | h
        · have := hmono i l h hl; omega
        · have : l = i := by omega
          subst this; omega
      simp [hli, hge]
  apply List.ext_getElem
  · rw [gapOfList_length, List.length_set, gapOfList_length, List.length_map]
  · intro j h1 h2
    have jlen : j < pos.length := by rw [gapOfList_length, hlen] at h1; exact h1
    rw [← List.getI_eq_getElem (l := gapOfList (pos.map φ)),
        ← List.getI_eq_getElem (l := (gapOfList pos).set i _)]
    rw [gapOfList_getI _ _ (by rw [hlen]; exact jlen)]
    rw [map_getI _ _ _ jlen, hφval j jlen]
    rw [set_getI _ _ _ _ (by rw [gapOfList_length]; exact jlen)]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, gapOfList_getI _ _ hi]
      by_cases hi0 : i = 0
      · subst hi0; simp
      · have hjm1 : i - 1 < pos.length := by omega
        rw [map_getI _ _ _ hjm1, hφval (i-1) hjm1]
        have hm := hmono (i-1) i (by omega) hi
        simp only [if_neg hi0, if_neg (show ¬ i < i by omega), if_pos (show i - 1 < i by omega)]
        omega
    · rw [if_neg hij, gapOfList_getI _ _ jlen]
      by_cases hj0 : j = 0
      · subst hj0
        have hpos : 0 < i := by omega
        simp only [if_true, if_pos hpos]
      · have hjm1 : j - 1 < pos.length := by omega
        rw [map_getI _ _ _ hjm1, hφval (j-1) hjm1]
        simp only [if_neg hj0]
        rcases Nat.lt_or_ge j i with hlt | hge
        · simp only [if_pos (show j < i by omega), if_pos (show j - 1 < i by omega)]
        · have hgt : i < j := by omega
          have hm := hmono (j-1) j (by omega) jlen
          simp only [if_neg (show ¬ j < i by omega), if_neg (show ¬ j - 1 < i by omega)]
          omega

/-- The sorted support of `mapDomain φ d` (for `φ` strictly monotone) is the sorted support of `d`
mapped through `φ`. -/
theorem support_sort_mapDomain (d : ℕ →₀ ℕ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    (Finsupp.mapDomain φ d).support.sort (· ≤ ·) = (d.support.sort (· ≤ ·)).map φ := by
  have hinj : Function.Injective φ := hφ.injective
  have he : (Finsupp.mapDomain φ d).support = Finset.map ⟨φ, hinj⟩ d.support := by
    rw [Finsupp.mapDomain_support_of_injective hinj d]
    exact (Finset.map_eq_image ⟨φ, hinj⟩ d.support).symm
  rw [he, ← StrictMonoOn.map_finsetSort ⟨φ, hinj⟩ d.support (hφ.strictMonoOn _)]
  rfl

/-- The sorted support of `d` is strictly increasing (in `getI` form). -/
theorem support_sort_strictMono (d : ℕ →₀ ℕ) (l₁ l₂ : ℕ)
    (h12 : l₁ < l₂) (h2 : l₂ < (d.support.sort (· ≤ ·)).length) :
    (d.support.sort (· ≤ ·)).getI l₁ < (d.support.sort (· ≤ ·)).getI l₂ := by
  have h1 : l₁ < (d.support.sort (· ≤ ·)).length := by omega
  rw [List.getI_eq_getElem (l := d.support.sort (· ≤ ·)) h1,
      List.getI_eq_getElem (l := d.support.sort (· ≤ ·)) h2]
  have hsm := d.support.sortedLT_sort
  exact hsm (show (⟨l₁, h1⟩ : Fin _) < ⟨l₂, h2⟩ from h12)

/-- Each entry of the sorted support of `d` is an element of `d.support`. -/
theorem support_sort_getI_mem (d : ℕ →₀ ℕ) (l : ℕ)
    (hl : l < (d.support.sort (· ≤ ·)).length) :
    (d.support.sort (· ≤ ·)).getI l ∈ d.support := by
  rw [List.getI_eq_getElem (l := d.support.sort (· ≤ ·)) hl]
  have : (d.support.sort (· ≤ ·))[l] ∈ d.support.sort (· ≤ ·) := List.getElem_mem hl
  rwa [Finset.mem_sort] at this

/-- Every element of `d.support` is some entry of the sorted support. -/
theorem mem_support_eq_getI (d : ℕ →₀ ℕ) (x : ℕ) (hx : x ∈ d.support) :
    ∃ l, l < (d.support.sort (· ≤ ·)).length ∧ (d.support.sort (· ≤ ·)).getI l = x := by
  have hx2 : x ∈ d.support.sort (· ≤ ·) := by rwa [Finset.mem_sort]
  rw [List.mem_iff_getElem] at hx2
  obtain ⟨l, hl, hlx⟩ := hx2
  exact ⟨l, hl, by rw [List.getI_eq_getElem (l := d.support.sort (· ≤ ·)) hl]; exact hlx⟩

/-- **Lemma `lem:30089`**: the gap-addition closure.

Fix a word `d` (a finsupp encoding a nonzero-digit pattern) and let `G_d ⊆ ℕ^t` be the set of gap
vectors of elements of `S` with word `d`. If `g ∈ G_d` and the `i`-th gap coordinate `g[i] ≥ M`,
then `g` with coordinate `i` incremented by `N` (i.e. `g + N eᵢ`) is also in `G_d`.

This is a direct rephrasing of condition (S2): a gap of size `≥ M` at position `i` is exactly a
run of `M` consecutive zeros at the `i`-th gap, and inserting `N` further zeros there produces an
element of `S` with the same word and gap vector `g + N eᵢ`.

We formulate this in terms of gap-vector lists: if `gapVector d = g` and `g.getI i ≥ M`, then
there exists `d'` with `word d' = word d` and `gapVector d' = g.set i (g.getI i + N)` and
the corresponding element is in `S`. -/
theorem gap_add_mem {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {b : ℤ} {c : ℕ}
    {m : ℤ} {hm : -b ≤ m} {M N : ℕ+} {S : Set ℚ}
    (hS : IsAdmissible p a b c m hm M N S)
    -- `d` encodes some element of S
    (d : ℕ →₀ ℕ) (hd_digit : ∀ i, d i < p) (hd_sum : d.sum (fun _ v => v) ≤ c)
    (hq : (1 / (a : ℚ)) *
      ((m : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∈ S)
    -- `i` is a gap index with gap length ≥ M
    (i : ℕ) (hi : M ≤ (gapVector d).getI i) :
    -- There is an element in S obtained by inserting N zeros at gap i
    ∃ (d' : ℕ →₀ ℕ),
      word d' = word d ∧
      gapVector d' = (gapVector d).set i ((gapVector d).getI i + N) ∧
      (∀ j, d' j < p) ∧ (d'.sum fun _ v => v) ≤ c ∧
      (1 / (a : ℚ)) *
        ((m : ℚ) - d'.sum fun j v => (v : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ))) ∈ S := by
  classical
  set pos := d.support.sort (· ≤ ·) with hpos
  clear_value pos
  -- `i` is a valid gap index: otherwise `getI i = 0 < M`, contradicting `hi`.
  have hi_lt : i < (gapVector d).length := by
    by_contra hcon
    rw [not_lt] at hcon
    rw [List.getI_eq_default _ hcon] at hi
    simp only [Nat.default_eq_zero] at hi
    have hMpos : 0 < (M : ℕ) := M.pos
    omega
  have hi_pos : i < pos.length := by
    rw [hpos, Finset.length_sort, ← gapVector_length]; exact hi_lt
  -- `pos`-stated forms of the support-sort helpers (kept opaque so `omega` sees one atom).
  have hmono_pos : ∀ l₁ l₂, l₁ < l₂ → l₂ < pos.length → pos.getI l₁ < pos.getI l₂ := by
    intro l₁ l₂ h12 h2; rw [hpos] at h2 ⊢; exact support_sort_strictMono d l₁ l₂ h12 h2
  have hmem_pos : ∀ x, x ∈ d.support → ∃ l, l < pos.length ∧ pos.getI l = x := by
    intro x hx; rw [hpos]; exact mem_support_eq_getI d x hx
  -- The gap before position `i` in terms of the sorted support positions.
  have hgapi : (gapVector d).getI i = pos.getI i - (if i = 0 then 0 else pos.getI (i-1) + 1) := by
    rw [gapVector_getI _ _ hi_lt, ← hpos]
  -- `M ≤ pos.getI i` (the gap is `≥ M`), and the (S2) start index `k` with `k + M = pos.getI i`.
  have hM_le : (M : ℕ) ≤ pos.getI i := by
    have h := hi; rw [hgapi] at h; exact le_trans h (Nat.sub_le _ _)
  set k : ℕ := pos.getI i - (M : ℕ) with hk
  have hkM : k + (M : ℕ) = pos.getI i := by rw [hk]; omega
  -- Build `d'` via the digit-insertion reindexing `ψ` with threshold `pos.getI i`.
  set ψ : ℕ → ℕ := fun x => if x < pos.getI i then x else x + (N : ℕ) with hψ
  have hψmono : StrictMono ψ := by rw [hψ]; exact strictMono_insertZeros _ _
  refine ⟨Finsupp.mapDomain ψ d, ?_, ?_, ?_, ?_, ?_⟩
  · -- word preserved
    exact word_mapDomain_strictMono d hψmono
  · -- gap vector: `+N` at coordinate `i`
    rw [gapVector_eq_gapOfList, gapVector_eq_gapOfList, support_sort_mapDomain d hψmono, ← hpos, hψ]
    exact gapOfList_map_insertZeros pos hmono_pos i (N : ℕ) hi_pos
  · -- digits stay `< p`
    exact mapDomain_digit_lt d hψmono.injective hd_digit
  · -- digit sum preserved (hence `≤ c`)
    rw [sum_mapDomain_inj d hψmono.injective]; exact hd_sum
  · -- membership: condition (S2) applied at the run of `M` zeros starting at `k`.
    -- the run of `M` zeros at position `k`: positions in `[k, k+M)` are not in the support.
    have hrun : ∀ x, k ≤ x → x < k + (M : ℕ) → d x = 0 := by
      intro x hx1 hx2
      by_contra hne
      obtain ⟨l, hl, hlx⟩ := hmem_pos x (Finsupp.mem_support_iff.mpr hne)
      have hxlt : pos.getI l < pos.getI i := by rw [hlx]; omega
      have hli : l < i := by
        rcases lt_trichotomy l i with h | h | h
        · exact h
        · subst h; exact absurd hxlt (lt_irrefl _)
        · exact absurd (hmono_pos i l h hl) (by omega)
      have hi0 : i ≠ 0 := by rintro rfl; exact absurd hli (Nat.not_lt_zero _)
      have hle : pos.getI l ≤ pos.getI (i-1) := by
        rcases eq_or_lt_of_le (show l ≤ i - 1 by omega) with heq | hlt
        · rw [heq]
        · exact le_of_lt (hmono_pos l (i-1) hlt (by omega))
      have hgap_lb : pos.getI (i-1) + 1 ≤ k := by
        have h := hi; rw [hgapi, if_neg hi0] at h; omega
      omega
    have hmem := hS.2.1 d hd_digit hd_sum hq k hrun
    rw [hψ, ← hkM]
    exact hmem

/-!
### Order-type infrastructure for `lem:27279`

The deep lemma `gap_at_most_one_ge_M` argues that two gaps `≥ M` produce an `ω²`-ordered family
inside `S`, contradicting (S3). The following helpers package the analytic content: the digit
value of an `N`-zero insertion, iterated insertion at a fixed threshold, the threshold form of
condition (S2), and the sequential criterion for membership in `derivedSet`.
-/

/-- Membership in `derivedSet` from a convergent sequence of distinct points of `S`. -/
theorem mem_derivedSet_of_tendsto_seq {α : Type*} [TopologicalSpace α] {S : Set α} {x : α}
    (u : ℕ → α) (hmem : ∀ n, u n ∈ S) (hne : ∀ n, u n ≠ x)
    (hlim : Filter.Tendsto u Filter.atTop (nhds x)) : x ∈ derivedSet S := by
  rw [mem_derivedSet, accPt_iff_frequently, Filter.frequently_iff]
  intro U hU
  have hUE : ∀ᶠ n in Filter.atTop, u n ∈ U := hlim hU
  rcases (Filter.eventually_atTop.1 hUE) with ⟨N, hN⟩
  exact ⟨u N, hN N le_rfl, hne N, hmem N⟩

/-- Single-threshold split of the digit value of an insertion `insertAt s n` (insert `n` zeros at
threshold `s`): the value is `head + p^{-n}·tail` where `head`/`tail` are the digit-value sums over
the position blocks `< s` and `≥ s`. -/
theorem digitVal_split {p : ℕ} [Fact (Nat.Prime p)] (d : ℕ →₀ ℕ) (s n : ℕ) :
    (Finsupp.mapDomain (fun x => if x < s then x else x + n) d).sum
        (fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      = (∑ i ∈ d.support.filter (fun i => i < s), (d i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
        + (p : ℚ) ^ (-(n : ℤ)) *
          ∑ i ∈ d.support.filter (fun i => s ≤ i), (d i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
  have hp0 : (p : ℚ) ≠ 0 := by
    have := (Fact.out : Nat.Prime p).pos; exact_mod_cast this.ne'
  set σ : ℕ → ℕ := fun x => if x < s then x else x + n with hσ
  have hinj : Function.Injective σ := by
    intro u v huv; simp only [hσ] at huv; split_ifs at huv <;> omega
  rw [Finsupp.sum_mapDomain_index_inj hinj]
  simp only [Finsupp.sum]
  rw [← Finset.sum_filter_add_sum_filter_not d.support (fun i => i < s)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    have hsi : σ i = i := by simp only [hσ]; exact if_pos hi.2
    rw [hsi]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr
    · ext i; simp only [Finset.mem_filter, not_lt]
    · intro i hi
      rw [Finset.mem_filter] at hi
      have hsi : σ i = i + n := by simp only [hσ]; exact if_neg (by omega)
      rw [hsi, show (-(↑(i + n) + 1) : ℤ) = (-(n:ℤ)) + (-(↑i + 1)) by push_cast; ring,
          zpow_add₀ hp0]
      ring

/-- Three-way split of the digit value of a double insertion `ρ_{s,t}` (insert `s·N` zeros at
threshold `Plo`, then `t·N` zeros at threshold `Phi`, with `Plo ≤ Phi`): the value is
`A + p^{-sN}·B + p^{-(s+t)N}·C` where `A,B,C` are the digit-value sums over the position blocks
`< Plo`, `[Plo,Phi)`, `≥ Phi`. -/
theorem digitVal_double_split {p : ℕ} [Fact (Nat.Prime p)] (d : ℕ →₀ ℕ)
    (Plo Phi s t N : ℕ) (hlohi : Plo ≤ Phi) :
    (Finsupp.mapDomain
        (fun x => x + (if Plo ≤ x then s*N else 0) + (if Phi ≤ x then t*N else 0)) d).sum
        (fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      = (∑ x ∈ d.support.filter (fun x => x < Plo), (d x : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ)))
        + (p : ℚ) ^ (-(s*N : ℤ)) *
            (∑ x ∈ d.support.filter (fun x => Plo ≤ x ∧ x < Phi),
              (d x : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ)))
        + (p : ℚ) ^ (-((s*N : ℕ) + t*N : ℤ)) *
            (∑ x ∈ d.support.filter (fun x => Phi ≤ x),
              (d x : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ))) := by
  have hp0 : (p : ℚ) ≠ 0 := by
    have := (Fact.out : Nat.Prime p).pos; exact_mod_cast this.ne'
  set ρ : ℕ → ℕ := fun x => x + (if Plo ≤ x then s*N else 0) + (if Phi ≤ x then t*N else 0) with hρ
  have hinj : Function.Injective ρ := by
    intro u v huv; simp only [hρ] at huv; split_ifs at huv <;> omega
  rw [Finsupp.sum_mapDomain_index_inj hinj]
  simp only [Finsupp.sum]
  set g : ℕ → ℚ := fun x =>
    if x < Plo then (d x : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ))
    else if x < Phi then (p:ℚ)^(-(s*N:ℤ)) * ((d x : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ)))
    else (p:ℚ)^(-((s*N:ℕ)+t*N:ℤ)) * ((d x : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ))) with hg
  have hstep1 : (∑ x ∈ d.support, (d x : ℚ) * (p : ℚ) ^ (-(ρ x + 1 : ℤ)))
      = ∑ x ∈ d.support, g x := by
    apply Finset.sum_congr rfl
    intro x _
    simp only [hg, hρ]
    by_cases h1 : x < Plo
    · rw [if_pos h1, if_neg (by omega : ¬ Plo ≤ x), if_neg (by omega : ¬ Phi ≤ x)]; simp
    · by_cases h2 : x < Phi
      · rw [if_neg h1, if_pos h2, if_pos (by omega : Plo ≤ x), if_neg (by omega : ¬ Phi ≤ x)]
        rw [show (-(↑(x + s*N + 0) + 1) : ℤ) = (-(s*N:ℤ)) + (-(↑x+1)) by push_cast; ring,
            zpow_add₀ hp0]; ring
      · rw [if_neg h1, if_neg h2, if_pos (by omega : Plo ≤ x), if_pos (by omega : Phi ≤ x)]
        rw [show (-(↑(x + s*N + t*N) + 1) : ℤ) = (-((s*N:ℕ)+t*N:ℤ)) + (-(↑x+1)) by push_cast; ring,
            zpow_add₀ hp0]; ring
  rw [hstep1]
  have hB1 : (∑ x ∈ d.support.filter (fun x => x < Plo), g x)
      = ∑ x ∈ d.support.filter (fun x => x < Plo), (d x : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ)) := by
    apply Finset.sum_congr rfl; intro x hx; rw [Finset.mem_filter] at hx
    simp only [hg, if_pos hx.2]
  have hB2 : (∑ x ∈ d.support.filter (fun x => Plo ≤ x ∧ x < Phi), g x)
      = (p:ℚ)^(-(s*N:ℤ)) * ∑ x ∈ d.support.filter (fun x => Plo ≤ x ∧ x < Phi),
          (d x : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x hx; rw [Finset.mem_filter] at hx
    simp only [hg, if_neg (by omega : ¬ x < Plo), if_pos hx.2.2]
  have hB3 : (∑ x ∈ d.support.filter (fun x => Phi ≤ x), g x)
      = (p:ℚ)^(-((s*N:ℕ)+t*N:ℤ)) * ∑ x ∈ d.support.filter (fun x => Phi ≤ x),
          (d x : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x hx; rw [Finset.mem_filter] at hx
    simp only [hg, if_neg (by omega : ¬ x < Plo), if_neg (by omega : ¬ x < Phi)]
  have hpart : (∑ x ∈ d.support, g x)
      = (∑ x ∈ d.support.filter (fun x => x < Plo), g x)
        + (∑ x ∈ d.support.filter (fun x => Plo ≤ x ∧ x < Phi), g x)
        + (∑ x ∈ d.support.filter (fun x => Phi ≤ x), g x) := by
    rw [← Finset.sum_filter_add_sum_filter_not d.support (fun x => x < Plo) g, add_assoc]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not (d.support.filter (fun x => ¬ x < Plo))
          (fun x => x < Phi) g]
    congr 1
    · apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext x; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hx,_⟩,h2⟩; exact ⟨hx, by omega, h2⟩
      · rintro ⟨hx,_,h2⟩; exact ⟨⟨hx, by omega⟩, h2⟩
    · apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext x; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hx,_⟩,h2⟩; exact ⟨hx, by omega⟩
      · rintro ⟨hx,h2⟩; exact ⟨⟨hx, by omega⟩, by omega⟩
  rw [hpart, hB1, hB2, hB3]

/-- Iterating insertion at a *fixed* threshold `P` composes: `s` insertions of `N` zeros equals one
insertion of `s·N` zeros. -/
theorem mapDomain_insert_iterate (e : ℕ →₀ ℕ) (P N : ℕ) (s : ℕ) :
    (fun e' => Finsupp.mapDomain (fun x => if x < P then x else x + N) e')^[s] e
      = Finsupp.mapDomain (fun x => if x < P then x else x + s * N) e := by
  induction s with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.zero_mul, add_zero]
    rw [show (fun x : ℕ => if x < P then x else x) = id from by
      funext x; by_cases h : x < P <;> simp [h]]
    rw [Finsupp.mapDomain_id]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, ← Finsupp.mapDomain_comp]
    congr 1
    funext x
    by_cases h : x < P
    · simp [h]
    · simp only [Function.comp, if_neg h]
      have : ¬ x + n * N < P := by omega
      simp only [if_neg this]; ring

/-- Inserting `n` zeros at threshold `P` does not change the digits below `P`. -/
theorem insertAt_below {e : ℕ →₀ ℕ} {P n y : ℕ} (hy : y < P) :
    (Finsupp.mapDomain (fun x => if x < P then x else x + n) e) y = e y := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_eq_single y]
  · simp only [if_pos hy, if_true]
  · intro x _ hxy
    have : (if x < P then x else x + n) ≠ y := by
      by_cases h : x < P
      · simp only [if_pos h]; exact hxy
      · simp only [if_neg h]; omega
    rw [if_neg this]
  · intro hy'; simp only [Finsupp.mem_support_iff, not_not] at hy'; rw [hy']; simp

/-- Above the inserted block (`P + n ≤ x`), the digit of the insertion at `x` is the digit of `e`
at the unshifted position `x - n`. -/
theorem insertAt_above {e : ℕ →₀ ℕ} {P n x : ℕ} (hx : P + n ≤ x) :
    (Finsupp.mapDomain (fun y => if y < P then y else y + n) e) x = e (x - n) := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_eq_single (x - n)]
  · have : (if x - n < P then x - n else x - n + n) = x := by rw [if_neg (by omega)]; omega
    rw [this]; simp
  · intro y _ hyx
    have hne : (if y < P then y else y + n) ≠ x := by
      by_cases h : y < P
      · simp only [if_pos h]; omega
      · simp only [if_neg h]; omega
    rw [if_neg hne]
  · intro hxn; simp only [Finsupp.mem_support_iff, not_not] at hxn; rw [hxn]; simp

/-- **Membership iterator.** If `val e ∈ S` (with digit/sum bounds) and `e` has a length-`M` zero
run on `[P-M, P)`, then inserting `s·N` zeros at threshold `P` keeps the value in `S`, preserves
the digit/sum bounds, and preserves the zero run — so the construction can be iterated. -/
theorem insert_pow_mem {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {b : ℤ} {c : ℕ}
    {m : ℤ} {hm : -b ≤ m} {M N : ℕ+} {S : Set ℚ}
    (hS : IsAdmissible p a b c m hm M N S)
    (P : ℕ) (hPM : (M : ℕ) ≤ P) (s : ℕ) :
    ∀ (e : ℕ →₀ ℕ), (∀ i, e i < p) → (e.sum fun _ v => v) ≤ c →
      (1 / (a : ℚ)) * ((m : ℚ) - e.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∈ S →
      (∀ x, P - (M : ℕ) ≤ x → x < P → e x = 0) →
      let e' := Finsupp.mapDomain (fun x => if x < P then x else x + s * (N : ℕ)) e
      (∀ i, e' i < p) ∧ (e'.sum fun _ v => v) ≤ c ∧
        (1 / (a : ℚ)) * ((m : ℚ) - e'.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∈ S ∧
        (∀ x, P - (M : ℕ) ≤ x → x < P → e' x = 0) := by
  induction s with
  | zero =>
    intro e he_digit he_sum he_mem hrun
    simp only [Nat.zero_mul, add_zero]
    rw [show (fun x : ℕ => if x < P then x else x) = id from by
      funext x; by_cases h : x < P <;> simp [h], Finsupp.mapDomain_id]
    exact ⟨he_digit, he_sum, he_mem, hrun⟩
  | succ n ih =>
    intro e he_digit he_sum he_mem hrun
    -- one more insertion of `N` zeros at `P`, then apply ih to the result.
    set φ : ℕ → ℕ := fun x => if x < P then x else x + (N : ℕ) with hφ
    have hφmono : StrictMono φ := by rw [hφ]; exact strictMono_insertZeros _ _
    set e1 := Finsupp.mapDomain φ e with he1
    -- e1 ∈ S via (S2) at the run [P-M, P).
    have h1_digit : ∀ i, e1 i < p := mapDomain_digit_lt e hφmono.injective he_digit
    have h1_sum : (e1.sum fun _ v => v) ≤ c := by
      rw [he1, sum_mapDomain_inj e hφmono.injective]; exact he_sum
    have h1_mem : (1 / (a : ℚ)) *
        ((m : ℚ) - e1.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∈ S := by
      have := hS.2.1 e he_digit he_sum he_mem (P - (M : ℕ))
        (fun i hi1 hi2 => hrun i (by omega) (by omega))
      rw [show P - (M : ℕ) + (M : ℕ) = P from by omega] at this
      rw [he1, hφ]; exact this
    have h1_run : ∀ x, P - (M : ℕ) ≤ x → x < P → e1 x = 0 := by
      intro x hx1 hx2; rw [he1, hφ, insertAt_below hx2]; exact hrun x hx1 hx2
    -- chain through ih
    have := ih e1 h1_digit h1_sum h1_mem h1_run
    -- rewrite the composed mapDomain
    simp only at this ⊢
    rw [he1, ← Finsupp.mapDomain_comp] at this
    rw [show ((fun x => if x < P then x else x + n * (N:ℕ)) ∘ φ)
        = (fun x => if x < P then x else x + (n+1) * (N:ℕ)) from by
      funext x; rw [hφ]; by_cases h : x < P
      · simp [h]
      · simp only [Function.comp, if_neg h, if_neg (show ¬ x + (N:ℕ) < P by omega)]; ring] at this
    exact this

/-- The doubly-indexed family `v_{s,t}` of values arising from inserting `s·N` zeros at the
`i`-th support position and `t·N` zeros at the `j`-th, all lying in `S`. The core of `lem:27279`:
two gaps `≥ M` make this family contradict (S3). We package the `i < j` case here; the symmetric
statement follows by swapping `i` and `j`. -/
theorem two_gaps_ge_M_absurd {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {b : ℤ} {c : ℕ}
    {m : ℤ} {hm : -b ≤ m} {M N : ℕ+} {S : Set ℚ}
    (hS : IsAdmissible p a b c m hm M N S)
    (d : ℕ →₀ ℕ) (hd_digit : ∀ i, d i < p) (hd_sum : d.sum (fun _ v => v) ≤ c)
    (hq : (1 / (a : ℚ)) *
      ((m : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∈ S)
    (i j : ℕ) (hij : i < j)
    (hi : (M : ℕ) ≤ (gapVector d).getI i) (hj : (M : ℕ) ≤ (gapVector d).getI j) : False := by
  classical
  set pos := d.support.sort (· ≤ ·) with hpos
  clear_value pos
  -- Both gap indices are valid positions of the sorted support.
  have hi_lt : i < (gapVector d).length := by
    by_contra hcon; rw [not_lt] at hcon
    rw [List.getI_eq_default _ hcon] at hi; simp only [Nat.default_eq_zero] at hi
    have := M.pos; omega
  have hj_lt : j < (gapVector d).length := by
    by_contra hcon; rw [not_lt] at hcon
    rw [List.getI_eq_default _ hcon] at hj; simp only [Nat.default_eq_zero] at hj
    have := M.pos; omega
  have hi_pos : i < pos.length := by rw [hpos, Finset.length_sort, ← gapVector_length]; exact hi_lt
  have hj_pos : j < pos.length := by rw [hpos, Finset.length_sort, ← gapVector_length]; exact hj_lt
  -- `pos`-stated helper facts.
  have hmono_pos : ∀ l₁ l₂, l₁ < l₂ → l₂ < pos.length → pos.getI l₁ < pos.getI l₂ := by
    intro l₁ l₂ h12 h2; rw [hpos] at h2 ⊢; exact support_sort_strictMono d l₁ l₂ h12 h2
  have hmem_pos : ∀ x, x ∈ d.support → ∃ l, l < pos.length ∧ pos.getI l = x := by
    intro x hx; rw [hpos]; exact mem_support_eq_getI d x hx
  -- Thresholds.
  set Pi := pos.getI i with hPi
  set Pj := pos.getI j with hPj
  have hPiPj : Pi < Pj := hmono_pos i j hij hj_pos
  -- gap formulas: gap i = Pi - (prev+1); gap j = Pj - Pos(j-1) - 1.
  have hgap_i : (gapVector d).getI i = Pi - (if i = 0 then 0 else pos.getI (i-1) + 1) := by
    rw [gapVector_getI _ _ hi_lt, ← hpos]
  have hgap_j : (gapVector d).getI j = Pj - (pos.getI (j-1) + 1) := by
    rw [gapVector_getI _ _ hj_lt, ← hpos, if_neg (by omega : j ≠ 0)]
  -- `M ≤ Pi`, and the gap-`i` run is `[Pi-M, Pi)`.
  have hMPi : (M : ℕ) ≤ Pi := le_trans hi (by rw [hgap_i]; exact Nat.sub_le _ _)
  -- `M ≤ Pj` and `Pi ≤ Pj - M` (the gap-`j` run lies above `Pi`).
  have hPi_le_runj : Pi ≤ Pj - (M : ℕ) := by
    have hj' := hj; rw [hgap_j] at hj'
    have hi_le : i ≤ j - 1 := by omega
    have hple : Pi ≤ pos.getI (j-1) := by
      rcases eq_or_lt_of_le hi_le with heq | hlt
      · rw [hPi, heq]
      · exact le_of_lt (hmono_pos i (j-1) hlt (by omega))
    omega
  have hMPj : (M : ℕ) ≤ Pj := by omega
  -- The gap-`i` zero run: positions `[Pi-M, Pi)` not in support.
  have hrun_i : ∀ x, Pi - (M : ℕ) ≤ x → x < Pi → d x = 0 := by
    intro x hx1 hx2
    by_contra hne
    obtain ⟨l, hl, hlx⟩ := hmem_pos x (Finsupp.mem_support_iff.mpr hne)
    have hxlt : pos.getI l < Pi := by rw [hlx]; exact hx2
    have hli : l < i := by
      rcases lt_trichotomy l i with h | h | h
      · exact h
      · subst h; exact absurd hxlt (by rw [hPi]; exact lt_irrefl _)
      · exact absurd (hmono_pos i l h hl) (by rw [← hPi]; omega)
    have hi0 : i ≠ 0 := by rintro rfl; exact absurd hli (Nat.not_lt_zero _)
    have hle : pos.getI l ≤ pos.getI (i-1) := by
      rcases eq_or_lt_of_le (show l ≤ i - 1 by omega) with heq | hlt
      · rw [heq]
      · exact le_of_lt (hmono_pos l (i-1) hlt (by omega))
    have hgap_lb : pos.getI (i-1) + 1 ≤ Pi - (M : ℕ) := by
      have h := hi; rw [hgap_i, if_neg hi0] at h; omega
    rw [hlx] at hle; omega
  -- The gap-`j` zero run: positions `[Pj-M, Pj)` not in support.
  have hrun_j : ∀ x, Pj - (M : ℕ) ≤ x → x < Pj → d x = 0 := by
    intro x hx1 hx2
    by_contra hne
    obtain ⟨l, hl, hlx⟩ := hmem_pos x (Finsupp.mem_support_iff.mpr hne)
    have hxlt : pos.getI l < Pj := by rw [hlx]; exact hx2
    have hlj : l < j := by
      rcases lt_trichotomy l j with h | h | h
      · exact h
      · subst h; exact absurd hxlt (by rw [hPj]; exact lt_irrefl _)
      · exact absurd (hmono_pos j l h hl) (by rw [← hPj]; omega)
    have hle : pos.getI l ≤ pos.getI (j-1) := by
      rcases eq_or_lt_of_le (show l ≤ j - 1 by omega) with heq | hlt
      · rw [heq]
      · exact le_of_lt (hmono_pos l (j-1) hlt (by omega))
    have hgap_lb : pos.getI (j-1) + 1 ≤ Pj - (M : ℕ) := by
      have h := hj; rw [hgap_j] at h; omega
    rw [hlx] at hle; omega
  -- `Pi`, `Pj` are genuine support positions (so their digits are `≥ 1`).
  have hPi_supp : Pi ∈ d.support := by
    rw [hPi, hpos]; exact support_sort_getI_mem d i (by rw [← hpos]; exact hi_pos)
  have hPj_supp : Pj ∈ d.support := by
    rw [hPj, hpos]; exact support_sort_getI_mem d j (by rw [← hpos]; exact hj_pos)
  -- The double-insertion reindexing and its value via `digitVal_double_split`.
  set ρ : ℕ → ℕ → ℕ → ℕ := fun s t x =>
    x + (if Pi ≤ x then s*(N:ℕ) else 0) + (if Pj ≤ x then t*(N:ℕ) else 0) with hρ
  -- Membership of the double insertion `mapDomain (ρ s t) d ∈ S`, with bookkeeping.
  have hmem_st : ∀ s t : ℕ,
      (1 / (a : ℚ)) * ((m : ℚ) -
        (Finsupp.mapDomain (ρ s t) d).sum fun x v => (v : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ))) ∈ S := by
    intro s t
    -- Step 1: insert s·N zeros at threshold Pi → d_s ∈ S.
    obtain ⟨hs_digit, hs_sum, hs_mem, hs_run_i⟩ :=
      insert_pow_mem hS Pi hMPi s d hd_digit hd_sum hq hrun_i
    set d_s := Finsupp.mapDomain (fun x => if x < Pi then x else x + s*(N:ℕ)) d with hds
    -- The gap-`j` run is preserved (shifted by s·N) in d_s: positions [Pj+sN-M, Pj+sN) are zero.
    have hs_run_j : ∀ x, (Pj + s*(N:ℕ)) - (M:ℕ) ≤ x → x < Pj + s*(N:ℕ) → d_s x = 0 := by
      intro x hx1 hx2
      -- x ≥ Pj+sN-M ≥ Pi+sN, so x is above the gap-`i` block; preimage `x - sN ∈ [Pj-M, Pj)`.
      have hx_above : Pi + s*(N:ℕ) ≤ x := by omega
      rw [hds, insertAt_above hx_above]
      exact hrun_j (x - s*(N:ℕ)) (by omega) (by omega)
    -- Step 2: insert t·N zeros at threshold Pj+sN on d_s → d_{s,t} ∈ S.
    obtain ⟨_, _, hst_mem, _⟩ :=
      insert_pow_mem hS (Pj + s*(N:ℕ)) (by omega) t d_s hs_digit hs_sum hs_mem hs_run_j
    -- The composed reindexing equals ρ s t.
    have hcomp : Finsupp.mapDomain
        (fun x => if x < Pj + s*(N:ℕ) then x else x + t*(N:ℕ)) d_s
        = Finsupp.mapDomain (ρ s t) d := by
      rw [hds, ← Finsupp.mapDomain_comp]
      congr 1
      funext x
      simp only [Function.comp, hρ]
      by_cases hxi : Pi ≤ x
      · by_cases hxj : Pj ≤ x
        · rw [if_neg (by omega : ¬ x < Pi), if_neg (by omega : ¬ x + s*(N:ℕ) < Pj + s*(N:ℕ)),
              if_pos hxi, if_pos hxj]
        · rw [if_neg (by omega : ¬ x < Pi), if_pos (by omega : x + s*(N:ℕ) < Pj + s*(N:ℕ)),
              if_pos hxi, if_neg hxj]; ring
      · rw [if_pos (by omega : x < Pi), if_pos (by omega : x < Pj + s*(N:ℕ)),
            if_neg hxi, if_neg (by omega : ¬ Pj ≤ x)]; ring
    rw [hcomp] at hst_mem
    exact hst_mem
  -- Analytic finish: extract infinitely many distinct accumulation points.
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp0 : (p : ℚ) ≠ 0 := by have := (Fact.out : Nat.Prime p).pos; exact_mod_cast this.ne'
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp2
  -- the three position blocks
  set A : ℚ := ∑ x ∈ d.support.filter (fun x => x < Pi),
    (d x : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ)) with hA
  set B : ℚ := ∑ x ∈ d.support.filter (fun x => Pi ≤ x ∧ x < Pj),
    (d x : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ)) with hB
  set C : ℚ := ∑ x ∈ d.support.filter (fun x => Pj ≤ x),
    (d x : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ)) with hC
  set r : ℚ := (p : ℚ) ^ (-(N : ℤ)) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, zpow_neg, inv_lt_one_iff₀]; right
    exact one_lt_zpow₀ hp1 (by exact_mod_cast N.pos)
  have hpow_conv : ∀ s : ℕ, (p:ℚ)^(-(s*(N:ℕ):ℤ)) = r^s := by
    intro s; rw [hr, ← zpow_natCast ((p:ℚ)^(-(N:ℤ))) s, ← zpow_mul]; congr 1; ring
  -- B > 0 and C > 0
  have hB_pos : 0 < B := by
    rw [hB]; apply Finset.sum_pos'
    · intro x hx; rw [Finset.mem_filter, Finsupp.mem_support_iff] at hx; positivity
    · refine ⟨Pi, ?_, ?_⟩
      · rw [Finset.mem_filter]; exact ⟨hPi_supp, le_rfl, hPiPj⟩
      · have hd : (0:ℚ) < (d Pi : ℚ) := by
          exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hPi_supp)
        positivity
  have hC_pos : 0 < C := by
    rw [hC]; apply Finset.sum_pos'
    · intro x hx; rw [Finset.mem_filter, Finsupp.mem_support_iff] at hx; positivity
    · refine ⟨Pj, ?_, ?_⟩
      · rw [Finset.mem_filter]; exact ⟨hPj_supp, le_rfl⟩
      · have hd : (0:ℚ) < (d Pj : ℚ) := by
          exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hPj_supp)
        positivity
  -- The value of v_{s,t} in closed form.
  set v : ℕ → ℕ → ℚ := fun s t =>
    (1 / (a : ℚ)) * ((m : ℚ) - (A + r^s * B + r^s * r^t * C)) with hv
  have hv_eq : ∀ s t, (1 / (a : ℚ)) * ((m : ℚ) -
      (Finsupp.mapDomain (ρ s t) d).sum fun x w => (w : ℚ) * (p : ℚ) ^ (-(x + 1 : ℤ)))
      = v s t := by
    intro s t
    rw [hρ, digitVal_double_split d Pi Pj s t (N:ℕ) (le_of_lt hPiPj)]
    rw [← hA, ← hB, ← hC, hv]
    rw [show (-((s*(N:ℕ):ℕ) + t*(N:ℕ):ℤ)) = (-(s*(N:ℕ):ℤ)) + (-(t*(N:ℕ):ℤ)) by push_cast; ring,
        zpow_add₀ hp0, hpow_conv s, hpow_conv t]
  have hv_mem : ∀ s t, v s t ∈ S := by
    intro s t; rw [← hv_eq s t]; exact hmem_st s t
  -- limit point of the t-sequence for fixed s
  set w : ℕ → ℚ := fun s => (1 / (a : ℚ)) * ((m : ℚ) - (A + r^s * B)) with hw
  have haQ : (0 : ℚ) < a := by exact_mod_cast a.pos
  have hw_tendsto : ∀ s, Filter.Tendsto (fun t => v s t) Filter.atTop (nhds (w s)) := by
    intro s
    have h0 : Filter.Tendsto (fun t : ℕ => r^t) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hr0) hr1
    have h1 : Filter.Tendsto (fun t : ℕ => r^s * r^t * C) Filter.atTop (nhds (r^s * 0 * C)) :=
      (Filter.Tendsto.mul (Filter.Tendsto.const_mul _ h0) tendsto_const_nhds)
    simp only [mul_zero, zero_mul] at h1
    have h2 : Filter.Tendsto (fun t : ℕ => A + r^s * B + r^s * r^t * C)
        Filter.atTop (nhds (A + r^s*B + 0)) := tendsto_const_nhds.add h1
    simp only [add_zero] at h2
    rw [hv, hw]
    exact (Filter.Tendsto.const_mul _ (tendsto_const_nhds.sub h2))
  have hv_ne : ∀ s t, v s t ≠ w s := by
    intro s t
    rw [hv, hw]
    have hpos : 0 < r^s * r^t * C := by positivity
    have : (1/(a:ℚ)) > 0 := by positivity
    intro heq
    have := mul_left_cancel₀ (ne_of_gt this) heq
    nlinarith [hpos]
  -- each w s is an accumulation point
  have hw_mem : ∀ s, w s ∈ derivedSet S := fun s =>
    mem_derivedSet_of_tendsto_seq (fun t => v s t) (fun t => hv_mem s t)
      (fun t => hv_ne s t) (hw_tendsto s)
  -- w injective ⇒ infinitely many accumulation points ⇒ contradiction with (S3).
  have hw_inj : Function.Injective w := by
    have hmono : StrictMono w := by
      intro s1 s2 hs
      rw [hw]
      have hrlt : r^s2 < r^s1 := pow_lt_pow_right_of_lt_one₀ hr0 hr1 hs
      have hia : (0:ℚ) < 1/a := by positivity
      have hBlt : r^s2 * B < r^s1 * B := by nlinarith
      nlinarith [mul_lt_mul_of_pos_left hBlt hia]
    exact hmono.injective
  have hsubset : Set.range w ⊆ derivedSet S := by
    rintro y ⟨s, rfl⟩; exact hw_mem s
  have hfin : (Set.range w).Finite := hS.2.2.subset hsubset
  exact (Set.infinite_range_of_injective hw_inj) hfin

/-- **Lemma `lem:27279`**: at most one gap coordinate is `≥ M`.

For every word occurring in `S` and every gap vector `g` of an element of `S` with that word, at
most one coordinate of `g` is `≥ M`.

*Proof sketch*: if `g_i ≥ M` and `g_j ≥ M` for `i < j`, then by `gap_add_mem`, the element with
gap vector `g + sN eᵢ + tN eⱼ` is in `S` for all `s, t ∈ ℕ`. For fixed `s`, the sequence
`{v_{s,t}}_t` has order type `ω`; and for `s < s'`, `v_{s,t} < v_{s',t'}` for all `t, t'`.
So the double-indexed sequence has order type `ω²` inside `S`, contradicting (S3). -/
theorem gap_at_most_one_ge_M {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {b : ℤ} {c : ℕ}
    {m : ℤ} {hm : -b ≤ m} {M N : ℕ+} {S : Set ℚ}
    (hS : IsAdmissible p a b c m hm M N S)
    (d : ℕ →₀ ℕ) (hd_digit : ∀ i, d i < p) (hd_sum : d.sum (fun _ v => v) ≤ c)
    (hq : (1 / (a : ℚ)) *
      ((m : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∈ S)
    (i j : ℕ) (hij : i ≠ j)
    (hi : M ≤ (gapVector d).getI i) :
    ¬ (M ≤ (gapVector d).getI j) := by
  intro hj
  -- both gaps are `≥ M`; apply the symmetric core with the smaller index first.
  rcases lt_or_gt_of_ne hij with h | h
  · exact two_gaps_ge_M_absurd hS d hd_digit hd_sum hq i j h hi hj
  · exact two_gaps_ge_M_absurd hS d hd_digit hd_sum hq j i h hj hi

/-- The set of `List ℕ` of length `≤ c` with all entries `< M` is finite (it embeds into the
length-`≤ c` lists over the finite type `Fin M`). -/
theorem finite_bounded_lists (c M : ℕ) :
    {l : List ℕ | l.length ≤ c ∧ ∀ x ∈ l, x < M}.Finite := by
  have hfin : {l : List (Fin M) | l.length ≤ c}.Finite := List.finite_length_le (Fin M) c
  apply Set.Finite.subset (hfin.image (fun l => l.map Fin.val))
  rintro l ⟨hlen, hbd⟩
  refine ⟨l.attachWith (fun x => x < M) hbd |>.map (fun x => (⟨x.1, x.2⟩ : Fin M)), ?_, ?_⟩
  · simp [List.length_map, hlen]
  · simp [List.map_map, List.map_attachWith]

/-- The set of finsupps with values `< p` and support contained in `range B` is finite (it embeds
into the finite function type `Fin B → Fin p`). Used to bound the finite "remainder" part of the
ray decomposition. -/
theorem finite_bounded_finsupp (B p : ℕ) (hp : 0 < p) :
    {d : ℕ →₀ ℕ | (∀ i, d i < p) ∧ d.support ⊆ Finset.range B}.Finite := by
  classical
  apply Set.Finite.of_finite_image
    (f := fun d : ℕ →₀ ℕ => (fun i : Fin B =>
      (if h : d i.val < p then (⟨d i.val, h⟩ : Fin p) else ⟨0, hp⟩)))
  · exact Set.toFinite _
  · intro d1 hd1 d2 hd2 heq
    simp only [Set.mem_setOf_eq] at hd1 hd2
    ext i
    by_cases hi : i < B
    · have hcong := congrFun heq ⟨i, hi⟩
      simp only [hd1.1 i, hd2.1 i, dif_pos] at hcong
      exact Fin.mk.injEq .. ▸ hcong
    · have h1 : d1 i = 0 := by
        by_contra hne
        have := hd1.2 (Finsupp.mem_support_iff.mpr hne); rw [Finset.mem_range] at this; omega
      have h2 : d2 i = 0 := by
        by_contra hne
        have := hd2.2 (Finsupp.mem_support_iff.mpr hne); rw [Finset.mem_range] at this; omega
      rw [h1, h2]

/-- The sum of the word equals the digit sum. -/
theorem word_sum (d : ℕ →₀ ℕ) : (word d).sum = d.sum (fun _ v => v) := by
  unfold word
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
  rfl

/-- Membership in the word: `v` occurs iff some support position carries digit value `v`. -/
theorem mem_word (d : ℕ →₀ ℕ) (v : ℕ) : v ∈ word d ↔ ∃ i ∈ d.support, d i = v := by
  unfold word
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by rwa [Finset.mem_sort] at hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by rwa [Finset.mem_sort], rfl⟩

/-- If two finsupps have the same word and one has all digits `< p`, so does the other. -/
theorem digit_lt_of_word_eq {p : ℕ} (hp : 0 < p) (d' d_word : ℕ →₀ ℕ)
    (hw : word d' = word d_word) (hbd : ∀ i, d_word i < p) : ∀ i, d' i < p := by
  intro i
  by_cases hi : i ∈ d'.support
  · have : d' i ∈ word d' := by rw [mem_word]; exact ⟨i, hi, rfl⟩
    rw [hw, mem_word] at this
    obtain ⟨j, _, hj⟩ := this
    rw [← hj]; exact hbd j
  · rw [Finsupp.notMem_support_iff.mp hi]; exact hp

/-- Equal words have equal digit sums. -/
theorem sum_eq_of_word_eq (d' d_word : ℕ →₀ ℕ) (hw : word d' = word d_word) :
    d'.sum (fun _ v => v) = d_word.sum (fun _ v => v) := by
  rw [← word_sum d', ← word_sum d_word, hw]

/-- **Lemma `lem:19048`**: decomposition of the gap set.

For any fixed word `d`, the gap set `G_d` (gap vectors of elements of `S` with word `d`)
decomposes as `G_d = W ∪ A₁ ∪ ⋯ ∪ Aᵣ`, where:
- `W` is a finite set of gap vectors (all coordinates `< M`);
- each `Aᵢ = { g + k · N · eᵤ | k : ℕ }` for some gap vector `v ∈ G_d` with exactly one
  coordinate `≥ M` (at index `u`) and the standard basis direction `eᵤ`.

Formulated here in terms of the gap-vector list: the gap set (viewed as `List ℕ` indexed over `ℕ`)
decomposes as a finite part plus finitely many arithmetic progressions, each in exactly one
coordinate. -/
theorem gapSet_decomp {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {b : ℤ} {c : ℕ}
    {m : ℤ} {hm : -b ≤ m} {M N : ℕ+} {S : Set ℚ}
    (hS : IsAdmissible p a b c m hm M N S)
    -- d_word encodes the fixed word
    (d_word : ℕ →₀ ℕ) (hd_digit : ∀ i, d_word i < p) (hd_sum : d_word.sum (fun _ v => v) ≤ c)
    -- G_d is the set of gap-vector lists of elements of S with word d_word
    (G_d : Set (List ℕ))
    (hG_d : ∀ g, g ∈ G_d ↔ ∃ (d' : ℕ →₀ ℕ),
      word d' = word d_word ∧ gapVector d' = g ∧
      (1 / (a : ℚ)) *
        ((m : ℚ) - d'.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∈ S) :
    ∃ (W : Finset (List ℕ)) (progressions : Finset (List ℕ × ℕ)),
      G_d = ↑W ∪ (⋃ p ∈ progressions, { g | ∃ k : ℕ,
        g = (p.1.set p.2 (p.1.getI p.2 + k * (N : ℕ))) }) ∧
      (∀ q ∈ progressions, q.1 ∈ G_d ∧ q.2 < q.1.length ∧ (M : ℕ) ≤ q.1.getI q.2) ∧
      (∀ g ∈ W, ∀ x ∈ g, x < (M : ℕ)) := by
  classical
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  -- Common length `t` of all gap vectors in `G_d`.
  set t := (word d_word).length with ht
  -- Every gap vector in `G_d` has length `t`.
  have hlen : ∀ g ∈ G_d, g.length = t := by
    intro g hg; rw [hG_d] at hg
    obtain ⟨d', hw, hgv, _⟩ := hg
    rw [← hgv, gapVector_length, ht, ← hw]
    unfold word; rw [List.length_map, Finset.length_sort]
  -- `t ≤ c`.
  have ht_le : t ≤ c := by rw [ht]; exact word_length_le hS d_word hd_sum
  -- The gap-closure bridge: a coordinate `≥ M` can be increased by `N` within `G_d`.
  have hclosure : ∀ g ∈ G_d, ∀ i, (M : ℕ) ≤ g.getI i → g.set i (g.getI i + (N : ℕ)) ∈ G_d := by
    intro g hg i hi
    rw [hG_d] at hg
    obtain ⟨d', hw, hgv, hmem⟩ := hg
    have hd'_digit : ∀ j, d' j < p := digit_lt_of_word_eq hp_pos d' d_word hw hd_digit
    have hd'_sum : (d'.sum fun _ v => v) ≤ c := by
      rw [sum_eq_of_word_eq d' d_word hw]; exact hd_sum
    -- apply gap_add_mem to d' (whose gap vector is g)
    have hi' : (M : ℕ) ≤ (gapVector d').getI i := by rw [hgv]; exact hi
    obtain ⟨d'', hw'', hgv'', hd''_digit, hd''_sum, hmem''⟩ :=
      gap_add_mem hS d' hd'_digit hd'_sum hmem i hi'
    rw [hG_d]
    refine ⟨d'', by rw [hw'', hw], ?_, hmem''⟩
    rw [hgv'', hgv]
  -- The "small" gap vectors: all coordinates `< M`. These form `W`.
  have hWfin : {g | g ∈ G_d ∧ ∀ x ∈ g, x < M}.Finite := by
    apply Set.Finite.subset (finite_bounded_lists c M)
    rintro g ⟨hg, hsmall⟩
    exact ⟨by rw [hlen g hg]; exact ht_le, hsmall⟩
  set W : Finset (List ℕ) := hWfin.toFinset with hWdef
  -- For `g ∈ G_d \ W`: there is a coordinate `≥ M`, and (by `gap_at_most_one_ge_M`) it is unique.
  -- Translate `gap_at_most_one_ge_M` to a statement about gap-vector lists in `G_d`.
  have huniq : ∀ g ∈ G_d, ∀ u u', (M:ℕ) ≤ g.getI u → (M:ℕ) ≤ g.getI u' → u = u' := by
    intro g hg u u' hu hu'
    by_contra hne
    rw [hG_d] at hg
    obtain ⟨d', hw, hgv, hmem⟩ := hg
    have hd'_digit : ∀ j, d' j < p := digit_lt_of_word_eq hp_pos d' d_word hw hd_digit
    have hd'_sum : (d'.sum fun _ v => v) ≤ c := by
      rw [sum_eq_of_word_eq d' d_word hw]; exact hd_sum
    exact gap_at_most_one_ge_M hS d' hd'_digit hd'_sum hmem u u' hne
      (by rw [hgv]; exact hu) (by rw [hgv]; exact hu')
  -- For a vector `g` with a long coordinate, the candidate `u`-values forming its bucket.
  -- The minimal such value is the base's coordinate.
  set bucketVals : List ℕ → ℕ → Set ℕ := fun g u =>
    {w | (M:ℕ) ≤ w ∧ w % (N:ℕ) = g.getI u % (N:ℕ) ∧ g.set u w ∈ G_d} with hbV
  -- base of a vector with long coordinate `u`: replace coordinate `u` by the minimal bucket value.
  set baseOf : List ℕ → ℕ → List ℕ := fun g u => g.set u (sInf (bucketVals g u)) with hbase
  -- Key facts about the bucket value `w₀ = sInf (bucketVals g u)` when `g ∈ G_d`, `u` long.
  -- (1) `g.getI u ∈ bucketVals g u` (so the bucket is nonempty).
  have hbV_self : ∀ g ∈ G_d, ∀ u, (M:ℕ) ≤ g.getI u → u < g.length →
      g.getI u ∈ bucketVals g u := by
    intro g hg u hu hulen
    refine ⟨hu, rfl, ?_⟩
    rw [List.getI_eq_getElem (l := g) hulen, List.set_getElem_self]; exact hg
  -- (2) the inf is in the bucket, and is `≤` any member.
  have hbV_inf_mem : ∀ g ∈ G_d, ∀ u, (M:ℕ) ≤ g.getI u → u < g.length →
      sInf (bucketVals g u) ∈ bucketVals g u :=
    fun g hg u hu hl => Nat.sInf_mem ⟨g.getI u, hbV_self g hg u hu hl⟩
  -- For `g ∈ G_d` not entirely small, choose its (unique) long coordinate.
  have hlong : ∀ g, g ∈ G_d → g ∉ W → ∃ u, u < g.length ∧ (M:ℕ) ≤ g.getI u := by
    intro g hg hgW
    by_contra hcon
    rw [not_exists] at hcon
    apply hgW
    rw [hWdef, Set.Finite.mem_toFinset]
    refine ⟨hg, ?_⟩
    intro x hx
    obtain ⟨u, hu, rfl⟩ := List.mem_iff_getElem.mp hx
    have hnotge : ¬ (M:ℕ) ≤ g.getI u := fun h => hcon u ⟨by simpa using hu, h⟩
    rw [List.getI_eq_getElem (l := g) (by simpa using hu)] at hnotge
    omega
  -- The progression generated by a base/index pair.
  set prog : List ℕ × ℕ → Set (List ℕ) :=
    fun q => {g | ∃ k : ℕ, g = q.1.set q.2 (q.1.getI q.2 + k * (N : ℕ))} with hprogdef
  -- Long-coordinate index of a vector (total; meaningful for non-small `g ∈ G_d`).
  set longIdx : List ℕ → ℕ :=
    fun g => if h : ∃ u, u < g.length ∧ (M:ℕ) ≤ g.getI u then h.choose else 0 with hlongIdx
  -- Base/index map: each non-small `g ∈ G_d` is sent to its base + long index.
  set bmap : List ℕ → List ℕ × ℕ := fun g => (baseOf g (longIdx g), longIdx g) with hbmap
  -- spec of `longIdx` on non-small members.
  have hlongIdx_spec : ∀ g, g ∈ G_d → g ∉ W →
      longIdx g < g.length ∧ (M:ℕ) ≤ g.getI (longIdx g) := by
    intro g hg hgW
    have hex := hlong g hg hgW
    have : longIdx g = hex.choose := by rw [hlongIdx]; exact dif_pos hex
    rw [this]; exact hex.choose_spec
  -- `longIdx` is THE unique long index.
  have hlongIdx_unique : ∀ g, g ∈ G_d → g ∉ W → ∀ u, (M:ℕ) ≤ g.getI u → u = longIdx g := by
    intro g hg hgW u hu
    exact huniq g hg u (longIdx g) hu (hlongIdx_spec g hg hgW).2
  -- The base of a non-small member is itself in `G_d`.
  have hbase_mem : ∀ g, g ∈ G_d → g ∉ W → baseOf g (longIdx g) ∈ G_d := by
    intro g hg hgW
    obtain ⟨hulen, hu⟩ := hlongIdx_spec g hg hgW
    have := hbV_inf_mem g hg (longIdx g) hu hulen
    rw [hbV] at this; exact this.2.2
  -- progression membership is closed in `G_d` (reverse iteration of `hclosure`).
  have hprog_iter : ∀ (base : List ℕ) (u : ℕ), base ∈ G_d → u < base.length →
      (M:ℕ) ≤ base.getI u → ∀ k, base.set u (base.getI u + k * (N:ℕ)) ∈ G_d := by
    intro base u hbase hulen hbu k
    induction k with
    | zero =>
      simp only [Nat.zero_mul, add_zero]
      rw [List.getI_eq_getElem (l := base) hulen, List.set_getElem_self]; exact hbase
    | succ n ih =>
      have hgi : (base.set u (base.getI u + n*(N:ℕ))).getI u = base.getI u + n*(N:ℕ) :=
        set_getI_self base u _ hulen
      have hcl := hclosure (base.set u (base.getI u + n*(N:ℕ))) ih u (by rw [hgi]; omega)
      rw [hgi, List.set_set] at hcl
      rw [show base.getI u + (n+1)*(N:ℕ) = base.getI u + n*(N:ℕ) + (N:ℕ) from by ring]
      exact hcl
  -- `g` lies on the progression of its own base/index pair.
  have hg_in_prog : ∀ g, g ∈ G_d → g ∉ W → g ∈ prog (bmap g) := by
    intro g hg hgW
    obtain ⟨hulen, hu⟩ := hlongIdx_spec g hg hgW
    set u := longIdx g with hu_def
    set w₀ := sInf (bucketVals g u) with hw0
    have hw0_mem := hbV_inf_mem g hg u hu hulen
    rw [hbV] at hw0_mem
    obtain ⟨hw0M, hw0res, hw0G⟩ := hw0_mem
    -- baseOf g u = g.set u w₀, with (baseOf g u).getI u = w₀
    have hbaseU : (baseOf g u).getI u = w₀ := by
      rw [hbase]; exact set_getI_self g u w₀ hulen
    -- w₀ ≤ g.getI u
    have hle : w₀ ≤ g.getI u := Nat.sInf_le (hbV_self g hg u hu hulen)
    -- ∃ k, g.getI u = w₀ + k*N
    obtain ⟨k, hk⟩ : ∃ k, g.getI u = w₀ + k * (N:ℕ) := by
      have hmod : w₀ ≡ g.getI u [MOD (N:ℕ)] := hw0res
      have hdvd : (N:ℕ) ∣ (g.getI u - w₀) := (Nat.modEq_iff_dvd' hle).mp hmod
      obtain ⟨k, hk⟩ := hdvd
      exact ⟨k, by rw [mul_comm]; omega⟩
    refine ⟨k, ?_⟩
    change g = (baseOf g u).set u ((baseOf g u).getI u + k * (N:ℕ))
    rw [hbaseU, hbase, List.set_set, ← hk, List.getI_eq_getElem (l := g) hulen,
        List.set_getElem_self]
  -- progression of a base/index pair (for non-small `g`) stays inside `G_d`.
  have hprog_sub : ∀ g, g ∈ G_d → g ∉ W → prog (bmap g) ⊆ G_d := by
    intro g hg hgW h hh
    obtain ⟨hulen, hu⟩ := hlongIdx_spec g hg hgW
    set u := longIdx g with hu_def
    obtain ⟨k, rfl⟩ := hh
    have hbm := hbase_mem g hg hgW
    have hblen : u < (baseOf g u).length := by rw [hbase, List.length_set]; exact hulen
    have hbu : (M:ℕ) ≤ (baseOf g u).getI u := by
      have := hbV_inf_mem g hg u hu hulen
      rw [hbV] at this
      rw [hbase, set_getI_self g u _ hulen]; exact this.1
    exact hprog_iter (bmap g).1 (bmap g).2 hbm hblen hbu k
  -- The set of base/index pairs of non-small members is finite.
  have hPfin : (bmap '' {g | g ∈ G_d ∧ g ∉ W}).Finite := by
    -- inject into (bounded lists) × indices × residues via
    -- `(base, u) ↦ (base.set u 0, u, base.getI u % N)`
    apply Set.Finite.of_finite_image
      (f := fun q : List ℕ × ℕ => (q.1.set q.2 0, q.2, q.1.getI q.2 % (N:ℕ)))
    · apply Set.Finite.subset
        ((finite_bounded_lists t M).prod ((Set.finite_Iio t).prod (Set.finite_Iio (N:ℕ))))
      rintro _ ⟨_, ⟨g, ⟨hg, hgW⟩, rfl⟩, rfl⟩
      obtain ⟨hulen, hu⟩ := hlongIdx_spec g hg hgW
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · -- length of base.set u 0 = t
        rw [hbmap]; simp only [hbase, List.length_set]; exact (hlen g hg).le
      · -- all entries < M
        intro x hx
        rw [hbmap] at hx; simp only [hbase] at hx
        -- x is an entry of (g.set u w₀).set u 0 = g.set u 0
        rw [List.set_set] at hx
        obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.mp hx
        rw [List.length_set] at hl
        by_cases hlu : longIdx g = l
        · rw [List.getElem_set, if_pos hlu]; exact M.pos
        · rw [List.getElem_set_ne hlu]
          -- coordinate l ≠ u is < M (else l would be a long index = u)
          by_contra hcon
          rw [not_lt] at hcon
          have : l = longIdx g := huniq g hg l (longIdx g)
            (by rw [List.getI_eq_getElem (l := g) (by simpa using hl)]; exact hcon) hu
          exact hlu this.symm
      · rw [hbmap]; simp only; exact (hlongIdx_spec g hg hgW).1.trans_eq (hlen g hg)
      · rw [hbmap]; simp only; exact Nat.mod_lt _ N.pos
    · -- injectivity on the image
      rintro _ ⟨g₁, ⟨hg₁, hg₁W⟩, rfl⟩ _ ⟨g₂, ⟨hg₂, hg₂W⟩, rfl⟩ heq
      simp only [hbmap, Prod.mk.injEq] at heq ⊢
      obtain ⟨hset0, hidx, hres⟩ := heq
      obtain ⟨hu1len, hu1ge⟩ := hlongIdx_spec g₁ hg₁ hg₁W
      obtain ⟨hu2len, hu2ge⟩ := hlongIdx_spec g₂ hg₂ hg₂W
      refine ⟨?_, hidx⟩
      -- rewrite everything to use the common index `longIdx g₁`
      rw [← hidx] at hset0 hres hu2len hu2ge
      simp only [hbase] at hset0 hres ⊢
      rw [List.set_set, List.set_set] at hset0
      have hsetw : ∀ w, g₁.set (longIdx g₁) w = g₂.set (longIdx g₁) w := by
        intro w
        rw [← List.set_set (a := (0:ℕ)) (l := g₁), ← List.set_set (a := (0:ℕ)) (l := g₂), hset0]
      -- residue equality from the bucket membership facts
      have hs1 := hbV_inf_mem g₁ hg₁ (longIdx g₁) hu1ge hu1len
      have hs2 := hbV_inf_mem g₂ hg₂ (longIdx g₁) hu2ge hu2len
      rw [hbV] at hs1 hs2
      rw [set_getI_self g₁ (longIdx g₁) _ hu1len,
          set_getI_self g₂ (longIdx g₁) _ hu2len] at hres
      have hres' : g₁.getI (longIdx g₁) % (N:ℕ) = g₂.getI (longIdx g₁) % (N:ℕ) := by
        rw [← hs1.2.1, hres, hs2.2.1]
      have hbveq : bucketVals g₁ (longIdx g₁) = bucketVals g₂ (longIdx g₁) := by
        rw [hbV]; ext w
        simp only [Set.mem_setOf_eq, hsetw w, hres']
      rw [hbveq, ← hidx]
      exact hsetw _
  -- Assemble `progressions` as a Finset and prove the set equality.
  refine ⟨W, hPfin.toFinset, ?_, ?_, ?_⟩
  · ext g
    simp only [Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset,
      Set.mem_iUnion]
    constructor
    · intro hg
      by_cases hgW : g ∈ W
      · left; exact hgW
      · right
        refine ⟨bmap g, ⟨g, ⟨hg, hgW⟩, rfl⟩, hg_in_prog g hg hgW⟩
    · rintro (hgW | ⟨q, hq, hgq⟩)
      · rw [hWdef, Set.Finite.mem_toFinset] at hgW; exact hgW.1
      · obtain ⟨g', ⟨hg', hg'W⟩, rfl⟩ := hq
        exact hprog_sub g' hg' hg'W hgq
  · -- Each progression's base lies in `G_d` with a (unique) long coordinate `≥ M`.
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨g', ⟨hg', hg'W⟩, rfl⟩ := hq
    obtain ⟨hulen, hu⟩ := hlongIdx_spec g' hg' hg'W
    refine ⟨hbase_mem g' hg' hg'W, ?_, ?_⟩
    · -- `longIdx g' < (baseOf g' (longIdx g')).length`
      rw [hbmap]; simp only [hbase, List.length_set]; exact hulen
    · -- `M ≤ (baseOf g' (longIdx g')).getI (longIdx g')`
      rw [hbmap]; simp only
      have := hbV_inf_mem g' hg' (longIdx g') hu hulen
      rw [hbV] at this
      rw [hbase, set_getI_self g' (longIdx g') _ hulen]; exact this.1
  · -- `W` consists of small gap-vectors (all entries `< M`), by definition of `W`.
    intro g hgW x hx
    rw [hWdef, Set.Finite.mem_toFinset] at hgW
    exact hgW.2 x hx

/-!
### Rays (`def:33761`) and the decomposition
-/

/-- **Definition `def:33761`**: a ray in `S`.

A **ray** in `S` is a subset of `S` of the form
```
{ (1/a)(m - 0.q₁⋯qₛ 0⋯0 qₛ₊₁⋯) | k = 0, 1, 2, … }
               ←kN zeros→
```
where the base element `q_base = (1/a)(m - 0.q₁⋯qₙ⋯) ∈ S` is a fixed element with exactly one
gap coordinate `≥ M` (at some unique index), and the `kN` zeros are inserted at that unique long
gap.

In terms of finsupps: a ray is determined by a base finsupp `d_base` and a shift position
`shift_pos : ℕ`, such that `R = { q_k | k : ℕ }` where `q_k` is the element encoded by shifting
all digits at index `≥ shift_pos` rightward by `kN` in `d_base`. -/
def IsRay (p : ℕ) [Fact (Nat.Prime p)] (a : ℕ+) (c : ℕ) (m : ℤ) (N : ℕ+)
    (S : Set ℚ) (R : Set ℚ) : Prop :=
  R ⊆ S ∧
  ∃ (d_base : ℕ →₀ ℕ) (shift_pos : ℕ),
    (∀ i, d_base i < p) ∧ (d_base.sum fun _ v => v) ≤ c ∧
    R = { q : ℚ | ∃ k : ℕ,
      q = (1 / (a : ℚ)) * ((m : ℚ) -
        (Finsupp.mapDomain
          (fun i => if i < shift_pos then i else i + k * (N : ℕ)) d_base).sum
          fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) }

/-- **Bridge: a long gap yields a ray.** If `d_base` encodes an element of `S` (digit/sum bounds)
and gap index `u` has gap `≥ M` (so positions `[pos_u - M, pos_u)` form a zero run, where
`pos_u = (sorted support).getI u`), then the set obtained by inserting `kN` zeros at the threshold
`pos_u` for `k = 0, 1, 2, …` is a ray in `S`. This is the geometric content of `def:33761`,
realised through the membership iterator `insert_pow_mem`. -/
theorem progression_isRay {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {b : ℤ} {c : ℕ}
    {m : ℤ} {hm : -b ≤ m} {M N : ℕ+} {S : Set ℚ}
    (hS : IsAdmissible p a b c m hm M N S)
    (d_base : ℕ →₀ ℕ) (hd_digit : ∀ i, d_base i < p) (hd_sum : d_base.sum (fun _ v => v) ≤ c)
    (hq : (1 / (a : ℚ)) *
      ((m : ℚ) - d_base.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∈ S)
    (u : ℕ) (hu : (M : ℕ) ≤ (gapVector d_base).getI u) :
    IsRay p a c m N S
      { q : ℚ | ∃ k : ℕ, q = (1 / (a : ℚ)) * ((m : ℚ) -
        (Finsupp.mapDomain
          (fun i => if i < (d_base.support.sort (· ≤ ·)).getI u then i else i + k * (N : ℕ))
          d_base).sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) } := by
  classical
  set pos := d_base.support.sort (· ≤ ·) with hpos
  -- `u` is a valid gap index (else `getI u = 0 < M`).
  have hu_lt : u < (gapVector d_base).length := by
    by_contra hcon; rw [not_lt] at hcon
    rw [List.getI_eq_default _ hcon] at hu; simp only [Nat.default_eq_zero] at hu
    have := M.pos; omega
  have hu_pos : u < pos.length := by rw [hpos, Finset.length_sort, ← gapVector_length]; exact hu_lt
  -- `pos`-stated helper facts.
  have hmono_pos : ∀ l₁ l₂, l₁ < l₂ → l₂ < pos.length → pos.getI l₁ < pos.getI l₂ := by
    intro l₁ l₂ h12 h2; rw [hpos] at h2 ⊢; exact support_sort_strictMono d_base l₁ l₂ h12 h2
  have hmem_pos : ∀ x, x ∈ d_base.support → ∃ l, l < pos.length ∧ pos.getI l = x := by
    intro x hx; rw [hpos]; exact mem_support_eq_getI d_base x hx
  set Pu := pos.getI u with hPu
  -- `M ≤ Pu` and the gap-`u` zero run `[Pu - M, Pu)`.
  have hgap_u : (gapVector d_base).getI u = Pu - (if u = 0 then 0 else pos.getI (u-1) + 1) := by
    rw [gapVector_getI _ _ hu_lt, ← hpos]
  have hMPu : (M : ℕ) ≤ Pu := le_trans hu (by rw [hgap_u]; exact Nat.sub_le _ _)
  have hrun : ∀ x, Pu - (M : ℕ) ≤ x → x < Pu → d_base x = 0 := by
    intro x hx1 hx2
    by_contra hne
    obtain ⟨l, hl, hlx⟩ := hmem_pos x (Finsupp.mem_support_iff.mpr hne)
    have hxlt : pos.getI l < Pu := by rw [hlx]; exact hx2
    have hlu : l < u := by
      rcases lt_trichotomy l u with h | h | h
      · exact h
      · subst h; exact absurd hxlt (by rw [hPu]; exact lt_irrefl _)
      · exact absurd (hmono_pos u l h hl) (by rw [← hPu]; omega)
    have hu0 : u ≠ 0 := by rintro rfl; exact absurd hlu (Nat.not_lt_zero _)
    have hle : pos.getI l ≤ pos.getI (u-1) := by
      rcases eq_or_lt_of_le (show l ≤ u - 1 by omega) with heq | hlt
      · rw [heq]
      · exact le_of_lt (hmono_pos l (u-1) hlt (by omega))
    have hgap_lb : pos.getI (u-1) + 1 ≤ Pu - (M : ℕ) := by
      have h := hu; rw [hgap_u, if_neg hu0] at h; omega
    rw [hlx] at hle; omega
  refine ⟨?_, d_base, Pu, hd_digit, hd_sum, rfl⟩
  -- `R ⊆ S`: each element is `enc (insert kN zeros at threshold Pu)`, in `S` by `insert_pow_mem`.
  rintro q ⟨k, rfl⟩
  obtain ⟨_, _, hmemk, _⟩ := insert_pow_mem hS Pu hMPu k d_base hd_digit hd_sum hq hrun
  exact hmemk

/-- **Reconstruction infrastructure (1/3): `gapOfList` is injective on strictly increasing lists.**
If two lists `pos₁, pos₂` (whose `getI` is strictly monotone — the case for sorted supports) have
the same `gapOfList`, they are equal. The sorted support is recovered from its gap vector by the
prefix-sum formula `posⱼ = (∑_{i≤j} gᵢ) + j`. -/
theorem sortedSupportList_inj {pos₁ pos₂ : List ℕ}
    (hmono₁ : ∀ j₁ j₂, j₁ < j₂ → j₂ < pos₁.length → pos₁.getI j₁ < pos₁.getI j₂)
    (hmono₂ : ∀ j₁ j₂, j₁ < j₂ → j₂ < pos₂.length → pos₂.getI j₁ < pos₂.getI j₂)
    (h : gapOfList pos₁ = gapOfList pos₂) : pos₁ = pos₂ := by
  have hlen : pos₁.length = pos₂.length := by
    rw [← gapOfList_length pos₁, ← gapOfList_length pos₂, h]
  have hgetI : ∀ j, j < pos₁.length → pos₁.getI j = pos₂.getI j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j IH =>
      intro hj1
      have hj2 : j < pos₂.length := hlen ▸ hj1
      have e : (gapOfList pos₁).getI j = (gapOfList pos₂).getI j := by rw [h]
      rw [gapOfList_getI pos₁ j hj1, gapOfList_getI pos₂ j hj2] at e
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0; simpa using e
      · have hjne : j ≠ 0 := by omega
        rw [if_neg hjne, if_neg hjne] at e
        have hprev : pos₁.getI (j - 1) = pos₂.getI (j - 1) :=
          IH (j - 1) (by omega) (by omega)
        have hs1 : pos₁.getI (j - 1) < pos₁.getI j := hmono₁ (j - 1) j (by omega) hj1
        have hs2 : pos₂.getI (j - 1) < pos₂.getI j := hmono₂ (j - 1) j (by omega) hj2
        omega
  apply List.ext_getElem hlen
  intro i h1 h2
  rw [← List.getI_eq_getElem pos₁ h1, ← List.getI_eq_getElem pos₂ h2]
  exact hgetI i h1

/-- **Reconstruction infrastructure (2/3): a finsupp is determined by its word and gap vector.**
The gap vector fixes the sorted support (hence the support); the word then fixes the digit value at
each support position. This is the key fact that lets the gap-vector decomposition `gapSet_decomp`
be transported back to a decomposition of `enc`-values. -/
theorem finsupp_eq_of_word_gapVector_eq {d₁ d₂ : ℕ →₀ ℕ}
    (hw : word d₁ = word d₂) (hgv : gapVector d₁ = gapVector d₂) : d₁ = d₂ := by
  classical
  have hpos : d₁.support.sort (· ≤ ·) = d₂.support.sort (· ≤ ·) := by
    apply sortedSupportList_inj (support_sort_strictMono d₁) (support_sort_strictMono d₂)
    rw [← gapVector_eq_gapOfList, ← gapVector_eq_gapOfList]; exact hgv
  have hsupp : d₁.support = d₂.support := by
    have h := congrArg List.toFinset hpos
    rwa [Finset.sort_toFinset, Finset.sort_toFinset] at h
  apply Finsupp.ext
  intro x
  by_cases hx : x ∈ d₁.support
  · obtain ⟨l, hl, hlx⟩ := mem_support_eq_getI d₁ x hx
    have hl2 : l < (d₂.support.sort (· ≤ ·)).length := by rw [← hpos]; exact hl
    have e1 : (word d₁).getI l = d₁ x := by
      rw [word, map_getI _ _ _ hl, hlx]
    have e2 : (word d₂).getI l = d₂ x := by
      rw [word, map_getI _ _ _ hl2]
      rw [← hpos, hlx]
    rw [← e1, hw, e2]
  · have hx2 : x ∉ d₂.support := by rwa [hsupp] at hx
    rw [Finsupp.notMem_support_iff.mp hx, Finsupp.notMem_support_iff.mp hx2]


/-- **Reconstruction infrastructure (3/3): the gap vector of an inserted finsupp.**
Inserting `k·N'` zeros at the threshold `pos_u = (sorted support).getI u` (via the strictly monotone
reindexing) changes the gap vector by exactly `set u (· + k·N')` at the long-gap coordinate `u`. -/
theorem gapVector_mapDomain_insert (d_base : ℕ →₀ ℕ) (u k N' : ℕ)
    (hu : u < (gapVector d_base).length) :
    gapVector (Finsupp.mapDomain
        (fun i => if i < (d_base.support.sort (· ≤ ·)).getI u then i else i + k * N') d_base)
      = (gapVector d_base).set u ((gapVector d_base).getI u + k * N') := by
  have hu' : u < (d_base.support.sort (· ≤ ·)).length := by
    rwa [gapVector_eq_gapOfList, gapOfList_length] at hu
  rw [gapVector_eq_gapOfList,
    support_sort_mapDomain d_base (strictMono_insertZeros _ _),
    gapOfList_map_insertZeros _ (support_sort_strictMono d_base) u (k * N') hu',
    ← gapVector_eq_gapOfList]

/-- **Corollary `coro:8081`**: `S` is a union of a finite set and finitely many rays.

*Proof sketch*: By `word_length_le`, only finitely many words occur in `S`. For each word `d`,
apply `gapSet_decomp` to write `G_d = W ∪ A₁ ∪ ⋯ ∪ Aᵣ`. The finite parts `W` give a finite set;
each progression `Aᵢ` is a ray (`progression_isRay`). Sum over the finitely many words. -/
theorem eq_finite_union_rays {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {b : ℤ} {c : ℕ}
    {m : ℤ} {hm : -b ≤ m} {M N : ℕ+} {S : Set ℚ}
    (hS : IsAdmissible p a b c m hm M N S) :
    ∃ (E : Finset ℚ) (rays : Finset (Set ℚ)),
      (∀ R ∈ rays, IsRay p a c m N S R) ∧
      S = ↑E ∪ rays.sup id := by
  classical
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  -- `enc d` is the rational encoded by the digit finsupp `d`.
  -- We keep the literal everywhere so the existing lemmas (`digitVal_split`, `progression_isRay`,
  -- …) keyed on this exact term continue to fire.
  -- `occ w`: word `w` occurs as the word of a (bounded) element of `S`.
  set occ : List ℕ → Prop := fun w => ∃ d : ℕ →₀ ℕ, (∀ i, d i < p) ∧ (d.sum fun _ v => v) ≤ c ∧
    word d = w ∧ (1 / (a : ℚ)) * ((m : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∈ S
    with hocc_def
  -- `Gw w`: the gap set of elements of `S` whose word is `w`.
  set Gw : List ℕ → Set (List ℕ) := fun w => {g | ∃ d' : ℕ →₀ ℕ,
    word d' = w ∧ gapVector d' = g ∧
    (1 / (a : ℚ)) * ((m : ℚ) - d'.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∈ S}
    with hGw_def
  -- Per word, `gapSet_decomp` (strengthened) yields the finite/progression split, with
  -- each progression's base exposed in `Gw w` with a long coordinate.
  have key : ∀ w, ∃ (Ww : Finset (List ℕ)) (progsw : Finset (List ℕ × ℕ)),
      occ w → (Gw w = ↑Ww ∪ (⋃ q ∈ progsw, {g | ∃ k : ℕ,
          g = q.1.set q.2 (q.1.getI q.2 + k * (N : ℕ))}) ∧
        (∀ q ∈ progsw, q.1 ∈ Gw w ∧ q.2 < q.1.length ∧ (M : ℕ) ≤ q.1.getI q.2) ∧
        (∀ g ∈ Ww, ∀ x ∈ g, x < (M : ℕ))) := by
    intro w
    by_cases h : occ w
    · obtain ⟨dbnd, hdig, hsum, hword, _hmem⟩ := h
      obtain ⟨Ww, progsw, hd, hpr, hsm⟩ :=
        gapSet_decomp hS dbnd hdig hsum (Gw w) (by
          intro g
          rw [hGw_def]
          simp only [Set.mem_setOf_eq, hword])
      exact ⟨Ww, progsw, fun _ => ⟨hd, hpr, hsm⟩⟩
    · exact ⟨∅, ∅, fun hcon => absurd hcon h⟩
  choose Ww progsw hkey using key
  -- A bounded witness finsupp for each occurring word.
  set dW : List ℕ → (ℕ →₀ ℕ) := fun w => if h : occ w then h.choose else 0 with hdW
  -- A realization finsupp for each gap-vector list in `Gw w`.
  set realize : List ℕ → List ℕ → (ℕ →₀ ℕ) :=
    fun w g => if h : g ∈ Gw w then h.choose else 0 with hrealize
  -- Spec of the realization on `Gw`-members.
  have realize_spec : ∀ w g, g ∈ Gw w →
      word (realize w g) = w ∧ gapVector (realize w g) = g ∧
      (1 / (a : ℚ)) * ((m : ℚ) -
        (realize w g).sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∈ S := by
    intro w g hg
    rw [hrealize]; simp only [dif_pos hg]
    exact hg.choose_spec
  -- Spec of the bounded word-witness on occurring words.
  have dW_spec : ∀ w, occ w → (∀ i, (dW w) i < p) ∧ ((dW w).sum fun _ v => v) ≤ c ∧
      word (dW w) = w := by
    intro w hw
    rw [hdW]; simp only [dif_pos hw]
    obtain ⟨hdig, hsum, hword, _⟩ := hw.choose_spec
    exact ⟨hdig, hsum, hword⟩
  -- A realization of a `Gw w`-member is digit/sum-bounded (transferred from the word-witness).
  have realize_bounded : ∀ w, occ w → ∀ g, g ∈ Gw w →
      (∀ i, (realize w g) i < p) ∧ ((realize w g).sum fun _ v => v) ≤ c := by
    intro w hw g hg
    obtain ⟨hword, _, _⟩ := realize_spec w g hg
    obtain ⟨hdigW, hsumW, hwordW⟩ := dW_spec w hw
    have hwe : word (realize w g) = word (dW w) := by rw [hword, hwordW]
    exact ⟨digit_lt_of_word_eq hp_pos (realize w g) (dW w) hwe hdigW,
      by rw [sum_eq_of_word_eq (realize w g) (dW w) hwe]; exact hsumW⟩
  -- The (finite) set of occurring words.
  have hWordsFin : {w : List ℕ | occ w}.Finite := by
    apply Set.Finite.subset (finite_bounded_lists c p)
    rintro w ⟨d, hdig, hsum, hword, _⟩
    refine ⟨?_, ?_⟩
    · rw [← hword]; exact word_length_le hS d hsum
    · intro x hx
      rw [← hword, mem_word] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact hdig i
  set Words : Finset (List ℕ) := hWordsFin.toFinset with hWords
  -- The ray attached to a progression `q` in word `w`.
  set rayOf : List ℕ → (List ℕ × ℕ) → Set ℚ := fun w q =>
    { x : ℚ | ∃ k : ℕ, x = (1 / (a : ℚ)) * ((m : ℚ) -
      (Finsupp.mapDomain
        (fun i => if i < ((realize w q.1).support.sort (· ≤ ·)).getI q.2 then i
          else i + k * (N : ℕ))
        (realize w q.1)).sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) } with hrayOf
  -- The finite set of rays and the finite remainder set.
  set rays : Finset (Set ℚ) := Words.biUnion (fun w => (progsw w).image (rayOf w)) with hrays
  set E : Finset ℚ := Words.biUnion (fun w => (Ww w).image
    (fun g => (1 / (a : ℚ)) * ((m : ℚ) -
      (realize w g).sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))))) with hE
  -- Every member of `rays` is a ray. Proven once; reused for both the conclusion and `⊇`.
  have hrays_isRay : ∀ R ∈ rays, IsRay p a c m N S R := by
    intro R hR
    rw [hrays, Finset.mem_biUnion] at hR
    obtain ⟨w, hwWords, hRimg⟩ := hR
    rw [Finset.mem_image] at hRimg
    obtain ⟨q, hqprog, rfl⟩ := hRimg
    rw [hWords, Set.Finite.mem_toFinset] at hwWords
    have hw : occ w := hwWords
    obtain ⟨_hd, hpr, _hsm⟩ := hkey w hw
    obtain ⟨hq1G, _hq2len, hq2M⟩ := hpr q hqprog
    -- `realize w q.1` realizes the gap-vector list `q.1`.
    obtain ⟨_hword, hgv, hmem⟩ := realize_spec w q.1 hq1G
    obtain ⟨hdig, hsum⟩ := realize_bounded w hw q.1 hq1G
    -- The long-coordinate bound transfers to `realize w q.1`.
    have hu : (M : ℕ) ≤ (gapVector (realize w q.1)).getI q.2 := by rw [hgv]; exact hq2M
    -- `rayOf w q` is exactly the ray produced by `progression_isRay`.
    have := progression_isRay hS (realize w q.1) hdig hsum hmem q.2 hu
    rw [hrayOf]
    exact this
  refine ⟨E, rays, hrays_isRay, ?_⟩
  -- `S = ↑E ∪ rays.sup id`.
  rw [Finset.sup_set_eq_biUnion]
  apply Set.eq_of_subset_of_subset
  · -- `S ⊆ ↑E ∪ ⋃ rays`.
    intro y hy
    -- (S1): `y ∈ Sabc_m`, so `y = enc d` for a bounded finsupp `d`.
    obtain ⟨d, hdig, hsum, hyd⟩ := hS.1 hy
    -- The word `w := word d` occurs.
    set w := word d with hw_def
    have hw : occ w := ⟨d, hdig, hsum, rfl, hyd ▸ hy⟩
    -- `gapVector d ∈ Gw w`.
    have hgd : gapVector d ∈ Gw w := ⟨d, rfl, rfl, hyd ▸ hy⟩
    obtain ⟨hd_decomp, hpr, _hsm⟩ := hkey w hw
    -- Split `gapVector d ∈ Gw w` into the finite part or a progression.
    rw [hd_decomp] at hgd
    rcases hgd with hgWw | hgprog
    · -- Finite part: `y ∈ E` via reconstruction `realize w (gapVector d) = d`.
      left
      rw [hE, Finset.mem_coe, Finset.mem_biUnion]
      refine ⟨w, by rw [hWords, Set.Finite.mem_toFinset]; exact hw, ?_⟩
      rw [Finset.mem_image]
      refine ⟨gapVector d, hgWw, ?_⟩
      -- `realize w (gapVector d) = d`, so the `enc`-values agree.
      have hgG : gapVector d ∈ Gw w := by rw [hd_decomp]; left; exact hgWw
      obtain ⟨hrword, hrgv, _⟩ := realize_spec w (gapVector d) hgG
      have hreq : realize w (gapVector d) = d :=
        finsupp_eq_of_word_gapVector_eq (by rw [hrword]) hrgv
      rw [hreq, ← hyd]
    · -- Progression part: `y ∈ rayOf w q ∈ rays`.
      right
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hgprog
      obtain ⟨q, hqmem, k, hgv_eq⟩ := hgprog
      obtain ⟨hq1G, hq2len, _hq2M⟩ := hpr q hqmem
      set base := realize w q.1 with hbase_def
      obtain ⟨hbword, hbgv, _hbmem⟩ := realize_spec w q.1 hq1G
      -- `d'`: insert `k·N` zeros at the threshold `base.sort.getI q.2` of `base`.
      set d' := Finsupp.mapDomain
        (fun i => if i < (base.support.sort (· ≤ ·)).getI q.2 then i else i + k * (N : ℕ)) base
        with hd'_def
      -- `d' = d` by reconstruction (word + gap vector agree).
      have hword' : word d' = word d := by
        rw [hd'_def, word_mapDomain_strictMono base (strictMono_insertZeros _ _), hbword, ← hw_def]
      have hgv' : gapVector d' = gapVector d := by
        rw [hd'_def,
          gapVector_mapDomain_insert base q.2 k (N : ℕ) (by rw [hbgv]; exact hq2len),
          hbgv, ← hgv_eq]
      have hd'eq : d' = d := finsupp_eq_of_word_gapVector_eq hword' hgv'
      -- `y = enc d = enc d'`, so `y ∈ rayOf w q`, and `rayOf w q ∈ rays`.
      simp only [Set.mem_iUnion, id_eq, exists_prop]
      refine ⟨rayOf w q, ?_, ?_⟩
      · -- `rayOf w q ∈ rays`.
        rw [hrays, Finset.mem_biUnion]
        refine ⟨w, by rw [hWords, Set.Finite.mem_toFinset]; exact hw, ?_⟩
        rw [Finset.mem_image]
        exact ⟨q, hqmem, rfl⟩
      · -- `y ∈ rayOf w q`.
        refine ⟨k, ?_⟩
        rw [hyd, ← hd'eq]
  · -- `↑E ∪ ⋃ rays ⊆ S`.
    rintro y (hyE | hyR)
    · -- `y ∈ E`: `y = enc (realize w g)` for some `g ∈ Ww w ⊆ Gw w`, in `S` by `realize_spec`.
      rw [hE, Finset.mem_coe, Finset.mem_biUnion] at hyE
      obtain ⟨w, hwWords, hyimg⟩ := hyE
      rw [Finset.mem_image] at hyimg
      obtain ⟨g, hgWw, rfl⟩ := hyimg
      rw [hWords, Set.Finite.mem_toFinset] at hwWords
      have hw : occ w := hwWords
      obtain ⟨hd, _hpr, _hsm⟩ := hkey w hw
      -- `g ∈ Ww w ⊆ Gw w`.
      have hgG : g ∈ Gw w := by
        rw [hd]; left; exact hgWw
      exact (realize_spec w g hgG).2.2
    · -- `y` lies in some ray `R ∈ rays`; rays are `⊆ S`.
      simp only [Set.mem_iUnion, id_eq] at hyR
      obtain ⟨R, hRrays, hyR⟩ := hyR
      exact (hrays_isRay R hRrays).1 hyR

/-- **Lemma `lem:59667`**: two rays are comparable or have finite intersection.

For two rays `R₁, R₂` in `S`, exactly one holds:
1. `R₁ ⊆ R₂` or `R₂ ⊆ R₁`; or
2. `R₁ ∩ R₂` is finite.

*Proof sketch*: Write `Rₗ = { (1/a)(m - αₗ - λₗ p^{-Nk}) | k ≥ 0 }`. If `α₁ = α₂`, comparing
any element in `R₁ ∩ R₂` yields `R₁ ⊆ R₂`. If `α₁ ≠ α₂` but `R₁ ∩ R₂` is infinite, it
converges to both limit points, forcing `α₁ = α₂` — contradiction. -/
theorem rays_sub_or_finite_inter {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {c : ℕ} {m : ℤ}
    {N : ℕ+} {S : Set ℚ}
    {R₁ R₂ : Set ℚ}
    (h₁ : IsRay p a c m N S R₁) (h₂ : IsRay p a c m N S R₂) :
    R₁ ⊆ R₂ ∨ R₂ ⊆ R₁ ∨ (R₁ ∩ R₂).Finite := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp0 : (p : ℚ) ≠ 0 := by have := (Fact.out : Nat.Prime p).pos; exact_mod_cast this.ne'
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp2
  set r : ℚ := (p : ℚ) ^ (-(N : ℤ)) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, zpow_neg, inv_lt_one_iff₀]; right
    exact one_lt_zpow₀ hp1 (by exact_mod_cast N.pos)
  -- Unpack the two rays into the affine-geometric form `R_l = { α_l - λ_l r^k }`.
  obtain ⟨_, d₁, sp₁, _, _, hR₁⟩ := h₁
  obtain ⟨_, d₂, sp₂, _, _, hR₂⟩ := h₂
  -- head/tail decomposition of each ray.
  set head₁ : ℚ := ∑ i ∈ d₁.support.filter (fun i => i < sp₁),
    (d₁ i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) with hhead₁
  set tail₁ : ℚ := ∑ i ∈ d₁.support.filter (fun i => sp₁ ≤ i),
    (d₁ i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) with htail₁
  set head₂ : ℚ := ∑ i ∈ d₂.support.filter (fun i => i < sp₂),
    (d₂ i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) with hhead₂
  set tail₂ : ℚ := ∑ i ∈ d₂.support.filter (fun i => sp₂ ≤ i),
    (d₂ i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) with htail₂
  set α₁ : ℚ := (1 / (a : ℚ)) * ((m : ℚ) - head₁) with hα₁
  set α₂ : ℚ := (1 / (a : ℚ)) * ((m : ℚ) - head₂) with hα₂
  set lam₁ : ℚ := (1 / (a : ℚ)) * tail₁ with hlam₁
  set lam₂ : ℚ := (1 / (a : ℚ)) * tail₂ with hlam₂
  have hpow_conv : ∀ k : ℕ, (p:ℚ) ^ (-(↑(k * (N:ℕ)) : ℤ)) = r ^ k := by
    intro k; rw [hr, ← zpow_natCast ((p:ℚ)^(-(N:ℤ))) k, ← zpow_mul]; congr 1; push_cast; ring
  -- Membership in `R_l` reduces to `∃ k, q = α_l - lam_l * r^k`.
  have hmem₁ : ∀ q, q ∈ R₁ ↔ ∃ k : ℕ, q = α₁ - lam₁ * r ^ k := by
    intro q; rw [hR₁]; constructor
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      rw [digitVal_split d₁ sp₁ (k * (N:ℕ)), ← hhead₁, ← htail₁, hα₁, hlam₁, hpow_conv k]
      ring
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      rw [digitVal_split d₁ sp₁ (k * (N:ℕ)), ← hhead₁, ← htail₁, hα₁, hlam₁, hpow_conv k]
      ring
  have hmem₂ : ∀ q, q ∈ R₂ ↔ ∃ k : ℕ, q = α₂ - lam₂ * r ^ k := by
    intro q; rw [hR₂]; constructor
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      rw [digitVal_split d₂ sp₂ (k * (N:ℕ)), ← hhead₂, ← htail₂, hα₂, hlam₂, hpow_conv k]
      ring
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      rw [digitVal_split d₂ sp₂ (k * (N:ℕ)), ← hhead₂, ← htail₂, hα₂, hlam₂, hpow_conv k]
      ring
  -- `lam_l ≥ 0` (tails are nonnegative).
  have htail₁_nonneg : 0 ≤ tail₁ := by
    rw [htail₁]; apply Finset.sum_nonneg; intro i _; positivity
  have htail₂_nonneg : 0 ≤ tail₂ := by
    rw [htail₂]; apply Finset.sum_nonneg; intro i _; positivity
  have haQ : (0 : ℚ) < a := by exact_mod_cast a.pos
  have hlam₁_nonneg : 0 ≤ lam₁ := by rw [hlam₁]; positivity
  have hlam₂_nonneg : 0 ≤ lam₂ := by rw [hlam₂]; positivity
  -- Geometric fact: `{k | ε ≤ r^k}` is finite for `ε > 0`.
  have hfin_pow : ∀ ε : ℚ, 0 < ε → {k : ℕ | ε ≤ r ^ k}.Finite := by
    intro ε hε
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε hr1
    apply Set.Finite.subset (Set.finite_Iio K)
    intro k hk
    simp only [Set.mem_setOf_eq] at hk
    simp only [Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    have : r ^ k ≤ r ^ K := pow_le_pow_of_le_one (le_of_lt hr0) (le_of_lt hr1) hcon
    linarith
  -- Core: if `α_lo < α_hi` and `lam_hi > 0`, then `R_lo ∩ R_hi` is finite.
  -- Every `q ∈ R_lo` has `q ≤ α_lo < α_hi`; for `q ∈ R_hi`, `lam_hi r^k = α_hi - q ≥ α_hi - α_lo`,
  -- so `r^k` is bounded below, giving finitely many `k`, and `q ↦ k` is injective.
  have hfin_of_lt : ∀ (αlo αhi lamlo lamhi : ℚ) (Rlo Rhi : Set ℚ),
      0 ≤ lamlo → 0 < lamhi → αlo < αhi →
      (∀ q, q ∈ Rlo ↔ ∃ k : ℕ, q = αlo - lamlo * r ^ k) →
      (∀ q, q ∈ Rhi ↔ ∃ k : ℕ, q = αhi - lamhi * r ^ k) →
      (Rlo ∩ Rhi).Finite := by
    intro αlo αhi lamlo lamhi Rlo Rhi hlamlo hlamhi hlt hRlo hRhi
    set ε : ℚ := (αhi - αlo) / lamhi with hε
    have hεpos : 0 < ε := by rw [hε]; apply div_pos (by linarith) hlamhi
    -- the map `q ↦ k_hi(q)`, well-defined on `R_hi` by choice, lands in `{k | ε ≤ r^k}`.
    -- We bound the intersection via the injective map `q ↦ (αhi - q)/lamhi`'s exponent.
    apply Set.Finite.subset (Set.Finite.image (fun k => αhi - lamhi * r ^ k) (hfin_pow ε hεpos))
    rintro q ⟨hqlo, hqhi⟩
    obtain ⟨klo, hklo⟩ := (hRlo q).mp hqlo
    obtain ⟨khi, hkhi⟩ := (hRhi q).mp hqhi
    -- q ≤ αlo < αhi, and lamhi * r^khi = αhi - q ≥ αhi - αlo, so ε ≤ r^khi.
    have hq_le : q ≤ αlo := by
      rw [hklo]; have : 0 ≤ lamlo * r ^ klo := by positivity
      linarith
    have hbound : ε ≤ r ^ khi := by
      rw [hε, div_le_iff₀ hlamhi]
      have : lamhi * r ^ khi = αhi - q := by rw [hkhi]; ring
      rw [mul_comm]; rw [this]; linarith
    exact ⟨khi, hbound, hkhi.symm⟩
  -- Case analysis on the limit points and the slopes.
  rcases eq_or_ne lam₁ 0 with hl1 | hl1
  · -- R₁ is the singleton {α₁}; intersection ⊆ {α₁} is finite.
    right; right
    apply Set.Finite.subset (Set.finite_singleton α₁)
    rintro q ⟨hq1, _⟩
    obtain ⟨k, hk⟩ := (hmem₁ q).mp hq1
    rw [hk, hl1]; simp
  rcases eq_or_ne lam₂ 0 with hl2 | hl2
  · -- R₂ is the singleton {α₂}; intersection ⊆ {α₂} is finite.
    right; right
    apply Set.Finite.subset (Set.finite_singleton α₂)
    rintro q ⟨_, hq2⟩
    obtain ⟨k, hk⟩ := (hmem₂ q).mp hq2
    rw [hk, hl2]; simp
  have hlam₁_pos : 0 < lam₁ := lt_of_le_of_ne hlam₁_nonneg (Ne.symm hl1)
  have hlam₂_pos : 0 < lam₂ := lt_of_le_of_ne hlam₂_nonneg (Ne.symm hl2)
  rcases lt_trichotomy α₁ α₂ with hα | hα | hα
  · right; right; exact hfin_of_lt α₁ α₂ lam₁ lam₂ R₁ R₂ hlam₁_nonneg hlam₂_pos hα hmem₁ hmem₂
  · -- α₁ = α₂: the rays are nested, or the intersection is finite.
    -- Decide whether the slope ratio is an integer power of `r`.
    by_cases hd : ∃ d : ℤ, lam₁ = lam₂ * r ^ d
    · obtain ⟨d, hd⟩ := hd
      rcases le_or_gt 0 d with hd0 | hd0
      · -- d ≥ 0 ⇒ R₁ ⊆ R₂
        left
        intro q hq
        obtain ⟨k, hk⟩ := (hmem₁ q).mp hq
        rw [hmem₂]
        refine ⟨d.toNat + k, ?_⟩
        rw [hk, hd, ← hα]
        have : r ^ d * r ^ k = r ^ (d.toNat + k) := by
          rw [← zpow_natCast r (d.toNat + k), ← zpow_natCast r k, ← zpow_add₀ (ne_of_gt hr0)]
          congr 1; push_cast [Int.toNat_of_nonneg hd0]; ring
        rw [mul_assoc, this]
      · -- d < 0 ⇒ R₂ ⊆ R₁
        right; left
        intro q hq
        obtain ⟨k, hk⟩ := (hmem₂ q).mp hq
        rw [hmem₁]
        refine ⟨(-d).toNat + k, ?_⟩
        rw [hk, hα]
        -- lam₂ = lam₁ * r^{-d}
        have hd' : lam₂ = lam₁ * r ^ (-d) := by
          rw [hd, mul_assoc, ← zpow_add₀ (ne_of_gt hr0)]; simp
        rw [hd']
        have : r ^ (-d) * r ^ k = r ^ ((-d).toNat + k) := by
          rw [← zpow_natCast r ((-d).toNat + k), ← zpow_natCast r k, ← zpow_add₀ (ne_of_gt hr0)]
          congr 1; push_cast [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -d)]; ring
        rw [mul_assoc, this]
    · -- no integer power relation ⇒ the intersection is empty.
      right; right
      convert Set.finite_empty
      rw [Set.eq_empty_iff_forall_notMem]
      rintro q ⟨hq1, hq2⟩
      obtain ⟨k₁, hk₁⟩ := (hmem₁ q).mp hq1
      obtain ⟨k₂, hk₂⟩ := (hmem₂ q).mp hq2
      apply hd
      -- lam₁ r^{k₁} = lam₂ r^{k₂} ⇒ lam₁ = lam₂ r^{k₂ - k₁}
      refine ⟨(k₂ : ℤ) - k₁, ?_⟩
      have heq : lam₁ * r ^ k₁ = lam₂ * r ^ k₂ := by
        have hαq : α₁ - lam₁ * r ^ k₁ = α₁ - lam₂ * r ^ k₂ := by rw [← hk₁, hα, ← hk₂]
        linarith
      have hrk1 : (r : ℚ) ^ k₁ ≠ 0 := by positivity
      rw [zpow_sub₀ (ne_of_gt hr0), zpow_natCast, zpow_natCast, mul_div_assoc',
          eq_div_iff hrk1, ← heq]
  · right; right
    rw [Set.inter_comm]
    exact hfin_of_lt α₂ α₁ lam₂ lam₁ R₂ R₁ hlam₂_nonneg hlam₁_pos hα hmem₂ hmem₁

/-- **Composition of two threshold insertions (same threshold).** Inserting `k·N'` zeros then
`j·N'` zeros at the *same* threshold `P` equals inserting `(k+j)·N'` zeros at `P`. -/
theorem insertZeros_comp_same (P N' k j : ℕ) :
    ((fun i => if i < P then i else i + j * N') ∘ (fun i => if i < P then i else i + k * N'))
      = (fun i => if i < P then i else i + (k + j) * N') := by
  funext i; simp only [Function.comp, add_mul]; split_ifs <;> omega

/-- **Affine form of a ray's parametrization.** With `r = p^{-N} ∈ (0,1)`, the `k`-th element of the
explicit base-`P` ray equals `α - λ·rᵏ`, where `α = (1/a)(m - head)` is the limit point and
`λ = (1/a)·tail ≥ 0` is the slope; `head`/`tail` are the digit-value sums below/at-or-above `P`. -/
theorem ray_enc_affine {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {m : ℤ} {N : ℕ+}
    (d_base : ℕ →₀ ℕ) (P k : ℕ) :
    (1 / (a : ℚ)) * ((m : ℚ) -
      (Finsupp.mapDomain (fun i => if i < P then i else i + k * (N : ℕ)) d_base).sum
        fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
    = (1 / (a : ℚ)) * ((m : ℚ) -
        ∑ i ∈ d_base.support.filter (fun i => i < P), (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      - ((p : ℚ) ^ (-(N : ℤ))) ^ k * ((1 / (a : ℚ)) *
        ∑ i ∈ d_base.support.filter (fun i => P ≤ i),
          (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) := by
  rw [digitVal_split d_base P (k * (N : ℕ))]
  have hpow : (p : ℚ) ^ (-(↑(k * (N : ℕ)) : ℤ)) = ((p : ℚ) ^ (-(N : ℤ))) ^ k := by
    rw [← zpow_natCast ((p : ℚ) ^ (-(N : ℤ))) k, ← zpow_mul]; congr 1; push_cast; ring
  rw [hpow]; ring

/-- **Tail of a ray is a ray (explicit base form).** For a base finsupp `d_base` with digit/sum
bounds and threshold `P`, the tail `{ enc (insert `k·N` zeros at `P`) | k ≥ k₀ }` is again a ray,
provided the tail lies in `S`. Its base is `mapDomain (insert `k₀·N` zeros at `P`) d_base` with the
same threshold `P`; the bounds transfer along the injective insertion reindexing, and the set
identity is the composition `insertZeros_comp_same`. -/
theorem ray_explicit_tail_isRay {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {c : ℕ} {m : ℤ} {N : ℕ+}
    {S : Set ℚ} (d_base : ℕ →₀ ℕ) (P : ℕ) (hdig : ∀ i, d_base i < p)
    (hsum : (d_base.sum fun _ v => v) ≤ c) (k₀ : ℕ)
    (hsub : { q : ℚ | ∃ k : ℕ, k₀ ≤ k ∧ q = (1 / (a : ℚ)) * ((m : ℚ) -
      (Finsupp.mapDomain (fun i => if i < P then i else i + k * (N : ℕ)) d_base).sum
        fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) } ⊆ S) :
    IsRay p a c m N S
      { q : ℚ | ∃ k : ℕ, k₀ ≤ k ∧ q = (1 / (a : ℚ)) * ((m : ℚ) -
        (Finsupp.mapDomain (fun i => if i < P then i else i + k * (N : ℕ)) d_base).sum
          fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) } := by
  classical
  refine ⟨hsub,
    Finsupp.mapDomain (fun i => if i < P then i else i + k₀ * (N : ℕ)) d_base, P, ?_, ?_, ?_⟩
  · -- digit bound transfers (insertion is injective)
    exact mapDomain_digit_lt d_base (strictMono_insertZeros _ _).injective hdig
  · -- sum bound transfers
    rw [sum_mapDomain_inj d_base (strictMono_insertZeros _ _).injective]; exact hsum
  · -- the set identity, via the composition of insertions
    ext q
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k - k₀, ?_⟩
      rw [← Finsupp.mapDomain_comp, insertZeros_comp_same]
      congr 2
      have : k₀ + (k - k₀) = k := by omega
      rw [this]
    · rintro ⟨j, rfl⟩
      refine ⟨k₀ + j, by omega, ?_⟩
      rw [← Finsupp.mapDomain_comp, insertZeros_comp_same]

/-- **Infinite-ray tail avoids a finite set.** If the explicit base-`P` ray has positive slope
`λ = (1/a)·tail > 0` (equivalently the tail digit-sum below the cutoff is nonzero — the ray is not a
single point), then for any finite `F` there is a cutoff `k₀` beyond which every ray element avoids
`F`. The map `k ↦ α - λ·rᵏ` is strictly antitone (`0 < r < 1`), hence injective, so its `F`-preimage
is finite and bounded. -/
theorem infinite_ray_tail_avoids_finite {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {m : ℤ} {N : ℕ+}
    (d_base : ℕ →₀ ℕ) (P : ℕ)
    (hlam : (0 : ℚ) < (1 / (a : ℚ)) *
      ∑ i ∈ d_base.support.filter (fun i => P ≤ i), (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
    (F : Finset ℚ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (1 / (a : ℚ)) * ((m : ℚ) -
        (Finsupp.mapDomain (fun i => if i < P then i else i + k * (N : ℕ)) d_base).sum
          fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∉ F := by
  classical
  have hp1 : (1 : ℚ) < p := by
    exact_mod_cast (Fact.out : Nat.Prime p).two_le.trans_lt' (by norm_num)
  set r : ℚ := (p : ℚ) ^ (-(N : ℤ)) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, zpow_neg, inv_lt_one_iff₀]; right
    exact one_lt_zpow₀ hp1 (by exact_mod_cast N.pos)
  set α : ℚ := (1 / (a : ℚ)) * ((m : ℚ) -
    ∑ i ∈ d_base.support.filter (fun i => i < P), (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) with hα
  set lam : ℚ := (1 / (a : ℚ)) *
    ∑ i ∈ d_base.support.filter (fun i => P ≤ i),
      (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) with hlamdef
  -- The parametrization `g k = α - r^k * lam` is strictly monotone (increasing), hence injective.
  set g : ℕ → ℚ := fun k => α - r ^ k * lam with hg
  have hg_mono : StrictMono g := by
    intro k₁ k₂ hk
    simp only [hg]
    have hpow : r ^ k₂ < r ^ k₁ := pow_lt_pow_right_of_lt_one₀ hr0 hr1 hk
    have hml : r ^ k₂ * lam < r ^ k₁ * lam := mul_lt_mul_of_pos_right hpow hlam
    linarith
  have hg_inj : Function.Injective g := hg_mono.injective
  -- `{k | g k ∈ F}` is finite (injective preimage of a finite set), hence bounded.
  have hfin : {k : ℕ | g k ∈ F}.Finite := by
    apply Set.Finite.preimage (f := g)
    · exact hg_inj.injOn
    · exact F.finite_toSet
  obtain ⟨k₀, hk₀⟩ := hfin.bddAbove
  refine ⟨k₀ + 1, fun k hk => ?_⟩
  rw [ray_enc_affine d_base P k, ← hα, ← hlamdef, ← hr]
  change g k ∉ F
  intro hmem
  have hmemset : k ∈ {k : ℕ | g k ∈ F} := hmem
  have := hk₀ hmemset
  omega

/-- **Per-ray split for disjointification.** Given a ray `R ⊆ S` and a finite set `D`, write
`R = ↑head ∪ Rt` with `head` finite and `Rt ⊆ R`, where either `Rt = ∅` (the degenerate
single-point ray, fully absorbed into `head`) or `Rt` is again a ray disjoint from `D`. The tail
`Rt` is produced by `ray_explicit_tail_isRay`, and `infinite_ray_tail_avoids_finite` provides the
cutoff making it avoid `D`. -/
theorem ray_split_for_disjoint {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {c : ℕ} {m : ℤ} {N : ℕ+}
    {S : Set ℚ} {R : Set ℚ} (hR : IsRay p a c m N S R) (D : Finset ℚ) :
    ∃ (head : Finset ℚ) (Rt : Set ℚ), R = ↑head ∪ Rt ∧ Rt ⊆ R ∧
      (Rt = ∅ ∨ (IsRay p a c m N S Rt ∧ Disjoint Rt (↑D : Set ℚ))) := by
  classical
  obtain ⟨hRS, d_base, P, hdig, hsum, hReq⟩ := hR
  -- The slope `lam` of `R` (digit-value mass at or above the cutoff `P`).
  set lam : ℚ := (1 / (a : ℚ)) *
    ∑ i ∈ d_base.support.filter (fun i => P ≤ i),
      (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) with hlamdef
  by_cases hlam0 : lam = 0
  · -- Degenerate ray: every element equals the single limit point `α`, so `R = {α}`.
    set α : ℚ := (1 / (a : ℚ)) * ((m : ℚ) -
      ∑ i ∈ d_base.support.filter (fun i => i < P), (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      with hαdef
    have hR_eq : R = {α} := by
      rw [hReq]
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨k, rfl⟩
        rw [ray_enc_affine d_base P k, ← hαdef, ← hlamdef, hlam0, mul_zero, sub_zero]
      · rintro rfl
        exact ⟨0, by rw [ray_enc_affine d_base P 0, ← hαdef, ← hlamdef, hlam0, mul_zero, sub_zero]⟩
    -- Put the single point `α` in `head`, with `Rt = ∅`.
    refine ⟨{α}, ∅, ?_, by simp, Or.inl rfl⟩
    rw [hR_eq]; simp
  · -- Infinite ray: positive slope, so the tail avoids `D`.
    have hlam_pos : 0 < lam := by
      rcases lt_or_gt_of_ne hlam0 with h | h
      · exfalso
        rw [hlamdef] at h
        have haQ : (0 : ℚ) < a := by exact_mod_cast a.pos
        have hinva : (0 : ℚ) < 1 / a := by positivity
        have hsum_nonneg : 0 ≤ ∑ i ∈ d_base.support.filter (fun i => P ≤ i),
            (d_base i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
          apply Finset.sum_nonneg; intro i _; positivity
        nlinarith [mul_nonneg (le_of_lt hinva) hsum_nonneg]
      · exact h
    -- Cutoff `k₀` beyond which the ray avoids `D`.
    obtain ⟨k₀, hk₀⟩ := infinite_ray_tail_avoids_finite (a := a) (m := m) (N := N) d_base P
      (by rw [← hlamdef]; exact hlam_pos) D
    -- The enc-element at index `k`.
    set enc : ℕ → ℚ := fun k => (1 / (a : ℚ)) * ((m : ℚ) -
      (Finsupp.mapDomain (fun i => if i < P then i else i + k * (N : ℕ)) d_base).sum
        fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) with hencdef
    -- The tail `Rt` from cutoff `k₀`.
    set Rt : Set ℚ := { q : ℚ | ∃ k : ℕ, k₀ ≤ k ∧ q = enc k } with hRtdef
    have hRt_sub : Rt ⊆ R := by
      rw [hRtdef, hReq]; rintro q ⟨k, _, rfl⟩; exact ⟨k, rfl⟩
    -- `head = { enc k | k < k₀ }`, a finite set covering `R \ Rt`.
    refine ⟨(Finset.range k₀).image enc, Rt, ?_, hRt_sub, ?_⟩
    · -- `R = ↑head ∪ Rt`.
      rw [hReq]
      ext q
      simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_range, Set.mem_union,
        Set.mem_image, Set.mem_Iio, hRtdef, hencdef]
      constructor
      · rintro ⟨k, rfl⟩
        rcases lt_or_ge k k₀ with hk | hk
        · exact Or.inl ⟨k, hk, rfl⟩
        · exact Or.inr ⟨k, hk, rfl⟩
      · rintro (⟨k, _, rfl⟩ | ⟨k, _, rfl⟩) <;> exact ⟨k, rfl⟩
    · -- `Rt` is a ray disjoint from `D`.
      right
      refine ⟨ray_explicit_tail_isRay d_base P hdig hsum k₀ ?_, ?_⟩
      · -- the tail lies in `S` (it is `⊆ R ⊆ S`).
        intro q hq; exact hRS (hRt_sub hq)
      · -- disjoint from `D`.
        rw [Set.disjoint_left]
        rintro q ⟨k, hk, rfl⟩ hqD
        rw [Finset.mem_coe] at hqD
        exact hk₀ k hk hqD

/-- **Proposition `prop:29055`**: `S` is a union of a finite set and finitely many
**pairwise disjoint** rays.

*Proof sketch*: Start from `eq_finite_union_rays`. By `rays_sub_or_finite_inter`, discard any ray
contained in another; then pairwise intersections are finite. Choose tail cutoff `k₀` large enough
to make the tails pairwise disjoint; the removed heads are finite and go into `E`. -/
theorem eq_finite_union_disjoint_rays {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {b : ℤ} {c : ℕ}
    {m : ℤ} {hm : -b ≤ m} {M N : ℕ+} {S : Set ℚ}
    (hS : IsAdmissible p a b c m hm M N S) :
    ∃ (E : Finset ℚ) (rays : Finset (Set ℚ)),
      (∀ R ∈ rays, IsRay p a c m N S R) ∧
      (∀ R₁ ∈ rays, ∀ R₂ ∈ rays, R₁ ≠ R₂ → Disjoint R₁ R₂) ∧
      S = ↑E ∪ rays.sup id := by
  classical
  -- Start from the (possibly overlapping) ray decomposition.
  obtain ⟨E₀, rays₀, hisray₀, hSeq⟩ := eq_finite_union_rays hS
  -- The maximal rays (under `⊆`) of `rays₀`: discarding rays contained in another keeps the union.
  set Mx : Finset (Set ℚ) := rays₀.filter (fun R => Maximal (· ∈ rays₀) R) with hMx
  have hMx_sub : Mx ⊆ rays₀ := Finset.filter_subset _ _
  have hMx_ray : ∀ R ∈ Mx, IsRay p a c m N S R := fun R hR => hisray₀ R (hMx_sub hR)
  -- Every ray in `rays₀` is contained in a maximal one, so the unions agree.
  have hsup_eq : rays₀.sup id = Mx.sup id := by
    apply le_antisymm
    · apply Finset.sup_le
      intro R hR
      obtain ⟨R', hRR', hR'max⟩ := Finset.exists_le_maximal rays₀ hR
      have hR'Mx : R' ∈ Mx := by rw [hMx, Finset.mem_filter]; exact ⟨hR'max.1, hR'max⟩
      exact le_trans hRR' (Finset.le_sup (f := id) hR'Mx)
    · exact Finset.sup_mono hMx_sub
  -- Distinct maximal rays have finite intersection.
  have hMx_fin_inter : ∀ R₁ ∈ Mx, ∀ R₂ ∈ Mx, R₁ ≠ R₂ → (R₁ ∩ R₂).Finite := by
    intro R₁ hR₁ R₂ hR₂ hne
    have hR₁max : Maximal (· ∈ rays₀) R₁ := (Finset.mem_filter.mp hR₁).2
    have hR₂max : Maximal (· ∈ rays₀) R₂ := (Finset.mem_filter.mp hR₂).2
    rcases rays_sub_or_finite_inter (hMx_ray R₁ hR₁) (hMx_ray R₂ hR₂) with h | h | h
    · exact absurd (hR₁max.eq_of_le hR₂max.1 h) hne
    · exact absurd (hR₂max.eq_of_le hR₁max.1 h).symm hne
    · exact h
  -- The set `D` of all pairwise overlaps among maximal rays is finite.
  set D : Set ℚ := ⋃ R₁ ∈ Mx, ⋃ R₂ ∈ Mx, (if R₁ = R₂ then (∅ : Set ℚ) else R₁ ∩ R₂) with hD
  have hDfin : D.Finite := by
    rw [hD]
    apply Set.Finite.biUnion Mx.finite_toSet
    intro R₁ hR₁
    apply Set.Finite.biUnion Mx.finite_toSet
    intro R₂ hR₂
    by_cases h : R₁ = R₂
    · simp [h]
    · rw [if_neg h]
      exact hMx_fin_inter R₁ hR₁ R₂ hR₂ h
  -- Per maximal ray: split into a finite head plus a ray-tail disjoint from `D`.
  set D' : Finset ℚ := hDfin.toFinset with hD'
  have hsplit : ∀ R ∈ Mx, ∃ (head : Finset ℚ) (Rt : Set ℚ), R = ↑head ∪ Rt ∧ Rt ⊆ R ∧
      (Rt = ∅ ∨ (IsRay p a c m N S Rt ∧ Disjoint Rt (↑D' : Set ℚ))) :=
    fun R hR => ray_split_for_disjoint (hMx_ray R hR) D'
  choose! head Rt hsplit_eq hsplit_sub hsplit_or using hsplit
  -- The disjoint ray family: the nonempty tails.
  set rays : Finset (Set ℚ) := (Mx.image Rt).erase ∅ with hrays
  -- The finite remainder: `E₀` plus all the heads (which include the absorbed singleton rays).
  set E : Finset ℚ := E₀ ∪ Mx.biUnion head with hE
  refine ⟨E, rays, ?_, ?_, ?_⟩
  · -- Every element of `rays` is a ray.
    intro T hT
    rw [hrays, Finset.mem_erase, Finset.mem_image] at hT
    obtain ⟨hTne, R, hRMx, rfl⟩ := hT
    rcases hsplit_or R hRMx with h | h
    · exact absurd h hTne
    · exact h.1
  · -- Distinct tails are disjoint.
    intro T₁ hT₁ T₂ hT₂ hne
    rw [hrays, Finset.mem_erase, Finset.mem_image] at hT₁ hT₂
    obtain ⟨hT₁ne, R₁, hR₁Mx, rfl⟩ := hT₁
    obtain ⟨hT₂ne, R₂, hR₂Mx, rfl⟩ := hT₂
    have hR12 : R₁ ≠ R₂ := fun h => hne (by rw [h])
    -- `Rt R₁` is disjoint from `D`, and `Rt R₁ ∩ Rt R₂ ⊆ R₁ ∩ R₂ ⊆ D`.
    rcases hsplit_or R₁ hR₁Mx with h1 | h1
    · exact absurd h1 hT₁ne
    · rw [Set.disjoint_left]
      intro q hq1 hq2
      have hqR1 : q ∈ R₁ := hsplit_sub R₁ hR₁Mx hq1
      have hqR2 : q ∈ R₂ := hsplit_sub R₂ hR₂Mx hq2
      -- `q ∈ R₁ ∩ R₂ ⊆ D = ↑D'`.
      have hqD : q ∈ D := by
        rw [hD]
        simp only [Set.mem_iUnion]
        exact ⟨R₁, hR₁Mx, R₂, hR₂Mx, by rw [if_neg hR12]; exact ⟨hqR1, hqR2⟩⟩
      have hqD' : q ∈ (↑D' : Set ℚ) := by rw [hD', Set.Finite.coe_toFinset]; exact hqD
      exact (Set.disjoint_left.mp h1.2) hq1 hqD'
  · -- `S = ↑E ∪ rays.sup id`.
    rw [hSeq, hsup_eq]
    -- `Mx.sup id = ↑(Mx.biUnion head) ∪ rays.sup id`.
    have hkey : Mx.sup id = (↑(Mx.biUnion head) : Set ℚ) ∪ rays.sup id := by
      rw [Finset.sup_set_eq_biUnion, Finset.sup_set_eq_biUnion]
      ext q
      simp only [Set.mem_iUnion, id_eq, Finset.coe_biUnion, Finset.mem_coe,
        Set.mem_union, exists_prop]
      constructor
      · rintro ⟨R, hRMx, hqR⟩
        rw [hsplit_eq R hRMx] at hqR
        rcases hqR with hqhead | hqRt
        · exact Or.inl ⟨R, hRMx, hqhead⟩
        · -- `q ∈ Rt R`; if `Rt R = ∅` impossible, else it's an element of `rays`.
          rcases hsplit_or R hRMx with hempty | _
          · rw [hempty] at hqRt; exact absurd hqRt (Set.notMem_empty q)
          · refine Or.inr ⟨Rt R, ?_, hqRt⟩
            rw [hrays, Finset.mem_erase, Finset.mem_image]
            refine ⟨?_, R, hRMx, rfl⟩
            intro hc; rw [hc] at hqRt; exact absurd hqRt (Set.notMem_empty q)
      · rintro (⟨R, hRMx, hqhead⟩ | ⟨T, hTrays, hqT⟩)
        · exact ⟨R, hRMx, by rw [hsplit_eq R hRMx]; exact Or.inl hqhead⟩
        · rw [hrays, Finset.mem_erase, Finset.mem_image] at hTrays
          obtain ⟨_, R, hRMx, rfl⟩ := hTrays
          exact ⟨R, hRMx, by rw [hsplit_eq R hRMx]; exact Or.inr hqT⟩
    rw [hkey, hE]
    rw [Finset.coe_union]
    ext q; simp only [Set.mem_union, Finset.mem_coe]; tauto

/-!
### Main corollary: QTR sets decompose into rays (`coro:48108`)
-/

/-- **Corollary `coro:48108`**: ray decomposition of bounded QTR sets.

Let `U = Function.support x` where `x : ℚ → 𝔽ᵃ_[p]` is QTR with data `(a, b, c, M, N)`.
If `U` is bounded (as a subset of `ℚ`) and has only finitely many accumulation points, then `U`
decomposes as a union of a finite set and finitely many pairwise disjoint rays, each contained in
some `(a, b, c, mᵢ, M, N)`-admissible subset of `U` with `mᵢ ≥ -b`.

*Proof sketch*: Since `U` is bounded, there exist finitely many integers `mᵢ ≥ -b` with
`U ⊆ ⋃ᵢ Sabc_m p a c mᵢ`. Each slice `Sabc_m p a c mᵢ ∩ U` is `(a,b,c,mᵢ,M,N)`-admissible
with finitely many accumulation points. The slices are disjoint for distinct `mᵢ`. Apply
`eq_finite_union_disjoint_rays` to each slice and union. -/
theorem qtr_ray_decomposition {p : ℕ} [Fact (Nat.Prime p)]
    {a : ℕ+} {b c : ℕ} {M N : ℕ+}
    {x : ℚ → 𝔽ᵃ_[p]}
    (hqtr : IsQTR x a b c M N)
    (hbdd : Bornology.IsBounded (Function.support x))
    (hfin_acc : (derivedSet (Function.support x)).Finite) :
    ∃ (E : Finset ℚ) (rays : Finset (Set ℚ)),
      (∀ R ∈ rays, ∃ (m : ℤ) (hm : -(b : ℤ) ≤ m),
        IsRay p a c m N (Function.support x) R ∧
        IsAdmissible p a (b : ℤ) c m hm M N
          (Function.support x ∩ Sabc_m p a c m)) ∧
      (∀ R₁ ∈ rays, ∀ R₂ ∈ rays, R₁ ≠ R₂ → Disjoint R₁ R₂) ∧
      Function.support x = ↑E ∪ rays.sup id := by
  classical
  have hp1 : (1 : ℕ) < p := (Fact.out : Nat.Prime p).one_lt
  have hp1Q : (1 : ℚ) < p := by exact_mod_cast hp1
  have haQ : (0 : ℚ) < a := by exact_mod_cast a.pos
  set U : Set ℚ := Function.support x with hU
  obtain ⟨hWF, hUsub, hrec⟩ := hqtr
  -- The integer part `mOf s = ⌈a·s⌉` of an element `s ∈ U`.
  set mOf : ℚ → ℤ := fun s => ⌈(a : ℚ) * s⌉ with hmOf
  -- Each `s ∈ Sabc` with witness `(n, d)` (so `n ≥ -b`) has `mOf s = n` and lies in `Sabc_m … n`.
  have hmem_slice : ∀ s ∈ U, -(b : ℤ) ≤ mOf s ∧ s ∈ Sabc_m p a c (mOf s) := by
    intro s hsU
    obtain ⟨n, d, hnb, hdig, hsum, hseq⟩ := hUsub hsU
    -- `a·s = n - DV`, with `0 ≤ DV < 1`, so `⌈a·s⌉ = n`.
    set DV : ℚ := d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) with hDV
    have hDV_lt : DV < 1 := digitValue_lt_one hp1 d hdig
    have hDV_nonneg : 0 ≤ DV := by rw [hDV]; apply Finset.sum_nonneg; intro i _; positivity
    have has : (a : ℚ) * s = (n : ℚ) - DV := by
      rw [hseq]; field_simp
    have hmOf_eq : mOf s = n := by
      simp only [hmOf]
      rw [has, Int.ceil_eq_iff]
      constructor
      · linarith
      · linarith
    refine ⟨by rw [hmOf_eq]; exact hnb, ?_⟩
    rw [hmOf_eq]
    exact ⟨d, hdig, hsum, hseq⟩
  -- Each slice `U ∩ Sabc_m … m` with `m ≥ -b` is admissible.
  have hslice_adm : ∀ (m : ℤ) (hm : -(b : ℤ) ≤ m),
      IsAdmissible p a (b : ℤ) c m hm M N (U ∩ Sabc_m p a c m) := by
    intro m hm
    refine ⟨?_, ?_, ?_⟩
    · -- (S1): the slice is contained in `Sabc_m`.
      exact Set.inter_subset_right
    · -- (S2): the `M`-zero-run ⇒ `N`-zero-insertion closure, from the QTR recurrence.
      intro d hdig hsum _qval hqmem k hrun
      -- `q ∈ U ∩ Sabc_m`; the QTR recurrence gives `x q = x q'` for the insertion `q'`.
      simp only [Set.mem_inter_iff] at hqmem ⊢
      obtain ⟨hqU, hqS⟩ := hqmem
      set d' : ℕ →₀ ℕ := Finsupp.mapDomain
        (fun i => if i < k + (M : ℕ) then i else i + (N : ℕ)) d with hd'def
      set q' : ℚ := (1 / (a : ℚ)) *
        ((m : ℚ) - d'.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) with hq'def
      -- The recurrence: `x q = x q'`.
      have hxeq : x ((1 / (a : ℚ)) *
          ((m : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))) = x q' :=
        hrec m hm d hdig hsum k hrun
      -- `x q ≠ 0` (since `q ∈ U = support x`), so `x q' ≠ 0`, i.e. `q' ∈ U`.
      have hq'U : q' ∈ U := by
        rw [hU, Function.mem_support, ← hxeq]
        exact hqU
      refine ⟨hq'U, ?_⟩
      -- `q' ∈ Sabc_m`: same `m`, insertion preserves digit/sum bounds.
      refine ⟨d', ?_, ?_, rfl⟩
      · exact mapDomain_digit_lt d (strictMono_insertZeros _ _).injective hdig
      · rw [hd'def, sum_mapDomain_inj d (strictMono_insertZeros _ _).injective]; exact hsum
    · -- (S3): finitely many accumulation points (monotone in the set).
      apply Set.Finite.subset hfin_acc
      apply derivedSet_mono
      exact Set.inter_subset_left
  -- The set of relevant integer parts `mOf '' U` is finite (boundedness of `U`).
  have hmvals_fin : (mOf '' U).Finite := by
    rw [hmOf]
    rw [Metric.isBounded_iff] at hbdd
    obtain ⟨C, hC⟩ := hbdd
    rcases U.eq_empty_or_nonempty with hUe | ⟨q0, hq0⟩
    · rw [hUe]; simp
    · set R : ℝ := |(q0 : ℝ)| + C with hR
      set B : ℤ := ⌈(a : ℝ) * R⌉ + 1 with hB
      apply Set.Finite.subset (Set.finite_Icc (-B) B)
      rintro n ⟨q, hq, rfl⟩
      have hdist : dist q q0 ≤ C := hC hq hq0
      have hqq0 : |(q : ℝ) - (q0:ℝ)| ≤ C := by
        have := hdist; rw [Rat.dist_eq] at this; linarith [this]
      have hqbound : |(q : ℝ)| ≤ R := by
        rw [hR]
        calc |(q:ℝ)| = |((q:ℝ) - (q0:ℝ)) + (q0:ℝ)| := by ring_nf
          _ ≤ |(q:ℝ) - (q0:ℝ)| + |(q0:ℝ)| := abs_add_le _ _
          _ ≤ C + |(q0:ℝ)| := by linarith
          _ = |(q0:ℝ)| + C := by ring
      have haR : (0:ℝ) ≤ (a:ℝ) := by positivity
      have hax : |(a:ℝ) * (q:ℝ)| ≤ (a:ℝ) * R := by
        rw [abs_mul, abs_of_nonneg haR]; exact mul_le_mul_of_nonneg_left hqbound haR
      have hax' := abs_le.mp hax
      simp only [Set.mem_Icc]
      have hceil2 : (a:ℝ) * (q:ℝ) ≤ ((⌈(a:ℚ) * q⌉ : ℤ) : ℝ) := by
        have := Int.le_ceil ((a:ℚ) * q); exact_mod_cast this
      have hceil : ((⌈(a:ℚ) * q⌉ : ℤ) : ℝ) < (a:ℝ) * (q:ℝ) + 1 := by
        have := Int.ceil_lt_add_one ((a:ℚ) * q); exact_mod_cast this
      constructor
      · have h1 : ((⌈(a:ℚ) * q⌉:ℤ):ℝ) ≥ -((a:ℝ)*R) := le_trans (by linarith [hax'.1]) hceil2
        have h2 : (-(B:ℤ):ℝ) ≤ -((a:ℝ)*R) := by
          rw [hB]; push_cast; have := Int.le_ceil ((a:ℝ)*R); linarith
        exact_mod_cast le_trans h2 h1
      · have h1 : ((⌈(a:ℚ) * q⌉:ℤ):ℝ) < (a:ℝ)*R + 1 := by linarith [hax'.2]
        have h2 : (a:ℝ)*R + 1 ≤ ((B:ℤ):ℝ) := by
          rw [hB]; push_cast; have := Int.le_ceil ((a:ℝ)*R); linarith
        have hlt : ((⌈(a:ℚ) * q⌉:ℤ):ℝ) < ((B:ℤ):ℝ) := by linarith
        exact_mod_cast le_of_lt hlt
  -- The finite set of integer parts, all `≥ -b`.
  set ms : Finset ℤ := hmvals_fin.toFinset with hms
  have hms_ge : ∀ m ∈ ms, -(b : ℤ) ≤ m := by
    intro m hmem
    rw [hms, Set.Finite.mem_toFinset] at hmem
    obtain ⟨s, hsU, rfl⟩ := hmem
    exact (hmem_slice s hsU).1
  -- Per relevant `m`, decompose the admissible slice into disjoint rays.
  have hdecomp : ∀ m ∈ ms, ∃ (Em : Finset ℚ) (raysm : Finset (Set ℚ)),
      (∀ R ∈ raysm, IsRay p a c m N (U ∩ Sabc_m p a c m) R) ∧
      (∀ R₁ ∈ raysm, ∀ R₂ ∈ raysm, R₁ ≠ R₂ → Disjoint R₁ R₂) ∧
      (U ∩ Sabc_m p a c m) = ↑Em ∪ raysm.sup id := by
    intro m hmem
    exact eq_finite_union_disjoint_rays (hslice_adm m (hms_ge m hmem))
  choose! Em raysm hraysm_ray hraysm_disj hslice_eq using hdecomp
  -- Assemble.
  refine ⟨ms.biUnion Em, ms.biUnion raysm, ?_, ?_, ?_⟩
  · -- Each collected ray is a ray in `U` with the admissibility witness.
    intro R hR
    rw [Finset.mem_biUnion] at hR
    obtain ⟨m, hmem, hRraysm⟩ := hR
    have hRslice := hraysm_ray m hmem R hRraysm
    -- `R ⊆ slice m ⊆ U`, so `IsRay … U R` (the `∃ base` part is `S`-independent).
    have hRU : IsRay p a c m N U R := by
      refine ⟨?_, hRslice.2⟩
      exact le_trans hRslice.1 Set.inter_subset_left
    exact ⟨m, hms_ge m hmem, hRU, hslice_adm m (hms_ge m hmem)⟩
  · -- Disjointness: within a slice (prop:29055) and across slices (disjoint `Sabc_m`).
    -- Helper: every element of `Sabc_m … m` has integer part `mOf = m`.
    have hmOf_slice : ∀ (m : ℤ) (s : ℚ), s ∈ Sabc_m p a c m → mOf s = m := by
      intro m s hs
      obtain ⟨d, hdig, hsum, hseq⟩ := hs
      set DV : ℚ := d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) with hDV
      have hDV_lt : DV < 1 := digitValue_lt_one hp1 d hdig
      have hDV_nonneg : 0 ≤ DV := by rw [hDV]; apply Finset.sum_nonneg; intro i _; positivity
      have has : (a : ℚ) * s = (m : ℚ) - DV := by rw [hseq]; field_simp
      simp only [hmOf]
      rw [has, Int.ceil_eq_iff]
      exact ⟨by linarith, by linarith⟩
    intro R₁ hR₁ R₂ hR₂ hne
    rw [Finset.mem_biUnion] at hR₁ hR₂
    obtain ⟨m₁, hm₁mem, hR₁raysm⟩ := hR₁
    obtain ⟨m₂, hm₂mem, hR₂raysm⟩ := hR₂
    by_cases hmeq : m₁ = m₂
    · -- same slice: use prop:29055's pairwise disjointness.
      subst hmeq
      exact hraysm_disj m₁ hm₁mem R₁ hR₁raysm R₂ hR₂raysm hne
    · -- distinct integer parts: the slices are disjoint, so the rays are.
      have hR₁slice : R₁ ⊆ U ∩ Sabc_m p a c m₁ := (hraysm_ray m₁ hm₁mem R₁ hR₁raysm).1
      have hR₂slice : R₂ ⊆ U ∩ Sabc_m p a c m₂ := (hraysm_ray m₂ hm₂mem R₂ hR₂raysm).1
      rw [Set.disjoint_left]
      intro q hq1 hq2
      have hqm1 : mOf q = m₁ := hmOf_slice m₁ q (hR₁slice hq1).2
      have hqm2 : mOf q = m₂ := hmOf_slice m₂ q (hR₂slice hq2).2
      exact hmeq (hqm1 ▸ hqm2)
  · -- Union equality.
    apply Set.eq_of_subset_of_subset
    · -- `U ⊆ ↑(⋃ Em) ∪ (⋃ raysm).sup id`.
      intro s hsU
      -- `mOf s ∈ ms` and `s ∈ slice (mOf s)`.
      have hmsmem : mOf s ∈ ms := by
        rw [hms, Set.Finite.mem_toFinset]; exact ⟨s, hsU, rfl⟩
      have hsslice : s ∈ U ∩ Sabc_m p a c (mOf s) :=
        ⟨hsU, (hmem_slice s hsU).2⟩
      rw [hslice_eq (mOf s) hmsmem] at hsslice
      rcases hsslice with hsE | hsray
      · -- `s ∈ ↑Em (mOf s) ⊆ ↑(⋃ Em)`.
        left
        rw [Finset.coe_biUnion]
        simp only [Set.mem_iUnion, Finset.mem_coe]
        exact ⟨mOf s, hmsmem, hsE⟩
      · -- `s ∈ (raysm (mOf s)).sup id ⊆ (⋃ raysm).sup id`.
        right
        rw [Finset.sup_set_eq_biUnion] at hsray ⊢
        simp only [Set.mem_iUnion, id_eq] at hsray ⊢
        obtain ⟨R, hRmem, hsR⟩ := hsray
        exact ⟨R, Finset.mem_biUnion.mpr ⟨mOf s, hmsmem, hRmem⟩, hsR⟩
    · -- `↑(⋃ Em) ∪ (⋃ raysm).sup id ⊆ U`.
      rintro s (hsE | hsray)
      · -- `s ∈ ↑Em m` for some `m ∈ ms`; `Em m ⊆ slice m ⊆ U`.
        rw [Finset.coe_biUnion] at hsE
        simp only [Set.mem_iUnion, Finset.mem_coe] at hsE
        obtain ⟨m, hmmem, hsEm⟩ := hsE
        have : s ∈ U ∩ Sabc_m p a c m := by
          rw [hslice_eq m hmmem]; left; exact hsEm
        exact this.1
      · -- `s ∈ (raysm m).sup id`; rays `⊆ slice m ⊆ U`.
        rw [Finset.sup_set_eq_biUnion] at hsray
        simp only [Set.mem_iUnion, id_eq] at hsray
        obtain ⟨R, hRmem, hsR⟩ := hsray
        rw [Finset.mem_biUnion] at hRmem
        obtain ⟨m, hmmem, hRraysm⟩ := hRmem
        exact ((hraysm_ray m hmmem R hRraysm).1 hsR).1

end FormalizedSparse
