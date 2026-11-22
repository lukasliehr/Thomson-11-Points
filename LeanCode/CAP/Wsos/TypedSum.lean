module

public import Mathlib.Tactic.Linarith
public import CAP.Schema.ThreePoint.Triples

/-!
# The typed three-point bound as a statement on indices

`typed_sum`: let `ι` be a finite set of indices (the points), and let real numbers be given

* `H i j` for pairs (the value of the pair polynomial of the classes of `i`, `j` at their inner product),
* `Pp i j k` for triples (the share of the pair `i, j` that belongs to the third point `k`),
* `S i j k` for triples (the rooted form at the root `i` for the points `j`, `k`; indices may coincide),
* `c i j k` for triples of distinct indices (the constant of the triple type),

such that

* `0 ≤ ∑ j k, S i j k` for every `i` (the rooted blocks and the kernels are positive semidefinite),
* `∑ k ∉ {i, j}, Pp i j k = H i j - (S i i j + S i j i + S i j j + S j j i + S j i j + S j i i)` for
  `i ≠ j` (the share equation),
* `c i j k ≤ Pp i j k + Pp i k j + Pp j k i - 2 (S i j k + S j i k + S k i j)` for distinct `i, j, k`
  (the inequality of the triple type).

Then the sum of `c` over the ordered triples of distinct indices is at most
`3 ∑ i ≠ j, H i j + 6 ∑ i, S i i i`. Classes do not occur in this statement: they enter only when
the three hypotheses are derived from the data of a certificate.
-/

@[expose] public section

namespace CAP.Wsos

open Finset CAP.ThreePoint

theorem sum3_le {ι : Type*} [Fintype ι] {F G : ι → ι → ι → ℝ} (h : ∀ i j k, F i j k ≤ G i j k) :
    sum3 F ≤ sum3 G :=
  sum_le_sum fun i _ => sum_le_sum fun j _ => sum_le_sum fun k _ => h i j k

theorem distinct3_231 {ι : Type*} (i j k : ι) : Distinct3 j k i ↔ Distinct3 i j k :=
  ⟨fun ⟨a, b, c⟩ => ⟨b.symm, c.symm, a⟩, fun ⟨a, b, c⟩ => ⟨c, a.symm, b.symm⟩⟩

theorem distinct3_312 {ι : Type*} (i j k : ι) : Distinct3 k i j ↔ Distinct3 i j k :=
  ⟨fun ⟨a, b, c⟩ => ⟨c, a.symm, b.symm⟩, fun ⟨a, b, c⟩ => ⟨b.symm, c.symm, a⟩⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum of a function over the triples of distinct indices. -/
def dsum3 (F : ι → ι → ι → ℝ) : ℝ := sum3 fun i j k => if Distinct3 i j k then F i j k else 0

theorem dsum3_swap23 (F : ι → ι → ι → ℝ) : dsum3 (fun i j k => F i k j) = dsum3 F := by
  unfold dsum3
  rw [← sum3_swap23 fun i j k => if Distinct3 i j k then F i j k else 0]
  exact sum3_congr fun i j k => if_congr (distinct3_swap23 i j k).symm rfl rfl

theorem dsum3_swap12 (F : ι → ι → ι → ℝ) : dsum3 (fun i j k => F j i k) = dsum3 F := by
  unfold dsum3
  rw [← sum3_swap12 fun i j k => if Distinct3 i j k then F i j k else 0]
  exact sum3_congr fun i j k => if_congr (distinct3_swap12 i j k).symm rfl rfl

theorem dsum3_231 (F : ι → ι → ι → ℝ) : dsum3 (fun i j k => F j k i) = dsum3 F := by
  unfold dsum3
  rw [← sum3_perm231 fun i j k => if Distinct3 i j k then F i j k else 0]
  exact sum3_congr fun i j k => if_congr (distinct3_231 i j k).symm rfl rfl

theorem dsum3_312 (F : ι → ι → ι → ℝ) : dsum3 (fun i j k => F k i j) = dsum3 F := by
  unfold dsum3
  rw [← sum3_perm312 fun i j k => if Distinct3 i j k then F i j k else 0]
  exact sum3_congr fun i j k => if_congr (distinct3_312 i j k).symm rfl rfl

theorem dsum3_add (F G : ι → ι → ι → ℝ) : dsum3 (fun i j k => F i j k + G i j k) = dsum3 F + dsum3 G := by
  unfold dsum3
  rw [← sum3_add]
  exact sum3_congr fun i j k => by split_ifs <;> simp

theorem dsum3_smul (a : ℝ) (F : ι → ι → ι → ℝ) : dsum3 (fun i j k => a * F i j k) = a * dsum3 F := by
  unfold dsum3
  rw [← sum3_smul]
  exact sum3_congr fun i j k => by split_ifs <;> simp

theorem dsum3_le {F G : ι → ι → ι → ℝ} (h : ∀ i j k, Distinct3 i j k → F i j k ≤ G i j k) : dsum3 F ≤ dsum3 G :=
  sum3_le fun i j k => by
    split_ifs with hd
    · exact h i j k hd
    · exact le_rfl

/-- **The typed three-point bound on indices.** -/
theorem typed_sum (S Pp c : ι → ι → ι → ℝ) (H : ι → ι → ℝ)
    (hS : ∀ i, 0 ≤ ∑ j, ∑ k, S i j k)
    (hshare : ∀ i j, i ≠ j → (∑ k, if i ≠ k ∧ j ≠ k then Pp i j k else 0)
      = H i j - (S i i j + S i j i + S i j j + S j j i + S j i j + S j i i))
    (hlam : ∀ i j k, Distinct3 i j k →
      c i j k ≤ Pp i j k + Pp i k j + Pp j k i - 2 * (S i j k + S j i k + S k i j)) :
    dsum3 c ≤ 3 * (∑ i, ∑ j, if i ≠ j then H i j else 0) + 6 * ∑ i, S i i i := by
  -- the inequality of the triple types, summed
  have hA : dsum3 c ≤ 3 * dsum3 Pp - 6 * dsum3 S := by
    have h1 := dsum3_le hlam
    have e : dsum3 (fun i j k => Pp i j k + Pp i k j + Pp j k i - 2 * (S i j k + S j i k + S k i j))
        = 3 * dsum3 Pp - 6 * dsum3 S := by
      have e1 : (fun i j k => Pp i j k + Pp i k j + Pp j k i - 2 * (S i j k + S j i k + S k i j))
          = fun i j k => (Pp i j k + (Pp i k j + (Pp j k i + ((-2) * S i j k + ((-2) * S j i k + (-2) * S k i j))))) := by
        funext i j k
        ring
      rw [e1, dsum3_add, dsum3_add, dsum3_add, dsum3_add, dsum3_add, dsum3_smul, dsum3_smul, dsum3_smul,
        dsum3_swap23 Pp, dsum3_231 Pp, dsum3_swap12 S, dsum3_312 S]
      ring
    linarith
  -- the share equation, summed over the pairs
  set E2 := ∑ i, ∑ j, if i ≠ j then S i i j + S i j i + S i j j else 0 with hE2
  have hB : dsum3 Pp = (∑ i, ∑ j, if i ≠ j then H i j else 0) - 2 * E2 := by
    have e1 : dsum3 Pp = ∑ i, ∑ j, if i ≠ j then
        H i j - (S i i j + S i j i + S i j j + S j j i + S j i j + S j i i) else 0 := by
      unfold dsum3 sum3
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      by_cases h : i = j
      · subst h
        simp [Distinct3]
      · rw [if_pos h, ← hshare i j h]
        refine sum_congr rfl fun k _ => ?_
        exact if_congr ⟨fun ⟨_, h2, h3⟩ => ⟨h2, h3⟩, fun ⟨h2, h3⟩ => ⟨h, h2, h3⟩⟩ rfl rfl
    have e2 : (∑ i, ∑ j, if i ≠ j then S j j i + S j i j + S j i i else 0) = E2 := by
      rw [hE2, sum_comm]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      exact if_congr ⟨fun h => h.symm, fun h => h.symm⟩ rfl rfl
    rw [e1, ← e2]
    have e3 : ∀ i j, (if i ≠ j then H i j - (S i i j + S i j i + S i j j + S j j i + S j i j + S j i i) else 0)
        = (if i ≠ j then H i j else 0) - (if i ≠ j then S i i j + S i j i + S i j j else 0)
          - (if i ≠ j then S j j i + S j i j + S j i i else 0) := fun i j => by
      split_ifs <;> ring
    simp only [e3, sum_sub_distrib]
    rw [e2]
    ring
  -- the positivity of the rooted forms, summed over the roots
  have hC : 0 ≤ dsum3 S + E2 + ∑ i, S i i i := by
    have h1 : 0 ≤ sum3 S := sum_nonneg fun i _ => hS i
    rw [sum3_split] at h1
    have e : E2 = (∑ i, ∑ j, if i ≠ j then S i j j else 0) + (∑ i, ∑ k, if i ≠ k then S i i k else 0)
        + (∑ i, ∑ j, if i ≠ j then S i j i else 0) := by
      rw [hE2, ← sum_add_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_add_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    unfold dsum3
    linarith
  linarith

end CAP.Wsos
