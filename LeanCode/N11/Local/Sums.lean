module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# G7 of route G: sums over the coordinates of a configuration

A coordinate of a configuration of eleven points has the flat index `k = 3 u + c` with the point `u < 11` and
`c < 3`. The lemmas of this file do not depend on the data.

* `sum_flat`: a sum over the flat indices is the sum over the points and the coordinates.
* `sum_mul3`, `sum_mul21`: a triple sum with a table that is a product is a product of sums.
* `sum3_six`: the six orders of the indices of a table of a cubic form give the same form.
* `flatten`: the square of a cubic form is at most the quadratic form of the Gram matrix of its flattening (along
  the middle index) times the cube of the square of the norm. (The Cauchy–Schwarz inequality.)
* `tri_full`: the quadratic form of a table from the upper triangle of its symmetric matrix.
* `dl`: the indicator of the diagonal; `sumP`: the sum over the pairs `i < j < 11`; `sumP_quad`, `sumP_cub`: the
  form of a sum of tables over the pairs is the sum of the forms.
-/

@[expose] public section

namespace N11.Local

open Finset

theorem sum_range_three_mul (F : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range (3 * n), F k = ∑ u ∈ range n, ∑ c ∈ range 3, F (3 * u + c) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun u => ∑ c ∈ range 3, F (3 * u + c)) n]
    simp only [sum_range_succ, sum_range_zero]
    show _ + F (3 * n) + F (3 * n + 1) + F (3 * n + 2) = _ + (0 + F (3 * n) + F (3 * n + 1) + F (3 * n + 2))
    ring

/-- A sum over the flat indices is the sum over the points and the coordinates. -/
theorem sum_flat (F : ℕ → ℕ → ℝ) :
    ∑ k ∈ range 33, F (k / 3) (k % 3) = ∑ u ∈ range 11, ∑ c ∈ range 3, F u c := by
  have h := sum_range_three_mul (fun k => F (k / 3) (k % 3)) 11
  have e : 3 * 11 = 33 := by norm_num
  rw [e] at h
  rw [h]
  refine sum_congr rfl fun u _ => sum_congr rfl fun c hc => ?_
  have hc' : c < 3 := mem_range.mp hc
  have e1 : (3 * u + c) / 3 = u := by omega
  have e2 : (3 * u + c) % 3 = c := by omega
  rw [e1, e2]

theorem sum_mul3 (n : ℕ) (f g h z : ℕ → ℝ) :
    ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, f k * g a * h b * z k * z a * z b
      = (∑ k ∈ range n, f k * z k) * (∑ a ∈ range n, g a * z a) * (∑ b ∈ range n, h b * z b) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun b _ => ?_
  ring

theorem sum_mul21 (n : ℕ) (f z : ℕ → ℝ) (M : ℕ → ℕ → ℝ) :
    ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, f k * M a b * z k * z a * z b
      = (∑ k ∈ range n, f k * z k) * (∑ a ∈ range n, ∑ b ∈ range n, M a b * (z a * z b)) := by
  rw [Finset.sum_mul]
  refine sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun b _ => ?_
  ring

theorem sum_mul2 (n : ℕ) (f g z : ℕ → ℝ) :
    ∑ a ∈ range n, ∑ b ∈ range n, f a * g b * z a * z b
      = (∑ a ∈ range n, f a * z a) * (∑ b ∈ range n, g b * z b) := by
  rw [Finset.sum_mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  ring

/-! ## The six orders of the indices -/

theorem sum3_swap23 (n : ℕ) (R : ℕ → ℕ → ℕ → ℝ) (z : ℕ → ℝ) :
    ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R k b a * z k * z a * z b
      = ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R k a b * z k * z a * z b := by
  refine sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  ring

theorem sum3_swap12 (n : ℕ) (R : ℕ → ℕ → ℕ → ℝ) (z : ℕ → ℝ) :
    ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R a k b * z k * z a * z b
      = ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R k a b * z k * z a * z b := by
  rw [Finset.sum_comm]
  refine sum_congr rfl fun k _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  ring

/-- The sum of a table over the six orders of its indices gives six times its cubic form. -/
theorem sum3_six (n : ℕ) (R : ℕ → ℕ → ℕ → ℝ) (z : ℕ → ℝ) :
    ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n,
        (R k a b + R k b a + R a k b + R a b k + R b k a + R b a k) * z k * z a * z b
      = 6 * ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R k a b * z k * z a * z b := by
  have e2 := sum3_swap23 n R z
  have e3 := sum3_swap12 n R z
  have e4 : ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R a b k * z k * z a * z b
      = ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R k a b * z k * z a * z b := by
    rw [sum3_swap12 n (fun x y w => R x w y) z]
    exact sum3_swap23 n R z
  have e5 : ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R b k a * z k * z a * z b
      = ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R k a b * z k * z a * z b := by
    rw [sum3_swap23 n (fun x y w => R y x w) z]
    exact sum3_swap12 n R z
  have e6 : ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R b a k * z k * z a * z b
      = ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R k a b * z k * z a * z b := by
    rw [sum3_swap23 n (fun x y w => R y w x) z]
    exact e4
  have split : ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n,
        (R k a b + R k b a + R a k b + R a b k + R b k a + R b a k) * z k * z a * z b
      = ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R k a b * z k * z a * z b
        + ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R k b a * z k * z a * z b
        + ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R a k b * z k * z a * z b
        + ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R a b k * z k * z a * z b
        + ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R b k a * z k * z a * z b
        + ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, R b a k * z k * z a * z b := by
    simp only [← sum_add_distrib]
    refine sum_congr rfl fun k _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    ring
  rw [split, e2, e3, e4, e5, e6]
  ring

/-! ## The flattening -/

theorem sum_comm22 (m n : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ a ∈ range m, ∑ a' ∈ range m, ∑ b ∈ range n, ∑ k ∈ range n, F a a' b k
      = ∑ b ∈ range n, ∑ k ∈ range n, ∑ a ∈ range m, ∑ a' ∈ range m, F a a' b k := by
  calc ∑ a ∈ range m, ∑ a' ∈ range m, ∑ b ∈ range n, ∑ k ∈ range n, F a a' b k
      = ∑ a ∈ range m, ∑ b ∈ range n, ∑ a' ∈ range m, ∑ k ∈ range n, F a a' b k :=
        sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ b ∈ range n, ∑ a ∈ range m, ∑ a' ∈ range m, ∑ k ∈ range n, F a a' b k := Finset.sum_comm
    _ = ∑ b ∈ range n, ∑ a ∈ range m, ∑ k ∈ range n, ∑ a' ∈ range m, F a a' b k :=
        sum_congr rfl fun b _ => sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ b ∈ range n, ∑ k ∈ range n, ∑ a ∈ range m, ∑ a' ∈ range m, F a a' b k :=
        sum_congr rfl fun b _ => Finset.sum_comm

theorem sum_comm32 (m n : ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, ∑ i ∈ range n, ∑ j ∈ range n, F k a b i j
      = ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, F k a b i j := by
  calc ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, ∑ i ∈ range n, ∑ j ∈ range n, F k a b i j
      = ∑ k ∈ range m, ∑ i ∈ range n, ∑ j ∈ range n, ∑ a ∈ range m, ∑ b ∈ range m, F k a b i j :=
        sum_congr rfl fun k _ => sum_comm22 m n (fun a b i j => F k a b i j)
    _ = ∑ i ∈ range n, ∑ k ∈ range m, ∑ j ∈ range n, ∑ a ∈ range m, ∑ b ∈ range m, F k a b i j := Finset.sum_comm
    _ = ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, F k a b i j :=
        sum_congr rfl fun i _ => Finset.sum_comm

/-- **The flattening of a cubic form along its middle index.** -/
theorem flatten (n : ℕ) (T : ℕ → ℕ → ℕ → ℝ) (z : ℕ → ℝ) :
    (∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, T k a b * z k * z a * z b) ^ 2
      ≤ (∑ a ∈ range n, ∑ a' ∈ range n, (∑ b ∈ range n, ∑ k ∈ range n, T k a b * T k a' b) * (z a * z a'))
        * (∑ k ∈ range n, z k ^ 2) ^ 2 := by
  have h1 : ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, T k a b * z k * z a * z b
      = ∑ p ∈ range n ×ˢ range n, (∑ a ∈ range n, T p.2 a p.1 * z a) * (z p.1 * z p.2) := by
    rw [Finset.sum_product]
    calc ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n, T k a b * z k * z a * z b
        = ∑ k ∈ range n, ∑ b ∈ range n, ∑ a ∈ range n, T k a b * z k * z a * z b :=
          sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ b ∈ range n, ∑ k ∈ range n, ∑ a ∈ range n, T k a b * z k * z a * z b := Finset.sum_comm
      _ = ∑ b ∈ range n, ∑ k ∈ range n, (∑ a ∈ range n, T k a b * z a) * (z b * z k) := by
          refine sum_congr rfl fun b _ => sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine sum_congr rfl fun a _ => ?_
          ring
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (range n ×ˢ range n)
    (fun p => ∑ a ∈ range n, T p.2 a p.1 * z a) (fun p => z p.1 * z p.2)
  have h3 : ∑ p ∈ range n ×ˢ range n, (z p.1 * z p.2) ^ 2 = (∑ k ∈ range n, z k ^ 2) ^ 2 := by
    rw [Finset.sum_product, sq (∑ k ∈ range n, z k ^ 2), Finset.sum_mul_sum]
    refine sum_congr rfl fun b _ => sum_congr rfl fun k _ => ?_
    ring
  have h4 : ∑ p ∈ range n ×ˢ range n, (∑ a ∈ range n, T p.2 a p.1 * z a) ^ 2
      = ∑ a ∈ range n, ∑ a' ∈ range n, (∑ b ∈ range n, ∑ k ∈ range n, T k a b * T k a' b) * (z a * z a') := by
    rw [Finset.sum_product]
    have e : ∑ a ∈ range n, ∑ a' ∈ range n, (∑ b ∈ range n, ∑ k ∈ range n, T k a b * T k a' b) * (z a * z a')
        = ∑ a ∈ range n, ∑ a' ∈ range n, ∑ b ∈ range n, ∑ k ∈ range n, T k a b * T k a' b * (z a * z a') := by
      refine sum_congr rfl fun a _ => sum_congr rfl fun a' _ => ?_
      rw [Finset.sum_mul]
      refine sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul]
    rw [e, sum_comm22 n n (fun a a' b k => T k a b * T k a' b * (z a * z a'))]
    refine sum_congr rfl fun b _ => sum_congr rfl fun k _ => ?_
    rw [sq, Finset.sum_mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun a' _ => ?_
    ring
  rw [h1]
  rw [h3, h4] at h2
  exact h2

/-! ## The upper triangle -/

/-- The quadratic form of a table `M`, from the upper triangle `X` of its symmetric matrix. -/
theorem tri_full (n : ℕ) (M X : ℕ → ℕ → ℝ) (v : ℕ → ℝ) (hd : ∀ i, i < n → X i i = M i i)
    (ho : ∀ i j, i < j → j < n → X i j = M i j + M j i) :
    ∑ i ∈ range n, ∑ j ∈ range n, (if i ≤ j then X i j * (v i * v j) else 0)
      = ∑ i ∈ range n, ∑ j ∈ range n, M i j * (v i * v j) := by
  have hsplit : ∀ i j, M i j * (v i * v j) = ((if i < j then M i j * (v i * v j) else 0)
      + (if i = j then M i j * (v i * v j) else 0)) + (if j < i then M i j * (v i * v j) else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · rw [if_pos h, if_neg (ne_of_lt h), if_neg (not_lt.mpr h.le)]
      ring
    · subst h
      rw [if_neg (lt_irrefl _), if_pos rfl]
      ring
    · rw [if_neg (not_lt.mpr h.le), if_neg (ne_of_gt h), if_pos h]
      ring
  have hswap : ∑ i ∈ range n, ∑ j ∈ range n, (if j < i then M i j * (v i * v j) else 0)
      = ∑ i ∈ range n, ∑ j ∈ range n, (if i < j then M j i * (v i * v j) else 0) := by
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases h : i < j
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
  have hR : ∑ i ∈ range n, ∑ j ∈ range n, M i j * (v i * v j)
      = ∑ i ∈ range n, ∑ j ∈ range n, (((if i < j then M i j * (v i * v j) else 0)
          + (if i = j then M i j * (v i * v j) else 0)) + (if i < j then M j i * (v i * v j) else 0)) := by
    have e : ∑ i ∈ range n, ∑ j ∈ range n, (((if i < j then M i j * (v i * v j) else 0)
          + (if i = j then M i j * (v i * v j) else 0)) + (if i < j then M j i * (v i * v j) else 0))
        = ∑ i ∈ range n, ∑ j ∈ range n, ((if i < j then M i j * (v i * v j) else 0)
            + (if i = j then M i j * (v i * v j) else 0))
          + ∑ i ∈ range n, ∑ j ∈ range n, (if i < j then M j i * (v i * v j) else 0) := by
      simp only [sum_add_distrib]
    rw [e, ← hswap]
    simp only [← sum_add_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => hsplit i j
  rw [hR]
  refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
  have hi' := mem_range.mp hi
  have hj' := mem_range.mp hj
  rcases lt_trichotomy i j with h | h | h
  · rw [if_pos h.le, if_pos h, if_neg (ne_of_lt h), if_pos h, ho i j h hj']
    ring
  · subst h
    rw [if_pos le_rfl, if_neg (lt_irrefl _), if_pos rfl, hd i hi']
    ring
  · rw [if_neg (not_le.mpr h), if_neg (not_lt.mpr h.le), if_neg (ne_of_gt h), if_neg (not_lt.mpr h.le)]
    ring

/-! ## Double sums -/

theorem sum2_add (m : ℕ) (f g : ℕ → ℕ → ℝ) :
    ∑ k ∈ range m, ∑ l ∈ range m, (f k l + g k l)
      = ∑ k ∈ range m, ∑ l ∈ range m, f k l + ∑ k ∈ range m, ∑ l ∈ range m, g k l := by
  simp only [sum_add_distrib]

theorem sum2_sub (m : ℕ) (f g : ℕ → ℕ → ℝ) :
    ∑ k ∈ range m, ∑ l ∈ range m, (f k l - g k l)
      = ∑ k ∈ range m, ∑ l ∈ range m, f k l - ∑ k ∈ range m, ∑ l ∈ range m, g k l := by
  simp only [sum_sub_distrib]

theorem sum2_mul (m : ℕ) (s : ℝ) (f : ℕ → ℕ → ℝ) :
    ∑ k ∈ range m, ∑ l ∈ range m, s * f k l = s * ∑ k ∈ range m, ∑ l ∈ range m, f k l := by
  simp only [Finset.mul_sum]

/-! ## Triple sums -/

theorem sum3_add (m : ℕ) (f g : ℕ → ℕ → ℕ → ℝ) :
    ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, (f k a b + g k a b)
      = ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, f k a b
        + ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, g k a b := by
  simp only [sum_add_distrib]

theorem sum3_sub (m : ℕ) (f g : ℕ → ℕ → ℕ → ℝ) :
    ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, (f k a b - g k a b)
      = ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, f k a b
        - ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, g k a b := by
  simp only [sum_sub_distrib]

theorem sum3_mul (m : ℕ) (s : ℝ) (f : ℕ → ℕ → ℕ → ℝ) :
    ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, s * f k a b
      = s * ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, f k a b := by
  simp only [Finset.mul_sum]

/-! ## The indicator of the diagonal -/

/-- `1` if `a = b`, and `0` otherwise. -/
def dl (a b : ℕ) : ℝ := if a = b then 1 else 0

theorem dl_self (a : ℕ) : dl a a = 1 := by
  unfold dl
  exact if_pos rfl

theorem dl_ne {a b : ℕ} (h : a ≠ b) : dl a b = 0 := by
  unfold dl
  exact if_neg h

theorem dl_comm (a b : ℕ) : dl a b = dl b a := by
  unfold dl
  by_cases h : a = b
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem sum_dl (n i : ℕ) (hi : i < n) (f : ℕ → ℝ) : ∑ u ∈ range n, dl u i * f u = f i := by
  rw [Finset.sum_eq_single i]
  · rw [dl_self, one_mul]
  · intro u _ hu
    rw [dl_ne hu, zero_mul]
  · intro h
    exact absurd (mem_range.mpr hi) h

theorem sum_dl' (n i : ℕ) (hi : i < n) (f : ℕ → ℝ) : ∑ u ∈ range n, dl i u * f u = f i := by
  rw [← sum_dl n i hi f]
  exact sum_congr rfl fun u _ => by rw [dl_comm]

/-! ## The sum over the pairs -/

/-- The sum over the pairs `i < j < 11`. -/
def sumP (F : ℕ → ℕ → ℝ) : ℝ := ∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then F i j else 0

theorem sumP_congr {F G : ℕ → ℕ → ℝ} (h : ∀ i j, i < j → j < 11 → F i j = G i j) : sumP F = sumP G := by
  unfold sumP
  refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
  by_cases hij : i < j
  · rw [if_pos hij, if_pos hij, h i j hij (mem_range.mp hj)]
  · rw [if_neg hij, if_neg hij]

theorem sumP_mul (s : ℝ) (F : ℕ → ℕ → ℝ) : sumP (fun i j => s * F i j) = s * sumP F := by
  unfold sumP
  rw [Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun j _ => ?_
  by_cases hij : i < j
  · rw [if_pos hij, if_pos hij]
  · rw [if_neg hij, if_neg hij, mul_zero]

/-- The quadratic form of a sum of tables over the pairs. -/
theorem sumP_quad (m : ℕ) (G : ℕ → ℕ → ℕ → ℕ → ℝ) (w : ℕ → ℕ → ℝ) :
    ∑ k ∈ range m, ∑ l ∈ range m, (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then G i j k l else 0) * w k l
      = sumP fun i j => ∑ k ∈ range m, ∑ l ∈ range m, G i j k l * w k l := by
  have e1 : ∀ k l, (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then G i j k l else 0) * w k l
      = ∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then G i j k l * w k l else 0 := by
    intro k l
    rw [Finset.sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [ite_mul, zero_mul]
  have e2 : ∀ i j, (∑ k ∈ range m, ∑ l ∈ range m, if i < j then G i j k l * w k l else 0)
      = if i < j then ∑ k ∈ range m, ∑ l ∈ range m, G i j k l * w k l else 0 := by
    intro i j
    by_cases h : i < j
    · simp only [if_pos h]
    · simp only [if_neg h, sum_const_zero]
  calc ∑ k ∈ range m, ∑ l ∈ range m, (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then G i j k l else 0) * w k l
      = ∑ k ∈ range m, ∑ l ∈ range m, ∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then G i j k l * w k l else 0 :=
        sum_congr rfl fun k _ => sum_congr rfl fun l _ => e1 k l
    _ = ∑ i ∈ range 11, ∑ j ∈ range 11, ∑ k ∈ range m, ∑ l ∈ range m, if i < j then G i j k l * w k l else 0 :=
        sum_comm22 m 11 (fun k l i j => if i < j then G i j k l * w k l else 0)
    _ = sumP fun i j => ∑ k ∈ range m, ∑ l ∈ range m, G i j k l * w k l :=
        sum_congr rfl fun i _ => sum_congr rfl fun j _ => e2 i j

/-- The cubic form of a sum of tables over the pairs. -/
theorem sumP_cub (m : ℕ) (G : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) (z : ℕ → ℝ) :
    ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m,
        (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then G i j k a b else 0) * z k * z a * z b
      = sumP fun i j => ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, G i j k a b * z k * z a * z b := by
  have e1 : ∀ k a b, (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then G i j k a b else 0) * z k * z a * z b
      = ∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then G i j k a b * z k * z a * z b else 0 := by
    intro k a b
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : i < j
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_mul, zero_mul, zero_mul]
  have e2 : ∀ i j, (∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m,
        if i < j then G i j k a b * z k * z a * z b else 0)
      = if i < j then ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, G i j k a b * z k * z a * z b else 0 := by
    intro i j
    by_cases h : i < j
    · simp only [if_pos h]
    · simp only [if_neg h, sum_const_zero]
  calc ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m,
        (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then G i j k a b else 0) * z k * z a * z b
      = ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, ∑ i ∈ range 11, ∑ j ∈ range 11,
          if i < j then G i j k a b * z k * z a * z b else 0 :=
        sum_congr rfl fun k _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => e1 k a b
    _ = ∑ i ∈ range 11, ∑ j ∈ range 11, ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m,
          if i < j then G i j k a b * z k * z a * z b else 0 :=
        sum_comm32 m 11 (fun k a b i j => if i < j then G i j k a b * z k * z a * z b else 0)
    _ = sumP fun i j => ∑ k ∈ range m, ∑ a ∈ range m, ∑ b ∈ range m, G i j k a b * z k * z a * z b :=
        sum_congr rfl fun i _ => sum_congr rfl fun j _ => e2 i j

end N11.Local
