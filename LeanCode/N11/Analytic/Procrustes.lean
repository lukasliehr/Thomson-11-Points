module

public import N11.Analytic.Basic
public import N11.Local.Sums

/-!
# The theorem for 11 points, analytic part: an inequality of Procrustes type, and the gauge (row A7)

Configurations are functions `ℕ → ℕ → ℝ` as in `N11/Local`. For a configuration `y` and the reference `p` let
`d = y - p` (`dsub y p`), and let `N`, `T`, `R` be the `3 × 3` matrices `N_kl = ∑_i d_ik d_il`,
`T_kl = ∑_i d_ik p_il`, `R_kl = ∑_i p_ik p_il`; then `S = T + R` is `S_kl = ∑_i y_ik p_il`.

* `bilin`: `∑_{i,j} <A_i, B_j> <C_i, D_j> = ∑_{k,l} (∑_i A_ik C_il) (∑_j B_jk D_jl)`;
* `procrustes`: if `S` is symmetric and positive semidefinite, then
  `∑_{i,j} (<y_i, y_j> - <p_i, p_j>)² ≥ (2/3) ∑_{i,j} <p_i, d_j>²`. Indeed, with `T` symmetric the left side is
  `∑_{kl} N² + 4 N T + 2 T² + 2 N R = ∑_{kl} (N + (4/3) T)² + (2/9) T² + (4/3) N S + (2/3) N R`, and
  `∑_{kl} N_kl S_kl = ∑_i d_iᵀ S d_i ≥ 0`, `∑_{kl} N_kl R_kl = ∑_{i,j} <p_i, d_j>²`;
* `gauge_term`: the second term of the penalty `penf p x` of G7 is `(1/2) ∑_{kl} (T_kl - T_lk)²` with
  `T_kl = ∑_i x_ik p_il` (the identity of Lagrange); `penf_of_sym`: it vanishes if `T` is symmetric.
-/

@[expose] public section

namespace N11.Analytic

open Finset N11.Local

/-- The difference of two configurations. -/
def dsub (y p : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ := fun i k => y i k - p i k

/-- **A rearrangement of a sum of products of inner products.** -/
theorem bilin (A B C D : ℕ → ℕ → ℝ) :
    ∑ i ∈ range 11, ∑ j ∈ range 11, dot (A i) (B j) * dot (C i) (D j)
      = ∑ k ∈ range 3, ∑ l ∈ range 3, (∑ i ∈ range 11, A i k * C i l) * (∑ j ∈ range 11, B j k * D j l) := by
  have e1 : ∀ i j, dot (A i) (B j) * dot (C i) (D j)
      = ∑ k ∈ range 3, ∑ l ∈ range 3, A i k * C i l * (B j k * D j l) := by
    intro i j
    unfold dot
    rw [Finset.sum_mul_sum]
    exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
  have e2 : ∀ k l, (∑ i ∈ range 11, A i k * C i l) * (∑ j ∈ range 11, B j k * D j l)
      = ∑ i ∈ range 11, ∑ j ∈ range 11, A i k * C i l * (B j k * D j l) := fun k l => Finset.sum_mul_sum _ _ _ _
  simp only [e1, e2]
  exact sum_comm22 11 3 (fun i j k l => A i k * C i l * (B j k * D j l))

theorem dot_sub_expand (p y : ℕ → ℕ → ℝ) (i j : ℕ) :
    dot (y i) (y j) - dot (p i) (p j) = dot (p i) (dsub y p j) + dot (dsub y p i) (p j)
      + dot (dsub y p i) (dsub y p j) := by
  unfold dsub
  simp only [dot_eq]
  ring

/-- **The inequality of Procrustes type.** -/
theorem procrustes (p y : ℕ → ℕ → ℝ)
    (hsym : ∀ k l, k < 3 → l < 3 → ∑ i ∈ range 11, y i k * p i l = ∑ i ∈ range 11, y i l * p i k)
    (hpsd : ∀ u : ℕ → ℝ, 0 ≤ ∑ k ∈ range 3, ∑ l ∈ range 3, u k * u l * ∑ i ∈ range 11, y i k * p i l) :
    2 / 3 * ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p i) (dsub y p j) ^ 2
      ≤ ∑ i ∈ range 11, ∑ j ∈ range 11, (dot (y i) (y j) - dot (p i) (p j)) ^ 2 := by
  set d := dsub y p with hd
  -- the matrices
  set N : ℕ → ℕ → ℝ := fun k l => ∑ i ∈ range 11, d i k * d i l with hN
  set T : ℕ → ℕ → ℝ := fun k l => ∑ i ∈ range 11, d i k * p i l with hT
  set R : ℕ → ℕ → ℝ := fun k l => ∑ i ∈ range 11, p i k * p i l with hR
  have hS : ∀ k l, ∑ i ∈ range 11, y i k * p i l = T k l + R k l := by
    intro k l
    rw [hT, hR, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [hd]
    unfold dsub
    ring
  have hTs : ∀ k l, k < 3 → l < 3 → T l k = T k l := by
    intro k l hk hl
    have h1 := hsym k l hk hl
    rw [hS, hS] at h1
    have h2 : R k l = R l k := by
      rw [hR]
      exact sum_congr rfl fun i _ => by ring
    linarith
  -- the six sums
  have s1 : ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p i) (d j) * dot (p i) (d j)
      = ∑ k ∈ range 3, ∑ l ∈ range 3, R k l * N k l := bilin p d p d
  have s2 : ∑ i ∈ range 11, ∑ j ∈ range 11, dot (d i) (p j) * dot (d i) (p j)
      = ∑ k ∈ range 3, ∑ l ∈ range 3, N k l * R k l := bilin d p d p
  have s3 : ∑ i ∈ range 11, ∑ j ∈ range 11, dot (d i) (d j) * dot (d i) (d j)
      = ∑ k ∈ range 3, ∑ l ∈ range 3, N k l * N k l := bilin d d d d
  have s4 : ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p i) (d j) * dot (d i) (p j)
      = ∑ k ∈ range 3, ∑ l ∈ range 3, T l k * T k l := by
    rw [bilin p d d p]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    rw [hT]
    simp only
    congr 1
    exact sum_congr rfl fun i _ => by ring
  have s5 : ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p i) (d j) * dot (d i) (d j)
      = ∑ k ∈ range 3, ∑ l ∈ range 3, T l k * N k l := by
    rw [bilin p d d d]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    rw [hT]
    simp only
    congr 1
    exact sum_congr rfl fun i _ => by ring
  have s6 : ∑ i ∈ range 11, ∑ j ∈ range 11, dot (d i) (p j) * dot (d i) (d j)
      = ∑ k ∈ range 3, ∑ l ∈ range 3, N k l * T l k := by
    rw [bilin d p d d]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    rw [hT]
    simp only
    congr 1
    exact sum_congr rfl fun j _ => by ring
  -- the left side
  have hL : ∑ i ∈ range 11, ∑ j ∈ range 11, (dot (y i) (y j) - dot (p i) (p j)) ^ 2
      = ∑ k ∈ range 3, ∑ l ∈ range 3,
          (2 * R k l * N k l + N k l * N k l + 2 * T k l * T k l + 4 * T k l * N k l) := by
    have e : ∀ i j, (dot (y i) (y j) - dot (p i) (p j)) ^ 2
        = dot (p i) (d j) * dot (p i) (d j) + dot (d i) (p j) * dot (d i) (p j) + dot (d i) (d j) * dot (d i) (d j)
          + 2 * (dot (p i) (d j) * dot (d i) (p j)) + 2 * (dot (p i) (d j) * dot (d i) (d j))
          + 2 * (dot (d i) (p j) * dot (d i) (d j)) := by
      intro i j
      rw [dot_sub_expand p y i j]
      ring
    simp only [e, sum_add_distrib, ← Finset.mul_sum]
    rw [s1, s2, s3, s4, s5, s6]
    simp only [Finset.mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => sum_congr rfl fun l hl => ?_
    rw [hTs k l (mem_range.mp hk) (mem_range.mp hl)]
    ring
  -- positivity of `∑ N S`
  have hNS : 0 ≤ ∑ k ∈ range 3, ∑ l ∈ range 3, N k l * (T k l + R k l) := by
    have e : ∑ k ∈ range 3, ∑ l ∈ range 3, N k l * (T k l + R k l)
        = ∑ i ∈ range 11, ∑ k ∈ range 3, ∑ l ∈ range 3, d i k * d i l * ∑ j ∈ range 11, y j k * p j l := by
      symm
      rw [Finset.sum_comm]
      refine sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine sum_congr rfl fun l _ => ?_
      rw [hS, hN]
      simp only
      rw [Finset.sum_mul]
    rw [e]
    exact sum_nonneg fun i _ => hpsd (d i)
  have hRN : ∑ k ∈ range 3, ∑ l ∈ range 3, R k l * N k l
      = ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p i) (d j) ^ 2 := by
    rw [← s1]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have key : ∑ k ∈ range 3, ∑ l ∈ range 3,
        (2 * R k l * N k l + N k l * N k l + 2 * T k l * T k l + 4 * T k l * N k l)
      = ∑ k ∈ range 3, ∑ l ∈ range 3, ((N k l + 4 / 3 * T k l) ^ 2 + 2 / 9 * T k l ^ 2)
        + 4 / 3 * ∑ k ∈ range 3, ∑ l ∈ range 3, N k l * (T k l + R k l)
        + 2 / 3 * ∑ k ∈ range 3, ∑ l ∈ range 3, R k l * N k l := by
    simp only [Finset.mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
  have hsq : 0 ≤ ∑ k ∈ range 3, ∑ l ∈ range 3, ((N k l + 4 / 3 * T k l) ^ 2 + 2 / 9 * T k l ^ 2) :=
    sum_nonneg fun k _ => sum_nonneg fun l _ => by positivity
  rw [hL, key, hRN]
  linarith

/-- **The gauge term of the penalty** (the identity of Lagrange). -/
theorem gauge_term (p x : ℕ → ℕ → ℝ) :
    ∑ i ∈ range 11, ∑ j ∈ range 11, (dot (p i) (p j) * dot (x i) (x j) - dot (p i) (x j) * dot (x i) (p j))
      = 1 / 2 * ∑ k ∈ range 3, ∑ l ∈ range 3,
          (∑ i ∈ range 11, x i k * p i l - ∑ i ∈ range 11, x i l * p i k) ^ 2 := by
  set W : ℕ → ℕ → ℝ := fun k l => ∑ i ∈ range 11, p i k * x i l with hW
  have h1 : ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p i) (p j) * dot (x i) (x j)
      = ∑ k ∈ range 3, ∑ l ∈ range 3, W k l * W k l := bilin p p x x
  have h2 : ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p i) (x j) * dot (x i) (p j)
      = ∑ k ∈ range 3, ∑ l ∈ range 3, W k l * W l k := by
    rw [bilin p x x p]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    rw [hW]
    simp only
    congr 1
    exact sum_congr rfl fun j _ => by ring
  have h3 : ∑ k ∈ range 3, ∑ l ∈ range 3, W l k * W l k = ∑ k ∈ range 3, ∑ l ∈ range 3, W k l * W k l :=
    Finset.sum_comm
  have hx : ∀ k l, ∑ i ∈ range 11, x i k * p i l = W l k := by
    intro k l
    rw [hW]
    exact sum_congr rfl fun i _ => by ring
  simp only [hx]
  rw [sum2_sub, h1, h2]
  have e : ∑ k ∈ range 3, ∑ l ∈ range 3, (W l k - W k l) ^ 2
      = ∑ k ∈ range 3, ∑ l ∈ range 3, W l k * W l k + ∑ k ∈ range 3, ∑ l ∈ range 3, W k l * W k l
        - 2 * ∑ k ∈ range 3, ∑ l ∈ range 3, W k l * W l k := by
    simp only [Finset.mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
  rw [e, h3]
  ring

/-- **The penalty of a displacement in the gauge.** -/
theorem penf_of_sym (p x : ℕ → ℕ → ℝ)
    (hT : ∀ k l, k < 3 → l < 3 → ∑ i ∈ range 11, x i k * p i l = ∑ i ∈ range 11, x i l * p i k) :
    penf p x = ∑ i ∈ range 11, dot (p i) (x i) ^ 2 := by
  unfold penf
  rw [gauge_term]
  have h0 : ∑ k ∈ range 3, ∑ l ∈ range 3,
      (∑ i ∈ range 11, x i k * p i l - ∑ i ∈ range 11, x i l * p i k) ^ 2 = 0 := by
    refine sum_eq_zero fun k hk => sum_eq_zero fun l hl => ?_
    rw [hT k l (mem_range.mp hk) (mem_range.mp hl), sub_self]
    ring
  rw [h0, mul_zero, add_zero]

end N11.Analytic
