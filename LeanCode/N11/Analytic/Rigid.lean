module

public import N11.Analytic.Procrustes
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.BigOperators.Field

/-!
# The theorem for 11 points, analytic part: the rigidity bound (row A8)

Let `y` be a configuration whose points lie on the spheres of the radii `|p_i|` (`|y_i|² = |p_i|²`), aligned with the
reference configuration `p` (the matrix `S = ∑_i y_i p_iᵀ` is symmetric and positive semidefinite), and let
`Δ_ij = <y_i, y_j> - <p_i, p_j>` with `∑_{i<j} Δ_ij² ≤ δ2`. Let `d = y - p` and `X = |d|²`. Then
`2 <p_i, d_i> + |d_i|² = 0`, and the gauge makes the penalty `penf p d = ∑_i <p_i, d_i>² = ∑_i |d_i|⁴ / 4`.

* `rigid_apriori`: `σ² X ≤ 3 K δ2`. By the field `rig` of G7, `σ² X ≤ ∑_{i<j} L_ij(d)² + K penf p d`, which is at most
  `K ∑_{i,j} <p_i, d_j>²` for `K ≥ 2`, and by the inequality of Procrustes type this is at most
  `(3/2) K ∑_{i,j} Δ_ij² = 3 K ∑_{i<j} Δ_ij²`. This excludes the branch of large displacements.
* `rigid_refine`: if `X ≤ X0`, then `(σ² - ((1 + 1/θ)/2 + K/4) X0) X ≤ (1 + θ) δ2` for every `θ > 0`, since
  `L_ij(d) = Δ_ij - <d_i, d_j>`, `∑_{i<j} <d_i, d_j>² ≤ X² / 2` and `penf p d ≤ X² / 4`.
-/

@[expose] public section

namespace N11.Analytic

open Finset N11.Local

theorem sq_sub_le (a b θ : ℝ) (hθ : 0 < θ) : (a - b) ^ 2 ≤ (1 + θ) * a ^ 2 + (1 + 1 / θ) * b ^ 2 := by
  have h1 : θ * a ^ 2 + b ^ 2 / θ + 2 * a * b = (θ * a + b) ^ 2 / θ := by
    field_simp
    ring
  have h2 : 0 ≤ (θ * a + b) ^ 2 / θ := by positivity
  have e : (1 + θ) * a ^ 2 + (1 + 1 / θ) * b ^ 2 - (a - b) ^ 2 = θ * a ^ 2 + b ^ 2 / θ + 2 * a * b := by
    field_simp
    ring
  linarith

theorem sq_add_le (a b θ : ℝ) (hθ : 0 < θ) : (a + b) ^ 2 ≤ (1 + θ) * a ^ 2 + (1 + 1 / θ) * b ^ 2 := by
  have h := sq_sub_le a (-b) θ hθ
  simp only [sub_neg_eq_add, neg_sq] at h
  exact h

/-- The points of `y` lie on the spheres of the radii `|p_i|`. -/
theorem diag_rel {p y : ℕ → ℕ → ℝ} (hy : ∀ i, i < 11 → dot (y i) (y i) = dot (p i) (p i)) {i : ℕ} (hi : i < 11) :
    2 * dot (p i) (dsub y p i) + dot (dsub y p i) (dsub y p i) = 0 := by
  have h := hy i hi
  unfold dsub
  simp only [dot_eq] at h ⊢
  linarith

theorem sum_all_sq {p y : ℕ → ℕ → ℝ} (hy : ∀ i, i < 11 → dot (y i) (y i) = dot (p i) (p i)) :
    ∑ i ∈ range 11, ∑ j ∈ range 11, (dot (y i) (y j) - dot (p i) (p j)) ^ 2
      = 2 * sumP (fun i j => (dot (y i) (y j) - dot (p i) (p j)) ^ 2) := by
  rw [sum_sq_eq_sumP _ fun i j _ _ => by rw [dot_comm (y i), dot_comm (p i)]]
  have h0 : ∑ i ∈ range 11, (dot (y i) (y i) - dot (p i) (p i)) ^ 2 = 0 :=
    sum_eq_zero fun i hi => by rw [hy i (mem_range.mp hi), sub_self]; ring
  rw [h0, add_zero]

/-- The square of a sum of nonnegative numbers bounds the sum of the products of the pairs. -/
theorem sumP_prod_le (D : ℕ → ℝ) (hD : ∀ i, i < 11 → 0 ≤ D i) :
    sumP (fun i j => D i * D j) ≤ (∑ i ∈ range 11, D i) ^ 2 / 2 := by
  have h := sum_sq_eq_sumP (fun i j => D i * D j) fun i j _ _ => mul_comm _ _
  have e : (∑ i ∈ range 11, D i) ^ 2 = ∑ i ∈ range 11, ∑ j ∈ range 11, D i * D j := by
    rw [sq, Finset.sum_mul_sum]
  have h2 : 0 ≤ ∑ i ∈ range 11, D i * D i := sum_nonneg fun i hi => mul_self_nonneg _
  rw [e, h]
  linarith

theorem sum_sq_le_sq (D : ℕ → ℝ) (hD : ∀ i, i < 11 → 0 ≤ D i) :
    ∑ i ∈ range 11, D i ^ 2 ≤ (∑ i ∈ range 11, D i) ^ 2 := by
  have h := sum_sq_eq_sumP (fun i j => D i * D j) fun i j _ _ => mul_comm _ _
  have e : (∑ i ∈ range 11, D i) ^ 2 = ∑ i ∈ range 11, ∑ j ∈ range 11, D i * D j := by
    rw [sq, Finset.sum_mul_sum]
  have h2 : 0 ≤ sumP (fun i j => D i * D j) :=
    sumP_nonneg fun i j hij hj => mul_nonneg (hD i (by omega)) (hD j hj)
  rw [e, h]
  have e2 : ∑ i ∈ range 11, D i ^ 2 = ∑ i ∈ range 11, D i * D i := sum_congr rfl fun i _ => sq _
  rw [e2]
  linarith

/-- The form of the rigidity plus the diagonal terms, from the inner products `<p_i, d_j>`. -/
theorem Rf_le (p d : ℕ → ℕ → ℝ) {c : ℝ} (hc : 2 ≤ c) :
    Rf p d + c * ∑ i ∈ range 11, dot (p i) (d i) ^ 2 ≤ c * ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p i) (d j) ^ 2 := by
  have h1 : Rf p d ≤ sumP (fun i j => 2 * (dot (p i) (d j) ^ 2 + dot (p j) (d i) ^ 2)) := by
    unfold Rf
    refine sumP_le fun i j _ _ => ?_
    unfold Lf
    rw [dot_comm (d i) (p j)]
    nlinarith [sq_nonneg (dot (p i) (d j) - dot (p j) (d i))]
  have h2 := sum_sq_eq_sumP (fun i j => dot (p i) (d j) ^ 2 + dot (p j) (d i) ^ 2) fun i j _ _ => by ring
  have e1 : ∑ i ∈ range 11, ∑ j ∈ range 11, (dot (p i) (d j) ^ 2 + dot (p j) (d i) ^ 2)
      = 2 * ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p i) (d j) ^ 2 := by
    rw [sum2_add]
    have e2 : ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p j) (d i) ^ 2
        = ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p i) (d j) ^ 2 := Finset.sum_comm
    rw [e2]
    ring
  have e3 : ∑ i ∈ range 11, (dot (p i) (d i) ^ 2 + dot (p i) (d i) ^ 2)
      = 2 * ∑ i ∈ range 11, dot (p i) (d i) ^ 2 := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [e1, e3] at h2
  rw [sumP_mul] at h1
  have hd : ∑ i ∈ range 11, dot (p i) (d i) ^ 2 ≤ ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p i) (d j) ^ 2 :=
    sum_le_sum fun i hi => single_le_sum (f := fun j => dot (p i) (d j) ^ 2) (fun j _ => sq_nonneg _) hi
  nlinarith

/-- The hypotheses on a configuration `y` aligned with `p`: the points on the spheres of the radii `|p_i|`, the
matrix `∑_i y_i p_iᵀ` symmetric and positive semidefinite. -/
structure Aligned (p y : ℕ → ℕ → ℝ) : Prop where
  sph : ∀ i, i < 11 → dot (y i) (y i) = dot (p i) (p i)
  sym : ∀ k l, k < 3 → l < 3 → ∑ i ∈ range 11, y i k * p i l = ∑ i ∈ range 11, y i l * p i k
  psd : ∀ u : ℕ → ℝ, 0 ≤ ∑ k ∈ range 3, ∑ l ∈ range 3, u k * u l * ∑ i ∈ range 11, y i k * p i l

theorem Aligned.sym_d {p y : ℕ → ℕ → ℝ} (A : Aligned p y) :
    ∀ k l, k < 3 → l < 3 → ∑ i ∈ range 11, dsub y p i k * p i l = ∑ i ∈ range 11, dsub y p i l * p i k := by
  intro k l hk hl
  have h := A.sym k l hk hl
  unfold dsub
  simp only [sub_mul, sum_sub_distrib]
  have e : ∑ i ∈ range 11, p i k * p i l = ∑ i ∈ range 11, p i l * p i k := sum_congr rfl fun i _ => mul_comm _ _
  rw [h, e]

theorem Aligned.penf_d {p y : ℕ → ℕ → ℝ} (A : Aligned p y) :
    penf p (dsub y p) = ∑ i ∈ range 11, dot (dsub y p i) (dsub y p i) ^ 2 / 4 := by
  rw [penf_of_sym p (dsub y p) A.sym_d]
  refine sum_congr rfl fun i hi => ?_
  have h := diag_rel A.sph (mem_range.mp hi)
  have e : dot (p i) (dsub y p i) = -(dot (dsub y p i) (dsub y p i)) / 2 := by linarith
  rw [e]
  ring

/-- **The a priori bound for the displacement.** -/
theorem rigid_apriori {p a b c y : ℕ → ℕ → ℝ} {K : Consts} (G : G7 p a b c K) (hK : 2 ≤ K.penR)
    (A : Aligned p y) {δ2 : ℝ} (hΔ : sumP (fun i j => (dot (y i) (y j) - dot (p i) (p j)) ^ 2) ≤ δ2) :
    K.sigma2 * nsq (dsub y p) ≤ 3 * K.penR * δ2 := by
  have h1 := G.rig (dsub y p)
  have h2 := Rf_le p (dsub y p) hK
  have h3 := procrustes p y A.sym A.psd
  rw [sum_all_sq A.sph] at h3
  have hpen : penf p (dsub y p) = ∑ i ∈ range 11, dot (p i) (dsub y p i) ^ 2 :=
    penf_of_sym p (dsub y p) A.sym_d
  rw [hpen] at h1
  have hM : 0 ≤ ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p i) (dsub y p j) ^ 2 :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  have hK0 : 0 ≤ K.penR := by linarith
  have h4 : K.penR * ∑ i ∈ range 11, ∑ j ∈ range 11, dot (p i) (dsub y p j) ^ 2 ≤ K.penR * (3 * δ2) := by
    apply mul_le_mul_of_nonneg_left _ hK0
    linarith
  linarith

/-- **The rigidity bound.** -/
theorem rigid_refine {p a b c y : ℕ → ℕ → ℝ} {K : Consts} (G : G7 p a b c K) (hK : 0 ≤ K.penR)
    (A : Aligned p y) {δ2 : ℝ} (hΔ : sumP (fun i j => (dot (y i) (y j) - dot (p i) (p j)) ^ 2) ≤ δ2)
    {X0 θ : ℝ} (hθ : 0 < θ) (hX : nsq (dsub y p) ≤ X0) :
    (K.sigma2 - ((1 + 1 / θ) / 2 + K.penR / 4) * X0) * nsq (dsub y p) ≤ (1 + θ) * δ2 := by
  set d := dsub y p with hd
  have h1 := G.rig d
  rw [A.penf_d] at h1
  have hD : ∀ i, i < 11 → 0 ≤ dot (d i) (d i) := fun i _ => dot_self_nonneg _
  have hX0 : 0 ≤ nsq d := nsq_nonneg d
  -- the penalty
  have hpen : ∑ i ∈ range 11, dot (d i) (d i) ^ 2 / 4 ≤ nsq d ^ 2 / 4 := by
    have := sum_sq_le_sq (fun i => dot (d i) (d i)) hD
    unfold nsq
    rw [← Finset.sum_div]
    linarith
  -- the first-order changes
  have hL : ∀ i j, i < j → j < 11 → Lf p d i j ^ 2
      ≤ (1 + θ) * (dot (y i) (y j) - dot (p i) (p j)) ^ 2 + (1 + 1 / θ) * dot (d i) (d j) ^ 2 := by
    intro i j _ _
    have e : Lf p d i j = (dot (y i) (y j) - dot (p i) (p j)) - dot (d i) (d j) := by
      rw [hd, dot_sub_expand p y i j]
      unfold Lf
      ring
    rw [e]
    exact sq_sub_le _ _ θ hθ
  have hdd : sumP (fun i j => dot (d i) (d j) ^ 2) ≤ nsq d ^ 2 / 2 := by
    have h2 : sumP (fun i j => dot (d i) (d j) ^ 2) ≤ sumP (fun i j => dot (d i) (d i) * dot (d j) (d j)) :=
      sumP_le fun i j _ _ => dot_sq_le (d i) (d j)
    have h3 := sumP_prod_le (fun i => dot (d i) (d i)) hD
    unfold nsq
    linarith
  have hR : Rf p d ≤ (1 + θ) * δ2 + (1 + 1 / θ) * (nsq d ^ 2 / 2) := by
    unfold Rf
    have h2 := sumP_le hL
    rw [sumP_add, sumP_mul, sumP_mul] at h2
    have h3 : 0 ≤ 1 + 1 / θ := by positivity
    have h4 : 0 ≤ 1 + θ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hΔ h4, mul_le_mul_of_nonneg_left hdd h3]
  have h5 : K.penR * ∑ i ∈ range 11, dot (d i) (d i) ^ 2 / 4 ≤ K.penR * (nsq d ^ 2 / 4) :=
    mul_le_mul_of_nonneg_left hpen hK
  have h6 : nsq d ^ 2 ≤ X0 * nsq d := by nlinarith
  have h7 : 0 ≤ (1 + 1 / θ) / 2 + K.penR / 4 := by positivity
  have h8 := mul_le_mul_of_nonneg_left h6 h7
  nlinarith

end N11.Analytic
