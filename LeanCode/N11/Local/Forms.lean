module

public import N11.Local.Sums

/-!
# G7 of route G for eleven points: the forms of the local statement, and the statement

A configuration is a function `p : ℕ → ℕ → ℝ`: `p i c` is the coordinate `c < 3` of the point `i < 11`. A
displacement `x` has the same type. The coefficients of the pairs are functions `a b c : ℕ → ℕ → ℝ`.

* `dot`: the inner product of `ℝ³`; `nsq x = ∑ |x_i|²`.
* `Lf p x i j = <p_i, x_j> + <x_i, p_j>`: the first-order change of the inner product of the points `i`, `j`.
* `psif p x i j = <x_i, x_j> - (<p_i, p_j> / 2) (|x_i|² + |x_j|²)`: its second-order change, for `x_i ⊥ p_i`.
* `rhof p x i j = -(1/2) (|x_j|² <x_i, p_j> + |x_i|² <p_i, x_j>)`: its third-order change.
* `penf p x = ∑ <p_i, x_i>² + ∑_{i, j} (<p_i, p_j> <x_i, x_j> - <p_i, x_j> <x_i, p_j>)`. By the identity of Lagrange the
  second sum is `|∑ p_i × x_i|²`: the form vanishes for the displacements that are tangential and satisfy the
  condition of the gauge `∑ p_i × x_i = 0`.
* `Qf = ∑_{i<j} a psi + b L²`, `Rf = ∑_{i<j} L²`, `Cf = ∑_{i<j} c L³ + 2 b L psi + a rho`.
* `frc p a i = ∑_{j ≠ i} a_ij p_j`.

`G7 p a b c K`: the statement G7 for the reference configuration `p`, the coefficients `a, b, c` and the constants
`K`. With `f(t) = (2 - 2t)^(-1/2)` and `w = f(<p_i, p_j>)` the coefficients enclose `f' = w³`, `f''/2 = (3/2) w⁵`,
`f'''/6 = (5/2) w⁷`. The statement is about explicit polynomials; the analytic part of route G uses it with the
inequality `f(t) ≥ f(t₀) + f'(t₀) (t - t₀) + (f''(t₀)/2) (t - t₀)² + (f'''(t₀)/6) (t - t₀)³`.
-/

@[expose] public section

namespace N11.Local

open Finset

/-- The inner product of `ℝ³`. -/
def dot (y y' : ℕ → ℝ) : ℝ := ∑ c ∈ range 3, y c * y' c

theorem dot_eq (y y' : ℕ → ℝ) : dot y y' = y 0 * y' 0 + y 1 * y' 1 + y 2 * y' 2 := by
  unfold dot
  simp only [sum_range_succ, sum_range_zero, zero_add]

theorem dot_comm (y y' : ℕ → ℝ) : dot y y' = dot y' y := by
  unfold dot
  exact sum_congr rfl fun c _ => mul_comm _ _

theorem dot_self_nonneg (y : ℕ → ℝ) : 0 ≤ dot y y := by
  unfold dot
  exact sum_nonneg fun c _ => mul_self_nonneg _

/-- The sum of the squares of the norms of eleven vectors. -/
def nsq (x : ℕ → ℕ → ℝ) : ℝ := ∑ i ∈ range 11, dot (x i) (x i)

theorem nsq_nonneg (x : ℕ → ℕ → ℝ) : 0 ≤ nsq x := by
  unfold nsq
  exact sum_nonneg fun i _ => dot_self_nonneg _

/-- `<p_i, x_j> + <x_i, p_j>`. -/
def Lf (p x : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ := dot (p i) (x j) + dot (x i) (p j)

/-- `<x_i, x_j> - (<p_i, p_j> / 2) (|x_i|² + |x_j|²)`. -/
noncomputable def psif (p x : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  dot (x i) (x j) - dot (p i) (p j) / 2 * (dot (x i) (x i) + dot (x j) (x j))

/-- `-(1/2) (|x_j|² <x_i, p_j> + |x_i|² <p_i, x_j>)`. -/
noncomputable def rhof (p x : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  -(1 / 2) * (dot (x j) (x j) * dot (x i) (p j) + dot (x i) (x i) * dot (p i) (x j))

/-- `∑ <p_i, x_i>² + |∑ p_i × x_i|²`, the second term written with inner products. -/
def penf (p x : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ range 11, dot (p i) (x i) ^ 2
    + ∑ i ∈ range 11, ∑ j ∈ range 11, (dot (p i) (p j) * dot (x i) (x j) - dot (p i) (x j) * dot (x i) (p j))

/-- The quadratic form of the energy. -/
noncomputable def Qf (p a b x : ℕ → ℕ → ℝ) : ℝ := sumP fun i j => a i j * psif p x i j + b i j * Lf p x i j ^ 2

/-- The form of the rigidity. -/
def Rf (p x : ℕ → ℕ → ℝ) : ℝ := sumP fun i j => Lf p x i j ^ 2

/-- The cubic form of the energy. -/
noncomputable def Cf (p a b c x : ℕ → ℕ → ℝ) : ℝ :=
  sumP fun i j => c i j * Lf p x i j ^ 3 + 2 * b i j * (Lf p x i j * psif p x i j) + a i j * rhof p x i j

/-- `∑_{j ≠ i} a_ij p_j`. -/
def frc (p a : ℕ → ℕ → ℝ) (i : ℕ) (k : ℕ) : ℝ := ∑ j ∈ range 11, if j = i then 0 else a i j * p j k

/-- The sum of the coefficients of the pairs that contain the point `i`. -/
def rowS (a : ℕ → ℕ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ range 11, if j = i then 0 else a i j

/-! ## The multiples of a configuration -/

/-- The configuration `s p`. -/
def sc (s : ℝ) (p : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ := fun i k => s * p i k

theorem dot_sc_left (s : ℝ) (p : ℕ → ℕ → ℝ) (i : ℕ) (y : ℕ → ℝ) : dot (sc s p i) y = s * dot (p i) y := by
  unfold dot
  rw [Finset.mul_sum]
  refine sum_congr rfl fun k _ => ?_
  show s * p i k * y k = s * (p i k * y k)
  ring

theorem dot_sc_right (s : ℝ) (p : ℕ → ℕ → ℝ) (i : ℕ) (y : ℕ → ℝ) : dot y (sc s p i) = s * dot y (p i) := by
  rw [dot_comm, dot_sc_left, dot_comm]

theorem dot_sc_sc (s : ℝ) (p : ℕ → ℕ → ℝ) (i j : ℕ) : dot (sc s p i) (sc s p j) = s ^ 2 * dot (p i) (p j) := by
  rw [dot_sc_left, dot_sc_right]
  ring

theorem Lf_sc (s : ℝ) (p x : ℕ → ℕ → ℝ) (i j : ℕ) : Lf (sc s p) x i j = s * Lf p x i j := by
  unfold Lf
  rw [dot_sc_left, dot_sc_right]
  ring

theorem penf_sc (s : ℝ) (p x : ℕ → ℕ → ℝ) : penf (sc s p) x = s ^ 2 * penf p x := by
  have e1 : ∀ i, dot (sc s p i) (x i) ^ 2 = s ^ 2 * dot (p i) (x i) ^ 2 := by
    intro i
    rw [dot_sc_left]
    ring
  have e2 : ∀ i j, dot (sc s p i) (sc s p j) * dot (x i) (x j) - dot (sc s p i) (x j) * dot (x i) (sc s p j)
      = s ^ 2 * (dot (p i) (p j) * dot (x i) (x j) - dot (p i) (x j) * dot (x i) (p j)) := by
    intro i j
    rw [dot_sc_sc, dot_sc_left, dot_sc_right]
    ring
  unfold penf
  rw [sum_congr rfl fun i _ => e1 i, sum_congr rfl fun i _ => sum_congr rfl fun j _ => e2 i j, ← Finset.mul_sum,
    sum2_mul, mul_add]

/-! ## The statement -/

/-- The constants of the statement G7. -/
structure Consts where
  /-- the enclosures of the coefficients: `|a - w³| ≤ eps`, `|b - (3/2) w⁵| ≤ (3/2) eps`, `|c - (5/2) w⁷| ≤ (5/2) eps` -/
  eps : ℝ
  /-- the residual of the first-order condition -/
  gam : ℝ
  /-- the bound for the sums of the coefficients `a` over the pairs that contain a point -/
  ra : ℝ
  /-- the same for `b` -/
  rb : ℝ
  /-- the same for `c` -/
  rc : ℝ
  /-- `| |p_i|² - 1 | ≤ nu` -/
  nu : ℝ
  /-- `<p_i, p_j> ≤ tmax` -/
  tmax : ℝ
  /-- the lower bound of the quadratic form -/
  kappa : ℝ
  /-- the factor of the penalty in the bound of the quadratic form -/
  penQ : ℝ
  /-- the lower bound of the form of the rigidity -/
  sigma2 : ℝ
  /-- the factor of the penalty in the bound of the rigidity -/
  penR : ℝ
  /-- the bound of the cubic form -/
  c3 : ℝ

/-- **The statement G7**: the local constants of the energy at the reference configuration `p`. -/
structure G7 (p a b c : ℕ → ℕ → ℝ) (K : Consts) : Prop where
  /-- the points of the reference configuration are close to the sphere -/
  norm : ∀ i, i < 11 → |dot (p i) (p i) - 1| ≤ K.nu
  /-- the inner products stay away from one -/
  top : ∀ i j, i < j → j < 11 → dot (p i) (p j) ≤ K.tmax
  /-- the coefficients are symmetric -/
  sym : ∀ i j, i < j → j < 11 → a i j = a j i ∧ b i j = b j i ∧ c i j = c j i
  /-- the coefficients enclose the derivatives of the potential -/
  enc : ∀ i j, i < j → j < 11 → ∀ w : ℝ, 0 < w → w ^ 2 * (2 - 2 * dot (p i) (p j)) = 1 →
    |a i j - w ^ 3| ≤ K.eps ∧ |b i j - 3 / 2 * w ^ 5| ≤ 3 / 2 * K.eps ∧ |c i j - 5 / 2 * w ^ 7| ≤ 5 / 2 * K.eps
  /-- the first-order condition holds up to `gam` -/
  grad : ∑ i ∈ range 11, ∑ k ∈ range 3, (frc p a i k - dot (frc p a i) (p i) * p i k) ^ 2 ≤ K.gam ^ 2
  /-- the sums of the coefficients -/
  rows : ∀ i, i < 11 → rowS a i ≤ K.ra ∧ rowS b i ≤ K.rb ∧ rowS c i ≤ K.rc
  /-- the quadratic form is positive definite modulo the penalty -/
  hess : ∀ x : ℕ → ℕ → ℝ, K.kappa * nsq x ≤ Qf p a b x + K.penQ * penf p x
  /-- the rigidity: the first-order changes of the inner products control the displacement modulo the penalty -/
  rig : ∀ x : ℕ → ℕ → ℝ, K.sigma2 * nsq x ≤ Rf p x + K.penR * penf p x
  /-- the cubic form on the tangential displacements -/
  cub : ∀ x : ℕ → ℕ → ℝ, (∀ i, i < 11 → dot (p i) (x i) = 0) → Cf p a b c x ^ 2 ≤ K.c3 ^ 2 * nsq x ^ 3

end N11.Local
