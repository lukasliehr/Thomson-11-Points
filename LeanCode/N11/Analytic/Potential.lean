module

public import N11.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp

/-!
# The theorem for 11 points, analytic part: the potential (row A2)

The Coulomb potential of two points of the unit sphere with the inner product `t` is `fpot t = (2 - 2 t)^(-1/2)`.
With `u = (2 - 2 t₀)^(1/2)`, `s = (2 - 2 t)^(1/2)` and `w = fpot t₀ = 1 / u`:

* `taylor3`: `fpot` lies above its Taylor polynomial of degree three at every `t₀ < 1`, since
  `1/s - [1/u + w³ (t - t₀) + (3/2) w⁵ (t - t₀)² + (5/2) w⁷ (t - t₀)³] = (u - s)⁴ (5s³ + 20s²u + 29su² + 16u³) / (16 s u⁷)`;
* `upper2`: `fpot t ≤ fpot t₀ + w³ (t - t₀) + 2 (t - t₀)² / m⁵` if `u, s ≥ m > 0`, since
  `1/s - 1/u - w³ (t - t₀) = (u - s)² (2u + s) / (2 s u³)`;
* `fpot_lip`, `fpot_le`, `fpot_ge`, `pow_succ_sub_le`: a Lipschitz bound and bounds of `fpot` on `[-11/10, 3/5]`;
* `fpot_div`: `fpot (t / m) = √m · fpot (t + 1 - m)`, for the inner products of points on spheres of other radii.
-/

@[expose] public section

namespace N11.Analytic

open Finset

theorem fpot_pos {t : ℝ} (ht : t < 1) : 0 < fpot t := by
  unfold fpot
  have : 0 < Real.sqrt (2 - 2 * t) := Real.sqrt_pos.mpr (by linarith)
  positivity

theorem fpot_nonneg (t : ℝ) : 0 ≤ fpot t := by
  unfold fpot
  have := Real.sqrt_nonneg (2 - 2 * t)
  positivity

theorem fpot_sq {t : ℝ} (ht : t < 1) : fpot t ^ 2 * (2 - 2 * t) = 1 := by
  unfold fpot
  have h0 : 0 < 2 - 2 * t := by linarith
  have hs := Real.sq_sqrt h0.le
  have hp : 0 < Real.sqrt (2 - 2 * t) := Real.sqrt_pos.mpr h0
  rw [div_pow, one_pow, hs]
  exact one_div_mul_cancel h0.ne'

/-- **The potential lies above each of its Taylor polynomials of degree three.** -/
theorem taylor3 {t0 t : ℝ} (ht0 : t0 < 1) (ht : t < 1) :
    fpot t0 + fpot t0 ^ 3 * (t - t0) + 3 / 2 * fpot t0 ^ 5 * (t - t0) ^ 2 + 5 / 2 * fpot t0 ^ 7 * (t - t0) ^ 3
      ≤ fpot t := by
  obtain ⟨u, hu_def⟩ : ∃ u, u = Real.sqrt (2 - 2 * t0) := ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (2 - 2 * t) := ⟨_, rfl⟩
  have hu : 0 < u := by rw [hu_def]; exact Real.sqrt_pos.mpr (by linarith)
  have hs : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.mpr (by linarith)
  have hu2 : u ^ 2 = 2 - 2 * t0 := by rw [hu_def]; exact Real.sq_sqrt (by linarith)
  have hs2 : s ^ 2 = 2 - 2 * t := by rw [hs_def]; exact Real.sq_sqrt (by linarith)
  have ht' : t - t0 = (u ^ 2 - s ^ 2) / 2 := by rw [hu2, hs2]; ring
  have e0 : fpot t0 = 1 / u := by rw [hu_def]; rfl
  have e1 : fpot t = 1 / s := by rw [hs_def]; rfl
  rw [e0, e1, ht']
  have key : 1 / s - (1 / u + (1 / u) ^ 3 * ((u ^ 2 - s ^ 2) / 2) + 3 / 2 * (1 / u) ^ 5 * ((u ^ 2 - s ^ 2) / 2) ^ 2
      + 5 / 2 * (1 / u) ^ 7 * ((u ^ 2 - s ^ 2) / 2) ^ 3)
      = (u - s) ^ 4 * (5 * s ^ 3 + 20 * s ^ 2 * u + 29 * s * u ^ 2 + 16 * u ^ 3) / (16 * s * u ^ 7) := by
    field_simp
    ring
  have hnn : 0 ≤ (u - s) ^ 4 * (5 * s ^ 3 + 20 * s ^ 2 * u + 29 * s * u ^ 2 + 16 * u ^ 3) / (16 * s * u ^ 7) := by
    positivity
  linarith

/-- **The potential lies below its tangent plus a quadratic term**, where both inner products are at most `T < 1`
and `m² ≤ 2 - 2T`. -/
theorem upper2 {t0 t T m : ℝ} (ht0 : t0 ≤ T) (ht : t ≤ T) (hT : T < 1) (hm : 0 < m) (hmT : m ^ 2 ≤ 2 - 2 * T) :
    fpot t ≤ fpot t0 + fpot t0 ^ 3 * (t - t0) + 2 * (t - t0) ^ 2 / m ^ 5 := by
  obtain ⟨u, hu_def⟩ : ∃ u, u = Real.sqrt (2 - 2 * t0) := ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt (2 - 2 * t) := ⟨_, rfl⟩
  have hu : 0 < u := by rw [hu_def]; exact Real.sqrt_pos.mpr (by linarith)
  have hs : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.mpr (by linarith)
  have hu2 : u ^ 2 = 2 - 2 * t0 := by rw [hu_def]; exact Real.sq_sqrt (by linarith)
  have hs2 : s ^ 2 = 2 - 2 * t := by rw [hs_def]; exact Real.sq_sqrt (by linarith)
  have hmu : m ≤ u := by
    rw [hu_def]
    exact (Real.le_sqrt hm.le (by linarith)).mpr (by linarith)
  have hms : m ≤ s := by
    rw [hs_def]
    exact (Real.le_sqrt hm.le (by linarith)).mpr (by linarith)
  have ht' : t - t0 = (u ^ 2 - s ^ 2) / 2 := by rw [hu2, hs2]; ring
  have e0 : fpot t0 = 1 / u := by rw [hu_def]; rfl
  have e1 : fpot t = 1 / s := by rw [hs_def]; rfl
  rw [e0, e1, ht']
  have key : 1 / s - (1 / u + (1 / u) ^ 3 * ((u ^ 2 - s ^ 2) / 2))
      = (u - s) ^ 2 * (2 * u + s) / (2 * s * u ^ 3) := by
    field_simp
    ring
  -- `(2u + s) m⁵ ≤ (u + s)² s u³`
  have h1 : (2 * u + s) * m ^ 5 ≤ (u + s) ^ 2 * s * u ^ 3 := by
    have hm3 : m ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ hm.le hmu 3
    have a1 : (u + s) * (2 * m) ≤ (u + s) * (u + s) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have a2 : (u + s) * (2 * m) * m ≤ (u + s) * (u + s) * s :=
      mul_le_mul a1 hms hm.le (by positivity)
    have a3 : (u + s) * (2 * m) * m * m ^ 3 ≤ (u + s) * (u + s) * s * u ^ 3 :=
      mul_le_mul a2 hm3 (by positivity) (by positivity)
    have a4 : (2 * u + s) * m ^ 5 ≤ (u + s) * (2 * m) * m * m ^ 3 := by
      have : 0 ≤ s * m ^ 5 := by positivity
      nlinarith
    calc (2 * u + s) * m ^ 5 ≤ (u + s) * (2 * m) * m * m ^ 3 := a4
      _ ≤ (u + s) * (u + s) * s * u ^ 3 := a3
      _ = (u + s) ^ 2 * s * u ^ 3 := by ring
  have h2 : (u - s) ^ 2 * (2 * u + s) / (2 * s * u ^ 3) ≤ 2 * ((u ^ 2 - s ^ 2) / 2) ^ 2 / m ^ 5 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : 0 ≤ (u - s) ^ 2 := sq_nonneg _
    have h4 := mul_le_mul_of_nonneg_left h1 h3
    have e : 2 * ((u ^ 2 - s ^ 2) / 2) ^ 2 * (2 * s * u ^ 3) = (u - s) ^ 2 * ((u + s) ^ 2 * s * u ^ 3) := by
      ring
    rw [e]
    nlinarith
  linarith

/-! ## Bounds -/

theorem sqrt_ge_of {x c : ℝ} (hc : 0 ≤ c) (h : c ^ 2 ≤ x) : c ≤ Real.sqrt x :=
  (Real.le_sqrt hc (le_trans (sq_nonneg c) h)).mpr h

theorem fpot_le {t : ℝ} (ht : t ≤ 3 / 5) : fpot t ≤ 9 / 8 := by
  unfold fpot
  have hs : 8 / 9 ≤ Real.sqrt (2 - 2 * t) := sqrt_ge_of (by norm_num) (by nlinarith)
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem fpot_ge {t : ℝ} (ht : -11 / 10 ≤ t) (ht1 : t < 1) : 2 / 5 ≤ fpot t := by
  unfold fpot
  have h0 : 0 < 2 - 2 * t := by linarith
  have hs0 : 0 < Real.sqrt (2 - 2 * t) := Real.sqrt_pos.mpr h0
  have hs : Real.sqrt (2 - 2 * t) ≤ 5 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith
  rw [le_div_iff₀ hs0]
  linarith

/-- **A Lipschitz bound of the potential.** -/
theorem fpot_lip {t t' : ℝ} (ht : t ≤ 3 / 5) (ht' : t' ≤ 3 / 5) : |fpot t - fpot t'| ≤ 3 / 2 * |t - t'| := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (2 - 2 * t) := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = Real.sqrt (2 - 2 * t') := ⟨_, rfl⟩
  have hs2 : s ^ 2 = 2 - 2 * t := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hs2' : s' ^ 2 = 2 - 2 * t' := by rw [hs']; exact Real.sq_sqrt (by linarith)
  have hs0 : 8 / 9 ≤ s := by rw [hs]; exact sqrt_ge_of (by norm_num) (by nlinarith)
  have hs0' : 8 / 9 ≤ s' := by rw [hs']; exact sqrt_ge_of (by norm_num) (by nlinarith)
  have e0 : fpot t = 1 / s := by rw [hs]; rfl
  have e1 : fpot t' = 1 / s' := by rw [hs']; rfl
  have hpos : 0 < s * s' * (s + s') := by positivity
  have e : fpot t - fpot t' = 2 * (t - t') / (s * s' * (s + s')) := by
    rw [e0, e1, div_sub_div _ _ (by positivity) (by positivity), div_eq_div_iff (by positivity) hpos.ne']
    have h2 : 2 * (t - t') = s' ^ 2 - s ^ 2 := by rw [hs2, hs2']; ring
    rw [h2]
    ring
  rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, abs_mul, abs_two]
  have h1a : 64 / 81 ≤ s * s' := by nlinarith
  have h1b : 16 / 9 ≤ s + s' := by linarith
  have h1 : 1024 / 729 ≤ s * s' * (s + s') := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg (t - t')), abs_nonneg (t - t')]

/-- A bound for the difference of two powers. -/
theorem pow_succ_sub_le (n : ℕ) {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ M) (hbM : b ≤ M) :
    |a ^ (n + 1) - b ^ (n + 1)| ≤ (n + 1) * M ^ n * |a - b| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) = a * (a ^ (n + 1) - b ^ (n + 1)) + b ^ (n + 1) * (a - b) := by
      ring
    have hM : 0 ≤ M := le_trans ha haM
    have hbn : b ^ (n + 1) ≤ M ^ (n + 1) := pow_le_pow_left₀ hb hbM (n + 1)
    rw [e]
    calc |a * (a ^ (n + 1) - b ^ (n + 1)) + b ^ (n + 1) * (a - b)|
        ≤ |a * (a ^ (n + 1) - b ^ (n + 1))| + |b ^ (n + 1) * (a - b)| := abs_add_le _ _
      _ = a * |a ^ (n + 1) - b ^ (n + 1)| + b ^ (n + 1) * |a - b| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (pow_nonneg hb (n + 1))]
      _ ≤ M * ((n + 1) * M ^ n * |a - b|) + M ^ (n + 1) * |a - b| := by
          gcongr
      _ = ((n + 1 : ℕ) + 1) * M ^ (n + 1) * |a - b| := by
          push_cast
          ring

/-- A power of the potential is Lipschitz on `(-∞, 3/5]`. -/
theorem fpot_pow_lip (n : ℕ) {t t' : ℝ} (ht : t ≤ 3 / 5) (ht' : t' ≤ 3 / 5) :
    |fpot t ^ (n + 1) - fpot t' ^ (n + 1)| ≤ (n + 1) * (9 / 8) ^ n * (3 / 2) * |t - t'| := by
  have h := pow_succ_sub_le n (fpot_nonneg t) (fpot_nonneg t') (fpot_le ht) (fpot_le ht')
  have h2 := fpot_lip ht ht'
  have h3 : 0 ≤ ((n : ℝ) + 1) * (9 / 8) ^ n := by positivity
  calc |fpot t ^ (n + 1) - fpot t' ^ (n + 1)| ≤ (n + 1) * (9 / 8) ^ n * |fpot t - fpot t'| := h
    _ ≤ (n + 1) * (9 / 8) ^ n * (3 / 2 * |t - t'|) := mul_le_mul_of_nonneg_left h2 h3
    _ = (n + 1) * (9 / 8) ^ n * (3 / 2) * |t - t'| := by ring

/-- **The potential of the inner product of two points on spheres of other radii.** -/
theorem fpot_div {t m : ℝ} (hm : 0 < m) (ht : t < m) : fpot (t / m) = Real.sqrt m * fpot (t + 1 - m) := by
  unfold fpot
  have h0 : 0 ≤ 2 * m - 2 * t := by linarith
  have e1 : 2 - 2 * (t / m) = (2 * m - 2 * t) / m := by field_simp
  have e2 : 2 - 2 * (t + 1 - m) = 2 * m - 2 * t := by ring
  rw [e1, e2, Real.sqrt_div h0]
  have hs : 0 < Real.sqrt (2 * m - 2 * t) := Real.sqrt_pos.mpr (by linarith)
  have hm' : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  field_simp

end N11.Analytic
