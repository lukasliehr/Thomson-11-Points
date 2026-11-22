module

public import N11.Analytic.Potential

/-!
# The theorem for 11 points, analytic part: a minimizer is critical (row A4)

Let `z` be a configuration of the sphere (in the form of `N11/Local`) that minimizes the energy among the
configurations of distinct points of the sphere (`IsMinN`), and whose points have pairwise squared distances at
least `δ2 > 0`. Then for every point `i` the vector `F_i = ∑_{j ≠ i} fpot(<z_i, z_j>)³ z_j` is the multiple
`<F_i, z_i> z_i` of `z_i` (`critical`).

The proof moves the point `i` along the circle through `z_i` in the direction of the tangential part `u` of `F_i`:
`w = ((1 - θ²|u|²) z_i - 2θ u) / (1 + θ²|u|²)` is a unit vector. By `upper2` the energy changes by at most
`<F_i, w - z_i> + K |w - z_i|² = -2θ|u|² (1 + θ <F_i, z_i>) / (1 + θ²|u|²) + 80 K θ² |u|² / (1 + θ²|u|²)`, which is
negative for small `θ > 0` unless `u = 0`. No derivative occurs.
-/

@[expose] public section

namespace N11.Analytic

open Finset N11.Local

/-- The coefficients of the first-order term of the energy at a configuration of the sphere: `fpot(<z_i, z_j>)³`. -/
noncomputable def alpha (z : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ := fpot (dot (z i) (z j)) ^ 3

theorem alpha_symm (z : ℕ → ℕ → ℝ) (i j : ℕ) : alpha z i j = alpha z j i := by
  unfold alpha
  rw [dot_comm]

/-- `z` minimizes the energy among the configurations of distinct points of the sphere. -/
def IsMinN (z : ℕ → ℕ → ℝ) : Prop :=
  ∀ z' : ℕ → ℕ → ℝ, (∀ i, i < 11 → dot (z' i) (z' i) = 1) →
    (∀ i j, i < 11 → j < 11 → i ≠ j → dot (z' i) (z' j) < 1) → En z ≤ En z'

theorem dot_add_add (a b c d : ℕ → ℝ) :
    dot (fun k => a k + b k) (fun k => c k + d k) = dot a c + dot a d + dot b c + dot b d := by
  simp only [dot_eq]
  ring

theorem dot_lincomb (a z u : ℕ → ℝ) (α β c : ℝ) :
    dot a (fun k => (α * z k + β * u k) / c) = (α * dot a z + β * dot a u) / c := by
  simp only [dot_eq]
  ring

theorem dot_sub_smul (a b c : ℕ → ℝ) (s : ℝ) : dot (fun k => a k - s * b k) c = dot a c - s * dot b c := by
  simp only [dot_eq]
  ring

theorem dot_zero_left (c : ℕ → ℝ) : dot (fun _ => 0) c = 0 := by
  simp only [dot_eq]
  ring

theorem rowS_one {i : ℕ} (hi : i < 11) : rowS (fun _ _ => (1 : ℝ)) i = 10 := by
  unfold rowS
  interval_cases i <;> simp [sum_range_succ] <;> norm_num

/-- `sumP` of a sum of two values of the points, with weight one. -/
theorem sumP_sum_pts (φ : ℕ → ℝ) : sumP (fun i j => φ i + φ j) = 10 * ∑ i ∈ range 11, φ i := by
  have h := sumP_rows (fun _ _ => (1 : ℝ)) φ (fun _ _ _ _ => rfl)
  simp only [one_mul] at h
  rw [h, Finset.mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [rowS_one (mem_range.mp hi)]
  ring

/-- **The energy after moving one point.** Let `z` be a configuration of the sphere and `e` a vector such that
all inner products of distinct points of `z` and of the moved configuration `z + E` (`E` is `e` at the point
`i0` and `0` elsewhere) are at most `T < 1`, with `m² ≤ 2 - 2T`. Then the energy grows by at most
`<F_{i0}, e> + (40 / m⁵) |e|²`. -/
theorem energy_move {z : ℕ → ℕ → ℝ} (hz : ∀ i, i < 11 → dot (z i) (z i) = 1) {i0 : ℕ} (hi0 : i0 < 11)
    (e : ℕ → ℝ) {T m : ℝ} (hT : T < 1) (hm : 0 < m) (hmT : m ^ 2 ≤ 2 - 2 * T)
    (htop : ∀ i j, i < 11 → j < 11 → i ≠ j → dot (z i) (z j) ≤ T)
    (htop' : ∀ i j, i < 11 → j < 11 → i ≠ j →
      dot (fun k => z i k + (if i = i0 then e k else 0)) (fun k => z j k + (if j = i0 then e k else 0)) ≤ T) :
    En (fun i k => z i k + (if i = i0 then e k else 0)) - En z
      ≤ dot (frc z (alpha z) i0) e + 40 / m ^ 5 * dot e e := by
  set E : ℕ → ℕ → ℝ := fun i k => if i = i0 then e k else 0 with hE
  have hEE : ∀ i j, i < j → dot (E i) (E j) = 0 := by
    intro i j hij
    by_cases hi : i = i0
    · have hj : j ≠ i0 := by omega
      have e1 : E j = fun _ => 0 := by
        funext k
        simp only [hE, if_neg hj]
      rw [e1, dot_comm, dot_zero_left]
    · have e1 : E i = fun _ => 0 := by
        funext k
        simp only [hE, if_neg hi]
      rw [e1, dot_zero_left]
  -- the change of an inner product is the linear form `Lf z E`
  have hdiff : ∀ i j, i < j → dot (fun k => z i k + E i k) (fun k => z j k + E j k) - dot (z i) (z j)
      = Lf z E i j := by
    intro i j hij
    rw [dot_add_add, hEE i j hij]
    unfold Lf
    ring
  have hpair : ∀ i j, i < j → j < 11 →
      fpot (dot (fun k => z i k + E i k) (fun k => z j k + E j k)) - fpot (dot (z i) (z j))
        ≤ alpha z i j * Lf z E i j + 2 / m ^ 5 * Lf z E i j ^ 2 := by
    intro i j hij hj
    have h1 := upper2 (htop i j (by omega) hj (ne_of_lt hij)) (htop' i j (by omega) hj (ne_of_lt hij)) hT hm hmT
    rw [hdiff i j hij] at h1
    unfold alpha
    have e2 : 2 * Lf z E i j ^ 2 / m ^ 5 = 2 / m ^ 5 * Lf z E i j ^ 2 := by ring
    linarith
  -- the quadratic term
  have hsq : ∀ i j, i < j → j < 11 → Lf z E i j ^ 2 ≤ 2 * (dot (E i) (E i) + dot (E j) (E j)) := by
    intro i j hij hj
    unfold Lf
    have h1 := dot_sq_le (z i) (E j)
    have h2 := dot_sq_le (E i) (z j)
    rw [hz i (by omega), one_mul] at h1
    rw [hz j hj, mul_one] at h2
    nlinarith [sq_nonneg (dot (z i) (E j) - dot (E i) (z j))]
  have hEsum : ∑ i ∈ range 11, dot (E i) (E i) = dot e e := by
    rw [Finset.sum_eq_single i0]
    · have e1 : E i0 = e := by
        funext k
        simp only [hE, if_pos rfl]
      rw [e1]
    · intro b _ hb
      have e1 : E b = fun _ => 0 := by
        funext k
        simp only [hE, if_neg hb]
      rw [e1, dot_zero_left]
    · intro h
      exact absurd (mem_range.mpr hi0) h
  have hlin : sumP (fun i j => alpha z i j * Lf z E i j) = dot (frc z (alpha z) i0) e := by
    rw [sumP_lin (alpha z) z E (fun i j _ _ => alpha_symm z i j)]
    rw [Finset.sum_eq_single i0]
    · have e1 : E i0 = e := by
        funext k
        simp only [hE, if_pos rfl]
      rw [e1]
    · intro b _ hb
      have e1 : E b = fun _ => 0 := by
        funext k
        simp only [hE, if_neg hb]
      rw [e1, dot_comm, dot_zero_left]
    · intro h
      exact absurd (mem_range.mpr hi0) h
  have hm5 : 0 < m ^ 5 := by positivity
  calc En (fun i k => z i k + E i k) - En z
      = sumP (fun i j => fpot (dot (fun k => z i k + E i k) (fun k => z j k + E j k)) - fpot (dot (z i) (z j))) := by
        unfold En
        rw [sumP_sub]
    _ ≤ sumP (fun i j => alpha z i j * Lf z E i j + 2 / m ^ 5 * Lf z E i j ^ 2) := sumP_le hpair
    _ = sumP (fun i j => alpha z i j * Lf z E i j) + 2 / m ^ 5 * sumP (fun i j => Lf z E i j ^ 2) := by
        rw [sumP_add, sumP_mul]
    _ ≤ dot (frc z (alpha z) i0) e + 2 / m ^ 5 * sumP (fun i j => 2 * (dot (E i) (E i) + dot (E j) (E j))) := by
        rw [hlin]
        have := sumP_le hsq
        have h2 : 0 ≤ 2 / m ^ 5 := by positivity
        nlinarith
    _ = dot (frc z (alpha z) i0) e + 40 / m ^ 5 * dot e e := by
        rw [sumP_mul, sumP_sum_pts, hEsum]
        ring

/-- **A minimizer is critical.** -/
theorem critical {z : ℕ → ℕ → ℝ} (hz : ∀ i, i < 11 → dot (z i) (z i) = 1) {δ2 : ℝ} (hδ : 0 < δ2)
    (hsep : ∀ i j, i < 11 → j < 11 → i ≠ j → δ2 ≤ 2 - 2 * dot (z i) (z j)) (hmin : IsMinN z) :
    ∀ i, i < 11 → ∀ k, k < 3 → frc z (alpha z) i k = dot (frc z (alpha z) i) (z i) * z i k := by
  intro i0 hi0
  obtain ⟨F, hF⟩ : ∃ F, F = frc z (alpha z) i0 := ⟨_, rfl⟩
  rw [← hF]
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = dot F (z i0) := ⟨_, rfl⟩
  rw [← hlam]
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, u = fun k => F k - lam * z i0 k := ⟨_, rfl⟩
  have hz0 := hz i0 hi0
  have huz : dot u (z i0) = 0 := by
    rw [hu, dot_sub_smul, hz0, ← hlam]
    ring
  have hzu : dot (z i0) u = 0 := by rw [dot_comm]; exact huz
  have hFu : dot F u = dot u u := by
    have e1 : F = fun k => u k + lam * z i0 k := by
      funext k
      rw [hu]
      ring
    have e2 : dot (fun k => u k + lam * z i0 k) u = dot u u + lam * dot (z i0) u := by
      simp only [dot_eq]
      ring
    rw [e1, e2, hzu, mul_zero, add_zero]
  suffices huu : dot u u = 0 by
    intro k hk
    have h1 := sq_le_dot_self u hk
    rw [huu] at h1
    have h2 : u k = 0 := by nlinarith [sq_nonneg (u k)]
    rw [hu] at h2
    linarith
  by_contra hne
  have hU : 0 < dot u u := lt_of_le_of_ne (dot_self_nonneg u) (Ne.symm hne)
  obtain ⟨U, hUdef⟩ : ∃ U, U = dot u u := ⟨_, rfl⟩
  rw [← hUdef] at hU hFu
  -- the constants
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 1 - δ2 / 4 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = Real.sqrt (δ2 / 2) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; exact Real.sqrt_pos.mpr (by linarith)
  have hm2 : m ^ 2 = δ2 / 2 := by rw [hm]; exact Real.sq_sqrt (by linarith)
  have hmT : m ^ 2 ≤ 2 - 2 * T := by rw [hm2, hT]; linarith
  have hT1 : T < 1 := by rw [hT]; linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 40 / m ^ 5 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = min (δ2 / (8 * (U + 1))) (1 / (4 * K + 2 * |lam| + 1)) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by
    rw [hθ]
    exact lt_min (by positivity) (by positivity)
  have hθ1 : θ * (8 * (U + 1)) ≤ δ2 := by
    have h := min_le_left (δ2 / (8 * (U + 1))) (1 / (4 * K + 2 * |lam| + 1))
    rw [← hθ] at h
    rw [le_div_iff₀ (by positivity)] at h
    exact h
  have hθ2 : θ * (4 * K + 2 * |lam| + 1) ≤ 1 := by
    have h := min_le_right (δ2 / (8 * (U + 1))) (1 / (4 * K + 2 * |lam| + 1))
    rw [← hθ] at h
    rw [le_div_iff₀ (by positivity)] at h
    exact h
  -- the displacement of the point
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 + θ ^ 2 * U := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, e = fun k => (-2 * θ ^ 2 * U * z i0 k + -2 * θ * u k) / c := ⟨_, rfl⟩
  have hdz : ∀ a : ℕ → ℝ, dot a e = (-2 * θ ^ 2 * U * dot a (z i0) + -2 * θ * dot a u) / c := by
    intro a
    rw [he]
    exact dot_lincomb a (z i0) u (-2 * θ ^ 2 * U) (-2 * θ) c
  have hze : dot (z i0) e = -2 * θ ^ 2 * U / c := by
    rw [hdz, hz0, hzu]
    ring
  have hee : dot e e = 4 * θ ^ 2 * U / c := by
    have h1 : dot e (z i0) = -2 * θ ^ 2 * U / c := by rw [dot_comm]; exact hze
    have h2 : dot e u = -2 * θ * U / c := by
      rw [dot_comm, hdz, huz, ← hUdef]
      ring
    rw [hdz, h1, h2]
    rw [hc]
    field_simp
    ring
  have hFe : dot F e = (-2 * θ ^ 2 * U * lam + -2 * θ * U) / c := by
    rw [hdz, ← hlam, hFu]
  have hee' : dot e e ≤ 4 * θ ^ 2 * U := by
    rw [hee, div_le_iff₀ hc0]
    have : 0 ≤ 4 * θ ^ 2 * U * (θ ^ 2 * U) := by positivity
    rw [hc]
    nlinarith
  -- the moved configuration
  set z' : ℕ → ℕ → ℝ := fun i k => z i k + (if i = i0 then e k else 0) with hz'
  have hz'i : ∀ i, z' i = fun k => z i k + (if i = i0 then e k else 0) := fun i => rfl
  have hsmall : ∀ j, j < 11 → |dot e (z j)| ≤ δ2 / 4 := by
    intro j hj
    have h1 := dot_sq_le e (z j)
    rw [hz j hj, mul_one] at h1
    have h2 : (θ * (8 * (U + 1))) ^ 2 ≤ δ2 ^ 2 := pow_le_pow_left₀ (by positivity) hθ1 2
    have h3 : dot e (z j) ^ 2 ≤ (δ2 / 4) ^ 2 := by nlinarith [sq_nonneg U]
    exact abs_le_of_sq_le_sq h3 (by positivity)
  have htop : ∀ i j, i < 11 → j < 11 → i ≠ j → dot (z i) (z j) ≤ T := by
    intro i j hi hj hij
    have := hsep i j hi hj hij
    rw [hT]
    linarith
  have hdot' : ∀ i j, i < 11 → j < 11 → i ≠ j → dot (z' i) (z' j) ≤ T := by
    intro i j hi hj hij
    rw [hz'i, hz'i, dot_add_add]
    have hs := hsep i j hi hj hij
    by_cases hii : i = i0
    · have hjj : j ≠ i0 := fun h => hij (by rw [hii, h])
      simp only [if_pos hii, if_neg hjj]
      rw [show (fun _ : ℕ => (0 : ℝ)) = fun _ => 0 from rfl, dot_comm (z i) (fun _ => 0), dot_zero_left,
        dot_comm e (fun _ => 0), dot_zero_left]
      have h1 := hsmall j hj
      rw [hT]
      have := (abs_le.mp h1).2
      linarith
    · simp only [if_neg hii]
      by_cases hjj : j = i0
      · simp only [if_pos hjj]
        rw [dot_zero_left, dot_zero_left]
        have h1 := hsmall i hi
        rw [dot_comm] at h1
        rw [hT]
        have := (abs_le.mp h1).2
        linarith
      · simp only [if_neg hjj]
        rw [dot_zero_left, dot_zero_left, dot_comm (z i) (fun _ => 0), dot_zero_left]
        rw [hT]
        linarith
  have hsph' : ∀ i, i < 11 → dot (z' i) (z' i) = 1 := by
    intro i hi
    rw [hz'i, dot_add_add]
    by_cases hii : i = i0
    · simp only [if_pos hii]
      rw [hii, hz0, hze, dot_comm e (z i0), hze, hee]
      field_simp
      ring
    · simp only [if_neg hii]
      rw [dot_zero_left, dot_comm (z i) (fun _ => 0), dot_zero_left, dot_zero_left, hz i hi]
      ring
  have hmin' := hmin z' hsph' (fun i j hi hj hij => lt_of_le_of_lt (hdot' i j hi hj hij) hT1)
  have hmove := energy_move hz hi0 e hT1 hm0 hmT htop hdot'
  rw [← hF] at hmove
  rw [hFe, hee] at hmove
  -- the energy decreases: a contradiction
  have h0 : 0 ≤ (-2 * θ ^ 2 * U * lam + -2 * θ * U) / c + 40 / m ^ 5 * (4 * θ ^ 2 * U / c) := by linarith
  rw [← hK] at h0
  have h1 : 0 ≤ -2 * θ ^ 2 * U * lam + -2 * θ * U + K * (4 * θ ^ 2 * U) := by
    have e1 : (-2 * θ ^ 2 * U * lam + -2 * θ * U) / c + K * (4 * θ ^ 2 * U / c)
        = (-2 * θ ^ 2 * U * lam + -2 * θ * U + K * (4 * θ ^ 2 * U)) / c := by ring
    rw [e1] at h0
    exact (div_nonneg_iff.mp h0).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hc0))
  -- divide by `2 θ U`
  have h2 : 0 ≤ -θ * lam - 1 + 2 * K * θ := by
    have e2 : -2 * θ ^ 2 * U * lam + -2 * θ * U + K * (4 * θ ^ 2 * U) = (2 * θ * U) * (-θ * lam - 1 + 2 * K * θ) := by
      ring
    rw [e2] at h1
    exact nonneg_of_mul_nonneg_right h1 (by positivity)
  have h3 : -θ * lam ≤ θ * |lam| := by
    have := neg_abs_le lam
    nlinarith
  nlinarith

end N11.Analytic
