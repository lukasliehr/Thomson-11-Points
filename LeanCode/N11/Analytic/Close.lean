module

public import N11.Analytic.Expand

/-!
# The theorem for 11 points, analytic part: a minimizer lies within `10⁻¹¹` of the reference configuration (row A9)

The points of the reference configuration `p` do not lie on the sphere exactly. Let `nrm p i = |p_i|`,
`phat p i = p_i / |p_i|` (the normalized configuration) and, for a configuration `z` of the sphere,
`scl p z i = |p_i| z_i`. Then `<z_i, z_j> = <y_i, y_j> / m` and `<phat_i, phat_j> = <p_i, p_j> / m` with `y = scl p z`
and `m = |p_i| |p_j|`, so by `fpot_div` and `taylor3` (with the base `t' = <p_i, p_j> + 1 - m`)

    fpot <z_i, z_j> - fpot <phat_i, phat_j> ≥ √m (W³ Δ + (3/2) W⁵ Δ² + (5/2) W⁷ Δ³),   W = fpot t',

with `Δ = <y_i, y_j> - <p_i, p_j>` (`pair_energy`). The coefficients differ from those of G7 by at most
`22 ν + ε`, `63 ν + 2 ε`, `177 ν + 3 ε` (`scale_pow_close`), so the energy gap is at least the polynomial of
`expand_lower` minus `3·10⁻¹⁶ ∑_{i<j} |Δ_ij| ≥ 3·10⁻¹⁶ · 48 V` (`sum_abs_dlt`). No error is a constant: the base is
the normalized configuration itself.

`energy_gap`: `V² / 50 - 10⁻¹³ V ≤ En z - En (phat p)`, with `V` the norm of the tangential part of `y - p`.
`close_of_min`: if moreover `En z ≤ En (phat p)`, then `V ≤ 5·10⁻¹²` and `|z_i - p_i|² ≤ 10⁻²²` for every point.
-/

@[expose] public section

namespace N11.Analytic

open Finset N11.Local

/-- The norm of a point of the reference configuration. -/
noncomputable def nrm (p : ℕ → ℕ → ℝ) (i : ℕ) : ℝ := Real.sqrt (dot (p i) (p i))

/-- The points `|p_i| z_i`. -/
noncomputable def scl (p z : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ := fun i k => nrm p i * z i k

/-- The normalized reference configuration. -/
noncomputable def phat (p : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ := fun i k => p i k / nrm p i

theorem dot_smul_smul (s s' : ℝ) (u w : ℕ → ℝ) : dot (fun k => s * u k) (fun k => s' * w k) = s * s' * dot u w := by
  simp only [dot_eq]
  ring

theorem dot_div_div (s s' : ℝ) (u w : ℕ → ℝ) : dot (fun k => u k / s) (fun k => w k / s') = dot u w / (s * s') := by
  simp only [dot_eq]
  ring

theorem dot_add_self_le (A B : ℕ → ℝ) :
    dot (fun k => A k + B k) (fun k => A k + B k) ≤ 2 * dot A A + 2 * dot B B := by
  simp only [dot_eq]
  nlinarith [sq_nonneg (A 0 - B 0), sq_nonneg (A 1 - B 1), sq_nonneg (A 2 - B 2)]

theorem sqrt_sub_one_le {m : ℝ} (hm : 0 ≤ m) : |Real.sqrt m - 1| ≤ |m - 1| := by
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt m := ⟨_, rfl⟩
  rw [← hs_def]
  have hs : 0 ≤ s := by rw [hs_def]; exact Real.sqrt_nonneg m
  have hs2 : s ^ 2 = m := by rw [hs_def]; exact Real.sq_sqrt hm
  have e : |m - 1| = |s - 1| * (s + 1) := by
    rw [← hs2, show s ^ 2 - 1 = (s - 1) * (s + 1) by ring, abs_mul, abs_of_pos (by linarith : 0 < s + 1)]
  rw [e]
  have := abs_nonneg (s - 1)
  nlinarith

section Ref

variable {p a b c : ℕ → ℕ → ℝ} {K : Consts}

theorem nrm_sq (G : G7 p a b c K) (hK : CK K) {i : ℕ} (hi : i < 11) : nrm p i ^ 2 = dot (p i) (p i) := by
  unfold nrm
  exact Real.sq_sqrt (by linarith [norm_lo G hK hi])

theorem nrm_pos (G : G7 p a b c K) (hK : CK K) {i : ℕ} (hi : i < 11) : 0 < nrm p i := by
  unfold nrm
  exact Real.sqrt_pos.mpr (by linarith [norm_lo G hK hi])

theorem nrm_sub_one (G : G7 p a b c K) (hK : CK K) {i : ℕ} (hi : i < 11) : |nrm p i - 1| ≤ K.nu := by
  have h := sqrt_sub_one_le (m := dot (p i) (p i)) (by linarith [norm_lo G hK hi])
  exact le_trans h (norm_nu G hi)

/-- The product of the norms of two points. -/
theorem m_close (G : G7 p a b c K) (hK : CK K) {i j : ℕ} (hi : i < 11) (hj : j < 11) :
    |nrm p i * nrm p j - 1| ≤ 3 * K.nu := by
  have h1 := nrm_sub_one G hK hi
  have h2 := nrm_sub_one G hK hj
  have hnu := hK.nu1
  have hnu0 := hK.nu0
  have e : nrm p i * nrm p j - 1 = (nrm p i - 1) * nrm p j + (nrm p j - 1) := by ring
  rw [e]
  have hj1 : nrm p j ≤ 2 := by linarith [(abs_le.mp h2).2]
  have hj0 := nrm_pos G hK hj
  calc |(nrm p i - 1) * nrm p j + (nrm p j - 1)| ≤ |(nrm p i - 1) * nrm p j| + |nrm p j - 1| := abs_add_le _ _
    _ = |nrm p i - 1| * nrm p j + |nrm p j - 1| := by rw [abs_mul, abs_of_pos hj0]
    _ ≤ K.nu * 2 + K.nu := by
        have := mul_le_mul h1 hj1 hj0.le hnu0
        linarith
    _ = 3 * K.nu := by ring

theorem phat_sph (G : G7 p a b c K) (hK : CK K) {i : ℕ} (hi : i < 11) : dot (phat p i) (phat p i) = 1 := by
  have h := dot_div_div (nrm p i) (nrm p i) (p i) (p i)
  have hn := nrm_pos G hK hi
  unfold phat
  rw [h, ← nrm_sq G hK hi]
  field_simp

theorem dot_phat (p : ℕ → ℕ → ℝ) (i j : ℕ) : dot (phat p i) (phat p j) = dot (p i) (p j) / (nrm p i * nrm p j) :=
  dot_div_div _ _ _ _

theorem phat_lt (G : G7 p a b c K) (hK : CK K) {i j : ℕ} (hi : i < 11) (hj : j < 11) (hij : i ≠ j) :
    dot (phat p i) (phat p j) < 1 := by
  rw [dot_phat]
  have hm := m_close G hK hi hj
  have hnu := hK.nu1
  have hm0 : 99 / 100 ≤ nrm p i * nrm p j := by linarith [(abs_le.mp hm).1]
  have ht : dot (p i) (p j) ≤ 17 / 32 := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact le_trans (G.top i j h hj) hK.tmax
    · rw [dot_comm]
      exact le_trans (G.top j i h hi) hK.tmax
  rw [div_lt_one (by linarith)]
  linarith

/-- **The coefficients at the normalized base.** -/
theorem scale_pow_close (G : G7 p a b c K) (hK : CK K) (n : ℕ) {i j : ℕ} (hij : i < j) (hj : j < 11) :
    |Real.sqrt (nrm p i * nrm p j) * fpot (dot (p i) (p j) + 1 - nrm p i * nrm p j) ^ (n + 1)
        - fpot (dot (p i) (p j)) ^ (n + 1)|
      ≤ ((9 / 8) ^ (n + 1) + (n + 1) * (9 / 8) ^ n * (3 / 2)) * (3 * K.nu) := by
  have hi : i < 11 := by omega
  set m := nrm p i * nrm p j with hm_def
  set t := dot (p i) (p j) with ht_def
  have hm := m_close G hK hi hj
  rw [← hm_def] at hm
  have hnu := hK.nu1
  have hnu0 := hK.nu0
  have hm0 : 0 ≤ m := mul_nonneg (nrm_pos G hK hi).le (nrm_pos G hK hj).le
  have ht : t ≤ 17 / 32 := le_trans (G.top i j hij hj) hK.tmax
  have ht' : t + 1 - m ≤ 3 / 5 := by linarith [(abs_le.mp hm).1]
  have h1 := sqrt_sub_one_le hm0
  have h2 := fpot_pow_lip n ht' (by linarith : t ≤ 3 / 5)
  have e1 : t + 1 - m - t = -(m - 1) := by ring
  rw [e1, abs_neg] at h2
  have hW := pow_le_pow_left₀ (fpot_nonneg _) (fpot_le ht') (n + 1)
  have hW0 : 0 ≤ fpot (t + 1 - m) ^ (n + 1) := pow_nonneg (fpot_nonneg _) _
  have e2 : Real.sqrt m * fpot (t + 1 - m) ^ (n + 1) - fpot t ^ (n + 1)
      = (Real.sqrt m - 1) * fpot (t + 1 - m) ^ (n + 1) + (fpot (t + 1 - m) ^ (n + 1) - fpot t ^ (n + 1)) := by
    ring
  rw [e2]
  have h3 : |(Real.sqrt m - 1) * fpot (t + 1 - m) ^ (n + 1)| ≤ |m - 1| * (9 / 8) ^ (n + 1) := by
    rw [abs_mul, abs_of_nonneg hW0]
    exact mul_le_mul h1 hW hW0 (abs_nonneg _)
  have h4 := abs_add_le ((Real.sqrt m - 1) * fpot (t + 1 - m) ^ (n + 1))
    (fpot (t + 1 - m) ^ (n + 1) - fpot t ^ (n + 1))
  have h5 : 0 ≤ (9 / 8 : ℝ) ^ (n + 1) := by positivity
  have h6 : 0 ≤ ((n : ℝ) + 1) * (9 / 8) ^ n * (3 / 2) := by positivity
  have h7 : |m - 1| * (9 / 8) ^ (n + 1) ≤ 3 * K.nu * (9 / 8) ^ (n + 1) := mul_le_mul_of_nonneg_right hm h5
  have h8 : ((n : ℝ) + 1) * (9 / 8) ^ n * (3 / 2) * |m - 1| ≤ ((n : ℝ) + 1) * (9 / 8) ^ n * (3 / 2) * (3 * K.nu) :=
    mul_le_mul_of_nonneg_left hm h6
  nlinarith

end Ref

section Gap

variable {p a b c : ℕ → ℕ → ℝ} {K : Consts}

/-- **The energy of a pair at the normalized base**: the Taylor polynomial of degree three. -/
theorem pair_energy (G : G7 p a b c K) (hK : CK K) {z : ℕ → ℕ → ℝ} (hz : ∀ i, i < 11 → dot (z i) (z i) = 1)
    (hzd : ∀ i j, i < 11 → j < 11 → i ≠ j → dot (z i) (z j) < 1) {i j : ℕ} (hij : i < j) (hj : j < 11) :
    Real.sqrt (nrm p i * nrm p j) * fpot (dot (p i) (p j) + 1 - nrm p i * nrm p j) ^ 3 * dlt p (scl p z) i j
        + 3 / 2 * Real.sqrt (nrm p i * nrm p j) * fpot (dot (p i) (p j) + 1 - nrm p i * nrm p j) ^ 5
          * dlt p (scl p z) i j ^ 2
        + 5 / 2 * Real.sqrt (nrm p i * nrm p j) * fpot (dot (p i) (p j) + 1 - nrm p i * nrm p j) ^ 7
          * dlt p (scl p z) i j ^ 3
      ≤ fpot (dot (z i) (z j)) - fpot (dot (phat p i) (phat p j)) := by
  have hi : i < 11 := by omega
  set m := nrm p i * nrm p j with hm_def
  set t := dot (p i) (p j) with ht_def
  have hm := m_close G hK hi hj
  rw [← hm_def] at hm
  have hnu := hK.nu1
  have hm0 : 0 < m := mul_pos (nrm_pos G hK hi) (nrm_pos G hK hj)
  have hm1 : 99 / 100 ≤ m := by linarith [(abs_le.mp hm).1]
  have ht : t ≤ 17 / 32 := le_trans (G.top i j hij hj) hK.tmax
  have hyz : dot (scl p z i) (scl p z j) = m * dot (z i) (z j) := by
    unfold scl
    rw [dot_smul_smul]
  have hzlt := hzd i j hi hj (ne_of_lt hij)
  have hz1 : dot (z i) (z j) = dot (scl p z i) (scl p z j) / m := by
    rw [hyz]
    field_simp
  have hlt1 : dot (scl p z i) (scl p z j) < m := by
    rw [hyz]
    nlinarith
  have hlt2 : t < m := by linarith
  have hE1 : fpot (dot (z i) (z j)) = Real.sqrt m * fpot (dot (scl p z i) (scl p z j) + 1 - m) := by
    rw [hz1]
    exact fpot_div hm0 hlt1
  have hE2 : fpot (dot (phat p i) (phat p j)) = Real.sqrt m * fpot (t + 1 - m) := by
    rw [dot_phat, ← hm_def]
    exact fpot_div hm0 hlt2
  have hT := taylor3 (t0 := t + 1 - m) (t := dot (scl p z i) (scl p z j) + 1 - m) (by linarith) (by linarith)
  have e : dot (scl p z i) (scl p z j) + 1 - m - (t + 1 - m) = dlt p (scl p z) i j := by
    unfold dlt
    rw [← ht_def]
    ring
  rw [e] at hT
  rw [hE1, hE2]
  have hs : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have h := mul_le_mul_of_nonneg_left hT hs
  nlinarith

/-- The coefficients at the normalized base differ from those of G7 by little: the polynomial of a pair. -/
theorem pair_coef (G : G7 p a b c K) (hK : CK K) {i j : ℕ} (hij : i < j) (hj : j < 11) {Δ : ℝ}
    (hΔ : |Δ| ≤ 1 / 25) :
    a i j * Δ + b i j * Δ ^ 2 + c i j * Δ ^ 3 - 3 / 10 ^ 16 * |Δ|
      ≤ Real.sqrt (nrm p i * nrm p j) * fpot (dot (p i) (p j) + 1 - nrm p i * nrm p j) ^ 3 * Δ
        + 3 / 2 * Real.sqrt (nrm p i * nrm p j) * fpot (dot (p i) (p j) + 1 - nrm p i * nrm p j) ^ 5 * Δ ^ 2
        + 5 / 2 * Real.sqrt (nrm p i * nrm p j) * fpot (dot (p i) (p j) + 1 - nrm p i * nrm p j) ^ 7 * Δ ^ 3 := by
  obtain ⟨A, hA⟩ : ∃ A, A = Real.sqrt (nrm p i * nrm p j) * fpot (dot (p i) (p j) + 1 - nrm p i * nrm p j) ^ 3 :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = Real.sqrt (nrm p i * nrm p j) * fpot (dot (p i) (p j) + 1 - nrm p i * nrm p j) ^ 5 :=
    ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = Real.sqrt (nrm p i * nrm p j) * fpot (dot (p i) (p j) + 1 - nrm p i * nrm p j) ^ 7 :=
    ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = fpot (dot (p i) (p j)) := ⟨_, rfl⟩
  have ht1 : dot (p i) (p j) ≤ 17 / 32 := le_trans (G.top i j hij hj) hK.tmax
  have hlt : dot (p i) (p j) < 1 := by linarith
  have hw0 : 0 < w := by rw [hw]; exact fpot_pos hlt
  have hwsq : w ^ 2 * (2 - 2 * dot (p i) (p j)) = 1 := by rw [hw]; exact fpot_sq hlt
  obtain ⟨ha, hb, hc⟩ := G.enc i j hij hj w hw0 hwsq
  have h3 := scale_pow_close G hK 2 hij hj
  have h5 := scale_pow_close G hK 4 hij hj
  have h7 := scale_pow_close G hK 6 hij hj
  rw [← hA, ← hw] at h3
  rw [← hB, ← hw] at h5
  rw [← hC, ← hw] at h7
  norm_num at h3 h5 h7
  have hnu := hK.nu1
  have hnu0 := hK.nu0
  have he := hK.eps1
  have he0 := hK.eps0
  -- the three differences
  have dA : |A - a i j| ≤ 25 / 10 ^ 17 := by
    have e : A - a i j = (A - w ^ 3) + (w ^ 3 - a i j) := by ring
    have h1 : |A - a i j| ≤ |A - w ^ 3| + |w ^ 3 - a i j| := by rw [e]; exact abs_add_le _ _
    rw [abs_sub_comm (w ^ 3)] at h1
    linarith
  have dB : |3 / 2 * B - b i j| ≤ 1 / 10 ^ 15 := by
    have e : 3 / 2 * B - b i j = 3 / 2 * (B - w ^ 5) + (3 / 2 * w ^ 5 - b i j) := by ring
    have h1 : |3 / 2 * B - b i j| ≤ |3 / 2 * (B - w ^ 5)| + |3 / 2 * w ^ 5 - b i j| := by
      rw [e]; exact abs_add_le _ _
    rw [abs_sub_comm (3 / 2 * w ^ 5), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at h1
    linarith
  have dC : |5 / 2 * C - c i j| ≤ 2 / 10 ^ 15 := by
    have e : 5 / 2 * C - c i j = 5 / 2 * (C - w ^ 7) + (5 / 2 * w ^ 7 - c i j) := by ring
    have h1 : |5 / 2 * C - c i j| ≤ |5 / 2 * (C - w ^ 7)| + |5 / 2 * w ^ 7 - c i j| := by
      rw [e]; exact abs_add_le _ _
    rw [abs_sub_comm (5 / 2 * w ^ 7), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2)] at h1
    linarith
  -- the polynomial
  have hD0 := abs_nonneg Δ
  have hD2 : Δ ^ 2 ≤ 1 / 25 * |Δ| := by
    have h1 := mul_le_mul_of_nonneg_left hΔ hD0
    rw [← sq_abs, sq]
    linarith
  have hD3 : |Δ| ^ 3 ≤ 1 / 625 * |Δ| := by
    have h1 := mul_le_mul_of_nonneg_left hΔ hD0
    have h2 : |Δ| * |Δ| ≤ 1 / 25 * |Δ| := by linarith
    have h3 : |Δ| * |Δ| * |Δ| ≤ 1 / 25 * |Δ| * (1 / 25) :=
      mul_le_mul h2 hΔ hD0 (by positivity)
    have e : |Δ| ^ 3 = |Δ| * |Δ| * |Δ| := by ring
    rw [e]
    linarith
  have t1 : -(25 / 10 ^ 17 * |Δ|) ≤ (A - a i j) * Δ := by
    have h1 := neg_abs_le ((A - a i j) * Δ)
    rw [abs_mul] at h1
    have h2 : |A - a i j| * |Δ| ≤ 25 / 10 ^ 17 * |Δ| := mul_le_mul_of_nonneg_right dA hD0
    linarith
  have t2 : -(1 / 10 ^ 15 * (1 / 25 * |Δ|)) ≤ (3 / 2 * B - b i j) * Δ ^ 2 := by
    have h1 := neg_abs_le ((3 / 2 * B - b i j) * Δ ^ 2)
    rw [abs_mul, abs_of_nonneg (sq_nonneg Δ)] at h1
    have h2 : |3 / 2 * B - b i j| * Δ ^ 2 ≤ 1 / 10 ^ 15 * (1 / 25 * |Δ|) :=
      mul_le_mul dB hD2 (sq_nonneg _) (by norm_num)
    linarith
  have t3 : -(2 / 10 ^ 15 * (1 / 625 * |Δ|)) ≤ (5 / 2 * C - c i j) * Δ ^ 3 := by
    have h1 := neg_abs_le ((5 / 2 * C - c i j) * Δ ^ 3)
    rw [abs_mul, abs_pow] at h1
    have h2 : |5 / 2 * C - c i j| * |Δ| ^ 3 ≤ 2 / 10 ^ 15 * (1 / 625 * |Δ|) :=
      mul_le_mul dC hD3 (pow_nonneg hD0 3) (by norm_num)
    linarith
  have e : A * Δ + 3 / 2 * B * Δ ^ 2 + 5 / 2 * C * Δ ^ 3
      = (a i j * Δ + b i j * Δ ^ 2 + c i j * Δ ^ 3)
        + ((A - a i j) * Δ + (3 / 2 * B - b i j) * Δ ^ 2 + (5 / 2 * C - c i j) * Δ ^ 3) := by ring
  have e2 : 3 / 2 * Real.sqrt (nrm p i * nrm p j) * fpot (dot (p i) (p j) + 1 - nrm p i * nrm p j) ^ 5 * Δ ^ 2
      = 3 / 2 * B * Δ ^ 2 := by rw [hB]; ring
  have e3 : 5 / 2 * Real.sqrt (nrm p i * nrm p j) * fpot (dot (p i) (p j) + 1 - nrm p i * nrm p j) ^ 7 * Δ ^ 3
      = 5 / 2 * C * Δ ^ 3 := by rw [hC]; ring
  rw [← hA, e2, e3, e]
  linarith

/-- `(∑_{i<j} F_ij)² ≤ 55 ∑_{i<j} F_ij²`. -/
theorem sumP_sq_le (F : ℕ → ℕ → ℝ) : sumP F ^ 2 ≤ 55 * sumP (fun i j => F i j ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (range 11 ×ˢ range 11)
    (fun x => if x.1 < x.2 then (1 : ℝ) else 0) (fun x => if x.1 < x.2 then F x.1 x.2 else 0)
  simp only [Finset.sum_product] at h
  have e1 : ∑ i ∈ range 11, ∑ j ∈ range 11, (if i < j then (1 : ℝ) else 0) * (if i < j then F i j else 0) = sumP F := by
    unfold sumP
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases hij : i < j <;> simp [hij]
  have e2 : ∑ i ∈ range 11, ∑ j ∈ range 11, (if i < j then (1 : ℝ) else 0) ^ 2 = 55 := by
    have := sumP_const 1
    unfold sumP at this
    rw [mul_one] at this
    rw [← this]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases hij : i < j <;> simp [hij]
  have e3 : ∑ i ∈ range 11, ∑ j ∈ range 11, (if i < j then F i j else 0) ^ 2 = sumP (fun i j => F i j ^ 2) := by
    unfold sumP
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases hij : i < j <;> simp [hij]
  rw [e1, e2, e3] at h
  exact h

/-- **The changes of the inner products of a pair**, for a configuration near the reference configuration. -/
theorem dlt_bounds (G : G7 p a b c K) (hK : CK K) {y : ℕ → ℕ → ℝ} (A : Aligned p y)
    (hX : nsq (dsub y p) ≤ 63 / 2000000) {i j : ℕ} (hij : i < j) (hj : j < 11) :
    |dlt p y i j| ≤ 1 / 25 ∧
      dlt p y i j ^ 2 ≤ 41 / 10 * (dot (tang p (dsub y p) i) (tang p (dsub y p) i)
        + dot (tang p (dsub y p) j) (tang p (dsub y p) j)) := by
  have hi : i < 11 := by omega
  set d := dsub y p with hd
  set v := tang p d with hv
  have hqi : 0 ≤ dot (v i) (v i) := dot_self_nonneg _
  have hqj : 0 ≤ dot (v j) (v j) := dot_self_nonneg _
  have hDi : 0 ≤ dot (d i) (d i) := dot_self_nonneg _
  have hDj : 0 ≤ dot (d j) (d j) := dot_self_nonneg _
  have hDXi : dot (d i) (d i) ≤ 63 / 2000000 := le_trans (D_le_nsq d hi) hX
  have hDXj : dot (d j) (d j) ≤ 63 / 2000000 := le_trans (D_le_nsq d hj) hX
  have hqXi : dot (v i) (v i) ≤ 63 / 2000000 := le_trans (q_le_D G hK d hi) hDXi
  have hqXj : dot (v j) (v j) ≤ 63 / 2000000 := le_trans (q_le_D G hK d hj) hDXj
  have hP1 : dot (p i) (v j) ^ 2 ≤ 101 / 100 * dot (v j) (v j) := by
    have h1 := dot_sq_le (p i) (v j)
    have h2 := norm_hi G hK hi
    nlinarith
  have hP2 : dot (v i) (p j) ^ 2 ≤ 101 / 100 * dot (v i) (v i) := by
    have h1 := dot_sq_le (v i) (p j)
    have h2 := norm_hi G hK hj
    nlinarith
  have hL2 : Lf p v i j ^ 2 ≤ 2 * (101 / 100) * (dot (v i) (v i) + dot (v j) (v j)) := by
    unfold Lf
    nlinarith [sq_nonneg (dot (p i) (v j) - dot (v i) (p j))]
  have hL : |Lf p v i j| ≤ 1 / 50 := abs_le_of_sq_le_sq (by nlinarith) (by norm_num)
  have ht := t_abs G hK hi hj
  have hri := r_abs G hK A hi
  have hrj := r_abs G hK A hj
  have hDqi := D_le_q G hK A hX hi
  have hDqj := D_le_q G hK A hX hj
  set η := (rco p d i + rco p d j) * dot (p i) (p j) + dot (d i) (d j) with hη_def
  have hη : |η| ≤ 102 / 100 * (dot (d i) (d i) + dot (d j) (d j)) := by
    have h1 : |(rco p d i + rco p d j) * dot (p i) (p j)| ≤ (|rco p d i| + |rco p d j|) * (101 / 100) := by
      rw [abs_mul]
      exact mul_le_mul (abs_add_le _ _) ht (abs_nonneg _) (by positivity)
    have h2 := two_mul_abs_dot_le (d i) (d j)
    have h3 : |η| ≤ |(rco p d i + rco p d j) * dot (p i) (p j)| + |dot (d i) (d j)| := abs_add_le _ _
    linarith
  have hη1 : |η| ≤ 1 / 100 := by linarith
  have hΔ : dlt p y i j = Lf p v i j + η := dlt_eq p y i j
  constructor
  · rw [hΔ]
    have := abs_add_le (Lf p v i j) η
    linarith
  · rw [hΔ]
    have h1 : η ^ 2 ≤ 1 / 100 * |η| := by
      rw [← sq_abs]
      nlinarith [abs_nonneg η]
    have h2 : |η| ≤ 102 / 100 * ((1 + 1 / 10 ^ 5) * (dot (v i) (v i) + dot (v j) (v j))) := by linarith
    nlinarith [sq_nonneg (Lf p v i j - η)]

theorem nsq_d_le (G : G7 p a b c K) (hK : CK K) {y : ℕ → ℕ → ℝ} (A : Aligned p y)
    (hX : nsq (dsub y p) ≤ 63 / 2000000) : nsq (dsub y p) ≤ (1 + 1 / 10 ^ 5) * nsq (tang p (dsub y p)) := by
  unfold nsq
  rw [Finset.mul_sum]
  exact sum_le_sum fun i hi => D_le_q G hK A hX (mem_range.mp hi)

/-- **The energy gap.** -/
theorem energy_gap (G : G7 p a b c K) (hK : CK K) {z : ℕ → ℕ → ℝ} (hz : ∀ i, i < 11 → dot (z i) (z i) = 1)
    (hzd : ∀ i j, i < 11 → j < 11 → i ≠ j → dot (z i) (z j) < 1) (A : Aligned p (scl p z))
    (hX : nsq (dsub (scl p z) p) ≤ 63 / 2000000) :
    1 / 50 * nsq (tang p (dsub (scl p z) p)) - 1 / 10 ^ 13 * Real.sqrt (nsq (tang p (dsub (scl p z) p)))
      ≤ En z - En (phat p) := by
  set y := scl p z with hy
  set v := tang p (dsub y p) with hv
  set V := Real.sqrt (nsq v) with hV
  have hQ : 0 ≤ nsq v := nsq_nonneg v
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  have hV2 : V ^ 2 = nsq v := Real.sq_sqrt hQ
  have hQX : nsq v ≤ 63 / 2000000 := le_trans (nsq_tang_le G hK _) hX
  have hVm : V ≤ 5613 / 1000000 := by
    have : V ^ 2 ≤ (5613 / 1000000) ^ 2 := by rw [hV2]; linarith
    exact abs_le_of_sq_le_sq' this (by norm_num) |>.2
  -- the pairs
  have hpair : ∀ i j, i < j → j < 11 →
      a i j * dlt p y i j + b i j * dlt p y i j ^ 2 + c i j * dlt p y i j ^ 3 - 3 / 10 ^ 16 * |dlt p y i j|
        ≤ fpot (dot (z i) (z j)) - fpot (dot (phat p i) (phat p j)) := by
    intro i j hij hj
    have h1 := pair_coef G hK hij hj (dlt_bounds G hK A hX hij hj).1
    have h2 := pair_energy G hK hz hzd hij hj
    linarith
  have hsum := sumP_le hpair
  rw [sumP_sub, sumP_mul] at hsum
  have hE : En z - En (phat p) = sumP (fun i j => fpot (dot (z i) (z j)) - fpot (dot (phat p i) (phat p j))) := by
    unfold En
    rw [sumP_sub]
  rw [← hE] at hsum
  -- the sum of the absolute values
  have habs : sumP (fun i j => |dlt p y i j|) ≤ 48 * V := by
    have h1 := sumP_sq_le (fun i j => |dlt p y i j|)
    have h2 : sumP (fun i j => |dlt p y i j| ^ 2) ≤ sumP (fun i j => 41 / 10 * (dot (v i) (v i) + dot (v j) (v j))) :=
      sumP_le fun i j hij hj => by rw [sq_abs]; exact (dlt_bounds G hK A hX hij hj).2
    rw [sumP_mul, sumP_sum_pts] at h2
    have h3 : sumP (fun i j => |dlt p y i j|) ^ 2 ≤ (48 * V) ^ 2 := by
      have e : ∑ i ∈ range 11, dot (v i) (v i) = nsq v := rfl
      rw [e] at h2
      nlinarith
    exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2
  have hlow := expand_lower G hK A hX
  rw [← hv, ← hV] at hlow
  -- the constants
  have hk := hK.kappa
  have hc3 := hK.c31
  have hc30 := hK.c30
  have hg := hK.gam1
  have hg0 := hK.gam0
  have hnu := hK.nu1
  have h4 : K.c3 * V ^ 3 ≤ 113 / 32 * (5613 / 1000000) * V ^ 2 := by
    have : V ^ 3 = V * V ^ 2 := by ring
    rw [this]
    have h5 : K.c3 * V ≤ 113 / 32 * (5613 / 1000000) := mul_le_mul hc3 hVm hV0 (by norm_num)
    nlinarith [sq_nonneg V]
  have h6 : 150 * nsq v ^ 2 ≤ 150 * (63 / 2000000) * nsq v := by nlinarith
  have h7 : K.gam * V ≤ 1 / 10 ^ 17 * V := mul_le_mul_of_nonneg_right hg hV0
  rw [hV2] at h4
  nlinarith

/-- **A minimizer lies within `10⁻¹¹` of the reference configuration.** -/
theorem close_of_min (G : G7 p a b c K) (hK : CK K) {z : ℕ → ℕ → ℝ} (hz : ∀ i, i < 11 → dot (z i) (z i) = 1)
    (hzd : ∀ i j, i < 11 → j < 11 → i ≠ j → dot (z i) (z j) < 1) (A : Aligned p (scl p z))
    (hX : nsq (dsub (scl p z) p) ≤ 63 / 2000000) (hmin : En z ≤ En (phat p)) :
    ∀ i, i < 11 → dot (fun k => z i k - p i k) (fun k => z i k - p i k) ≤ 1 / 10 ^ 22 := by
  have hgap := energy_gap G hK hz hzd A hX
  set y := scl p z with hy
  set v := tang p (dsub y p) with hv
  set V := Real.sqrt (nsq v) with hV
  have hQ : 0 ≤ nsq v := nsq_nonneg v
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  have hV2 : V ^ 2 = nsq v := Real.sq_sqrt hQ
  have hVs : V ≤ 5 / 10 ^ 12 := by
    rw [← hV2] at hgap
    by_contra hlt
    have hlt' := not_le.mp hlt
    nlinarith
  have hX2 := nsq_d_le G hK A hX
  rw [← hv] at hX2
  intro i hi
  have hn := nrm_pos G hK hi
  have hn2 := nrm_sq G hK hi
  have hn1 := nrm_sub_one G hK hi
  have hnu := hK.nu1
  have hlo := norm_lo G hK hi
  -- `z_i - p_i = d_i / |p_i| + p_i (1 / |p_i| - 1)`
  have hz_eq : ∀ k, z i k - p i k = dsub y p i k / nrm p i + p i k * (1 / nrm p i - 1) := by
    intro k
    unfold dsub
    rw [hy]
    unfold scl
    field_simp
    ring
  have h1 : dot (fun k => z i k - p i k) (fun k => z i k - p i k)
      ≤ 2 * (dot (dsub y p i) (dsub y p i) / nrm p i ^ 2) + 2 * ((1 / nrm p i - 1) ^ 2 * dot (p i) (p i)) := by
    have e1 : (fun k => z i k - p i k) = fun k => dsub y p i k / nrm p i + p i k * (1 / nrm p i - 1) :=
      funext hz_eq
    rw [e1]
    have h2 := dot_add_self_le (fun k => dsub y p i k / nrm p i) (fun k => (1 / nrm p i - 1) * p i k)
    have e2 : (fun k => dsub y p i k / nrm p i + (1 / nrm p i - 1) * p i k)
        = fun k => dsub y p i k / nrm p i + p i k * (1 / nrm p i - 1) := funext fun k => by ring
    rw [e2, dot_div_div, dot_smul_smul] at h2
    have e3 : nrm p i * nrm p i = nrm p i ^ 2 := by ring
    rw [e3] at h2
    linarith
  have h2 : (1 / nrm p i - 1) ^ 2 * dot (p i) (p i) = (1 - nrm p i) ^ 2 := by
    rw [← hn2]
    field_simp
  have h3 : dot (dsub y p i) (dsub y p i) ≤ (1 + 1 / 10 ^ 5) * (5 / 10 ^ 12) ^ 2 := by
    have a1 := D_le_nsq (dsub y p) hi
    have a2 : V ^ 2 ≤ (5 / 10 ^ 12) ^ 2 := pow_le_pow_left₀ hV0 hVs 2
    rw [hV2] at a2
    nlinarith
  have h4 : dot (dsub y p i) (dsub y p i) / nrm p i ^ 2 ≤ dot (dsub y p i) (dsub y p i) * (100 / 99) := by
    rw [hn2, div_le_iff₀ (by linarith)]
    have := dot_self_nonneg (dsub y p i)
    nlinarith
  have h5 : (1 - nrm p i) ^ 2 ≤ (1 / 10 ^ 17) ^ 2 := by
    rw [← sq_abs, abs_sub_comm]
    exact pow_le_pow_left₀ (abs_nonneg _) (le_trans hn1 hnu) 2
  rw [h2] at h1
  nlinarith

end Gap

end N11.Analytic
