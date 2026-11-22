module

public import N11.Analytic.Close

/-!
# The theorem for 11 points, analytic part: uniqueness (row A10)

Let `Z` and `Z'` be configurations of the sphere within `ζ = 10⁻¹¹` of the reference configuration `p` (in each
point), both in the gauge (`∑_i |p_i| Z_i p_iᵀ` symmetric), with `En Z' ≤ En Z`, and let `Z` be critical
(`frc Z (alpha Z) i = λ_i Z_i`). Then `Z' = Z` (`unique`).

The proof uses `taylor3` with the base `Z`, where the coefficients are exact. For `e = Z' - Z` the change of an inner
product is `Δ'_ij = L^Z_ij(e) + <e_i, e_j>`, and by the criticality the term of the first order is exactly
`∑_{i<j} α_ij ψ^Z_ij(e)` (`first_order`), since `2 <Z_i, e_i> + |e_i|² = 0`. Hence

    0 ≥ En Z' - En Z ≥ ∑_{i<j} α ψ^Z(e) + β Δ'² + ς Δ'³ ≥ Q_p(e) - (300 ζ + 5 ε) ∑_{i<j} (|e_i|² + |e_j|²),

where `Q_p = Qf p a b` is the quadratic form of G7: the coefficients at `Z` differ from those at `p` by at most
`12 ζ + ε` and `37 ζ + 2 ε`, `L^Z - L^p` and `<e_i, e_j>` are of the order `ζ |e|`, and `|Δ'| ≤ 6 ζ` (`pair_unique`).
The penalty is small: `penf p e ≤ (4 ζ² + 200 ν²) |e|²`, since `<p_i, e_i> = -|e_i|²/2 + <p_i - Z_i, e_i>` and the
gauge of `Z` and `Z'` differ from that of `e` by the factors `|p_i| - 1` (`penf_small`). By the field `hess` of G7,
`κ |e|² ≤ Q_p(e) + 16384 penf p e ≤ 4·10⁻⁸ |e|²`, so `e = 0`.
-/

@[expose] public section

namespace N11.Analytic

open Finset N11.Local

/-! ## A pair -/

/-- **The polynomial of a pair at the base `Z`**, compared with the quadratic form at `p`. -/
theorem pair_unique {α a β b ς ψZ ψp L μ Ei Ej ζ A1 B1 δt : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 100)
    (hα : |α - a| ≤ A1) (hβ : |β - b| ≤ B1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 3) (hς0 : 0 ≤ ς) (hς1 : ς ≤ 6)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 3 / 2) (hEi : 0 ≤ Ei) (hEj : 0 ≤ Ej) (hE : Ei + Ej ≤ 8 * ζ ^ 2)
    (hψZ : |ψZ| ≤ Ei + Ej) (hψ : |ψZ - ψp| ≤ δt * (Ei + Ej))
    (hL : L ^ 2 ≤ 203 / 100 * (Ei + Ej)) (hμ : μ ^ 2 ≤ 15 * ζ ^ 2 * (Ei + Ej)) :
    a * ψp + b * L ^ 2 - (A1 + 3 / 2 * δt + 54 * ζ + 203 / 100 * B1 + 150 * ζ) * (Ei + Ej)
      ≤ α * ψZ + β * (L + μ) ^ 2 + ς * (L + μ) ^ 3 := by
  have hS : 0 ≤ Ei + Ej := by linarith
  have hA1 : 0 ≤ A1 := le_trans (abs_nonneg _) hα
  have hB1 : 0 ≤ B1 := le_trans (abs_nonneg _) hβ
  -- the first term
  have t1 : a * ψp - (A1 + 3 / 2 * δt) * (Ei + Ej) ≤ α * ψZ := by
    have e : α * ψZ = a * ψp + (α - a) * ψZ + a * (ψZ - ψp) := by ring
    have h1 : |(α - a) * ψZ| ≤ A1 * (Ei + Ej) := by
      rw [abs_mul]
      exact mul_le_mul hα hψZ (abs_nonneg _) hA1
    have h2 : |a * (ψZ - ψp)| ≤ 3 / 2 * (δt * (Ei + Ej)) := by
      rw [abs_mul, abs_of_nonneg ha0]
      exact mul_le_mul ha1 hψ (abs_nonneg _) (by norm_num)
    have h3 := neg_abs_le ((α - a) * ψZ)
    have h4 := neg_abs_le (a * (ψZ - ψp))
    rw [e]
    linarith
  -- the square: `β (L + μ)² ≥ β L² - β (ζ L² + μ² / ζ)`
  have t2 : β * L ^ 2 - 54 * ζ * (Ei + Ej) ≤ β * (L + μ) ^ 2 := by
    have h1 : -(ζ * L ^ 2 + μ ^ 2 / ζ) ≤ 2 * L * μ := by
      have h2 : 0 ≤ (ζ * L + μ) ^ 2 / ζ := by positivity
      have e : (ζ * L + μ) ^ 2 / ζ = ζ * L ^ 2 + 2 * L * μ + μ ^ 2 / ζ := by
        field_simp
        ring
      linarith
    have h3 : μ ^ 2 / ζ ≤ 15 * ζ * (Ei + Ej) := by
      rw [div_le_iff₀ hζ]
      linarith
    have h4 : ζ * L ^ 2 ≤ ζ * (203 / 100 * (Ei + Ej)) := mul_le_mul_of_nonneg_left hL hζ.le
    have h7 : ζ * L ^ 2 + μ ^ 2 / ζ ≤ 18 * ζ * (Ei + Ej) := by nlinarith
    have h8 : 0 ≤ ζ * L ^ 2 + μ ^ 2 / ζ := by positivity
    have h9 : β * (ζ * L ^ 2 + μ ^ 2 / ζ) ≤ 3 * (18 * ζ * (Ei + Ej)) := mul_le_mul hβ1 h7 h8 (by norm_num)
    have h5 : -(β * (ζ * L ^ 2 + μ ^ 2 / ζ)) ≤ β * (2 * L * μ) := by
      have := mul_le_mul_of_nonneg_left h1 hβ0
      linarith
    have e : β * (L + μ) ^ 2 = β * L ^ 2 + β * (2 * L * μ) + β * μ ^ 2 := by ring
    have h10 : 0 ≤ β * μ ^ 2 := mul_nonneg hβ0 (sq_nonneg _)
    linarith
  -- the coefficient `β` against `b`
  have t3 : b * L ^ 2 - 203 / 100 * B1 * (Ei + Ej) ≤ β * L ^ 2 := by
    have h1 := neg_abs_le ((β - b) * L ^ 2)
    rw [abs_mul, abs_of_nonneg (sq_nonneg L)] at h1
    have h2 : |β - b| * L ^ 2 ≤ B1 * (203 / 100 * (Ei + Ej)) :=
      mul_le_mul hβ hL (sq_nonneg _) hB1
    have e : β * L ^ 2 = b * L ^ 2 + (β - b) * L ^ 2 := by ring
    linarith
  -- the cube
  have t4 : -(150 * ζ * (Ei + Ej)) ≤ ς * (L + μ) ^ 3 := by
    have hζ2 : ζ ^ 2 ≤ 1 / 10 ^ 4 := by nlinarith
    have hμ' : μ ^ 2 ≤ 15 / 10 ^ 4 * (Ei + Ej) := by nlinarith
    have h1 : (L + μ) ^ 2 ≤ 41 / 10 * (Ei + Ej) := by nlinarith [sq_nonneg (L - μ)]
    have h2 : (L + μ) ^ 2 ≤ (6 * ζ) ^ 2 := by nlinarith
    have h3 : |L + μ| ≤ 6 * ζ := abs_le_of_sq_le_sq h2 (by linarith)
    have h4 : |ς * (L + μ) ^ 3| ≤ 6 * (6 * ζ * (41 / 10 * (Ei + Ej))) := by
      rw [abs_mul, abs_of_nonneg hς0, show (L + μ) ^ 3 = (L + μ) * (L + μ) ^ 2 by ring, abs_mul,
        abs_of_nonneg (sq_nonneg (L + μ))]
      have h5 : |L + μ| * (L + μ) ^ 2 ≤ 6 * ζ * (41 / 10 * (Ei + Ej)) :=
        mul_le_mul h3 h1 (sq_nonneg _) (by linarith)
      exact mul_le_mul hς1 h5 (by positivity) (by norm_num)
    have h6 := neg_abs_le (ς * (L + μ) ^ 3)
    nlinarith
  linarith

/-! ## The first-order term at a critical configuration -/

theorem dot_frc (z w : ℕ → ℕ → ℝ) (i : ℕ) (u : ℕ → ℝ) :
    dot (frc z w i) u = ∑ j ∈ range 11, if j = i then 0 else w i j * dot (z j) u := by
  have e1 : frc z w i = fun k => ∑ j ∈ range 11, (fun j k => if j = i then 0 else w i j * z j k) j k := by
    funext k
    unfold frc
    rfl
  rw [e1, dot_sum_left]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : j = i
  · rw [if_pos h]
    unfold dot
    simp only [if_pos h, zero_mul, sum_const_zero]
  · rw [if_neg h]
    unfold dot
    simp only [if_neg h]
    rw [Finset.mul_sum]
    exact sum_congr rfl fun k _ => by ring

/-- **The first-order term at a critical configuration of the sphere** is `∑_{i<j} α_ij ψ^Z_ij(e)`. -/
theorem first_order {Z e : ℕ → ℕ → ℝ}
    (he : ∀ i, i < 11 → 2 * dot (Z i) (e i) + dot (e i) (e i) = 0)
    (hcrit : ∀ i, i < 11 → ∀ k, k < 3 → frc Z (alpha Z) i k = dot (frc Z (alpha Z) i) (Z i) * Z i k) :
    sumP (fun i j => alpha Z i j * (Lf Z e i j + dot (e i) (e j)))
      = sumP (fun i j => alpha Z i j * psif Z e i j) := by
  have hsym : ∀ i j, i < j → j < 11 → alpha Z i j = alpha Z j i := fun i j _ _ => alpha_symm Z i j
  have h1 : sumP (fun i j => alpha Z i j * (Lf Z e i j + dot (e i) (e j)))
      = sumP (fun i j => alpha Z i j * Lf Z e i j) + sumP (fun i j => alpha Z i j * dot (e i) (e j)) := by
    rw [← sumP_add]
    exact sumP_congr fun i j _ _ => by ring
  have h2 : sumP (fun i j => alpha Z i j * Lf Z e i j)
      = ∑ i ∈ range 11, dot (e i) (e i) * (-(1 / 2) * rowS (fun i j => alpha Z i j * dot (Z i) (Z j)) i) := by
    rw [sumP_lin (alpha Z) Z e hsym]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    have hc : dot (frc Z (alpha Z) i) (e i) = dot (frc Z (alpha Z) i) (Z i) * dot (Z i) (e i) := by
      have e1 : dot (frc Z (alpha Z) i) (e i)
          = dot (fun k => dot (frc Z (alpha Z) i) (Z i) * Z i k) (e i) :=
        dot_congr (fun k hk => hcrit i hi' k hk) (fun k _ => rfl)
      rw [e1]
      simp only [dot_eq]
      ring
    have hl : dot (frc Z (alpha Z) i) (Z i) = rowS (fun i j => alpha Z i j * dot (Z i) (Z j)) i := by
      rw [dot_frc]
      unfold rowS
      refine sum_congr rfl fun j _ => ?_
      by_cases h : j = i
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, dot_comm]
    rw [hc, hl]
    have := he i hi'
    have e2 : dot (Z i) (e i) = -(dot (e i) (e i)) / 2 := by linarith
    rw [e2]
    ring
  have h3 : ∑ i ∈ range 11, dot (e i) (e i) * (-(1 / 2) * rowS (fun i j => alpha Z i j * dot (Z i) (Z j)) i)
      = -(1 / 2) * sumP (fun i j => alpha Z i j * dot (Z i) (Z j) * (dot (e i) (e i) + dot (e j) (e j))) := by
    rw [sumP_rows _ _ fun i j _ _ => by rw [alpha_symm, dot_comm], Finset.mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [h1, h2, h3, ← sumP_mul, ← sumP_add]
  refine sumP_congr fun i j _ _ => ?_
  unfold psif
  ring

/-! ## The penalty of the difference of two configurations in the gauge -/

section Pen

variable {p a b c : ℕ → ℕ → ℝ} {K : Consts}

theorem penf_small (G : G7 p a b c K) (hK : CK K) {Z Z' : ℕ → ℕ → ℝ}
    (hZ : ∀ i, i < 11 → dot (Z i) (Z i) = 1) (hZ' : ∀ i, i < 11 → dot (Z' i) (Z' i) = 1)
    (hcZ : ∀ i, i < 11 → dot (fun k => Z i k - p i k) (fun k => Z i k - p i k) ≤ 1 / 10 ^ 22)
    (hgZ : ∀ k l, k < 3 → l < 3 → ∑ i ∈ range 11, scl p Z i k * p i l = ∑ i ∈ range 11, scl p Z i l * p i k)
    (hgZ' : ∀ k l, k < 3 → l < 3 → ∑ i ∈ range 11, scl p Z' i k * p i l = ∑ i ∈ range 11, scl p Z' i l * p i k)
    (hE : ∀ i, i < 11 → dot (dsub Z' Z i) (dsub Z' Z i) ≤ 4 / 10 ^ 22) :
    penf p (dsub Z' Z) ≤ (4 / 10 ^ 22 + 200 * K.nu ^ 2) * nsq (dsub Z' Z) := by
  set e := dsub Z' Z with he
  have hnu0 := hK.nu0
  unfold penf
  rw [gauge_term]
  -- the diagonal terms
  have hd : ∀ i, i < 11 → dot (p i) (e i) ^ 2 ≤ 4 / 10 ^ 22 * dot (e i) (e i) := by
    intro i hi
    have h1 : 2 * dot (Z i) (e i) + dot (e i) (e i) = 0 := by
      have a1 := hZ i hi
      have a2 := hZ' i hi
      rw [he]
      unfold dsub
      simp only [dot_eq] at a1 a2 ⊢
      linarith
    have h2 : dot (p i) (e i) = -(dot (e i) (e i)) / 2 - dot (fun k => Z i k - p i k) (e i) := by
      have : dot (p i) (e i) = dot (Z i) (e i) - dot (fun k => Z i k - p i k) (e i) := by
        simp only [dot_eq]
        ring
      rw [this]
      linarith
    have h3 := dot_sq_le (fun k => Z i k - p i k) (e i)
    have h4 := hcZ i hi
    have h5 := hE i hi
    have h6 := dot_self_nonneg (e i)
    have h7 : dot (fun k => Z i k - p i k) (e i) ^ 2 ≤ 1 / 10 ^ 22 * dot (e i) (e i) := by
      have := mul_le_mul_of_nonneg_right h4 h6
      linarith
    have h8 : dot (e i) (e i) * dot (e i) (e i) ≤ 4 / 10 ^ 22 * dot (e i) (e i) :=
      mul_le_mul_of_nonneg_right h5 h6
    rw [h2]
    nlinarith [sq_nonneg (dot (e i) (e i) / 2 - dot (fun k => Z i k - p i k) (e i))]
  have hdiag : ∑ i ∈ range 11, dot (p i) (e i) ^ 2 ≤ 4 / 10 ^ 22 * nsq e := by
    unfold nsq
    rw [Finset.mul_sum]
    exact sum_le_sum fun i hi => hd i (mem_range.mp hi)
  -- the gauge term
  have hT : ∀ k l, k < 3 → l < 3 →
      ∑ i ∈ range 11, e i k * p i l - ∑ i ∈ range 11, e i l * p i k
        = ∑ i ∈ range 11, (1 - nrm p i) * (e i k * p i l - e i l * p i k) := by
    intro k l hk hl
    have h1 := hgZ k l hk hl
    have h2 := hgZ' k l hk hl
    unfold scl at h1 h2
    rw [he]
    unfold dsub
    have e1 : ∑ i ∈ range 11, (1 - nrm p i) * ((Z' i k - Z i k) * p i l - (Z' i l - Z i l) * p i k)
        = (∑ i ∈ range 11, (Z' i k - Z i k) * p i l - ∑ i ∈ range 11, (Z' i l - Z i l) * p i k)
          - ((∑ i ∈ range 11, nrm p i * Z' i k * p i l - ∑ i ∈ range 11, nrm p i * Z' i l * p i k)
            - (∑ i ∈ range 11, nrm p i * Z i k * p i l - ∑ i ∈ range 11, nrm p i * Z i l * p i k)) := by
      simp only [← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [e1, h1, h2]
    ring
  have hcs : ∀ k l, k < 3 → l < 3 →
      (∑ i ∈ range 11, e i k * p i l - ∑ i ∈ range 11, e i l * p i k) ^ 2
        ≤ 11 * K.nu ^ 2 * ∑ i ∈ range 11, 2 * (e i k ^ 2 * p i l ^ 2 + e i l ^ 2 * p i k ^ 2) := by
    intro k l hk hl
    rw [hT k l hk hl]
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq (range 11) (fun i => 1 - nrm p i) (fun i => e i k * p i l - e i l * p i k)
    have h2 : ∑ i ∈ range 11, (1 - nrm p i) ^ 2 ≤ 11 * K.nu ^ 2 := by
      have : ∑ i ∈ range 11, (1 - nrm p i) ^ 2 ≤ ∑ i ∈ range 11, K.nu ^ 2 := by
        refine sum_le_sum fun i hi => ?_
        have h3 := nrm_sub_one G hK (mem_range.mp hi)
        rw [← sq_abs, abs_sub_comm]
        exact pow_le_pow_left₀ (abs_nonneg _) h3 2
      simpa using this
    have h3 : ∑ i ∈ range 11, (e i k * p i l - e i l * p i k) ^ 2
        ≤ ∑ i ∈ range 11, 2 * (e i k ^ 2 * p i l ^ 2 + e i l ^ 2 * p i k ^ 2) :=
      sum_le_sum fun i _ => by nlinarith [sq_nonneg (e i k * p i l + e i l * p i k)]
    have h4 : 0 ≤ ∑ i ∈ range 11, (e i k * p i l - e i l * p i k) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    calc (∑ i ∈ range 11, (1 - nrm p i) * (e i k * p i l - e i l * p i k)) ^ 2
        ≤ (∑ i ∈ range 11, (1 - nrm p i) ^ 2) * ∑ i ∈ range 11, (e i k * p i l - e i l * p i k) ^ 2 := h1
      _ ≤ 11 * K.nu ^ 2 * ∑ i ∈ range 11, 2 * (e i k ^ 2 * p i l ^ 2 + e i l ^ 2 * p i k ^ 2) :=
          mul_le_mul h2 h3 h4 (by positivity)
  have hsum : ∑ k ∈ range 3, ∑ l ∈ range 3, ∑ i ∈ range 11, 2 * (e i k ^ 2 * p i l ^ 2 + e i l ^ 2 * p i k ^ 2)
      = 4 * ∑ i ∈ range 11, dot (e i) (e i) * dot (p i) (p i) := by
    simp only [dot_eq, sum_range_succ, sum_range_zero]
    ring
  have hnp : ∑ i ∈ range 11, dot (e i) (e i) * dot (p i) (p i) ≤ 101 / 100 * nsq e := by
    unfold nsq
    rw [Finset.mul_sum]
    refine sum_le_sum fun i hi => ?_
    have h1 := norm_hi G hK (mem_range.mp hi)
    have h2 := dot_self_nonneg (e i)
    nlinarith
  have hgauge : 1 / 2 * ∑ k ∈ range 3, ∑ l ∈ range 3,
      (∑ i ∈ range 11, e i k * p i l - ∑ i ∈ range 11, e i l * p i k) ^ 2 ≤ 200 * K.nu ^ 2 * nsq e := by
    have h1 : ∑ k ∈ range 3, ∑ l ∈ range 3,
        (∑ i ∈ range 11, e i k * p i l - ∑ i ∈ range 11, e i l * p i k) ^ 2
          ≤ ∑ k ∈ range 3, ∑ l ∈ range 3,
            11 * K.nu ^ 2 * ∑ i ∈ range 11, 2 * (e i k ^ 2 * p i l ^ 2 + e i l ^ 2 * p i k ^ 2) :=
      sum_le_sum fun k hk => sum_le_sum fun l hl => hcs k l (mem_range.mp hk) (mem_range.mp hl)
    rw [sum2_mul, hsum] at h1
    have h2 : 0 ≤ K.nu ^ 2 := sq_nonneg _
    have h3 : 0 ≤ nsq e := nsq_nonneg e
    nlinarith
  linarith

/-! ## Uniqueness -/

theorem sq_add3_le (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

/-- The hypotheses on a configuration of the sphere near `p` in the gauge. -/
structure NearP (p Z : ℕ → ℕ → ℝ) : Prop where
  sph : ∀ i, i < 11 → dot (Z i) (Z i) = 1
  close : ∀ i, i < 11 → dot (fun k => Z i k - p i k) (fun k => Z i k - p i k) ≤ 1 / 10 ^ 22
  gauge : ∀ k l, k < 3 → l < 3 → ∑ i ∈ range 11, scl p Z i k * p i l = ∑ i ∈ range 11, scl p Z i l * p i k

theorem NearP.dot_err {Z : ℕ → ℕ → ℝ} (hN : NearP p Z) {i : ℕ} (hi : i < 11) (u : ℕ → ℝ) :
    dot (fun k => Z i k - p i k) u ^ 2 ≤ 1 / 10 ^ 22 * dot u u := by
  have h1 := dot_sq_le (fun k => Z i k - p i k) u
  have h2 := hN.close i hi
  have h3 := dot_self_nonneg u
  have := mul_le_mul_of_nonneg_right h2 h3
  linarith

theorem NearP.t_close (G : G7 p a b c K) (hK : CK K) {Z : ℕ → ℕ → ℝ} (hN : NearP p Z) {i j : ℕ} (hi : i < 11)
    (hj : j < 11) : |dot (Z i) (Z j) - dot (p i) (p j)| ≤ 201 / 100 / 10 ^ 11 := by
  have e : dot (Z i) (Z j) - dot (p i) (p j) = dot (fun k => Z i k - p i k) (Z j) + dot (p i) (fun k => Z j k - p j k) := by
    simp only [dot_eq]
    ring
  have h1 := hN.dot_err hi (Z j)
  rw [hN.sph j hj, mul_one] at h1
  have h2 := hN.dot_err hj (p i)
  rw [dot_comm] at h2
  have h3 := norm_hi G hK hi
  have a1 : |dot (fun k => Z i k - p i k) (Z j)| ≤ 1 / 10 ^ 11 :=
    abs_le_of_sq_le_sq (by norm_num at h1 ⊢; linarith) (by norm_num)
  have a2 : |dot (p i) (fun k => Z j k - p j k)| ≤ 101 / 100 / 10 ^ 11 :=
    abs_le_of_sq_le_sq (by norm_num at h2 ⊢; nlinarith) (by norm_num)
  rw [e]
  have := abs_add_le (dot (fun k => Z i k - p i k) (Z j)) (dot (p i) (fun k => Z j k - p j k))
  linarith

theorem NearP.t_top (G : G7 p a b c K) (hK : CK K) {Z : ℕ → ℕ → ℝ} (hN : NearP p Z) {i j : ℕ} (hij : i < j)
    (hj : j < 11) : dot (Z i) (Z j) ≤ 3 / 5 := by
  have h1 := hN.t_close G hK (show i < 11 by omega) hj
  have h2 := le_trans (G.top i j hij hj) hK.tmax
  have := (abs_le.mp h1).2
  linarith

/-- **The estimate of a pair for the uniqueness.** -/
theorem pair_step (G : G7 p a b c K) (hK : CK K) {Z Z' : ℕ → ℕ → ℝ} (hN : NearP p Z) (hN' : NearP p Z')
    (hE : ∀ i, i < 11 → dot (dsub Z' Z i) (dsub Z' Z i) ≤ 4 / 10 ^ 22) {i j : ℕ} (hij : i < j) (hj : j < 11) :
    a i j * psif p (dsub Z' Z) i j + b i j * Lf p (dsub Z' Z) i j ^ 2
        - (3 / 10 ^ 9 + 6 * K.eps) * (dot (dsub Z' Z i) (dsub Z' Z i) + dot (dsub Z' Z j) (dsub Z' Z j))
      ≤ alpha Z i j * psif Z (dsub Z' Z) i j
        + (3 / 2 * fpot (dot (Z i) (Z j)) ^ 5 * (Lf Z (dsub Z' Z) i j + dot (dsub Z' Z i) (dsub Z' Z j)) ^ 2
          + 5 / 2 * fpot (dot (Z i) (Z j)) ^ 7 * (Lf Z (dsub Z' Z) i j + dot (dsub Z' Z i) (dsub Z' Z j)) ^ 3) := by
  have hi : i < 11 := by omega
  set e := dsub Z' Z with he
  set t := dot (Z i) (Z j) with ht
  set t0 := dot (p i) (p j) with ht0
  have hζ : (0 : ℝ) < 1 / 10 ^ 11 := by norm_num
  have hζ1 : (1 : ℝ) / 10 ^ 11 ≤ 1 / 100 := by norm_num
  have hζ2 : ((1 : ℝ) / 10 ^ 11) ^ 2 = 1 / 10 ^ 22 := by norm_num
  have htt := hN.t_close G hK hi hj
  rw [← ht, ← ht0] at htt
  have ht1 : t ≤ 3 / 5 := hN.t_top G hK hij hj
  have ht01 : t0 ≤ 17 / 32 := le_trans (G.top i j hij hj) hK.tmax
  have he0 := hK.eps0
  have he1 := hK.eps1
  -- the coefficients
  obtain ⟨ha, hb, hc⟩ := G.enc i j hij hj (fpot t0) (fpot_pos (by linarith)) (fpot_sq (by linarith))
  obtain ⟨ha0, hb0, hc0, _⟩ := coef_facts G hK hij hj
  have hl3 := fpot_pow_lip 2 ht1 (by linarith : t0 ≤ 3 / 5)
  have hl5 := fpot_pow_lip 4 ht1 (by linarith : t0 ≤ 3 / 5)
  norm_num at hl3 hl5
  have hw1 := fpot_le ht1
  have hw0 := fpot_nonneg t
  have hw01 := fpot_le (by linarith : t0 ≤ 3 / 5)
  have hA : |alpha Z i j - a i j| ≤ 12 / 10 ^ 11 + K.eps := by
    have e1 : alpha Z i j - a i j = (fpot t ^ 3 - fpot t0 ^ 3) + (fpot t0 ^ 3 - a i j) := by
      unfold alpha
      ring
    rw [e1]
    have h1 := abs_add_le (fpot t ^ 3 - fpot t0 ^ 3) (fpot t0 ^ 3 - a i j)
    rw [abs_sub_comm (fpot t0 ^ 3)] at h1
    have h2 : 729 / 128 * |t - t0| ≤ 729 / 128 * (201 / 100 / 10 ^ 11) :=
      mul_le_mul_of_nonneg_left htt (by norm_num)
    norm_num at h2
    linarith
  have hB : |3 / 2 * fpot t ^ 5 - b i j| ≤ 37 / 10 ^ 11 + 2 * K.eps := by
    have e1 : 3 / 2 * fpot t ^ 5 - b i j = 3 / 2 * (fpot t ^ 5 - fpot t0 ^ 5) + (3 / 2 * fpot t0 ^ 5 - b i j) := by
      ring
    rw [e1]
    have h1 := abs_add_le (3 / 2 * (fpot t ^ 5 - fpot t0 ^ 5)) (3 / 2 * fpot t0 ^ 5 - b i j)
    rw [abs_sub_comm (3 / 2 * fpot t0 ^ 5), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at h1
    have h2 : 98415 / 8192 * |t - t0| ≤ 98415 / 8192 * (201 / 100 / 10 ^ 11) :=
      mul_le_mul_of_nonneg_left htt (by norm_num)
    norm_num at h2
    linarith
  have hβ0 : 0 ≤ 3 / 2 * fpot t ^ 5 := by positivity
  have hβ1 : 3 / 2 * fpot t ^ 5 ≤ 3 := by
    have := pow_le_pow_left₀ hw0 hw1 5
    norm_num at this ⊢
    linarith
  have hς0 : 0 ≤ 5 / 2 * fpot t ^ 7 := by positivity
  have hς1 : 5 / 2 * fpot t ^ 7 ≤ 6 := by
    have := pow_le_pow_left₀ hw0 hw1 7
    norm_num at this ⊢
    linarith
  have ha1 : a i j ≤ 3 / 2 := by
    have := pow_le_pow_left₀ (fpot_nonneg t0) hw01 3
    have h2 := (abs_le.mp ha).2
    norm_num at this
    linarith
  -- the displacement
  have hEi := hE i hi
  have hEj := hE j hj
  have hEi0 := dot_self_nonneg (e i)
  have hEj0 := dot_self_nonneg (e j)
  have hS : dot (e i) (e i) + dot (e j) (e j) ≤ 8 * (1 / 10 ^ 11) ^ 2 := by rw [hζ2]; linarith
  have hψZ : |psif Z e i j| ≤ dot (e i) (e i) + dot (e j) (e j) := by
    unfold psif
    rw [← ht]
    have h1 := two_mul_abs_dot_le (e i) (e j)
    have h2 : |t| ≤ 1 := by
      have := dot_sq_le (Z i) (Z j)
      rw [hN.sph i hi, hN.sph j hj, one_mul] at this
      exact abs_le_of_sq_le_sq (by rw [← ht] at this; linarith) (by norm_num)
    have h3 : |t / 2 * (dot (e i) (e i) + dot (e j) (e j))| ≤ 1 / 2 * (dot (e i) (e i) + dot (e j) (e j)) := by
      rw [abs_mul, abs_div, abs_two, abs_of_nonneg (by linarith : 0 ≤ dot (e i) (e i) + dot (e j) (e j))]
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h4 := abs_sub (dot (e i) (e j)) (t / 2 * (dot (e i) (e i) + dot (e j) (e j)))
    linarith
  have hψ : |psif Z e i j - psif p e i j| ≤ 101 / 100 / 10 ^ 11 * (dot (e i) (e i) + dot (e j) (e j)) := by
    have e1 : psif Z e i j - psif p e i j = -((t - t0) / 2) * (dot (e i) (e i) + dot (e j) (e j)) := by
      unfold psif
      rw [← ht, ← ht0]
      ring
    rw [e1, abs_mul, abs_neg, abs_div, abs_two, abs_of_nonneg (by linarith : 0 ≤ dot (e i) (e i) + dot (e j) (e j))]
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hL : Lf p e i j ^ 2 ≤ 203 / 100 * (dot (e i) (e i) + dot (e j) (e j)) := by
    unfold Lf
    have h1 := dot_sq_le (p i) (e j)
    have h2 := dot_sq_le (e i) (p j)
    have h3 := norm_hi G hK hi
    have h4 := norm_hi G hK hj
    have h5 : dot (p i) (p i) * dot (e j) (e j) ≤ 101 / 100 * dot (e j) (e j) := mul_le_mul_of_nonneg_right h3 hEj0
    have h6 : dot (e i) (e i) * dot (p j) (p j) ≤ 101 / 100 * dot (e i) (e i) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right h4 hEi0
    linarith [sq_nonneg (dot (p i) (e j) - dot (e i) (p j))]
  -- `Lf Z e = Lf p e + μ₁`
  set μ := dot (fun k => Z i k - p i k) (e j) + dot (e i) (fun k => Z j k - p j k) + dot (e i) (e j) with hμ_def
  have hLZ : Lf Z e i j + dot (e i) (e j) = Lf p e i j + μ := by
    rw [hμ_def]
    unfold Lf
    simp only [dot_eq]
    ring
  have hμ : μ ^ 2 ≤ 15 * (1 / 10 ^ 11) ^ 2 * (dot (e i) (e i) + dot (e j) (e j)) := by
    rw [hζ2]
    have h1 := hN.dot_err hi (e j)
    have h2 := hN.dot_err hj (e i)
    rw [dot_comm] at h2
    have h3 := dot_sq_le (e i) (e j)
    have h4 : dot (e i) (e i) * dot (e j) (e j) ≤ dot (e i) (e i) * (4 / 10 ^ 22) := mul_le_mul_of_nonneg_left hEj hEi0
    have h5 : μ ^ 2 ≤ 3 * (dot (fun k => Z i k - p i k) (e j) ^ 2 + dot (e i) (fun k => Z j k - p j k) ^ 2
        + dot (e i) (e j) ^ 2) := by
      rw [hμ_def]
      exact sq_add3_le _ _ _
    linarith
  have hmain := pair_unique hζ hζ1 hA hB hβ0 hβ1 hς0 hς1 ha0 ha1 hEi0 hEj0 hS hψZ hψ hL hμ
  rw [hLZ]
  have hK1 : 12 / 10 ^ 11 + K.eps + 3 / 2 * (101 / 100 / 10 ^ 11) + 54 * (1 / 10 ^ 11)
      + 203 / 100 * (37 / 10 ^ 11 + 2 * K.eps) + 150 * (1 / 10 ^ 11) ≤ 3 / 10 ^ 9 + 6 * K.eps := by
    norm_num
    linarith
  have hS0 : 0 ≤ dot (e i) (e i) + dot (e j) (e j) := by linarith
  have := mul_le_mul_of_nonneg_right hK1 hS0
  have e2 : 3 / 2 * fpot t ^ 5 * (Lf p e i j + μ) ^ 2 + 5 / 2 * fpot t ^ 7 * (Lf p e i j + μ) ^ 3
      = 3 / 2 * fpot t ^ 5 * (Lf p e i j + μ) ^ 2 + 5 / 2 * fpot t ^ 7 * (Lf p e i j + μ) ^ 3 := rfl
  linarith

/-- **Uniqueness.** Two configurations of the sphere near `p` in the gauge, the first one critical and with energy
at least that of the second, coincide. -/
theorem unique (G : G7 p a b c K) (hK : CK K) {Z Z' : ℕ → ℕ → ℝ} (hN : NearP p Z) (hN' : NearP p Z')
    (hcrit : ∀ i, i < 11 → ∀ k, k < 3 → frc Z (alpha Z) i k = dot (frc Z (alpha Z) i) (Z i) * Z i k)
    (hEn : En Z' ≤ En Z) : ∀ i, i < 11 → ∀ k, k < 3 → Z' i k = Z i k := by
  set e := dsub Z' Z with he
  -- `|e_i|² ≤ 4 ζ²`
  have hE : ∀ i, i < 11 → dot (e i) (e i) ≤ 4 / 10 ^ 22 := by
    intro i hi
    have h := dot_add_self_le (fun k => Z' i k - p i k) (fun k => p i k - Z i k)
    have e1 : (fun k => Z' i k - p i k + (p i k - Z i k)) = e i := by
      funext k
      rw [he]
      unfold dsub
      ring
    have e2 : dot (fun k => p i k - Z i k) (fun k => p i k - Z i k)
        = dot (fun k => Z i k - p i k) (fun k => Z i k - p i k) := by
      simp only [dot_eq]
      ring
    rw [e1, e2] at h
    linarith [hN.close i hi, hN'.close i hi]
  have hdiag : ∀ i, i < 11 → 2 * dot (Z i) (e i) + dot (e i) (e i) = 0 := by
    intro i hi
    have a1 := hN.sph i hi
    have a2 := hN'.sph i hi
    rw [he]
    unfold dsub
    simp only [dot_eq] at a1 a2 ⊢
    linarith
  -- the energy difference, by the Taylor polynomial at `Z`
  have hpair : ∀ i j, i < j → j < 11 →
      alpha Z i j * (Lf Z e i j + dot (e i) (e j))
          + (3 / 2 * fpot (dot (Z i) (Z j)) ^ 5 * (Lf Z e i j + dot (e i) (e j)) ^ 2
            + 5 / 2 * fpot (dot (Z i) (Z j)) ^ 7 * (Lf Z e i j + dot (e i) (e j)) ^ 3)
        ≤ fpot (dot (Z' i) (Z' j)) - fpot (dot (Z i) (Z j)) := by
    intro i j hij hj
    have ht := hN.t_top G hK hij hj
    have ht' := hN'.t_top G hK hij hj
    have hT := taylor3 (t0 := dot (Z i) (Z j)) (t := dot (Z' i) (Z' j)) (by linarith) (by linarith)
    have hd : dot (Z' i) (Z' j) - dot (Z i) (Z j) = Lf Z e i j + dot (e i) (e j) := by
      rw [he]
      unfold Lf dsub
      simp only [dot_eq]
      ring
    rw [hd] at hT
    unfold alpha
    linarith
  have hsum := sumP_le hpair
  rw [sumP_add, first_order hdiag hcrit, sumP_sub] at hsum
  have hEdiff : sumP (fun i j => fpot (dot (Z' i) (Z' j))) - sumP (fun i j => fpot (dot (Z i) (Z j)))
      = En Z' - En Z := rfl
  rw [hEdiff] at hsum
  -- the lower bound by the forms at `p`
  have hstep := sumP_le (fun i j hij hj => pair_step G hK hN hN' hE hij hj)
  rw [← he] at hstep
  have hLs : sumP (fun i j => a i j * psif p e i j + b i j * Lf p e i j ^ 2
        - (3 / 10 ^ 9 + 6 * K.eps) * (dot (e i) (e i) + dot (e j) (e j)))
      = Qf p a b e - (3 / 10 ^ 9 + 6 * K.eps) * (10 * nsq e) := by
    rw [sumP_sub, sumP_mul, sumP_sum_pts]
    rfl
  have hRs := sumP_add (fun i j => alpha Z i j * psif Z e i j)
    (fun i j => 3 / 2 * fpot (dot (Z i) (Z j)) ^ 5 * (Lf Z e i j + dot (e i) (e j)) ^ 2
      + 5 / 2 * fpot (dot (Z i) (Z j)) ^ 7 * (Lf Z e i j + dot (e i) (e j)) ^ 3)
  rw [hLs, hRs] at hstep
  -- the quadratic form and the penalty
  have hhess := G.hess e
  have hpen := penf_small G hK hN.sph hN'.sph hN.close hN.gauge hN'.gauge hE
  rw [← he] at hpen
  have hQ0 := nsq_nonneg e
  have hk := hK.kappa
  have hpQ := hK.penQ1
  have hpQ0 := hK.penQ0
  have he1 := hK.eps1
  have he0 := hK.eps0
  have hnu := hK.nu1
  have hnu0 := hK.nu0
  have h1 : K.penQ * penf p e ≤ 16384 * ((4 / 10 ^ 22 + 200 * (1 / 10 ^ 17) ^ 2) * nsq e) := by
    have a1 : K.nu ^ 2 ≤ (1 / 10 ^ 17) ^ 2 := pow_le_pow_left₀ hnu0 hnu 2
    have a2 : (4 / 10 ^ 22 + 200 * K.nu ^ 2) * nsq e ≤ (4 / 10 ^ 22 + 200 * (1 / 10 ^ 17) ^ 2) * nsq e :=
      mul_le_mul_of_nonneg_right (by linarith) hQ0
    have a3 : 0 ≤ penf p e := by
      have := G.hess e
      unfold penf
      rw [gauge_term]
      have b1 : 0 ≤ ∑ i ∈ range 11, dot (p i) (e i) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
      have b2 : 0 ≤ ∑ k ∈ range 3, ∑ l ∈ range 3,
          (∑ i ∈ range 11, e i k * p i l - ∑ i ∈ range 11, e i l * p i k) ^ 2 :=
        sum_nonneg fun k _ => sum_nonneg fun l _ => sq_nonneg _
      linarith
    calc K.penQ * penf p e ≤ 16384 * penf p e := mul_le_mul_of_nonneg_right hpQ a3
      _ ≤ 16384 * ((4 / 10 ^ 22 + 200 * (1 / 10 ^ 17) ^ 2) * nsq e) :=
          mul_le_mul_of_nonneg_left (le_trans hpen a2) (by norm_num)
  have h2 : (3 / 10 ^ 9 + 6 * K.eps) * (10 * nsq e) ≤ (3 / 10 ^ 9 + 6 * (1 / 10 ^ 18)) * (10 * nsq e) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h3 : K.kappa * nsq e ≥ 371 / 8192 * nsq e := mul_le_mul_of_nonneg_right hk hQ0
  have h4 : nsq e ≤ 0 := by nlinarith
  have h5 : nsq e = 0 := le_antisymm h4 hQ0
  intro i hi k hk3
  have h6 := D_le_nsq e hi
  rw [h5] at h6
  have h7 := sq_le_dot_self (e i) hk3
  have h8 : e i k = 0 := by nlinarith [sq_nonneg (e i k)]
  rw [he] at h8
  unfold dsub at h8
  linarith

end Pen

end N11.Analytic
