module

public import N11.Analytic.Rigid
public import N11.Analytic.Potential
public import N11.Analytic.Critical

/-!
# The theorem for 11 points, analytic part: the lower bound near the reference configuration (row A9)

Let `y` be aligned with the reference configuration `p` (`Aligned p y`) with `X = |y - p|² ≤ 63/2000000`. Let
`d = y - p`, `r_i = <p_i, d_i> / |p_i|²`, and `v_i = d_i - r_i p_i` the tangential part (`tang`). Then `<p_i, v_i> = 0`,
the gauge holds for `v`, so `penf p v = 0`, and with `q_i = |v_i|²`, `D_i = |d_i|²`:
`2 <p_i, d_i> + D_i = 0`, `r_i = -D_i / (2 |p_i|²)`, `D_i = q_i + r_i² |p_i|²`.

For a pair `i < j` the change of the inner product is `Δ_ij = <y_i, y_j> - <p_i, p_j> = L_ij(v) + η_ij` with
`η_ij = (r_i + r_j) <p_i, p_j> + <d_i, d_j>`. With `ψ = psif p v`, `ρ = rhof p v`:
`aΔ + bΔ² + cΔ³ - [aL + (aψ + bL²) + (cL³ + 2bLψ + aρ)] = a(η - ψ - ρ) + 2bLρ + 2bL(η - ψ - ρ) + 3cL²η + η²(b + 3cL + cη)`
(`pair_alg`), and `η - ψ - ρ = (e_i + e_j) t + r_i r_j t + e_i <p_i, v_j> + e_j <v_i, p_j>` with
`e_i = r_i + q_i / 2 = q_i (|p_i|² - 1) / (2 |p_i|²) - r_i² / 2`. The last term is nonnegative, and the others are
bounded per pair by `q_i`, `q_j` (`pair_err`); summed with the bounds `rows` of G7 they give at most
`3 ν Q + 150 Q²`, `Q = |v|²` (`err_sum`).

`expand_lower`: `∑_{i<j} aΔ + bΔ² + cΔ³ ≥ -γ V + κ V² - c₃ V³ - 150 V⁴ - 10⁻¹⁶ V²` with `V = |v|`, by the fields
`grad`, `hess` (for `v`, where the penalty vanishes) and `cub` of G7.
-/

@[expose] public section

namespace N11.Analytic

open Finset N11.Local

/-! ## The constants -/

/-- The numerical bounds on the constants of G7 that the analytic part uses. -/
structure CK (K : Consts) : Prop where
  eps0 : 0 ≤ K.eps
  eps1 : K.eps ≤ 1 / 10 ^ 18
  gam0 : 0 ≤ K.gam
  gam1 : K.gam ≤ 1 / 10 ^ 17
  ra : K.ra ≤ 2615 / 512
  rb : K.rb ≤ 1643 / 256
  rc : K.rc ≤ 5089 / 512
  nu0 : 0 ≤ K.nu
  nu1 : K.nu ≤ 1 / 10 ^ 17
  tmax : K.tmax ≤ 17 / 32
  kappa : 371 / 8192 ≤ K.kappa
  penQ0 : 0 ≤ K.penQ
  penQ1 : K.penQ ≤ 16384
  sigma2 : 3643 / 1024 ≤ K.sigma2
  penR0 : 2 ≤ K.penR
  penR1 : K.penR ≤ 64
  c30 : 0 ≤ K.c3
  c31 : K.c3 ≤ 113 / 32

section Ref

variable {p a b c : ℕ → ℕ → ℝ} {K : Consts}

theorem norm_lo (G : G7 p a b c K) (hK : CK K) {i : ℕ} (hi : i < 11) : 99 / 100 ≤ dot (p i) (p i) := by
  have h := abs_le.mp (G.norm i hi)
  have := hK.nu1
  linarith [h.1]

theorem norm_hi (G : G7 p a b c K) (hK : CK K) {i : ℕ} (hi : i < 11) : dot (p i) (p i) ≤ 101 / 100 := by
  have h := abs_le.mp (G.norm i hi)
  have := hK.nu1
  linarith [h.2]

theorem norm_nu (G : G7 p a b c K) {i : ℕ} (hi : i < 11) : |dot (p i) (p i) - 1| ≤ K.nu := G.norm i hi

theorem t_abs (G : G7 p a b c K) (hK : CK K) {i j : ℕ} (hi : i < 11) (hj : j < 11) :
    |dot (p i) (p j)| ≤ 101 / 100 := by
  have h1 := dot_sq_le (p i) (p j)
  have h2 := norm_hi G hK hi
  have h3 := norm_hi G hK hj
  have h4 : 0 ≤ dot (p i) (p i) := dot_self_nonneg _
  have h5 : dot (p i) (p j) ^ 2 ≤ (101 / 100) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq h5 (by norm_num)

/-- The coefficients of a pair are positive, and `b ≥ (7/100) c`. -/
theorem coef_facts (G : G7 p a b c K) (hK : CK K) {i j : ℕ} (hij : i < j) (hj : j < 11) :
    0 ≤ a i j ∧ 0 ≤ b i j ∧ 0 ≤ c i j ∧ 7 / 100 * c i j ≤ b i j := by
  have ht1 : dot (p i) (p j) ≤ 17 / 32 := le_trans (G.top i j hij hj) hK.tmax
  have ht0 : -11 / 10 ≤ dot (p i) (p j) := by
    have := (abs_le.mp (t_abs G hK (show i < 11 by omega) hj)).1
    linarith
  have hlt : dot (p i) (p j) < 1 := by linarith
  obtain ⟨w, hw⟩ : ∃ w, w = fpot (dot (p i) (p j)) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; exact fpot_pos hlt
  have hwsq : w ^ 2 * (2 - 2 * dot (p i) (p j)) = 1 := by rw [hw]; exact fpot_sq hlt
  have hwlo : 2 / 5 ≤ w := by rw [hw]; exact fpot_ge ht0 hlt
  have hw2 : w ^ 2 ≤ 16 / 15 := by
    have h2 : 15 / 16 ≤ 2 - 2 * dot (p i) (p j) := by linarith
    nlinarith
  obtain ⟨ha, hb, hc⟩ := G.enc i j hij hj w hw0 hwsq
  have he0 := hK.eps0
  have he1 := hK.eps1
  have hw3 : (2 / 5) ^ 3 ≤ w ^ 3 := pow_le_pow_left₀ (by norm_num) hwlo 3
  have hw5 : (2 / 5) ^ 5 ≤ w ^ 5 := pow_le_pow_left₀ (by norm_num) hwlo 5
  have hw7 : w ^ 7 ≤ 16 / 15 * w ^ 5 := by
    have : w ^ 7 = w ^ 5 * w ^ 2 := by ring
    rw [this]
    nlinarith [pow_pos hw0 5]
  have ha' := (abs_le.mp ha).1
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have hw7' : 0 ≤ w ^ 7 := by positivity
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

end Ref

/-! ## The tangential part of a displacement -/

/-- The coefficient of `p_i` in `d_i`. -/
noncomputable def rco (p d : ℕ → ℕ → ℝ) (i : ℕ) : ℝ := dot (p i) (d i) / dot (p i) (p i)

/-- The tangential part of a displacement. -/
noncomputable def tang (p d : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ := fun i k => d i k - rco p d i * p i k

theorem dot_p_tang (p d : ℕ → ℕ → ℝ) {i : ℕ} (hp : dot (p i) (p i) ≠ 0) : dot (p i) (tang p d i) = 0 := by
  have e : dot (p i) (tang p d i) = dot (p i) (d i) - rco p d i * dot (p i) (p i) := by
    unfold tang
    simp only [dot_eq]
    ring
  rw [e]
  unfold rco
  field_simp
  ring

theorem d_eq_tang (p d : ℕ → ℕ → ℝ) (i : ℕ) : d i = fun k => tang p d i k + rco p d i * p i k := by
  funext k
  unfold tang
  ring

theorem dot_vr (vi vj pi pj : ℕ → ℝ) (ri rj : ℝ) :
    dot (fun k => vi k + ri * pi k) (fun k => vj k + rj * pj k)
      = dot vi vj + rj * dot vi pj + ri * dot pi vj + ri * rj * dot pi pj := by
  simp only [dot_eq]
  ring

theorem dot_d_d (p d : ℕ → ℕ → ℝ) {i : ℕ} (hp : dot (p i) (p i) ≠ 0) :
    dot (d i) (d i) = dot (tang p d i) (tang p d i) + rco p d i ^ 2 * dot (p i) (p i) := by
  have h := dot_vr (tang p d i) (tang p d i) (p i) (p i) (rco p d i) (rco p d i)
  rw [← d_eq_tang] at h
  rw [h, dot_comm (tang p d i) (p i), dot_p_tang p d hp]
  ring

theorem dot_d_d' (p d : ℕ → ℕ → ℝ) (i j : ℕ) :
    dot (d i) (d j) = dot (tang p d i) (tang p d j) + rco p d j * dot (tang p d i) (p j)
      + rco p d i * dot (p i) (tang p d j) + rco p d i * rco p d j * dot (p i) (p j) := by
  rw [d_eq_tang p d i, d_eq_tang p d j, dot_vr]

theorem Lf_d (p d : ℕ → ℕ → ℝ) (i j : ℕ) :
    Lf p d i j = Lf p (tang p d) i j + (rco p d i + rco p d j) * dot (p i) (p j) := by
  unfold Lf
  rw [d_eq_tang p d i, d_eq_tang p d j]
  simp only [dot_eq]
  ring

section Aligned

variable {p a b c y : ℕ → ℕ → ℝ} {K : Consts}

theorem rco_eq (G : G7 p a b c K) (hK : CK K) (A : Aligned p y) {i : ℕ} (hi : i < 11) :
    rco p (dsub y p) i = -(dot (dsub y p i) (dsub y p i)) / (2 * dot (p i) (p i)) := by
  have h := diag_rel A.sph hi
  have hn := norm_lo G hK hi
  have e : dot (p i) (dsub y p i) = -(dot (dsub y p i) (dsub y p i)) / 2 := by linarith
  unfold rco
  rw [e]
  field_simp

theorem tang_sym (G : G7 p a b c K) (hK : CK K) (A : Aligned p y) :
    ∀ k l, k < 3 → l < 3 → ∑ i ∈ range 11, tang p (dsub y p) i k * p i l
      = ∑ i ∈ range 11, tang p (dsub y p) i l * p i k := by
  intro k l hk hl
  have h := A.sym_d k l hk hl
  unfold tang
  simp only [sub_mul, sum_sub_distrib]
  have e : ∑ i ∈ range 11, rco p (dsub y p) i * p i k * p i l = ∑ i ∈ range 11, rco p (dsub y p) i * p i l * p i k :=
    sum_congr rfl fun i _ => by ring
  rw [h, e]

theorem penf_tang (G : G7 p a b c K) (hK : CK K) (A : Aligned p y) : penf p (tang p (dsub y p)) = 0 := by
  rw [penf_of_sym p _ (tang_sym G hK A)]
  refine sum_eq_zero fun i hi => ?_
  have hn := norm_lo G hK (mem_range.mp hi)
  rw [dot_p_tang p _ (by linarith)]
  ring

theorem tang_perp (G : G7 p a b c K) (hK : CK K) {d : ℕ → ℕ → ℝ} {i : ℕ} (hi : i < 11) :
    dot (p i) (tang p d i) = 0 := by
  have hn := norm_lo G hK hi
  exact dot_p_tang p d (by linarith)

end Aligned

/-! ## The algebra of a pair -/

theorem pair_alg (a b c L η ψ ρ : ℝ) :
    a * (L + η) + b * (L + η) ^ 2 + c * (L + η) ^ 3
        - (a * L + (a * ψ + b * L ^ 2) + (c * L ^ 3 + 2 * b * (L * ψ) + a * ρ))
      = a * (η - ψ - ρ) + 2 * b * L * ρ + 2 * b * L * (η - ψ - ρ) + 3 * c * L ^ 2 * η
        + η ^ 2 * (b + 3 * c * L + c * η) := by
  ring

/-- **The lower bound of the polynomial of a pair.** -/
theorem pair_lower {a b c L η ψ ρ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : 7 / 100 * c ≤ b)
    (hL : |L| ≤ 1 / 50) (hη : |η| ≤ 1 / 100) :
    a * L + (a * ψ + b * L ^ 2) + (c * L ^ 3 + 2 * b * (L * ψ) + a * ρ)
        - (a * |η - ψ - ρ| + 2 * b * (|L| * |ρ|) + 2 * b * (|L| * |η - ψ - ρ|) + 3 * c * (L ^ 2 * |η|))
      ≤ a * (L + η) + b * (L + η) ^ 2 + c * (L + η) ^ 3 := by
  have e := pair_alg a b c L η ψ ρ
  have h1 : -(a * |η - ψ - ρ|) ≤ a * (η - ψ - ρ) := by
    have := neg_abs_le (η - ψ - ρ)
    nlinarith
  have h2 : -(2 * b * (|L| * |ρ|)) ≤ 2 * b * L * ρ := by
    have h := neg_abs_le (L * ρ)
    rw [abs_mul] at h
    nlinarith
  have h3 : -(2 * b * (|L| * |η - ψ - ρ|)) ≤ 2 * b * L * (η - ψ - ρ) := by
    have h := neg_abs_le (L * (η - ψ - ρ))
    rw [abs_mul] at h
    nlinarith
  have h4 : -(3 * c * (L ^ 2 * |η|)) ≤ 3 * c * L ^ 2 * η := by
    have h := neg_abs_le η
    have : 0 ≤ 3 * c * L ^ 2 := by positivity
    nlinarith
  have h5 : 0 ≤ η ^ 2 * (b + 3 * c * L + c * η) := by
    have hL' := neg_abs_le L
    have hη' := neg_abs_le η
    have : 0 ≤ b + 3 * c * L + c * η := by nlinarith
    positivity
  linarith

/-- `|L| |ρ|` for `L = P1 + P2`, `ρ = -(q_j P2 + q_i P1) / 2`. -/
theorem abs_L_rho {P1 P2 qi qj : ℝ} (hqi : 0 ≤ qi) (hqj : 0 ≤ qj) :
    |P1 + P2| * |-(1 / 2) * (qj * P2 + qi * P1)| ≤ 3 / 4 * (qi + qj) * (P1 ^ 2 + P2 ^ 2) := by
  have h1 : |P1 + P2| ≤ |P1| + |P2| := abs_add_le _ _
  have h2 : |-(1 / 2) * (qj * P2 + qi * P1)| ≤ 1 / 2 * (qj * |P2| + qi * |P1|) := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    have := abs_add_le (qj * P2) (qi * P1)
    rw [abs_mul, abs_mul, abs_of_nonneg hqi, abs_of_nonneg hqj] at this
    linarith
  have h3 : (|P1| + |P2|) * (1 / 2 * (qj * |P2| + qi * |P1|)) ≤ 3 / 4 * (qi + qj) * (P1 ^ 2 + P2 ^ 2) := by
    have e1 : P1 ^ 2 = |P1| ^ 2 := (sq_abs P1).symm
    have e2 : P2 ^ 2 = |P2| ^ 2 := (sq_abs P2).symm
    rw [e1, e2]
    have a1 := abs_nonneg P1
    have a2 := abs_nonneg P2
    nlinarith [sq_nonneg (|P1| - |P2|), mul_nonneg hqi (sq_nonneg (|P1| - |P2|)),
      mul_nonneg hqj (sq_nonneg (|P1| - |P2|))]
  calc |P1 + P2| * |-(1 / 2) * (qj * P2 + qi * P1)|
      ≤ (|P1| + |P2|) * (1 / 2 * (qj * |P2| + qi * |P1|)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ ≤ 3 / 4 * (qi + qj) * (P1 ^ 2 + P2 ^ 2) := h3

/-- **The error of a pair**, bounded by the squared norms of the tangential parts. -/
theorem pair_err {a b c t P1 P2 qi qj Di Dj ri rj η nu : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hqi : 0 ≤ qi) (hqj : 0 ≤ qj) (hDi : 0 ≤ Di) (hDj : 0 ≤ Dj)
    (hnu : 0 ≤ nu)
    (hP : P1 ^ 2 + P2 ^ 2 ≤ 101 / 100 * (qi + qj)) (hP1 : |P1| ≤ 1 / 100) (hP2 : |P2| ≤ 1 / 100)
    (ht : |t| ≤ 101 / 100) (hri : |ri| ≤ 50 / 99 * Di) (hrj : |rj| ≤ 50 / 99 * Dj)
    (hei : |ri + qi / 2| ≤ 51 / 100 * (nu * qi) + 13 / 100 * Di ^ 2)
    (hej : |rj + qj / 2| ≤ 51 / 100 * (nu * qj) + 13 / 100 * Dj ^ 2)
    (hη : |η| ≤ 102 / 100 * (Di + Dj)) (hDqi : Di ≤ (1 + 1 / 10 ^ 5) * qi) (hDqj : Dj ≤ (1 + 1 / 10 ^ 5) * qj)
    (hL : |P1 + P2| ≤ 1 / 50) (ψ ρ : ℝ)
    (hηψρ : η - ψ - ρ = (ri + qi / 2 + (rj + qj / 2)) * t + ri * rj * t + (ri + qi / 2) * P1 + (rj + qj / 2) * P2)
    (hρ : ρ = -(1 / 2) * (qj * P2 + qi * P1)) :
    a * |η - ψ - ρ| + 2 * b * (|P1 + P2| * |ρ|) + 2 * b * (|P1 + P2| * |η - ψ - ρ|)
        + 3 * c * ((P1 + P2) ^ 2 * |η|)
      ≤ (a + b / 25) * (53 / 100 * nu * (qi + qj))
        + (27 / 100 * (a + b / 25) + 31 / 10 * b + 124 / 10 * c) * (qi ^ 2 + qj ^ 2) := by
  -- the term `η - ψ - ρ`
  have hE : |η - ψ - ρ| ≤ 53 / 100 * nu * (qi + qj) + 27 / 100 * (qi ^ 2 + qj ^ 2) := by
    rw [hηψρ]
    have h1 : |(ri + qi / 2 + (rj + qj / 2)) * t| ≤ (|ri + qi / 2| + |rj + qj / 2|) * (101 / 100) := by
      rw [abs_mul]
      exact mul_le_mul (abs_add_le _ _) ht (abs_nonneg _) (by positivity)
    have h2 : |ri * rj * t| ≤ |ri| * |rj| * (101 / 100) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left ht (by positivity)
    have h3 : |(ri + qi / 2) * P1| ≤ |ri + qi / 2| * (1 / 100) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hP1 (abs_nonneg _)
    have h4 : |(rj + qj / 2) * P2| ≤ |rj + qj / 2| * (1 / 100) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hP2 (abs_nonneg _)
    have h5 : |(ri + qi / 2 + (rj + qj / 2)) * t + ri * rj * t + (ri + qi / 2) * P1 + (rj + qj / 2) * P2|
        ≤ |(ri + qi / 2 + (rj + qj / 2)) * t| + |ri * rj * t| + |(ri + qi / 2) * P1| + |(rj + qj / 2) * P2| := by
      have a1 := abs_add_le ((ri + qi / 2 + (rj + qj / 2)) * t + ri * rj * t + (ri + qi / 2) * P1)
        ((rj + qj / 2) * P2)
      have a2 := abs_add_le ((ri + qi / 2 + (rj + qj / 2)) * t + ri * rj * t) ((ri + qi / 2) * P1)
      have a3 := abs_add_le ((ri + qi / 2 + (rj + qj / 2)) * t) (ri * rj * t)
      linarith
    have hrr : |ri| * |rj| ≤ 13 / 100 * (Di ^ 2 + Dj ^ 2) := by
      have b1 : |ri| * |ri| ≤ 50 / 99 * Di * (50 / 99 * Di) :=
        mul_le_mul hri hri (abs_nonneg _) (by positivity)
      have b2 : |rj| * |rj| ≤ 50 / 99 * Dj * (50 / 99 * Dj) :=
        mul_le_mul hrj hrj (abs_nonneg _) (by positivity)
      have b3 := sq_nonneg (|ri| - |rj|)
      linarith [sq_nonneg Di, sq_nonneg Dj]
    have hDi2 : Di ^ 2 ≤ 10001 / 10000 * qi ^ 2 := by
      have := mul_le_mul hDqi hDqi hDi (by positivity)
      linarith [sq_nonneg qi]
    have hDj2 : Dj ^ 2 ≤ 10001 / 10000 * qj ^ 2 := by
      have := mul_le_mul hDqj hDqj hDj (by positivity)
      linarith [sq_nonneg qj]
    have hnq : 0 ≤ nu * qi := mul_nonneg hnu hqi
    have hnq' : 0 ≤ nu * qj := mul_nonneg hnu hqj
    have hrr0 : 0 ≤ |ri| * |rj| := by positivity
    have hsum : 0 ≤ |ri + qi / 2| + |rj + qj / 2| := by positivity
    have h6 : |η - ψ - ρ| ≤ 102 / 100 * (|ri + qi / 2| + |rj + qj / 2|) + 101 / 100 * (|ri| * |rj|) := by
      rw [hηψρ]
      linarith
    rw [← hηψρ]
    have e1 : 53 / 100 * nu * (qi + qj) = 53 / 100 * (nu * qi) + 53 / 100 * (nu * qj) := by ring
    rw [e1]
    linarith
  -- the term `L ρ`
  have hLρ : |P1 + P2| * |ρ| ≤ 3 / 2 * (101 / 100) * (qi ^ 2 + qj ^ 2) := by
    rw [hρ]
    have h1 := abs_L_rho (P1 := P1) (P2 := P2) hqi hqj
    have h2 : 3 / 4 * (qi + qj) * (P1 ^ 2 + P2 ^ 2) ≤ 3 / 4 * (qi + qj) * (101 / 100 * (qi + qj)) :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    linarith [sq_nonneg (qi - qj)]
  -- the term `L² η`
  have hL2 : (P1 + P2) ^ 2 * |η| ≤ 2 * (101 / 100) * (102 / 100) * (1 + 1 / 10 ^ 5) * (2 * (qi ^ 2 + qj ^ 2)) := by
    have h1 : (P1 + P2) ^ 2 ≤ 2 * (101 / 100 * (qi + qj)) := by linarith [sq_nonneg (P1 - P2)]
    have h2 : |η| ≤ 102 / 100 * ((1 + 1 / 10 ^ 5) * (qi + qj)) := by linarith
    have h3 : (P1 + P2) ^ 2 * |η| ≤ 2 * (101 / 100 * (qi + qj)) * (102 / 100 * ((1 + 1 / 10 ^ 5) * (qi + qj))) :=
      mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    linarith [sq_nonneg (qi - qj)]
  have hLE : |P1 + P2| * |η - ψ - ρ| ≤ 1 / 50 * |η - ψ - ρ| := mul_le_mul_of_nonneg_right hL (abs_nonneg _)
  have hq2 : 0 ≤ qi ^ 2 + qj ^ 2 := by positivity
  have hb2 : 2 * b * (|P1 + P2| * |ρ|) ≤ 2 * b * (3 / 2 * (101 / 100) * (qi ^ 2 + qj ^ 2)) :=
    mul_le_mul_of_nonneg_left hLρ (by positivity)
  have hb3 : 2 * b * (|P1 + P2| * |η - ψ - ρ|) ≤ 2 * b * (1 / 50 * |η - ψ - ρ|) :=
    mul_le_mul_of_nonneg_left hLE (by positivity)
  have hc4 : 3 * c * ((P1 + P2) ^ 2 * |η|)
      ≤ 3 * c * (2 * (101 / 100) * (102 / 100) * (1 + 1 / 10 ^ 5) * (2 * (qi ^ 2 + qj ^ 2))) :=
    mul_le_mul_of_nonneg_left hL2 (by positivity)
  have ha1 : (a + b / 25) * |η - ψ - ρ| ≤ (a + b / 25) * (53 / 100 * nu * (qi + qj) + 27 / 100 * (qi ^ 2 + qj ^ 2)) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have hbq : 0 ≤ b * (qi ^ 2 + qj ^ 2) := mul_nonneg hb hq2
  have hcq : 0 ≤ c * (qi ^ 2 + qj ^ 2) := mul_nonneg hc hq2
  linarith

/-! ## A configuration near the reference configuration -/

theorem D_le_nsq (d : ℕ → ℕ → ℝ) {i : ℕ} (hi : i < 11) : dot (d i) (d i) ≤ nsq d := by
  unfold nsq
  exact single_le_sum (f := fun i => dot (d i) (d i)) (fun i _ => dot_self_nonneg _) (mem_range.mpr hi)

/-- The rows of a combination of the coefficients. -/
theorem rowS_lin (a b c : ℕ → ℕ → ℝ) (α β γ : ℝ) (i : ℕ) :
    rowS (fun i j => α * a i j + β * b i j + γ * c i j) i = α * rowS a i + β * rowS b i + γ * rowS c i := by
  unfold rowS
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : j = i
  · rw [if_pos h, if_pos h, if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h, if_neg h, if_neg h]

/-- **The inequality of Cauchy and Schwarz** for the coordinates of eleven vectors. -/
theorem cs_double (f g : ℕ → ℕ → ℝ) :
    (∑ i ∈ range 11, ∑ k ∈ range 3, f i k * g i k) ^ 2
      ≤ (∑ i ∈ range 11, ∑ k ∈ range 3, f i k ^ 2) * (∑ i ∈ range 11, ∑ k ∈ range 3, g i k ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (range 11 ×ˢ range 3) (fun x => f x.1 x.2) (fun x => g x.1 x.2)
  simp only [Finset.sum_product] at h
  exact h

theorem nsq_eq (v : ℕ → ℕ → ℝ) : nsq v = ∑ i ∈ range 11, ∑ k ∈ range 3, v i k ^ 2 := by
  unfold nsq dot
  exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring

section Near

variable {p a b c y : ℕ → ℕ → ℝ} {K : Consts}

theorem q_le_D (G : G7 p a b c K) (hK : CK K) (d : ℕ → ℕ → ℝ) {i : ℕ} (hi : i < 11) :
    dot (tang p d i) (tang p d i) ≤ dot (d i) (d i) := by
  have hn := norm_lo G hK hi
  rw [dot_d_d p d (by linarith)]
  have : 0 ≤ rco p d i ^ 2 * dot (p i) (p i) := mul_nonneg (sq_nonneg _) (dot_self_nonneg _)
  linarith

theorem nsq_tang_le (G : G7 p a b c K) (hK : CK K) (d : ℕ → ℕ → ℝ) : nsq (tang p d) ≤ nsq d :=
  sum_le_sum fun i hi => q_le_D G hK d (mem_range.mp hi)

theorem r_abs (G : G7 p a b c K) (hK : CK K) (A : Aligned p y) {i : ℕ} (hi : i < 11) :
    |rco p (dsub y p) i| ≤ 50 / 99 * dot (dsub y p i) (dsub y p i) := by
  rw [rco_eq G hK A hi]
  have hn := norm_lo G hK hi
  have hD := dot_self_nonneg (dsub y p i)
  rw [abs_div, abs_neg, abs_of_nonneg hD, abs_of_pos (by linarith : (0 : ℝ) < 2 * dot (p i) (p i)),
    div_le_iff₀ (by linarith)]
  nlinarith [mul_nonneg hD (sub_nonneg.mpr hn)]

/-- The coefficient `e_i = r_i + q_i / 2` of the term of order three. -/
theorem e_abs (G : G7 p a b c K) (hK : CK K) (A : Aligned p y) {i : ℕ} (hi : i < 11) :
    |rco p (dsub y p) i + dot (tang p (dsub y p) i) (tang p (dsub y p) i) / 2|
      ≤ 51 / 100 * (K.nu * dot (tang p (dsub y p) i) (tang p (dsub y p) i))
        + 13 / 100 * dot (dsub y p i) (dsub y p i) ^ 2 := by
  obtain ⟨D, hD⟩ : ∃ D, D = dot (dsub y p i) (dsub y p i) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = dot (tang p (dsub y p) i) (tang p (dsub y p) i) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = rco p (dsub y p) i := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ n2, n2 = dot (p i) (p i) := ⟨_, rfl⟩
  rw [← hD, ← hq, ← hr]
  have hn : 99 / 100 ≤ n2 := by rw [hn2]; exact norm_lo G hK hi
  have hnu : |n2 - 1| ≤ K.nu := by rw [hn2]; exact norm_nu G hi
  have hDq : D = q + r ^ 2 * n2 := by rw [hD, hq, hr, hn2]; exact dot_d_d p _ (by linarith)
  have hrD : r = -D / (2 * n2) := by rw [hr, hD, hn2]; exact rco_eq G hK A hi
  have h1 : 2 * n2 * r = -D := by
    rw [hrD]
    field_simp
  have h2 : 2 * n2 * (r + q / 2) = q * (n2 - 1) - r ^ 2 * n2 := by linear_combination h1 - hDq
  have h3 : 4 * n2 * (r ^ 2 * n2) = D ^ 2 := by linear_combination (2 * n2 * r - D) * h1
  have hq0 : 0 ≤ q := by rw [hq]; exact dot_self_nonneg _
  have h4 : |q * (n2 - 1)| ≤ q * K.nu := by
    rw [abs_mul, abs_of_nonneg hq0]
    exact mul_le_mul_of_nonneg_left hnu hq0
  have h5 : 0 ≤ r ^ 2 * n2 := mul_nonneg (sq_nonneg _) (by linarith)
  have h6 : |r + q / 2| * (2 * n2) ≤ q * K.nu + r ^ 2 * n2 := by
    have e : |2 * n2 * (r + q / 2)| = |r + q / 2| * (2 * n2) := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * n2)]
      ring
    rw [← e, h2]
    calc |q * (n2 - 1) - r ^ 2 * n2| ≤ |q * (n2 - 1)| + |r ^ 2 * n2| := abs_sub _ _
      _ ≤ q * K.nu + r ^ 2 * n2 := by rw [abs_of_nonneg h5]; linarith
  have h7 : r ^ 2 * n2 ≤ 100 / 396 * D ^ 2 := by
    have : 396 / 100 * (r ^ 2 * n2) ≤ 4 * n2 * (r ^ 2 * n2) := by nlinarith
    linarith [sq_nonneg D]
  have h8 : |r + q / 2| * (198 / 100) ≤ |r + q / 2| * (2 * n2) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have h9 : 0 ≤ q * K.nu := mul_nonneg hq0 hK.nu0
  have e2 : K.nu * q = q * K.nu := mul_comm _ _
  rw [e2]
  nlinarith [sq_nonneg D]

theorem D_le_q (G : G7 p a b c K) (hK : CK K) (A : Aligned p y) (hX : nsq (dsub y p) ≤ 63 / 2000000)
    {i : ℕ} (hi : i < 11) :
    dot (dsub y p i) (dsub y p i) ≤ (1 + 1 / 10 ^ 5) * dot (tang p (dsub y p) i) (tang p (dsub y p) i) := by
  obtain ⟨D, hD⟩ : ∃ D, D = dot (dsub y p i) (dsub y p i) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = dot (tang p (dsub y p) i) (tang p (dsub y p) i) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = rco p (dsub y p) i := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ n2, n2 = dot (p i) (p i) := ⟨_, rfl⟩
  rw [← hD, ← hq]
  have hn : 99 / 100 ≤ n2 := by rw [hn2]; exact norm_lo G hK hi
  have hDq : D = q + r ^ 2 * n2 := by rw [hD, hq, hr, hn2]; exact dot_d_d p _ (by linarith)
  have hrD : r = -D / (2 * n2) := by rw [hr, hD, hn2]; exact rco_eq G hK A hi
  have h1 : 2 * n2 * r = -D := by
    rw [hrD]
    field_simp
  have h3 : 4 * n2 * (r ^ 2 * n2) = D ^ 2 := by linear_combination (2 * n2 * r - D) * h1
  have hD0 : 0 ≤ D := by rw [hD]; exact dot_self_nonneg _
  have hDX : D ≤ 63 / 2000000 := by rw [hD]; exact le_trans (D_le_nsq _ hi) hX
  -- `r² n2 = D² / (4 n2) ≤ D · 8 · 10⁻⁶`
  have h4 : r ^ 2 * n2 ≤ 8 / 10 ^ 6 * D := by
    have a1 : D ^ 2 ≤ 63 / 2000000 * D := by nlinarith
    have a2 : 396 / 100 * (r ^ 2 * n2) ≤ 4 * n2 * (r ^ 2 * n2) := by
      have : 0 ≤ r ^ 2 * n2 := mul_nonneg (sq_nonneg _) (by linarith)
      nlinarith
    linarith
  have hq0 : 0 ≤ q := by rw [hq]; exact dot_self_nonneg _
  nlinarith

/-- The change of the inner products of a pair, `Δ_ij = <y_i, y_j> - <p_i, p_j>`. -/
noncomputable def dlt (p y : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ := dot (y i) (y j) - dot (p i) (p j)

/-- The part of `Δ_ij` of order two and higher: `η_ij = (r_i + r_j) <p_i, p_j> + <d_i, d_j>`. -/
theorem dlt_eq (p y : ℕ → ℕ → ℝ) (i j : ℕ) :
    dlt p y i j = Lf p (tang p (dsub y p)) i j
      + ((rco p (dsub y p) i + rco p (dsub y p) j) * dot (p i) (p j) + dot (dsub y p i) (dsub y p j)) := by
  unfold dlt
  rw [dot_sub_expand p y i j]
  have h := Lf_d p (dsub y p) i j
  unfold Lf at h ⊢
  linarith

/-- **The inequality of a pair**: the polynomial of the pair is at least its terms of order one to three in the
tangential displacement, minus an error of order `ν q + q²`. -/
theorem pair_ineq (G : G7 p a b c K) (hK : CK K) (A : Aligned p y) (hX : nsq (dsub y p) ≤ 63 / 2000000)
    {i j : ℕ} (hij : i < j) (hj : j < 11) :
    a i j * Lf p (tang p (dsub y p)) i j
        + (a i j * psif p (tang p (dsub y p)) i j + b i j * Lf p (tang p (dsub y p)) i j ^ 2)
        + (c i j * Lf p (tang p (dsub y p)) i j ^ 3
          + 2 * b i j * (Lf p (tang p (dsub y p)) i j * psif p (tang p (dsub y p)) i j)
          + a i j * rhof p (tang p (dsub y p)) i j)
        - ((53 / 100 * K.nu * a i j + 53 / 2500 * K.nu * b i j + 0 * c i j)
            * (dot (tang p (dsub y p) i) (tang p (dsub y p) i) + dot (tang p (dsub y p) j) (tang p (dsub y p) j))
          + (27 / 100 * a i j + (27 / 2500 + 31 / 10) * b i j + 124 / 10 * c i j)
            * (dot (tang p (dsub y p) i) (tang p (dsub y p) i) ^ 2
              + dot (tang p (dsub y p) j) (tang p (dsub y p) j) ^ 2))
      ≤ a i j * dlt p y i j + b i j * dlt p y i j ^ 2 + c i j * dlt p y i j ^ 3 := by
  have hi : i < 11 := by omega
  set d := dsub y p with hd
  set v := tang p d with hv
  obtain ⟨ha, hb, hc, hbc⟩ := coef_facts G hK hij hj
  have hnu := hK.nu0
  -- the quantities of the pair
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
  have hP : dot (p i) (v j) ^ 2 + dot (v i) (p j) ^ 2 ≤ 101 / 100 * (dot (v i) (v i) + dot (v j) (v j)) := by
    linarith
  have hP1a : |dot (p i) (v j)| ≤ 1 / 100 := abs_le_of_sq_le_sq (by nlinarith) (by norm_num)
  have hP2a : |dot (v i) (p j)| ≤ 1 / 100 := abs_le_of_sq_le_sq (by nlinarith) (by norm_num)
  have hL : |dot (p i) (v j) + dot (v i) (p j)| ≤ 1 / 50 := by
    have : (dot (p i) (v j) + dot (v i) (p j)) ^ 2 ≤ (1 / 50) ^ 2 := by
      nlinarith [sq_nonneg (dot (p i) (v j) - dot (v i) (p j))]
    exact abs_le_of_sq_le_sq this (by norm_num)
  have ht := t_abs G hK hi hj
  have hri := r_abs G hK A hi
  have hrj := r_abs G hK A hj
  have hei := e_abs G hK A hi
  have hej := e_abs G hK A hj
  have hDqi := D_le_q G hK A hX hi
  have hDqj := D_le_q G hK A hX hj
  -- the term `η`
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
  have hLe : Lf p v i j = dot (p i) (v j) + dot (v i) (p j) := rfl
  have hψ : psif p v i j = dot (v i) (v j) - dot (p i) (p j) / 2 * (dot (v i) (v i) + dot (v j) (v j)) := rfl
  have hρ : rhof p v i j = -(1 / 2) * (dot (v j) (v j) * dot (v i) (p j) + dot (v i) (v i) * dot (p i) (v j)) := rfl
  have hηψρ : η - psif p v i j - rhof p v i j
      = (rco p d i + dot (v i) (v i) / 2 + (rco p d j + dot (v j) (v j) / 2)) * dot (p i) (p j)
        + rco p d i * rco p d j * dot (p i) (p j) + (rco p d i + dot (v i) (v i) / 2) * dot (p i) (v j)
        + (rco p d j + dot (v j) (v j) / 2) * dot (v i) (p j) := by
    rw [hη_def, hψ, hρ, dot_d_d' p d i j]
    ring
  have hlow := pair_lower ha hb hc hbc (hLe ▸ hL) hη1 (ψ := psif p v i j) (ρ := rhof p v i j)
  have herr := pair_err ha hb hc hqi hqj hDi hDj hnu hP hP1a hP2a ht hri hrj hei hej hη hDqi hDqj hL
    (psif p v i j) (rhof p v i j) hηψρ hρ
  rw [← hLe] at herr
  rw [hΔ]
  have e : (53 / 100 * K.nu * a i j + 53 / 2500 * K.nu * b i j + 0 * c i j)
          * (dot (v i) (v i) + dot (v j) (v j))
        + (27 / 100 * a i j + (27 / 2500 + 31 / 10) * b i j + 124 / 10 * c i j)
          * (dot (v i) (v i) ^ 2 + dot (v j) (v j) ^ 2)
      = (a i j + b i j / 25) * (53 / 100 * K.nu * (dot (v i) (v i) + dot (v j) (v j)))
        + (27 / 100 * (a i j + b i j / 25) + 31 / 10 * b i j + 124 / 10 * c i j)
          * (dot (v i) (v i) ^ 2 + dot (v j) (v j) ^ 2) := by ring
  rw [e]
  linarith

/-- **The sum of the errors.** -/
theorem err_sum (G : G7 p a b c K) (hK : CK K) (v : ℕ → ℕ → ℝ) :
    sumP (fun i j => (53 / 100 * K.nu * a i j + 53 / 2500 * K.nu * b i j + 0 * c i j)
          * (dot (v i) (v i) + dot (v j) (v j))
        + (27 / 100 * a i j + (27 / 2500 + 31 / 10) * b i j + 124 / 10 * c i j)
          * (dot (v i) (v i) ^ 2 + dot (v j) (v j) ^ 2))
      ≤ 3 * K.nu * nsq v + 150 * nsq v ^ 2 := by
  have hsym : ∀ (α β γ : ℝ), ∀ i j, i < j → j < 11 →
      α * a i j + β * b i j + γ * c i j = α * a j i + β * b j i + γ * c j i := by
    intro α β γ i j hij hj
    obtain ⟨h1, h2, h3⟩ := G.sym i j hij hj
    rw [h1, h2, h3]
  rw [sumP_add, sumP_rows _ _ (hsym _ _ _), sumP_rows _ _ (hsym _ _ _)]
  simp only [rowS_lin]
  have hnu := hK.nu0
  have hra := hK.ra
  have hrb := hK.rb
  have hrc := hK.rc
  have hq : ∀ i, 0 ≤ dot (v i) (v i) := fun i => dot_self_nonneg _
  have h1 : ∑ i ∈ range 11, dot (v i) (v i) * (53 / 100 * K.nu * rowS a i + 53 / 2500 * K.nu * rowS b i + 0 * rowS c i)
      ≤ ∑ i ∈ range 11, dot (v i) (v i) * (3 * K.nu) := by
    refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hq i)
    obtain ⟨r1, r2, _⟩ := G.rows i (mem_range.mp hi)
    have a1 : 53 / 100 * K.nu * rowS a i ≤ 53 / 100 * K.nu * (2615 / 512) :=
      mul_le_mul_of_nonneg_left (le_trans r1 hra) (by positivity)
    have a2 : 53 / 2500 * K.nu * rowS b i ≤ 53 / 2500 * K.nu * (1643 / 256) :=
      mul_le_mul_of_nonneg_left (le_trans r2 hrb) (by positivity)
    nlinarith
  have h2 : ∑ i ∈ range 11, dot (v i) (v i) ^ 2
        * (27 / 100 * rowS a i + (27 / 2500 + 31 / 10) * rowS b i + 124 / 10 * rowS c i)
      ≤ ∑ i ∈ range 11, dot (v i) (v i) ^ 2 * 150 := by
    refine sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    obtain ⟨r1, r2, r3⟩ := G.rows i (mem_range.mp hi)
    linarith
  have h3 : ∑ i ∈ range 11, dot (v i) (v i) ^ 2 ≤ nsq v ^ 2 := sum_sq_le_sq _ fun i _ => hq i
  rw [← Finset.sum_mul] at h1 h2
  have h4 : ∑ i ∈ range 11, dot (v i) (v i) = nsq v := rfl
  rw [h4] at h1
  nlinarith

/-- **The lower bound of the polynomial below the energy**, in the norm `V = |v|` of the tangential part. -/
theorem expand_lower (G : G7 p a b c K) (hK : CK K) (A : Aligned p y) (hX : nsq (dsub y p) ≤ 63 / 2000000) :
    -K.gam * Real.sqrt (nsq (tang p (dsub y p))) + (K.kappa - 3 * K.nu) * nsq (tang p (dsub y p))
        - K.c3 * Real.sqrt (nsq (tang p (dsub y p))) ^ 3 - 150 * nsq (tang p (dsub y p)) ^ 2
      ≤ sumP (fun i j => a i j * dlt p y i j + b i j * dlt p y i j ^ 2 + c i j * dlt p y i j ^ 3) := by
  set v := tang p (dsub y p) with hv
  set V := Real.sqrt (nsq v) with hV
  have hQ : 0 ≤ nsq v := nsq_nonneg v
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  have hV2 : V ^ 2 = nsq v := Real.sq_sqrt hQ
  -- the sum of the inequalities of the pairs
  have hsum := sumP_le (fun i j hij hj => pair_ineq G hK A hX hij hj)
  rw [sumP_sub, sumP_add, sumP_add] at hsum
  have herr := err_sum G hK v
  -- the first-order term
  have hsymA : ∀ i j, i < j → j < 11 → a i j = a j i := fun i j hij hj => (G.sym i j hij hj).1
  have hlin : sumP (fun i j => a i j * Lf p v i j) = ∑ i ∈ range 11, ∑ k ∈ range 3,
      (frc p a i k - dot (frc p a i) (p i) * p i k) * v i k := by
    rw [sumP_lin a p v hsymA]
    refine sum_congr rfl fun i hi => ?_
    have hperp := tang_perp G hK (d := dsub y p) (mem_range.mp hi)
    have e : ∑ k ∈ range 3, (frc p a i k - dot (frc p a i) (p i) * p i k) * v i k
        = dot (frc p a i) (v i) - dot (frc p a i) (p i) * dot (p i) (v i) := by
      unfold dot
      rw [Finset.mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by ring
    rw [e, hperp, mul_zero, sub_zero]
  have hgrad : -K.gam * V ≤ sumP (fun i j => a i j * Lf p v i j) := by
    rw [hlin]
    have h1 := cs_double (fun i k => frc p a i k - dot (frc p a i) (p i) * p i k) v
    have h2 := G.grad
    rw [← nsq_eq v] at h1
    have h3 : (∑ i ∈ range 11, ∑ k ∈ range 3, (frc p a i k - dot (frc p a i) (p i) * p i k) * v i k) ^ 2
        ≤ (K.gam * V) ^ 2 := by
      rw [mul_pow, hV2]
      exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hQ)
    have h4 := abs_le_of_sq_le_sq' h3 (mul_nonneg hK.gam0 hV0)
    linarith [h4.1]
  -- the quadratic term
  have hquad : K.kappa * nsq v ≤ Qf p a b v := by
    have h := G.hess v
    rw [hv, penf_tang G hK A, mul_zero, add_zero] at h
    exact h
  -- the cubic term
  have hcub : -(K.c3 * V ^ 3) ≤ Cf p a b c v := by
    have h := G.cub v fun i hi => tang_perp G hK hi
    have h2 : Cf p a b c v ^ 2 ≤ (K.c3 * V ^ 3) ^ 2 := by
      rw [mul_pow, ← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, hV2]
      exact h
    have h3 := abs_le_of_sq_le_sq' h2 (mul_nonneg hK.c30 (pow_nonneg hV0 3))
    linarith [h3.1]
  have hQf : Qf p a b v = sumP (fun i j => a i j * psif p v i j + b i j * Lf p v i j ^ 2) := rfl
  have hCf : Cf p a b c v = sumP (fun i j => c i j * Lf p v i j ^ 3 + 2 * b i j * (Lf p v i j * psif p v i j)
      + a i j * rhof p v i j) := rfl
  rw [← hQf, ← hCf] at hsum
  nlinarith

end Near

end N11.Analytic
