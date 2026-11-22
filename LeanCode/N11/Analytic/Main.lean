module

public import N11.Analytic.Exist
public import N11.Analytic.Align
public import N11.Analytic.Unique
public import N11.Analytic.Route

/-!
# The theorem for 11 points, analytic part: the theorem (row A12)

`thomson11_of`: the theorem for 11 points follows from the statement G7 (`G7 p a b c K` with the bounds `CK K` on
its constants), the link `∑_{a<b} (<p_a, p_b> - τ_ab)² ≤ 2^-45` with a table of centres `τ`, the theorem of the route
for `τ` (`RouteHyp τ`), a configuration of distinct points of the sphere with energy at most `40.59645051`, and the
closeness of `p` to the decimal candidate `Xdec` (`5·10⁻¹⁶` in every coordinate).

The proof. A minimizer `X₁` exists (`exists_minimizer`). For every minimizer `x` (`aligned_near`): the theorem of
the route gives a relabelling `σ` with `∑_{a<b} (<x_σa, x_σb> - τ_ab)² < 1/9000` (`route_confine`); with the link and
the norms of `p` the configuration `y_a = |p_a| U x_σa` has `∑_{a<b} (<y_a, y_b> - <p_a, p_b>)² ≤ 1.1113·10⁻⁴`
(`confine_y`) for every orthogonal `U`; the alignment chooses `U` with `∑_a y_a p_aᵀ` symmetric and positive
semidefinite (`exists_align`); the rigidity gives `|y - p|² ≤ 3.15·10⁻⁵` (`X_small`); the minimality and
`close_of_min` give `|U x_σa - p_a|² ≤ 10⁻²²`. The aligned minimizer `Z` of `X₁` is the configuration of the theorem:
it is critical (`critical`), and every minimizer `x` arises from it by an orthogonal map and a relabelling, since its
aligned form equals `Z` (`unique`).
-/

@[expose] public section

namespace N11.Analytic

open Finset Matrix N11.Local

section Main

variable {p a b c : ℕ → ℕ → ℝ} {K : Consts}

/-- The bound of the energy of the route. -/
noncomputable abbrev Etop : ℝ := 4059645051 / 100000000

theorem dot_lt_one {u w : ℕ → ℝ} (hu : dot u u = 1) (hw : dot w w = 1)
    (hne : ∃ k, k < 3 ∧ u k ≠ w k) : dot u w < 1 := by
  rcases lt_or_ge (dot u w) 1 with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk, hne⟩ := hne
    have h1 : dot (fun k => u k - w k) (fun k => u k - w k) = 2 - 2 * dot u w := by
      have : dot (fun k => u k - w k) (fun k => u k - w k) = dot u u - 2 * dot u w + dot w w := by
        simp only [dot_eq]
        ring
      rw [this, hu, hw]
      ring
    have h2 := sq_le_dot_self (fun k => u k - w k) hk
    have h3 : (u k - w k) ^ 2 ≤ 0 := by linarith
    have h4 : u k - w k = 0 := by nlinarith [sq_nonneg (u k - w k)]
    exact hne (by linarith)

/-- **The confinement of the inner products of the scaled configuration.** -/
theorem confine_y (G : G7 p a b c K) (hK : CK K) {τ : ℕ → ℕ → ℝ}
    (hlink : sumP (fun a b => (dot (p a) (p b) - τ a b) ^ 2) ≤ 1 / 2 ^ 45)
    {z : ℕ → ℕ → ℝ} (hz : ∀ i, i < 11 → dot (z i) (z i) = 1)
    (hc : sumP (fun a b => (dot (z a) (z b) - τ a b) ^ 2) < 1 / 9000) :
    sumP (fun a b => (dot (scl p z a) (scl p z b) - dot (p a) (p b)) ^ 2) ≤ 11113 / 10 ^ 8 := by
  have hnu := hK.nu1
  have hnu0 := hK.nu0
  have hθ : (0 : ℝ) < 1 / 8192 := by norm_num
  have hpair : ∀ i j, i < j → j < 11 → (dot (scl p z i) (scl p z j) - dot (p i) (p j)) ^ 2
      ≤ (1 + 1 / 8192) * (dot (z i) (z j) - τ i j) ^ 2
        + (1 + 1 / (1 / 8192)) * (2 * (τ i j - dot (p i) (p j)) ^ 2 + 2 * (9 * (1 / 10 ^ 17) ^ 2)) := by
    intro i j hij hj
    have hi : i < 11 := by omega
    have e : dot (scl p z i) (scl p z j) - dot (p i) (p j)
        = (dot (z i) (z j) - τ i j) + ((τ i j - dot (p i) (p j)) + (nrm p i * nrm p j - 1) * dot (z i) (z j)) := by
      unfold scl
      rw [dot_smul_smul]
      ring
    rw [e]
    have h1 := sq_add_le (dot (z i) (z j) - τ i j) ((τ i j - dot (p i) (p j)) + (nrm p i * nrm p j - 1) * dot (z i) (z j)) _ hθ
    have h2 : ((τ i j - dot (p i) (p j)) + (nrm p i * nrm p j - 1) * dot (z i) (z j)) ^ 2
        ≤ 2 * (τ i j - dot (p i) (p j)) ^ 2 + 2 * (9 * (1 / 10 ^ 17) ^ 2) := by
      have a1 := m_close G hK hi hj
      have a2 : dot (z i) (z j) ^ 2 ≤ 1 := by
        have := dot_sq_le (z i) (z j)
        rw [hz i hi, hz j hj] at this
        linarith
      have a3 : (nrm p i * nrm p j - 1) ^ 2 ≤ (3 * (1 / 10 ^ 17)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
      have a4 : ((nrm p i * nrm p j - 1) * dot (z i) (z j)) ^ 2 ≤ 9 * (1 / 10 ^ 17) ^ 2 := by
        rw [mul_pow]
        have : (3 * (1 / 10 ^ 17 : ℝ)) ^ 2 = 9 * (1 / 10 ^ 17) ^ 2 := by ring
        rw [this] at a3
        have a5 := sq_nonneg (nrm p i * nrm p j - 1)
        nlinarith [sq_nonneg (dot (z i) (z j))]
      nlinarith [sq_nonneg ((τ i j - dot (p i) (p j)) - (nrm p i * nrm p j - 1) * dot (z i) (z j))]
    have h3 : 0 ≤ 1 + 1 / (1 / 8192 : ℝ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  have hsum := sumP_le hpair
  rw [sumP_add, sumP_mul, sumP_mul, sumP_add, sumP_mul, sumP_const] at hsum
  have h1 : sumP (fun i j => (τ i j - dot (p i) (p j)) ^ 2) ≤ 1 / 2 ^ 45 := by
    have e : sumP (fun i j => (τ i j - dot (p i) (p j)) ^ 2) = sumP (fun a b => (dot (p a) (p b) - τ a b) ^ 2) :=
      sumP_congr fun i j _ _ => by ring
    rw [e]
    exact hlink
  have h2 : 0 ≤ sumP (fun a b => (dot (z a) (z b) - τ a b) ^ 2) := sumP_nonneg fun i j _ _ => sq_nonneg _
  norm_num at hsum h1 ⊢
  nlinarith

/-- **The rigidity bound for a configuration aligned with `p`.** -/
theorem X_small (G : G7 p a b c K) (hK : CK K) {y : ℕ → ℕ → ℝ} (A : Aligned p y)
    (hΔ : sumP (fun a b => (dot (y a) (y b) - dot (p a) (p b)) ^ 2) ≤ 11113 / 10 ^ 8) :
    nsq (dsub y p) ≤ 63 / 2000000 := by
  have hs := hK.sigma2
  have hR0 := hK.penR0
  have hR1 := hK.penR1
  have hX0 := nsq_nonneg (dsub y p)
  -- the a priori bound
  have h1 := rigid_apriori G hR0 A hΔ
  have hX1 : nsq (dsub y p) ≤ 6 / 1000 := by
    have : K.penR * (11113 / 10 ^ 8) ≤ 64 * (11113 / 10 ^ 8) := mul_le_mul_of_nonneg_right hR1 (by norm_num)
    have h2 : 3643 / 1024 * nsq (dsub y p) ≤ K.sigma2 * nsq (dsub y p) := mul_le_mul_of_nonneg_right hs hX0
    nlinarith
  -- two refinements
  have h2 := rigid_refine G (by linarith) A hΔ (θ := 1 / 16) (by norm_num) hX1
  have hX2 : nsq (dsub y p) ≤ 35 / 10 ^ 6 := by
    have hc : 341 / 100 ≤ K.sigma2 - ((1 + 1 / (1 / 16)) / 2 + K.penR / 4) * (6 / 1000) := by
      norm_num
      linarith
    have := mul_le_mul_of_nonneg_right hc hX0
    norm_num at h2 this ⊢
    nlinarith
  have h3 := rigid_refine G (by linarith) A hΔ (θ := 1 / 256) (by norm_num) hX2
  have hc : 355 / 100 ≤ K.sigma2 - ((1 + 1 / (1 / 256)) / 2 + K.penR / 4) * (35 / 10 ^ 6) := by
    norm_num
    linarith
  have := mul_le_mul_of_nonneg_right hc hX0
  norm_num at h3 this ⊢
  nlinarith

/-- The aligned and relabelled configuration of the statement. -/
def alignC (U : Matrix (Fin 3) (Fin 3) ℝ) (σ : Equiv.Perm (Fin 11)) (x : Fin 11 → Fin 3 → ℝ) : Fin 11 → Fin 3 → ℝ :=
  fun a => U.mulVec (x (σ a))

theorem energy_alignC {U : Matrix (Fin 3) (Fin 3) ℝ} (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (σ : Equiv.Perm (Fin 11)) (x : Fin 11 → Fin 3 → ℝ) : energy (alignC U σ x) = energy x := by
  unfold alignC
  rw [energy_mulVec U hU (fun a => x (σ a)), energy_comp_perm]

theorem onSphere_comp (x : Fin 11 → Fin 3 → ℝ) (hx : OnSphere x) (σ : Equiv.Perm (Fin 11)) :
    OnSphere (fun a => x (σ a)) := fun a => hx (σ a)

theorem onSphere_alignC {U : Matrix (Fin 3) (Fin 3) ℝ} (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (σ : Equiv.Perm (Fin 11)) {x : Fin 11 → Fin 3 → ℝ} (hx : OnSphere x) : OnSphere (alignC U σ x) :=
  onSphere_mulVec U hU _ (onSphere_comp x hx σ)

theorem injective_alignC {U : Matrix (Fin 3) (Fin 3) ℝ} (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ)
    (σ : Equiv.Perm (Fin 11)) {x : Fin 11 → Fin 3 → ℝ} (hx : Function.Injective x) :
    Function.Injective (alignC U σ x) :=
  injective_mulVec U hU _ (hx.comp σ.injective)

/-- Distinct points of the sphere have inner products below one. -/
theorem dot_lt_of_inj {x : Fin 11 → Fin 3 → ℝ} (hx : OnSphere x) (hinj : Function.Injective x) :
    ∀ i j, i < 11 → j < 11 → i ≠ j → dot (toN x i) (toN x j) < 1 := by
  intro i j hi hj hij
  have hs := (onSphere_iff_dot x).mp hx
  refine dot_lt_one (hs i hi) (hs j hj) ?_
  by_contra hall
  have hne : (⟨i, hi⟩ : Fin 11) ≠ ⟨j, hj⟩ := fun h => hij (Fin.mk.inj h)
  apply hne
  apply hinj
  funext k
  have := toN_apply x ⟨i, hi⟩ k
  have h2 := toN_apply x ⟨j, hj⟩ k
  simp only at this h2
  rw [← this, ← h2]
  by_contra hk
  exact hall ⟨k.val, k.isLt, hk⟩

/-- A configuration in the form of `N11/Local` with points of the sphere and inner products below one is a
configuration of distinct points of the sphere. -/
theorem ofN_valid {z : ℕ → ℕ → ℝ} (hz : ∀ i, i < 11 → dot (z i) (z i) = 1)
    (hd : ∀ i j, i < 11 → j < 11 → i ≠ j → dot (z i) (z j) < 1) : OnSphere (ofN z) ∧ Function.Injective (ofN z) := by
  constructor
  · intro i
    have h := dot_ofN z i i
    rw [hz i i.isLt] at h
    rw [← h]
    exact sum_congr rfl fun k _ => by ring
  · intro i j hij
    by_contra hne
    have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
    have h1 := hd i j i.isLt j.isLt hne'
    have h2 : dot (z i) (z j) = dot (z i) (z i) := by
      rw [← dot_ofN, ← dot_ofN, hij]
    rw [h2, hz i i.isLt] at h1
    exact lt_irrefl _ h1

/-- **The aligned form of a minimizer.** -/
theorem aligned_near (G : G7 p a b c K) (hK : CK K) {τ : ℕ → ℕ → ℝ} (hR : RouteHyp τ)
    (hlink : sumP (fun a b => (dot (p a) (p b) - τ a b) ^ 2) ≤ 1 / 2 ^ 45)
    {x : Fin 11 → Fin 3 → ℝ} (hx : OnSphere x) (hinj : Function.Injective x) (hE : energy x ≤ Etop)
    (hmin : ∀ x' : Fin 11 → Fin 3 → ℝ, OnSphere x' → Function.Injective x' → energy x ≤ energy x') :
    ∃ U ∈ Matrix.orthogonalGroup (Fin 3) ℝ, ∃ σ : Equiv.Perm (Fin 11),
      NearP p (toN (alignC U σ x)) ∧ (4059644951 : ℝ) / 100000000 < energy x := by
  obtain ⟨σ, hlow, hc⟩ := route_confine hR x hx hinj hE
  -- the alignment of the scaled configuration
  set Y : Fin 11 → Fin 3 → ℝ := fun a => nrm p a • x (σ a) with hY
  set P : Fin 11 → Fin 3 → ℝ := fun a k => p a k with hP
  obtain ⟨U, hU, hsym, hpsd⟩ := exists_align Y P
  refine ⟨U, hU, σ, ?_, hlow⟩
  set z := alignC U σ x with hz_def
  set zN := toN z with hzN
  have hzs : OnSphere z := onSphere_alignC hU σ hx
  have hzi : Function.Injective z := injective_alignC hU σ hinj
  have hsph : ∀ i, i < 11 → dot (zN i) (zN i) = 1 := (onSphere_iff_dot z).mp hzs
  have hdist := dot_lt_of_inj hzs hzi
  -- the inner products are those of the relabelled configuration
  have hdot : ∀ i j, i < 11 → j < 11 → dot (zN i) (zN j) = dot (toN (fun c => x (σ c)) i) (toN (fun c => x (σ c)) j) := by
    intro i j hi hj
    have e1 := dot_toN z ⟨i, hi⟩ ⟨j, hj⟩
    have e2 := dot_toN (fun c => x (σ c)) ⟨i, hi⟩ ⟨j, hj⟩
    simp only at e1 e2
    rw [e1, e2]
    exact dot_mulVec U hU _ _
  have hc' : sumP (fun a b => (dot (zN a) (zN b) - τ a b) ^ 2) < 1 / 9000 := by
    have e : sumP (fun a b => (dot (zN a) (zN b) - τ a b) ^ 2)
        = sumP (fun a b => (dot (toN (fun c => x (σ c)) a) (toN (fun c => x (σ c)) b) - τ a b) ^ 2) :=
      sumP_congr fun i j hij hj => by rw [hdot i j (by omega) hj]
    rw [e]
    exact hc
  -- the matrix of the alignment in the form of `N11/Local`
  have hS : ∀ k l : Fin 3, alignS Y P U k l = ∑ i ∈ range 11, scl p zN i k * p i l := by
    intro k l
    unfold alignS
    rw [← sum_fin11 (fun i => scl p zN i k * p i l)]
    refine sum_congr rfl fun i _ => ?_
    have e1 : U.mulVec (Y i) k = nrm p i * z i k := by
      rw [hY]
      simp only
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [e1, hP]
    unfold scl
    rw [hzN, toN_apply]
  have hA : Aligned p (scl p zN) := by
    refine ⟨fun i hi => ?_, fun k l hk hl => ?_, fun u => ?_⟩
    · unfold scl
      rw [dot_smul_smul, hsph i hi, mul_one, ← sq, nrm_sq G hK hi]
    · have := hsym ⟨k, hk⟩ ⟨l, hl⟩
      rw [hS, hS] at this
      exact this
    · have h1 := hpsd (fun k => u k)
      have e : ∑ k : Fin 3, ∑ l : Fin 3, u k * u l * alignS Y P U k l
          = ∑ k ∈ range 3, ∑ l ∈ range 3, u k * u l * ∑ i ∈ range 11, scl p zN i k * p i l := by
        rw [← sum_fin3 (fun k => ∑ l ∈ range 3, u k * u l * ∑ i ∈ range 11, scl p zN i k * p i l)]
        refine sum_congr rfl fun k _ => ?_
        rw [← sum_fin3 (fun l => u k * u l * ∑ i ∈ range 11, scl p zN i k * p i l)]
        exact sum_congr rfl fun l _ => by rw [hS]
      rw [e] at h1
      exact h1
  have hΔ := confine_y G hK hlink hsph hc'
  have hX := X_small G hK hA hΔ
  -- the minimality against the normalized reference configuration
  have hph := ofN_valid (fun i hi => phat_sph G hK hi) (fun i j hi hj hij => phat_lt G hK hi hj hij)
  have hEz : En zN ≤ En (phat p) := by
    have h1 := hmin (ofN (phat p)) hph.1 hph.2
    rw [← energy_alignC hU σ x, energy_eq_En z hzs, energy_ofN _ hph.1] at h1
    exact h1
  have hclose := close_of_min G hK hsph hdist hA hX hEz
  exact ⟨hsph, hclose, hA.sym⟩

/-- **The theorem for 11 points from its computational statements.** -/
theorem thomson11_of (G : G7 p a b c K) (hK : CK K) {τ : ℕ → ℕ → ℝ} (hR : RouteHyp τ)
    (hlink : sumP (fun a b => (dot (p a) (p b) - τ a b) ^ 2) ≤ 1 / 2 ^ 45)
    (hne : ∃ x : Fin 11 → EuclideanSpace ℝ (Fin 3), (∀ i, ‖x i‖ = 1) ∧ Function.Injective x ∧
      N11.Circ.energy x ≤ Etop)
    (hdec : ∀ (i : Fin 11) (k : Fin 3), |p i k - Xdec i k| ≤ 5 / 10 ^ 16) :
    Thomson11 := by
  -- a minimizer
  obtain ⟨x0, hx0u, hx0i, hx0E⟩ := hne
  have hx0s : OnSphere (ofE x0) := onSphere_of_norm _ (by rw [toE_ofE]; exact hx0u)
  have hx0j : Function.Injective (ofE x0) := by
    intro i j hij
    apply hx0i
    rw [← toE_ofE x0]
    unfold toE
    rw [hij]
  have hx0E' : energy (ofE x0) ≤ Etop := by rw [← circ_energy_toE, toE_ofE]; exact hx0E
  obtain ⟨X1, hX1s, hX1i, hX1E, hX1min⟩ := exists_minimizer (by norm_num) hx0s hx0j hx0E'
  -- its aligned form
  obtain ⟨U, hU, σ, hN, hlow⟩ := aligned_near G hK hR hlink hX1s hX1i hX1E hX1min
  set Z := alignC U σ X1 with hZ
  have hZs : OnSphere Z := onSphere_alignC hU σ hX1s
  have hZi : Function.Injective Z := injective_alignC hU σ hX1i
  have hZE : energy Z = energy X1 := energy_alignC hU σ X1
  -- `Z` is critical
  have hcrit : ∀ i, i < 11 → ∀ k, k < 3 →
      frc (toN Z) (alpha (toN Z)) i k = dot (frc (toN Z) (alpha (toN Z)) i) (toN Z i) * toN Z i k := by
    have hsph := (onSphere_iff_dot Z).mp hZs
    have hsep : ∀ i j, i < 11 → j < 11 → i ≠ j → 1 / Etop ^ 2 ≤ 2 - 2 * dot (toN Z i) (toN Z j) := by
      intro i j hi hj hij
      have h1 := sep_of_energy_le (B := Etop) (by norm_num) Z hZi (hZE.le.trans hX1E) ⟨i, hi⟩ ⟨j, hj⟩
        (fun h => hij (Fin.mk.inj h))
      rw [sqdist_eq, hZs ⟨i, hi⟩, hZs ⟨j, hj⟩] at h1
      have e : dot (toN Z i) (toN Z j) = ∑ k, Z ⟨i, hi⟩ k * Z ⟨j, hj⟩ k := dot_toN Z ⟨i, hi⟩ ⟨j, hj⟩
      linarith
    have hmin : IsMinN (toN Z) := by
      intro z' hz' hd'
      obtain ⟨h1, h2⟩ := ofN_valid hz' hd'
      have h3 := hX1min (ofN z') h1 h2
      rw [← hZE, energy_eq_En Z hZs, energy_ofN z' h1] at h3
      exact h3
    exact critical hsph (by norm_num) hsep hmin
  refine ⟨Z, hZs, hZi, ?_, ?_, ?_, ?_⟩
  · -- the coordinates
    intro i k
    have h1 := hN.close i i.isLt
    have h2 := sq_le_dot_self (fun k => toN Z i k - p i k) k.isLt
    rw [toN_apply] at h2
    have h3 : |Z i k - p i k| ≤ 1 / 10 ^ 11 := abs_le_of_sq_le_sq (by norm_num at h1 ⊢; linarith) (by norm_num)
    have h4 := hdec i k
    have h5 := abs_sub_le (Z i k) (p i k) (Xdec i k)
    have h6 : (1 : ℝ) / 10 ^ 11 + 5 / 10 ^ 16 ≤ 1 / 10 ^ 10 := by norm_num
    linarith
  · rw [hZE]
    have e : (4059644951 : ℝ) / 10 ^ 8 = 4059644951 / 100000000 := by norm_num
    rw [e]
    exact hlow
  · rw [hZE]
    have e : (4059645051 : ℝ) / 10 ^ 8 = Etop := by norm_num
    rw [e]
    exact hX1E
  · intro x hx hinj
    have hZx : energy Z ≤ energy x := by rw [hZE]; exact hX1min x hx hinj
    refine ⟨hZx, fun heq => ?_⟩
    -- `x` is a minimizer; its aligned form is `Z`
    have hxE : energy x ≤ Etop := by rw [heq, hZE]; exact hX1E
    have hxmin : ∀ x' : Fin 11 → Fin 3 → ℝ, OnSphere x' → Function.Injective x' → energy x ≤ energy x' := by
      intro x' h1 h2
      rw [heq, hZE]
      exact hX1min x' h1 h2
    obtain ⟨U', hU', σ', hN', _⟩ := aligned_near G hK hR hlink hx hinj hxE hxmin
    have hEn : En (toN (alignC U' σ' x)) ≤ En (toN Z) := by
      rw [← energy_eq_En _ (onSphere_alignC hU' σ' hx), ← energy_eq_En Z hZs, energy_alignC hU' σ' x, heq]
    have hu := unique G hK hN hN' hcrit hEn
    have hZ' : alignC U' σ' x = Z := by
      funext i k
      have := hu i i.isLt k k.isLt
      rw [toN_apply, toN_apply] at this
      exact this
    -- the inverse of the orthogonal map
    have hUt : U'ᵀ * U' = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp hU'
    have hUt' : U'ᵀ ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
      rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_transpose]
      exact hUt
    refine ⟨U'ᵀ, hUt', σ'.symm, fun i => ?_⟩
    have h1 : U'.mulVec (x (σ' (σ'.symm i))) = Z (σ'.symm i) := by
      rw [← hZ']
      rfl
    rw [Equiv.apply_symm_apply] at h1
    rw [← h1, Matrix.mulVec_mulVec, hUt, Matrix.one_mulVec]

end Main

end N11.Analytic

namespace N11

open N11.Local

/-- **The theorem for 11 points from its computational statements**: the statement G7 for `p a b c K` with the
bounds `CK K`, the theorem of the route for the table of centres `τ`, the link of `p` with `τ`, a configuration of
distinct points of the sphere with energy at most `40.59645051`, and the closeness of `p` to the candidate `Xdec`. -/
theorem thomson11_of {p a b c : ℕ → ℕ → ℝ} {K : Consts} (G : G7 p a b c K) (hK : N11.Analytic.CK K)
    {τ : ℕ → ℕ → ℝ} (hR : N11.Analytic.RouteHyp τ)
    (hlink : sumP (fun a b => (dot (p a) (p b) - τ a b) ^ 2) ≤ 1 / 2 ^ 45)
    (hne : ∃ x : Fin 11 → EuclideanSpace ℝ (Fin 3), (∀ i, ‖x i‖ = 1) ∧ Function.Injective x ∧
      N11.Circ.energy x ≤ 4059645051 / 100000000)
    (hdec : ∀ (i : Fin 11) (k : Fin 3), |p i k - Xdec i k| ≤ 5 / 10 ^ 16) :
    Thomson11 :=
  N11.Analytic.thomson11_of G hK hR hlink hne hdec

end N11
