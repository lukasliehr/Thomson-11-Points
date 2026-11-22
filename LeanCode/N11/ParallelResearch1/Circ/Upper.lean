module

public import N11.ParallelResearch1.Circ.Graph
public import N11.ParallelResearch1.Circ.UpperKernel

/-!
# An upper bound for the energy of an explicit configuration: soundness

`Pt.vec p` is the point `((a - d) / d, (b - d) / d, (c - d) / d)` of `ℝ³`, and `confOf pts N` the configuration of
the first `N` points of a list. `upper_sound`: if `upperOk N s pts rs tp tq` holds, then the configuration consists
of distinct unit vectors with inner products at most `73/100` (`Sep`), and its Coulomb energy is at most `tp / tq`.
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

theorem inner_toLp3 (x y : Fin 3 → ℝ) :
    inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3)) (WithLp.toLp 2 y) = ∑ k, x k * y k := by
  simp [PiLp.inner_apply, mul_comm]

/-- The point of `ℝ³` of an entry. -/
noncomputable def Pt.vec (p : Pt) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![((p.a : ℝ) - p.d) / p.d, ((p.b : ℝ) - p.d) / p.d, ((p.c : ℝ) - p.d) / p.d]

/-- The configuration of the first `N` points of a list. -/
noncomputable def confOf (pts : List Pt) (N : ℕ) : Fin N → EuclideanSpace ℝ (Fin 3) := fun i => (nthPt pts i).vec

theorem Pt.inner_vec (p q : Pt) :
    inner ℝ p.vec q.vec = (((p.a : ℝ) - p.d) * ((q.a : ℝ) - q.d) + ((p.b : ℝ) - p.d) * ((q.b : ℝ) - q.d)
      + ((p.c : ℝ) - p.d) * ((q.c : ℝ) - q.d)) / (p.d * q.d) := by
  unfold Pt.vec
  rw [inner_toLp3, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem unitOk_sound {p : Pt} (h : unitOk p = true) : ‖p.vec‖ = 1 := by
  unfold unitOk at h
  rw [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hd, he⟩ := h
  have he' : p.a * p.a + p.b * p.b + p.c * p.c + 2 * (p.d * p.d) = 2 * p.d * (p.a + p.b + p.c) :=
    Nat.eq_of_beq_eq_true he
  have hr : (p.a : ℝ) * p.a + p.b * p.b + p.c * p.c + 2 * ((p.d : ℝ) * p.d) = 2 * p.d * (p.a + p.b + p.c) := by
    exact_mod_cast he'
  have hd' : (0 : ℝ) < p.d := by exact_mod_cast hd
  have h2 : ‖p.vec‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, Pt.inner_vec, div_eq_one_iff_eq (by positivity)]
    linear_combination hr
  have h0 : 0 ≤ ‖p.vec‖ := norm_nonneg _
  nlinarith [h2, h0]

/-- `1 - ⟨p, q⟩ = (wPos - wNeg) / (d_p d_q)`. -/
theorem one_sub_inner {p q : Pt} (hp : 0 < p.d) (hq : 0 < q.d) :
    1 - inner ℝ p.vec q.vec = ((wPos p q : ℝ) - wNeg p q) / (p.d * q.d) := by
  have hp' : (0 : ℝ) < p.d := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q.d := by exact_mod_cast hq
  rw [Pt.inner_vec]
  have hw : (wPos p q : ℝ) = q.d * ((p.a : ℝ) + p.b + p.c) + p.d * ((q.a : ℝ) + q.b + q.c) := by
    have : wPos p q = q.d * (p.a + p.b + p.c) + p.d * (q.a + q.b + q.c) := rfl
    exact_mod_cast this
  have hn : (wNeg p q : ℝ) = 2 * ((p.d : ℝ) * q.d) + ((p.a : ℝ) * q.a + p.b * q.b + p.c * q.c) := by
    have : wNeg p q = 2 * (p.d * q.d) + (p.a * q.a + p.b * q.b + p.c * q.c) := rfl
    exact_mod_cast this
  rw [hw, hn]
  field_simp
  ring

theorem pairOk_sound {s : ℕ} {p q : Pt} {r : ℕ} (hp : unitOk p = true) (hq : unitOk q = true)
    (h : pairOk s p q r = true) :
    0 < r ∧ (r : ℝ) / 2 ^ s ≤ ‖p.vec - q.vec‖ ∧ inner ℝ p.vec q.vec ≤ 73 / 100 := by
  have hpd : 0 < p.d := by
    unfold unitOk at hp
    rw [Bool.and_eq_true, Nat.blt_eq] at hp
    exact hp.1
  have hqd : 0 < q.d := by
    unfold unitOk at hq
    rw [Bool.and_eq_true, Nat.blt_eq] at hq
    exact hq.1
  have hp' : (0 : ℝ) < p.d := by exact_mod_cast hpd
  have hq' : (0 : ℝ) < q.d := by exact_mod_cast hqd
  unfold pairOk at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨hr, h1⟩, h2⟩ := h
  have h1' : r * r * (p.d * q.d) + 2 ^ (2 * s + 1) * wNeg p q ≤ 2 ^ (2 * s + 1) * wPos p q := h1
  have h2' : 27 * (p.d * q.d) + 100 * wNeg p q ≤ 100 * wPos p q := h2
  have h1r : (r : ℝ) * r * (p.d * q.d) + 2 ^ (2 * s + 1) * wNeg p q ≤ 2 ^ (2 * s + 1) * wPos p q := by
    exact_mod_cast h1'
  have h2r : (27 : ℝ) * (p.d * q.d) + 100 * wNeg p q ≤ 100 * wPos p q := by exact_mod_cast h2'
  have hw := one_sub_inner hpd hqd
  have hdd : (0 : ℝ) < p.d * q.d := by positivity
  set W : ℝ := (wPos p q : ℝ) - wNeg p q with hW
  have hin : inner ℝ p.vec q.vec = 1 - W / (p.d * q.d) := by linarith
  refine ⟨hr, ?_, ?_⟩
  · -- the distance
    have hsq : ‖p.vec - q.vec‖ ^ 2 = 2 * W / (p.d * q.d) := by
      rw [@norm_sub_sq_real, unitOk_sound hp, unitOk_sound hq, hin]
      ring
    have hpow : (2 : ℝ) ^ (2 * s + 1) = 2 * (2 ^ s) ^ 2 := by
      rw [pow_succ, pow_mul, mul_comm]
      congr 1
      rw [← pow_mul, ← pow_mul, mul_comm]
    have hle : ((r : ℝ) / 2 ^ s) ^ 2 ≤ ‖p.vec - q.vec‖ ^ 2 := by
      rw [hsq, div_pow, div_le_div_iff₀ (by positivity) hdd]
      rw [hpow] at h1r
      nlinarith [h1r]
    exact le_of_sq_le_sq hle (norm_nonneg _)
  · rw [hin, sub_le_iff_le_add]
    have : (27 : ℝ) / 100 ≤ W / (p.d * q.d) := by
      rw [div_le_div_iff₀ (by norm_num) hdd]
      linarith
    linarith

theorem invUp_ge {s r : ℕ} (hr : 0 < r) : (2 : ℝ) ^ s / r ≤ (invUp s r : ℝ) / 2 ^ s := by
  have hq : 2 ^ (2 * s) ≤ invUp s r * r := by
    have e : invUp s r = (2 ^ (2 * s) + (r - 1)) / r := rfl
    rw [e]
    generalize 2 ^ (2 * s) = x
    have h1 := Nat.div_add_mod (x + (r - 1)) r
    have h2 := Nat.mod_lt (x + (r - 1)) hr
    generalize (x + (r - 1)) / r = q at h1 ⊢
    generalize (x + (r - 1)) % r = m at h1 h2
    have h3 : x ≤ r * q := by omega
    rw [Nat.mul_comm]
    exact h3
  have hq' : (2 : ℝ) ^ (2 * s) ≤ (invUp s r : ℝ) * r := by exact_mod_cast hq
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [div_le_div_iff₀ hr' (by positivity)]
  have : (2 : ℝ) ^ s * 2 ^ s = 2 ^ (2 * s) := by
    rw [← pow_add]
    congr 1
    omega
  nlinarith [hq']

/-- **The upper bound of the energy of an explicit configuration.** -/
theorem upper_sound {N s tp tq : ℕ} {pts : List Pt} {rs : List (List ℕ)} (h : upperOk N s pts rs tp tq = true) :
    Sep (confOf pts N) ∧ energy (confOf pts N) ≤ (tp : ℝ) / tq := by
  unfold upperOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨htq, hu⟩, hpair⟩, hsum⟩ := h
  rw [Nat.blt_eq] at htq
  have hunit : ∀ i < N, unitOk (nthPt pts i) = true := (allN_iff _ _).mp hu
  have hp : ∀ j < N, ∀ i < j, pairOk s (nthPt pts i) (nthPt pts j) (rAt rs i j) = true :=
    fun j hj i hi => (allN_iff _ _).mp ((allN_iff _ _).mp hpair j hj) i hi
  have hps : ∀ i j : Fin N, i < j → 0 < rAt rs i j ∧ (rAt rs i j : ℝ) / 2 ^ s ≤ ‖confOf pts N i - confOf pts N j‖
      ∧ inner ℝ (confOf pts N i) (confOf pts N j) ≤ 73 / 100 := fun i j hij =>
    pairOk_sound (hunit i i.isLt) (hunit j j.isLt) (hp j j.isLt i hij)
  have hdist : ∀ i j : Fin N, i < j → 0 < ‖confOf pts N i - confOf pts N j‖ := by
    intro i j hij
    obtain ⟨hr, hle, _⟩ := hps i j hij
    have : (0 : ℝ) < (rAt rs i j : ℝ) / 2 ^ s := by
      have : (0 : ℝ) < rAt rs i j := by exact_mod_cast hr
      positivity
    linarith
  refine ⟨⟨fun i => unitOk_sound (hunit i i.isLt), ?_, ?_⟩, ?_⟩
  · intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := hdist i j hl
      rw [hij, sub_self, norm_zero] at this
      exact lt_irrefl _ this
    · have := hdist j i hl
      rw [hij, sub_self, norm_zero] at this
      exact lt_irrefl _ this
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hl | hl
    · exact (hps i j hl).2.2
    · rw [real_inner_comm]
      exact (hps j i hl).2.2
  · -- the energy
    have hterm : ∀ i j : Fin N, i < j →
        1 / ‖confOf pts N i - confOf pts N j‖ ≤ (invUp s (rAt rs i j) : ℝ) / 2 ^ s := by
      intro i j hij
      obtain ⟨hr, hle, _⟩ := hps i j hij
      have hr' : (0 : ℝ) < rAt rs i j := by exact_mod_cast hr
      have h1 : 1 / ‖confOf pts N i - confOf pts N j‖ ≤ 1 / ((rAt rs i j : ℝ) / 2 ^ s) :=
        one_div_le_one_div_of_le (by positivity) hle
      have h2 : 1 / ((rAt rs i j : ℝ) / 2 ^ s) = 2 ^ s / rAt rs i j := by
        rw [one_div, inv_div]
      rw [h2] at h1
      exact le_trans h1 (invUp_ge hr)
    have hE : energy (confOf pts N) ≤ ∑ i : Fin N, ∑ j : Fin N,
        ((cond (Nat.blt i j) (invUp s (rAt rs i j)) 0 : ℕ) : ℝ) / 2 ^ s := by
      unfold energy
      refine sum_le_sum fun i _ => ?_
      rw [sum_filter]
      refine sum_le_sum fun j _ => ?_
      by_cases hij : i < j
      · rw [if_pos hij]
        have hb : Nat.blt (i : ℕ) j = true := by
          rw [Nat.blt_eq]
          exact hij
        rw [hb]
        exact hterm i j hij
      · rw [if_neg hij]
        positivity
    have hS : (∑ i : Fin N, ∑ j : Fin N, ((cond (Nat.blt i j) (invUp s (rAt rs i j)) 0 : ℕ) : ℝ) / 2 ^ s)
        = ((sumN (fun i => sumN (fun j => cond (Nat.blt i j) (invUp s (rAt rs i j)) 0) N) N : ℕ) : ℝ) / 2 ^ s := by
      rw [sumN_eq, Nat.cast_sum, sum_div,
        ← Fin.sum_univ_eq_sum_range (fun i => ((sumN (fun j => cond (Nat.blt i j) (invUp s (rAt rs i j)) 0) N : ℕ) : ℝ) / 2 ^ s)]
      refine sum_congr rfl fun i _ => ?_
      rw [sumN_eq, Nat.cast_sum, sum_div,
        ← Fin.sum_univ_eq_sum_range (fun j => ((cond (Nat.blt (i : ℕ) j) (invUp s (rAt rs i j)) 0 : ℕ) : ℝ) / 2 ^ s)]
    rw [hS] at hE
    refine le_trans hE ?_
    rw [Nat.ble_eq] at hsum
    have hs' : sumN (fun i => sumN (fun j => cond (Nat.blt i j) (invUp s (rAt rs i j)) 0) N) N * tq ≤ tp * 2 ^ s := hsum
    have hsr : ((sumN (fun i => sumN (fun j => cond (Nat.blt i j) (invUp s (rAt rs i j)) 0) N) N : ℕ) : ℝ) * tq
        ≤ tp * 2 ^ s := by exact_mod_cast hs'
    have htq' : (0 : ℝ) < tq := by exact_mod_cast htq
    rw [div_le_div_iff₀ (by positivity) htq']
    exact hsr

end N11.Circ
