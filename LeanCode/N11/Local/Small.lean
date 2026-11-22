module

public import Mathlib.Tactic.LinearCombination
public import N11.Local.Tables

/-!
# G7 of route G: the coefficients, the residual, the sums, the norms

* `enc`: the coefficients enclose `w³`, `(3/2) w⁵`, `(5/2) w⁷` for the number `w > 0` with
  `w² (2 - 2 <p_i, p_j>) = 1`. (The tests compare squares: with `Q = 2^121 - 2 T` the number `2^60 w³` has the square
  `2^480 / Q³`, and the tests are `(A - E)² Q³ ≤ 2^480 ≤ (A + E)² Q³`.)
* `sym`: the coefficients are symmetric.
* `grad`: the residual of the first-order condition.
* `rows`: the sums of the coefficients over the pairs that contain a point.
* `norm`: `| |p_i|² - 1 | ≤ e / 2^120`; `top`: `<p_i, p_j> ≤ tmax / 2^120`.
-/

set_option exponentiation.threshold 100000

@[expose] public section

namespace N11.Local

open Finset CAP

/-! ## The enclosures -/

theorem le_of_sq_le_sq' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hlt
  have hlt' : b < a := not_le.mp hlt
  have h1 : 0 < (a - b) * (a + b) := mul_pos (sub_pos.mpr hlt') (by linarith)
  nlinarith

theorem encl {lo hi v Q : ℝ} (hQ : 0 < Q) (hv : 0 ≤ v) (hhi : 0 ≤ hi) (h1 : lo ^ 2 * Q ≤ v ^ 2 * Q)
    (h2 : v ^ 2 * Q ≤ hi ^ 2 * Q) : lo ≤ v ∧ v ≤ hi :=
  ⟨le_of_sq_le_sq' hv (le_of_mul_le_mul_right h1 hQ), le_of_sq_le_sq' hhi (le_of_mul_le_mul_right h2 hQ)⟩

theorem cast_sq_mul_le {lo Qn S : ℕ} (h : lo ^ 2 * Qn ≤ S) : (lo : ℝ) ^ 2 * (Qn : ℝ) ≤ (S : ℝ) := by
  have h1 : ((lo ^ 2 * Qn : ℕ) : ℝ) ≤ (S : ℝ) := Nat.cast_le.mpr h
  rw [Nat.cast_mul, Nat.cast_pow] at h1
  exact h1

theorem cast_le_sq_mul {hi Qn S : ℕ} (h : S ≤ hi ^ 2 * Qn) : (S : ℝ) ≤ (hi : ℝ) ^ 2 * (Qn : ℝ) := by
  have h1 : (S : ℝ) ≤ ((hi ^ 2 * Qn : ℕ) : ℝ) := Nat.cast_le.mpr h
  rw [Nat.cast_mul, Nat.cast_pow] at h1
  exact h1

/-- The tests of `encQ`, as inequalities between natural numbers. -/
theorem encQ_sound (A B C E q : ℕ) (h : encQ A B C E q = true) :
    E < A ∧ (A - E) ^ 2 * (q * (q * q)) ≤ Nat.shiftLeft 1 480
      ∧ Nat.shiftLeft 1 480 ≤ (A + E) ^ 2 * (q * (q * q))
      ∧ 3 * E < 2 * B ∧ (2 * B - 3 * E) ^ 2 * (q * (q * q) * (q * q)) ≤ Nat.shiftLeft 9 720
      ∧ Nat.shiftLeft 9 720 ≤ (2 * B + 3 * E) ^ 2 * (q * (q * q) * (q * q))
      ∧ 5 * E < 2 * C ∧ (2 * C - 5 * E) ^ 2 * (q * (q * q) * (q * q) * (q * q)) ≤ Nat.shiftLeft 25 960
      ∧ Nat.shiftLeft 25 960 ≤ (2 * C + 5 * E) ^ 2 * (q * (q * q) * (q * q) * (q * q)) := by
  unfold encQ at h
  simp only [forceN_eq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨Nat.blt_eq.mp h1, Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3, Nat.blt_eq.mp h4,
    Nat.le_of_ble_eq_true h5, Nat.le_of_ble_eq_true h6, Nat.blt_eq.mp h7, Nat.le_of_ble_eq_true h8,
    Nat.le_of_ble_eq_true h9⟩

/-- **The enclosures of a pair**, at the scale of the integers. -/
theorem enc_real (A B C E : ℕ) (T : ℕ × ℕ)
    (h : Prod.rec (motive := fun _ => Bool) (fun t1 t2 => encBody A B C E t1 t2) T = true) (w : ℝ) (hw : 0 < w)
    (hw2 : w ^ 2 * (2 ^ 121 - 2 * zr T) = 2 ^ 120) :
    |(A : ℝ) - 2 ^ 60 * w ^ 3| ≤ (E : ℝ) ∧ |2 * (B : ℝ) - 3 * (2 ^ 60 * w ^ 5)| ≤ 3 * (E : ℝ)
      ∧ |2 * (C : ℝ) - 5 * (2 ^ 60 * w ^ 7)| ≤ 5 * (E : ℝ) := by
  obtain ⟨t1, t2⟩ := T
  have h' : encBody A B C E t1 t2 = true := h
  unfold encBody at h'
  rw [Bool.and_eq_true, forceN_eq] at h'
  obtain ⟨h0, hq⟩ := h'
  have h0' : 2 * t1 < Nat.shiftLeft 1 121 + 2 * t2 := Nat.blt_eq.mp h0
  obtain ⟨q, hqd⟩ : ∃ q : ℕ, q = Nat.shiftLeft 1 121 + 2 * t2 - 2 * t1 := ⟨_, rfl⟩
  have hq' : encQ A B C E q = true := by
    rw [hqd]
    exact hq
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := encQ_sound A B C E q hq'
  have hQ : (q : ℝ) = 2 ^ 121 - 2 * zr (t1, t2) := by
    rw [hqd, Nat.cast_sub (le_of_lt h0'), Nat.cast_add, shl1_cast, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat,
      zr_pair]
    ring
  have hQpos : (0 : ℝ) < q := by
    have h1 : 0 < q := by
      rw [hqd]
      omega
    exact_mod_cast h1
  rw [← hQ] at hw2
  have c3 : ((q * (q * q) : ℕ) : ℝ) = (q : ℝ) ^ 3 := by
    simp only [Nat.cast_mul]
    ring
  have c5 : ((q * (q * q) * (q * q) : ℕ) : ℝ) = (q : ℝ) ^ 5 := by
    simp only [Nat.cast_mul]
    ring
  have c7 : ((q * (q * q) * (q * q) * (q * q) : ℕ) : ℝ) = (q : ℝ) ^ 7 := by
    simp only [Nat.cast_mul]
    ring
  have sA : ((A - E : ℕ) : ℝ) = (A : ℝ) - E := Nat.cast_sub (le_of_lt g1)
  have aA : ((A + E : ℕ) : ℝ) = (A : ℝ) + E := Nat.cast_add A E
  have sB : ((2 * B - 3 * E : ℕ) : ℝ) = 2 * (B : ℝ) - 3 * E := by
    rw [Nat.cast_sub (le_of_lt g4), Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
  have aB : ((2 * B + 3 * E : ℕ) : ℝ) = 2 * (B : ℝ) + 3 * E := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
  have sC : ((2 * C - 5 * E : ℕ) : ℝ) = 2 * (C : ℝ) - 5 * E := by
    rw [Nat.cast_sub (le_of_lt g7), Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
  have aC : ((2 * C + 5 * E : ℕ) : ℝ) = 2 * (C : ℝ) + 5 * E := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
  have r2 := cast_sq_mul_le g2
  have r3 := cast_le_sq_mul g3
  have r5 := cast_sq_mul_le g5
  have r6 := cast_le_sq_mul g6
  have r8 := cast_sq_mul_le g8
  have r9 := cast_le_sq_mul g9
  rw [sA, c3, shl_cast] at r2
  rw [aA, c3, shl_cast] at r3
  rw [sB, c5, shl_cast] at r5
  rw [aB, c5, shl_cast] at r6
  rw [sC, c7, shl_cast] at r8
  rw [aC, c7, shl_cast] at r9
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg E
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have vA : (2 ^ 60 * w ^ 3) ^ 2 * (q : ℝ) ^ 3 = ((1 : ℕ) : ℝ) * 2 ^ 480 := by
    have e : (2 ^ 60 * w ^ 3) ^ 2 * (q : ℝ) ^ 3 = 2 ^ 120 * (w ^ 2 * q) ^ 3 := by ring
    rw [e, hw2]
    norm_num
  have vB : (3 * (2 ^ 60 * w ^ 5)) ^ 2 * (q : ℝ) ^ 5 = ((9 : ℕ) : ℝ) * 2 ^ 720 := by
    have e : (3 * (2 ^ 60 * w ^ 5)) ^ 2 * (q : ℝ) ^ 5 = 9 * 2 ^ 120 * (w ^ 2 * q) ^ 5 := by ring
    rw [e, hw2]
    norm_num
  have vC : (5 * (2 ^ 60 * w ^ 7)) ^ 2 * (q : ℝ) ^ 7 = ((25 : ℕ) : ℝ) * 2 ^ 960 := by
    have e : (5 * (2 ^ 60 * w ^ 7)) ^ 2 * (q : ℝ) ^ 7 = 25 * 2 ^ 120 * (w ^ 2 * q) ^ 7 := by ring
    rw [e, hw2]
    norm_num
  rw [← vA] at r2 r3
  rw [← vB] at r5 r6
  rw [← vC] at r8 r9
  obtain ⟨a1, a2⟩ := encl (pow_pos hQpos 3) (by positivity) (by linarith) r2 r3
  obtain ⟨b1, b2⟩ := encl (pow_pos hQpos 5) (by positivity) (by linarith) r5 r6
  obtain ⟨c1, c2⟩ := encl (pow_pos hQpos 7) (by positivity) (by linarith) r8 r9
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- **The enclosures of the coefficients.** -/
theorem enc (D : Dat) (E : ℕ) (h : encOk D E = true) (i j : ℕ) (hij : i < j) (hj : j < 11) (w : ℝ) (hw : 0 < w)
    (hw2 : w ^ 2 * (2 - 2 * dot (rp D i) (rp D j)) = 1) :
    |ra D i j - w ^ 3| ≤ (E : ℝ) / 2 ^ 60 ∧ |rb D i j - 3 / 2 * w ^ 5| ≤ 3 / 2 * ((E : ℝ) / 2 ^ 60)
      ∧ |rc D i j - 5 / 2 * w ^ 7| ≤ 5 / 2 * ((E : ℝ) / 2 ^ 60) := by
  have h1 : ball (fun i => encPair D E i j) j = true := ball_sound h j hj
  have h2 : encPair D E i j = true := ball_sound h1 i hij
  have hw3 : w ^ 2 * (2 ^ 121 - 2 * zr (tI D i j)) = 2 ^ 120 := by
    rw [zr_tI, dot_Pz]
    linear_combination (2 ^ 120 : ℝ) * hw2
  obtain ⟨ha, hb, hc⟩ := enc_real (ga D i j) (gb D i j) (gc D i j) E (tI D i j) h2 w hw hw3
  rw [abs_le] at ha hb hc
  have eA : (ga D i j : ℝ) = 2 ^ 60 * ra D i j := Az_val D i j
  have eB : (gb D i j : ℝ) = 2 ^ 60 * rb D i j := Bz_val D i j
  have eC : (gc D i j : ℝ) = 2 ^ 60 * rc D i j := Cz_val D i j
  rw [eA] at ha
  rw [eB] at hb
  rw [eC] at hc
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]

/-! ## The symmetry -/

theorem sym (D : Dat) (h : symOk D = true) (i j : ℕ) (hij : i < j) (hj : j < 11) :
    ra D i j = ra D j i ∧ rb D i j = rb D j i ∧ rc D i j = rc D j i := by
  have h1 : ball (fun i => Nat.beq (ga D i j) (ga D j i) && Nat.beq (gb D i j) (gb D j i)
      && Nat.beq (gc D i j) (gc D j i)) j = true := ball_sound h j hj
  have h2 : (Nat.beq (ga D i j) (ga D j i) && Nat.beq (gb D i j) (gb D j i)
      && Nat.beq (gc D i j) (gc D j i)) = true := ball_sound h1 i hij
  rw [Bool.and_eq_true, Bool.and_eq_true] at h2
  unfold ra rb rc Az Bz Cz
  rw [Nat.eq_of_beq_eq_true h2.1.1, Nat.eq_of_beq_eq_true h2.1.2, Nat.eq_of_beq_eq_true h2.2]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The residual of the first-order condition -/

theorem zr_fI (D : Dat) (i c : ℕ) :
    zr (fI D i c) = ∑ j ∈ range 11, if j = i then 0 else Az D i j * Pz D j c := by
  unfold fI
  rw [zr_zsum]
  refine sum_congr rfl fun j _ => ?_
  rw [zr_ind_nbeq, zr_nat]
  rfl

theorem fI_val (D : Dat) (i c : ℕ) : zr (fI D i c) = 2 ^ 120 * frc (rp D) (ra D) i c := by
  unfold frc
  rw [zr_fI, Finset.mul_sum]
  refine sum_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · rw [if_pos hj, if_pos hj, mul_zero]
  · rw [if_neg hj, if_neg hj, Az_val, Pz_val]
    ring

theorem gI_val (D : Dat) (i c : ℕ) :
    zr (gI D i c) = 2 ^ 240 * (frc (rp D) (ra D) i c - dot (frc (rp D) (ra D) i) (rp D i) * rp D i c) := by
  unfold gI muI
  rw [zr_sub, zr_nat, zr_mul, zr_add, zr_add, zr_mul, zr_mul, zr_mul, shl1_cast, fI_val D i c, fI_val D i 0,
    fI_val D i 1, fI_val D i 2, dot_eq]
  show 2 ^ 120 * (2 ^ 120 * frc (rp D) (ra D) i c)
      - (2 ^ 120 * frc (rp D) (ra D) i 0 * Pz D i 0 + 2 ^ 120 * frc (rp D) (ra D) i 1 * Pz D i 1
        + 2 ^ 120 * frc (rp D) (ra D) i 2 * Pz D i 2) * Pz D i c = _
  rw [Pz_val D i 0, Pz_val D i 1, Pz_val D i 2, Pz_val D i c]
  ring

/-- **The residual of the first-order condition.** -/
theorem grad (D : Dat) (Gam : ℕ) (h : gradOk D Gam = true) :
    ∑ i ∈ range 11, ∑ k ∈ range 3, (frc (rp D) (ra D) i k - dot (frc (rp D) (ra D) i) (rp D i) * rp D i k) ^ 2
      ≤ ((Gam : ℝ) / 2 ^ 240) ^ 2 := by
  have h1 : zr (zsum (fun i => zsum (fun c => zmul (gI D i c) (gI D i c)) 3) 11) ≤ zr (Nat.mul Gam Gam, 0) :=
    zle_sound h
  have e1 : zr (zsum (fun i => zsum (fun c => zmul (gI D i c) (gI D i c)) 3) 11)
      = 2 ^ 480 * ∑ i ∈ range 11, ∑ k ∈ range 3,
        (frc (rp D) (ra D) i k - dot (frc (rp D) (ra D) i) (rp D i) * rp D i k) ^ 2 := by
    rw [zr_zsum, Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [zr_zsum, Finset.mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [zr_mul, gI_val]
    ring
  have e2 : zr (Nat.mul Gam Gam, 0) = (Gam : ℝ) ^ 2 := by
    rw [zr_pair, Nat.cast_zero, sub_zero]
    show ((Gam * Gam : ℕ) : ℝ) = _
    rw [Nat.cast_mul]
    ring
  rw [e1, e2] at h1
  have e3 : ((Gam : ℝ) / 2 ^ 240) ^ 2 = (Gam : ℝ) ^ 2 / 2 ^ 480 := by ring
  rw [e3, le_div_iff₀ (by positivity)]
  linarith

/-! ## The sums of the coefficients -/

theorem rowS_le (g : ℕ → ℕ → ℕ) (i R : ℕ)
    (h : Nat.ble (nsum (fun j => cond (Nat.beq j i) 0 (g i j)) 11) R = true) :
    rowS (fun i j => (g i j : ℝ) / 2 ^ 60) i ≤ (R : ℝ) / 2 ^ 60 := by
  have h1 := Nat.le_of_ble_eq_true h
  rw [nsum_eq] at h1
  have h2 : ((∑ j ∈ range 11, cond (Nat.beq j i) 0 (g i j) : ℕ) : ℝ) ≤ (R : ℝ) := Nat.cast_le.mpr h1
  rw [Nat.cast_sum] at h2
  have e : rowS (fun i j => (g i j : ℝ) / 2 ^ 60) i
      = (∑ j ∈ range 11, ((cond (Nat.beq j i) 0 (g i j) : ℕ) : ℝ)) / 2 ^ 60 := by
    unfold rowS
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · rw [if_pos hj, (beq_iff j i).mpr hj]
      show (0 : ℝ) = ((0 : ℕ) : ℝ) * (2 ^ 60)⁻¹
      rw [Nat.cast_zero, zero_mul]
    · rw [if_neg hj, beq_false_of_ne hj]
      exact div_eq_mul_inv _ _
  rw [e]
  have h3 : (0 : ℝ) < 2 ^ 60 := by positivity
  exact div_le_div_of_nonneg_right h2 (le_of_lt h3)

/-- **The sums of the coefficients** over the pairs that contain a point. -/
theorem rows (D : Dat) (Ra Rb Rc : ℕ) (h : rowsOk D Ra Rb Rc = true) (i : ℕ) (hi : i < 11) :
    rowS (ra D) i ≤ (Ra : ℝ) / 2 ^ 60 ∧ rowS (rb D) i ≤ (Rb : ℝ) / 2 ^ 60 ∧ rowS (rc D) i ≤ (Rc : ℝ) / 2 ^ 60 := by
  have h1 : (Nat.ble (nsum (fun j => cond (Nat.beq j i) 0 (ga D i j)) 11) Ra
      && Nat.ble (nsum (fun j => cond (Nat.beq j i) 0 (gb D i j)) 11) Rb
      && Nat.ble (nsum (fun j => cond (Nat.beq j i) 0 (gc D i j)) 11) Rc) = true := ball_sound h i hi
  rw [Bool.and_eq_true, Bool.and_eq_true] at h1
  exact ⟨rowS_le (ga D) i Ra h1.1.1, rowS_le (gb D) i Rb h1.1.2, rowS_le (gc D) i Rc h1.2⟩

/-! ## The norms and the inner products -/

/-- **The points of the reference configuration are close to the sphere.** -/
theorem norm (D : Dat) (e : ℕ) (h : normOk D e = true) (i : ℕ) (hi : i < 11) :
    |dot (rp D i) (rp D i) - 1| ≤ (e : ℝ) / 2 ^ 120 := by
  have h1 : (zle (tI D i i) (Nat.add (Nat.shiftLeft 1 120) e, 0)
      && zle (Nat.shiftLeft 1 120, e) (tI D i i)) = true := ball_sound h i hi
  rw [Bool.and_eq_true] at h1
  have h2 := zle_sound h1.1
  have h3 := zle_sound h1.2
  have e1 : ((Nat.add (Nat.shiftLeft 1 120) e : ℕ) : ℝ) = 2 ^ 120 + (e : ℝ) := by
    show ((Nat.shiftLeft 1 120 + e : ℕ) : ℝ) = _
    rw [Nat.cast_add, shl1_cast]
  rw [zr_tI, dot_Pz, zr_pair (Nat.add (Nat.shiftLeft 1 120) e) 0, e1, Nat.cast_zero, sub_zero] at h2
  rw [zr_tI, dot_Pz, zr_pair (Nat.shiftLeft 1 120) e, shl1_cast] at h3
  have h4 : (0 : ℝ) < 2 ^ 120 := by positivity
  rw [abs_le]
  constructor
  · rw [neg_le, neg_sub, sub_le_iff_le_add, div_add' _ _ _ (ne_of_gt h4), le_div_iff₀ h4]
    linarith
  · rw [sub_le_iff_le_add, div_add' _ _ _ (ne_of_gt h4), le_div_iff₀ h4]
    linarith

/-- **The inner products of the reference configuration stay away from one.** -/
theorem top (D : Dat) (tmax : ℕ) (h : topOk D tmax = true) (i j : ℕ) (hij : i < j) (hj : j < 11) :
    dot (rp D i) (rp D j) ≤ (tmax : ℝ) / 2 ^ 120 := by
  have h1 : ball (fun i => zle (tI D i j) (tmax, 0)) j = true := ball_sound h j hj
  have h2 : zle (tI D i j) (tmax, 0) = true := ball_sound h1 i hij
  have h3 := zle_sound h2
  rw [zr_tI, dot_Pz, zr_pair tmax 0, Nat.cast_zero, sub_zero] at h3
  have h4 : (0 : ℝ) < 2 ^ 120 := by positivity
  rw [le_div_iff₀ h4]
  linarith

end N11.Local
