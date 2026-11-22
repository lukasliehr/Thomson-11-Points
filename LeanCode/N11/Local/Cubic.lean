module

public import N11.Local.Quad

/-!
# G7 of route G: the cubic form

The table `T6` is six times the symmetric tensor of the cubic form `∑_{i<j} c L³ + 2 b L psi + a rho`, with the
projections `1 - p_i p_iᵀ` in its linear forms. For a displacement `x` with `<p_i, x_i> = 0` its form is six times
the cubic form (`form_T6`). The square of a cubic form is at most the quadratic form of the Gram matrix `W` of its
flattening times `|x|⁴` (`flatten`), and the checker of E2 accepts `c3s - W` (`cubOk`, `wEntOk`). So
`Cub(x)² ≤ c3² |x|⁶` (`cub`).
-/

set_option exponentiation.threshold 100000

@[expose] public section

namespace N11.Local

open Finset CAP

/-! ## The entries of the tables -/

theorem zr_Mb (D : Dat) (T : ℕ × ℕ) (i j u c : ℕ) :
    zr (Mb D T i j u c) = dl u i * (2 ^ 120 * Pz D j c - zr T * Pz D i c) := by
  unfold Mb
  rw [zr_ind_beq, zr_sub, zr_nat, zr_mul, shl1_cast]
  rfl

theorem zr_Lb (D : Dat) (T : ℕ × ℕ) (i j u c : ℕ) :
    zr (Lb D T i j u c) = zr (Mb D T i j u c) + zr (Mb D T j i u c) := by
  unfold Lb
  rw [zr_add]

theorem zr_Gt (D : Dat) (i u c u' c' : ℕ) :
    zr (Gt D i u c u' c') = dl u i * dl u' i * (dl c c' * 2 ^ 120 - Pz D i c * Pz D i c') := by
  unfold Gt
  rw [zr_ind_beq2, zr_sub, zr_ind_beq, zr_mul, zr_shl1]
  rfl

theorem zr_Ht (D : Dat) (T : ℕ × ℕ) (i j u c u' c' : ℕ) :
    zr (Ht D T i j u c u' c')
      = dl u i * dl u' j * (dl c c' * 2 ^ 240 - 2 ^ 120 * (Pz D i c * Pz D i c' + Pz D j c * Pz D j c')
          + zr T * (Pz D i c * Pz D j c')) := by
  unfold Ht
  rw [zr_ind_beq2, zr_add, zr_sub, zr_ind_beq, zr_nat, zr_add, zr_mul, zr_mul, zr_mul, zr_mul, zr_shl1, shl1_cast]
  rfl

theorem zr_psib2 (D : Dat) (T : ℕ × ℕ) (i j u c u' c' : ℕ) :
    zr (psib2 D T i j u c u' c')
      = 2 * zr (Ht D T i j u c u' c') - zr T * (zr (Gt D i u c u' c') + zr (Gt D j u c u' c')) := by
  unfold psib2
  rw [zr_sub, zr_nat, zr_mul, zr_add, Nat.cast_ofNat]

theorem zr_Rraw (D : Dat) (T : ℕ × ℕ) (i j k a b : ℕ) :
    zr (Rraw D T i j k a b)
      = Cz D i j * (zr (Lb D T i j (pt k) (co k))
          * (zr (Lb D T i j (pt a) (co a)) * zr (Lb D T i j (pt b) (co b))))
        + 2 ^ 120 * Bz D i j * (zr (Lb D T i j (pt k) (co k)) * zr (psib2 D T i j (pt a) (co a) (pt b) (co b)))
        - 2 ^ 239 * Az D i j * (zr (Mb D T i j (pt k) (co k)) * zr (Gt D j (pt a) (co a) (pt b) (co b))
            + zr (Mb D T j i (pt k) (co k)) * zr (Gt D i (pt a) (co a) (pt b) (co b))) := by
  unfold Rraw
  rw [zr_sub, zr_add, zr_nat, zr_nat, zr_nat, zr_add, zr_mul, zr_mul, zr_mul, zr_mul, zr_mul, cast_shl_mul,
    cast_shl_mul]
  rfl

theorem zr_R6 (D : Dat) (T : ℕ × ℕ) (i j k a b : ℕ) :
    zr (R6 D T i j k a b)
      = zr (Rraw D T i j k a b) + zr (Rraw D T i j k b a) + zr (Rraw D T i j a k b)
        + zr (Rraw D T i j a b k) + zr (Rraw D T i j b k a) + zr (Rraw D T i j b a k) := by
  unfold R6
  rw [zr_add, zr_add, zr_add, zr_add, zr_add]
  ring

/-! ## The support of the table of a pair -/

theorem zr_Mb_ne (D : Dat) (T : ℕ × ℕ) (i j u c : ℕ) (h : u ≠ i) : zr (Mb D T i j u c) = 0 := by
  rw [zr_Mb, dl_ne h, zero_mul]

theorem zr_Lb_out (D : Dat) (T : ℕ × ℕ) (i j u c : ℕ) (h : ¬ (u = i ∨ u = j)) : zr (Lb D T i j u c) = 0 := by
  rw [zr_Lb, zr_Mb_ne D T i j u c (fun e => h (Or.inl e)), zr_Mb_ne D T j i u c (fun e => h (Or.inr e)), add_zero]

theorem zr_Gt_left (D : Dat) (i u c u' c' : ℕ) (h : u ≠ i) : zr (Gt D i u c u' c') = 0 := by
  rw [zr_Gt, dl_ne h, zero_mul, zero_mul]

theorem zr_Gt_right (D : Dat) (i u c u' c' : ℕ) (h : u' ≠ i) : zr (Gt D i u c u' c') = 0 := by
  rw [zr_Gt, dl_ne h, mul_zero, zero_mul]

theorem zr_Ht_left (D : Dat) (T : ℕ × ℕ) (i j u c u' c' : ℕ) (h : u ≠ i) : zr (Ht D T i j u c u' c') = 0 := by
  rw [zr_Ht, dl_ne h, zero_mul, zero_mul]

theorem zr_Ht_right (D : Dat) (T : ℕ × ℕ) (i j u c u' c' : ℕ) (h : u' ≠ j) : zr (Ht D T i j u c u' c') = 0 := by
  rw [zr_Ht, dl_ne h, mul_zero, zero_mul]

theorem zr_psib2_left (D : Dat) (T : ℕ × ℕ) (i j u c u' c' : ℕ) (h : ¬ (u = i ∨ u = j)) :
    zr (psib2 D T i j u c u' c') = 0 := by
  rw [zr_psib2, zr_Ht_left D T i j u c u' c' (fun e => h (Or.inl e)),
    zr_Gt_left D i u c u' c' (fun e => h (Or.inl e)), zr_Gt_left D j u c u' c' (fun e => h (Or.inr e))]
  ring

theorem zr_psib2_right (D : Dat) (T : ℕ × ℕ) (i j u c u' c' : ℕ) (h : ¬ (u' = i ∨ u' = j)) :
    zr (psib2 D T i j u c u' c') = 0 := by
  rw [zr_psib2, zr_Ht_right D T i j u c u' c' (fun e => h (Or.inr e)),
    zr_Gt_right D i u c u' c' (fun e => h (Or.inl e)), zr_Gt_right D j u c u' c' (fun e => h (Or.inr e))]
  ring

/-- The table of a pair vanishes if the point of one of its indices is not a point of the pair. -/
theorem zr_Rraw_zero (D : Dat) (T : ℕ × ℕ) (i j k a b : ℕ)
    (h : ¬ ((pt k = i ∨ pt k = j) ∧ (pt a = i ∨ pt a = j) ∧ (pt b = i ∨ pt b = j))) :
    zr (Rraw D T i j k a b) = 0 := by
  rw [zr_Rraw]
  by_cases hk : pt k = i ∨ pt k = j
  · by_cases ha : pt a = i ∨ pt a = j
    · have hb : ¬ (pt b = i ∨ pt b = j) := fun hb => h ⟨hk, ha, hb⟩
      rw [zr_Lb_out D T i j (pt b) (co b) hb, zr_psib2_right D T i j (pt a) (co a) (pt b) (co b) hb,
        zr_Gt_right D j (pt a) (co a) (pt b) (co b) (fun e => hb (Or.inr e)),
        zr_Gt_right D i (pt a) (co a) (pt b) (co b) (fun e => hb (Or.inl e))]
      ring
    · rw [zr_Lb_out D T i j (pt a) (co a) ha, zr_psib2_left D T i j (pt a) (co a) (pt b) (co b) ha,
        zr_Gt_left D j (pt a) (co a) (pt b) (co b) (fun e => ha (Or.inr e)),
        zr_Gt_left D i (pt a) (co a) (pt b) (co b) (fun e => ha (Or.inl e))]
      ring
  · rw [zr_Lb_out D T i j (pt k) (co k) hk, zr_Mb_ne D T i j (pt k) (co k) (fun e => hk (Or.inl e)),
      zr_Mb_ne D T j i (pt k) (co k) (fun e => hk (Or.inr e))]
    ring

theorem inP_iff (i j u : ℕ) : inP i j u = true ↔ (u = i ∨ u = j) := by
  unfold inP
  rw [Bool.or_eq_true, beq_iff, beq_iff]

theorem zr_T6term (D : Dat) (i j k a b : ℕ) :
    zr (ind (inP i j (pt k) && inP i j (pt a) && inP i j (pt b))
        (Prod.rec (motive := fun _ => ℕ × ℕ) (fun t1 t2 => R6 D (t1, t2) i j k a b) (tI D i j)))
      = zr (Rraw D (tI D i j) i j k a b) + zr (Rraw D (tI D i j) i j k b a) + zr (Rraw D (tI D i j) i j a k b)
        + zr (Rraw D (tI D i j) i j a b k) + zr (Rraw D (tI D i j) i j b k a)
        + zr (Rraw D (tI D i j) i j b a k) := by
  rw [prod_rec_eta (fun T => R6 D T i j k a b), zr_ind, zr_R6]
  by_cases h : (inP i j (pt k) && inP i j (pt a) && inP i j (pt b)) = true
  · rw [if_pos h]
  · rw [if_neg h]
    have h' : ¬ ((pt k = i ∨ pt k = j) ∧ (pt a = i ∨ pt a = j) ∧ (pt b = i ∨ pt b = j)) := by
      intro hh
      apply h
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨(inP_iff i j _).mpr hh.1, (inP_iff i j _).mpr hh.2.1⟩, (inP_iff i j _).mpr hh.2.2⟩
    rw [zr_Rraw_zero D _ i j k a b h', zr_Rraw_zero D _ i j k b a (fun hh => h' ⟨hh.1, hh.2.2, hh.2.1⟩),
      zr_Rraw_zero D _ i j a k b (fun hh => h' ⟨hh.2.1, hh.1, hh.2.2⟩),
      zr_Rraw_zero D _ i j a b k (fun hh => h' ⟨hh.2.2, hh.1, hh.2.1⟩),
      zr_Rraw_zero D _ i j b k a (fun hh => h' ⟨hh.2.1, hh.2.2, hh.1⟩),
      zr_Rraw_zero D _ i j b a k (fun hh => h' ⟨hh.2.2, hh.2.1, hh.1⟩)]
    ring

theorem zr_T6 (D : Dat) (k a b : ℕ) :
    zr (T6 D k a b) = ∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then
      zr (Rraw D (tI D i j) i j k a b) + zr (Rraw D (tI D i j) i j k b a) + zr (Rraw D (tI D i j) i j a k b)
        + zr (Rraw D (tI D i j) i j a b k) + zr (Rraw D (tI D i j) i j b k a)
        + zr (Rraw D (tI D i j) i j b a k)
      else 0 := by
  unfold T6
  rw [zr_zsumP]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases hij : i < j
  · rw [if_pos hij, if_pos hij]
    exact zr_T6term D i j k a b
  · rw [if_neg hij, if_neg hij]

/-! ## The forms of the tables, for a tangential displacement -/

theorem form_Mb (D : Dat) (T : ℕ × ℕ) (x : ℕ → ℕ → ℝ) (i j : ℕ) (hi : i < 11) :
    ∑ k ∈ range 33, zr (Mb D T i j (pt k) (co k)) * flat x k
      = 2 ^ 120 * dot (Pz D j) (x i) - zr T * dot (Pz D i) (x i) := by
  have e : ∀ k, zr (Mb D T i j (pt k) (co k)) * flat x k
      = dl (pt k) i * (2 ^ 120 * Pz D j (co k) - zr T * Pz D i (co k)) * flat x k := by
    intro k
    rw [zr_Mb]
  rw [sum_congr rfl fun k _ => e k, sum_vec x i hi (fun c => 2 ^ 120 * Pz D j c - zr T * Pz D i c)]
  unfold dot
  rw [Finset.mul_sum, Finset.mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun c _ => by ring

theorem form_Lb (D : Dat) (T : ℕ × ℕ) (x : ℕ → ℕ → ℝ) (i j : ℕ) (hi : i < 11) (hj : j < 11)
    (hti : dot (Pz D i) (x i) = 0) (htj : dot (Pz D j) (x j) = 0) :
    ∑ k ∈ range 33, zr (Lb D T i j (pt k) (co k)) * flat x k
      = 2 ^ 120 * (dot (Pz D j) (x i) + dot (Pz D i) (x j)) := by
  have e : ∀ k, zr (Lb D T i j (pt k) (co k)) * flat x k
      = zr (Mb D T i j (pt k) (co k)) * flat x k + zr (Mb D T j i (pt k) (co k)) * flat x k := by
    intro k
    rw [zr_Lb]
    ring
  rw [sum_congr rfl fun k _ => e k, sum_add_distrib, form_Mb D T x i j hi, form_Mb D T x j i hj, hti, htj]
  ring

theorem form_Gt (D : Dat) (x : ℕ → ℕ → ℝ) (i : ℕ) (hi : i < 11) :
    ∑ a ∈ range 33, ∑ b ∈ range 33, zr (Gt D i (pt a) (co a) (pt b) (co b)) * (flat x a * flat x b)
      = 2 ^ 120 * dot (x i) (x i) - dot (Pz D i) (x i) * dot (Pz D i) (x i) := by
  have e : ∀ a b, zr (Gt D i (pt a) (co a) (pt b) (co b)) * (flat x a * flat x b)
      = dl (pt a) i * dl (pt b) i * (dl (co a) (co b) * 2 ^ 120) * (flat x a * flat x b)
        - dl (pt a) i * dl (pt b) i * (Pz D i (co a) * Pz D i (co b)) * (flat x a * flat x b) := by
    intro a b
    rw [zr_Gt]
    ring
  rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => e a b, sum2_sub,
    sum_block x x i i hi hi (fun c c' => dl c c' * 2 ^ 120),
    sum_block x x i i hi hi (fun c c' => Pz D i c * Pz D i c'), sum_dlc, sum_rank1]

theorem form_Ht (D : Dat) (T : ℕ × ℕ) (x : ℕ → ℕ → ℝ) (i j : ℕ) (hi : i < 11) (hj : j < 11) :
    ∑ a ∈ range 33, ∑ b ∈ range 33, zr (Ht D T i j (pt a) (co a) (pt b) (co b)) * (flat x a * flat x b)
      = 2 ^ 240 * dot (x i) (x j)
        - 2 ^ 120 * (dot (Pz D i) (x i) * dot (Pz D i) (x j) + dot (Pz D j) (x i) * dot (Pz D j) (x j))
        + zr T * (dot (Pz D i) (x i) * dot (Pz D j) (x j)) := by
  have e : ∀ a b, zr (Ht D T i j (pt a) (co a) (pt b) (co b)) * (flat x a * flat x b)
      = dl (pt a) i * dl (pt b) j * (dl (co a) (co b) * 2 ^ 240) * (flat x a * flat x b)
        - 2 ^ 120 * (dl (pt a) i * dl (pt b) j * (Pz D i (co a) * Pz D i (co b)) * (flat x a * flat x b)
            + dl (pt a) i * dl (pt b) j * (Pz D j (co a) * Pz D j (co b)) * (flat x a * flat x b))
        + zr T * (dl (pt a) i * dl (pt b) j * (Pz D i (co a) * Pz D j (co b)) * (flat x a * flat x b)) := by
    intro a b
    rw [zr_Ht]
    ring
  rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => e a b, sum2_add, sum2_sub, sum2_mul, sum2_add, sum2_mul,
    sum_block x x i j hi hj (fun c c' => dl c c' * 2 ^ 240),
    sum_block x x i j hi hj (fun c c' => Pz D i c * Pz D i c'),
    sum_block x x i j hi hj (fun c c' => Pz D j c * Pz D j c'),
    sum_block x x i j hi hj (fun c c' => Pz D i c * Pz D j c'), sum_dlc, sum_rank1, sum_rank1, sum_rank1]

theorem form_psib2 (D : Dat) (T : ℕ × ℕ) (x : ℕ → ℕ → ℝ) (i j : ℕ) (hi : i < 11) (hj : j < 11)
    (hti : dot (Pz D i) (x i) = 0) (htj : dot (Pz D j) (x j) = 0) :
    ∑ a ∈ range 33, ∑ b ∈ range 33, zr (psib2 D T i j (pt a) (co a) (pt b) (co b)) * (flat x a * flat x b)
      = 2 ^ 241 * dot (x i) (x j) - zr T * (2 ^ 120 * (dot (x i) (x i) + dot (x j) (x j))) := by
  have e : ∀ a b, zr (psib2 D T i j (pt a) (co a) (pt b) (co b)) * (flat x a * flat x b)
      = 2 * (zr (Ht D T i j (pt a) (co a) (pt b) (co b)) * (flat x a * flat x b))
        - zr T * (zr (Gt D i (pt a) (co a) (pt b) (co b)) * (flat x a * flat x b)
          + zr (Gt D j (pt a) (co a) (pt b) (co b)) * (flat x a * flat x b)) := by
    intro a b
    rw [zr_psib2]
    ring
  rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => e a b, sum2_sub, sum2_mul, sum2_mul, sum2_add,
    form_Ht D T x i j hi hj, form_Gt D x i hi, form_Gt D x j hj, hti, htj]
  ring

/-- The cubic form of a pair at the scale of the integers, for a tangential displacement. -/
noncomputable def rawF (D : Dat) (x : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  Cz D i j * (2 ^ 120 * Lf (Pz D) x i j) ^ 3
    + 2 ^ 120 * Bz D i j * (2 ^ 120 * Lf (Pz D) x i j
        * (2 ^ 241 * dot (x i) (x j) - dot (Pz D i) (Pz D j) * (2 ^ 120 * (dot (x i) (x i) + dot (x j) (x j)))))
    - 2 ^ 239 * Az D i j * (2 ^ 120 * dot (Pz D j) (x i) * (2 ^ 120 * dot (x j) (x j))
        + 2 ^ 120 * dot (Pz D i) (x j) * (2 ^ 120 * dot (x i) (x i)))

theorem form_Rraw (D : Dat) (x : ℕ → ℕ → ℝ) (i j : ℕ) (hi : i < 11) (hj : j < 11)
    (hti : dot (Pz D i) (x i) = 0) (htj : dot (Pz D j) (x j) = 0) :
    ∑ k ∈ range 33, ∑ a ∈ range 33, ∑ b ∈ range 33,
        zr (Rraw D (tI D i j) i j k a b) * flat x k * flat x a * flat x b = rawF D x i j := by
  have e : ∀ k a b, zr (Rraw D (tI D i j) i j k a b) * flat x k * flat x a * flat x b
      = Cz D i j * (zr (Lb D (tI D i j) i j (pt k) (co k)) * zr (Lb D (tI D i j) i j (pt a) (co a))
            * zr (Lb D (tI D i j) i j (pt b) (co b)) * flat x k * flat x a * flat x b)
        + (2 ^ 120 * Bz D i j * (zr (Lb D (tI D i j) i j (pt k) (co k))
              * zr (psib2 D (tI D i j) i j (pt a) (co a) (pt b) (co b)) * flat x k * flat x a * flat x b)
          - 2 ^ 239 * Az D i j * (zr (Mb D (tI D i j) i j (pt k) (co k))
                * zr (Gt D j (pt a) (co a) (pt b) (co b)) * flat x k * flat x a * flat x b
              + zr (Mb D (tI D i j) j i (pt k) (co k))
                * zr (Gt D i (pt a) (co a) (pt b) (co b)) * flat x k * flat x a * flat x b)) := by
    intro k a b
    rw [zr_Rraw]
    ring
  rw [sum_congr rfl fun k _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => e k a b,
    sum3_add, sum3_sub, sum3_mul, sum3_mul, sum3_mul, sum3_add,
    sum_mul3 33 (fun k => zr (Lb D (tI D i j) i j (pt k) (co k))) (fun a => zr (Lb D (tI D i j) i j (pt a) (co a)))
      (fun b => zr (Lb D (tI D i j) i j (pt b) (co b))) (flat x),
    sum_mul21 33 (fun k => zr (Lb D (tI D i j) i j (pt k) (co k))) (flat x)
      (fun a b => zr (psib2 D (tI D i j) i j (pt a) (co a) (pt b) (co b))),
    sum_mul21 33 (fun k => zr (Mb D (tI D i j) i j (pt k) (co k))) (flat x)
      (fun a b => zr (Gt D j (pt a) (co a) (pt b) (co b))),
    sum_mul21 33 (fun k => zr (Mb D (tI D i j) j i (pt k) (co k))) (flat x)
      (fun a b => zr (Gt D i (pt a) (co a) (pt b) (co b))),
    form_Lb D (tI D i j) x i j hi hj hti htj, form_psib2 D (tI D i j) x i j hi hj hti htj,
    form_Mb D (tI D i j) x i j hi, form_Mb D (tI D i j) x j i hj, form_Gt D x j hj, form_Gt D x i hi, hti, htj,
    zr_tI]
  unfold rawF Lf
  rw [dot_comm (x i) (Pz D j)]
  ring

/-- **The form of the table `T6`** is six times the cubic form, for a tangential displacement. -/
theorem form_T6 (D : Dat) (x : ℕ → ℕ → ℝ) (ht : ∀ i, i < 11 → dot (Pz D i) (x i) = 0) :
    ∑ k ∈ range 33, ∑ a ∈ range 33, ∑ b ∈ range 33, zr (T6 D k a b) * flat x k * flat x a * flat x b
      = 6 * sumP (rawF D x) := by
  have e : ∀ k a b, zr (T6 D k a b) * flat x k * flat x a * flat x b
      = (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then
          zr (Rraw D (tI D i j) i j k a b) + zr (Rraw D (tI D i j) i j k b a) + zr (Rraw D (tI D i j) i j a k b)
            + zr (Rraw D (tI D i j) i j a b k) + zr (Rraw D (tI D i j) i j b k a)
            + zr (Rraw D (tI D i j) i j b a k)
          else 0) * flat x k * flat x a * flat x b := by
    intro k a b
    rw [zr_T6]
  rw [sum_congr rfl fun k _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ => e k a b,
    sumP_cub 33 (fun i j k a b =>
      zr (Rraw D (tI D i j) i j k a b) + zr (Rraw D (tI D i j) i j k b a) + zr (Rraw D (tI D i j) i j a k b)
        + zr (Rraw D (tI D i j) i j a b k) + zr (Rraw D (tI D i j) i j b k a)
        + zr (Rraw D (tI D i j) i j b a k)) (flat x), ← sumP_mul]
  refine sumP_congr fun i j hij hj => ?_
  have hi : i < 11 := lt_trans hij hj
  show ∑ k ∈ range 33, ∑ a ∈ range 33, ∑ b ∈ range 33,
      (zr (Rraw D (tI D i j) i j k a b) + zr (Rraw D (tI D i j) i j k b a) + zr (Rraw D (tI D i j) i j a k b)
        + zr (Rraw D (tI D i j) i j a b k) + zr (Rraw D (tI D i j) i j b k a)
        + zr (Rraw D (tI D i j) i j b a k)) * flat x k * flat x a * flat x b
    = 6 * rawF D x i j
  rw [sum3_six 33 (fun k a b => zr (Rraw D (tI D i j) i j k a b)) (flat x),
    form_Rraw D x i j hi hj (ht i hi) (ht j hj)]

/-! ## The Gram matrix of the flattening -/

theorem toff_succ (k : ℕ) (hk : k < 33) : toff (k + 1) = toff k + (33 - k) := by
  interval_cases k <;> rfl

theorem toff_eq : ∀ k, k ≤ 33 → toff k = triOff 33 k
  | 0, _ => by
    rw [triOff_zero]
    rfl
  | k + 1, h => by
    rw [triOff_succ, ← toff_eq k (by omega), toff_succ k (by omega)]

theorem tab_entry (D : Dat) (off : ℕ) (tab : List (List (List ℕ)))
    (htab : ∀ a, a < 33 → tabOk D off (getLLN tab a) a = true) (a b k : ℕ) (ha : a < 33) (hb : b < 33)
    (hk : k < 33) : (getN (getLN (getLLN tab a) b) k : ℝ) - (off : ℝ) = zr (T6 D k a b) := by
  have h1 := ball_sound (htab a ha) b hb
  have h2 := ball_sound h1 k hk
  have h3 : zr (getN (getLN (getLLN tab a) b) k, off) = zr (T6 D k a b) := zeq_sound h2
  rw [zr_pair] at h3
  exact h3

theorem shape_sound (tab : List (List (List ℕ))) (h : shapeOk tab = true) (a : ℕ) (ha : a < 33) :
    (getLLN tab a).length = 33 ∧ ∀ b, b < 33 → (getLN (getLLN tab a) b).length = 33 := by
  have h1 : (Nat.beq (lenLN (getLLN tab a)) 33
      && ball (fun b => Nat.beq (lenN (getLN (getLLN tab a) b)) 33) 33) = true := ball_sound h a ha
  rw [Bool.and_eq_true] at h1
  refine ⟨?_, fun b hb => ?_⟩
  · rw [← lenLN_eq]
    exact Nat.eq_of_beq_eq_true h1.1
  · have h2 : Nat.beq (lenN (getLN (getLLN tab a) b)) 33 = true := ball_sound h1.2 b hb
    rw [← lenN_eq]
    exact Nat.eq_of_beq_eq_true h2

theorem zr_wEnt (D : Dat) (off : ℕ) (tab : List (List (List ℕ)))
    (htab : ∀ a, a < 33 → tabOk D off (getLLN tab a) a = true) (hsh : shapeOk tab = true) (a a' : ℕ)
    (ha : a < 33) (ha' : a' < 33) :
    zr (wEnt off tab a a') = ∑ b ∈ range 33, ∑ k ∈ range 33, zr (T6 D k a b) * zr (T6 D k a' b) := by
  obtain ⟨hl, hr⟩ := shape_sound tab hsh a ha
  obtain ⟨hl', hr'⟩ := shape_sound tab hsh a' ha'
  unfold wEnt
  rw [zr_dotB off _ _ (hl.trans hl'.symm), hl]
  refine sum_congr rfl fun b hb => ?_
  have hb' := mem_range.mp hb
  rw [zr_dotR off _ _ ((hr b hb').trans (hr' b hb').symm), hr b hb']
  refine sum_congr rfl fun k hk => ?_
  rw [tab_entry D off tab htab a b k ha hb' (mem_range.mp hk),
    tab_entry D off tab htab a' b k ha' hb' (mem_range.mp hk)]

/-- **The bound of the form of the table `T6`.** -/
theorem cub_int (D : Dat) (off c3s : ℕ) (tab : List (List (List ℕ))) (P : PSD.Params) (rows cols : ℕ)
    (htab : ∀ a, a < 33 → tabOk D off (getLLN tab a) a = true) (hc : cubOk tab P rows cols = true)
    (hw : ∀ k s, k < 33 → s < 33 - k → wEntOk off c3s tab P rows k s = true) (z : ℕ → ℝ) :
    (∑ k ∈ range 33, ∑ a ∈ range 33, ∑ b ∈ range 33, zr (T6 D k a b) * z k * z a * z b) ^ 2
      ≤ (c3s : ℝ) * (∑ k ∈ range 33, z k ^ 2) ^ 3 := by
  unfold cubOk at hc
  rw [Bool.and_eq_true, Bool.and_eq_true] at hc
  obtain ⟨⟨hn, hsh⟩, hchk⟩ := hc
  have hn' : P.n = 33 := Nat.eq_of_beq_eq_true hn
  obtain ⟨W, hW⟩ : ∃ W : ℕ → ℕ → ℝ, ∀ a a', W a a'
      = ∑ b ∈ range 33, ∑ k ∈ range 33, zr (T6 D k a b) * zr (T6 D k a' b) := ⟨_, fun _ _ => rfl⟩
  have hsym : ∀ a a', W a a' = W a' a := by
    intro a a'
    rw [hW, hW]
    exact sum_congr rfl fun b _ => sum_congr rfl fun k _ => mul_comm _ _
  have hg := N14.Local.gram_quad P rows cols hchk z
  rw [hn'] at hg
  have hE : ∀ k s, k < 33 → s < 33 - k →
      (PSD.dataEntry P rows k (k + s) : ℝ) = zr (wUpper off c3s tab k s) := by
    intro k s hk hs
    have h1 : zr (slot P.w rows (Nat.add (toff k) s), Nat.pow 2 (Nat.pred P.a))
        = zr (wUpper off c3s tab k s) := zeq_sound (hw k s hk hs)
    have e4 : triEnt P.w 33 rows k s = slot P.w rows (Nat.add (toff k) s) := by
      unfold triEnt
      rw [toff_eq k (le_of_lt hk)]
      rfl
    rw [dataEntry_cast P rows hn', Nat.add_sub_cancel_left, e4, ← h1, zr_pair, pow_pred_cast]
  have hd : ∀ i, i < 33 → (PSD.dataEntry P rows i i : ℝ) = dl i i * (c3s : ℝ) - W i i := by
    intro i hi
    have h2 := hE i 0 hi (by omega)
    rw [Nat.add_zero] at h2
    rw [h2]
    show zr (zsub (c3s, 0) (wEnt off tab i i)) = _
    rw [zr_sub, zr_pair c3s 0, Nat.cast_zero, sub_zero, zr_wEnt D off tab htab hsh i i hi hi, dl_self, one_mul, hW]
  have ho : ∀ i j, i < j → j < 33 → (PSD.dataEntry P rows i j : ℝ)
      = (dl i j * (c3s : ℝ) - W i j) + (dl j i * (c3s : ℝ) - W j i) := by
    intro i j hij hj
    obtain ⟨s, rfl⟩ : ∃ s, j = i + (s + 1) := ⟨j - i - 1, by omega⟩
    rw [hE i (s + 1) (by omega) (by omega)]
    show zr (znat 2 (zneg (wEnt off tab i (i + (s + 1))))) = _
    rw [zr_nat, zr_neg, zr_wEnt D off tab htab hsh i (i + (s + 1)) (by omega) hj, dl_ne (by omega),
      dl_ne (by omega), hsym (i + (s + 1)) i, hW, Nat.cast_ofNat]
    ring
  have hq : 0 ≤ ∑ k ∈ range 33, ∑ l ∈ range 33, (dl k l * (c3s : ℝ) - W k l) * (z k * z l) :=
    le_of_le_of_eq hg (tri_full 33 (fun k l => dl k l * (c3s : ℝ) - W k l)
      (fun i j => (PSD.dataEntry P rows i j : ℝ)) z hd ho)
  have hq2 : ∑ k ∈ range 33, ∑ l ∈ range 33, (dl k l * (c3s : ℝ) - W k l) * (z k * z l)
      = (c3s : ℝ) * ∑ k ∈ range 33, z k ^ 2 - ∑ k ∈ range 33, ∑ l ∈ range 33, W k l * (z k * z l) := by
    have e : ∀ k l, (dl k l * (c3s : ℝ) - W k l) * (z k * z l)
        = dl k l * ((c3s : ℝ) * (z k * z l)) - W k l * (z k * z l) := fun k l => by ring
    rw [sum_congr rfl fun k _ => sum_congr rfl fun l _ => e k l, sum2_sub, Finset.mul_sum]
    refine congrArg₂ (· - ·) (sum_congr rfl fun k hk => ?_) rfl
    rw [sum_dl' 33 k (mem_range.mp hk) (fun l => (c3s : ℝ) * (z k * z l))]
    ring
  have hf : (∑ k ∈ range 33, ∑ a ∈ range 33, ∑ b ∈ range 33, zr (T6 D k a b) * z k * z a * z b) ^ 2
      ≤ (∑ a ∈ range 33, ∑ a' ∈ range 33, W a a' * (z a * z a')) * (∑ k ∈ range 33, z k ^ 2) ^ 2 := by
    have e : ∑ a ∈ range 33, ∑ a' ∈ range 33, W a a' * (z a * z a')
        = ∑ a ∈ range 33, ∑ a' ∈ range 33,
          (∑ b ∈ range 33, ∑ k ∈ range 33, zr (T6 D k a b) * zr (T6 D k a' b)) * (z a * z a') :=
      sum_congr rfl fun a _ => sum_congr rfl fun a' _ => by rw [hW]
    rw [e]
    exact flatten 33 (fun k a b => zr (T6 D k a b)) z
  rw [hq2] at hq
  have h1 : ∑ a ∈ range 33, ∑ a' ∈ range 33, W a a' * (z a * z a') ≤ (c3s : ℝ) * ∑ k ∈ range 33, z k ^ 2 := by
    linarith
  calc (∑ k ∈ range 33, ∑ a ∈ range 33, ∑ b ∈ range 33, zr (T6 D k a b) * z k * z a * z b) ^ 2
      ≤ (∑ a ∈ range 33, ∑ a' ∈ range 33, W a a' * (z a * z a')) * (∑ k ∈ range 33, z k ^ 2) ^ 2 := hf
    _ ≤ ((c3s : ℝ) * ∑ k ∈ range 33, z k ^ 2) * (∑ k ∈ range 33, z k ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = (c3s : ℝ) * (∑ k ∈ range 33, z k ^ 2) ^ 3 := by ring

/-! ## The cubic form -/

theorem rawF_eq (D : Dat) (x : ℕ → ℕ → ℝ) (i j : ℕ) :
    rawF D x i j = 2 ^ 600 * (rc D i j * Lf (rp D) x i j ^ 3
      + 2 * rb D i j * (Lf (rp D) x i j * psif (rp D) x i j) + ra D i j * rhof (rp D) x i j) := by
  unfold rawF
  rw [Az_val, Bz_val, Cz_val, Lf_Pz, dot_Pz, dot_Pz_left D j (x i), dot_Pz_left D i (x j)]
  unfold psif rhof
  rw [dot_comm (x i) (rp D j)]
  ring

/-- **The cubic form**: `Cub(x)² ≤ c3² |x|⁶` with `c3 = n / d`, for the displacements with `<p_i, x_i> = 0`. -/
theorem cub (D : Dat) (off c3s : ℕ) (tab : List (List (List ℕ))) (P : PSD.Params) (rows cols : ℕ)
    (htab : ∀ a, a < 33 → tabOk D off (getLLN tab a) a = true) (hc : cubOk tab P rows cols = true)
    (hw : ∀ k s, k < 33 → s < 33 - k → wEntOk off c3s tab P rows k s = true)
    (n d : ℕ) (hd : 0 < d) (hcs : c3s * d ^ 2 = 36 * n ^ 2 * 2 ^ 1200) (x : ℕ → ℕ → ℝ)
    (ht : ∀ i, i < 11 → dot (rp D i) (x i) = 0) :
    Cf (rp D) (ra D) (rb D) (rc D) x ^ 2 ≤ ((n : ℝ) / d) ^ 2 * nsq x ^ 3 := by
  have ht' : ∀ i, i < 11 → dot (Pz D i) (x i) = 0 := by
    intro i hi
    rw [dot_Pz_left, ht i hi, mul_zero]
  have h0 := cub_int D off c3s tab P rows cols htab hc hw (flat x)
  have e1 : sumP (rawF D x) = 2 ^ 600 * Cf (rp D) (ra D) (rb D) (rc D) x := by
    unfold Cf
    rw [← sumP_mul]
    exact sumP_congr fun i j _ _ => rawF_eq D x i j
  rw [form_T6 D x ht', sum_sq_flat, e1] at h0
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hcs' : (c3s : ℝ) * (d : ℝ) ^ 2 = 36 * (n : ℝ) ^ 2 * 2 ^ 1200 := by exact_mod_cast hcs
  have hcs2 : (c3s : ℝ) = 36 * 2 ^ 1200 * ((n : ℝ) / d) ^ 2 := by
    rw [div_pow, mul_div_assoc', eq_div_iff (ne_of_gt (pow_pos hd' 2))]
    linarith
  rw [hcs2] at h0
  have h1 : (36 * 2 ^ 1200 : ℝ) * Cf (rp D) (ra D) (rb D) (rc D) x ^ 2
      ≤ 36 * 2 ^ 1200 * (((n : ℝ) / d) ^ 2 * nsq x ^ 3) := by
    calc (36 * 2 ^ 1200 : ℝ) * Cf (rp D) (ra D) (rb D) (rc D) x ^ 2
        = (6 * (2 ^ 600 * Cf (rp D) (ra D) (rb D) (rc D) x)) ^ 2 := by ring
      _ ≤ 36 * 2 ^ 1200 * ((n : ℝ) / d) ^ 2 * nsq x ^ 3 := h0
      _ = 36 * 2 ^ 1200 * (((n : ℝ) / d) ^ 2 * nsq x ^ 3) := by ring
  exact le_of_mul_le_mul_left h1 (by positivity)

end N11.Local
