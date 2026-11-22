module

public import N14.Local.Scatter
public import N11.Local.Tables

/-!
# G7 of route G: the quadratic forms

* `matOk_sound`: if `matOk q P rows cols` holds, the quadratic form of the table `q` is nonnegative. (The upper
  triangle of the symmetric matrix of the table is the matrix `rows` of E2, and the checker of E2 accepts it.)
* `hess`: the quadratic form of the energy plus the penalty is at least `kappa |x|²`.
* `rig`: the form of the rigidity plus the penalty is at least `sigma² |x|²`.
-/

set_option exponentiation.threshold 100000

@[expose] public section

namespace N11.Local

open Finset CAP

theorem upper_succ (q : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ) (k s : ℕ) :
    upper q k (s + 1) = zadd (q (pt k) (co k) (pt (k + (s + 1))) (co (k + (s + 1))))
      (q (pt (k + (s + 1))) (co (k + (s + 1))) (pt k) (co k)) := rfl

/-- The entries of a matrix of E2 of the order 33 as real numbers. -/
theorem dataEntry_cast (P : PSD.Params) (rows : ℕ) (hn : P.n = 33) (i j : ℕ) :
    (PSD.dataEntry P rows i j : ℝ) = (triEnt P.w 33 rows i (j - i) : ℝ) - (2 : ℝ) ^ (P.a - 1) := by
  unfold PSD.dataEntry
  rw [hn]
  push_cast
  ring

theorem pow_pred_cast (a : ℕ) : ((Nat.pow 2 (Nat.pred a) : ℕ) : ℝ) = (2 : ℝ) ^ (a - 1) := by
  show (((2 : ℕ) ^ (a - 1) : ℕ) : ℝ) = _
  rw [Nat.cast_pow, Nat.cast_ofNat]

/-- **A table whose matrix the checker of E2 accepts**: its quadratic form is nonnegative. -/
theorem matOk_sound (q : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ) (P : PSD.Params) (rows cols : ℕ)
    (h : matOk q P rows cols = true) (v : ℕ → ℝ) :
    0 ≤ ∑ k ∈ range 33, ∑ l ∈ range 33, zr (q (pt k) (co k) (pt l) (co l)) * (v k * v l) := by
  unfold matOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hn, hc⟩, ht⟩ := h
  have hn' : P.n = 33 := Nat.eq_of_beq_eq_true hn
  have hg := N14.Local.gram_quad P rows cols hc v
  rw [hn'] at hg
  have hE : ∀ i s, i < 33 → s < 33 - i → (PSD.dataEntry P rows i (i + s) : ℝ) = zr (upper q i s) := by
    intro i s hi hs
    have h1 : zr (triEnt P.w 33 rows i s, Nat.pow 2 (Nat.pred P.a)) = zr (upper q i s) :=
      zeq_sound (N14.Local.triAll_sound P.w 33 rows _ ht i s hi hs)
    rw [dataEntry_cast P rows hn', Nat.add_sub_cancel_left, ← h1, zr_pair, pow_pred_cast]
  have hd : ∀ i, i < 33 → (PSD.dataEntry P rows i i : ℝ) = zr (q (pt i) (co i) (pt i) (co i)) := by
    intro i hi
    have h2 := hE i 0 hi (by omega)
    rw [Nat.add_zero] at h2
    rw [h2]
    rfl
  have ho : ∀ i j, i < j → j < 33 → (PSD.dataEntry P rows i j : ℝ)
      = zr (q (pt i) (co i) (pt j) (co j)) + zr (q (pt j) (co j) (pt i) (co i)) := by
    intro i j hij hj
    obtain ⟨s, rfl⟩ : ∃ s, j = i + (s + 1) := ⟨j - i - 1, by omega⟩
    rw [hE i (s + 1) (by omega) (by omega), upper_succ, zr_add]
  exact le_of_le_of_eq hg (tri_full 33 (fun k l => zr (q (pt k) (co k) (pt l) (co l)))
    (fun i j => (PSD.dataEntry P rows i j : ℝ)) v hd ho)

/-! ## The quadratic form of the energy -/

/-- The bound of the quadratic form at the scale of the integers. -/
theorem hess_int (D : Dat) (kap K : ℕ) (P : PSD.Params) (rows cols : ℕ)
    (h : hessOk D kap K P rows cols = true) (x : ℕ → ℕ → ℝ) :
    (kap : ℝ) * nsq x
      ≤ sumP (fun i j => Az D i j * (2 ^ 121 * dot (x i) (x j)
              - dot (Pz D i) (Pz D j) * (dot (x i) (x i) + dot (x j) (x j)))
            + 2 * Bz D i j * Lf (Pz D) x i j ^ 2)
        + (K : ℝ) * penf (Pz D) x := by
  have h0 := matOk_sound (qtab D kap K) P rows cols h (flat x)
  rw [form_qtab] at h0
  linarith

/-- **The quadratic form of the energy**: `kappa |x|² ≤ Q(x) + K pen(x)` with `kappa = nk / dk`. -/
theorem hess (D : Dat) (kap K : ℕ) (P : PSD.Params) (rows cols : ℕ) (h : hessOk D kap K P rows cols = true)
    (nk dk Kp : ℕ) (hk : kap * dk = nk * 2 ^ 181) (hdk : 0 < dk) (hK : K = Kp * 2 ^ 61) (x : ℕ → ℕ → ℝ) :
    (nk : ℝ) / dk * nsq x ≤ Qf (rp D) (ra D) (rb D) x + (Kp : ℝ) * penf (rp D) x := by
  have h0 := hess_int D kap K P rows cols h x
  have e1 : sumP (fun i j => Az D i j * (2 ^ 121 * dot (x i) (x j)
        - dot (Pz D i) (Pz D j) * (dot (x i) (x i) + dot (x j) (x j)))
      + 2 * Bz D i j * Lf (Pz D) x i j ^ 2) = 2 ^ 181 * Qf (rp D) (ra D) (rb D) x := by
    unfold Qf
    rw [← sumP_mul]
    refine sumP_congr fun i j _ _ => ?_
    show Az D i j * (2 ^ 121 * dot (x i) (x j) - dot (Pz D i) (Pz D j) * (dot (x i) (x i) + dot (x j) (x j)))
        + 2 * Bz D i j * Lf (Pz D) x i j ^ 2
      = 2 ^ 181 * (ra D i j * psif (rp D) x i j + rb D i j * Lf (rp D) x i j ^ 2)
    rw [Az_val, Bz_val, Lf_Pz, dot_Pz]
    unfold psif
    ring
  have hdk' : (0 : ℝ) < dk := by exact_mod_cast hdk
  have hk' : (kap : ℝ) * dk = nk * 2 ^ 181 := by exact_mod_cast hk
  have hk2 : (kap : ℝ) = (nk : ℝ) / dk * 2 ^ 181 := by
    rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hdk')]
    exact hk'
  have hK' : (K : ℝ) = Kp * 2 ^ 61 := by
    rw [hK, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [e1, penf_Pz, hk2, hK'] at h0
  have h1 : (2 : ℝ) ^ 181 * ((nk : ℝ) / dk * nsq x)
      ≤ 2 ^ 181 * (Qf (rp D) (ra D) (rb D) x + (Kp : ℝ) * penf (rp D) x) := by linarith
  exact le_of_mul_le_mul_left h1 (by positivity)

/-! ## The rigidity -/

theorem rig_int (D : Dat) (sig K : ℕ) (P : PSD.Params) (rows cols : ℕ) (h : rigOk D sig K P rows cols = true)
    (x : ℕ → ℕ → ℝ) :
    (sig : ℝ) * nsq x ≤ sumP (fun i j => Lf (Pz D) x i j ^ 2) + (K : ℝ) * penf (Pz D) x := by
  have h0 := matOk_sound (rtab D sig K) P rows cols h (flat x)
  rw [form_rtab] at h0
  linarith

/-- **The rigidity**: `sigma² |x|² ≤ ∑ L_ij(x)² + K pen(x)` with `sigma² = ns / ds`. -/
theorem rig (D : Dat) (sig K : ℕ) (P : PSD.Params) (rows cols : ℕ) (h : rigOk D sig K P rows cols = true)
    (ns ds : ℕ) (hs : sig * ds = ns * 2 ^ 120) (hds : 0 < ds) (x : ℕ → ℕ → ℝ) :
    (ns : ℝ) / ds * nsq x ≤ Rf (rp D) x + (K : ℝ) * penf (rp D) x := by
  have h0 := rig_int D sig K P rows cols h x
  have e1 : sumP (fun i j => Lf (Pz D) x i j ^ 2) = 2 ^ 120 * Rf (rp D) x := by
    unfold Rf
    rw [← sumP_mul]
    refine sumP_congr fun i j _ _ => ?_
    show Lf (Pz D) x i j ^ 2 = 2 ^ 120 * Lf (rp D) x i j ^ 2
    rw [Lf_Pz]
    ring
  have hds' : (0 : ℝ) < ds := by exact_mod_cast hds
  have hs' : (sig : ℝ) * ds = ns * 2 ^ 120 := by exact_mod_cast hs
  have hs2 : (sig : ℝ) = (ns : ℝ) / ds * 2 ^ 120 := by
    rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hds')]
    exact hs'
  rw [e1, penf_Pz, hs2] at h0
  have h1 : (2 : ℝ) ^ 120 * ((ns : ℝ) / ds * nsq x)
      ≤ 2 ^ 120 * (Rf (rp D) x + (K : ℝ) * penf (rp D) x) := by linarith
  exact le_of_mul_le_mul_left h1 (by positivity)

end N11.Local
