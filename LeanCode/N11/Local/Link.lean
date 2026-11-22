module

public import N11.Local.Tables
public import N11.Local.LinkKernel
public import N11.ParallelResearch1.Circ.Cell

/-!
# G7 of route G: the reference configuration lies near the centres of the inner box

`link`: if `linkOk D T tb del` holds, then `∑_{a<b} (<p_a, p_b> - tau_ab)² ≤ del / 2^(2 (120 + tb))` for the reference
configuration `p = rp D` and the centres `tau_ab = N11.Circ.tauV T tb a b` of the table `T`. With the statement G6
of the route (`c ∑ (t_ab - tau_ab)² < 10⁻⁶` for a minimizer, in the numbering of the certificate) this bounds the
distance between the inner products of a minimizer and those of the reference configuration.
-/

set_option exponentiation.threshold 100000

@[expose] public section

namespace N11.Local

open Finset CAP

theorem zr_linkD (D : Dat) (T tb a b : ℕ) :
    zr (linkD D T tb a b)
      = 2 ^ tb * dot (Pz D a) (Pz D b) - 2 ^ 120 * ((N11.Circ.tauP T a b : ℝ) - (N11.Circ.tauN T a b : ℝ)) := by
  unfold linkD
  rw [zr_sub, zr_nat, zr_nat, shl1_cast, shl1_cast, zr_tI, zr_pair]

/-- **The inner products of the reference configuration are close to the centres of the inner box.** -/
theorem link (D : Dat) (T tb del : ℕ) (h : linkOk D T tb del = true) :
    sumP (fun a b => (dot (rp D a) (rp D b) - N11.Circ.tauV T tb a b) ^ 2)
      ≤ (del : ℝ) / (2 ^ tb * 2 ^ 120) ^ 2 := by
  have h1 : zr (zsumP fun a b => Prod.rec (motive := fun _ => ℕ × ℕ) (fun d1 d2 => zmul (d1, d2) (d1, d2))
      (linkD D T tb a b)) ≤ zr (del, 0) := zle_sound h
  rw [zr_zsumP, zr_pair del 0, Nat.cast_zero, sub_zero] at h1
  have e : ∀ a b, zr (Prod.rec (motive := fun _ => ℕ × ℕ) (fun d1 d2 => zmul (d1, d2) (d1, d2))
        (linkD D T tb a b))
      = (2 ^ tb * 2 ^ 120) ^ 2 * (dot (rp D a) (rp D b) - N11.Circ.tauV T tb a b) ^ 2 := by
    intro a b
    have h2 : (2 : ℝ) ^ tb ≠ 0 := pow_ne_zero _ (by norm_num)
    have hτ : ((N11.Circ.tauP T a b : ℝ) - (N11.Circ.tauN T a b : ℝ)) = 2 ^ tb * N11.Circ.tauV T tb a b := by
      unfold N11.Circ.tauV
      field_simp
    rw [prod_rec_eta (fun d => zmul d d), zr_mul, zr_linkD, dot_Pz, hτ]
    ring
  have e2 : (∑ a ∈ range 11, ∑ b ∈ range 11, if a < b then
        zr (Prod.rec (motive := fun _ => ℕ × ℕ) (fun d1 d2 => zmul (d1, d2) (d1, d2)) (linkD D T tb a b)) else 0)
      = (2 ^ tb * 2 ^ 120) ^ 2 * sumP (fun a b => (dot (rp D a) (rp D b) - N11.Circ.tauV T tb a b) ^ 2) := by
    rw [← sumP_mul]
    unfold sumP
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    by_cases hab : a < b
    · rw [if_pos hab, if_pos hab, e a b]
    · rw [if_neg hab, if_neg hab]
  have h3 : (2 ^ tb * 2 ^ 120) ^ 2 * sumP (fun a b => (dot (rp D a) (rp D b) - N11.Circ.tauV T tb a b) ^ 2)
      ≤ (del : ℝ) := le_of_eq_of_le e2.symm h1
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact h3

end N11.Local
