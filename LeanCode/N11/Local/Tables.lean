module

public import Mathlib.Tactic.IntervalCases
public import N11.Local.ZVal
public import N11.Local.Forms

/-!
# G7 of route G: the tables of the checks as real numbers

The data of a check are integers at scales that are powers of two. This file states them as real numbers and
evaluates the forms of the tables.

* `Pz D i k`: the coordinate `k` of the point `i` (scale `2^60`); `Az`, `Bz`, `Cz`: the coefficients (scale `2^60`).
  `rp`, `ra`, `rb`, `rc`: the same numbers divided by `2^60`, the data of the statement.
* `flat x k = x (pt k) (co k)`: the coordinates of a displacement in the order of the flat indices.
* `sum_vec`, `sum_block`: the forms of a table that is supported on one point, or on one pair of points.
* `zr_Lu`, …: the entries of the tables, with the indicator `dl` in the place of the tests.
* `form_Lu`, `form_psi2`, `form_pen`, `form_id`, `form_qtab`, `form_rtab`: the linear and the quadratic forms.
-/

set_option exponentiation.threshold 100000

@[expose] public section

namespace N11.Local

open Finset CAP

/-! ## Casts and tests -/

theorem shl_cast (m n : ℕ) : ((Nat.shiftLeft m n : ℕ) : ℝ) = (m : ℝ) * 2 ^ n := by
  show ((m <<< n : ℕ) : ℝ) = _
  rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem shl1_cast (n : ℕ) : ((Nat.shiftLeft 1 n : ℕ) : ℝ) = 2 ^ n := by
  rw [shl_cast, Nat.cast_one, one_mul]

theorem zr_shl1 (n : ℕ) : zr (Nat.shiftLeft 1 n, 0) = 2 ^ n := by
  rw [zr_pair, shl1_cast, Nat.cast_zero, sub_zero]

theorem cast_two_mul (m : ℕ) : ((Nat.mul 2 m : ℕ) : ℝ) = 2 * (m : ℝ) := by
  show ((2 * m : ℕ) : ℝ) = _
  rw [Nat.cast_mul, Nat.cast_ofNat]

theorem cast_shl_mul (n m : ℕ) : ((Nat.mul (Nat.shiftLeft 1 n) m : ℕ) : ℝ) = 2 ^ n * (m : ℝ) := by
  show ((Nat.shiftLeft 1 n * m : ℕ) : ℝ) = _
  rw [Nat.cast_mul, shl1_cast]

theorem beq_iff (a b : ℕ) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => by rw [h]; exact Nat.beq_refl b⟩

theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem zr_ind_beq (u i : ℕ) (v : ℕ × ℕ) : zr (ind (Nat.beq u i) v) = dl u i * zr v := by
  rw [zr_ind]
  by_cases h : u = i
  · rw [if_pos ((beq_iff u i).mpr h), h, dl_self, one_mul]
  · rw [if_neg (fun hb => h ((beq_iff u i).mp hb)), dl_ne h, zero_mul]

theorem zr_ind_beq2 (u i u' j : ℕ) (v : ℕ × ℕ) :
    zr (ind (Nat.beq u i && Nat.beq u' j) v) = dl u i * dl u' j * zr v := by
  rw [zr_ind]
  by_cases h : u = i
  · by_cases h' : u' = j
    · have hb : (Nat.beq u i && Nat.beq u' j) = true := by
        rw [Bool.and_eq_true]
        exact ⟨(beq_iff u i).mpr h, (beq_iff u' j).mpr h'⟩
      rw [if_pos hb, h, h', dl_self, dl_self, one_mul, one_mul]
    · have hb : ¬ (Nat.beq u i && Nat.beq u' j) = true := by
        rw [Bool.and_eq_true]
        exact fun hh => h' ((beq_iff u' j).mp hh.2)
      rw [if_neg hb, dl_ne h', mul_zero, zero_mul]
  · have hb : ¬ (Nat.beq u i && Nat.beq u' j) = true := by
      rw [Bool.and_eq_true]
      exact fun hh => h ((beq_iff u i).mp hh.1)
    rw [if_neg hb, dl_ne h, zero_mul, zero_mul]

/-- The value with the test `j ≠ i`. -/
theorem zr_ind_nbeq (j i : ℕ) (v : ℕ × ℕ) : zr (ind (not (Nat.beq j i)) v) = if j = i then 0 else zr v := by
  by_cases h : j = i
  · rw [if_pos h, (beq_iff j i).mpr h]
    exact zr_zero
  · rw [if_neg h, beq_false_of_ne h]
    rfl

/-! ## The data -/

/-- The coordinate `k` of the point `i` of the reference configuration: scale `2^60`. -/
noncomputable def Pz (D : Dat) (i k : ℕ) : ℝ := zr (gp D i k)

/-- The coefficient `a` of a pair: scale `2^60`. -/
noncomputable def Az (D : Dat) (i j : ℕ) : ℝ := (ga D i j : ℝ)

/-- The coefficient `b` of a pair: scale `2^60`. -/
noncomputable def Bz (D : Dat) (i j : ℕ) : ℝ := (gb D i j : ℝ)

/-- The coefficient `c` of a pair: scale `2^60`. -/
noncomputable def Cz (D : Dat) (i j : ℕ) : ℝ := (gc D i j : ℝ)

/-- The reference configuration of the data. -/
noncomputable def rp (D : Dat) (i k : ℕ) : ℝ := Pz D i k / 2 ^ 60

/-- The coefficients `a` of the data. -/
noncomputable def ra (D : Dat) (i j : ℕ) : ℝ := Az D i j / 2 ^ 60

/-- The coefficients `b` of the data. -/
noncomputable def rb (D : Dat) (i j : ℕ) : ℝ := Bz D i j / 2 ^ 60

/-- The coefficients `c` of the data. -/
noncomputable def rc (D : Dat) (i j : ℕ) : ℝ := Cz D i j / 2 ^ 60

theorem Pz_eq (D : Dat) : Pz D = sc (2 ^ 60) (rp D) := by
  funext i k
  show Pz D i k = 2 ^ 60 * (Pz D i k / 2 ^ 60)
  ring

theorem Pz_val (D : Dat) (i k : ℕ) : Pz D i k = 2 ^ 60 * rp D i k := by
  unfold rp
  ring

theorem Az_val (D : Dat) (i j : ℕ) : Az D i j = 2 ^ 60 * ra D i j := by
  unfold ra
  ring

theorem Bz_val (D : Dat) (i j : ℕ) : Bz D i j = 2 ^ 60 * rb D i j := by
  unfold rb
  ring

theorem Cz_val (D : Dat) (i j : ℕ) : Cz D i j = 2 ^ 60 * rc D i j := by
  unfold rc
  ring

theorem dot_Pz (D : Dat) (i j : ℕ) : dot (Pz D i) (Pz D j) = 2 ^ 120 * dot (rp D i) (rp D j) := by
  rw [Pz_eq, dot_sc_sc]
  ring

theorem dot_Pz_left (D : Dat) (i : ℕ) (y : ℕ → ℝ) : dot (Pz D i) y = 2 ^ 60 * dot (rp D i) y := by
  rw [Pz_eq, dot_sc_left]

theorem Lf_Pz (D : Dat) (x : ℕ → ℕ → ℝ) (i j : ℕ) : Lf (Pz D) x i j = 2 ^ 60 * Lf (rp D) x i j := by
  rw [Pz_eq, Lf_sc]

theorem penf_Pz (D : Dat) (x : ℕ → ℕ → ℝ) : penf (Pz D) x = 2 ^ 120 * penf (rp D) x := by
  rw [Pz_eq, penf_sc]
  ring

theorem zr_tI (D : Dat) (i j : ℕ) : zr (tI D i j) = dot (Pz D i) (Pz D j) := by
  unfold tI
  rw [zr_add, zr_add, zr_mul, zr_mul, zr_mul, dot_eq]
  rfl

/-! ## The flat indices -/

/-- The coordinates of a displacement in the order of the flat indices. -/
noncomputable def flat (x : ℕ → ℕ → ℝ) (k : ℕ) : ℝ := x (pt k) (co k)

theorem sum_flat' (F : ℕ → ℕ → ℝ) : ∑ k ∈ range 33, F (pt k) (co k) = ∑ u ∈ range 11, ∑ c ∈ range 3, F u c :=
  sum_flat F

theorem sum_sq_flat (x : ℕ → ℕ → ℝ) : ∑ k ∈ range 33, flat x k ^ 2 = nsq x := by
  have h : ∑ k ∈ range 33, flat x k ^ 2 = ∑ u ∈ range 11, ∑ c ∈ range 3, x u c ^ 2 :=
    sum_flat' (fun u c => x u c ^ 2)
  rw [h]
  unfold nsq dot
  exact sum_congr rfl fun u _ => sum_congr rfl fun c _ => sq _

/-- The linear form of a table that is supported on the point `i`. -/
theorem sum_vec (x : ℕ → ℕ → ℝ) (i : ℕ) (hi : i < 11) (g : ℕ → ℝ) :
    ∑ k ∈ range 33, dl (pt k) i * g (co k) * flat x k = ∑ c ∈ range 3, g c * x i c := by
  have h : ∑ k ∈ range 33, dl (pt k) i * g (co k) * flat x k
      = ∑ u ∈ range 11, ∑ c ∈ range 3, dl u i * g c * x u c := sum_flat' (fun u c => dl u i * g c * x u c)
  rw [h]
  have e : ∀ u, ∑ c ∈ range 3, dl u i * g c * x u c = dl u i * ∑ c ∈ range 3, g c * x u c := by
    intro u
    rw [Finset.mul_sum]
    exact sum_congr rfl fun c _ => by ring
  rw [sum_congr rfl fun u _ => e u]
  exact sum_dl 11 i hi (fun u => ∑ c ∈ range 3, g c * x u c)

/-- The bilinear form of a table that is supported on the pair of points `(i, j)`. -/
theorem sum_block (x x' : ℕ → ℕ → ℝ) (i j : ℕ) (hi : i < 11) (hj : j < 11) (G : ℕ → ℕ → ℝ) :
    ∑ a ∈ range 33, ∑ b ∈ range 33, dl (pt a) i * dl (pt b) j * G (co a) (co b) * (flat x a * flat x' b)
      = ∑ c ∈ range 3, ∑ c' ∈ range 3, G c c' * (x i c * x' j c') := by
  have e1 : ∀ a, ∑ b ∈ range 33, dl (pt a) i * dl (pt b) j * G (co a) (co b) * (flat x a * flat x' b)
      = dl (pt a) i * (∑ c' ∈ range 3, G (co a) c' * x' j c') * flat x a := by
    intro a
    have e : ∀ b, dl (pt a) i * dl (pt b) j * G (co a) (co b) * (flat x a * flat x' b)
        = (dl (pt a) i * flat x a) * (dl (pt b) j * G (co a) (co b) * flat x' b) := fun b => by ring
    rw [sum_congr rfl fun b _ => e b, ← Finset.mul_sum, sum_vec x' j hj (fun c' => G (co a) c')]
    ring
  rw [sum_congr rfl fun a _ => e1 a, sum_vec x i hi (fun c => ∑ c' ∈ range 3, G c c' * x' j c')]
  refine sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul]
  exact sum_congr rfl fun c' _ => by ring

theorem sum_dlc (α : ℝ) (y y' : ℕ → ℝ) :
    ∑ c ∈ range 3, ∑ c' ∈ range 3, dl c c' * α * (y c * y' c') = α * dot y y' := by
  unfold dot
  rw [Finset.mul_sum]
  refine sum_congr rfl fun c hc => ?_
  have e : ∀ c', dl c c' * α * (y c * y' c') = dl c c' * (α * (y c * y' c')) := fun c' => by ring
  rw [sum_congr rfl fun c' _ => e c']
  exact sum_dl' 3 c (mem_range.mp hc) (fun c' => α * (y c * y' c'))

theorem sum_rank1 (g g' y y' : ℕ → ℝ) :
    ∑ c ∈ range 3, ∑ c' ∈ range 3, g c * g' c' * (y c * y' c') = dot g y * dot g' y' := by
  unfold dot
  rw [Finset.sum_mul_sum]
  exact sum_congr rfl fun c _ => sum_congr rfl fun c' _ => by ring

/-- A bilinear form over the flat indices, as a sum over the points and the coordinates. -/
theorem sum_flat2 (M : ℕ → ℕ → ℕ → ℕ → ℝ) (x x' : ℕ → ℕ → ℝ) :
    ∑ k ∈ range 33, ∑ l ∈ range 33, M (pt k) (co k) (pt l) (co l) * (flat x k * flat x' l)
      = ∑ u ∈ range 11, ∑ u' ∈ range 11, ∑ c ∈ range 3, ∑ c' ∈ range 3, M u c u' c' * (x u c * x' u' c') := by
  have h1 : ∀ k, ∑ l ∈ range 33, M (pt k) (co k) (pt l) (co l) * (flat x k * flat x' l)
      = ∑ u' ∈ range 11, ∑ c' ∈ range 3, M (pt k) (co k) u' c' * (flat x k * x' u' c') :=
    fun k => sum_flat' (fun u' c' => M (pt k) (co k) u' c' * (flat x k * x' u' c'))
  have h2 : ∑ k ∈ range 33, ∑ u' ∈ range 11, ∑ c' ∈ range 3, M (pt k) (co k) u' c' * (flat x k * x' u' c')
      = ∑ u ∈ range 11, ∑ c ∈ range 3, ∑ u' ∈ range 11, ∑ c' ∈ range 3, M u c u' c' * (x u c * x' u' c') :=
    sum_flat' (fun u c => ∑ u' ∈ range 11, ∑ c' ∈ range 3, M u c u' c' * (x u c * x' u' c'))
  rw [sum_congr rfl fun k _ => h1 k, h2]
  exact sum_congr rfl fun u _ => Finset.sum_comm

/-! ## The entries of the tables of the quadratic forms -/

theorem zr_Lu (D : Dat) (i j u c : ℕ) : zr (Lu D i j u c) = dl u i * Pz D j c + dl u j * Pz D i c := by
  unfold Lu
  rw [zr_add, zr_ind_beq, zr_ind_beq]
  rfl

theorem zr_psi2 (T : ℕ × ℕ) (i j u c u' c' : ℕ) :
    zr (psi2 T i j u c u' c')
      = dl c c' * (dl u i * dl u' j * 2 ^ 121 - (dl u i * dl u' i * zr T + dl u j * dl u' j * zr T)) := by
  unfold psi2
  rw [zr_ind_beq, zr_sub, zr_add, zr_ind_beq2, zr_ind_beq2, zr_ind_beq2, zr_shl1]

theorem zr_pen (D : Dat) (u c u' c' : ℕ) :
    zr (pen D u c u' c')
      = dl u u' * (Pz D u c * Pz D u c') + (dl c c' * dot (Pz D u) (Pz D u') - Pz D u c' * Pz D u' c) := by
  unfold pen
  rw [zr_add, zr_ind_beq, zr_mul, zr_sub, zr_ind_beq, zr_mul, zr_tI]
  rfl

theorem zr_qterm (D : Dat) (i j u c u' c' : ℕ) :
    zr (Prod.rec (motive := fun _ => ℕ × ℕ)
        (fun t1 t2 => zadd (znat (ga D i j) (psi2 (t1, t2) i j u c u' c'))
          (znat (Nat.mul 2 (gb D i j)) (zmul (Lu D i j u c) (Lu D i j u' c')))) (tI D i j))
      = Az D i j * zr (psi2 (tI D i j) i j u c u' c')
        + 2 * Bz D i j * (zr (Lu D i j u c) * zr (Lu D i j u' c')) := by
  rw [prod_rec_eta (fun T => zadd (znat (ga D i j) (psi2 T i j u c u' c'))
    (znat (Nat.mul 2 (gb D i j)) (zmul (Lu D i j u c) (Lu D i j u' c')))), zr_add, zr_nat, zr_nat, zr_mul,
    cast_two_mul]
  rfl

theorem zr_qtab (D : Dat) (kap K u c u' c' : ℕ) :
    zr (qtab D kap K u c u' c')
      = (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then
            Az D i j * zr (psi2 (tI D i j) i j u c u' c')
              + 2 * Bz D i j * (zr (Lu D i j u c) * zr (Lu D i j u' c'))
          else 0)
        + (K : ℝ) * zr (pen D u c u' c') - dl u u' * dl c c' * (kap : ℝ) := by
  unfold qtab
  rw [zr_sub, zr_add, zr_zsumP, zr_nat, zr_ind_beq2, zr_pair kap 0, Nat.cast_zero, sub_zero]
  refine congrArg₂ (· - ·) (congrArg₂ (· + ·) ?_ rfl) rfl
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [zr_qterm]

theorem zr_rtab (D : Dat) (sig K u c u' c' : ℕ) :
    zr (rtab D sig K u c u' c')
      = (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then zr (Lu D i j u c) * zr (Lu D i j u' c') else 0)
        + (K : ℝ) * zr (pen D u c u' c') - dl u u' * dl c c' * (sig : ℝ) := by
  unfold rtab
  rw [zr_sub, zr_add, zr_zsumP, zr_nat, zr_ind_beq2, zr_pair sig 0, Nat.cast_zero, sub_zero]
  simp only [zr_mul]

/-! ## The forms of the tables of the quadratic forms -/

theorem form_Lu (D : Dat) (x : ℕ → ℕ → ℝ) (i j : ℕ) (hi : i < 11) (hj : j < 11) :
    ∑ k ∈ range 33, zr (Lu D i j (pt k) (co k)) * flat x k = dot (Pz D j) (x i) + dot (Pz D i) (x j) := by
  have e : ∀ k, zr (Lu D i j (pt k) (co k)) * flat x k
      = dl (pt k) i * Pz D j (co k) * flat x k + dl (pt k) j * Pz D i (co k) * flat x k := by
    intro k
    rw [zr_Lu]
    ring
  rw [sum_congr rfl fun k _ => e k, sum_add_distrib, sum_vec x i hi (Pz D j), sum_vec x j hj (Pz D i)]
  rfl

theorem form_psi2 (T : ℕ × ℕ) (x : ℕ → ℕ → ℝ) (i j : ℕ) (hi : i < 11) (hj : j < 11) :
    ∑ k ∈ range 33, ∑ l ∈ range 33, zr (psi2 T i j (pt k) (co k) (pt l) (co l)) * (flat x k * flat x l)
      = 2 ^ 121 * dot (x i) (x j) - zr T * (dot (x i) (x i) + dot (x j) (x j)) := by
  have e : ∀ k l, zr (psi2 T i j (pt k) (co k) (pt l) (co l)) * (flat x k * flat x l)
      = dl (pt k) i * dl (pt l) j * (dl (co k) (co l) * 2 ^ 121) * (flat x k * flat x l)
        - (dl (pt k) i * dl (pt l) i * (dl (co k) (co l) * zr T) * (flat x k * flat x l)
          + dl (pt k) j * dl (pt l) j * (dl (co k) (co l) * zr T) * (flat x k * flat x l)) := by
    intro k l
    rw [zr_psi2]
    ring
  rw [sum_congr rfl fun k _ => sum_congr rfl fun l _ => e k l, sum2_sub, sum2_add,
    sum_block x x i j hi hj (fun c c' => dl c c' * 2 ^ 121), sum_block x x i i hi hi (fun c c' => dl c c' * zr T),
    sum_block x x j j hj hj (fun c c' => dl c c' * zr T), sum_dlc, sum_dlc, sum_dlc]
  ring

theorem form_pen (D : Dat) (x : ℕ → ℕ → ℝ) :
    ∑ k ∈ range 33, ∑ l ∈ range 33, zr (pen D (pt k) (co k) (pt l) (co l)) * (flat x k * flat x l)
      = penf (Pz D) x := by
  have e : ∀ u u', ∑ c ∈ range 3, ∑ c' ∈ range 3, zr (pen D u c u' c') * (x u c * x u' c')
      = dl u u' * (dot (Pz D u) (x u) * dot (Pz D u) (x u'))
        + (dot (Pz D u) (Pz D u') * dot (x u) (x u') - dot (Pz D u) (x u') * dot (x u) (Pz D u')) := by
    intro u u'
    have e0 : ∀ c c', zr (pen D u c u' c') * (x u c * x u' c')
        = dl u u' * (Pz D u c * Pz D u c' * (x u c * x u' c'))
          + (dl c c' * dot (Pz D u) (Pz D u') * (x u c * x u' c')
            - Pz D u' c * Pz D u c' * (x u c * x u' c')) := by
      intro c c'
      rw [zr_pen]
      ring
    rw [sum_congr rfl fun c _ => sum_congr rfl fun c' _ => e0 c c', sum2_add, sum2_sub, sum2_mul,
      sum_rank1 (Pz D u) (Pz D u) (x u) (x u'), sum_dlc, sum_rank1 (Pz D u') (Pz D u) (x u) (x u'),
      dot_comm (Pz D u') (x u)]
    ring
  rw [sum_flat2 (fun u c u' c' => zr (pen D u c u' c')) x x,
    sum_congr rfl fun u _ => sum_congr rfl fun u' _ => e u u', sum2_add]
  unfold penf
  refine congrArg₂ (· + ·) (sum_congr rfl fun u hu => ?_) rfl
  rw [sum_dl' 11 u (mem_range.mp hu) (fun u' => dot (Pz D u) (x u) * dot (Pz D u) (x u')), sq]

theorem form_id (x : ℕ → ℕ → ℝ) :
    ∑ k ∈ range 33, ∑ l ∈ range 33, dl (pt k) (pt l) * dl (co k) (co l) * (flat x k * flat x l) = nsq x := by
  have e : ∀ u u', ∑ c ∈ range 3, ∑ c' ∈ range 3, dl u u' * dl c c' * (x u c * x u' c')
      = dl u u' * dot (x u) (x u') := by
    intro u u'
    have e0 : ∀ c c', dl u u' * dl c c' * (x u c * x u' c') = dl c c' * dl u u' * (x u c * x u' c') :=
      fun c c' => by ring
    rw [sum_congr rfl fun c _ => sum_congr rfl fun c' _ => e0 c c', sum_dlc]
  rw [sum_flat2 (fun u c u' c' => dl u u' * dl c c') x x, sum_congr rfl fun u _ => sum_congr rfl fun u' _ => e u u']
  unfold nsq
  exact sum_congr rfl fun u hu => sum_dl' 11 u (mem_range.mp hu) (fun u' => dot (x u) (x u'))

theorem form_LuLu (D : Dat) (x : ℕ → ℕ → ℝ) (i j : ℕ) (hi : i < 11) (hj : j < 11) :
    ∑ k ∈ range 33, ∑ l ∈ range 33,
        zr (Lu D i j (pt k) (co k)) * zr (Lu D i j (pt l) (co l)) * flat x k * flat x l
      = Lf (Pz D) x i j ^ 2 := by
  rw [sum_mul2 33 (fun k => zr (Lu D i j (pt k) (co k))) (fun l => zr (Lu D i j (pt l) (co l))) (flat x),
    form_Lu D x i j hi hj]
  unfold Lf
  rw [dot_comm (Pz D j) (x i)]
  ring

/-- **The form of the table `qtab`.** -/
theorem form_qtab (D : Dat) (kap K : ℕ) (x : ℕ → ℕ → ℝ) :
    ∑ k ∈ range 33, ∑ l ∈ range 33, zr (qtab D kap K (pt k) (co k) (pt l) (co l)) * (flat x k * flat x l)
      = sumP (fun i j => Az D i j * (2 ^ 121 * dot (x i) (x j)
              - dot (Pz D i) (Pz D j) * (dot (x i) (x i) + dot (x j) (x j)))
            + 2 * Bz D i j * Lf (Pz D) x i j ^ 2)
        + ((K : ℝ) * penf (Pz D) x - (kap : ℝ) * nsq x) := by
  have e : ∀ k l, zr (qtab D kap K (pt k) (co k) (pt l) (co l)) * (flat x k * flat x l)
      = (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then
            Az D i j * zr (psi2 (tI D i j) i j (pt k) (co k) (pt l) (co l))
              + 2 * Bz D i j * (zr (Lu D i j (pt k) (co k)) * zr (Lu D i j (pt l) (co l)))
          else 0) * (flat x k * flat x l)
        + ((K : ℝ) * (zr (pen D (pt k) (co k) (pt l) (co l)) * (flat x k * flat x l))
          - (kap : ℝ) * (dl (pt k) (pt l) * dl (co k) (co l) * (flat x k * flat x l))) := by
    intro k l
    rw [zr_qtab]
    ring
  rw [sum_congr rfl fun k _ => sum_congr rfl fun l _ => e k l, sum2_add, sum2_sub, sum2_mul, sum2_mul,
    form_pen, form_id,
    sumP_quad 33 (fun i j k l => Az D i j * zr (psi2 (tI D i j) i j (pt k) (co k) (pt l) (co l))
      + 2 * Bz D i j * (zr (Lu D i j (pt k) (co k)) * zr (Lu D i j (pt l) (co l))))
      (fun k l => flat x k * flat x l)]
  refine congrArg₂ (· + ·) (sumP_congr fun i j hij hj => ?_) rfl
  have hi : i < 11 := lt_trans hij hj
  show ∑ k ∈ range 33, ∑ l ∈ range 33,
      (Az D i j * zr (psi2 (tI D i j) i j (pt k) (co k) (pt l) (co l))
        + 2 * Bz D i j * (zr (Lu D i j (pt k) (co k)) * zr (Lu D i j (pt l) (co l)))) * (flat x k * flat x l)
    = Az D i j * (2 ^ 121 * dot (x i) (x j) - dot (Pz D i) (Pz D j) * (dot (x i) (x i) + dot (x j) (x j)))
      + 2 * Bz D i j * Lf (Pz D) x i j ^ 2
  have e1 : ∀ k l, (Az D i j * zr (psi2 (tI D i j) i j (pt k) (co k) (pt l) (co l))
        + 2 * Bz D i j * (zr (Lu D i j (pt k) (co k)) * zr (Lu D i j (pt l) (co l)))) * (flat x k * flat x l)
      = Az D i j * (zr (psi2 (tI D i j) i j (pt k) (co k) (pt l) (co l)) * (flat x k * flat x l))
        + 2 * Bz D i j
          * (zr (Lu D i j (pt k) (co k)) * zr (Lu D i j (pt l) (co l)) * flat x k * flat x l) :=
    fun k l => by ring
  rw [sum_congr rfl fun k _ => sum_congr rfl fun l _ => e1 k l, sum2_add, sum2_mul, sum2_mul,
    form_psi2 (tI D i j) x i j hi hj, form_LuLu D x i j hi hj, zr_tI]

/-- **The form of the table `rtab`.** -/
theorem form_rtab (D : Dat) (sig K : ℕ) (x : ℕ → ℕ → ℝ) :
    ∑ k ∈ range 33, ∑ l ∈ range 33, zr (rtab D sig K (pt k) (co k) (pt l) (co l)) * (flat x k * flat x l)
      = sumP (fun i j => Lf (Pz D) x i j ^ 2) + ((K : ℝ) * penf (Pz D) x - (sig : ℝ) * nsq x) := by
  have e : ∀ k l, zr (rtab D sig K (pt k) (co k) (pt l) (co l)) * (flat x k * flat x l)
      = (∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then
            zr (Lu D i j (pt k) (co k)) * zr (Lu D i j (pt l) (co l)) else 0) * (flat x k * flat x l)
        + ((K : ℝ) * (zr (pen D (pt k) (co k) (pt l) (co l)) * (flat x k * flat x l))
          - (sig : ℝ) * (dl (pt k) (pt l) * dl (co k) (co l) * (flat x k * flat x l))) := by
    intro k l
    rw [zr_rtab]
    ring
  rw [sum_congr rfl fun k _ => sum_congr rfl fun l _ => e k l, sum2_add, sum2_sub, sum2_mul, sum2_mul,
    form_pen, form_id,
    sumP_quad 33 (fun i j k l => zr (Lu D i j (pt k) (co k)) * zr (Lu D i j (pt l) (co l)))
      (fun k l => flat x k * flat x l)]
  refine congrArg₂ (· + ·) (sumP_congr fun i j hij hj => ?_) rfl
  have hi : i < 11 := lt_trans hij hj
  show ∑ k ∈ range 33, ∑ l ∈ range 33,
      zr (Lu D i j (pt k) (co k)) * zr (Lu D i j (pt l) (co l)) * (flat x k * flat x l)
    = Lf (Pz D) x i j ^ 2
  rw [← form_LuLu D x i j hi hj]
  exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring

end N11.Local
