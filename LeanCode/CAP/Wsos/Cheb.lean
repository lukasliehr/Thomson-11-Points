module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import CAP.Wsos.Weights

/-!
# The Chebyshev combination

* `chebVal_rep`: the number `CAP.Wsos.chebVal` stands for the polynomial `chOutV` in the
  Chebyshev polynomials of `x`, `y`, `z`.
* `chOutV_bd`: its coefficients are bounded by the sum of the digits times `3 ^ D`.
* `chOutV_lower`, `chOutV_upper`: at a real point of the cube `[-1, 1] ^ 3` its value lies between
  twice the first digit minus the sum of the digits, and the sum of the digits.
-/

@[expose] public section

namespace CAP.Wsos

open Finset MvPolynomial

variable {P : Params} {pM mM : ℕ}

/-! ## The lists of Chebyshev polynomials -/

theorem chl_succ (s n prev cur : ℕ) :
    chl pM mM s (n + 1) prev cur
      = prev :: chl pM mM s n cur (Nat.land (subM pM mM (Nat.shiftLeft cur s) prev) mM) := rfl

theorem chl_rep (hM : Mod P pM mM) {sx : ℕ} {XP : Poly} (hX : Rep P (Nat.shiftLeft 1 sx) XP) :
    ∀ (n k prev cur : ℕ), Rep P prev (tV XP k) → Rep P cur (tV XP (k + 1)) →
      (chl pM mM (Nat.succ sx) n prev cur).length = n ∧
      ∀ i, i < n → Rep P ((chl pM mM (Nat.succ sx) n prev cur).getD i 0) (tV XP (k + i))
  | 0, _, _, _, _, _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1, k, prev, cur, hp, hc => by
    have hnext : Rep P (Nat.land (subM pM mM (Nat.shiftLeft cur (Nat.succ sx)) prev) mM) (tV XP (k + 1 + 1)) := by
      have e : Nat.shiftLeft cur (Nat.succ sx) = 2 * (Nat.shiftLeft 1 sx * cur) := by
        show cur <<< (sx + 1) = 2 * ((1 <<< sx) * cur)
        rw [Nat.shiftLeft_eq, Nat.one_shiftLeft, pow_succ]
        ring
      rw [e]
      refine (((Rep.smul 2 (hX.mul hc)).subM hM hp).land hM).congr ?_
      show _ = 2 * XP * tV XP (k + 1) - tV XP k
      rw [C_natCast']
      push_cast
      ring
    have ih := chl_rep hM hX n (k + 1) cur _ hc hnext
    rw [chl_succ]
    refine ⟨by rw [List.length_cons, ih.1], fun i hi => ?_⟩
    cases i with
    | zero => exact hp
    | succ j =>
      rw [List.getD_cons_succ]
      have := ih.2 j (Nat.lt_of_succ_lt_succ hi)
      rwa [show k + 1 + j = k + (j + 1) by omega] at this

theorem chl_spec (hM : Mod P pM mM) {sx : ℕ} {XP : Poly} (hX : Rep P (Nat.shiftLeft 1 sx) XP) (n : ℕ) :
    ∀ i, i < n → Rep P ((chl pM mM (Nat.succ sx) n 1 (Nat.shiftLeft 1 sx)).getD i 0) (tV XP i) := by
  have := (chl_rep hM hX n 0 1 (Nat.shiftLeft 1 sx) Rep.one hX).2
  intro i hi
  have h := this i hi
  rwa [zero_add] at h

/-! ## The loops in closed form -/

theorem dotC_succ (w mw n : ℕ) (ts : List ℕ) (Cr U : ℕ) :
    dotC w mw (n + 1) ts Cr U
      = dotC w mw n (tl ts) (Nat.shiftRight Cr w) (Nat.add U (Nat.mul (Nat.land Cr mw) (hd ts))) := rfl

theorem dotC_eq (w : ℕ) : ∀ (n : ℕ) (ts : List ℕ) (Cr U : ℕ),
    dotC w (mask w) n ts Cr U = U + ∑ i ∈ range n, slot w Cr i * ts.getD i 0
  | 0, ts, Cr, U => by simp [dotC]
  | n + 1, ts, Cr, U => by
    rw [dotC_succ, dotC_eq w n, sum_range_succ', slot_zero, hd_eq, tl_eq]
    have h : ∀ i, slot w (Nat.shiftRight Cr w) i = slot w Cr (i + 1) := slot_shiftRight w Cr
    simp only [h, getD_tail]
    show U + (Cr &&& mask w) * ts.getD 0 0 + _ = _
    ring

theorem chMid_succ (w mw : ℕ) (tx : List ℕ) (j : ℕ) (ty : List ℕ) (Cr U : ℕ) :
    chMid w mw mM tx (j + 1) ty Cr U
      = chMid w mw mM tx j (tl ty) (Nat.shiftRight Cr (Nat.mul w (Nat.succ j)))
          (Nat.add U (mulM mM (hd ty) (dotC w mw (Nat.succ j) tx Cr 0))) := rfl

theorem chMid_rep (hM : Mod P pM mM) (wN : ℕ) {tx TY : List ℕ} {XP YP : Poly} {n : ℕ}
    (hx : ∀ i, i < n → Rep P (tx.getD i 0) (tV XP i)) (hy : ∀ i, i < n → Rep P (TY.getD i 0) (tV YP i)) :
    ∀ (j k2 Cr U : ℕ) (UF : Poly), k2 + j ≤ n → Rep P U UF →
      Rep P (chMid wN (mask wN) mM tx j (TY.drop k2) Cr U) (UF + chMidV wN XP YP j k2 Cr)
  | 0, k2, Cr, U, UF, _, hU => by simpa [chMid, chMidV] using hU
  | j + 1, k2, Cr, U, UF, hk, hU => by
    rw [chMid_succ, hd_drop, tl_drop]
    have hin : Rep P (dotC wN (mask wN) (Nat.succ j) tx Cr 0) (chInV wN XP (j + 1) Cr) := by
      rw [dotC_eq, zero_add]
      unfold chInV
      refine Rep.sum _ _ _ fun i hi => ?_
      exact (Rep.smul _ (hx i (by have := mem_range.mp hi; omega))).congr (by rw [C_natCast'])
    have hU' := hU.add ((hy k2 (by omega)).mulM hM hin)
    have ih := chMid_rep hM wN hx hy j (k2 + 1) (Nat.shiftRight Cr (Nat.mul wN (Nat.succ j))) _ _ (by omega) hU'
    refine ih.congr ?_
    show _ = UF + (tV YP k2 * chInV wN XP (j + 1) Cr + chMidV wN XP YP j (k2 + 1) (Cr >>> (wN * (j + 1))))
    rw [add_assoc]
    rfl

theorem chOut_succ (w mw : ℕ) (tx ty : List ℕ) (j : ℕ) (tz : List ℕ) (Cr U : ℕ) :
    chOut w mw mM tx ty (j + 1) tz Cr U
      = chOut w mw mM tx ty j (tl tz)
          (Nat.shiftRight Cr (Nat.mul w (Nat.div (Nat.mul (Nat.succ j) (Nat.succ (Nat.succ j))) 2)))
          (Nat.add U (mulM mM (hd tz) (chMid w mw mM tx (Nat.succ j) ty Cr 0))) := rfl

theorem chOut_rep (hM : Mod P pM mM) (wN : ℕ) {tx ty TZ : List ℕ} {XP YP ZP : Poly} {n : ℕ}
    (hx : ∀ i, i < n → Rep P (tx.getD i 0) (tV XP i)) (hy : ∀ i, i < n → Rep P (ty.getD i 0) (tV YP i))
    (hz : ∀ i, i < n → Rep P (TZ.getD i 0) (tV ZP i)) :
    ∀ (j k3 Cr U : ℕ) (UF : Poly), k3 + j ≤ n → Rep P U UF →
      Rep P (chOut wN (mask wN) mM tx ty j (TZ.drop k3) Cr U) (UF + chOutV wN XP YP ZP j k3 Cr)
  | 0, k3, Cr, U, UF, _, hU => by simpa [chOut, chOutV] using hU
  | j + 1, k3, Cr, U, UF, hk, hU => by
    rw [chOut_succ, hd_drop, tl_drop]
    have hmid : Rep P (chMid wN (mask wN) mM tx (Nat.succ j) ty Cr 0) (chMidV wN XP YP (j + 1) 0 Cr) := by
      have := chMid_rep hM wN hx hy (j + 1) 0 Cr 0 0 (by omega) Rep.zero
      rwa [List.drop_zero, zero_add] at this
    have hU' := hU.add ((hz k3 (by omega)).mulM hM hmid)
    have ih := chOut_rep hM wN hx hy hz j (k3 + 1)
      (Nat.shiftRight Cr (Nat.mul wN (Nat.div (Nat.mul (Nat.succ j) (Nat.succ (Nat.succ j))) 2))) _ _ (by omega) hU'
    refine ih.congr ?_
    show _ = UF + (tV ZP k3 * chMidV wN XP YP (j + 1) 0 Cr
      + chOutV wN XP YP ZP j (k3 + 1) (Cr >>> (wN * ((j + 1) * (j + 2) / 2))))
    rw [add_assoc]
    rfl

theorem chebVal_rep (hM : Mod P pM mM) (N : ℕ) :
    Rep P (chebVal P pM mM N) (chOutV P.wN (X 0) (X 1) (X 2) (P.D + 1) 0 N) := by
  unfold chebVal
  have hx := chl_spec hM (rep_X0 P) (Nat.succ P.D)
  have hy := chl_spec hM (rep_X1 P) (Nat.succ P.D)
  have hz := chl_spec hM (rep_X2 P) (Nat.succ P.D)
  have := chOut_rep hM P.wN hx hy hz (P.D + 1) 0 N 0 0 (by omega) Rep.zero
  rwa [List.drop_zero, zero_add] at this

/-! ## Sums of digits -/

/-- The sum of the first `n` slots. -/
def dsT (w n Cr : ℕ) : ℕ := ∑ i ∈ range n, slot w Cr i

theorem dsT_add (w a b Cr : ℕ) : dsT w (a + b) Cr = dsT w a Cr + dsT w b (Cr >>> (w * a)) := by
  unfold dsT
  rw [sum_range_add]
  congr 1
  exact sum_congr rfl fun i _ => by rw [slot_shiftRight_mul]

/-- `n * (n + 1) / 2` -/
def tri (n : ℕ) : ℕ := n * (n + 1) / 2

theorem tri_succ (n : ℕ) : tri (n + 1) = (n + 1) + tri n := by
  unfold tri
  rw [show (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) by ring, Nat.add_mul_div_left _ _ (by norm_num)]
  omega

theorem two_tri (n : ℕ) : 2 * tri n = n * (n + 1) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd

/-- `∑ i ≤ n, tri i` -/
def tet : ℕ → ℕ
  | 0 => 0
  | n + 1 => tri (n + 1) + tet n

theorem six_tet : ∀ n : ℕ, 6 * tet n = n * (n + 1) * (n + 2)
  | 0 => rfl
  | n + 1 => by
    have h := two_tri (n + 1)
    have e : 6 * tri (n + 1) = 3 * ((n + 1) * (n + 1 + 1)) := by rw [← h]; ring
    show 6 * (tri (n + 1) + tet n) = _
    rw [mul_add, six_tet n, e]
    ring

theorem tet_eq_nmon (D : ℕ) : tet (D + 1) = nmon D := by
  show _ = (D + 1) * (D + 2) * (D + 3) / 6
  rw [show (D + 1) * (D + 2) * (D + 3) = 6 * tet (D + 1) by rw [six_tet]]
  exact (Nat.mul_div_cancel_left _ (by norm_num)).symm

theorem chebSum_eq (P : Params) (N : ℕ) : chebSum P N = dsT P.wN (tet (P.D + 1)) N := by
  unfold chebSum
  rw [dsum_eq, zero_add, tet_eq_nmon]
  rfl

/-! ## Bounds for the coefficients -/

theorem tV_bd (i : Fin 3) : ∀ n : ℕ,
    Bd (tV (X i : Poly) n) (3 ^ n) n ∧ Bd (tV (X i : Poly) (n + 1)) (3 ^ (n + 1)) (n + 1)
  | 0 => ⟨by simpa [tV] using Bd.one, by simpa [tV] using (Bd.X i).mono (by norm_num) le_rfl⟩
  | n + 1 => by
    obtain ⟨h0, h1⟩ := tV_bd i n
    refine ⟨h1, ?_⟩
    have a : Bd ((2 : Poly) * X i * tV (X i) (n + 1)) (2 * 1 * 3 ^ (n + 1)) (0 + 1 + (n + 1)) := by
      have h2 : Bd (2 : Poly) 2 0 := by simpa using Bd.natCast 2
      exact (h2.mul (Bd.X i)).mul h1
    have := (a.mono le_rfl (by omega : 0 + 1 + (n + 1) ≤ n + 1 + 1)).sub (h0.mono le_rfl (by omega : n ≤ n + 1 + 1))
    refine this.mono ?_ le_rfl
    rw [pow_succ, pow_succ, pow_succ]
    omega

theorem tV_bd' (i : Fin 3) (n : ℕ) : Bd (tV (X i : Poly) n) (3 ^ n) n := (tV_bd i n).1

theorem chInV_bd (wN : ℕ) (i : Fin 3) (n Cr e : ℕ) (hn : n ≤ e + 1) :
    Bd (chInV wN (X i : Poly) n Cr) (dsT wN n Cr * 3 ^ e) e := by
  unfold chInV dsT
  rw [sum_mul]
  refine Bd.sum _ _ _ _ fun k hk => ?_
  have hk' : k ≤ e := by have := mem_range.mp hk; omega
  have := Bd.smul (slot wN Cr k) (tV_bd' i k)
  rw [C_natCast'] at this
  exact this.mono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hk')) hk'

theorem chMidV_bd (wN : ℕ) : ∀ (j k2 Cr e : ℕ), k2 + j ≤ e + 1 →
    Bd (chMidV wN (X 0 : Poly) (X 1) j k2 Cr) (dsT wN (tri j) Cr * 3 ^ e) e
  | 0, _, _, e, _ => by simpa [chMidV, tri, dsT] using Bd.zero.mono (Nat.zero_le _) (Nat.zero_le e)
  | j + 1, k2, Cr, e, h => by
    have t1 := (tV_bd' 1 k2).mul (chInV_bd wN 0 (j + 1) Cr j le_rfl)
    have t1' : Bd (tV (X 1 : Poly) k2 * chInV wN (X 0 : Poly) (j + 1) Cr) (dsT wN (j + 1) Cr * 3 ^ e) e := by
      refine t1.mono ?_ (by omega)
      calc 3 ^ k2 * (dsT wN (j + 1) Cr * 3 ^ j) = dsT wN (j + 1) Cr * 3 ^ (k2 + j) := by rw [pow_add]; ring
        _ ≤ dsT wN (j + 1) Cr * 3 ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have ih := chMidV_bd wN j (k2 + 1) (Cr >>> (wN * (j + 1))) e (by omega)
    refine (t1'.add ih).mono (le_of_eq ?_) le_rfl
    rw [tri_succ, dsT_add wN (j + 1) (tri j) Cr]
    exact (Nat.add_mul _ _ _).symm

theorem chOutV_bd (wN : ℕ) : ∀ (j k3 Cr e : ℕ), k3 + j ≤ e + 1 →
    Bd (chOutV wN (X 0 : Poly) (X 1) (X 2) j k3 Cr) (dsT wN (tet j) Cr * 3 ^ e) e
  | 0, _, _, e, _ => by simpa [chOutV, tet, dsT] using Bd.zero.mono (Nat.zero_le _) (Nat.zero_le e)
  | j + 1, k3, Cr, e, h => by
    have t1 := (tV_bd' 2 k3).mul (chMidV_bd wN (j + 1) 0 Cr j (by omega))
    have t1' : Bd (tV (X 2 : Poly) k3 * chMidV wN (X 0 : Poly) (X 1) (j + 1) 0 Cr)
        (dsT wN (tri (j + 1)) Cr * 3 ^ e) e := by
      refine t1.mono ?_ (by omega)
      calc 3 ^ k3 * (dsT wN (tri (j + 1)) Cr * 3 ^ j) = dsT wN (tri (j + 1)) Cr * 3 ^ (k3 + j) := by
            rw [pow_add]; ring
        _ ≤ dsT wN (tri (j + 1)) Cr * 3 ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have ih := chOutV_bd wN j (k3 + 1) (Cr >>> (wN * ((j + 1) * (j + 2) / 2))) e (by omega)
    refine (t1'.add ih).mono (le_of_eq ?_) le_rfl
    show _ = dsT wN (tri (j + 1) + tet j) Cr * 3 ^ e
    rw [dsT_add wN (tri (j + 1)) (tet j) Cr]
    exact (Nat.add_mul _ _ _).symm

/-! ## Values on the cube -/

theorem tV_cos (θ : ℝ) : ∀ n : ℕ,
    tV (Real.cos θ) n = Real.cos (n * θ) ∧ tV (Real.cos θ) (n + 1) = Real.cos ((n + 1 : ℕ) * θ)
  | 0 => by simp [tV]
  | n + 1 => by
    obtain ⟨h0, h1⟩ := tV_cos θ n
    refine ⟨h1, ?_⟩
    show 2 * Real.cos θ * tV (Real.cos θ) (n + 1) - tV (Real.cos θ) n = _
    rw [h0, h1]
    have e1 : ((n + 1 + 1 : ℕ) : ℝ) * θ = ((n + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
    have e2 : (n : ℝ) * θ = ((n + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
    rw [e1, e2, Real.cos_add, Real.cos_sub]
    ring

theorem abs_tV_le {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) : |tV x n| ≤ 1 := by
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  rw [← Real.cos_arccos h1 h2, (tV_cos (Real.arccos x) n).1]
  exact Real.abs_cos_le_one _

theorem chInV_abs {x : ℝ} (hx : |x| ≤ 1) (wN n Cr : ℕ) : |chInV wN x n Cr| ≤ ((dsT wN n Cr : ℕ) : ℝ) := by
  unfold chInV dsT
  push_cast
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) (abs_tV_le hx i)

theorem chMidV_abs {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (wN : ℕ) : ∀ (j k2 Cr : ℕ),
    |chMidV wN x y j k2 Cr| ≤ ((dsT wN (tri j) Cr : ℕ) : ℝ)
  | 0, _, _ => by simp [chMidV, tri, dsT]
  | j + 1, k2, Cr => by
    show |tV y k2 * chInV wN x (j + 1) Cr + chMidV wN x y j (k2 + 1) (Cr >>> (wN * (j + 1)))| ≤ _
    rw [tri_succ, dsT_add, Nat.cast_add]
    refine (abs_add_le _ _).trans (add_le_add ?_ (chMidV_abs hx hy wN j (k2 + 1) _))
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (abs_tV_le hy k2)).trans (chInV_abs hx wN (j + 1) Cr)

theorem chOutV_abs {x y z : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) (wN : ℕ) : ∀ (j k3 Cr : ℕ),
    |chOutV wN x y z j k3 Cr| ≤ ((dsT wN (tet j) Cr : ℕ) : ℝ)
  | 0, _, _ => by simp [chOutV, tet, dsT]
  | j + 1, k3, Cr => by
    show |tV z k3 * chMidV wN x y (j + 1) 0 Cr
      + chOutV wN x y z j (k3 + 1) (Cr >>> (wN * ((j + 1) * (j + 2) / 2)))| ≤ ((dsT wN (tri (j + 1) + tet j) Cr : ℕ) : ℝ)
    rw [dsT_add, Nat.cast_add]
    refine (abs_add_le _ _).trans (add_le_add ?_ (chOutV_abs hx hy hz wN j (k3 + 1) _))
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (abs_tV_le hz k3)).trans (chMidV_abs hx hy wN (j + 1) 0 Cr)

theorem chOutV_upper {x y z : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) (wN j Cr : ℕ) :
    chOutV wN x y z j 0 Cr ≤ ((dsT wN (tet j) Cr : ℕ) : ℝ) :=
  (le_abs_self _).trans (chOutV_abs hx hy hz wN j 0 Cr)

/-- The value of a Chebyshev combination with natural coefficients on the cube is at least twice
the first coefficient minus the sum of all coefficients. -/
theorem chOutV_lower {x y z : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hz : |z| ≤ 1) (wN n Cr : ℕ) :
    2 * ((slot wN Cr 0 : ℕ) : ℝ) - ((dsT wN (tet (n + 1)) Cr : ℕ) : ℝ) ≤ chOutV wN x y z (n + 1) 0 Cr := by
  have hout := chOutV_abs hx hy hz wN n 1 (Cr >>> (wN * ((n + 1) * (n + 2) / 2)))
  have hmid := chMidV_abs hx hy wN n 1 (Cr >>> (wN * (n + 1)))
  have hin : |∑ i ∈ range n, ((slot wN Cr (i + 1) : ℕ) : ℝ) * tV x (i + 1)|
      ≤ ((∑ i ∈ range n, slot wN Cr (i + 1) : ℕ) : ℝ) := by
    push_cast
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (abs_tV_le hx (i + 1))
  have e : chOutV wN x y z (n + 1) 0 Cr
      = ((slot wN Cr 0 : ℕ) : ℝ) + ∑ i ∈ range n, ((slot wN Cr (i + 1) : ℕ) : ℝ) * tV x (i + 1)
        + chMidV wN x y n 1 (Cr >>> (wN * (n + 1)))
        + chOutV wN x y z n 1 (Cr >>> (wN * ((n + 1) * (n + 2) / 2))) := by
    show tV z 0 * (tV y 0 * chInV wN x (n + 1) Cr + chMidV wN x y n (0 + 1) (Cr >>> (wN * (n + 1))))
      + chOutV wN x y z n (0 + 1) (Cr >>> (wN * ((n + 1) * (n + 2) / 2))) = _
    unfold chInV
    rw [sum_range_succ']
    simp [tV]
    ring
  have ed : ((dsT wN (tet (n + 1)) Cr : ℕ) : ℝ)
      = ((slot wN Cr 0 : ℕ) : ℝ) + ((∑ i ∈ range n, slot wN Cr (i + 1) : ℕ) : ℝ)
        + ((dsT wN (tri n) (Cr >>> (wN * (n + 1))) : ℕ) : ℝ)
        + ((dsT wN (tet n) (Cr >>> (wN * ((n + 1) * (n + 2) / 2))) : ℕ) : ℝ) := by
    have h1 : dsT wN (tet (n + 1)) Cr = dsT wN (tri (n + 1)) Cr + dsT wN (tet n) (Cr >>> (wN * tri (n + 1))) := by
      show dsT wN (tri (n + 1) + tet n) Cr = _
      rw [dsT_add]
    have h2 : dsT wN (tri (n + 1)) Cr = dsT wN (n + 1) Cr + dsT wN (tri n) (Cr >>> (wN * (n + 1))) := by
      rw [tri_succ, dsT_add]
    have h3 : dsT wN (n + 1) Cr = slot wN Cr 0 + ∑ i ∈ range n, slot wN Cr (i + 1) := by
      unfold dsT
      rw [sum_range_succ', add_comm]
    rw [h1, h2, h3]
    push_cast
    rfl
  rw [e, ed]
  have a1 := (abs_le.mp hin).1
  have a2 := (abs_le.mp hmid).1
  have a3 := (abs_le.mp hout).1
  linarith

end CAP.Wsos
