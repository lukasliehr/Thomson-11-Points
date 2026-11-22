module

public import CAP.UniPos.Sound
public import CAP.UniPos.PolyKernel

/-!
# E3, sign of a polynomial on an interval: soundness of the checker

**Theorem** (`CAP.UniPos.checkPoly_sound`). If `CAP.UniPos.checkPoly P Pp c0 cuts = true`, then for
all real `t` with `(c0 - off) / 2 ^ s ≤ t ≤ (c_m - off) / 2 ^ s`, where `c_m` is the last cut,

  `0 ≤ p(t)`,   and   `0 < p(t)` if `st = 1`,

where `p(t) = pEvalG P Pp t = ∑ d ≤ n, coefZG P Pp d * t ^ d` and `coefZG P Pp d` is slot `d` of `Pp`
minus the bias.

The proof has the structure of `CAP/UniPos/Sound.lean`, whose lemmas on polynomials with natural
coefficients it uses: the numbers of the checker are values at `2 ^ V` (`hornerG_eq`), the test
compares coefficients (`pieceOk_coeff`), and for a point between two cuts a value `y ≥ 0` of the
variable is chosen (`cutsG_cover`).
-/

@[expose] public section

namespace CAP.UniPos

open Polynomial Finset

/-- The linear form `off * (1 + y)`. -/
noncomputable def Of (off : ℕ) : ℕ[X] := C off * (1 + X)

theorem mulOff_eval (V off : ℕ) (F : ℕ[X]) : mulOff V off (F.eval (2 ^ V)) = (F * Of off).eval (2 ^ V) := by
  show off * (F.eval (2 ^ V) + F.eval (2 ^ V) <<< V) = _
  rw [Nat.shiftLeft_eq]
  simp only [Of, eval_mul, eval_C, eval_add, eval_one, eval_X]
  ring

theorem natDegree_Of (off : ℕ) : (Of off).natDegree ≤ 1 := by
  refine (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans ?_)
  rw [natDegree_one]
  exact max_le (Nat.zero_le 1) natDegree_X_le

theorem rv_Of (y : ℝ) (off : ℕ) : rv y (Of off) = off * (1 + y) := by
  unfold Of
  rw [map_mul, rv_C, map_add, map_one, rv_X]

/-! ## Horner's rule -/

/-- The state of Horner's rule as polynomials: with `k` coefficients left. -/
noncomputable def hornerGP (P : PParams) (Pp c c' : ℕ) : ℕ → ℕ[X] → ℕ[X] → ℕ[X] → ℕ[X] × ℕ[X]
  | 0, Sp, Sn, _ => (Sp, Sn)
  | k + 1, Sp, Sn, Pw =>
    hornerGP P Pp c c' k (Sp * Mf c c' + Sn * Of P.off + C (slot P.W Pp k) * Pw)
      (Sn * Mf c c' + Sp * Of P.off + C (2 ^ (P.aH - 1)) * Pw) (Pw * L2 P.s)

theorem hornerG_succ (P : PParams) (V Pp c c' k Sp Sn Pw : ℕ) :
    hornerG P V Pp c c' (k + 1) Sp Sn Pw =
      hornerG P V Pp c c' k (mulM V c c' Sp + mulOff V P.off Sn + slot P.W Pp k * Pw)
        (mulM V c c' Sn + mulOff V P.off Sp + 2 ^ (P.aH - 1) * Pw) (mulL2 V P.s Pw) := by
  rw [← Nat.one_shiftLeft]
  rfl

theorem hornerG_eq (P : PParams) (V Pp c c' : ℕ) : ∀ (k : ℕ) (Sp Sn Pw : ℕ[X]),
    hornerG P V Pp c c' k (Sp.eval (2 ^ V)) (Sn.eval (2 ^ V)) (Pw.eval (2 ^ V)) =
      ((hornerGP P Pp c c' k Sp Sn Pw).1.eval (2 ^ V), (hornerGP P Pp c c' k Sp Sn Pw).2.eval (2 ^ V))
  | 0, _, _, _ => rfl
  | k + 1, Sp, Sn, Pw => by
    have e1 : (Sp * Mf c c').eval (2 ^ V) + (Sn * Of P.off).eval (2 ^ V) + slot P.W Pp k * Pw.eval (2 ^ V)
        = (Sp * Mf c c' + Sn * Of P.off + C (slot P.W Pp k) * Pw).eval (2 ^ V) := by
      simp only [eval_add, eval_mul, eval_C]
    have e2 : (Sn * Mf c c').eval (2 ^ V) + (Sp * Of P.off).eval (2 ^ V) + 2 ^ (P.aH - 1) * Pw.eval (2 ^ V)
        = (Sn * Mf c c' + Sp * Of P.off + C (2 ^ (P.aH - 1)) * Pw).eval (2 ^ V) := by
      simp only [eval_add, eval_mul, eval_C]
    rw [hornerG_succ, mulL2_eval, mulM_eval, mulM_eval, mulOff_eval, mulOff_eval, e1, e2, hornerGP]
    exact hornerG_eq P V Pp c c' k _ _ _

/-- The pair of `B = ∑ d, P d * (M⁺ - M⁻) ^ d * L ^ (n - d)`. -/
noncomputable def bG (P : PParams) (Pp c c' : ℕ) : ℕ[X] × ℕ[X] := hornerGP P Pp c c' (P.n + 1) 0 0 1

theorem hornerG_top (P : PParams) (V Pp c c' : ℕ) :
    hornerG P V Pp c c' (P.n + 1) 0 0 1 = ((bG P Pp c c').1.eval (2 ^ V), (bG P Pp c c').2.eval (2 ^ V)) := by
  have h := hornerG_eq P V Pp c c' (P.n + 1) 0 0 1
  rw [eval_zero, eval_one] at h
  exact h

theorem natDegree_hornerGP (P : PParams) (Pp c c' : ℕ) : ∀ (k j : ℕ) (Sp Sn Pw : ℕ[X]),
    Sp.natDegree ≤ j → Sn.natDegree ≤ j → Pw.natDegree ≤ j →
    (hornerGP P Pp c c' k Sp Sn Pw).1.natDegree ≤ j + k ∧ (hornerGP P Pp c c' k Sp Sn Pw).2.natDegree ≤ j + k
  | 0, j, Sp, Sn, _, h1, h2, _ => ⟨h1, h2⟩
  | k + 1, j, Sp, Sn, Pw, h1, h2, h3 => by
    have hc : ∀ c : ℕ, (C c * Pw).natDegree ≤ j + 1 := fun c =>
      (natDegree_C_mul_le _ _).trans (h3.trans (Nat.le_succ j))
    have a1 : (Sp * Mf c c' + Sn * Of P.off + C (slot P.W Pp k) * Pw).natDegree ≤ j + 1 :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans
        (max_le (natDegree_mul_lin h1 (natDegree_Mf _ _)) (natDegree_mul_lin h2 (natDegree_Of _)))) (hc _))
    have a2 : (Sn * Mf c c' + Sp * Of P.off + C (2 ^ (P.aH - 1)) * Pw).natDegree ≤ j + 1 :=
      (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans
        (max_le (natDegree_mul_lin h2 (natDegree_Mf _ _)) (natDegree_mul_lin h1 (natDegree_Of _)))) (hc _))
    have a3 : (Pw * L2 P.s).natDegree ≤ j + 1 := natDegree_mul_lin h3 (natDegree_L2 _)
    have h := natDegree_hornerGP P Pp c c' k (j + 1) _ _ _ a1 a2 a3
    have e : j + 1 + k = j + (k + 1) := by ring
    rw [e] at h
    rw [hornerGP]
    exact h

theorem natDegree_bG (P : PParams) (Pp c c' : ℕ) :
    (bG P Pp c c').1.natDegree < P.n + 2 ∧ (bG P Pp c c').2.natDegree < P.n + 2 := by
  have h := natDegree_hornerGP P Pp c c' (P.n + 1) 0 0 0 1 (by simp) (by simp) (by simp)
  rw [zero_add] at h
  exact ⟨Nat.lt_succ_of_le h.1, Nat.lt_succ_of_le h.2⟩

/-! ## The comparison of the coefficients -/

theorem pieceOk_coeff (P : PParams) (Pp c c' : ℕ) (hV : 1 ≤ P.V) (h : pieceOk P Pp c c' = true) :
    (∀ i, (bG P Pp c c').2.coeff i ≤ (bG P Pp c c').1.coeff i) ∧
      (bG P Pp c c').2.coeff 0 + P.st ≤ (bG P Pp c c').1.coeff 0 := by
  have h0 : (Nat.blt (hornerG P 0 Pp c c' (P.n + 1) 0 0 1).1 (1 <<< (P.V - 1))
      && Nat.blt (hornerG P 0 Pp c c' (P.n + 1) 0 0 1).2 (1 <<< (P.V - 1))
      && geTest P.V (P.n + 2) (hornerG P P.V Pp c c' (P.n + 1) 0 0 1).1 (hornerG P P.V Pp c c' (P.n + 1) 0 0 1).2
      && Nat.ble (slot P.V (hornerG P P.V Pp c c' (P.n + 1) 0 0 1).2 0 + P.st)
        (slot P.V (hornerG P P.V Pp c c' (P.n + 1) 0 0 1).1 0)) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, Nat.one_shiftLeft,
    hornerG_top, hornerG_top, pow_zero] at h0
  obtain ⟨⟨⟨hb1, hb2⟩, hg⟩, hst⟩ := h0
  obtain ⟨d1, d2⟩ := natDegree_bG P Pp c c'
  have h2V : 2 ^ P.V = 2 * 2 ^ (P.V - 1) := two_pow_pred hV
  have hp : ∀ i, (bG P Pp c c').1.coeff i < 2 ^ (P.V - 1) := fun i =>
    lt_of_le_of_lt (coeff_le_eval_one _ i) hb1
  have hn : ∀ i, (bG P Pp c c').2.coeff i < 2 ^ (P.V - 1) := fun i =>
    lt_of_le_of_lt (coeff_le_eval_one _ i) hb2
  rw [eval_two_pow P.V _ _ d1, eval_two_pow P.V _ _ d2] at hg hst
  have key := geTest_sound P.V (P.n + 2) _ _ hV (fun i _ => hp i) (fun i _ => hn i) hg
  rw [slot_packSum P.V (P.n + 2) (bG P Pp c c').2.coeff (fun i _ => by have := hn i; omega) 0 (by omega),
    slot_packSum P.V (P.n + 2) (bG P Pp c c').1.coeff (fun i _ => by have := hp i; omega) 0 (by omega)] at hst
  refine ⟨fun i => ?_, Nat.le_of_ble_eq_true hst⟩
  by_cases hi : i < P.n + 2
  · exact key i hi
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le d2 (not_lt.mp hi))]
    exact Nat.zero_le _

/-! ## Real values -/

/-- The integer coefficient `d` of `p`: slot `d` of `Pp` minus the bias. -/
def coefZG (P : PParams) (Pp d : ℕ) : ℤ := (slot P.W Pp d : ℤ) - 2 ^ (P.aH - 1)

/-- `p(t) = ∑ d ≤ n, P d * t ^ d`. -/
noncomputable def pEvalG (P : PParams) (Pp : ℕ) (t : ℝ) : ℝ :=
  ∑ d ∈ range (P.n + 1), (coefZG P Pp d : ℝ) * t ^ d

theorem hornerGP_rv (P : PParams) (Pp c c' : ℕ) (y : ℝ) : ∀ (k : ℕ) (Sp Sn Pw : ℕ[X]),
    rv y (hornerGP P Pp c c' k Sp Sn Pw).1 - rv y (hornerGP P Pp c c' k Sp Sn Pw).2 =
      (rv y Sp - rv y Sn) * (rv y (Mf c c') - rv y (Of P.off)) ^ k
        + rv y Pw * ∑ d ∈ range k, (coefZG P Pp d : ℝ) * (rv y (Mf c c') - rv y (Of P.off)) ^ d
          * rv y (L2 P.s) ^ (k - 1 - d)
  | 0, Sp, Sn, Pw => by simp [hornerGP]
  | k + 1, Sp, Sn, Pw => by
    have e : ∀ d ∈ range k, (coefZG P Pp d : ℝ) * (rv y (Mf c c') - rv y (Of P.off)) ^ d
          * rv y (L2 P.s) ^ (k + 1 - 1 - d)
        = rv y (L2 P.s) * ((coefZG P Pp d : ℝ) * (rv y (Mf c c') - rv y (Of P.off)) ^ d
          * rv y (L2 P.s) ^ (k - 1 - d)) := by
      intro d hd
      have hd' := mem_range.mp hd
      have e' : k + 1 - 1 - d = (k - 1 - d) + 1 := by omega
      rw [e', pow_succ]
      ring
    rw [hornerGP, hornerGP_rv P Pp c c' y k, sum_range_succ, sum_congr rfl e, ← mul_sum]
    simp only [map_add, map_mul, rv_C, Nat.add_sub_cancel, Nat.sub_self, pow_zero, coefZG]
    push_cast
    ring

theorem bG_rv (P : PParams) (Pp c c' : ℕ) (y : ℝ) :
    rv y (bG P Pp c c').1 - rv y (bG P Pp c c').2 =
      ∑ d ∈ range (P.n + 1), (coefZG P Pp d : ℝ) * (rv y (Mf c c') - rv y (Of P.off)) ^ d
        * rv y (L2 P.s) ^ (P.n - d) := by
  have h := hornerGP_rv P Pp c c' y (P.n + 1) 0 0 1
  simp only [map_zero, map_one, sub_self, zero_mul, zero_add, one_mul, Nat.add_sub_cancel] at h
  exact h

/-- For a pair of points and `y ≥ 0`: `B(y) ≥ st`. -/
theorem piece_real (P : PParams) (Pp c c' : ℕ) (hV : 1 ≤ P.V) (h : pieceOk P Pp c c' = true) (y : ℝ)
    (hy : 0 ≤ y) :
    (P.st : ℝ) ≤ ∑ d ∈ range (P.n + 1), (coefZG P Pp d : ℝ)
      * ((c : ℝ) + c' * y - P.off * (1 + y)) ^ d * (2 ^ P.s * (1 + y)) ^ (P.n - d) := by
  obtain ⟨hc, hst⟩ := pieceOk_coeff P Pp c c' hV h
  have hle : ∀ i, ((bG P Pp c c').2 + C P.st).coeff i ≤ (bG P Pp c c').1.coeff i := by
    intro i
    rw [coeff_add, coeff_C]
    by_cases hi : i = 0
    · subst hi
      simpa using hst
    · simpa [hi] using hc i
  have hmono := rv_mono y hy _ _ hle
  rw [map_add, rv_C] at hmono
  have hb := bG_rv P Pp c c' y
  rw [rv_Mf, rv_Of, rv_L2] at hb
  linarith

/-- For a point `t` between two points: `p(t) * L ^ n ≥ st`. -/
theorem piece_sign (P : PParams) (Pp c c' : ℕ) (hV : 1 ≤ P.V) (h : pieceOk P Pp c c' = true) (t y : ℝ)
    (hy : 0 ≤ y) (hμ : (c : ℝ) + c' * y - P.off * (1 + y) = t * (2 ^ P.s * (1 + y))) :
    (P.st : ℝ) ≤ pEvalG P Pp t * (2 ^ P.s * (1 + y)) ^ P.n := by
  have key := piece_real P Pp c c' hV h y hy
  rw [hμ] at key
  have hsum : ∑ d ∈ range (P.n + 1), (coefZG P Pp d : ℝ) * (t * (2 ^ P.s * (1 + y))) ^ d
        * (2 ^ P.s * (1 + y)) ^ (P.n - d) = pEvalG P Pp t * (2 ^ P.s * (1 + y)) ^ P.n := by
    unfold pEvalG
    rw [sum_mul]
    refine sum_congr rfl fun d hd => ?_
    have hd' : d ≤ P.n := Nat.lt_succ_iff.mp (mem_range.mp hd)
    have e : (2 ^ P.s * (1 + y)) ^ P.n = (2 ^ P.s * (1 + y)) ^ d * (2 ^ P.s * (1 + y)) ^ (P.n - d) := by
      rw [← pow_add, Nat.add_sub_of_le hd']
    rw [e, mul_pow]
    ring
  rw [hsum] at key
  exact key

/-! ## The cover and the theorem -/

/-- The last cut. -/
def lastCut : ℕ → List ℕ → ℕ
  | prev, [] => prev
  | _, c :: l => lastCut c l

theorem cutsG_cover (P : PParams) (Pp : ℕ) : ∀ (l : List ℕ) (prev prev2 : ℕ),
    cutsG P Pp l prev prev2 = true → ∀ μ : ℝ, (prev : ℝ) ≤ μ → μ ≤ lastCut prev l →
      ∃ c c' : ℕ, ∃ y : ℝ, pieceOk P Pp c c' = true ∧ 0 ≤ y ∧ (c : ℝ) + c' * y = μ * (1 + y)
  | [], prev, prev2, h, μ, h1, h2 => by
    have e : μ = prev := le_antisymm h2 h1
    exact ⟨prev, prev2, 0, h, le_rfl, by rw [e]; ring⟩
  | c :: l, prev, _, h, μ, h1, h2 => by
    have h' : (Nat.blt prev c && pieceOk P Pp prev c && cutsG P Pp l c prev) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h'
    by_cases hμ : μ < c
    · have hpos : 0 < (c : ℝ) - μ := sub_pos.mpr hμ
      refine ⟨prev, c, (μ - prev) / (c - μ), h'.1.2, div_nonneg (sub_nonneg.mpr h1) hpos.le, ?_⟩
      field_simp
      ring
    · exact cutsG_cover P Pp l c prev h'.2 μ (not_lt.mp hμ) h2

/-- **Soundness of the checker of the sign of a polynomial.** If the checker accepts, then `p ≥ 0`
on the interval, and `p > 0` on the interval if `st = 1`. -/
theorem checkPoly_sound (P : PParams) (Pp c0 : ℕ) (cuts : List ℕ) (h : checkPoly P Pp c0 cuts = true)
    (t : ℝ) (h1 : ((c0 : ℝ) - P.off) / 2 ^ P.s ≤ t) (h2 : t ≤ ((lastCut c0 cuts : ℝ) - P.off) / 2 ^ P.s) :
    0 ≤ pEvalG P Pp t ∧ (P.st = 1 → 0 < pEvalG P Pp t) := by
  have h' : (Nat.ble 1 P.V && Nat.ble P.st 1 && cutsG P Pp cuts c0 c0) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq] at h'
  have hs : (0 : ℝ) < 2 ^ P.s := by positivity
  rw [div_le_iff₀ hs] at h1
  rw [le_div_iff₀ hs] at h2
  obtain ⟨c, c', y, hok, hy, hμ⟩ := cutsG_cover P Pp cuts c0 c0 h'.2 (t * 2 ^ P.s + P.off)
    (by linarith) (by linarith)
  have key := piece_sign P Pp c c' h'.1.1 hok t y hy (by rw [hμ]; ring)
  have hL : (0 : ℝ) < (2 ^ P.s * (1 + y)) ^ P.n := by positivity
  have hst0 : (0 : ℝ) ≤ P.st := Nat.cast_nonneg _
  constructor
  · by_contra hcon
    have := mul_neg_of_neg_of_pos (not_le.mp hcon) hL
    linarith
  · intro hst
    have h1' : (1 : ℝ) ≤ pEvalG P Pp t * (2 ^ P.s * (1 + y)) ^ P.n := by
      rw [hst] at key
      exact_mod_cast key
    by_contra hcon
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) hL.le
    linarith

end CAP.UniPos
