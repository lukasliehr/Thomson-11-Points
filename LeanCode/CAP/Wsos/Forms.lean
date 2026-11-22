module

public import CAP.Wsos.Value

/-!
# The numbers of the checker stand for the polynomials of the data: variables, powers, forms

For the parts of `CAP.Wsos.checkTy` that evaluate polynomials given by digits (the variables of a
box, their homogeneous powers, polynomials with signed digits, the bilinear form of a block of a
Gram matrix) this file proves that the number computed by the checker stands for the polynomial
of `CAP.Wsos.Value` (`Rep`), and bounds its coefficients and its degree (`Bd`).

Throughout, `E = 2 ^ m` as a natural number and `EP = 2 ^ m` as a polynomial.
-/

@[expose] public section

namespace CAP.Wsos

open Finset MvPolynomial

variable {P : Params} {pM mM : ℕ}

/-- `2 ^ m` as a polynomial. -/
noncomputable abbrev EP (P : Params) : Poly := (2 : Poly) ^ P.m

theorem C_natCast' (n : ℕ) : (C ((n : ℕ) : ℤ) : Poly) = ((n : ℕ) : Poly) := by simp

theorem C_intCast' (z : ℤ) : (C z : Poly) = ((z : ℤ) : Poly) := by simp

theorem C_two_pow (k : ℕ) : (C ((2 : ℤ) ^ k) : Poly) = (2 : Poly) ^ k := by
  rw [map_pow]; rfl

theorem bd_two_pow (k : ℕ) : Bd ((2 : Poly) ^ k) (2 ^ k) 0 := by
  have := Bd.natCast (2 ^ k)
  rw [show ((2 ^ k : ℕ) : ℤ) = (2 : ℤ) ^ k by push_cast; rfl, C_two_pow] at this
  exact this

theorem rep_two_pow (P : Params) (k : ℕ) : Rep P (Nat.shiftLeft 1 k) ((2 : Poly) ^ k) := by
  have := (Rep.one (P := P)).shiftLeft k
  rw [mul_one, C_two_pow] at this
  exact this

/-! ## The variable of a box -/

theorem boxOk_iff (P : Params) (b : Box) : boxOk P b = true ↔ 1 ≤ b.rho ∧ b.rho + b.cp + b.cn ≤ 2 ^ P.m := by
  unfold boxOk
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]
  show _ ∧ b.rho + b.cp + b.cn ≤ 1 <<< P.m ↔ _
  rw [Nat.one_shiftLeft]

theorem aff_rep (hM : Mod P pM mM) (b : Box) {X : ℕ} {XP : Poly} (hX : Rep P X XP) :
    Rep P (aff pM mM b X) (affV b XP) := by
  have h1 : Rep P (b.rho * X + b.cp) (C (b.rho : ℤ) * XP + C (b.cp : ℤ)) := (Rep.smul _ hX).add (Rep.natCast _)
  refine ((h1.subM hM (Rep.natCast b.cn)).land hM).congr ?_
  simp [affV]

theorem aff_bd (b : Box) (hb : boxOk P b = true) (i : Fin 3) : Bd (affV b (X i : Poly)) (2 ^ P.m) 1 := by
  obtain ⟨_, h2⟩ := (boxOk_iff P b).mp hb
  have h1 : Bd (C (b.rho : ℤ) * (X i : Poly)) (b.rho * 1) 1 := Bd.smul _ (Bd.X i)
  have h3 : Bd (C (b.cp : ℤ) : Poly) b.cp 1 := (Bd.natCast b.cp).mono le_rfl (Nat.zero_le _)
  have h4 : Bd (C (b.cn : ℤ) : Poly) b.cn 1 := (Bd.natCast b.cn).mono le_rfl (Nat.zero_le _)
  refine (((h1.add h3).sub h4).mono (by omega) le_rfl).congr ?_
  simp [affV]

/-! ## Powers -/

theorem pwr_rep (hM : Mod P pM mM) {w : ℕ} {Wp : Poly} (hw : Rep P w Wp) :
    ∀ i, Rep P (pwr mM w 1 i) (Wp ^ i)
  | 0 => by
    show Rep P 1 _
    rw [pow_zero]
    exact Rep.one
  | i + 1 => by
    rw [pow_succ]
    exact (pwr_rep hM hw i).mulM hM hw

/-- The list `h` holds the homogeneous powers of degree `n` of the variable `Wp`. -/
structure HomList (P : Params) (h : List ℕ) (Wp : Poly) (n : ℕ) : Prop where
  len : h.length = n + 1
  rep : ∀ i, i < n + 1 → Rep P (h.getD i 0) (hpow (EP P) Wp n i)

theorem homList (hM : Mod P pM mM) {w : ℕ} {Wp : Poly} (hw : Rep P w Wp) {n N : ℕ} (hn : n < N) :
    HomList P (hl P.m (Nat.succ n) (pows mM w N 1) (Nat.mul P.m n)) Wp n := by
  refine ⟨hl_length _ _ _ _, fun i hi => ?_⟩
  rw [hl_getD _ _ _ _ _ hi, pows_getD _ _ _ _ _ (by omega : i < N)]
  have h1 : Nat.mul P.m n - P.m * i = P.m * (n - i) := by
    show P.m * n - P.m * i = _
    rw [Nat.mul_sub]
  rw [h1]
  refine ((pwr_rep hM hw i).shiftLeft _).congr ?_
  unfold hpow EP
  rw [C_two_pow, pow_mul]

theorem hpow_bd {Wp : Poly} (hW : Bd Wp (2 ^ P.m) 1) {n i : ℕ} (hi : i < n + 1) :
    Bd (hpow (EP P) Wp n i) ((2 ^ P.m) ^ n) n := by
  have h1 : Bd ((EP P) ^ (n - i)) ((2 ^ P.m) ^ (n - i)) 0 := by
    have := (bd_two_pow P.m).pow (n - i)
    simpa using this
  have h2 := h1.mul (hW.pow i)
  refine h2.mono (le_of_eq ?_) (by omega)
  rw [← pow_add]
  congr 1
  omega

/-! ## Polynomials with signed digits -/

theorem spoly_rep (hM : Mod P pM mM) {h : List ℕ} {Wp : Poly} {n : ℕ} (hh : HomList P h Wp n) (wd c : ℕ) :
    Rep P (subM pM mM (dot wd (mask wd) h c 0) (bias wd h)) (spolyV wd (EP P) Wp n c) := by
  have := sdot_rep hM wd h (fun i => hpow (EP P) Wp n i) (fun i hi => hh.rep i (hh.len ▸ hi)) c
  rw [hh.len] at this
  refine this.congr ?_
  unfold spolyV
  exact sum_congr rfl fun i _ => by rw [C_intCast']

theorem spoly_bd {Wp : Poly} (hW : Bd Wp (2 ^ P.m) 1) (wd : ℕ) (hwd : 1 ≤ wd) (n c : ℕ) :
    Bd (spolyV wd (EP P) Wp n c) ((n + 1) * (2 ^ (wd - 1) * (2 ^ P.m) ^ n)) n := by
  have := sdot_bd wd hwd (n + 1) (fun i => hpow (EP P) Wp n i) ((2 ^ P.m) ^ n) n (fun i hi => hpow_bd hW hi) c
  refine this.congr ?_
  unfold spolyV
  exact sum_congr rfl fun i _ => by rw [C_intCast']

/-! ## The bilinear form of a block of a Gram matrix -/

theorem bilGo_cons (wG mG : ℕ) (h1 : List ℕ) (b1 zN hj : ℕ) (h2 : List ℕ) (Gr U : ℕ) :
    bilGo wG mG pM mM h1 b1 zN (hj :: h2) Gr U
      = bilGo wG mG pM mM h1 b1 zN h2 (Nat.shiftRight Gr zN)
          (Nat.add U (mulM mM hj (subM pM mM (dot wG mG h1 Gr 0) b1))) := rfl

theorem sdig_shift (w x o i : ℕ) : sdig w (x >>> (w * o)) i = sdig w x (o + i) := by
  unfold sdig
  rw [slot_shiftRight_mul]

theorem bilGo_rep (hM : Mod P pM mM) (wG : ℕ) {h1 : List ℕ} {W1 : Poly} {n : ℕ} (hh1 : HomList P h1 W1 n)
    (N : ℕ) : ∀ (h2 : List ℕ) (H2 : ℕ → Poly) (Gr U : ℕ) (UF : Poly),
      (∀ j, j < h2.length → Rep P (h2.getD j 0) (H2 j)) → Rep P U UF →
      Rep P (bilGo wG (mask wG) pM mM h1 (bias wG h1) (wG * N) h2 Gr U)
        (UF + ∑ j ∈ range h2.length, H2 j * ∑ i ∈ range (n + 1), ((sdig wG Gr (N * j + i) : ℤ) : Poly) * hpow (EP P) W1 n i)
  | [], H2, Gr, U, UF, _, hU => by simpa [bilGo] using hU
  | hj :: h2, H2, Gr, U, UF, hH, hU => by
    rw [bilGo_cons]
    have hrow : Rep P (subM pM mM (dot wG (mask wG) h1 Gr 0) (bias wG h1))
        (∑ i ∈ range (n + 1), ((sdig wG Gr i : ℤ) : Poly) * hpow (EP P) W1 n i) := by
      have := spoly_rep hM hh1 wG Gr
      unfold spolyV at this
      exact this
    have h0 : Rep P hj (H2 0) := hH 0 (by simp)
    have hU' := hU.add (h0.mulM hM hrow)
    have ih := bilGo_rep hM wG hh1 N h2 (fun j => H2 (j + 1)) (Nat.shiftRight Gr (wG * N)) _ _
      (fun j hj' => by
        have := hH (j + 1) (by simp; omega)
        simpa using this) hU'
    refine ih.congr ?_
    rw [List.length_cons, sum_range_succ' _ h2.length, add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    · refine sum_congr rfl fun j _ => ?_
      congr 1
      refine sum_congr rfl fun i _ => ?_
      rw [show Nat.shiftRight Gr (wG * N) = Gr >>> (wG * N) from rfl, sdig_shift]
      congr 3
      ring
    · simp

theorem bil_rep (hM : Mod P pM mM) {h1 h2 : List ℕ} {W1 W2 : Poly} {n : ℕ} (hh1 : HomList P h1 W1 n)
    (hh2 : HomList P h2 W2 n) (G b c : ℕ) :
    Rep P (bil P pM mM G n b c h1 h2)
      (bilV P.wG (EP P) W1 W2 n (P.q * (n + 1)) (blockOf P G n b c)) := by
  have := bilGo_rep hM P.wG hh1 (P.q * (n + 1)) h2 (fun j => hpow (EP P) W2 n j) (blockOf P G n b c) 0 0
    (fun j hj => hh2.rep j (hh2.len ▸ hj)) Rep.zero
  rw [hh2.len, zero_add] at this
  exact this

theorem bil_bd {W1 W2 : Poly} (h1 : Bd W1 (2 ^ P.m) 1) (h2 : Bd W2 (2 ^ P.m) 1) (wG : ℕ) (hw : 1 ≤ wG)
    (n N Gr : ℕ) :
    Bd (bilV wG (EP P) W1 W2 n N Gr)
      ((n + 1) * ((2 ^ P.m) ^ n * ((n + 1) * (2 ^ (wG - 1) * (2 ^ P.m) ^ n)))) (n + n) := by
  unfold bilV
  have hrow : ∀ j, Bd (∑ i ∈ range (n + 1), ((sdig wG Gr (N * j + i) : ℤ) : Poly) * hpow (EP P) W1 n i)
      ((n + 1) * (2 ^ (wG - 1) * (2 ^ P.m) ^ n)) n := fun j => by
    have := Bd.sum_le (range (n + 1)) (fun i => C (sdig wG Gr (N * j + i)) * hpow (EP P) W1 n i)
      (2 ^ (wG - 1) * (2 ^ P.m) ^ n) n
      (fun i hi => Bd.intC (abs_sdig_le wG Gr _ hw) (hpow_bd h1 (mem_range.mp hi)))
    rw [card_range] at this
    exact this.congr (sum_congr rfl fun i _ => by rw [C_intCast'])
  have := Bd.sum_le (range (n + 1))
    (fun j => hpow (EP P) W2 n j * ∑ i ∈ range (n + 1), ((sdig wG Gr (N * j + i) : ℤ) : Poly) * hpow (EP P) W1 n i)
    ((2 ^ P.m) ^ n * ((n + 1) * (2 ^ (wG - 1) * (2 ^ P.m) ^ n))) (n + n)
    (fun j hj => (hpow_bd h2 (mem_range.mp hj)).mul (hrow j))
  rw [card_range] at this
  exact this

end CAP.Wsos
