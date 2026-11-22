module

public import CAP.Wsos.Forms

/-!
# Soundness of the check of a Gram matrix

`gramOk_sound`: if `CAP.Wsos.gramOk P n cols G = true`, then the number `G` holds the matrix
`∑ columns, y * yᵀ`: for `p, p' < N = q * (n + 1)` the signed digit `p + N * p'` of `G` is the sum
over the columns of the products of their signed digits `p` and `p'`. A rooted block whose Gram
matrix passes this check is positive semidefinite by its form.

The proof uses `Rep` with the modulus `2 ^ (wG * N ^ 2)` and constant polynomials, and the fact that
a number determines its digits when they are balanced (`digits_unique`).
-/

@[expose] public section

namespace CAP.Wsos

open Finset MvPolynomial

/-- Balanced digits are unique: a combination of powers of `2 ^ z` with coefficients below `2 ^ z`
in absolute value that vanishes modulo `2 ^ (z * n)` has no nonzero coefficient. -/
theorem digits_unique (z : ℕ) : ∀ (n : ℕ) (d : ℕ → ℤ), (∀ s, s < n → |d s| < 2 ^ z) →
    (∑ s ∈ range n, d s * 2 ^ (z * s)) ≡ 0 [ZMOD (2 : ℤ) ^ (z * n)] → ∀ s, s < n → d s = 0
  | 0, _, _, _ => fun s hs => absurd hs (Nat.not_lt_zero s)
  | n + 1, d, hd, h => by
    have hsplit : ∑ s ∈ range (n + 1), d s * 2 ^ (z * s)
        = d 0 + 2 ^ z * ∑ s ∈ range n, d (s + 1) * 2 ^ (z * s) := by
      rw [sum_range_succ', mul_sum, add_comm]
      congr 1
      · simp
      · refine sum_congr rfl fun s _ => ?_
        rw [show z * (s + 1) = z + z * s by ring, pow_add]
        ring
    rw [hsplit] at h
    have e : (2 : ℤ) ^ (z * (n + 1)) = 2 ^ z * 2 ^ (z * n) := by
      rw [← pow_add]
      congr 1
      ring
    have h2 : (2 : ℤ) ^ z * 2 ^ (z * n) ∣ d 0 + 2 ^ z * ∑ s ∈ range n, d (s + 1) * 2 ^ (z * s) := by
      rw [← e]
      exact Int.modEq_zero_iff_dvd.mp h
    have hdvd : (2 : ℤ) ^ z ∣ d 0 :=
      (dvd_add_left (dvd_mul_right _ _)).mp (dvd_trans (dvd_mul_right _ _) h2)
    have h0 : d 0 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd (hd 0 (Nat.succ_pos n))
    rw [h0, zero_add] at h2
    have h' : (∑ s ∈ range n, d (s + 1) * 2 ^ (z * s)) ≡ 0 [ZMOD (2 : ℤ) ^ (z * n)] :=
      Int.modEq_zero_iff_dvd.mpr ((mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ z ≠ 0)).mp h2)
    have ih := digits_unique z n (fun s => d (s + 1)) (fun s hs => hd (s + 1) (Nat.succ_lt_succ hs)) h'
    intro s hs
    cases s with
    | zero => exact h0
    | succ j => exact ih j (Nat.lt_of_succ_lt_succ hs)

theorem sum_range_mul_eq (N : ℕ) (f : ℕ → ℤ) : ∀ k : ℕ,
    ∑ p' ∈ range k, ∑ p ∈ range N, f (p + N * p') = ∑ s ∈ range (N * k), f s
  | 0 => by simp
  | k + 1 => by
    rw [sum_range_succ, sum_range_mul_eq N f k, Nat.mul_succ, sum_range_add]
    congr 1
    exact sum_congr rfl fun p _ => by rw [add_comm]

/-- Parameters with the modulus `2 ^ (z * N ^ 2)`; only `W` and `slots` are used. -/
def gP (z N : ℕ) : Params := ⟨z, 0, 0, N * N, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

theorem repC {P : Params} {n : ℕ} {v : ℤ} (h : ((n : ℕ) : ℤ) = v) : Rep P n (C v) := by
  unfold Rep
  rw [h, show ev P (C v) = v from eval_C _]

theorem repC_iff {P : Params} {n : ℕ} {v : ℤ} : Rep P n (C v) ↔ ((n : ℕ) : ℤ) ≡ v [ZMOD (2 : ℤ) ^ Mb P] := by
  unfold Rep
  rw [show ev P (C v) = v from eval_C _]

theorem vecGo_succ (rb mr z zN mMg pMg bA bB k c A Bv sa sb : ℕ) :
    vecGo rb mr z zN mMg pMg bA bB (k + 1) c A Bv sa sb
      = vecGo rb mr z zN mMg pMg bA bB k (Nat.shiftRight c rb) (Nat.add A (Nat.shiftLeft (Nat.land c mr) sa))
          (Nat.add Bv (Nat.shiftLeft (Nat.land c mr) sb)) (Nat.add sa z) (Nat.add sb zN) := rfl

/-- The loop `vecGo` in closed form. -/
theorem vecGo_eq (rb z zN mMg pMg bA bB : ℕ) : ∀ (k c A Bv sa sb : ℕ),
    vecGo rb (mask rb) z zN mMg pMg bA bB k c A Bv sa sb
      = mulM mMg (subM pMg mMg (A + ∑ i ∈ range k, slot rb c i * 2 ^ (sa + z * i)) bA)
          (subM pMg mMg (Bv + ∑ i ∈ range k, slot rb c i * 2 ^ (sb + zN * i)) bB)
  | 0, c, A, Bv, sa, sb => by simp [vecGo]
  | k + 1, c, A, Bv, sa, sb => by
    rw [vecGo_succ, vecGo_eq rb z zN mMg pMg bA bB k]
    have h : ∀ i, slot rb (Nat.shiftRight c rb) i = slot rb c (i + 1) := slot_shiftRight rb c
    have e1 : Nat.add A (Nat.shiftLeft (Nat.land c (mask rb)) sa) + ∑ i ∈ range k, slot rb (Nat.shiftRight c rb) i * 2 ^ (Nat.add sa z + z * i)
        = A + ∑ i ∈ range (k + 1), slot rb c i * 2 ^ (sa + z * i) := by
      rw [sum_range_succ', slot_zero]
      simp only [h]
      show A + (c &&& mask rb) <<< sa + ∑ i ∈ range k, slot rb c (i + 1) * 2 ^ (sa + z + z * i) = _
      rw [Nat.shiftLeft_eq, Nat.mul_zero, Nat.add_zero, add_assoc]
      congr 1
      rw [add_comm]
      congr 1
      exact sum_congr rfl fun i _ => by rw [show sa + z + z * i = sa + z * (i + 1) by ring]
    have e2 : Nat.add Bv (Nat.shiftLeft (Nat.land c (mask rb)) sb) + ∑ i ∈ range k, slot rb (Nat.shiftRight c rb) i * 2 ^ (Nat.add sb zN + zN * i)
        = Bv + ∑ i ∈ range (k + 1), slot rb c i * 2 ^ (sb + zN * i) := by
      rw [sum_range_succ', slot_zero]
      simp only [h]
      show Bv + (c &&& mask rb) <<< sb + ∑ i ∈ range k, slot rb c (i + 1) * 2 ^ (sb + zN + zN * i) = _
      rw [Nat.shiftLeft_eq, Nat.mul_zero, Nat.add_zero, add_assoc]
      congr 1
      rw [add_comm]
      congr 1
      exact sum_congr rfl fun i _ => by rw [show sb + zN + zN * i = sb + zN * (i + 1) by ring]
    rw [e1, e2]

theorem ones_shift (w n s : ℕ) (hw : 0 < w) : Nat.shiftLeft (ones w n) s = 2 ^ s * ∑ i ∈ range n, 2 ^ (w * i) := by
  show (ones w n) <<< s = _
  rw [Nat.shiftLeft_eq, ones_eq w n hw, mul_comm]
  congr 1
  unfold packSum
  simp

/-- The product of the two packed vectors of a column, as an integer modulo `2 ^ (z * N ^ 2)`. -/
theorem vec_rep (z N rb : ℕ) (hz : 0 < z) (hN : 0 < N) {pMg mMg : ℕ} (hM : Mod (gP z N) pMg mMg) (c : ℕ) :
    Rep (gP z N) (vecGo rb (mask rb) z (z * N) mMg pMg (Nat.shiftLeft (ones z N) (Nat.pred rb))
        (Nat.shiftLeft (ones (z * N) N) (Nat.pred rb)) N c 0 0 0 0)
      (C ((∑ p ∈ range N, sdig rb c p * 2 ^ (z * p)) * (∑ p' ∈ range N, sdig rb c p' * 2 ^ (z * (N * p'))))) := by
  rw [vecGo_eq, ones_shift z N _ hz, ones_shift (z * N) N _ (Nat.mul_pos hz hN)]
  simp only [Nat.zero_add]
  have hA : Rep (gP z N) (∑ i ∈ range N, slot rb c i * 2 ^ (z * i))
      (C (∑ i ∈ range N, ((slot rb c i : ℕ) : ℤ) * 2 ^ (z * i))) := repC (by push_cast; rfl)
  have hbA : Rep (gP z N) (2 ^ Nat.pred rb * ∑ i ∈ range N, 2 ^ (z * i))
      (C ((2 : ℤ) ^ (rb - 1) * ∑ i ∈ range N, (2 : ℤ) ^ (z * i))) := repC (by push_cast; rfl)
  have hB : Rep (gP z N) (∑ i ∈ range N, slot rb c i * 2 ^ (z * N * i))
      (C (∑ i ∈ range N, ((slot rb c i : ℕ) : ℤ) * 2 ^ (z * (N * i)))) :=
    repC (by push_cast; exact sum_congr rfl fun i _ => by rw [mul_assoc])
  have hbB : Rep (gP z N) (2 ^ Nat.pred rb * ∑ i ∈ range N, 2 ^ (z * N * i))
      (C ((2 : ℤ) ^ (rb - 1) * ∑ i ∈ range N, (2 : ℤ) ^ (z * (N * i)))) :=
    repC (by push_cast; congr 1; exact sum_congr rfl fun i _ => by rw [mul_assoc])
  refine ((hA.subM hM hbA).mulM hM (hB.subM hM hbB)).congr ?_
  rw [← map_sub, ← map_sub, ← map_mul]
  congr 1
  unfold sdig
  congr 1
  · rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  · rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring

theorem gramGo_cons (rb mr z zN mMg pMg bA bB N c : ℕ) (cols : List ℕ) (S : ℕ) :
    gramGo rb mr z zN mMg pMg bA bB N (c :: cols) S
      = gramGo rb mr z zN mMg pMg bA bB N cols (Nat.add S (vecGo rb mr z zN mMg pMg bA bB N c 0 0 0 0)) := rfl

theorem gramGo_rep (z N rb : ℕ) (hz : 0 < z) (hN : 0 < N) {pMg mMg : ℕ} (hM : Mod (gP z N) pMg mMg) :
    ∀ (cols : List ℕ) (S : ℕ) (v : ℤ), Rep (gP z N) S (C v) →
      Rep (gP z N) (gramGo rb (mask rb) z (z * N) mMg pMg (Nat.shiftLeft (ones z N) (Nat.pred rb))
          (Nat.shiftLeft (ones (z * N) N) (Nat.pred rb)) N cols S)
        (C (v + (cols.map fun c => (∑ p ∈ range N, sdig rb c p * 2 ^ (z * p))
          * (∑ p' ∈ range N, sdig rb c p' * 2 ^ (z * (N * p')))).sum))
  | [], S, v, hS => by simpa [gramGo] using hS
  | c :: cols, S, v, hS => by
    rw [gramGo_cons]
    have h1 := hS.add (vec_rep z N rb hz hN hM c)
    rw [← map_add] at h1
    have ih := gramGo_rep z N rb hz hN hM cols _ _ h1
    refine ih.congr ?_
    rw [List.map_cons, List.sum_cons, add_assoc]

theorem abs_list_sum_le (f : ℕ → ℤ) (B : ℤ) (hB : ∀ c, |f c| ≤ B) : ∀ cols : List ℕ,
    |(cols.map f).sum| ≤ cols.length * B
  | [] => by simp
  | c :: cols => by
    rw [List.map_cons, List.sum_cons, List.length_cons]
    refine (abs_add_le _ _).trans ?_
    have := abs_list_sum_le f B hB cols
    push_cast
    linarith [hB c]

/-- **Soundness of the check of a Gram matrix.** -/
theorem gramOk_sound (P : Params) (n : ℕ) (cols : List ℕ) (G : ℕ) (h : gramOk P n cols G = true)
    (p p' : ℕ) (hp : p < P.q * (n + 1)) (hp' : p' < P.q * (n + 1)) :
    sdig P.wG G (p + P.q * (n + 1) * p') = (cols.map fun c => sdig P.rb c p * sdig P.rb c p').sum := by
  set N := P.q * (n + 1) with hNdef
  set z := P.wG with hzdef
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le p) hp
  set pMg := Nat.shiftLeft 1 (Nat.mul (Nat.mul z N) N) with hpMg
  set mMg := Nat.sub pMg 1 with hmMg
  have h1 : gramK P N z (Nat.mul z N) pMg mMg cols G = true := h
  unfold gramK at h1
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq, Nat.blt_eq,
    Nat.blt_eq] at h1
  obtain ⟨⟨⟨⟨hrb, hz⟩, hG⟩, hlen⟩, hnum⟩ := h1
  have hnum' := Nat.eq_of_beq_eq_true hnum
  have hM : Mod (gP z N) pMg mMg := by
    constructor
    · show 1 <<< (z * N * N) = 2 ^ (z * (N * N))
      rw [Nat.one_shiftLeft, mul_assoc]
    · show 1 <<< (z * N * N) - 1 = 2 ^ (z * (N * N)) - 1
      rw [Nat.one_shiftLeft, mul_assoc]
  have hMb : Mb (gP z N) = z * (N * N) := rfl
  -- the two sides as integers modulo `2 ^ (z * N ^ 2)`
  have hL : Rep (gP z N) (Nat.land (gramGo P.rb (mask P.rb) z (Nat.mul z N) mMg pMg
      (Nat.shiftLeft (ones z N) (Nat.pred P.rb)) (Nat.shiftLeft (ones (Nat.mul z N) N) (Nat.pred P.rb)) N cols 0) mMg)
      (C ((0 : ℤ) + (cols.map fun c => (∑ p ∈ range N, sdig P.rb c p * 2 ^ (z * p))
        * (∑ p' ∈ range N, sdig P.rb c p' * 2 ^ (z * (N * p')))).sum)) :=
    (gramGo_rep z N P.rb hz hN hM cols 0 0 (repC (by simp))).land hM
  have hGlt : G < 2 ^ (z * (N * N)) := by
    have : pMg = 2 ^ (z * (N * N)) := hM.hp
    rwa [this] at hG
  have hR : Rep (gP z N) (Nat.land (subM pMg mMg G (Nat.shiftLeft (ones z (Nat.mul N N)) (Nat.pred z))) mMg)
      (C (∑ s ∈ range (N * N), sdig z G s * 2 ^ (z * s))) := by
    rw [ones_shift z _ _ hz]
    have hGr : Rep (gP z N) G (C (∑ s ∈ range (N * N), ((slot z G s : ℕ) : ℤ) * 2 ^ (z * s))) := by
      refine repC ?_
      have := packSum_slot z (N * N) G hGlt
      unfold packSum at this
      exact_mod_cast this.symm
    have hb : Rep (gP z N) (2 ^ Nat.pred z * ∑ i ∈ range (Nat.mul N N), 2 ^ (z * i))
        (C ((2 : ℤ) ^ (z - 1) * ∑ i ∈ range (N * N), (2 : ℤ) ^ (z * i))) := repC (by push_cast; rfl)
    refine ((hGr.subM hM hb).land hM).congr ?_
    rw [← map_sub]
    congr 1
    unfold sdig
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hnum'] at hL
  -- digits
  set a : ℕ → ℤ := fun s => (cols.map fun c => sdig P.rb c (s % N) * sdig P.rb c (s / N)).sum with ha
  have hsumL : (0 : ℤ) + (cols.map fun c => (∑ p ∈ range N, sdig P.rb c p * 2 ^ (z * p))
      * (∑ p' ∈ range N, sdig P.rb c p' * 2 ^ (z * (N * p')))).sum = ∑ s ∈ range (N * N), a s * 2 ^ (z * s) := by
    rw [zero_add]
    have hcol : ∀ c : ℕ, (∑ p ∈ range N, sdig P.rb c p * 2 ^ (z * p)) * (∑ p' ∈ range N, sdig P.rb c p' * 2 ^ (z * (N * p')))
        = ∑ s ∈ range (N * N), sdig P.rb c (s % N) * sdig P.rb c (s / N) * 2 ^ (z * s) := by
      intro c
      rw [← sum_range_mul_eq N (fun s => sdig P.rb c (s % N) * sdig P.rb c (s / N) * 2 ^ (z * s)) N, sum_mul_sum,
        sum_comm]
      refine sum_congr rfl fun q' _ => sum_congr rfl fun q hq => ?_
      have hq' : q < N := mem_range.mp hq
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq', Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt hq', zero_add,
        show z * (q + N * q') = z * q + z * (N * q') by ring, pow_add]
      ring
    have : ∀ (l : List ℕ), (l.map fun c => (∑ p ∈ range N, sdig P.rb c p * 2 ^ (z * p))
        * (∑ p' ∈ range N, sdig P.rb c p' * 2 ^ (z * (N * p')))).sum
        = ∑ s ∈ range (N * N), (l.map fun c => sdig P.rb c (s % N) * sdig P.rb c (s / N)).sum * 2 ^ (z * s) := by
      intro l
      induction l with
      | nil => simp
      | cons c l ih =>
        rw [List.map_cons, List.sum_cons, ih, hcol c, ← sum_add_distrib]
        refine sum_congr rfl fun s _ => ?_
        rw [List.map_cons, List.sum_cons]
        ring
    exact this cols
  rw [hsumL] at hL
  have hcong : (∑ s ∈ range (N * N), (a s - sdig z G s) * 2 ^ (z * s)) ≡ 0 [ZMOD (2 : ℤ) ^ (z * (N * N))] := by
    have e1 := repC_iff.mp hL
    have e2 := repC_iff.mp hR
    rw [hMb] at e1 e2
    have e3 := e1.symm.trans e2
    have : ∑ s ∈ range (N * N), (a s - sdig z G s) * 2 ^ (z * s)
        = (∑ s ∈ range (N * N), a s * 2 ^ (z * s)) - ∑ s ∈ range (N * N), sdig z G s * 2 ^ (z * s) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun s _ => by ring
    rw [this]
    exact Int.modEq_zero_iff_dvd.mpr (by
      have h2 := Int.modEq_iff_dvd.mp e3
      have h3 : (∑ s ∈ range (N * N), a s * 2 ^ (z * s)) - ∑ s ∈ range (N * N), sdig z G s * 2 ^ (z * s)
          = -((∑ s ∈ range (N * N), sdig z G s * 2 ^ (z * s)) - ∑ s ∈ range (N * N), a s * 2 ^ (z * s)) := by ring
      rw [h3]
      exact (dvd_neg).mpr h2)
  have hbnd : ∀ s, s < N * N → |a s - sdig z G s| < 2 ^ z := by
    intro s _
    have h2 : |a s| ≤ (cols.length : ℤ) * ((2 ^ (P.rb - 1) : ℕ) : ℤ) ^ 2 := by
      refine abs_list_sum_le _ _ (fun c => ?_) cols
      rw [abs_mul, sq]
      exact mul_le_mul (abs_sdig_le P.rb c _ hrb) (abs_sdig_le P.rb c _ hrb) (abs_nonneg _) (Nat.cast_nonneg _)
    have h3 : |sdig z G s| ≤ ((2 ^ (z - 1) : ℕ) : ℤ) := abs_sdig_le z G s hz
    have h4 : (cols.length : ℤ) * ((2 ^ (P.rb - 1) : ℕ) : ℤ) ^ 2 < ((2 ^ (z - 1) : ℕ) : ℤ) := by
      have h5 : cols.length * 2 ^ (2 * P.rb - 2) < 2 ^ (z - 1) := by
        have e : Nat.shiftLeft (len cols) (Nat.sub (Nat.mul 2 P.rb) 2) = cols.length * 2 ^ (2 * P.rb - 2) := by
          show (len cols) <<< (2 * P.rb - 2) = _
          rw [Nat.shiftLeft_eq, len_eq]
        have e' : Nat.shiftLeft 1 (Nat.pred z) = 2 ^ (z - 1) := by
          show 1 <<< (z - 1) = _
          rw [Nat.one_shiftLeft]
        rwa [e, e'] at hlen
      have e6 : (2 : ℕ) ^ (2 * P.rb - 2) = (2 ^ (P.rb - 1)) ^ 2 := by
        rw [← pow_mul]
        congr 1
        omega
      rw [e6] at h5
      exact_mod_cast h5
    have h6 : ((2 ^ (z - 1) : ℕ) : ℤ) + ((2 ^ (z - 1) : ℕ) : ℤ) = 2 ^ z := by
      have e := two_pow_pred hz
      have e' : ((2 ^ z : ℕ) : ℤ) = 2 * ((2 ^ (z - 1) : ℕ) : ℤ) := by exact_mod_cast e
      have e'' : ((2 ^ z : ℕ) : ℤ) = (2 : ℤ) ^ z := by push_cast; rfl
      linarith
    calc |a s - sdig z G s| ≤ |a s| + |sdig z G s| := abs_sub _ _
      _ < ((2 ^ (z - 1) : ℕ) : ℤ) + ((2 ^ (z - 1) : ℕ) : ℤ) := by linarith
      _ = 2 ^ z := h6
  have hs : p + N * p' < N * N := by
    calc p + N * p' < N + N * p' := by omega
      _ = N * (p' + 1) := by ring
      _ ≤ N * N := Nat.mul_le_mul_left _ hp'
  have h0 := digits_unique z (N * N) (fun s => a s - sdig z G s) hbnd hcong (p + N * p') hs
  simp only [ha] at h0
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp, Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt hp, zero_add] at h0
  linarith

/-- The statement of a Gram matrix: `G` holds `∑ columns, y * yᵀ` for the columns with `q * (n + 1)` entries. -/
def GramHolds (P : Params) (n : ℕ) (cols : List ℕ) (G : ℕ) : Prop :=
  ∀ p p' : ℕ, p < P.q * (n + 1) → p' < P.q * (n + 1) →
    sdig P.wG G (p + P.q * (n + 1) * p') = (cols.map fun c => sdig P.rb c p * sdig P.rb c p').sum

theorem gramOk_holds {P : Params} {n : ℕ} {cols : List ℕ} {G : ℕ} (h : gramOk P n cols G = true) :
    GramHolds P n cols G := fun p p' hp hp' => gramOk_sound P n cols G h p p' hp hp'

end CAP.Wsos
