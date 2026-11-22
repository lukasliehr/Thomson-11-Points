module

public import CAP.Wsos.TypedBound
public import CAP.Wsos.CertKernel

/-!
# The bound of a typed certificate as a number

`boundOk_sound`: let the hypotheses `CertHolds` of the theorem of the schema hold and let the check
`boundOk P C xs sP M tp tq` succeed. If, for points with a labelling, the sum of the constants of the
triple types over the triples of points is at most `6 * 2 ^ (m D + aP + sP) * Ener` plus six times the
sum of the rooted forms at coinciding points, then `tp / tq < Ener`.

The first hypothesis is the conclusion of `typed_bound` once the pair polynomials are bounded by the
potential (`Energy.lean`). The proof evaluates both sums:

* `consts_eq`: the sum of the constants over the triples of points is a sum over the triples of
  classes (`Labelling.dsum3_cls`), which the checker forms with the common multiple `M` of the
  products of the multiplicities;
* `roots_eq`: the rooted form of a class at three coinciding points is `2 ^ aF * E ^ (2 d)` times the
  sum of the entries of the block `(a, a)` of its Gram matrix of degree `0` (`rootedV_root_first`).

The file also contains the loops of `CertKernel.lean` in closed form.
-/

@[expose] public section

namespace CAP.Wsos

open Finset CAP.ThreePoint

/-! ## The loops in closed form -/

theorem shl_one (k : ℕ) : Nat.shiftLeft 1 k = 2 ^ k := Nat.one_shiftLeft k

theorem shl_eq (x s : ℕ) : Nat.shiftLeft x s = x * 2 ^ s := Nat.shiftLeft_eq x s

theorem sumN_eq (f : ℕ → ℕ) : ∀ n, sumN f n = ∑ x ∈ range n, f x
  | 0 => by
    rw [range_zero, sum_empty]
    rfl
  | n + 1 => by
    show sumN f n + f n = _
    rw [sumN_eq f n, sum_range_succ]

theorem allN_iff (f : ℕ → Bool) : ∀ n, allN f n = true ↔ ∀ x < n, f x = true
  | 0 => ⟨fun _ x hx => absurd hx (Nat.not_lt_zero x), fun _ => rfl⟩
  | n + 1 => by
    show (allN f n && f n) = true ↔ _
    rw [Bool.and_eq_true, allN_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ x hx
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hx) with h | h
      · exact h1 x h
      · rw [h]
        exact h2
    · intro h
      exact ⟨fun x hx => h x (Nat.lt_succ_of_lt hx), h n (Nat.lt_succ_self n)⟩

theorem all2N_iff (f : ℕ → ℕ → Bool) (q : ℕ) : all2N f q = true ↔ ∀ a < q, ∀ b < q, f a b = true := by
  unfold all2N
  rw [allN_iff]
  exact forall₂_congr fun a _ => allN_iff _ _

theorem all3N_iff (f : ℕ → ℕ → ℕ → Bool) (q : ℕ) :
    all3N f q = true ↔ ∀ a < q, ∀ b < q, ∀ c < q, f a b c = true := by
  unfold all3N
  rw [allN_iff]
  refine forall₂_congr fun a _ => ?_
  rw [allN_iff]
  exact forall₂_congr fun b _ => allN_iff _ _

theorem sum3N_eq (f : ℕ → ℕ → ℕ → ℕ) (q : ℕ) :
    sum3N f q = ∑ a ∈ range q, ∑ b ∈ range q, ∑ c ∈ range q, f a b c := by
  unfold sum3N
  rw [sumN_eq]
  refine sum_congr rfl fun a _ => ?_
  rw [sumN_eq]
  refine sum_congr rfl fun b _ => ?_
  rw [sumN_eq]

/-! ## The numbers of pairs and triples, and the multiplicities -/

theorem pcnt_eq (C : Cert) (a b : ℕ) : pcnt C a b = C.n a * (C.n b - (if b = a then 1 else 0)) := by
  show Nat.mul (C.n a) (Nat.sub (C.n b) (cond (Nat.beq b a) 1 0)) = _
  rw [cond_beq]
  rfl

theorem cnt_cast (C : Cert) (a b c : ℕ) :
    ((cnt C a b c : ℕ) : ℝ) = (C.n a : ℝ) * ((C.n b : ℝ) - (if b = a then 1 else 0)) * (mult C a b c : ℝ) := by
  have e : cnt C a b c = C.n a * (C.n b - (if b = a then 1 else 0)) * mult C a b c := by
    show pcnt C a b * mult C a b c = _
    rw [pcnt_eq]
  rw [e]
  split_ifs with h
  · rw [h]
    rcases Nat.eq_zero_or_pos (C.n a) with h0 | h0
    · rw [h0]
      simp
    · rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (Nat.succ_le_of_lt h0), Nat.cast_one]
  · rw [Nat.sub_zero, sub_zero, Nat.cast_mul, Nat.cast_mul]

theorem shareOf_mult (C : Cert) (a b c : ℕ) : (shareOf C a b c).mult = smult C a b c := by
  unfold shareOf smult
  cases Nat.beq c (C.last a b) <;> rfl

/-- The constant of a triple type with the product of the multiplicities of its shares. -/
theorem tyC_eq (P : Params) (C : Cert) (X : TyX) :
    tyC P C X = ((X.c2p : ℝ) - (X.c2n : ℝ)) / ((P.d.factorial : ℝ) * (tmult C X : ℝ)) := by
  have e : tmult C X = smult C X.a X.b X.c * smult C X.a X.c X.b * smult C X.b X.c X.a := rfl
  unfold tyC
  rw [shareOf_mult, shareOf_mult, shareOf_mult, e, Nat.cast_mul, Nat.cast_mul]

/-! ## The sum of the constants -/

theorem cTerm_cast (C : Cert) (xs : List TyX) (M : ℕ) (sel : TyX → ℕ) (a b c : ℕ) :
    ((cTerm C xs M sel a b c : ℕ) : ℝ)
      = (cnt C a b c : ℝ) * (sel (typeOf xs a b c) : ℝ) * ((M / tmult C (typeOf xs a b c) : ℕ) : ℝ) := by
  show (((cnt C a b c * sel (typeOf xs a b c) * (M / tmult C (typeOf xs a b c)) : ℕ)) : ℝ) = _
  rw [Nat.cast_mul, Nat.cast_mul]

/-- The term of a triple of classes: `d! * M` times the number of its triples of points times the constant
of its triple type is the difference of the two numbers of the checker. -/
theorem cTerm_eq (P : Params) (C : Cert) (xs : List TyX) {M : ℕ} (hM : 0 < M) (a b c : ℕ)
    (h : divOk C xs M a b c = true) :
    (P.d.factorial : ℝ) * M * ((C.n a : ℝ) * ((C.n b : ℝ) - (if b = a then 1 else 0)) * (mult C a b c : ℝ)
        * tyC P C (typeOf xs a b c))
      = (cTerm C xs M (fun X => X.c2p) a b c : ℝ) - (cTerm C xs M (fun X => X.c2n) a b c : ℝ) := by
  rw [cTerm_cast, cTerm_cast, ← cnt_cast]
  rcases Nat.eq_zero_or_pos (cnt C a b c) with h0 | h0
  · rw [h0]
    simp
  · have hmod : M % tmult C (typeOf xs a b c) = 0 := by
      unfold divOk at h
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · exact absurd (Nat.eq_of_beq_eq_true h) h0.ne'
      · exact Nat.eq_of_beq_eq_true h
    have hμ : tmult C (typeOf xs a b c) ≠ 0 := by
      intro e
      rw [e, Nat.mod_zero] at hmod
      omega
    have hk : tmult C (typeOf xs a b c) * (M / tmult C (typeOf xs a b c)) = M :=
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)
    have hkR : (M : ℝ) = (tmult C (typeOf xs a b c) : ℝ) * ((M / tmult C (typeOf xs a b c) : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, hk]
    have hne : ((P.d.factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
    have hμR : ((tmult C (typeOf xs a b c) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hμ
    have e0 := mul_div_cancel₀ (((typeOf xs a b c).c2p : ℝ) - ((typeOf xs a b c).c2n : ℝ)) (mul_ne_zero hne hμR)
    rw [tyC_eq]
    calc (P.d.factorial : ℝ) * M * ((cnt C a b c : ℝ) * ((((typeOf xs a b c).c2p : ℝ) - ((typeOf xs a b c).c2n : ℝ))
            / ((P.d.factorial : ℝ) * (tmult C (typeOf xs a b c) : ℝ))))
        = (cnt C a b c : ℝ) * ((M / tmult C (typeOf xs a b c) : ℕ) : ℝ)
            * ((P.d.factorial : ℝ) * (tmult C (typeOf xs a b c) : ℝ)
              * ((((typeOf xs a b c).c2p : ℝ) - ((typeOf xs a b c).c2n : ℝ))
                / ((P.d.factorial : ℝ) * (tmult C (typeOf xs a b c) : ℝ)))) := by
          rw [hkR]
          ring
      _ = (cnt C a b c : ℝ) * ((M / tmult C (typeOf xs a b c) : ℕ) : ℝ)
            * (((typeOf xs a b c).c2p : ℝ) - ((typeOf xs a b c).c2n : ℝ)) := by rw [e0]
      _ = _ := by ring

section Points

variable {P : Params} {C : Cert} {xs : List TyX} {ι : Type*} [Fintype ι] [DecidableEq ι] {cls : ι → ℕ}

/-- **The sum of the constants over the triples of points**, multiplied by `d! * M`. -/
theorem consts_eq {M : ℕ} (L : Labelling P.q C cls) (hM : 0 < M) (hdiv : all3N (divOk C xs M) P.q = true) :
    (P.d.factorial : ℝ) * M * dsum3 (fun i j k => tyC P C (typeOf xs (cls i) (cls j) (cls k)))
      = (sum3N (cTerm C xs M fun X => X.c2p) P.q : ℝ) - (sum3N (cTerm C xs M fun X => X.c2n) P.q : ℝ) := by
  have h1 : dsum3 (fun i j k => tyC P C (typeOf xs (cls i) (cls j) (cls k)))
      = ∑ a ∈ range P.q, ∑ b ∈ range P.q, ∑ c ∈ range P.q,
          (C.n a : ℝ) * ((C.n b : ℝ) - (if b = a then 1 else 0)) * (mult C a b c : ℝ) * tyC P C (typeOf xs a b c) :=
    L.dsum3_cls (fun a b c => tyC P C (typeOf xs a b c))
  have hd : ∀ a ∈ range P.q, ∀ b ∈ range P.q, ∀ c ∈ range P.q, divOk C xs M a b c = true :=
    fun a ha b hb c hc => (all3N_iff _ _).mp hdiv a (mem_range.mp ha) b (mem_range.mp hb) c (mem_range.mp hc)
  rw [h1, sum3N_eq, sum3N_eq]
  simp only [Nat.cast_sum]
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun a ha => ?_
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun b hb => ?_
  rw [mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun c hc => cTerm_eq P C xs hM a b c (hd a ha b hb c hc)

end Points

/-! ## The rooted forms at three coinciding points -/

theorem linV_E {A : Type*} [CommRing A] (wG : ℕ) (E : A) (d N Gr : ℕ) :
    linV wG E E d N Gr = (∑ j ∈ range (d + 1), ∑ i ∈ range (d + 1), (sdig wG Gr (N * j + i) : A)) * E ^ d := by
  unfold linV
  rw [sum_mul]
  exact sum_congr rfl fun j hj => by rw [hpow_self E (Nat.lt_succ_iff.mp (mem_range.mp hj))]

theorem sum_sdig (w c N d : ℕ) :
    (∑ j ∈ range (d + 1), ∑ i ∈ range (d + 1), ((sdig w c (N * j + i) : ℤ) : ℝ))
      = ((∑ j ∈ range (d + 1), ∑ i ∈ range (d + 1), slot w c (N * j + i) : ℕ) : ℝ)
        - (((d + 1) * (d + 1) * 2 ^ (w - 1) : ℕ) : ℝ) := by
  have e : ∀ j i : ℕ, ((sdig w c (N * j + i) : ℤ) : ℝ) = (slot w c (N * j + i) : ℝ) - 2 ^ (w - 1) := by
    intro j i
    unfold sdig
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
  simp only [e, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, Nat.cast_sum]
  push_cast
  ring

theorem rootDiag_eq (P : Params) (C : Cert) (a : ℕ) :
    rootDiag P C a = ∑ j ∈ range (P.d + 1), ∑ i ∈ range (P.d + 1),
      slot P.wG (blockOf P ((C.gram a).getD 0 0) P.d a a) (P.q * (P.d + 1) * j + i) := by
  show linGo P.wG (mask P.wG) (P.d + 1) (P.wG * (P.q * (P.d + 1))) (rep 1 (P.d + 1))
    (blockOf P (hd (C.gram a)) P.d a a) 0 = _
  rw [linGo_eq, rep_length, zero_add, hd_eq]
  refine sum_congr rfl fun j hj => ?_
  rw [rep_getD 1 (P.d + 1) j (mem_range.mp hj), mul_one]

theorem rootNeg_eq (P : Params) : rootNeg P = (P.d + 1) * (P.d + 1) * 2 ^ (P.wG - 1) := by
  show Nat.shiftLeft ((P.d + 1) * (P.d + 1)) (P.wG - 1) = _
  rw [shl_eq]

theorem bF_eq (P : Params) (M : ℕ) : bF P M = 6 * P.d.factorial * M := by
  show 6 * fact P.d * M = _
  rw [fact_eq]

theorem bR_eq (P : Params) (M : ℕ) : bR P M = 6 * P.d.factorial * M * 2 ^ (P.aF + 2 * P.m * P.d) := by
  show bF P M * Nat.shiftLeft 1 (P.aF + 2 * P.m * P.d) = _
  rw [bF_eq, shl_one]

/-- The rooted form of a class at three coinciding points. -/
theorem rootS_diag {P : Params} {C : Cert} {xs : List TyX} (H : CertHolds P C xs) {a : ℕ} (ha : a < P.q) :
    rootS P C a a a ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m)
      = 2 ^ P.aF * ((2 : ℝ) ^ P.m) ^ P.d * ((2 : ℝ) ^ P.m) ^ P.d
        * ((rootDiag P C a : ℝ) - (((P.d + 1) * (P.d + 1) * 2 ^ (P.wG - 1) : ℕ) : ℝ)) := by
  have hlen := H.gramLen a ha
  have hne : ((P.d.factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  have h1 : 1 ≤ (⟨C.gram a, a, a⟩ : Rooted).gram.length := by
    show 1 ≤ (C.gram a).length
    omega
  unfold rootS
  rw [rootedV_root_first P ⟨C.gram a, a, a⟩ h1, linV_E, sum_sdig, ← rootDiag_eq, div_eq_iff hne]
  ring

section Points

variable {P : Params} {C : Cert} {xs : List TyX} {ι : Type*} [Fintype ι] [DecidableEq ι] {cls : ι → ℕ}

omit [DecidableEq ι] in
/-- **The sum of the rooted forms at coinciding points.** -/
theorem roots_eq (H : CertHolds P C xs) (L : Labelling P.q C cls) :
    ∑ i, rootS P C (cls i) (cls i) (cls i) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m)
      = 2 ^ P.aF * ((2 : ℝ) ^ P.m) ^ P.d * ((2 : ℝ) ^ P.m) ^ P.d
        * ((sumN (fun a => C.n a * rootDiag P C a) P.q : ℝ) - (sumN (fun a => C.n a * rootNeg P) P.q : ℝ)) := by
  have h1 : (∑ i, rootS P C (cls i) (cls i) (cls i) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m))
      = ∑ a ∈ range P.q, (C.n a : ℝ) * rootS P C a a a ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) :=
    L.sum_cls (fun a => rootS P C a a a ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m))
  rw [h1, sumN_eq, sumN_eq]
  simp only [Nat.cast_sum, Nat.cast_mul]
  rw [← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  rw [rootS_diag H (mem_range.mp ha), rootNeg_eq]
  ring

/-- **The bound of a certificate exceeds `tp / tq`.** `Ener` is any number for which the typed bound gives
the inequality `hE`; for the energy this is `Energy.lean`. -/
theorem boundOk_sound {sP M tp tq : ℕ} (H : CertHolds P C xs) (h : boundOk P C xs sP M tp tq = true)
    (L : Labelling P.q C cls) (Ener : ℝ)
    (hE : dsum3 (fun i j k => tyC P C (typeOf xs (cls i) (cls j) (cls k)))
      ≤ 6 * (2 : ℝ) ^ (P.m * P.D + P.aP + sP) * Ener
        + 6 * ∑ i, rootS P C (cls i) (cls i) (cls i) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m)) :
    (tp : ℝ) / tq < Ener := by
  unfold boundOk at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨hM, htq⟩, hdiv⟩, hlt⟩ := h
  have hc := consts_eq (P := P) (xs := xs) L hM hdiv
  have hr := roots_eq H L
  rw [shl_one] at hlt
  have hlt' : bF P M * 2 ^ (P.m * P.D + P.aP + sP) * tp
        + tq * (sum3N (cTerm C xs M fun X => X.c2n) P.q + bR P M * sumN (fun a => C.n a * rootDiag P C a) P.q)
      < tq * (sum3N (cTerm C xs M fun X => X.c2p) P.q + bR P M * sumN (fun a => C.n a * rootNeg P) P.q) := hlt
  rw [bR_eq, bF_eq] at hlt'
  have hltR : (6 * (P.d.factorial : ℝ) * M) * 2 ^ (P.m * P.D + P.aP + sP) * tp
        + tq * ((sum3N (cTerm C xs M fun X => X.c2n) P.q : ℝ)
          + 6 * (P.d.factorial : ℝ) * M * 2 ^ (P.aF + 2 * P.m * P.d)
            * (sumN (fun a => C.n a * rootDiag P C a) P.q : ℝ))
      < tq * ((sum3N (cTerm C xs M fun X => X.c2p) P.q : ℝ)
          + 6 * (P.d.factorial : ℝ) * M * 2 ^ (P.aF + 2 * P.m * P.d)
            * (sumN (fun a => C.n a * rootNeg P) P.q : ℝ)) := by
    exact_mod_cast hlt'
  have hR0 : (2 : ℝ) ^ P.aF * ((2 : ℝ) ^ P.m) ^ P.d * ((2 : ℝ) ^ P.m) ^ P.d = 2 ^ (P.aF + 2 * P.m * P.d) := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [hR0] at hr
  have htqR : (0 : ℝ) < tq := Nat.cast_pos.mpr htq
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hfR : (0 : ℝ) < (P.d.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hU : (0 : ℝ) < 2 ^ (P.m * P.D + P.aP + sP) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hE (mul_pos hfR hMR).le
  rw [hc, hr] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 htqR.le
  rw [div_lt_iff₀ htqR]
  have hpos : (0 : ℝ) < 6 * (P.d.factorial : ℝ) * M * 2 ^ (P.m * P.D + P.aP + sP) := by positivity
  refine lt_of_mul_lt_mul_left ?_ hpos.le
  linarith

end Points

end CAP.Wsos
