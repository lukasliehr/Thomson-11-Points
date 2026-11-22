module

public import CAP.Wsos.BoundValue
public import N11.ParallelResearch1.Circ.TypedBound

/-!
# The bound of a typed certificate on the two-sphere as a number

`boundOk2_sound`: if `N11.Circ.boundOk2 P C xs sP M tp tq = true`, then every number `Ener` for which the typed
bound gives

    ∑ (constants of the triples of points) ≤ 6 * 2 ^ (m D + aP + sP) * Ener + 6 * ∑ (rooted forms at the root)

exceeds `tp / tq`. The proof follows `CAP.Wsos.boundOk_sound`: the sum of the constants over the triples of
points is a sum over the triples of classes (`consts2_eq`), and the rooted form of a class at the root is the
sum of the entries of the block `(Q, Q)` of its Gram matrix of degree `0` (`rootS2_diag`).
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

theorem shareOf2_mult (Q : ℕ) (C : Cert) (a b c : ℕ) : (shareOf2 Q C a b c).mult = smult C a b c := by
  unfold shareOf2 smult
  cases Nat.beq c (C.last a b) <;> rfl

/-- The constant of a triple type with the product of the multiplicities of its shares. -/
theorem tyC2_eq (P : Params) (Q : ℕ) (C : Cert) (X : TyX) :
    tyC2 P Q C X = ((X.c2p : ℝ) - (X.c2n : ℝ)) / (tmult C X : ℝ) := by
  have e : tmult C X = smult C X.a X.b X.c * smult C X.a X.c X.b * smult C X.b X.c X.a := rfl
  unfold tyC2
  rw [shareOf2_mult, shareOf2_mult, shareOf2_mult, e, Nat.cast_mul, Nat.cast_mul]

/-- The term of a triple of classes: `M` times the number of its triples of points times the constant of its
triple type is the difference of the two numbers of the checker. -/
theorem cTerm2_eq (P : Params) (Q : ℕ) (C : Cert) (xs : List TyX) {M : ℕ} (a b c : ℕ)
    (h : divOk C xs M a b c = true) :
    (M : ℝ) * ((C.n a : ℝ) * ((C.n b : ℝ) - (if b = a then 1 else 0)) * (mult C a b c : ℝ)
        * tyC2 P Q C (typeOf xs a b c))
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
    by_cases hμ : tmult C (typeOf xs a b c) = 0
    · have hM0 : M = 0 := by
        rw [hμ, Nat.mod_zero] at hmod
        exact hmod
      rw [tyC2_eq, hμ, hM0]
      simp
    · have hk : tmult C (typeOf xs a b c) * (M / tmult C (typeOf xs a b c)) = M :=
        Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)
      have hkR : (M : ℝ) = (tmult C (typeOf xs a b c) : ℝ) * ((M / tmult C (typeOf xs a b c) : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, hk]
      have hμR : ((tmult C (typeOf xs a b c) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hμ
      rw [tyC2_eq]
      have e0 : (tmult C (typeOf xs a b c) : ℝ)
          * ((((typeOf xs a b c).c2p : ℝ) - ((typeOf xs a b c).c2n : ℝ)) / (tmult C (typeOf xs a b c) : ℝ))
          = ((typeOf xs a b c).c2p : ℝ) - ((typeOf xs a b c).c2n : ℝ) := by
        field_simp
      calc (M : ℝ) * ((cnt C a b c : ℝ) * ((((typeOf xs a b c).c2p : ℝ) - ((typeOf xs a b c).c2n : ℝ))
              / (tmult C (typeOf xs a b c) : ℝ)))
          = (cnt C a b c : ℝ) * ((M / tmult C (typeOf xs a b c) : ℕ) : ℝ)
              * ((tmult C (typeOf xs a b c) : ℝ)
                * ((((typeOf xs a b c).c2p : ℝ) - ((typeOf xs a b c).c2n : ℝ)) / (tmult C (typeOf xs a b c) : ℝ))) := by
            rw [hkR]
            ring
        _ = (cnt C a b c : ℝ) * ((M / tmult C (typeOf xs a b c) : ℕ) : ℝ)
              * (((typeOf xs a b c).c2p : ℝ) - ((typeOf xs a b c).c2n : ℝ)) := by rw [e0]
        _ = _ := by ring

section Points

variable {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} {ι : Type*} [Fintype ι] [DecidableEq ι] {cls : ι → ℕ}

/-- **The sum of the constants over the triples of points**, multiplied by `M`. -/
theorem consts2_eq {M : ℕ} (L : Labelling P.q C cls) (hdiv : all3N (divOk C xs M) P.q = true) :
    (M : ℝ) * dsum3 (fun i j k => tyC2 P Q C (typeOf xs (cls i) (cls j) (cls k)))
      = (sum3N (cTerm C xs M fun X => X.c2p) P.q : ℝ) - (sum3N (cTerm C xs M fun X => X.c2n) P.q : ℝ) := by
  have h1 : dsum3 (fun i j k => tyC2 P Q C (typeOf xs (cls i) (cls j) (cls k)))
      = ∑ a ∈ range P.q, ∑ b ∈ range P.q, ∑ c ∈ range P.q,
          (C.n a : ℝ) * ((C.n b : ℝ) - (if b = a then 1 else 0)) * (mult C a b c : ℝ) * tyC2 P Q C (typeOf xs a b c) :=
    L.dsum3_cls (fun a b c => tyC2 P Q C (typeOf xs a b c))
  have hd : ∀ a ∈ range P.q, ∀ b ∈ range P.q, ∀ c ∈ range P.q, divOk C xs M a b c = true :=
    fun a ha b hb c hc => (all3N_iff _ _).mp hdiv a (mem_range.mp ha) b (mem_range.mp hb) c (mem_range.mp hc)
  rw [h1, sum3N_eq, sum3N_eq]
  simp only [Nat.cast_sum]
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun a ha => ?_
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun b hb => ?_
  rw [mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun c hc => cTerm2_eq P Q C xs a b c (hd a ha b hb c hc)

end Points

/-! ## The rooted forms at the root -/

theorem rootDiag2_eq (P : Params) (C : Cert) (a : ℕ) {Q : ℕ} (hQ : Q + 1 = P.q) :
    rootDiag2 P C a = ∑ j ∈ range (P.d + 1), ∑ i ∈ range (P.d + 1),
      slot P.wG (blockOf P ((C.gram a).getD 0 0) P.d Q Q) (P.q * (P.d + 1) * j + i) := by
  have e : Nat.pred P.q = Q := by
    rw [← hQ]
    rfl
  show linGo P.wG (mask P.wG) (P.d + 1) (P.wG * (P.q * (P.d + 1))) (rep 1 (P.d + 1))
    (blockOf P (hd (C.gram a)) P.d (Nat.pred P.q) (Nat.pred P.q)) 0 = _
  rw [e, linGo_eq, rep_length, zero_add, hd_eq]
  refine sum_congr rfl fun j hj => ?_
  rw [rep_getD 1 (P.d + 1) j (mem_range.mp hj), mul_one]

theorem bR2_eq (P : Params) (M : ℕ) : bR2 P M = 6 * M * 2 ^ (P.aF + 2 * P.m * P.d) := by
  show 6 * M * Nat.shiftLeft 1 (P.aF + 2 * P.m * P.d) = _
  rw [shl_one]

/-- The rooted form of a class at the root. -/
theorem rootS2_diag {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} (H : CertHolds2 P Q C xs) {a : ℕ} (ha : a < Q) :
    rootS2 P C a Q Q ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m)
      = 2 ^ P.aF * ((2 : ℝ) ^ P.m) ^ P.d * ((2 : ℝ) ^ P.m) ^ P.d
        * ((rootDiag2 P C a : ℝ) - (((P.d + 1) * (P.d + 1) * 2 ^ (P.wG - 1) : ℕ) : ℝ)) := by
  have hlen := H.gramLen a ha
  have h1 : 1 ≤ (⟨C.gram a, Q, Q⟩ : Rooted).gram.length := by
    show 1 ≤ (C.gram a).length
    omega
  unfold rootS2
  rw [rootedV2_root_first P ⟨C.gram a, Q, Q⟩ h1, linV_E, sum_sdig, ← rootDiag2_eq P C a H.root]
  ring

section Points

variable {P : Params} {Q : ℕ} {C : Cert} {xs : List TyX} {ι : Type*} [Fintype ι] [DecidableEq ι] {cls : ι → ℕ}

omit [DecidableEq ι] in
/-- **The sum of the rooted forms at the root.** -/
theorem roots2_eq (H : CertHolds2 P Q C xs) (L : Labelling P.q C cls) :
    ∑ i, rootS2 P C (cls i) Q Q ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m)
      = 2 ^ P.aF * ((2 : ℝ) ^ P.m) ^ P.d * ((2 : ℝ) ^ P.m) ^ P.d
        * ((sumN (fun a => C.n a * rootDiag2 P C a) P.q : ℝ) - (sumN (fun a => C.n a * rootNeg P) P.q : ℝ)) := by
  have h1 : (∑ i, rootS2 P C (cls i) Q Q ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m))
      = ∑ a ∈ range P.q, (C.n a : ℝ) * rootS2 P C a Q Q ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) :=
    L.sum_cls (fun a => rootS2 P C a Q Q ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m))
  rw [h1, sumN_eq, sumN_eq]
  simp only [Nat.cast_sum, Nat.cast_mul]
  rw [← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  rcases Nat.lt_or_ge a Q with haQ | haQ
  · rw [rootS2_diag H haQ, rootNeg_eq]
    ring
  · have haq : a = Q := by
      have h2 := mem_range.mp ha
      have h3 := H.root
      omega
    rw [haq, H.empty]
    simp

/-- **The bound of a certificate exceeds `tp / tq`.** `Ener` is any number for which the typed bound gives the
inequality `hE`. -/
theorem boundOk2_sound {sP M tp tq : ℕ} (H : CertHolds2 P Q C xs) (h : boundOk2 P C xs sP M tp tq = true)
    (L : Labelling P.q C cls) (Ener : ℝ)
    (hE : dsum3 (fun i j k => tyC2 P Q C (typeOf xs (cls i) (cls j) (cls k)))
      ≤ 6 * (2 : ℝ) ^ (P.m * P.D + P.aP + sP) * Ener
        + 6 * ∑ i, rootS2 P C (cls i) Q Q ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m)) :
    (tp : ℝ) / tq < Ener := by
  unfold boundOk2 at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨hM, htq⟩, hdiv⟩, hlt⟩ := h
  have hc := consts2_eq (P := P) (Q := Q) (xs := xs) L hdiv
  have hr := roots2_eq H L
  rw [shl_one] at hlt
  have hlt' : 6 * M * 2 ^ (P.m * P.D + P.aP + sP) * tp
        + tq * (sum3N (cTerm C xs M fun X => X.c2n) P.q + bR2 P M * sumN (fun a => C.n a * rootDiag2 P C a) P.q)
      < tq * (sum3N (cTerm C xs M fun X => X.c2p) P.q + bR2 P M * sumN (fun a => C.n a * rootNeg P) P.q) := hlt
  rw [bR2_eq] at hlt'
  have hltR : (6 * (M : ℝ)) * 2 ^ (P.m * P.D + P.aP + sP) * tp
        + tq * ((sum3N (cTerm C xs M fun X => X.c2n) P.q : ℝ)
          + 6 * (M : ℝ) * 2 ^ (P.aF + 2 * P.m * P.d)
            * (sumN (fun a => C.n a * rootDiag2 P C a) P.q : ℝ))
      < tq * ((sum3N (cTerm C xs M fun X => X.c2p) P.q : ℝ)
          + 6 * (M : ℝ) * 2 ^ (P.aF + 2 * P.m * P.d)
            * (sumN (fun a => C.n a * rootNeg P) P.q : ℝ)) := by
    exact_mod_cast hlt'
  have hR0 : (2 : ℝ) ^ P.aF * ((2 : ℝ) ^ P.m) ^ P.d * ((2 : ℝ) ^ P.m) ^ P.d = 2 ^ (P.aF + 2 * P.m * P.d) := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  rw [hR0] at hr
  have htqR : (0 : ℝ) < tq := Nat.cast_pos.mpr htq
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hU : (0 : ℝ) < 2 ^ (P.m * P.D + P.aP + sP) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hE hMR.le
  rw [hc, hr] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 htqR.le
  rw [div_lt_iff₀ htqR]
  have hpos : (0 : ℝ) < 6 * (M : ℝ) * 2 ^ (P.m * P.D + P.aP + sP) := by positivity
  refine lt_of_mul_lt_mul_left ?_ hpos.le
  linarith

end Points

end N11.Circ
