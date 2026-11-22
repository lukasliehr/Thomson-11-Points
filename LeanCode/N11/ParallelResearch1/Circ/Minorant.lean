module

public import CAP.UniPos.Sound
public import CAP.Wsos.Minorant
public import N11.ParallelResearch1.Circ.Domain

/-!
# The sign conditions of a typed certificate on the two-sphere

`signOk2_sound`: if `N11.Circ.signOk2 P sP H I S = true` and `2 ≤ D`, then for `t` in the interval `I`, `t < 1`,

    K t + pen t ≤ 1 / √(2 - 2 t),

where `K t = (∑ j, (signed digit j of H) t ^ j) / 2 ^ sP` is the pair polynomial and `pen` the polynomial of
degree two of the witness (`Pen.val`). The witness is the polynomial `Dn (K + pen)`, `Dn = 2 ^ sP * sc`, in the
form of `CAP.UniPos`; the pieces between its cut points cover the interval (`cutsGo2_cover`), and on a piece
`CAP.UniPos.interval_bound` gives `(2 - 2 t) (Dn (K + pen)) ² ≤ Dn²`.
-/

@[expose] public section

namespace N11.Circ

open Finset CAP CAP.Wsos

/-- The value of the polynomial `pen` of a pair type, with the denominator `Dn`. -/
noncomputable def Pen.val (p : Pen) (Dn : ℝ) (t : ℝ) : ℝ :=
  (((p.a0p : ℝ) - (p.a0n : ℝ)) + ((p.a1p : ℝ) - (p.a1n : ℝ)) * t + ((p.a2p : ℝ) - (p.a2n : ℝ)) * t ^ 2) / Dn

theorem penP_ge (p : Pen) {j : ℕ} (h : 3 ≤ j) : penP p j = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
  rfl

theorem penN_ge (p : Pen) {j : ℕ} (h : 3 ≤ j) : penN p j = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 3 := ⟨j - 3, by omega⟩
  rfl

/-! ## The test `Ĥ ≤ 0` of a piece -/

open CAP.UniPos in
theorem negOk_coeff (pp : CAP.UniPos.Params) (Hp lk lk1 : ℕ) (hV : 1 ≤ pp.V) (h : negOk pp Hp lk lk1 = true) :
    ∀ i, (hbP pp Hp lk lk1).1.coeff i ≤ (hbP pp Hp lk lk1).2.coeff i := by
  have h0 : (Nat.blt (hornerGo pp 0 Hp lk lk1 (2 * pp.D + 1) 0 0 1).1 (1 <<< (pp.V - 1))
      && Nat.blt (hornerGo pp 0 Hp lk lk1 (2 * pp.D + 1) 0 0 1).2 (1 <<< (pp.V - 1))
      && geTest pp.V (2 * pp.D + 2) (hornerGo pp pp.V Hp lk lk1 (2 * pp.D + 1) 0 0 1).2
          (hornerGo pp pp.V Hp lk lk1 (2 * pp.D + 1) 0 0 1).1) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, Nat.one_shiftLeft, hornerGo_top, hornerGo_top,
    pow_zero] at h0
  obtain ⟨⟨hb1, hb2⟩, hg⟩ := h0
  obtain ⟨d1, d2⟩ := natDegree_hbP pp Hp lk lk1
  have d1' : (hbP pp Hp lk lk1).1.natDegree < 2 * pp.D + 2 := by omega
  have d2' : (hbP pp Hp lk lk1).2.natDegree < 2 * pp.D + 2 := by omega
  have hg' : geTest pp.V (2 * pp.D + 2) (packSum pp.V (2 * pp.D + 2) (hbP pp Hp lk lk1).2.coeff)
      (packSum pp.V (2 * pp.D + 2) (hbP pp Hp lk lk1).1.coeff) = true := by
    rw [← eval_two_pow pp.V _ _ d2', ← eval_two_pow pp.V _ _ d1']
    exact hg
  have key := geTest_sound pp.V (2 * pp.D + 2) _ _ hV
    (fun i _ => lt_of_le_of_lt (coeff_le_eval_one _ i) hb2)
    (fun i _ => lt_of_le_of_lt (coeff_le_eval_one _ i) hb1) hg'
  intro i
  by_cases hi : i < 2 * pp.D + 2
  · exact key i hi
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le d1' (not_lt.mp hi))]
    exact Nat.zero_le _

open CAP.UniPos in
/-- On a piece that `negOk` accepts, `Ĥ (t) ≤ 0`. -/
theorem negOk_sound (pp : CAP.UniPos.Params) (Hp lk lk1 : ℕ) (hV : 1 ≤ pp.V) (h : negOk pp Hp lk lk1 = true)
    (t : ℝ) (h1 : (lk1 : ℝ) < 2 ^ pp.s * (1 - t)) (h2 : 2 ^ pp.s * (1 - t) ≤ lk) : hEval pp Hp t ≤ 0 := by
  have hδ : 0 < 2 ^ pp.s * (1 - t) - lk1 := sub_pos.mpr h1
  have hy : 0 ≤ ((lk : ℝ) - 2 ^ pp.s * (1 - t)) / (2 ^ pp.s * (1 - t) - lk1) :=
    div_nonneg (sub_nonneg.mpr h2) hδ.le
  have hmono := rv_mono _ hy _ _ (negOk_coeff pp Hp lk lk1 hV h)
  have hb := hbP_rv pp Hp lk lk1 (((lk : ℝ) - 2 ^ pp.s * (1 - t)) / (2 ^ pp.s * (1 - t) - lk1))
  rw [rv_L2, rv_Mf] at hb
  generalize hyd : ((lk : ℝ) - 2 ^ pp.s * (1 - t)) / (2 ^ pp.s * (1 - t) - lk1) = y at hb hy hmono
  have hm : (lk : ℝ) + lk1 * y = 2 ^ pp.s * (1 + y) * (1 - t) := by
    rw [← hyd]
    field_simp
    ring
  have hpos : (0 : ℝ) < 2 ^ pp.s * (1 + y) := by positivity
  have hsub : (2 : ℝ) ^ pp.s * (1 + y) - ((lk : ℝ) + lk1 * y) = 2 ^ pp.s * (1 + y) * t := by
    rw [hm]
    ring
  have hsum : ∑ d ∈ range (2 * pp.D + 1), (coefZ pp Hp d : ℝ) * (2 ^ pp.s * (1 + y) * t) ^ d
        * (2 ^ pp.s * (1 + y)) ^ (2 * pp.D - d)
      = (2 ^ pp.s * (1 + y)) ^ (2 * pp.D) * hEval pp Hp t := by
    unfold hEval
    rw [mul_sum]
    refine sum_congr rfl fun d hd => ?_
    have hd' : d ≤ 2 * pp.D := Nat.lt_succ_iff.mp (mem_range.mp hd)
    have e : (2 ^ pp.s * (1 + y)) ^ (2 * pp.D) = (2 ^ pp.s * (1 + y)) ^ d * (2 ^ pp.s * (1 + y)) ^ (2 * pp.D - d) := by
      rw [← pow_add, Nat.add_sub_of_le hd']
    rw [e, mul_pow]
    ring
  rw [hsub, hsum] at hb
  have h3 : (2 ^ pp.s * (1 + y)) ^ (2 * pp.D) * hEval pp Hp t ≤ (2 ^ pp.s * (1 + y)) ^ (2 * pp.D) * 0 := by
    rw [mul_zero, ← hb]
    linarith
  exact le_of_mul_le_mul_left h3 (pow_pos hpos _)

/-- The pieces of the cuts cover the numbers between the last cut and the first one; each piece is accepted by
one of the two tests. -/
theorem cutsGo2_cover (pp : CAP.UniPos.Params) (Hp Dn : ℕ) : ∀ (l : List ℕ) (prev : ℕ), cutsGo2 pp Hp Dn l prev = true →
    ∀ μ : ℝ, ((lastCut2 l prev : ℕ) : ℝ) < μ → μ ≤ prev →
      ∃ lk lk1 : ℕ, (CAP.UniPos.intervalOk pp Hp Dn lk lk1 = true ∨ negOk pp Hp lk lk1 = true)
        ∧ (lk1 : ℝ) < μ ∧ μ ≤ lk
  | [], prev, _, μ, h0, h1 => by
    have e : lastCut2 [] prev = prev := rfl
    rw [e] at h0
    exact absurd h1 (not_le.mpr h0)
  | c :: l, prev, h, μ, h0, h1 => by
    have h' : (Nat.blt (c / 2) prev
        && cond (Nat.beq (c % 2) 0) (CAP.UniPos.intervalOk pp Hp Dn prev (c / 2)) (negOk pp Hp prev (c / 2))
        && cutsGo2 pp Hp Dn l (c / 2)) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h'
    by_cases hμ : ((c / 2 : ℕ) : ℝ) < μ
    · refine ⟨prev, c / 2, ?_, hμ, h1⟩
      have h2 := h'.1.2
      cases hb : Nat.beq (c % 2) 0 with
      | true =>
        rw [hb] at h2
        exact Or.inl h2
      | false =>
        rw [hb] at h2
        exact Or.inr h2
    · have e : lastCut2 (c :: l) prev = lastCut2 l (c / 2) := rfl
      rw [e] at h0
      exact cutsGo2_cover pp Hp Dn l (c / 2) h'.2 μ h0 (not_lt.mp hμ)

/-- The coefficient `j` of the witness. -/
theorem linkAt2_real {P : Params} {H : ℕ} {S : Sign2} {j : ℕ} (h : linkAt2 P H S j = true) :
    ((CAP.UniPos.coefZ S.pp S.Hp j : ℤ) : ℝ)
      = (S.sc : ℝ) * ((sdig P.wP H j : ℤ) : ℝ) + ((penP S.pen j : ℝ) - (penN S.pen j : ℝ)) := by
  have h' := Nat.eq_of_beq_eq_true h
  have e1 : Nat.shiftLeft 1 (Nat.pred P.wP) = 2 ^ (P.wP - 1) := shl_one _
  have e2 : Nat.shiftLeft 1 (Nat.pred S.pp.aH) = 2 ^ (S.pp.aH - 1) := shl_one _
  rw [e1, e2] at h'
  have h'' : slot S.pp.W S.Hp j + S.sc * 2 ^ (P.wP - 1) + penN S.pen j
      = S.sc * slot P.wP H j + penP S.pen j + 2 ^ (S.pp.aH - 1) := h'
  have hR : ((slot S.pp.W S.Hp j : ℕ) : ℝ) + (S.sc : ℝ) * 2 ^ (P.wP - 1) + (penN S.pen j : ℝ)
      = (S.sc : ℝ) * ((slot P.wP H j : ℕ) : ℝ) + (penP S.pen j : ℝ) + 2 ^ (S.pp.aH - 1) := by
    exact_mod_cast h''
  unfold CAP.UniPos.coefZ sdig
  push_cast
  linear_combination hR

/-- The sum of the coefficients of `Dn * pen`. -/
theorem pen_sum (p : Pen) {D : ℕ} (hD : 2 ≤ D) (t : ℝ) :
    ∑ j ∈ range (D + 1), ((penP p j : ℝ) - (penN p j : ℝ)) * t ^ j
      = ((p.a0p : ℝ) - (p.a0n : ℝ)) + ((p.a1p : ℝ) - (p.a1n : ℝ)) * t + ((p.a2p : ℝ) - (p.a2n : ℝ)) * t ^ 2 := by
  obtain ⟨r, hr⟩ : ∃ r, D + 1 = 3 + r := ⟨D - 2, by omega⟩
  rw [hr, sum_range_add]
  have htail : ∑ x ∈ range r, ((penP p (3 + x) : ℝ) - (penN p (3 + x) : ℝ)) * t ^ (3 + x) = 0 := by
    refine sum_eq_zero fun x _ => ?_
    rw [penP_ge p (by omega), penN_ge p (by omega)]
    simp
  rw [htail, add_zero, sum_range_succ, sum_range_succ, sum_range_one]
  have e0 : penP p 0 = p.a0p := rfl
  have e1 : penP p 1 = p.a1p := rfl
  have e2 : penP p 2 = p.a2p := rfl
  have f0 : penN p 0 = p.a0n := rfl
  have f1 : penN p 1 = p.a1n := rfl
  have f2 : penN p 2 = p.a2n := rfl
  rw [e0, e1, e2, f0, f1, f2]
  ring

/-- **Soundness of the sign condition of a pair type.** -/
theorem signOk2_sound {P : Params} {sP H : ℕ} {I : Ival} {S : Sign2} (hD2 : 2 ≤ P.D) (h : signOk2 P sP H I S = true)
    (t : ℝ) (h1 : I.lo ≤ t) (h2 : t ≤ I.hi) (ht : t < 1) :
    spolyV P.wP (1 : ℝ) t P.D H / 2 ^ sP + S.pen.val (2 ^ sP * (S.sc : ℝ)) t ≤ 1 / Real.sqrt (2 - 2 * t) := by
  unfold signOk2 at h
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, nat_beq_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hV, hD⟩, hsc⟩, hld⟩, hhd⟩, hlink⟩, hcuts⟩, hlo⟩, hhi⟩ := h
  have hD' : 2 * S.pp.D = P.D := hD
  rw [shl_one] at hcuts
  have hcuts' : cutsGo2 S.pp S.Hp (2 ^ sP * S.sc) S.cuts S.lam0 = true := hcuts
  rw [shl_one] at hlo hhi
  have hlo' : 2 ^ S.pp.s * (I.ld + I.ln) ≤ S.lam0 * I.ld + 2 ^ S.pp.s * I.lp := hlo
  have hhi' : lastCut2 S.cuts S.lam0 * I.hd + 2 ^ S.pp.s * I.hp < 2 ^ S.pp.s * (I.hd + I.hn) := hhi
  have hloR : (2 : ℝ) ^ S.pp.s * ((I.ld : ℝ) + (I.ln : ℝ)) ≤ (S.lam0 : ℝ) * (I.ld : ℝ) + 2 ^ S.pp.s * (I.lp : ℝ) := by
    exact_mod_cast hlo'
  have hhiR : ((lastCut2 S.cuts S.lam0 : ℕ) : ℝ) * (I.hd : ℝ) + 2 ^ S.pp.s * (I.hp : ℝ)
      < (2 : ℝ) ^ S.pp.s * ((I.hd : ℝ) + (I.hn : ℝ)) := by
    exact_mod_cast hhi'
  have hldR : (0 : ℝ) < (I.ld : ℝ) := Nat.cast_pos.mpr hld
  have hhdR : (0 : ℝ) < (I.hd : ℝ) := Nat.cast_pos.mpr hhd
  have hE : (0 : ℝ) < (2 : ℝ) ^ S.pp.s := by positivity
  have h1' : (I.lp : ℝ) - (I.ln : ℝ) ≤ t * (I.ld : ℝ) := by
    unfold Ival.lo at h1
    rwa [div_le_iff₀ hldR] at h1
  have h2' : t * (I.hd : ℝ) ≤ (I.hp : ℝ) - (I.hn : ℝ) := by
    unfold Ival.hi at h2
    rwa [le_div_iff₀ hhdR] at h2
  -- the piece of `μ = 2 ^ s (1 - t)`
  have hμ1 : (2 : ℝ) ^ S.pp.s * (1 - t) ≤ (S.lam0 : ℝ) := by
    have a1 := mul_le_mul_of_nonneg_left h1' hE.le
    refine le_of_mul_le_mul_right ?_ hldR
    nlinarith
  have hμ0 : ((lastCut2 S.cuts S.lam0 : ℕ) : ℝ) < (2 : ℝ) ^ S.pp.s * (1 - t) := by
    have a2 := mul_le_mul_of_nonneg_left h2' hE.le
    refine lt_of_mul_lt_mul_right ?_ hhdR.le
    nlinarith
  obtain ⟨lk, lk1, hok, hl, hu⟩ := cutsGo2_cover S.pp S.Hp (2 ^ sP * S.sc) S.cuts S.lam0 hcuts' _ hμ0 hμ1
  have hpos : (0 : ℝ) < 2 - 2 * t := by linarith
  have hDnR : (((2 ^ sP * S.sc : ℕ)) : ℝ) = 2 ^ sP * (S.sc : ℝ) := by push_cast; ring
  have hbd : CAP.UniPos.hEval S.pp S.Hp t ≤ 2 ^ sP * (S.sc : ℝ) / Real.sqrt (2 - 2 * t) := by
    rcases hok with hok | hok
    · have hb := CAP.UniPos.interval_bound S.pp S.Hp (2 ^ sP * S.sc) lk lk1 hV hok t hl hu
      have hbd := CAP.UniPos.le_div_sqrt hpos (Nat.cast_nonneg (2 ^ sP * S.sc)) hb
      rw [hDnR] at hbd
      exact hbd
    · have hneg := negOk_sound S.pp S.Hp lk lk1 hV hok t hl hu
      have hsq : (0 : ℝ) < Real.sqrt (2 - 2 * t) := Real.sqrt_pos.mpr hpos
      have hnn : (0 : ℝ) ≤ 2 ^ sP * (S.sc : ℝ) / Real.sqrt (2 - 2 * t) := by positivity
      linarith
  -- the value of the witness
  have hval : CAP.UniPos.hEval S.pp S.Hp t
      = (S.sc : ℝ) * spolyV P.wP (1 : ℝ) t P.D H
        + (((S.pen.a0p : ℝ) - (S.pen.a0n : ℝ)) + ((S.pen.a1p : ℝ) - (S.pen.a1n : ℝ)) * t
          + ((S.pen.a2p : ℝ) - (S.pen.a2n : ℝ)) * t ^ 2) := by
    unfold CAP.UniPos.hEval
    rw [hD', ← pen_sum S.pen hD2 t]
    unfold spolyV
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [linkAt2_real ((allN_iff _ _).mp hlink j (mem_range.mp hj))]
    unfold hpow
    rw [one_pow, one_mul]
    ring
  have hscR : (0 : ℝ) < (S.sc : ℝ) := Nat.cast_pos.mpr hsc
  have h2ne : ((2 : ℝ) ^ sP) ≠ 0 := by positivity
  have hDnpos : (0 : ℝ) < 2 ^ sP * (S.sc : ℝ) := by positivity
  have e : spolyV P.wP (1 : ℝ) t P.D H / 2 ^ sP + S.pen.val (2 ^ sP * (S.sc : ℝ)) t
      = CAP.UniPos.hEval S.pp S.Hp t / (2 ^ sP * (S.sc : ℝ)) := by
    rw [hval]
    unfold Pen.val
    rw [div_add_div _ _ h2ne hDnpos.ne', div_eq_div_iff (mul_ne_zero h2ne hDnpos.ne') hDnpos.ne']
    ring
  rw [e, div_le_iff₀ hDnpos]
  calc CAP.UniPos.hEval S.pp S.Hp t ≤ 2 ^ sP * (S.sc : ℝ) / Real.sqrt (2 - 2 * t) := hbd
    _ = 1 / Real.sqrt (2 - 2 * t) * (2 ^ sP * (S.sc : ℝ)) := by ring

/-- The sign conditions of a certificate: on the interval of every pair type that occurs, the pair polynomial
plus the polynomial `pen` of the pair type is at most the Coulomb potential. -/
def Minorant2 (P : Params) (C : Cert) (Dm : Dom) (sP : ℕ) (sg : ℕ → ℕ → Sign2) : Prop :=
  ∀ a < P.q, ∀ b < P.q, a ≤ b → 0 < pcnt C a b → ∀ t : ℝ, (Dm.iv a b).lo ≤ t → t ≤ (Dm.iv a b).hi → t < 1 →
    spolyV P.wP (1 : ℝ) t P.D (C.H a b) / 2 ^ sP + (sg a b).pen.val (2 ^ sP * ((sg a b).sc : ℝ)) t
      ≤ 1 / Real.sqrt (2 - 2 * t)

theorem minorant2_of_signs {P : Params} {C : Cert} {Dm : Dom} {sP : ℕ} {sg : ℕ → ℕ → Sign2} (hD2 : 2 ≤ P.D)
    (h : signsOk2 P C Dm sP sg = true) : Minorant2 P C Dm sP sg := by
  intro a ha b hb hab hp t h1 h2 ht
  unfold signsOk2 at h
  have h' := (all2N_iff _ _).mp h a ha b hb
  rw [Bool.or_eq_true, Bool.or_eq_true] at h'
  rcases h' with (h' | h') | h'
  · rw [Nat.blt_eq] at h'
    omega
  · exact absurd (Nat.eq_of_beq_eq_true h') hp.ne'
  · exact signOk2_sound hD2 h' t h1 h2 ht

/-! ## Witnesses without a polynomial `pen` -/

theorem penZero_val {p : Pen} (h : penZero p = true) (Dn t : ℝ) : p.val Dn t = 0 := by
  unfold penZero at h
  simp only [Bool.and_eq_true, nat_beq_iff] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  unfold Pen.val
  rw [h0, h1, h2, h3, h4, h5]
  simp

theorem pensZero_nth : ∀ (l : List Sign2), pensZero l = true → ∀ i : ℕ, penZero (nthS l i).pen = true
  | [], _, _ => rfl
  | S :: l, h, i => by
    have h' : (penZero S.pen && pensZero l) = true := h
    rw [Bool.and_eq_true] at h'
    cases i with
    | zero => exact h'.1
    | succ i => exact pensZero_nth l h'.2 i

/-- If no witness of the table has a polynomial `pen`, the polynomial `pen` of every pair type vanishes. -/
theorem pensZero_val {l : List Sign2} (h : pensZero l = true) (q a b : ℕ) (Dn t : ℝ) :
    (signOf2 q l a b).pen.val Dn t = 0 :=
  penZero_val (pensZero_nth l h _) Dn t

end N11.Circ
