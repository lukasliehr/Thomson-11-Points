module

public import CAP.UniPos.PolySound
public import CAP.Wsos.Domain

/-!
# The sign conditions of a typed certificate

The pair polynomial of a pair type is `H (t) = Hs (t) / 2 ^ sP`, where `Hs` has the signed digits of the
number `C.H a b`. The sign condition of the source is `H (t) ≤ 1 / (2 - 2 t)` on the interval of the pair
type, that is, `(2 - 2 t) Hs (t) ≤ 2 ^ sP`.

`signOk_sound`: if the check `signOk` succeeds, then `(2 - 2 t) Hs (t) ≤ 2 ^ sP` for all `t` of the
interval. The interval may end at `1`: that an inner product of two distinct unit vectors is below `1` is
used where the potential is bounded (`pairH_le`). The witness is an instance of the checker `CAP.UniPos.checkPoly` for the polynomial
`p (y) = den ^ n (2 ^ sP - (2 - 2 y / den) Hs (y / den))`, `n = D + 1`. The check `linkAt` compares the
coefficients of the witness with the digits of the pair polynomial: with `h (-1) = h n = 0`,

  `p j = [j = 0] den ^ n 2 ^ sP - 2 den ^ (n - j) (h j - h (j - 1))`,

and `link_eval` sums these coefficients (`telescope`).

`Minorant` is the statement for all pair types that occur; `minorant_of_signs` derives it from `signsOk`.
-/

@[expose] public section

namespace CAP.Wsos

open Finset

theorem lastK_eq : ∀ (l : List ℕ) (prev : ℕ), lastK l prev = CAP.UniPos.lastCut prev l
  | [], _ => rfl
  | c :: l, _ => lastK_eq l c

/-! ## The digits of a pair polynomial -/

theorem hDig_le (P : Params) (H : ℕ) {j : ℕ} (h : j ≤ P.D) : hDig P H j = slot P.wP H j := by
  unfold hDig
  rw [Nat.ble_eq_true_of_le h]
  rfl

theorem hDig_top (P : Params) (H : ℕ) : hDig P H (P.D + 1) = 2 ^ (P.wP - 1) := by
  have hb : Nat.ble (P.D + 1) P.D = false := by
    cases hb : Nat.ble (P.D + 1) P.D with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true hb) (by omega)
  unfold hDig
  rw [hb]
  exact shl_one _

/-- The signed digit `j` of a pair polynomial as a real number; it vanishes at `D + 1`. -/
noncomputable def hReal (P : Params) (H j : ℕ) : ℝ := (hDig P H j : ℝ) - 2 ^ (P.wP - 1)

theorem hReal_le (P : Params) (H : ℕ) {j : ℕ} (h : j ≤ P.D) : hReal P H j = ((sdig P.wP H j : ℤ) : ℝ) := by
  unfold hReal sdig
  rw [hDig_le P H h, Int.cast_sub, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]

theorem hReal_top (P : Params) (H : ℕ) : hReal P H (P.D + 1) = 0 := by
  unfold hReal
  rw [hDig_top, Nat.cast_pow, Nat.cast_ofNat, sub_self]

/-- The polynomial with the signed digits of `H` at an inner product. -/
theorem spolyV_one (P : Params) (H : ℕ) (t : ℝ) :
    spolyV P.wP (1 : ℝ) t P.D H = ∑ i ∈ range (P.D + 1), hReal P H i * t ^ i := by
  unfold spolyV
  refine sum_congr rfl fun i hi => ?_
  rw [hReal_le P H (Nat.lt_succ_iff.mp (mem_range.mp hi))]
  unfold hpow
  rw [one_pow, one_mul]

/-- A polynomial of the checker at `E` times an inner product is `E ^ n` times its value. -/
theorem spolyV_hom (wd : ℕ) (E t : ℝ) (n c : ℕ) : spolyV wd E (E * t) n c = E ^ n * spolyV wd 1 t n c := by
  unfold spolyV
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have e : E ^ n = E ^ (n - i) * E ^ i := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp (mem_range.mp hi))]
  unfold hpow
  rw [one_pow, one_mul, mul_pow, e]
  ring

/-! ## The coefficients of the witness -/

theorem telescope (g : ℕ → ℝ) (t : ℝ) : ∀ n : ℕ,
    g 0 + ∑ i ∈ range n, (g (i + 1) - g i) * t ^ (i + 1) = (1 - t) * ∑ i ∈ range n, g i * t ^ i + g n * t ^ n
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, sum_range_succ, ← add_assoc, telescope g t n]
    ring

/-- **The polynomial of the witness.** -/
theorem link_eval {P : Params} {sP H : ℕ} {S : Sign} (hn : S.pp.n = P.D + 1)
    (hl : ∀ j < P.D + 2, linkAt P sP H S j = true) (t : ℝ) :
    CAP.UniPos.pEvalG S.pp S.Pp (S.den * t)
      = (S.den : ℝ) ^ (P.D + 1) * (2 ^ sP - (2 - 2 * t) * spolyV P.wP (1 : ℝ) t P.D H) := by
  -- the conditions of the check as equations between natural numbers
  have e0 : slot S.pp.W S.Pp 0 + 2 * S.den ^ (P.D + 1 - 0) * hDig P H 0
      = Nat.shiftLeft 1 (S.pp.aH - 1) + 2 * S.den ^ (P.D + 1 - 0) * Nat.shiftLeft 1 (P.wP - 1)
        + Nat.shiftLeft (S.den ^ (P.D + 1)) sP := Nat.eq_of_beq_eq_true (hl 0 (by omega))
  have es : ∀ i < P.D + 1, slot S.pp.W S.Pp (i + 1) + 2 * S.den ^ (P.D + 1 - (i + 1)) * hDig P H (i + 1)
      = Nat.shiftLeft 1 (S.pp.aH - 1) + 2 * S.den ^ (P.D + 1 - (i + 1)) * hDig P H i + 0 :=
    fun i hi => Nat.eq_of_beq_eq_true (hl (i + 1) (by omega))
  rw [shl_one, shl_one, shl_eq, Nat.sub_zero] at e0
  -- the coefficients as real numbers
  have c0 : ((CAP.UniPos.coefZG S.pp S.Pp 0 : ℤ) : ℝ) = (S.den : ℝ) ^ (P.D + 1) * (2 ^ sP - 2 * hReal P H 0) := by
    have e0' : (slot S.pp.W S.Pp 0 : ℝ) + 2 * (S.den : ℝ) ^ (P.D + 1) * (hDig P H 0 : ℝ)
        = 2 ^ (S.pp.aH - 1) + 2 * (S.den : ℝ) ^ (P.D + 1) * 2 ^ (P.wP - 1) + (S.den : ℝ) ^ (P.D + 1) * 2 ^ sP := by
      exact_mod_cast e0
    unfold CAP.UniPos.coefZG hReal
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
    linear_combination e0'
  have cs : ∀ i < P.D + 1, ((CAP.UniPos.coefZG S.pp S.Pp (i + 1) : ℤ) : ℝ)
      = -(2 * (S.den : ℝ) ^ (P.D - i) * (hReal P H (i + 1) - hReal P H i)) := by
    intro i hi
    have e := es i hi
    rw [shl_one, Nat.add_sub_add_right, Nat.add_zero] at e
    have e' : (slot S.pp.W S.Pp (i + 1) : ℝ) + 2 * (S.den : ℝ) ^ (P.D - i) * (hDig P H (i + 1) : ℝ)
        = 2 ^ (S.pp.aH - 1) + 2 * (S.den : ℝ) ^ (P.D - i) * (hDig P H i : ℝ) := by
      exact_mod_cast e
    unfold CAP.UniPos.coefZG hReal
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
    linear_combination e'
  -- the sum
  have hterm : ∀ i ∈ range (P.D + 1), ((CAP.UniPos.coefZG S.pp S.Pp (i + 1) : ℤ) : ℝ) * ((S.den : ℝ) * t) ^ (i + 1)
      = -(2 * (S.den : ℝ) ^ (P.D + 1)) * ((hReal P H (i + 1) - hReal P H i) * t ^ (i + 1)) := by
    intro i hi
    have hi' : i < P.D + 1 := mem_range.mp hi
    have ep : (S.den : ℝ) ^ (P.D + 1) = (S.den : ℝ) ^ (P.D - i) * (S.den : ℝ) ^ (i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [cs i hi', mul_pow, ep]
    ring
  have htel := telescope (hReal P H) t (P.D + 1)
  rw [hReal_top, zero_mul, add_zero] at htel
  unfold CAP.UniPos.pEvalG
  rw [hn, sum_range_succ', sum_congr rfl hterm, ← mul_sum, c0, spolyV_one]
  linear_combination -(2 * (S.den : ℝ) ^ (P.D + 1)) * htel

/-! ## The sign condition of a pair type -/

/-- **Soundness of the check of a sign condition.** -/
theorem signOk_sound {P : Params} {sP H : ℕ} {I : Ival} {S : Sign} (h : signOk P sP H I S = true) (t : ℝ)
    (h1 : I.lo ≤ t) (h2 : t ≤ I.hi) :
    (2 - 2 * t) * spolyV P.wP (1 : ℝ) t P.D H ≤ 2 ^ sP := by
  unfold signOk at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hchk, hn⟩, hl⟩, hden⟩, hld⟩, hhd⟩, hlo⟩, hhi⟩ := h
  have hn' : S.pp.n = P.D + 1 := Nat.eq_of_beq_eq_true hn
  have hl' : ∀ j < P.D + 2, linkAt P sP H S j = true := (allN_iff _ _).mp hl
  have hldR : (0 : ℝ) < I.ld := Nat.cast_pos.mpr hld
  have hhdR : (0 : ℝ) < I.hd := Nat.cast_pos.mpr hhd
  have hdenR : (0 : ℝ) < S.den := Nat.cast_pos.mpr hden
  have h1' : (I.lp : ℝ) - (I.ln : ℝ) ≤ t * I.ld := (div_le_iff₀ hldR).mp h1
  have h2' : t * I.hd ≤ (I.hp : ℝ) - (I.hn : ℝ) := (le_div_iff₀ hhdR).mp h2
  have hs : (0 : ℝ) < 2 ^ S.pp.s := by positivity
  -- the interval of the witness contains `den * t`
  rw [shl_eq] at hlo hhi
  rw [lastK_eq] at hhi
  have hlo' : I.ld * S.c0 + S.den * 2 ^ S.pp.s * I.ln ≤ I.ld * S.pp.off + S.den * 2 ^ S.pp.s * I.lp := hlo
  have hhi' : S.den * 2 ^ S.pp.s * I.hp + I.hd * S.pp.off
      ≤ I.hd * CAP.UniPos.lastCut S.c0 S.cuts + S.den * 2 ^ S.pp.s * I.hn := hhi
  have hloR : (I.ld : ℝ) * S.c0 + S.den * 2 ^ S.pp.s * I.ln ≤ I.ld * S.pp.off + S.den * 2 ^ S.pp.s * I.lp := by
    exact_mod_cast hlo'
  have hhiR : (S.den : ℝ) * 2 ^ S.pp.s * I.hp + I.hd * S.pp.off
      ≤ I.hd * (CAP.UniPos.lastCut S.c0 S.cuts : ℝ) + S.den * 2 ^ S.pp.s * I.hn := by
    exact_mod_cast hhi'
  have hm : (0 : ℝ) ≤ S.den * 2 ^ S.pp.s := (mul_pos hdenR hs).le
  have m1 := mul_le_mul_of_nonneg_left h1' hm
  have m2 := mul_le_mul_of_nonneg_left h2' hm
  have hy1 : ((S.c0 : ℝ) - S.pp.off) / 2 ^ S.pp.s ≤ S.den * t := by
    rw [div_le_iff₀ hs]
    have g : ((S.c0 : ℝ) - S.pp.off) * I.ld ≤ (S.den * t * 2 ^ S.pp.s) * I.ld := by linarith
    exact le_of_mul_le_mul_right g hldR
  have hy2 : S.den * t ≤ ((CAP.UniPos.lastCut S.c0 S.cuts : ℝ) - S.pp.off) / 2 ^ S.pp.s := by
    rw [le_div_iff₀ hs]
    have g : (S.den * t * 2 ^ S.pp.s) * I.hd ≤ ((CAP.UniPos.lastCut S.c0 S.cuts : ℝ) - S.pp.off) * I.hd := by
      linarith
    exact le_of_mul_le_mul_right g hhdR
  have hp := (CAP.UniPos.checkPoly_sound S.pp S.Pp S.c0 S.cuts hchk (S.den * t) hy1 hy2).1
  rw [link_eval hn' hl' t] at hp
  have hq := nonneg_of_mul_nonneg_right hp (pow_pos hdenR (P.D + 1))
  linarith

/-- The sign conditions of a certificate: on the interval of every pair type that occurs, the pair
polynomial is at most `1 / (2 - 2 t)`, in the form `(2 - 2 t) * Hs t ≤ 2 ^ sP`. -/
def Minorant (P : Params) (C : Cert) (Dm : Dom) (sP : ℕ) : Prop :=
  ∀ a < P.q, ∀ b < P.q, a ≤ b → 0 < pcnt C a b → ∀ t : ℝ, (Dm.iv a b).lo ≤ t → t ≤ (Dm.iv a b).hi →
    (2 - 2 * t) * spolyV P.wP (1 : ℝ) t P.D (C.H a b) ≤ 2 ^ sP

theorem minorant_of_signs {P : Params} {C : Cert} {Dm : Dom} {sP : ℕ} {sg : ℕ → ℕ → Sign}
    (h : signsOk P C Dm sP sg = true) : Minorant P C Dm sP := by
  intro a ha b hb hab hp t h1 h2
  have h' : (Nat.blt b a || Nat.beq (pcnt C a b) 0 || signOk P sP (C.H a b) (Dm.iv a b) (sg a b)) = true :=
    (all2N_iff _ _).mp h a ha b hb
  rw [Bool.or_eq_true, Bool.or_eq_true] at h'
  rcases h' with (h' | h') | h'
  · rw [Nat.blt_eq] at h'
    omega
  · exact absurd (Nat.eq_of_beq_eq_true h') hp.ne'
  · exact signOk_sound h' t h1 h2

end CAP.Wsos
