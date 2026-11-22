module

public import CAP.Wsos.Shares
public import N11.ParallelResearch1.Circ.Value

/-!
# The numbers of the checker stand for the polynomials of the data: the kernels of the circle

`rootedVal2_rep`: the number `N11.Circ.rootedVal2` stands for the polynomial `N11.Circ.rootedV2`, and
`rootedV2_bd`: the coefficients of this polynomial are bounded by `N11.Circ.nRooted2`. The proofs follow
`CAP/Wsos/Rooted.lean` and `CAP/Wsos/Shares.lean`; the loop over the Gram matrices (`rootedGo_rep`) and the
bounds of the bilinear forms are those of the library.
-/

@[expose] public section

namespace N11.Circ

open Finset MvPolynomial CAP CAP.Wsos

variable {P : Params} {pM mM : ℕ}

/-! ## The kernels -/

theorem qnext2_rep (hM : Mod P pM mM) {Ah Wh prev cur : ℕ} {AhP WhP pP cP : Poly} (hA : Rep P Ah AhP)
    (hW : Rep P Wh WhP) (hp : Rep P prev pP) (hc : Rep P cur cP) (k : ℕ) :
    Rep P (qnext2 pM mM Ah Wh k prev cur) (((cf k : ℕ) : Poly) * AhP * cP - WhP * pP) := by
  have h1 : Rep P (cf k * mulM mM Ah cur) (C ((cf k : ℕ) : ℤ) * (AhP * cP)) := Rep.smul _ (hA.mulM hM hc)
  have h2 : Rep P (mulM mM Wh prev) (WhP * pP) := hW.mulM hM hp
  refine ((h1.subM hM h2).land hM).congr ?_
  rw [C_natCast']
  ring

theorem ql2_succ (Ah Wh n k prev cur : ℕ) :
    ql2 pM mM Ah Wh (n + 1) k prev cur = cur :: ql2 pM mM Ah Wh n (Nat.succ k) cur (qnext2 pM mM Ah Wh k prev cur) :=
  rfl

theorem ql2_rep (hM : Mod P pM mM) {Ah Wh : ℕ} {AhP WhP : Poly} (hA : Rep P Ah AhP) (hW : Rep P Wh WhP) :
    ∀ (n k prev cur : ℕ), Rep P prev (qPair2 AhP WhP k).1 → Rep P cur (qPair2 AhP WhP k).2 →
      (ql2 pM mM Ah Wh n k prev cur).length = n ∧
      ∀ i, i < n → Rep P ((ql2 pM mM Ah Wh n k prev cur).getD i 0) (qV2 AhP WhP (k + i))
  | 0, _, _, _, _, _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1, k, prev, cur, hp, hc => by
    have ih := ql2_rep hM hA hW n (k + 1) cur (qnext2 pM mM Ah Wh k prev cur) hc (qnext2_rep hM hA hW hp hc k)
    rw [ql2_succ]
    refine ⟨by rw [List.length_cons, ih.1], fun i hi => ?_⟩
    cases i with
    | zero => exact hc
    | succ j =>
      rw [List.getD_cons_succ]
      have := ih.2 j (Nat.lt_of_succ_lt_succ hi)
      rwa [show k + 1 + j = k + (j + 1) by omega] at this

theorem qlist2_rep (hM : Mod P pM mM) {w1 w2 w3 : ℕ} {W1 W2 W3 : Poly} (h1 : Rep P w1 W1) (h2 : Rep P w2 W2)
    (h3 : Rep P w3 W3) :
    (qlist2 P pM mM w1 w2 w3).length = P.d + 1 ∧
    ∀ i, i < P.d + 1 → Rep P ((qlist2 P pM mM w1 w2 w3).getD i 0) (qV2 (AhV (EP P) W1 W2 W3) (WhV (EP P) W1 W2) i) := by
  have := ql2_rep hM (AhV_rep hM h1 h2 h3) (WhV_rep hM h1 h2) (P.d + 1) 0 0 1 Rep.zero Rep.one
  refine ⟨this.1, fun i hi => ?_⟩
  have h := this.2 i hi
  rwa [zero_add] at h

/-! ## Bounds for the kernels -/

/-- The numbers `ρ (k - 1), ρ k` with `ρ (k + 1) = c k ρ k + ρ (k - 1)`. -/
def rhoPair2 : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | k + 1 => ((rhoPair2 k).2, cf k * (rhoPair2 k).2 + (rhoPair2 k).1)

theorem qPair2_bd {AhP WhP : Poly} {a : ℕ} (hA : Bd AhP a 2) (hW : Bd WhP (a ^ 2) 4) :
    ∀ k, Bd (qPair2 AhP WhP k).2 ((rhoPair2 k).2 * a ^ k) (2 * k) ∧
      Bd (qPair2 AhP WhP k).1 ((rhoPair2 k).1 * a ^ (k - 1)) (2 * k - 2)
  | 0 => by
    constructor
    · simpa [qPair2, rhoPair2] using Bd.one
    · simpa [qPair2, rhoPair2] using Bd.zero
  | k + 1 => by
    obtain ⟨hc, hp⟩ := qPair2_bd hA hW k
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa [qPair2, rhoPair2, cf_zero] using hA
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have t1 : Bd (C ((cf (j + 1) : ℕ) : ℤ) * (AhP * (qPair2 AhP WhP (j + 1)).2))
            (cf (j + 1) * (a * ((rhoPair2 (j + 1)).2 * a ^ (j + 1)))) (2 + 2 * (j + 1)) :=
          Bd.smul _ (hA.mul hc)
        have t2 : Bd (WhP * (qPair2 AhP WhP (j + 1)).1)
            (a ^ 2 * ((rhoPair2 (j + 1)).1 * a ^ j)) (2 + 2 * (j + 1)) := by
          have := hW.mul hp
          simp only [Nat.add_sub_cancel] at this
          exact this.mono le_rfl (by omega)
        refine ((t1.sub t2).mono (le_of_eq ?_) (by omega)).congr ?_
        · show _ = (cf (j + 1) * (rhoPair2 (j + 1)).2 + (rhoPair2 (j + 1)).1) * a ^ (j + 1 + 1)
          ring
        · show _ = ((cf (j + 1) : ℕ) : Poly) * AhP * (qPair2 AhP WhP (j + 1)).2 - WhP * (qPair2 AhP WhP (j + 1)).1
          rw [C_natCast']
          ring
    · have : (qPair2 AhP WhP (k + 1)).1 = (qPair2 AhP WhP k).2 := rfl
      rw [this]
      have h2 : (rhoPair2 (k + 1)).1 = (rhoPair2 k).2 := rfl
      rw [h2, Nat.add_sub_cancel]
      exact hc.mono le_rfl (by omega)

theorem qV2_bd {AhP WhP : Poly} {a : ℕ} (hA : Bd AhP a 2) (hW : Bd WhP (a ^ 2) 4) (k : ℕ) :
    Bd (qV2 AhP WhP k) ((rhoPair2 k).2 * a ^ k) (2 * k) := (qPair2_bd hA hW k).1

theorem rhoL2_spec : ∀ (n k : ℕ), (rhoL2 n k (rhoPair2 k).1 (rhoPair2 k).2).length = n ∧
    ∀ i, i < n → (rhoL2 n k (rhoPair2 k).1 (rhoPair2 k).2).getD i 0 = (rhoPair2 (k + i)).2
  | 0, _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1, k => by
    have ih := rhoL2_spec n (k + 1)
    have e : rhoL2 (n + 1) k (rhoPair2 k).1 (rhoPair2 k).2
        = (rhoPair2 k).2 :: rhoL2 n (k + 1) (rhoPair2 (k + 1)).1 (rhoPair2 (k + 1)).2 := rfl
    rw [e]
    refine ⟨by rw [List.length_cons, ih.1], fun i hi => ?_⟩
    cases i with
    | zero => rfl
    | succ j =>
      rw [List.getD_cons_succ, ih.2 j (Nat.lt_of_succ_lt_succ hi), show k + 1 + j = k + (j + 1) by omega]

theorem nRooted2_eq (P : Params) :
    nRooted2 P = (∑ j ∈ range (P.d + 1), (rhoPair2 j).2 * 2 ^ j * ((P.d - j + 1) * (P.d - j + 1)))
      * (2 ^ (P.wG - 1) * (2 ^ P.m) ^ P.D) := by
  have hr := rhoL2_spec (P.d + 1) 0
  have hlen : (rhoL2 (Nat.succ P.d) 0 0 1).length = P.d + 1 := hr.1
  have hget : ∀ j, j < P.d + 1 → (rhoL2 (Nat.succ P.d) 0 0 1).getD j 0 = (rhoPair2 j).2 := fun j hj => by
    have := hr.2 j hj
    rw [zero_add] at this
    exact this
  unfold nRooted2
  show (kSum _ P.d 0 0) <<< (P.wG - 1 + P.m * P.D) = _
  rw [Nat.shiftLeft_eq, kSum_eq, hlen, zero_add, pow_add, pow_mul]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [hget j (mem_range.mp hj), zero_add]

/-! ## The rooted forms -/

theorem rootedVal2_rep (hM : Mod P pM mM) {w1 w2 w3 : ℕ} {W1 W2 W3 : Poly} (h1 : Rep P w1 W1) (h2 : Rep P w2 W2)
    (h3 : Rep P w3 W3) (hD : P.d ≤ P.D) (R : Rooted) (hR : R.gram.length ≤ P.d + 1) :
    Rep P (rootedVal2 P pM mM R w1 w2 w3 (pows mM w1 (Nat.succ P.D) 1) (pows mM w2 (Nat.succ P.D) 1))
      (rootedV2 P (EP P) W1 W2 W3 R) := by
  have hq := qlist2_rep hM h1 h2 h3
  have := rootedGo_rep hM h1 h2 hD hq.2 (rep 1 (Nat.succ P.d)) R.b R.c R.gram 0 0 0 (by omega) Rep.zero
  simp only [List.drop_zero, Nat.sub_zero, zero_add] at this
  unfold rootedVal2
  refine this.congr ?_
  unfold rootedV2
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < Nat.succ P.d := by have := mem_range.mp hk; omega
  rw [rep_getD 1 (Nat.succ P.d) k hk']
  simp

theorem rootedV2_bd (hD : P.D = 2 * P.d) (hG : 1 ≤ P.wG) {W1 W2 W3 : Poly} (h1 : Bd W1 (2 ^ P.m) 1)
    (h2 : Bd W2 (2 ^ P.m) 1) (h3 : Bd W3 (2 ^ P.m) 1) (R : Rooted) (hR : R.gram.length ≤ P.d + 1) :
    Bd (rootedV2 P (EP P) W1 W2 W3 R) (nRooted2 P) P.D := by
  unfold rootedV2
  have hterm : ∀ k ∈ range R.gram.length,
      Bd (qV2 (AhV (EP P) W1 W2 W3) (WhV (EP P) W1 W2) k
        * bilV P.wG (EP P) W1 W2 (P.d - k) (P.q * (P.d - k + 1)) (blockOf P (R.gram.getD k 0) (P.d - k) R.b R.c))
        ((rhoPair2 k).2 * 2 ^ k * ((P.d - k + 1) * (P.d - k + 1)) * (2 ^ (P.wG - 1) * (2 ^ P.m) ^ P.D)) P.D := by
    intro k hk
    have hk' : k ≤ P.d := by have := mem_range.mp hk; omega
    have hq := qV2_bd (AhV_bd h1 h2 h3) (WhV_bd h1 h2) k
    have hb := bil_bd h1 h2 P.wG hG (P.d - k) (P.q * (P.d - k + 1)) (blockOf P (R.gram.getD k 0) (P.d - k) R.b R.c)
    refine (hq.mul hb).mono (le_of_eq ?_) (by omega)
    rw [hD]
    have e := term_bound P.m P.wG P.d k hk' ((rhoPair2 k).2)
    rw [← e]
  refine (Bd.sum _ _ _ _ hterm).mono ?_ le_rfl
  rw [nRooted2_eq, ← sum_mul]
  refine Nat.mul_le_mul_right _ ?_
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hR) fun _ _ _ => Nat.zero_le _

end N11.Circ
