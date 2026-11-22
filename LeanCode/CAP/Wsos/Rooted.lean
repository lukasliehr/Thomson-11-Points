module

public import CAP.Wsos.Forms

/-!
# The numbers of the checker stand for the polynomials of the data: kernels and rooted forms

`rootedVal_rep`: the number `CAP.Wsos.rootedVal` stands for the polynomial `CAP.Wsos.rootedV`, and
`rootedV_bd`: the coefficients of this polynomial are bounded by `CAP.Wsos.nRooted`.
-/

@[expose] public section

namespace CAP.Wsos

open Finset MvPolynomial

variable {P : Params} {pM mM : ℕ}

/-! ## Lists that are walked through from an index on -/

theorem hd_drop : ∀ (l : List ℕ) (k : ℕ), hd (l.drop k) = l.getD k 0
  | [], k => by simp [hd]
  | _ :: _, 0 => rfl
  | _ :: l, k + 1 => by simpa using hd_drop l k

theorem tl_drop : ∀ (l : List ℕ) (k : ℕ), tl (l.drop k) = l.drop (k + 1)
  | [], k => by simp [tl]
  | _ :: _, 0 => rfl
  | _ :: l, k + 1 => by simpa using tl_drop l k

/-! ## The kernels -/

theorem qnext_rep (hM : Mod P pM mM) {Ah Wh prev cur : ℕ} {AhP WhP pP cP : Poly} (hA : Rep P Ah AhP)
    (hW : Rep P Wh WhP) (hp : Rep P prev pP) (hc : Rep P cur cP) (k : ℕ) :
    Rep P (qnext pM mM Ah Wh k prev cur)
      (((2 * k + 1 : ℕ) : Poly) * AhP * cP - ((k * k : ℕ) : Poly) * WhP * pP) := by
  have h1 : Rep P ((2 * k + 1) * mulM mM Ah cur) (C ((2 * k + 1 : ℕ) : ℤ) * (AhP * cP)) :=
    Rep.smul _ (hA.mulM hM hc)
  have h2 : Rep P (k * k * mulM mM Wh prev) (C ((k * k : ℕ) : ℤ) * (WhP * pP)) := Rep.smul _ (hW.mulM hM hp)
  refine ((h1.subM hM h2).land hM).congr ?_
  rw [C_natCast', C_natCast']
  ring

theorem ql_succ (Ah Wh n k prev cur : ℕ) :
    ql pM mM Ah Wh (n + 1) k prev cur = cur :: ql pM mM Ah Wh n (Nat.succ k) cur (qnext pM mM Ah Wh k prev cur) :=
  rfl

theorem ql_rep (hM : Mod P pM mM) {Ah Wh : ℕ} {AhP WhP : Poly} (hA : Rep P Ah AhP) (hW : Rep P Wh WhP) :
    ∀ (n k prev cur : ℕ), Rep P prev (qPair AhP WhP k).1 → Rep P cur (qPair AhP WhP k).2 →
      (ql pM mM Ah Wh n k prev cur).length = n ∧
      ∀ i, i < n → Rep P ((ql pM mM Ah Wh n k prev cur).getD i 0) (qV AhP WhP (k + i))
  | 0, _, _, _, _, _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1, k, prev, cur, hp, hc => by
    have ih := ql_rep hM hA hW n (k + 1) cur (qnext pM mM Ah Wh k prev cur) hc (qnext_rep hM hA hW hp hc k)
    rw [ql_succ]
    refine ⟨by rw [List.length_cons, ih.1], fun i hi => ?_⟩
    cases i with
    | zero => exact hc
    | succ j =>
      rw [List.getD_cons_succ]
      have := ih.2 j (Nat.lt_of_succ_lt_succ hi)
      rwa [show k + 1 + j = k + (j + 1) by omega] at this

theorem AhV_rep (hM : Mod P pM mM) {w1 w2 w3 : ℕ} {W1 W2 W3 : Poly} (h1 : Rep P w1 W1) (h2 : Rep P w2 W2)
    (h3 : Rep P w3 W3) :
    Rep P (Nat.land (subM pM mM (Nat.shiftLeft w3 P.m) (mulM mM w1 w2)) mM) (AhV (EP P) W1 W2 W3) := by
  refine (((h3.shiftLeft P.m).subM hM (h1.mulM hM h2)).land hM).congr ?_
  unfold AhV EP
  rw [C_two_pow]

theorem rep_E2 (P : Params) : Rep P (Nat.shiftLeft 1 (Nat.mul 2 P.m)) ((EP P) ^ 2) := by
  have := rep_two_pow P (2 * P.m)
  rwa [show (2 : Poly) ^ (2 * P.m) = (EP P) ^ 2 by unfold EP; rw [← pow_mul, mul_comm]] at this

theorem WhV_rep (hM : Mod P pM mM) {w1 w2 : ℕ} {W1 W2 : Poly} (h1 : Rep P w1 W1) (h2 : Rep P w2 W2) :
    Rep P (mulM mM (subM pM mM (Nat.shiftLeft 1 (Nat.mul 2 P.m)) (mulM mM w1 w1))
      (subM pM mM (Nat.shiftLeft 1 (Nat.mul 2 P.m)) (mulM mM w2 w2))) (WhV (EP P) W1 W2) := by
  refine (((rep_E2 P).subM hM (h1.mulM hM h1)).mulM hM ((rep_E2 P).subM hM (h2.mulM hM h2))).congr ?_
  unfold WhV
  ring

theorem qlist_rep (hM : Mod P pM mM) {w1 w2 w3 : ℕ} {W1 W2 W3 : Poly} (h1 : Rep P w1 W1) (h2 : Rep P w2 W2)
    (h3 : Rep P w3 W3) :
    (qlist P pM mM w1 w2 w3).length = P.d + 1 ∧
    ∀ i, i < P.d + 1 → Rep P ((qlist P pM mM w1 w2 w3).getD i 0) (qV (AhV (EP P) W1 W2 W3) (WhV (EP P) W1 W2) i) := by
  have := ql_rep hM (AhV_rep hM h1 h2 h3) (WhV_rep hM h1 h2) (P.d + 1) 0 0 1 Rep.zero Rep.one
  refine ⟨this.1, fun i hi => ?_⟩
  have h := this.2 i hi
  rwa [zero_add] at h

/-! ## Bounds for the kernels -/

/-- The numbers `ρ (k - 1), ρ k` with `ρ (k + 1) = (2 k + 1) ρ k + k ^ 2 ρ (k - 1)`. -/
def rhoPair : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | k + 1 => ((rhoPair k).2, (2 * k + 1) * (rhoPair k).2 + k * k * (rhoPair k).1)

theorem AhV_bd {W1 W2 W3 : Poly} (h1 : Bd W1 (2 ^ P.m) 1) (h2 : Bd W2 (2 ^ P.m) 1) (h3 : Bd W3 (2 ^ P.m) 1) :
    Bd (AhV (EP P) W1 W2 W3) (2 * (2 ^ P.m) ^ 2) 2 := by
  unfold AhV
  have a := ((bd_two_pow P.m).mul h3).mono le_rfl (by omega : 0 + 1 ≤ 2)
  have b := h1.mul h2
  refine (a.sub b).mono (le_of_eq ?_) le_rfl
  ring

theorem E2_bd (P : Params) {W : Poly} (h : Bd W (2 ^ P.m) 1) :
    Bd ((EP P) ^ 2 - W ^ 2) (2 * (2 ^ P.m) ^ 2) 2 := by
  have a := ((bd_two_pow P.m).pow 2).mono le_rfl (by omega : 0 * 2 ≤ 1 * 2)
  refine (a.sub (h.pow 2)).mono (le_of_eq ?_) le_rfl
  ring

theorem WhV_bd {W1 W2 : Poly} (h1 : Bd W1 (2 ^ P.m) 1) (h2 : Bd W2 (2 ^ P.m) 1) :
    Bd (WhV (EP P) W1 W2) ((2 * (2 ^ P.m) ^ 2) ^ 2) 4 := by
  unfold WhV
  refine ((E2_bd P h1).mul (E2_bd P h2)).mono (le_of_eq ?_) le_rfl
  ring

theorem qPair_bd {AhP WhP : Poly} {a : ℕ} (hA : Bd AhP a 2) (hW : Bd WhP (a ^ 2) 4) :
    ∀ k, Bd (qPair AhP WhP k).2 ((rhoPair k).2 * a ^ k) (2 * k) ∧
      Bd (qPair AhP WhP k).1 ((rhoPair k).1 * a ^ (k - 1)) (2 * k - 2)
  | 0 => by
    constructor
    · simpa [qPair, rhoPair] using Bd.one
    · simpa [qPair, rhoPair] using Bd.zero
  | k + 1 => by
    obtain ⟨hc, hp⟩ := qPair_bd hA hW k
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa [qPair, rhoPair] using hA
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have t1 : Bd (C ((2 * (j + 1) + 1 : ℕ) : ℤ) * (AhP * (qPair AhP WhP (j + 1)).2))
            ((2 * (j + 1) + 1) * (a * ((rhoPair (j + 1)).2 * a ^ (j + 1)))) (2 + 2 * (j + 1)) :=
          Bd.smul _ (hA.mul hc)
        have t2 : Bd (C (((j + 1) * (j + 1) : ℕ) : ℤ) * (WhP * (qPair AhP WhP (j + 1)).1))
            ((j + 1) * (j + 1) * (a ^ 2 * ((rhoPair (j + 1)).1 * a ^ j))) (2 + 2 * (j + 1)) := by
          have := Bd.smul ((j + 1) * (j + 1)) (hW.mul hp)
          simp only [Nat.add_sub_cancel] at this
          exact this.mono le_rfl (by omega)
        refine ((t1.sub t2).mono (le_of_eq ?_) (by omega)).congr ?_
        · show _ = ((2 * (j + 1) + 1) * (rhoPair (j + 1)).2 + (j + 1) * (j + 1) * (rhoPair (j + 1)).1) * a ^ (j + 1 + 1)
          ring
        · show _ = ((2 * (j + 1) + 1 : ℕ) : Poly) * AhP * (qPair AhP WhP (j + 1)).2
              - (((j + 1) * (j + 1) : ℕ) : Poly) * WhP * (qPair AhP WhP (j + 1)).1
          rw [C_natCast', C_natCast']
          ring
    · have : (qPair AhP WhP (k + 1)).1 = (qPair AhP WhP k).2 := rfl
      rw [this]
      have h2 : (rhoPair (k + 1)).1 = (rhoPair k).2 := rfl
      rw [h2, Nat.add_sub_cancel]
      exact hc.mono le_rfl (by omega)

theorem qV_bd {AhP WhP : Poly} {a : ℕ} (hA : Bd AhP a 2) (hW : Bd WhP (a ^ 2) 4) (k : ℕ) :
    Bd (qV AhP WhP k) ((rhoPair k).2 * a ^ k) (2 * k) := (qPair_bd hA hW k).1

theorem rhoL_succ (n k prev cur : ℕ) :
    rhoL (n + 1) k prev cur = cur :: rhoL n (Nat.succ k) cur
      (Nat.add (Nat.mul (Nat.succ (Nat.mul 2 k)) cur) (Nat.mul (Nat.mul k k) prev)) := rfl

theorem rhoL_spec : ∀ (n k : ℕ), (rhoL n k (rhoPair k).1 (rhoPair k).2).length = n ∧
    ∀ i, i < n → (rhoL n k (rhoPair k).1 (rhoPair k).2).getD i 0 = (rhoPair (k + i)).2
  | 0, _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1, k => by
    have ih := rhoL_spec n (k + 1)
    have e : rhoL (n + 1) k (rhoPair k).1 (rhoPair k).2
        = (rhoPair k).2 :: rhoL n (k + 1) (rhoPair (k + 1)).1 (rhoPair (k + 1)).2 := rfl
    rw [e]
    refine ⟨by rw [List.length_cons, ih.1], fun i hi => ?_⟩
    cases i with
    | zero => rfl
    | succ j =>
      rw [List.getD_cons_succ, ih.2 j (Nat.lt_of_succ_lt_succ hi), show k + 1 + j = k + (j + 1) by omega]

/-! ## The list of the factors `d! / k!` and the sum of the bound -/

theorem factsGo_length : ∀ (n k g : ℕ) (acc : List ℕ), (factsGo n k g acc).length = acc.length + n
  | 0, _, _, _ => rfl
  | n + 1, k, g, acc => by
    show (factsGo n (Nat.pred k) (Nat.mul g k) (Nat.mul g k :: acc)).length = _
    rw [factsGo_length n, List.length_cons]
    omega

theorem facts_length (d : ℕ) : (facts d).length = d + 1 := by
  unfold facts
  rw [factsGo_length]
  simp [Nat.add_comm]

theorem zipMul_spec : ∀ (a b : List ℕ), (zipMul a b).length = a.length ∧
    ∀ i, i < a.length → (zipMul a b).getD i 0 = a.getD i 0 * b.getD i 0
  | [], _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | x :: a, b => by
    have ih := zipMul_spec a (tl b)
    have e : zipMul (x :: a) b = Nat.mul x (hd b) :: zipMul a (tl b) := rfl
    rw [e]
    refine ⟨by rw [List.length_cons, ih.1, List.length_cons], fun i hi => ?_⟩
    cases i with
    | zero => rw [List.getD_cons_zero, List.getD_cons_zero, hd_eq]; rfl
    | succ j =>
      rw [List.getD_cons_succ, List.getD_cons_succ, ih.2 j (by simpa using hi), tl_eq, getD_tail]

theorem kSum_cons (f : ℕ) (fs : List ℕ) (n k acc : ℕ) :
    kSum (f :: fs) n k acc = kSum fs (Nat.pred n) (Nat.succ k)
      (Nat.add acc (Nat.mul (Nat.mul f (Nat.shiftLeft 1 k)) (Nat.mul (Nat.succ n) (Nat.succ n)))) := rfl

/-- The loop `kSum` in closed form. -/
theorem kSum_eq : ∀ (fs : List ℕ) (n k acc : ℕ),
    kSum fs n k acc = acc + ∑ j ∈ range fs.length, fs.getD j 0 * 2 ^ (k + j) * ((n - j + 1) * (n - j + 1))
  | [], n, k, acc => by simp [kSum]
  | f :: fs, n, k, acc => by
    rw [kSum_cons, kSum_eq fs, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero, Nat.sub_zero]
    show acc + f * (1 <<< k) * ((n + 1) * (n + 1)) + _ = _
    rw [Nat.one_shiftLeft, add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [show Nat.succ k + j = k + (j + 1) by omega, show Nat.pred n - j = n - (j + 1) by
      rw [Nat.pred_eq_sub_one]; omega]

/-! ## The rooted forms -/

theorem rootedGo_cons (pw1 pw2 : List ℕ) (b c G : ℕ) (grams qs gs : List ℕ) (n S : ℕ) :
    rootedGo P pM mM pw1 pw2 b c (G :: grams) qs gs n S
      = rootedGo P pM mM pw1 pw2 b c grams (tl qs) (tl gs) (Nat.pred n)
          (Nat.add S (Nat.mul (hd gs) (mulM mM (hd qs)
            (Nat.land (bil P pM mM G n b c (hl P.m (Nat.succ n) pw1 (Nat.mul P.m n))
              (hl P.m (Nat.succ n) pw2 (Nat.mul P.m n))) mM)))) := rfl

theorem rootedGo_rep (hM : Mod P pM mM) {w1 w2 : ℕ} {W1 W2 : Poly} (hw1 : Rep P w1 W1) (hw2 : Rep P w2 W2)
    (hD : P.d ≤ P.D) {Q : List ℕ} {QP : ℕ → Poly} (hQ : ∀ i, i < P.d + 1 → Rep P (Q.getD i 0) (QP i))
    (Gs : List ℕ) (b c : ℕ) :
    ∀ (grams : List ℕ) (k S : ℕ) (SF : Poly), k + grams.length ≤ P.d + 1 → Rep P S SF →
      Rep P (rootedGo P pM mM (pows mM w1 (Nat.succ P.D) 1) (pows mM w2 (Nat.succ P.D) 1) b c grams
          (Q.drop k) (Gs.drop k) (P.d - k) S)
        (SF + ∑ j ∈ range grams.length, C ((Gs.getD (k + j) 0 : ℕ) : ℤ) * (QP (k + j)
          * bilV P.wG (EP P) W1 W2 (P.d - (k + j)) (P.q * (P.d - (k + j) + 1))
              (blockOf P (grams.getD j 0) (P.d - (k + j)) b c)))
  | [], k, S, SF, _, hS => by simpa [rootedGo] using hS
  | G :: grams, k, S, SF, hk, hS => by
    rw [List.length_cons] at hk
    rw [rootedGo_cons, hd_drop, hd_drop, tl_drop, tl_drop]
    have hn : P.d - k < Nat.succ P.D := by omega
    have hb := (bil_rep hM (homList hM hw1 hn) (homList hM hw2 hn) G b c).land hM
    have hq := hQ k (by omega)
    have hS' := hS.add (Rep.smul (Gs.getD k 0) (hq.mulM hM hb))
    have ih := rootedGo_rep hM hw1 hw2 hD hQ Gs b c grams (k + 1) _ _ (by omega) hS'
    rw [show Nat.pred (P.d - k) = P.d - (k + 1) by rw [Nat.pred_eq_sub_one]; omega]
    refine ih.congr ?_
    rw [List.length_cons, sum_range_succ', add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [show k + 1 + j = k + (j + 1) by omega, List.getD_cons_succ]

theorem rootedVal_rep (hM : Mod P pM mM) {w1 w2 w3 : ℕ} {W1 W2 W3 : Poly} (h1 : Rep P w1 W1) (h2 : Rep P w2 W2)
    (h3 : Rep P w3 W3) (hD : P.d ≤ P.D) (R : Rooted) (hR : R.gram.length ≤ P.d + 1) :
    Rep P (rootedVal P pM mM R w1 w2 w3 (pows mM w1 (Nat.succ P.D) 1) (pows mM w2 (Nat.succ P.D) 1))
      (rootedV P (EP P) W1 W2 W3 R) := by
  have hq := qlist_rep hM h1 h2 h3
  have := rootedGo_rep hM h1 h2 hD hq.2 (facts P.d) R.b R.c R.gram 0 0 0 (by omega) Rep.zero
  simp only [List.drop_zero, Nat.sub_zero, zero_add] at this
  unfold rootedVal
  refine this.congr ?_
  unfold rootedV
  exact sum_congr rfl fun k _ => by rw [C_natCast']

end CAP.Wsos
