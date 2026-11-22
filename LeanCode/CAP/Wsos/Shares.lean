module

public import CAP.Wsos.Rooted

/-!
# The numbers of the checker stand for the polynomials of the data: bounds of the rooted forms, shares

* `rootedV_bd`: the coefficients of a rooted form are bounded by `CAP.Wsos.nRooted`.
* `rootUseVal_rep`, `rootUseV_bd`: the polynomial of the rooted blocks of a class at coinciding points.
* `shareVal_rep`, `shareV_bd`: the shares.
-/

@[expose] public section

namespace CAP.Wsos

open Finset MvPolynomial

variable {P : Params} {pM mM : ℕ}

/-! ## The bound of a term of degree `2 * d` -/

theorem term_bound (m wG d k : ℕ) (hk : k ≤ d) (f : ℕ) :
    f * (2 * (2 ^ m) ^ 2) ^ k * ((d - k + 1) * ((2 ^ m) ^ (d - k) * ((d - k + 1) * (2 ^ (wG - 1) * (2 ^ m) ^ (d - k)))))
      = f * 2 ^ k * ((d - k + 1) * (d - k + 1)) * (2 ^ (wG - 1) * (2 ^ m) ^ (2 * d)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = k + n := ⟨d - k, by omega⟩
  rw [Nat.add_sub_cancel_left]
  generalize (2 : ℕ) ^ m = E
  generalize (2 : ℕ) ^ (wG - 1) = G
  rw [mul_pow, show 2 * (k + n) = 2 * k + n + n by ring, pow_add, pow_add, ← pow_mul]
  ring

theorem nRooted_eq (P : Params) :
    nRooted P = (∑ j ∈ range (P.d + 1), (facts P.d).getD j 0 * (rhoPair j).2 * 2 ^ j * ((P.d - j + 1) * (P.d - j + 1)))
      * (2 ^ (P.wG - 1) * (2 ^ P.m) ^ P.D) := by
  unfold nRooted
  have hz := zipMul_spec (facts P.d) (rhoL (Nat.succ P.d) 0 0 1)
  have hr := rhoL_spec (P.d + 1) 0
  show (kSum _ P.d 0 0) <<< (P.wG - 1 + P.m * P.D) = _
  rw [Nat.shiftLeft_eq, kSum_eq, hz.1, facts_length, zero_add, pow_add, pow_mul]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < P.d + 1 := mem_range.mp hj
  rw [hz.2 j (by rw [facts_length]; exact hj')]
  have := hr.2 j hj'
  rw [zero_add] at this
  rw [show rhoL (Nat.succ P.d) 0 0 1 = rhoL (P.d + 1) 0 (rhoPair 0).1 (rhoPair 0).2 from rfl, this, zero_add]

theorem rootedV_bd (hD : P.D = 2 * P.d) (hG : 1 ≤ P.wG) {W1 W2 W3 : Poly} (h1 : Bd W1 (2 ^ P.m) 1)
    (h2 : Bd W2 (2 ^ P.m) 1) (h3 : Bd W3 (2 ^ P.m) 1) (R : Rooted) (hR : R.gram.length ≤ P.d + 1) :
    Bd (rootedV P (EP P) W1 W2 W3 R) (nRooted P) P.D := by
  unfold rootedV
  have hterm : ∀ k ∈ range R.gram.length,
      Bd ((((facts P.d).getD k 0 : ℕ) : Poly) * (qV (AhV (EP P) W1 W2 W3) (WhV (EP P) W1 W2) k
        * bilV P.wG (EP P) W1 W2 (P.d - k) (P.q * (P.d - k + 1)) (blockOf P (R.gram.getD k 0) (P.d - k) R.b R.c)))
        ((facts P.d).getD k 0 * (rhoPair k).2 * 2 ^ k * ((P.d - k + 1) * (P.d - k + 1))
          * (2 ^ (P.wG - 1) * (2 ^ P.m) ^ P.D)) P.D := by
    intro k hk
    have hk' : k ≤ P.d := by have := mem_range.mp hk; omega
    have hq := qV_bd (AhV_bd h1 h2 h3) (WhV_bd h1 h2) k
    have hb := bil_bd h1 h2 P.wG hG (P.d - k) (P.q * (P.d - k + 1)) (blockOf P (R.gram.getD k 0) (P.d - k) R.b R.c)
    have := Bd.smul ((facts P.d).getD k 0) (hq.mul hb)
    rw [C_natCast'] at this
    refine this.mono (le_of_eq ?_) (by omega)
    rw [hD]
    have e := term_bound P.m P.wG P.d k hk' ((facts P.d).getD k 0 * (rhoPair k).2)
    rw [← e]
    ring
  refine (Bd.sum _ _ _ _ hterm).mono ?_ le_rfl
  rw [nRooted_eq, ← sum_mul]
  refine Nat.mul_le_mul_right _ ?_
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hR) fun _ _ _ => Nat.zero_le _

/-! ## The rooted blocks of a class at coinciding points -/

theorem linGo_cons (wG mG cnt zN hj : ℕ) (h : List ℕ) (Gr U : ℕ) :
    linGo wG mG cnt zN (hj :: h) Gr U
      = linGo wG mG cnt zN h (Nat.shiftRight Gr zN) (Nat.add U (Nat.mul (dsum wG mG cnt Gr 0) hj)) := rfl

/-- The loop `linGo` in closed form. -/
theorem linGo_eq (wG cnt N : ℕ) : ∀ (h : List ℕ) (Gr U : ℕ),
    linGo wG (mask wG) cnt (wG * N) h Gr U
      = U + ∑ j ∈ range h.length, (∑ i ∈ range cnt, slot wG Gr (N * j + i)) * h.getD j 0
  | [], Gr, U => by simp [linGo]
  | hj :: h, Gr, U => by
    rw [linGo_cons, linGo_eq wG cnt N h, dsum_eq, List.length_cons, sum_range_succ', zero_add]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.mul_zero, Nat.zero_add]
    show U + (∑ i ∈ range cnt, slot wG Gr i) * hj + _ = _
    rw [add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [show Nat.shiftRight Gr (wG * N) = Gr >>> (wG * N) from rfl, slot_shiftRight_mul]
    congr 1
    ring

theorem firstK_rep (hM : Mod P pM mM) {h : List ℕ} {Wp : Poly} (hh : HomList P h Wp P.d) (hG : 1 ≤ P.wG) (Gr : ℕ) :
    Rep P (firstK P pM mM h Gr) (linV P.wG (EP P) Wp P.d (P.q * (P.d + 1)) Gr) := by
  unfold firstK
  have e1 : linGo P.wG (mask P.wG) (Nat.succ P.d) (Nat.mul P.wG (Nat.mul P.q (Nat.succ P.d))) h Gr 0
      = ∑ j ∈ range (P.d + 1), (∑ i ∈ range (P.d + 1), slot P.wG Gr (P.q * (P.d + 1) * j + i)) * h.getD j 0 := by
    have := linGo_eq P.wG (P.d + 1) (P.q * (P.d + 1)) h Gr 0
    rw [zero_add, hh.len] at this
    exact this
  have e2 : Nat.mul (Nat.shiftLeft (Nat.succ P.d) (Nat.pred P.wG)) (lsum h)
      = ∑ j ∈ range (P.d + 1), ((P.d + 1) * 2 ^ (P.wG - 1)) * h.getD j 0 := by
    show ((P.d + 1) <<< (P.wG - 1)) * lsum h = _
    rw [Nat.shiftLeft_eq, lsum_eq, hh.len, mul_sum]
  rw [e1, e2]
  have h1 : Rep P (∑ j ∈ range (P.d + 1), (∑ i ∈ range (P.d + 1), slot P.wG Gr (P.q * (P.d + 1) * j + i)) * h.getD j 0)
      (∑ j ∈ range (P.d + 1), C (((∑ i ∈ range (P.d + 1), slot P.wG Gr (P.q * (P.d + 1) * j + i) : ℕ) : ℤ))
        * hpow (EP P) Wp P.d j) :=
    Rep.sum _ _ _ fun j hj => Rep.smul _ (hh.rep j (mem_range.mp hj))
  have h2 : Rep P (∑ j ∈ range (P.d + 1), ((P.d + 1) * 2 ^ (P.wG - 1)) * h.getD j 0)
      (∑ j ∈ range (P.d + 1), C ((((P.d + 1) * 2 ^ (P.wG - 1) : ℕ) : ℤ)) * hpow (EP P) Wp P.d j) :=
    Rep.sum _ _ _ fun j hj => Rep.smul _ (hh.rep j (mem_range.mp hj))
  refine (h1.subM hM h2).congr ?_
  unfold linV
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [← sub_mul]
  congr 1
  unfold sdig
  rw [← map_sub, C_intCast']
  congr 1
  push_cast
  rw [sum_sub_distrib, sum_const, card_range]
  simp

theorem abs_sum_sdig_le (w c : ℕ) (hw : 1 ≤ w) (n : ℕ) (f : ℕ → ℕ) :
    |∑ i ∈ range n, sdig w c (f i)| ≤ ((n * 2 ^ (w - 1) : ℕ) : ℤ) := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : ∑ i ∈ range n, |sdig w c (f i)| ≤ ∑ _i ∈ range n, ((2 ^ (w - 1) : ℕ) : ℤ) :=
    sum_le_sum fun i _ => abs_sdig_le w c (f i) hw
  refine this.trans (le_of_eq ?_)
  rw [sum_const, card_range]
  push_cast
  ring

theorem linV_bd {Wp : Poly} (hW : Bd Wp (2 ^ P.m) 1) (wG : ℕ) (hG : 1 ≤ wG) (d N Gr : ℕ) :
    Bd (linV wG (EP P) Wp d N Gr) ((d + 1) * ((d + 1) * 2 ^ (wG - 1) * (2 ^ P.m) ^ d)) d := by
  unfold linV
  have := Bd.sum_le (range (d + 1))
    (fun j => C (∑ i ∈ range (d + 1), sdig wG Gr (N * j + i)) * hpow (EP P) Wp d j)
    ((d + 1) * 2 ^ (wG - 1) * (2 ^ P.m) ^ d) d
    (fun j hj => Bd.intC (abs_sum_sdig_le wG Gr hG (d + 1) fun i => N * j + i) (hpow_bd hW (mem_range.mp hj)))
  rw [card_range] at this
  refine this.congr (sum_congr rfl fun j _ => ?_)
  rw [C_intCast']
  push_cast
  rfl

theorem dGo_cons (pw : List ℕ) (Vh b G : ℕ) (grams : List ℕ) (vk n S : ℕ) :
    dGo P pM mM pw Vh b (G :: grams) vk n S
      = dGo P pM mM pw Vh b grams (mulM mM vk Vh) (Nat.pred n)
          (Nat.add S (mulM mM vk (Nat.land (dStep P pM mM G n b (hl P.m (Nat.succ n) pw (Nat.mul P.m n))) mM))) := rfl

theorem dGo_rep (hM : Mod P pM mM) {w : ℕ} {Wp : Poly} (hw : Rep P w Wp) (hD : P.d ≤ P.D) {Vh : ℕ} {VhP : Poly}
    (hV : Rep P Vh VhP) (b : ℕ) :
    ∀ (grams : List ℕ) (k vk S : ℕ) (SF : Poly), k + grams.length ≤ P.d + 1 → Rep P vk (VhP ^ k) → Rep P S SF →
      Rep P (dGo P pM mM (pows mM w (Nat.succ P.D) 1) Vh b grams vk (P.d - k) S)
        (SF + ∑ j ∈ range grams.length, VhP ^ (k + j)
          * bilV P.wG (EP P) Wp Wp (P.d - (k + j)) (P.q * (P.d - (k + j) + 1))
              (blockOf P (grams.getD j 0) (P.d - (k + j)) b b))
  | [], k, vk, S, SF, _, _, hS => by simpa [dGo] using hS
  | G :: grams, k, vk, S, SF, hk, hv, hS => by
    rw [List.length_cons] at hk
    rw [dGo_cons]
    have hn : P.d - k < Nat.succ P.D := by omega
    have hh := homList hM hw hn
    have hb : Rep P (Nat.land (dStep P pM mM G (P.d - k) b
        (hl P.m (Nat.succ (P.d - k)) (pows mM w (Nat.succ P.D) 1) (Nat.mul P.m (P.d - k)))) mM) _ :=
      (bil_rep hM hh hh G b b).land hM
    have hS' := hS.add (hv.mulM hM hb)
    have hv' : Rep P (mulM mM vk Vh) (VhP ^ (k + 1)) := by
      rw [pow_succ]; exact hv.mulM hM hV
    have ih := dGo_rep hM hw hD hV b grams (k + 1) _ _ _ (by omega) hv' hS'
    rw [show Nat.pred (P.d - k) = P.d - (k + 1) by rw [Nat.pred_eq_sub_one]; omega]
    refine ih.congr ?_
    rw [List.length_cons, sum_range_succ', add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [show k + 1 + j = k + (j + 1) by omega, List.getD_cons_succ]

theorem rootUseVal_rep (hM : Mod P pM mM) {w : ℕ} {Wp : Poly} (hw : Rep P w Wp) (hD : P.d ≤ P.D) (hG : 1 ≤ P.wG)
    (Ru : RootUse) (hR : Ru.gram.length ≤ P.d + 1) :
    Rep P (rootUseVal P pM mM w (pows mM w (Nat.succ P.D) 1) Ru) (rootUseV P (EP P) Wp Ru) := by
  unfold rootUseVal
  have hh := homList hM hw (show P.d < Nat.succ P.D by omega)
  have hf := ((firstK_rep hM hh hG (blockOf P (Ru.gram.getD 0 0) P.d Ru.self Ru.other)).land hM).shiftLeft
    (Nat.succ (Nat.mul P.m P.d))
  have hV : Rep P (Nat.land (subM pM mM (Nat.shiftLeft 1 (Nat.mul 2 P.m)) (mulM mM w w)) mM) ((EP P) ^ 2 - Wp ^ 2) := by
    refine (((rep_E2 P).subM hM (hw.mulM hM hw)).land hM).congr ?_
    ring
  have hd := dGo_rep hM hw hD hV Ru.other Ru.gram 0 1 0 0 (by omega) (by simpa using Rep.one (P := P)) Rep.zero
  simp only [Nat.sub_zero, zero_add] at hd
  rw [hd_eq]
  refine (hf.add hd).congr ?_
  unfold rootUseV
  congr 1
  rw [show Nat.succ (Nat.mul P.m P.d) = P.m * P.d + 1 from rfl, C_two_pow, pow_succ, pow_mul]
  unfold EP
  ring

theorem nRootUse_eq (P : Params) :
    nRootUse P = 2 * ((P.d + 1) * (P.d + 1)) + ∑ j ∈ range (P.d + 1), 2 ^ j * ((P.d - j + 1) * (P.d - j + 1)) := by
  unfold nRootUse
  show 2 * ((P.d + 1) * (P.d + 1)) + kSum (rep 1 (P.d + 1)) P.d 0 0 = _
  rw [kSum_eq, rep_length, zero_add]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  rw [rep_getD 1 _ _ (mem_range.mp hj), one_mul, zero_add]

theorem rootUseV_bd (hD : P.D = 2 * P.d) (hG : 1 ≤ P.wG) {Wp : Poly} (hW : Bd Wp (2 ^ P.m) 1) (Ru : RootUse)
    (hR : Ru.gram.length ≤ P.d + 1) :
    Bd (rootUseV P (EP P) Wp Ru) (nRootUse P * (2 ^ (P.wG - 1) * (2 ^ P.m) ^ P.D)) P.D := by
  unfold rootUseV
  have hfirst : Bd (2 * (EP P) ^ P.d
      * linV P.wG (EP P) Wp P.d (P.q * (P.d + 1)) (blockOf P (Ru.gram.getD 0 0) P.d Ru.self Ru.other))
      (2 * ((P.d + 1) * (P.d + 1)) * (2 ^ (P.wG - 1) * (2 ^ P.m) ^ P.D)) P.D := by
    have a : Bd ((2 : Poly) * (EP P) ^ P.d) (2 * (2 ^ P.m) ^ P.d) 0 := by
      have := (Bd.natCast 2).mul ((bd_two_pow P.m).pow P.d)
      simpa using this
    have := a.mul (linV_bd hW P.wG hG P.d (P.q * (P.d + 1)) (blockOf P (Ru.gram.getD 0 0) P.d Ru.self Ru.other))
    refine this.mono (le_of_eq ?_) (by omega)
    rw [hD, show 2 * P.d = P.d + P.d by ring, pow_add]
    ring
  have hterm : ∀ k ∈ range Ru.gram.length,
      Bd (((EP P) ^ 2 - Wp ^ 2) ^ k * bilV P.wG (EP P) Wp Wp (P.d - k) (P.q * (P.d - k + 1))
        (blockOf P (Ru.gram.getD k 0) (P.d - k) Ru.other Ru.other))
        (2 ^ k * ((P.d - k + 1) * (P.d - k + 1)) * (2 ^ (P.wG - 1) * (2 ^ P.m) ^ P.D)) P.D := by
    intro k hk
    have hk' : k ≤ P.d := by have := mem_range.mp hk; omega
    have hb := bil_bd hW hW P.wG hG (P.d - k) (P.q * (P.d - k + 1))
      (blockOf P (Ru.gram.getD k 0) (P.d - k) Ru.other Ru.other)
    refine (((E2_bd P hW).pow k).mul hb).mono (le_of_eq ?_) (by omega)
    rw [hD]
    have e := term_bound P.m P.wG P.d k hk' 1
    rw [one_mul, one_mul] at e
    exact e
  refine (hfirst.add (Bd.sum _ _ _ _ hterm)).mono ?_ le_rfl
  rw [nRootUse_eq, ← sum_mul, ← add_mul]
  refine Nat.mul_le_mul_right _ (Nat.add_le_add_left ?_ _)
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hR) fun _ _ _ => Nat.zero_le _

theorem rootsGo_cons (w : ℕ) (pw : List ℕ) (Ru : RootUse) (roots : List RootUse) (U : ℕ) :
    rootsGo P pM mM w pw (Ru :: roots) U
      = rootsGo P pM mM w pw roots (Nat.add U (Nat.land (rootUseVal P pM mM w pw Ru) mM)) := rfl

theorem rootsGo_rep (hM : Mod P pM mM) {w : ℕ} {Wp : Poly} (hw : Rep P w Wp) (hD : P.d ≤ P.D) (hG : 1 ≤ P.wG) :
    ∀ (roots : List RootUse) (U : ℕ) (UF : Poly), (∀ Ru ∈ roots, Ru.gram.length ≤ P.d + 1) → Rep P U UF →
      Rep P (rootsGo P pM mM w (pows mM w (Nat.succ P.D) 1) roots U) (UF + (roots.map (rootUseV P (EP P) Wp)).sum)
  | [], U, UF, _, hU => by simpa [rootsGo] using hU
  | Ru :: roots, U, UF, hR, hU => by
    rw [rootsGo_cons]
    have h1 := (rootUseVal_rep hM hw hD hG Ru (hR Ru (by simp))).land hM
    have ih := rootsGo_rep hM hw hD hG roots _ _ (fun Ru' h' => hR Ru' (by simp [h'])) (hU.add h1)
    refine ih.congr ?_
    rw [List.map_cons, List.sum_cons]
    ring

theorem roots_bd (hD : P.D = 2 * P.d) (hG : 1 ≤ P.wG) {Wp : Poly} (hW : Bd Wp (2 ^ P.m) 1) :
    ∀ (roots : List RootUse), (∀ Ru ∈ roots, Ru.gram.length ≤ P.d + 1) →
      Bd ((roots.map (rootUseV P (EP P) Wp)).sum) (roots.length * (nRootUse P * (2 ^ (P.wG - 1) * (2 ^ P.m) ^ P.D))) P.D
  | [], _ => by simpa using Bd.zero.mono (Nat.zero_le _) (Nat.zero_le _)
  | Ru :: roots, hR => by
    rw [List.map_cons, List.sum_cons, List.length_cons]
    refine ((rootUseV_bd hD hG hW Ru (hR Ru (by simp))).add
      (roots_bd hD hG hW roots fun Ru' h' => hR Ru' (by simp [h']))).mono (le_of_eq ?_) le_rfl
    ring

/-! ## The shares -/

theorem negsGo_cons (wP mP : ℕ) (h : List ℕ) (c : ℕ) (negs ms : List ℕ) (U : ℕ) :
    negsGo wP mP h (c :: negs) ms U = negsGo wP mP h negs (tl ms) (Nat.add U (Nat.mul (hd ms) (dot wP mP h c 0))) := rfl

/-- The loop `negsGo` in closed form. -/
theorem negsGo_eq (wP mP : ℕ) (h : List ℕ) : ∀ (negs ms : List ℕ) (U : ℕ),
    negsGo wP mP h negs ms U = U + ∑ j ∈ range negs.length, ms.getD j 0 * dot wP mP h (negs.getD j 0) 0
  | [], ms, U => by simp [negsGo]
  | c :: negs, ms, U => by
    rw [negsGo_cons, negsGo_eq wP mP h negs, List.length_cons, sum_range_succ', hd_eq, tl_eq]
    simp only [List.getD_cons_succ, List.getD_cons_zero, getD_tail]
    show U + ms.getD 0 0 * dot wP mP h c 0 + _ = _
    ring

theorem lenR_eq (l : List RootUse) : lenR l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => show lenR l + 1 = _; rw [ih, List.length_cons]

theorem fact_eq (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => show (n + 1) * fact n = _; rw [ih, Nat.factorial_succ]

/-- The polynomial with the digits of `c` (not signed) and the sum of the powers. -/
theorem spolyV_eq (wd : ℕ) (E w : Poly) (n c : ℕ) :
    spolyV wd E w n c = (∑ i ∈ range (n + 1), C ((slot wd c i : ℕ) : ℤ) * hpow E w n i)
      - C (((2 ^ (wd - 1) : ℕ) : ℤ)) * ∑ i ∈ range (n + 1), hpow E w n i := by
  unfold spolyV sdig
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sub_mul, ← map_sub, C_intCast']
  push_cast
  rfl

theorem shareVal_rep (hM : Mod P pM mM) {w : ℕ} {Wp : Poly} (hw : Rep P w Wp) (hD : P.d ≤ P.D) (hG : 1 ≤ P.wG)
    (S : Share) (hlen : S.negs.length = S.negm.length) (hR : ∀ Ru ∈ S.roots, Ru.gram.length ≤ P.d + 1) (fd : ℕ) :
    Rep P (shareVal P pM mM fd S w (pows mM w (Nat.succ P.D) 1)) (((fd : ℕ) : Poly) * shareV P (EP P) Wp S) := by
  unfold shareVal shareH shareK
  have hh := homList hM hw (show P.D < Nat.succ P.D by omega)
  set h := hl P.m (Nat.succ P.D) (pows mM w (Nat.succ P.D) 1) (Nat.mul P.m P.D) with hdef
  set HS : Poly := ∑ i ∈ range (P.D + 1), hpow (EP P) Wp P.D i with hHS
  have hdot : ∀ c, Rep P (dot P.wP (mask P.wP) h c 0)
      (∑ i ∈ range (P.D + 1), C ((slot P.wP c i : ℕ) : ℤ) * hpow (EP P) Wp P.D i) := fun c => by
    rw [dot_eq, zero_add, hh.len]
    exact Rep.sum _ _ _ fun i hi => Rep.smul _ (hh.rep i (mem_range.mp hi))
  have hbias : Rep P (bias P.wP h) (C (((2 ^ (P.wP - 1) : ℕ) : ℤ)) * HS) := by
    rw [bias_eq, hh.len]
    exact Rep.smul _ (Rep.sum _ _ _ fun i hi => hh.rep i (mem_range.mp hi))
  have hpos : Rep P (Nat.add (dot P.wP (mask P.wP) h S.pos 0) (Nat.mul (lsum S.negm) (bias P.wP h)))
      ((∑ i ∈ range (P.D + 1), C ((slot P.wP S.pos i : ℕ) : ℤ) * hpow (EP P) Wp P.D i)
        + C ((lsum S.negm : ℕ) : ℤ) * (C (((2 ^ (P.wP - 1) : ℕ) : ℤ)) * HS)) :=
    (hdot S.pos).add (Rep.smul _ hbias)
  have hneg : Rep P (negsGo P.wP (mask P.wP) h S.negs S.negm (bias P.wP h))
      (C (((2 ^ (P.wP - 1) : ℕ) : ℤ)) * HS + ∑ j ∈ range S.negs.length, C ((S.negm.getD j 0 : ℕ) : ℤ)
        * ∑ i ∈ range (P.D + 1), C ((slot P.wP (S.negs.getD j 0) i : ℕ) : ℤ) * hpow (EP P) Wp P.D i) := by
    rw [negsGo_eq]
    exact hbias.add (Rep.sum _ _ _ fun j _ => Rep.smul _ (hdot _))
  have hroots := rootsGo_rep hM hw hD hG S.roots 0 0 hR Rep.zero
  rw [zero_add] at hroots
  have hA := (Rep.smul fd hpos).shiftLeft P.aP
  have hB := ((Rep.smul fd hneg).shiftLeft P.aP).add ((Rep.smul fd hroots).shiftLeft P.aF)
  refine ((hA.subM hM hB).land hM).congr ?_
  unfold shareV
  rw [spolyV_eq, C_two_pow, C_two_pow, C_natCast', C_natCast', C_natCast']
  have e : ∑ j ∈ range S.negs.length, ((S.negm.getD j 0 : ℕ) : Poly) * spolyV P.wP (EP P) Wp P.D (S.negs.getD j 0)
      = (∑ j ∈ range S.negs.length, ((S.negm.getD j 0 : ℕ) : Poly)
          * ∑ i ∈ range (P.D + 1), C ((slot P.wP (S.negs.getD j 0) i : ℕ) : ℤ) * hpow (EP P) Wp P.D i)
        - ((lsum S.negm : ℕ) : Poly) * (((2 ^ (P.wP - 1) : ℕ) : Poly) * HS) := by
    rw [lsum_eq, ← hlen, Nat.cast_sum, sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [spolyV_eq, C_natCast']
    ring
  rw [e]
  simp only [C_natCast']
  ring

theorem shareV_bd (hD : P.D = 2 * P.d) (hG : 1 ≤ P.wG) (hP : 1 ≤ P.wP) {Wp : Poly} (hW : Bd Wp (2 ^ P.m) 1)
    (S : Share) (hlen : S.negs.length = S.negm.length) (hR : ∀ Ru ∈ S.roots, Ru.gram.length ≤ P.d + 1) :
    Bd (shareV P (EP P) Wp S) (nShare P S) P.D := by
  unfold shareV
  have hs : ∀ c, Bd (spolyV P.wP (EP P) Wp P.D c) ((P.D + 1) * (2 ^ (P.wP - 1) * (2 ^ P.m) ^ P.D)) P.D :=
    fun c => spoly_bd hW P.wP hP P.D c
  have hn : Bd (∑ j ∈ range S.negs.length, ((S.negm.getD j 0 : ℕ) : Poly) * spolyV P.wP (EP P) Wp P.D (S.negs.getD j 0))
      (lsum S.negm * ((P.D + 1) * (2 ^ (P.wP - 1) * (2 ^ P.m) ^ P.D))) P.D := by
    have := Bd.sum (range S.negs.length)
      (fun j => C ((S.negm.getD j 0 : ℕ) : ℤ) * spolyV P.wP (EP P) Wp P.D (S.negs.getD j 0))
      (fun j => S.negm.getD j 0 * ((P.D + 1) * (2 ^ (P.wP - 1) * (2 ^ P.m) ^ P.D))) P.D
      (fun j _ => Bd.smul _ (hs _))
    have e : ∑ j ∈ range S.negs.length, S.negm.getD j 0 * ((P.D + 1) * (2 ^ (P.wP - 1) * (2 ^ P.m) ^ P.D))
        = lsum S.negm * ((P.D + 1) * (2 ^ (P.wP - 1) * (2 ^ P.m) ^ P.D)) := by
      rw [← sum_mul, hlen, ← lsum_eq]
    rw [e] at this
    exact this.congr (sum_congr rfl fun j _ => by rw [C_natCast'])
  have h1 : Bd ((2 : Poly) ^ P.aP * (spolyV P.wP (EP P) Wp P.D S.pos
      - ∑ j ∈ range S.negs.length, ((S.negm.getD j 0 : ℕ) : Poly) * spolyV P.wP (EP P) Wp P.D (S.negs.getD j 0)))
      (2 ^ P.aP * ((P.D + 1) * (2 ^ (P.wP - 1) * (2 ^ P.m) ^ P.D)
        + lsum S.negm * ((P.D + 1) * (2 ^ (P.wP - 1) * (2 ^ P.m) ^ P.D)))) P.D := by
    have := (bd_two_pow P.aP).mul ((hs S.pos).sub hn)
    simpa using this
  have h2 : Bd ((2 : Poly) ^ P.aF * (S.roots.map (rootUseV P (EP P) Wp)).sum)
      (2 ^ P.aF * (S.roots.length * (nRootUse P * (2 ^ (P.wG - 1) * (2 ^ P.m) ^ P.D)))) P.D := by
    have := (bd_two_pow P.aF).mul (roots_bd hD hG hW S.roots hR)
    simpa using this
  refine (h1.sub h2).mono (le_of_eq ?_) le_rfl
  unfold nShare
  show _ = (((lsum S.negm + 1) * (P.D + 1)) <<< (P.wP - 1 + P.aP)
    + (lenR S.roots * nRootUse P) <<< (P.wG - 1 + P.aF)) <<< (P.m * P.D)
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, lenR_eq, pow_add, pow_add, pow_mul]
  ring

end CAP.Wsos
