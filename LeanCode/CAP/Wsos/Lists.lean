module

public import CAP.Wsos.Rep

/-!
# The loops of the checker in closed form

The functions of `CAP.Wsos` that walk through lists and digits are written here as sums over
ranges. A list is described by its length and its entries (`List.getD`), a number by its slots
(`CAP.slot`). No polynomial occurs in the first part; the second part transports sums through
`Rep` and `Bd`.
-/

@[expose] public section

namespace CAP.Wsos

open Finset MvPolynomial

/-! ## Lists -/

theorem hd_eq (l : List ℕ) : hd l = l.getD 0 0 := by cases l <;> rfl

theorem tl_eq (l : List ℕ) : tl l = l.tail := by cases l <;> rfl

theorem lsum_cons (a : ℕ) (l : List ℕ) : lsum (a :: l) = a + lsum l := rfl

theorem len_cons (a : ℕ) (l : List ℕ) : len (a :: l) = len l + 1 := rfl

theorem len_eq (l : List ℕ) : len l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [len_cons, ih, List.length_cons]

theorem nth_eq (l : List ℕ) (i : ℕ) : nth l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ j => exact ih j

theorem getD_tail (l : List ℕ) (i : ℕ) : l.tail.getD i 0 = l.getD (i + 1) 0 := by
  cases l <;> simp

/-- The sum of a list as a sum over its indices. -/
theorem lsum_eq (l : List ℕ) : lsum l = ∑ i ∈ range l.length, l.getD i 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [lsum_cons, ih, List.length_cons, sum_range_succ']
    simp [add_comm]

theorem rep_length (x n : ℕ) : (rep x n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => show (x :: rep x n).length = n + 1; rw [List.length_cons, ih]

theorem rep_getD (x : ℕ) : ∀ (n i : ℕ), i < n → (rep x n).getD i 0 = x
  | n + 1, 0, _ => rfl
  | n + 1, i + 1, h => rep_getD x n i (Nat.lt_of_succ_lt_succ h)

/-! ## Powers -/

/-- `cur * w ^ i` modulo `2 ^ M`, by repeated multiplication. -/
def pwr (mM w cur : ℕ) : ℕ → ℕ
  | 0 => cur
  | i + 1 => mulM mM (pwr mM w cur i) w

theorem pwr_shift (mM w cur : ℕ) : ∀ i, pwr mM w (mulM mM cur w) i = pwr mM w cur (i + 1)
  | 0 => rfl
  | i + 1 => by show mulM mM (pwr mM w (mulM mM cur w) i) w = _; rw [pwr_shift mM w cur i]; rfl

theorem pows_succ (mM w n cur : ℕ) : pows mM w (n + 1) cur = cur :: pows mM w n (mulM mM cur w) := rfl

theorem pows_length (mM w : ℕ) : ∀ n cur, (pows mM w n cur).length = n
  | 0, _ => rfl
  | n + 1, cur => by rw [pows_succ, List.length_cons, pows_length mM w n]

theorem pows_getD (mM w : ℕ) : ∀ (n cur i : ℕ), i < n → (pows mM w n cur).getD i 0 = pwr mM w cur i
  | n + 1, cur, 0, _ => rfl
  | n + 1, cur, i + 1, h => by
    rw [pows_succ, List.getD_cons_succ, pows_getD mM w n _ i (Nat.lt_of_succ_lt_succ h), pwr_shift]

theorem hl_succ (m n : ℕ) (pw : List ℕ) (s : ℕ) :
    hl m (n + 1) pw s = Nat.shiftLeft (hd pw) s :: hl m n (tl pw) (Nat.sub s m) := rfl

theorem hl_length (m : ℕ) : ∀ (n : ℕ) (pw : List ℕ) (s : ℕ), (hl m n pw s).length = n
  | 0, _, _ => rfl
  | n + 1, pw, s => by rw [hl_succ, List.length_cons, hl_length m n]

theorem hl_getD (m : ℕ) : ∀ (n : ℕ) (pw : List ℕ) (s i : ℕ), i < n →
    (hl m n pw s).getD i 0 = pw.getD i 0 <<< (s - m * i)
  | n + 1, pw, s, 0, _ => by rw [hl_succ, List.getD_cons_zero, hd_eq]; rfl
  | n + 1, pw, s, i + 1, h => by
    rw [hl_succ, List.getD_cons_succ, hl_getD m n _ _ i (Nat.lt_of_succ_lt_succ h), tl_eq, getD_tail]
    show _ <<< (s - m - m * i) = _
    rw [Nat.sub_sub, Nat.mul_succ, Nat.add_comm (m * i) m]

/-! ## Sums of products with slots -/

theorem slot_zero (w x : ℕ) : slot w x 0 = x &&& mask w := by
  show (x >>> (w * 0)) &&& mask w = _
  rw [Nat.mul_zero, Nat.shiftRight_zero]

theorem slot_shiftRight (w x i : ℕ) : slot w (x >>> w) i = slot w x (i + 1) := by
  have h := slot_div w x 1 i
  rw [Nat.mul_one, Nat.add_comm] at h
  rw [Nat.shiftRight_eq_div_pow]
  exact h

theorem slot_shiftRight_mul (w x o i : ℕ) : slot w (x >>> (w * o)) i = slot w x (o + i) := by
  rw [Nat.shiftRight_eq_div_pow]
  exact slot_div w x o i

theorem dot_cons (w mw b : ℕ) (l : List ℕ) (Cr U : ℕ) :
    dot w mw (b :: l) Cr U = dot w mw l (Nat.shiftRight Cr w) (Nat.add U (Nat.mul (Nat.land Cr mw) b)) := rfl

/-- The loop `dot` in closed form. -/
theorem dot_eq (w : ℕ) : ∀ (l : List ℕ) (Cr U : ℕ),
    dot w (mask w) l Cr U = U + ∑ i ∈ range l.length, slot w Cr i * l.getD i 0
  | [], Cr, U => by simp [dot]
  | b :: l, Cr, U => by
    rw [dot_cons, dot_eq w l, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [slot_zero]
    have h : ∀ i, slot w (Nat.shiftRight Cr w) i = slot w Cr (i + 1) := slot_shiftRight w Cr
    simp only [h]
    show U + (Cr &&& mask w) * b + _ = _
    ring

theorem dsum_succ (w mw n Cr U : ℕ) :
    dsum w mw (n + 1) Cr U = dsum w mw n (Nat.shiftRight Cr w) (Nat.add U (Nat.land Cr mw)) := rfl

/-- The loop `dsum` in closed form. -/
theorem dsum_eq (w : ℕ) : ∀ (n Cr U : ℕ), dsum w (mask w) n Cr U = U + ∑ i ∈ range n, slot w Cr i
  | 0, Cr, U => by simp [dsum]
  | n + 1, Cr, U => by
    rw [dsum_succ, dsum_eq w n, sum_range_succ', slot_zero]
    have h : ∀ i, slot w (Nat.shiftRight Cr w) i = slot w Cr (i + 1) := slot_shiftRight w Cr
    simp only [h]
    show U + (Cr &&& mask w) + _ = _
    ring

/-- The bias of a list of powers. -/
theorem bias_eq (w : ℕ) (l : List ℕ) : bias w l = 2 ^ (w - 1) * ∑ i ∈ range l.length, l.getD i 0 := by
  show (lsum l) <<< (w - 1) = _
  rw [Nat.shiftLeft_eq, lsum_eq, mul_comm]

/-! ## Sums through `Rep` and `Bd` -/

theorem Rep.sum {P : Params} {ι : Type*} (s : Finset ι) (f : ι → ℕ) (F : ι → Poly)
    (h : ∀ i ∈ s, Rep P (f i) (F i)) : Rep P (∑ i ∈ s, f i) (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Rep.zero
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem Bd.sum {ι : Type*} (s : Finset ι) (F : ι → Poly) (B : ι → ℕ) (d : ℕ)
    (h : ∀ i ∈ s, Bd (F i) (B i) d) : Bd (∑ i ∈ s, F i) (∑ i ∈ s, B i) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Bd.zero.mono (Nat.zero_le _) (Nat.zero_le d)
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- A sum of terms with a common bound. -/
theorem Bd.sum_le {ι : Type*} (s : Finset ι) (F : ι → Poly) (B d : ℕ)
    (h : ∀ i ∈ s, Bd (F i) B d) : Bd (∑ i ∈ s, F i) (s.card * B) d := by
  have := Bd.sum s F (fun _ => B) d h
  simpa using this

/-- An integer constant. -/
theorem Bd.intC {c : ℤ} {n : ℕ} (h : |c| ≤ n) {F : Poly} {B d : ℕ} (hF : Bd F B d) :
    Bd (MvPolynomial.C c * F) (n * B) d := by
  simpa using (Bd.C h).mul hF

/-! ## Signed digits -/

/-- Slot `j` of width `w` of `c`, minus the bias `2 ^ (w - 1)`. -/
def sdig (w c j : ℕ) : ℤ := (slot w c j : ℤ) - 2 ^ (w - 1)

theorem abs_sdig_le (w c j : ℕ) (hw : 1 ≤ w) : |sdig w c j| ≤ ((2 ^ (w - 1) : ℕ) : ℤ) := by
  have h1 : slot w c j < 2 ^ w := slot_lt w c j
  rw [two_pow_pred hw] at h1
  have h2 : ((slot w c j : ℕ) : ℤ) < 2 * ((2 ^ (w - 1) : ℕ) : ℤ) := by exact_mod_cast h1
  have h3 : (0 : ℤ) ≤ ((slot w c j : ℕ) : ℤ) := Int.natCast_nonneg _
  have h4 : ((2 : ℤ) ^ (w - 1)) = ((2 ^ (w - 1) : ℕ) : ℤ) := by push_cast; rfl
  unfold sdig
  rw [h4, abs_le]
  constructor <;> linarith

/-- The value of the polynomial with the signed digits of `Cr` and the powers of the list `h`:
the loop `dot` minus the bias. -/
theorem sdot_rep {P : Params} {pM mM : ℕ} (hM : Mod P pM mM) (w : ℕ) (h : List ℕ) (H : ℕ → Poly)
    (hH : ∀ i, i < h.length → Rep P (h.getD i 0) (H i)) (Cr : ℕ) :
    Rep P (subM pM mM (dot w (mask w) h Cr 0) (bias w h)) (∑ i ∈ range h.length, C (sdig w Cr i) * H i) := by
  have h1 : Rep P (dot w (mask w) h Cr 0) (∑ i ∈ range h.length, C (slot w Cr i : ℤ) * H i) := by
    rw [dot_eq, zero_add]
    exact Rep.sum _ _ _ fun i hi => Rep.smul _ (hH i (mem_range.mp hi))
  have h2 : Rep P (bias w h) (C ((2 ^ (w - 1) : ℕ) : ℤ) * ∑ i ∈ range h.length, H i) := by
    rw [bias_eq]
    exact Rep.smul _ (Rep.sum _ _ _ fun i hi => hH i (mem_range.mp hi))
  refine (h1.subM hM h2).congr ?_
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  unfold sdig
  rw [C_sub]
  push_cast
  ring

theorem sdot_bd (w : ℕ) (hw : 1 ≤ w) (n : ℕ) (H : ℕ → Poly) (B d : ℕ)
    (hH : ∀ i, i < n → Bd (H i) B d) (Cr : ℕ) :
    Bd (∑ i ∈ range n, C (sdig w Cr i) * H i) (n * (2 ^ (w - 1) * B)) d := by
  have := Bd.sum_le (range n) (fun i => C (sdig w Cr i) * H i) (2 ^ (w - 1) * B) d
    (fun i hi => Bd.intC (abs_sdig_le w Cr i hw) (hH i (mem_range.mp hi)))
  simpa using this

end CAP.Wsos
