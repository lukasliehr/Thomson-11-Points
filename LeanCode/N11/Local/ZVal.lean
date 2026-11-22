module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import N11.Local.Kernel

/-!
# G7 of route G: the values of the signed integers and of the loops of the checks

`zr a` is the value `a.1 - a.2` of a pair, as a real number. The operations of `Kernel.lean` on pairs are the
operations on the values, the loops are sums over ranges, and the tests `zeq`, `zle` are the equality and the
order of the values. `zr_dotB`: the sum of the products of two blocks of a table of the shape `33 × 33`, taken in
step, is the double sum over the indices.
-/

@[expose] public section

namespace N11.Local

open Finset

/-- The value of a pair: `p - n`. -/
def zr (a : ℕ × ℕ) : ℝ := (a.1 : ℝ) - (a.2 : ℝ)

theorem forceN_eq {α : Type} (d : α) (v : ℕ) (f : ℕ → α) : forceN d v f = f v := rfl

theorem zmk_eq (p n : ℕ) : zmk p n = (p, n) := rfl

theorem zr_pair (p n : ℕ) : zr (p, n) = (p : ℝ) - (n : ℝ) := rfl

theorem zr_zero : zr (0, 0) = 0 := by
  rw [zr_pair]
  simp

theorem zr_add (a b : ℕ × ℕ) : zr (zadd a b) = zr a + zr b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  show zr (a1 + b1, a2 + b2) = _
  simp only [zr_pair]
  push_cast
  ring

theorem zr_sub (a b : ℕ × ℕ) : zr (zsub a b) = zr a - zr b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  show zr (a1 + b2, a2 + b1) = _
  simp only [zr_pair]
  push_cast
  ring

theorem zr_neg (a : ℕ × ℕ) : zr (zneg a) = -zr a := by
  obtain ⟨a1, a2⟩ := a
  show zr (a2, a1) = _
  simp only [zr_pair]
  ring

theorem zr_mul (a b : ℕ × ℕ) : zr (zmul a b) = zr a * zr b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  show zr (a1 * b1 + a2 * b2, a1 * b2 + a2 * b1) = _
  simp only [zr_pair]
  push_cast
  ring

theorem zr_nat (k : ℕ) (a : ℕ × ℕ) : zr (znat k a) = (k : ℝ) * zr a := by
  obtain ⟨a1, a2⟩ := a
  show zr (k * a1, k * a2) = _
  simp only [zr_pair]
  push_cast
  ring

theorem zeq_sound {a b : ℕ × ℕ} (h : zeq a b = true) : zr a = zr b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  have h' : Nat.beq (a1 + b2) (b1 + a2) = true := h
  have e := congrArg (Nat.cast : ℕ → ℝ) (Nat.eq_of_beq_eq_true h')
  push_cast at e
  simp only [zr_pair]
  linarith

theorem zle_sound {a b : ℕ × ℕ} (h : zle a b = true) : zr a ≤ zr b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  have h' : Nat.ble (a1 + b2) (b1 + a2) = true := h
  have e : ((a1 + b2 : ℕ) : ℝ) ≤ ((b1 + a2 : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_of_ble_eq_true h')
  push_cast at e
  simp only [zr_pair]
  linarith

theorem zr_ind (b : Bool) (v : ℕ × ℕ) : zr (ind b v) = if b = true then zr v else 0 := by
  cases b
  · show zr (0, 0) = _
    rw [zr_zero]
    simp
  · show zr v = _
    simp

theorem zr_zsum (f : ℕ → ℕ × ℕ) (n : ℕ) : zr (zsum f n) = ∑ k ∈ range n, zr (f k) := by
  induction n with
  | zero =>
    show zr (0, 0) = _
    rw [zr_zero]
    simp
  | succ n ih =>
    rw [sum_range_succ, ← ih]
    exact zr_add _ _

theorem zr_zsumP (f : ℕ → ℕ → ℕ × ℕ) :
    zr (zsumP f) = ∑ i ∈ range 11, ∑ j ∈ range 11, if i < j then zr (f i j) else 0 := by
  unfold zsumP
  rw [zr_zsum]
  refine sum_congr rfl fun i _ => ?_
  rw [zr_zsum]
  refine sum_congr rfl fun j _ => ?_
  rw [zr_ind]
  by_cases h : i < j
  · have hb : Nat.blt i j = true := by
      rw [Nat.blt_eq]
      exact h
    rw [if_pos h, if_pos hb]
  · have hb : ¬ Nat.blt i j = true := by
      rw [Nat.blt_eq]
      exact h
    rw [if_neg h, if_neg hb]

theorem ball_sound {f : ℕ → Bool} {n : ℕ} (h : ball f n = true) : ∀ k, k < n → f k = true := by
  induction n with
  | zero =>
    intro k hk
    omega
  | succ n ih =>
    have h' : (ball f n && f n) = true := h
    rw [Bool.and_eq_true] at h'
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h1 | h1
    · exact ih h'.1 k h1
    · rw [h1]
      exact h'.2

theorem nsum_eq (f : ℕ → ℕ) (n : ℕ) : nsum f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_range_succ, ← ih]
    rfl

/-- `Prod.rec` with a function of the pair. -/
theorem prod_rec_eta {α : Type} (f : ℕ × ℕ → α) (x : ℕ × ℕ) :
    Prod.rec (motive := fun _ => α) (fun a b => f (a, b)) x = f x := by
  obtain ⟨a, b⟩ := x
  rfl

/-! ## Lists -/

theorem lenN_eq (l : List ℕ) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih =>
    show Nat.succ (lenN _) = _
    rw [ih]
    rfl

theorem lenLN_eq (l : List (List ℕ)) : lenLN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih =>
    show Nat.succ (lenLN _) = _
    rw [ih]
    rfl

theorem zr_dotR (off : ℕ) : ∀ (xs ys : List ℕ), xs.length = ys.length →
    zr (dotR off xs ys)
      = ∑ k ∈ range xs.length, ((getN xs k : ℝ) - (off : ℝ)) * ((getN ys k : ℝ) - (off : ℝ)) := by
  intro xs
  induction xs with
  | nil =>
    intro ys _
    show zr (0, 0) = _
    rw [zr_zero]
    simp
  | cons x xs ih =>
    intro ys hl
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have hl' : xs.length = ys.length := by simpa using hl
      show zr (zadd (zmul (x, off) (y, off)) (dotR off xs ys)) = _
      rw [zr_add, zr_mul, ih ys hl', List.length_cons, sum_range_succ']
      simp only [zr_pair]
      have e : ∀ k, getN (x :: xs) (k + 1) = getN xs k := fun _ => rfl
      have e' : ∀ k, getN (y :: ys) (k + 1) = getN ys k := fun _ => rfl
      have e0 : getN (x :: xs) 0 = x := rfl
      have e0' : getN (y :: ys) 0 = y := rfl
      simp only [e, e', e0, e0']
      ring

theorem zr_dotB (off : ℕ) : ∀ (A B : List (List ℕ)), A.length = B.length →
    zr (dotB off A B) = ∑ b ∈ range A.length, zr (dotR off (getLN A b) (getLN B b)) := by
  intro A
  induction A with
  | nil =>
    intro B _
    show zr (0, 0) = _
    rw [zr_zero]
    simp
  | cons r A ih =>
    intro B hl
    cases B with
    | nil => simp at hl
    | cons s B =>
      have hl' : A.length = B.length := by simpa using hl
      show zr (zadd (dotR off r s) (dotB off A B)) = _
      rw [zr_add, ih B hl', List.length_cons, sum_range_succ']
      have e : ∀ k, getLN (r :: A) (k + 1) = getLN A k := fun _ => rfl
      have e' : ∀ k, getLN (s :: B) (k + 1) = getLN B k := fun _ => rfl
      have e0 : getLN (r :: A) 0 = r := rfl
      have e0' : getLN (s :: B) 0 = s := rfl
      simp only [e, e', e0, e0']
      ring

end N11.Local
