module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import CAP.Core.PackedLemmas
public import CAP.Wsos.Kernel

/-!
# Numbers that stand for polynomials

The checker `CAP.Wsos.checkTy` computes with natural numbers. This file states what such a number
means: `Rep P n F` says that the number `n` and the value of the polynomial `F ∈ ℤ[x, y, z]` at the
point `(2 ^ W, 2 ^ (W * k1), 2 ^ (W * k2))` agree modulo `2 ^ M`. The value at a point is a
homomorphism of rings, so every step of the checker (a sum, a product, a difference modulo
`2 ^ M`, a reduction, a shift) is a step on polynomials, without any condition on degrees or on
the sizes of coefficients.

Sizes enter once, at the end: a polynomial of total degree at most `D`, whose coefficients have
absolute values with a sum below `2 ^ (W - 1)`, and whose number vanishes modulo `2 ^ M`, is the
zero polynomial (`kron_zero`), if the map from the monomials of degree at most `D` to the slots is
injective. To bound the coefficients of a polynomial that is built by ring operations, we carry a
polynomial with natural coefficients that dominates it coefficient by coefficient (`Maj`); the sum
of its coefficients is its value at `(1, 1, 1)`, which is again a homomorphism (`csum`).
-/

@[expose] public section

namespace CAP.Wsos

open MvPolynomial Finset

/-- Polynomials in the coordinates `x, y, z` of the box. -/
abbrev Poly := MvPolynomial (Fin 3) ℤ

/-- Polynomials with natural coefficients, used as bounds. -/
abbrev NPoly := MvPolynomial (Fin 3) ℕ

/-- The point at which a number stands for a polynomial. -/
def kpt (P : Params) : Fin 3 → ℤ := ![2 ^ P.W, 2 ^ (P.W * P.k1), 2 ^ (P.W * P.k2)]

/-- The value of a polynomial at the point of the layout. -/
noncomputable def ev (P : Params) : Poly →+* ℤ := eval (kpt P)

/-- The number of bits of the modulus: `M = W * slots`. -/
def Mb (P : Params) : ℕ := P.W * P.slots

/-- The number `n` stands for the polynomial `F`. -/
def Rep (P : Params) (n : ℕ) (F : Poly) : Prop := (n : ℤ) ≡ ev P F [ZMOD (2 : ℤ) ^ Mb P]

/-- `pM` and `mM` are `2 ^ M` and `2 ^ M - 1`. -/
structure Mod (P : Params) (pM mM : ℕ) : Prop where
  hp : pM = 2 ^ Mb P
  hm : mM = 2 ^ Mb P - 1

theorem mod_of (P : Params) :
    Mod P (Nat.shiftLeft 1 (Nat.mul P.W P.slots)) (Nat.sub (Nat.shiftLeft 1 (Nat.mul P.W P.slots)) 1) := by
  constructor
  · show 1 <<< (P.W * P.slots) = 2 ^ Mb P
    rw [Nat.one_shiftLeft]; rfl
  · show 1 <<< (P.W * P.slots) - 1 = 2 ^ Mb P - 1
    rw [Nat.one_shiftLeft]; rfl

namespace Rep

variable {P : Params} {a b : ℕ} {F G : Poly}

theorem add (h₁ : Rep P a F) (h₂ : Rep P b G) : Rep P (a + b) (F + G) := by
  unfold Rep at *
  rw [Nat.cast_add, map_add]
  exact h₁.add h₂

theorem mul (h₁ : Rep P a F) (h₂ : Rep P b G) : Rep P (a * b) (F * G) := by
  unfold Rep at *
  rw [Nat.cast_mul, map_mul]
  exact h₁.mul h₂

theorem natCast (c : ℕ) : Rep P c (C (c : ℤ)) := by
  unfold Rep
  rw [show ev P (C (c : ℤ)) = (c : ℤ) from eval_C _]

theorem zero : Rep P 0 0 := by simpa using natCast (P := P) 0

theorem one : Rep P 1 1 := by simpa using natCast (P := P) 1

theorem smul (c : ℕ) (h : Rep P a F) : Rep P (c * a) (C (c : ℤ) * F) := (natCast c).mul h

theorem smul' (c : ℕ) (h : Rep P a F) : Rep P (a * c) (C (c : ℤ) * F) := by
  rw [mul_comm]; exact smul c h

theorem shiftLeft (s : ℕ) (h : Rep P a F) : Rep P (a <<< s) (C ((2 : ℤ) ^ s) * F) := by
  rw [Nat.shiftLeft_eq, mul_comm]
  have := smul (2 ^ s) h
  simpa using this

theorem congr (h : Rep P a F) (hF : F = G) : Rep P a G := hF ▸ h

/-- Reduction modulo `2 ^ M`. -/
theorem land {pM mM : ℕ} (hM : Mod P pM mM) (h : Rep P a F) : Rep P (a &&& mM) F := by
  unfold Rep at *
  rw [hM.hm, Nat.and_two_pow_sub_one_eq_mod]
  refine Int.ModEq.trans ?_ h
  rw [Int.natCast_mod]
  push_cast
  exact Int.mod_modEq _ _

theorem mulM {pM mM : ℕ} (hM : Mod P pM mM) (h₁ : Rep P a F) (h₂ : Rep P b G) :
    Rep P (mulM mM a b) (F * G) := (h₁.mul h₂).land hM

/-- Subtraction modulo `2 ^ M`. -/
theorem subM {pM mM : ℕ} (hM : Mod P pM mM) (h₁ : Rep P a F) (h₂ : Rep P b G) :
    Rep P (subM pM mM a b) (F - G) := by
  have hb : Rep P (b &&& mM) G := h₂.land hM
  have hle : b &&& mM ≤ a + pM := by
    have : b &&& mM ≤ mM := Nat.and_le_right
    have h1 : mM ≤ pM := by rw [hM.hm, hM.hp]; exact Nat.sub_le _ _
    omega
  unfold Rep at *
  show ((a + pM - (b &&& mM) : ℕ) : ℤ) ≡ _ [ZMOD _]
  rw [Nat.cast_sub hle, Nat.cast_add, map_sub, hM.hp]
  push_cast
  have h3 : ((a : ℤ) + 2 ^ Mb P) ≡ ev P F [ZMOD (2 : ℤ) ^ Mb P] := by
    have h0 : ((2 : ℤ) ^ Mb P) ≡ 0 [ZMOD (2 : ℤ) ^ Mb P] := Int.modEq_zero_iff_dvd.mpr (dvd_refl _)
    simpa using h₁.add h0
  exact h3.sub hb

end Rep

/-! ## The variables -/

theorem ev_X0 (P : Params) : ev P (X 0) = 2 ^ P.W := by simp [ev, kpt]

theorem ev_X1 (P : Params) : ev P (X 1) = 2 ^ (P.W * P.k1) := by simp [ev, kpt]

theorem ev_X2 (P : Params) : ev P (X 2) = 2 ^ (P.W * P.k2) := by simp [ev, kpt]

theorem rep_X0 (P : Params) : Rep P (Nat.shiftLeft 1 P.W) (X 0) := by
  unfold Rep
  rw [ev_X0]
  show ((1 <<< P.W : ℕ) : ℤ) ≡ _ [ZMOD _]
  rw [Nat.one_shiftLeft]; push_cast; rfl

theorem rep_X1 (P : Params) : Rep P (Nat.shiftLeft 1 (Nat.mul P.W P.k1)) (X 1) := by
  unfold Rep
  rw [ev_X1]
  show ((1 <<< (P.W * P.k1) : ℕ) : ℤ) ≡ _ [ZMOD _]
  rw [Nat.one_shiftLeft]; push_cast; rfl

theorem rep_X2 (P : Params) : Rep P (Nat.shiftLeft 1 (Nat.mul P.W P.k2)) (X 2) := by
  unfold Rep
  rw [ev_X2]
  show ((1 <<< (P.W * P.k2) : ℕ) : ℤ) ≡ _ [ZMOD _]
  rw [Nat.one_shiftLeft]; push_cast; rfl

/-! ## Bounds for the coefficients -/

/-- The sum of the coefficients of a polynomial with natural coefficients. -/
noncomputable def csum : NPoly →+* ℕ := eval (fun _ => 1)

theorem coeff_le_csum (G : NPoly) (m : Fin 3 →₀ ℕ) : coeff m G ≤ csum G := by
  unfold csum
  rw [eval_eq']
  simp only [one_pow, prod_const_one, mul_one]
  by_cases hm : m ∈ G.support
  · exact single_le_sum (f := fun m => coeff m G) (fun _ _ => Nat.zero_le _) hm
  · rw [notMem_support_iff.mp hm]; exact Nat.zero_le _

/-- `G` dominates `F` coefficient by coefficient. -/
def Maj (F : Poly) (G : NPoly) : Prop := ∀ m, |coeff m F| ≤ ((coeff m G : ℕ) : ℤ)

namespace Maj

variable {F F' : Poly} {G G' : NPoly}

theorem add (h : Maj F G) (h' : Maj F' G') : Maj (F + F') (G + G') := fun m => by
  rw [coeff_add, coeff_add, Nat.cast_add]
  exact (abs_add_le _ _).trans (add_le_add (h m) (h' m))

theorem neg (h : Maj F G) : Maj (-F) G := fun m => by
  rw [coeff_neg, abs_neg]; exact h m

theorem sub (h : Maj F G) (h' : Maj F' G') : Maj (F - F') (G + G') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem mul (h : Maj F G) (h' : Maj F' G') : Maj (F * F') (G * G') := fun m => by
  rw [coeff_mul, coeff_mul, Nat.cast_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  rw [abs_mul, Nat.cast_mul]
  exact mul_le_mul (h _) (h' _) (abs_nonneg _) (Nat.cast_nonneg _)

theorem C {c : ℤ} {n : ℕ} (h : |c| ≤ n) : Maj (MvPolynomial.C c) (MvPolynomial.C n) := fun m => by
  rw [coeff_C, coeff_C]
  split_ifs
  · exact h
  · simp

theorem X (i : Fin 3) : Maj (MvPolynomial.X i) (MvPolynomial.X i) := fun m => by
  rw [coeff_X, coeff_X]
  split_ifs <;> simp

theorem zero : Maj 0 0 := fun m => by simp

theorem one : Maj 1 1 := by simpa using C (c := 1) (n := 1) (by simp)

theorem pow (h : Maj F G) : ∀ n : ℕ, Maj (F ^ n) (G ^ n)
  | 0 => by simpa using one
  | n + 1 => by rw [pow_succ, pow_succ]; exact (pow h n).mul h

theorem sum {ι : Type*} (s : Finset ι) (f : ι → Poly) (g : ι → NPoly) (h : ∀ i ∈ s, Maj (f i) (g i)) :
    Maj (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem support_subset (h : Maj F G) : ∀ m ∈ F.support, m ∈ G.support := fun m hm => by
  rw [mem_support_iff] at hm ⊢
  intro h0
  have := h m
  rw [h0, Nat.cast_zero] at this
  exact hm (abs_nonpos_iff.mp this)

theorem totalDegree_le (h : Maj F G) : F.totalDegree ≤ G.totalDegree := by
  refine Finset.sup_le fun m hm => ?_
  exact Finset.le_sup (f := fun s => s.sum fun _ e => e) (h.support_subset m hm)

theorem coeff_le (h : Maj F G) (m : Fin 3 →₀ ℕ) : |coeff m F| ≤ (csum G : ℤ) :=
  (h m).trans (by exact_mod_cast coeff_le_csum G m)

end Maj

/-- `F` has total degree at most `deg`, and it is dominated by a polynomial whose coefficients
have a sum of at most `B`. -/
def Bd (F : Poly) (B deg : ℕ) : Prop := ∃ G : NPoly, Maj F G ∧ csum G ≤ B ∧ G.totalDegree ≤ deg

namespace Bd

variable {F F' : Poly} {B B' d d' : ℕ}

theorem mono (h : Bd F B d) (hB : B ≤ B') (hd : d ≤ d') : Bd F B' d' := by
  obtain ⟨G, h1, h2, h3⟩ := h
  exact ⟨G, h1, h2.trans hB, h3.trans hd⟩

theorem add (h : Bd F B d) (h' : Bd F' B' d) : Bd (F + F') (B + B') d := by
  obtain ⟨G, h1, h2, h3⟩ := h
  obtain ⟨G', h1', h2', h3'⟩ := h'
  refine ⟨G + G', h1.add h1', ?_, (totalDegree_add _ _).trans (max_le h3 h3')⟩
  rw [map_add]; exact add_le_add h2 h2'

theorem sub (h : Bd F B d) (h' : Bd F' B' d) : Bd (F - F') (B + B') d := by
  obtain ⟨G, h1, h2, h3⟩ := h
  obtain ⟨G', h1', h2', h3'⟩ := h'
  refine ⟨G + G', h1.sub h1', ?_, (totalDegree_add _ _).trans (max_le h3 h3')⟩
  rw [map_add]; exact add_le_add h2 h2'

theorem neg (h : Bd F B d) : Bd (-F) B d := by
  obtain ⟨G, h1, h2, h3⟩ := h
  exact ⟨G, h1.neg, h2, h3⟩

theorem mul (h : Bd F B d) (h' : Bd F' B' d') : Bd (F * F') (B * B') (d + d') := by
  obtain ⟨G, h1, h2, h3⟩ := h
  obtain ⟨G', h1', h2', h3'⟩ := h'
  refine ⟨G * G', h1.mul h1', ?_, (totalDegree_mul _ _).trans (add_le_add h3 h3')⟩
  rw [map_mul]; exact Nat.mul_le_mul h2 h2'

theorem C {c : ℤ} {n : ℕ} (h : |c| ≤ n) : Bd (MvPolynomial.C c) n 0 :=
  ⟨MvPolynomial.C n, Maj.C h, by simp [csum], (totalDegree_C n).le⟩

theorem natCast (n : ℕ) : Bd (MvPolynomial.C (n : ℤ)) n 0 := C (by simp)

theorem zero : Bd 0 0 0 := by simpa using natCast 0

theorem one : Bd 1 1 0 := by simpa using natCast 1

theorem X (i : Fin 3) : Bd (MvPolynomial.X i) 1 1 :=
  ⟨MvPolynomial.X i, Maj.X i, by simp [csum], by simp⟩

theorem smul (c : ℕ) (h : Bd F B d) : Bd (MvPolynomial.C (c : ℤ) * F) (c * B) d := by
  simpa using (natCast c).mul h

theorem pow (h : Bd F B d) : ∀ n : ℕ, Bd (F ^ n) (B ^ n) (d * n)
  | 0 => by simpa using one
  | n + 1 => by
    rw [pow_succ, pow_succ, Nat.mul_succ]
    exact (pow h n).mul h

theorem totalDegree_le (h : Bd F B d) : F.totalDegree ≤ d := by
  obtain ⟨G, h1, _, h3⟩ := h
  exact h1.totalDegree_le.trans h3

theorem coeff_le (h : Bd F B d) (m : Fin 3 →₀ ℕ) : |coeff m F| ≤ (B : ℤ) := by
  obtain ⟨G, h1, h2, _⟩ := h
  exact (h1.coeff_le m).trans (by exact_mod_cast h2)

theorem congr {G : Poly} (h : Bd F B d) (hF : F = G) : Bd G B d := hF ▸ h

end Bd

/-- The number `n` stands for `F`, with bounds for the coefficients and the degree of `F`. -/
structure Sem (P : Params) (n : ℕ) (F : Poly) (B deg : ℕ) : Prop where
  rep : Rep P n F
  bd : Bd F B deg

end CAP.Wsos
