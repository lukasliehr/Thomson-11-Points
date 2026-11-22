module

public import CAP.Wsos.Kron
public import CAP.Wsos.Gens

/-!
# The squares of a weight

A weight supplies a number `col i` for every column. The checker keeps the bits of `col i` in the
mask `allowed = (2 ^ w0 - 1) * mono`, where `mono` is the number of the polynomial `HP δ` that has
the coefficient `1` at every monomial of degree at most `δ`. This file shows that the masked
number minus the bias is, exactly, the value of a polynomial `ξ` of degree at most `δ` with
coefficients between `-2 ^ (w0 - 1)` and `2 ^ (w0 - 1)` (`masked_exists`), whatever `col i` is.
Hence the sum of the squares that the checker forms is the value of a sum of squares of
polynomials (`sqSum_exists`), and the sum over the weights stands for a polynomial that is
nonnegative wherever the generators are nonnegative (`weightsGo_exists`).
-/

@[expose] public section

namespace CAP.Wsos

open Finset MvPolynomial

/-! ## Sums over the monomials of degree at most `n` -/

section Simplex

variable {A : Type*} [CommSemiring A]

/-- `∑ a ≤ n, x ^ a` -/
def h1 (x : A) (n : ℕ) : A := ∑ a ∈ range (n + 1), x ^ a

/-- `∑ a + b ≤ n, x ^ a * y ^ b` -/
def h2 (x y : A) (n : ℕ) : A := ∑ b ∈ range (n + 1), y ^ b * h1 x (n - b)

/-- `∑ a + b + c ≤ n, x ^ a * y ^ b * z ^ c` -/
def h3 (x y z : A) (n : ℕ) : A := ∑ c ∈ range (n + 1), z ^ c * h2 x y (n - c)

theorem h1_zero (x : A) : h1 x 0 = 1 := by simp [h1]

theorem h2_zero (x y : A) : h2 x y 0 = 1 := by simp [h2, h1]

theorem h3_zero (x y z : A) : h3 x y z 0 = 1 := by simp [h3, h2, h1]

theorem h1_succ (x : A) (n : ℕ) : h1 x (n + 1) = 1 + x * h1 x n := by
  unfold h1
  rw [sum_range_succ', mul_sum, pow_zero, add_comm]
  congr 1
  exact sum_congr rfl fun a _ => by rw [pow_succ, mul_comm]

theorem h2_succ (x y : A) (n : ℕ) : h2 x y (n + 1) = h1 x (n + 1) + y * h2 x y n := by
  unfold h2
  rw [sum_range_succ', mul_sum, pow_zero, one_mul, Nat.sub_zero, add_comm]
  congr 1
  refine sum_congr rfl fun b _ => ?_
  rw [Nat.add_sub_add_right, pow_succ]
  ring

theorem h3_succ (x y z : A) (n : ℕ) : h3 x y z (n + 1) = h2 x y (n + 1) + z * h3 x y z n := by
  unfold h3
  rw [sum_range_succ', mul_sum, pow_zero, one_mul, Nat.sub_zero, add_comm]
  congr 1
  refine sum_congr rfl fun b _ => ?_
  rw [Nat.add_sub_add_right, pow_succ]
  ring

theorem map_h3 {A' : Type*} [CommSemiring A'] (φ : A →+* A') (x y z : A) (n : ℕ) :
    φ (h3 x y z n) = h3 (φ x) (φ y) (φ z) n := by
  simp [h3, h2, h1]

end Simplex

theorem h1_ones (n : ℕ) : h1 (1 : ℕ) n = n + 1 := by simp [h1]

theorem h2_ones : ∀ n : ℕ, 2 * h2 (1 : ℕ) 1 n = (n + 1) * (n + 2)
  | 0 => by rw [h2_zero]; rfl
  | n + 1 => by
    rw [h2_succ, h1_ones, one_mul, mul_add, h2_ones n]
    ring

theorem h3_ones : ∀ n : ℕ, 6 * h3 (1 : ℕ) 1 1 n = (n + 1) * (n + 2) * (n + 3)
  | 0 => by rw [h3_zero]; rfl
  | n + 1 => by
    have h := h2_ones (n + 1)
    have e : 6 * h2 (1 : ℕ) 1 (n + 1) = 3 * ((n + 1 + 1) * (n + 1 + 2)) := by rw [← h]; ring
    rw [h3_succ, one_mul, mul_add, h3_ones n, e]
    ring

theorem nmon_eq (n : ℕ) : nmon n = h3 (1 : ℕ) 1 1 n := by
  show (n + 1) * (n + 2) * (n + 3) / 6 = _
  rw [← h3_ones, Nat.mul_div_cancel_left _ (by norm_num)]

/-! ## The numbers of the monomials -/

/-- The number of the polynomial with the coefficient `1` at every monomial of degree at most `δ`. -/
def monoN (P : Params) (δ : ℕ) : ℕ := h3 (2 ^ P.W) (2 ^ (P.W * P.k1)) (2 ^ (P.W * P.k2)) δ

theorem monoGo_succ (sX sY sZ n m1 m2 m3 : ℕ) :
    monoGo sX sY sZ (n + 1) m1 m2 m3 = m3 :: monoGo sX sY sZ n (Nat.succ (Nat.shiftLeft m1 sX))
      (Nat.add (Nat.succ (Nat.shiftLeft m1 sX)) (Nat.shiftLeft m2 sY))
      (Nat.add (Nat.add (Nat.succ (Nat.shiftLeft m1 sX)) (Nat.shiftLeft m2 sY)) (Nat.shiftLeft m3 sZ)) := rfl

theorem monoGo_spec (sX sY sZ : ℕ) : ∀ (n k : ℕ),
    (monoGo sX sY sZ n (h1 (2 ^ sX) k) (h2 (2 ^ sX) (2 ^ sY) k) (h3 (2 ^ sX) (2 ^ sY) (2 ^ sZ) k)).length = n ∧
    ∀ i, i < n →
      (monoGo sX sY sZ n (h1 (2 ^ sX) k) (h2 (2 ^ sX) (2 ^ sY) k) (h3 (2 ^ sX) (2 ^ sY) (2 ^ sZ) k)).getD i 0
        = h3 (2 ^ sX) (2 ^ sY) (2 ^ sZ) (k + i)
  | 0, _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1, k => by
    have ih := monoGo_spec sX sY sZ n (k + 1)
    have e1 : Nat.succ (Nat.shiftLeft (h1 (2 ^ sX) k) sX) = h1 (2 ^ sX) (k + 1) := by
      show (h1 (2 ^ sX) k) <<< sX + 1 = _
      rw [Nat.shiftLeft_eq, h1_succ]; ring
    have e2 : Nat.add (h1 (2 ^ sX) (k + 1)) (Nat.shiftLeft (h2 (2 ^ sX) (2 ^ sY) k) sY) = h2 (2 ^ sX) (2 ^ sY) (k + 1) := by
      show _ + (h2 (2 ^ sX) (2 ^ sY) k) <<< sY = _
      rw [Nat.shiftLeft_eq, h2_succ]; ring
    have e3 : Nat.add (h2 (2 ^ sX) (2 ^ sY) (k + 1)) (Nat.shiftLeft (h3 (2 ^ sX) (2 ^ sY) (2 ^ sZ) k) sZ)
        = h3 (2 ^ sX) (2 ^ sY) (2 ^ sZ) (k + 1) := by
      show _ + (h3 (2 ^ sX) (2 ^ sY) (2 ^ sZ) k) <<< sZ = _
      rw [Nat.shiftLeft_eq, h3_succ]; ring
    rw [monoGo_succ, e1, e2, e3]
    refine ⟨by rw [List.length_cons, ih.1], fun i hi => ?_⟩
    cases i with
    | zero => rfl
    | succ j =>
      rw [List.getD_cons_succ, ih.2 j (Nat.lt_of_succ_lt_succ hi), show k + 1 + j = k + (j + 1) by omega]

theorem nth_monos (P : Params) {δ : ℕ} (hδ : δ < P.d + 1) :
    nth (monoGo P.W (Nat.mul P.W P.k1) (Nat.mul P.W P.k2) (Nat.succ P.d) 1 1 1) δ = monoN P δ := by
  have := (monoGo_spec P.W (P.W * P.k1) (P.W * P.k2) (P.d + 1) 0).2 δ hδ
  rw [h1_zero, h2_zero, h3_zero, zero_add] at this
  rw [nth_eq]
  exact this

/-! ## The polynomial of the monomials -/

/-- The polynomial with the coefficient `1` at every monomial of degree at most `δ`. -/
noncomputable def HP (δ : ℕ) : Poly := h3 (X 0) (X 1) (X 2) δ

theorem ev_HP (P : Params) (δ : ℕ) : ev P (HP δ) = ((monoN P δ : ℕ) : ℤ) := by
  unfold HP monoN
  rw [map_h3, ev_X0, ev_X1, ev_X2]
  have := map_h3 (Nat.castRingHom ℤ) (2 ^ P.W) (2 ^ (P.W * P.k1)) (2 ^ (P.W * P.k2)) δ
  simpa using this.symm

theorem sum_range_single {M : Type*} [AddCommMonoid M] (n k : ℕ) (F : ℕ → M) (h : ∀ c, c ≠ k → F c = 0) :
    ∑ c ∈ range n, F c = if k < n then F k else 0 := by
  split_ifs with hk
  · exact sum_eq_single k (fun c _ hc => h c hc) (fun hk' => absurd (mem_range.mpr hk) hk')
  · exact sum_eq_zero fun c hc => h c (by rintro rfl; exact hk (mem_range.mp hc))

theorem mono_eq (a b c : ℕ) :
    (X 2 : Poly) ^ c * ((X 1 : Poly) ^ b * (X 0 : Poly) ^ a)
      = monomial (Finsupp.single 2 c + (Finsupp.single 1 b + Finsupp.single 0 a)) 1 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, monomial_mul]
  simp

theorem expo_apply (a b c : ℕ) :
    (Finsupp.single (2 : Fin 3) c + (Finsupp.single (1 : Fin 3) b + Finsupp.single (0 : Fin 3) a)) 0 = a
    ∧ (Finsupp.single (2 : Fin 3) c + (Finsupp.single (1 : Fin 3) b + Finsupp.single (0 : Fin 3) a)) 1 = b
    ∧ (Finsupp.single (2 : Fin 3) c + (Finsupp.single (1 : Fin 3) b + Finsupp.single (0 : Fin 3) a)) 2 = c := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

theorem coeff_mono (a b c : ℕ) (m : Fin 3 →₀ ℕ) :
    coeff m ((X 2 : Poly) ^ c * ((X 1 : Poly) ^ b * (X 0 : Poly) ^ a))
      = if c = m 2 then (if b = m 1 then (if a = m 0 then 1 else 0) else 0) else 0 := by
  rw [mono_eq, coeff_monomial]
  obtain ⟨h0, h1, h2⟩ := expo_apply a b c
  by_cases hc : c = m 2
  · by_cases hb : b = m 1
    · by_cases ha : a = m 0
      · rw [if_pos hc, if_pos hb, if_pos ha, if_pos]
        ext i
        fin_cases i
        · exact h0.trans ha
        · exact h1.trans hb
        · exact h2.trans hc
      · rw [if_pos hc, if_pos hb, if_neg ha, if_neg]
        intro h
        exact ha (h0.symm.trans (congrArg (fun f => f 0) h))
    · rw [if_pos hc, if_neg hb, if_neg]
      intro h
      exact hb (h1.symm.trans (congrArg (fun f => f 1) h))
  · rw [if_neg hc, if_neg]
    intro h
    exact hc (h2.symm.trans (congrArg (fun f => f 2) h))

theorem coeff_HP (δ : ℕ) (m : Fin 3 →₀ ℕ) : coeff m (HP δ) = if m 0 + m 1 + m 2 ≤ δ then 1 else 0 := by
  unfold HP h3 h2 h1
  simp only [mul_sum, coeff_sum, coeff_mono]
  have e3 : ∀ c b : ℕ, ∑ a ∈ range (δ - c - b + 1),
      (if c = m 2 then (if b = m 1 then (if a = m 0 then (1 : ℤ) else 0) else 0) else 0)
      = if m 0 < δ - c - b + 1 then (if c = m 2 then (if b = m 1 then 1 else 0) else 0) else 0 := fun c b => by
    rw [sum_range_single _ (m 0) _ (fun a ha => by simp [ha])]
    simp
  have e2 : ∀ c : ℕ, ∑ b ∈ range (δ - c + 1),
      (if m 0 < δ - c - b + 1 then (if c = m 2 then (if b = m 1 then (1 : ℤ) else 0) else 0) else 0)
      = if m 1 < δ - c + 1 then (if m 0 < δ - c - m 1 + 1 then (if c = m 2 then 1 else 0) else 0) else 0 := fun c => by
    rw [sum_range_single _ (m 1) _ (fun b hb => by simp [hb])]
    simp
  have e1 : ∑ c ∈ range (δ + 1),
      (if m 1 < δ - c + 1 then (if m 0 < δ - c - m 1 + 1 then (if c = m 2 then (1 : ℤ) else 0) else 0) else 0)
      = if m 2 < δ + 1 then (if m 1 < δ - m 2 + 1 then (if m 0 < δ - m 2 - m 1 + 1 then 1 else 0) else 0) else 0 := by
    rw [sum_range_single _ (m 2) _ (fun c hc => by simp [hc])]
    simp
  simp only [e3, e2, e1]
  split_ifs <;> first | rfl | omega

theorem mem_support_HP (δ : ℕ) (m : Fin 3 →₀ ℕ) : m ∈ (HP δ).support ↔ m 0 + m 1 + m 2 ≤ δ := by
  rw [mem_support_iff, coeff_HP]
  split_ifs with h <;> simp [h]

theorem coeff_HP_of_mem {δ : ℕ} {m : Fin 3 →₀ ℕ} (hm : m ∈ (HP δ).support) : coeff m (HP δ) = 1 := by
  rw [coeff_HP, if_pos ((mem_support_HP δ m).mp hm)]

theorem card_support_HP (δ : ℕ) : (HP δ).support.card = nmon δ := by
  have h1 : eval (fun _ => (1 : ℤ)) (HP δ) = (((HP δ).support.card : ℕ) : ℤ) := by
    rw [eval_eq']
    simp only [one_pow, prod_const_one, mul_one]
    rw [sum_congr rfl fun m hm => coeff_HP_of_mem hm]
    simp
  have h2 : eval (fun _ => (1 : ℤ)) (HP δ) = ((nmon δ : ℕ) : ℤ) := by
    unfold HP
    rw [map_h3, eval_X, eval_X, eval_X, nmon_eq]
    have := map_h3 (Nat.castRingHom ℤ) 1 1 1 δ
    simpa using this.symm
  exact_mod_cast h1.symm.trans h2

/-! ## The masked number of a column -/

theorem ev_monomial (P : Params) (m : Fin 3 →₀ ℕ) (c : ℤ) : ev P (monomial m c) = c * 2 ^ (P.W * pos P m) := by
  unfold ev
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), prod_kpt]

/-- The fibre of the layout over the slot of a monomial of a set of bounded degree is that monomial. -/
theorem fiber_sum {P : Params} (hL : LayoutInj P.D P.k1 P.k2) {S : Finset (Fin 3 →₀ ℕ)}
    (hS : ∀ m ∈ S, m 0 + m 1 + m 2 ≤ P.D) (g : (Fin 3 →₀ ℕ) → ℕ) {m₀ : Fin 3 →₀ ℕ} (hm₀ : m₀ ∈ S) :
    ∑ m ∈ S with pos P m = pos P m₀, g m = g m₀ := by
  classical
  refine sum_eq_single_of_mem m₀ (mem_filter.mpr ⟨hm₀, rfl⟩) fun b hb hne => ?_
  exact absurd (eq_of_pos_eq hL (hS b (mem_filter.mp hb).1) (hS m₀ hm₀) (mem_filter.mp hb).2) hne

theorem and_mod_of_lt (x A M : ℕ) (hA : A < 2 ^ M) : x &&& A = (x % 2 ^ M) &&& A := by
  have h1 : (x &&& A) % 2 ^ M = x % 2 ^ M &&& A % 2 ^ M := Nat.and_mod_two_pow
  rw [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_right hA)] at h1
  exact h1

/-- **The masked number is a polynomial.** For every number `x`, the bits of `x` in the mask of the
monomials of degree at most `δ`, minus the bias, are the value of a polynomial of degree at most `δ`
whose coefficients are at most `2 ^ (w0 - 1)` in absolute value. -/
theorem masked_exists (P : Params) (hL : LayoutInj P.D P.k1 P.k2) (hk1 : 1 ≤ P.k1) (hk : P.k1 ≤ P.k2)
    (hs : P.k2 * P.D < P.slots) (hw1 : 1 ≤ P.w0) (hw : P.w0 ≤ P.W) {δ : ℕ} (hδ : δ ≤ P.D) (x : ℕ) :
    ∃ ξ : Poly, Bd ξ (nmon δ * 2 ^ (P.w0 - 1)) δ ∧
      (((x &&& (mask P.w0 * monoN P δ) : ℕ) : ℤ) - ((2 ^ (P.w0 - 1) * monoN P δ : ℕ) : ℤ)) = ev P ξ := by
  classical
  set S := (HP δ).support with hS
  have hdeg : ∀ m ∈ S, m 0 + m 1 + m 2 ≤ P.D := fun m hm => ((mem_support_HP δ m).mp hm).trans hδ
  have hdegδ : ∀ m ∈ S, m 0 + m 1 + m 2 ≤ δ := fun m hm => (mem_support_HP δ m).mp hm
  have hpos : ∀ m ∈ S, pos P m < P.slots := fun m hm =>
    lt_of_le_of_lt ((pos_le P hk1 hk m).trans (Nat.mul_le_mul_left _ (hdeg m hm))) hs
  -- the number of the monomials as a packed vector with slots 0 and 1
  set κ : ℕ → ℕ := fun p => ∑ m ∈ S with pos P m = p, 1 with hκ
  have hmono : monoN P δ = packSum P.W P.slots κ := by
    have h1 : ((monoN P δ : ℕ) : ℤ) = ((∑ m ∈ S, 1 * 2 ^ (P.W * pos P m) : ℕ) : ℤ) := by
      rw [← ev_HP, ev_eq]
      push_cast
      exact sum_congr rfl fun m hm => by rw [coeff_HP_of_mem hm]
    rw [← sum_eq_packSum P S (fun _ => 1) hpos]
    exact_mod_cast h1
  have hκ1 : ∀ p, κ p ≤ 1 := fun p => by
    by_cases hne : (S.filter fun m => pos P m = p).Nonempty
    · obtain ⟨m₀, hm₀⟩ := hne
      have hp : p = pos P m₀ := (mem_filter.mp hm₀).2.symm
      rw [hκ, hp]
      simp only
      rw [fiber_sum hL hdeg (fun _ => 1) (mem_filter.mp hm₀).1]
    · rw [hκ]
      simp only
      rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]
      exact Nat.zero_le _
  have hm0 : mask P.w0 < 2 ^ P.W := by
    rw [mask_eq]
    exact lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos) (Nat.pow_le_pow_right (by norm_num) hw)
  have hall : mask P.w0 * monoN P δ = packSum P.W P.slots (fun p => mask P.w0 * κ p) := by
    rw [hmono, packSum_mul]
  have hallB : ∀ p, p < P.slots → mask P.w0 * κ p < 2 ^ P.W := fun p _ =>
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (hκ1 p)) (by rwa [mul_one])
  have hAlt : mask P.w0 * monoN P δ < 2 ^ (P.W * P.slots) := by
    rw [hall]; exact packSum_lt _ _ _ hallB
  -- the slots of the masked number
  set s : ℕ → ℕ := slot P.W (x % 2 ^ (P.W * P.slots)) with hs'
  have hx : x % 2 ^ (P.W * P.slots) = packSum P.W P.slots s :=
    (packSum_slot P.W P.slots _ (Nat.mod_lt _ (Nat.two_pow_pos _))).symm
  have he : x &&& (mask P.w0 * monoN P δ) = packSum P.W P.slots (fun p => s p &&& (mask P.w0 * κ p)) := by
    rw [and_mod_of_lt x _ _ hAlt, hall, hx]
    exact packSum_and P.W P.slots s _ (fun p _ => slot_lt _ _ _) hallB
  -- the polynomial of the masked slots
  set g : (Fin 3 →₀ ℕ) → ℕ := fun m => s (pos P m) &&& mask P.w0 with hg
  have he2 : x &&& (mask P.w0 * monoN P δ) = ∑ m ∈ S, g m * 2 ^ (P.W * pos P m) := by
    rw [he, sum_eq_packSum P S g hpos]
    refine packSum_congr _ _ fun p _ => ?_
    by_cases hne : (S.filter fun m => pos P m = p).Nonempty
    · obtain ⟨m₀, hm₀⟩ := hne
      have hp : p = pos P m₀ := (mem_filter.mp hm₀).2.symm
      have hk1' : κ p = 1 := by
        rw [hκ, hp]
        simp only
        rw [fiber_sum hL hdeg (fun _ => 1) (mem_filter.mp hm₀).1]
      rw [hk1', mul_one, hp, fiber_sum hL hdeg g (mem_filter.mp hm₀).1]
    · have hk0 : κ p = 0 := by
        rw [hκ]
        simp only
        rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]
      rw [hk0, mul_zero, Nat.and_zero, not_nonempty_iff_eq_empty.mp hne, sum_empty]
  refine ⟨∑ m ∈ S, C (((g m : ℕ) : ℤ) - ((2 ^ (P.w0 - 1) : ℕ) : ℤ)) * monomial m 1, ?_, ?_⟩
  · -- the bound
    have hterm : ∀ m ∈ S, Bd (C (((g m : ℕ) : ℤ) - ((2 ^ (P.w0 - 1) : ℕ) : ℤ)) * (monomial m (1 : ℤ) : Poly))
        (2 ^ (P.w0 - 1) * 1) δ := by
      intro m hm
      have hc : |((g m : ℕ) : ℤ) - ((2 ^ (P.w0 - 1) : ℕ) : ℤ)| ≤ ((2 ^ (P.w0 - 1) : ℕ) : ℤ) := by
        have h1 : g m < 2 ^ P.w0 := by
          rw [hg]
          simp only
          exact lt_of_le_of_lt Nat.and_le_right (by rw [mask_eq]; exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
        rw [two_pow_pred hw1] at h1
        have h2 : ((g m : ℕ) : ℤ) < 2 * ((2 ^ (P.w0 - 1) : ℕ) : ℤ) := by exact_mod_cast h1
        have h3 : (0 : ℤ) ≤ ((g m : ℕ) : ℤ) := Int.natCast_nonneg _
        rw [abs_le]
        constructor <;> linarith
      have hmon : Bd (monomial m (1 : ℤ) : Poly) 1 δ := by
        refine ⟨monomial m 1, fun m' => ?_, by unfold csum; rw [eval_monomial]; simp, ?_⟩
        · rw [coeff_monomial, coeff_monomial]
          split_ifs <;> simp
        · rw [totalDegree_monomial _ one_ne_zero, degree_eq]
          exact hdegδ m hm
      exact Bd.intC hc hmon
    have := Bd.sum_le S _ _ δ hterm
    rw [mul_one, hS, card_support_HP] at this
    exact this
  · -- the value
    rw [he2, map_sum]
    have hb : ((2 ^ (P.w0 - 1) * monoN P δ : ℕ) : ℤ) = ∑ m ∈ S, ((2 ^ (P.w0 - 1) : ℕ) : ℤ) * 2 ^ (P.W * pos P m) := by
      have h1 : ((monoN P δ : ℕ) : ℤ) = ∑ m ∈ S, (2 : ℤ) ^ (P.W * pos P m) := by
        rw [← ev_HP, ev_eq]
        exact sum_congr rfl fun m hm => by rw [coeff_HP_of_mem hm, one_mul]
      rw [Nat.cast_mul, h1, mul_sum]
    rw [hb]
    push_cast
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [map_mul, show ev P (C (((g m : ℕ) : ℤ) - (2 : ℤ) ^ (P.w0 - 1))) = ((g m : ℕ) : ℤ) - (2 : ℤ) ^ (P.w0 - 1) from eval_C _,
      ev_monomial]
    ring

end CAP.Wsos
