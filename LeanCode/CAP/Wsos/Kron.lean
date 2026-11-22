module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import CAP.Wsos.Rep

/-!
# A polynomial is determined by its number

`kron_zero`: let the map `x ^ a * y ^ b * z ^ c ↦ a + k1 * b + k2 * c` be injective on the
monomials of total degree at most `D`, with values below `slots`. A polynomial of total degree at
most `D` whose coefficients are dominated by a polynomial with a sum of coefficients below
`2 ^ (W - 1)`, and whose number vanishes modulo `2 ^ (W * slots)`, is zero.

The proof writes the polynomial as the difference of two polynomials with natural coefficients.
Their numbers are packed vectors with slots below `2 ^ W` (`packSum`), they agree modulo
`2 ^ (W * slots)` and are below this modulus, hence they are equal, and so are their slots.
-/

@[expose] public section

namespace CAP.Wsos

open MvPolynomial Finset

/-- The slot of a monomial. -/
def pos (P : Params) (m : Fin 3 →₀ ℕ) : ℕ := m 0 + P.k1 * m 1 + P.k2 * m 2

/-- The map from the monomials of total degree at most `D` to the slots is injective. -/
def LayoutInj (D k1 k2 : ℕ) : Prop :=
  ∀ a b c a' b' c' : ℕ, a + b + c ≤ D → a' + b' + c' ≤ D →
    a + k1 * b + k2 * c = a' + k1 * b' + k2 * c' → a = a' ∧ b = b' ∧ c = c'

theorem prod_kpt (P : Params) (m : Fin 3 →₀ ℕ) : ∏ i, kpt P i ^ m i = (2 : ℤ) ^ (P.W * pos P m) := by
  rw [Fin.prod_univ_three]
  show ((2 : ℤ) ^ P.W) ^ m 0 * (2 ^ (P.W * P.k1)) ^ m 1 * (2 ^ (P.W * P.k2)) ^ m 2 = _
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  unfold pos
  ring

theorem ev_eq (P : Params) (F : Poly) : ev P F = ∑ m ∈ F.support, coeff m F * 2 ^ (P.W * pos P m) := by
  unfold ev
  rw [eval_eq']
  exact sum_congr rfl fun m _ => by rw [prod_kpt]

theorem degree_eq (m : Fin 3 →₀ ℕ) : (m.sum fun _ e => e) = m 0 + m 1 + m 2 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_three]

theorem degree_le {F : Poly} {D : ℕ} (hF : F.totalDegree ≤ D) {m : Fin 3 →₀ ℕ} (hm : m ∈ F.support) :
    m 0 + m 1 + m 2 ≤ D := by
  rw [← degree_eq]
  exact (le_totalDegree hm).trans hF

theorem pos_le (P : Params) (hk1 : 1 ≤ P.k1) (hk : P.k1 ≤ P.k2) (m : Fin 3 →₀ ℕ) :
    pos P m ≤ P.k2 * (m 0 + m 1 + m 2) := by
  unfold pos
  have h0 : m 0 ≤ P.k2 * m 0 := Nat.le_mul_of_pos_left _ (by omega)
  have h1 : P.k1 * m 1 ≤ P.k2 * m 1 := Nat.mul_le_mul_right _ hk
  rw [Nat.mul_add, Nat.mul_add]
  omega

theorem eq_of_pos_eq {P : Params} (hL : LayoutInj P.D P.k1 P.k2) {m m' : Fin 3 →₀ ℕ}
    (hm : m 0 + m 1 + m 2 ≤ P.D) (hm' : m' 0 + m' 1 + m' 2 ≤ P.D) (h : pos P m = pos P m') : m = m' := by
  obtain ⟨h0, h1, h2⟩ := hL _ _ _ _ _ _ hm hm' h
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The number of a polynomial with natural coefficients, supported in a set on which the layout
is injective, as a packed vector. -/
theorem sum_eq_packSum (P : Params) (S : Finset (Fin 3 →₀ ℕ)) (g : (Fin 3 →₀ ℕ) → ℕ)
    (hS : ∀ m ∈ S, pos P m < P.slots) :
    ∑ m ∈ S, g m * 2 ^ (P.W * pos P m) = packSum P.W P.slots (fun p => ∑ m ∈ S with pos P m = p, g m) := by
  unfold packSum
  rw [← sum_fiberwise_of_maps_to (g := pos P) (t := range P.slots) (fun m hm => mem_range.mpr (hS m hm))]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun m hm => ?_
  rw [(mem_filter.mp hm).2]

theorem toNat_le_abs (c : ℤ) : (c.toNat : ℤ) ≤ |c| := by
  rcases le_total 0 c with h | h
  · rw [Int.toNat_of_nonneg h, abs_of_nonneg h]
  · rw [Int.toNat_of_nonpos h]; simpa using abs_nonneg c

/-- **A polynomial is determined by its number.** -/
theorem kron_zero (P : Params) (hL : LayoutInj P.D P.k1 P.k2) (hk1 : 1 ≤ P.k1) (hk : P.k1 ≤ P.k2)
    (hs : P.k2 * P.D < P.slots) (hW1 : 1 ≤ P.W) {F : Poly} {B : ℕ} (hB : Bd F B P.D)
    (hW : B < 2 ^ (P.W - 1)) (h0 : ev P F ≡ 0 [ZMOD (2 : ℤ) ^ Mb P]) : F = 0 := by
  classical
  have hdeg : ∀ m ∈ F.support, m 0 + m 1 + m 2 ≤ P.D := fun m hm => degree_le hB.totalDegree_le hm
  have hpos : ∀ m ∈ F.support, pos P m < P.slots := fun m hm =>
    lt_of_le_of_lt ((pos_le P hk1 hk m).trans (Nat.mul_le_mul_left _ (hdeg m hm))) hs
  have hB2 : B < 2 ^ P.W := lt_of_lt_of_le hW (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
  set cp : (Fin 3 →₀ ℕ) → ℕ := fun m => (coeff m F).toNat with hcp
  set cn : (Fin 3 →₀ ℕ) → ℕ := fun m => (-coeff m F).toNat with hcn
  have hc : ∀ m, coeff m F = (cp m : ℤ) - cn m := fun m => (Int.toNat_sub_toNat_neg _).symm
  have hcpB : ∀ m, cp m ≤ B := fun m => by
    have h1 := hB.coeff_le m
    exact_mod_cast (toNat_le_abs (coeff m F)).trans h1
  have hcnB : ∀ m, cn m ≤ B := fun m => by
    have h1 := hB.coeff_le m
    have h2 := toNat_le_abs (-coeff m F)
    rw [abs_neg] at h2
    exact_mod_cast h2.trans h1
  -- a fibre of the layout has at most one element
  have hfib : ∀ (g : (Fin 3 →₀ ℕ) → ℕ), ∀ m₀ ∈ F.support,
      ∑ m ∈ F.support with pos P m = pos P m₀, g m = g m₀ := by
    intro g m₀ hm₀
    refine sum_eq_single_of_mem m₀ (mem_filter.mpr ⟨hm₀, rfl⟩) fun b hb hne => ?_
    exact absurd (eq_of_pos_eq hL (hdeg b (mem_filter.mp hb).1) (hdeg m₀ hm₀) (mem_filter.mp hb).2) hne
  have hfibB : ∀ (g : (Fin 3 →₀ ℕ) → ℕ), (∀ m, g m ≤ B) → ∀ p,
      ∑ m ∈ F.support with pos P m = p, g m < 2 ^ P.W := by
    intro g hg p
    by_cases hne : (F.support.filter fun m => pos P m = p).Nonempty
    · obtain ⟨m₀, hm₀⟩ := hne
      have hp : p = pos P m₀ := (mem_filter.mp hm₀).2.symm
      rw [hp, hfib g m₀ (mem_filter.mp hm₀).1]
      exact lt_of_le_of_lt (hg m₀) hB2
    · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]
      exact Nat.two_pow_pos _
  set fp : ℕ → ℕ := fun p => ∑ m ∈ F.support with pos P m = p, cp m with hfp
  set fn : ℕ → ℕ := fun p => ∑ m ∈ F.support with pos P m = p, cn m with hfn
  have hev : ev P F = (packSum P.W P.slots fp : ℤ) - packSum P.W P.slots fn := by
    rw [ev_eq, ← sum_eq_packSum P F.support cp hpos, ← sum_eq_packSum P F.support cn hpos]
    push_cast
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun m _ => by rw [hc m]; ring
  have hlt1 : packSum P.W P.slots fp < 2 ^ (P.W * P.slots) :=
    packSum_lt P.W P.slots fp fun j _ => hfibB cp hcpB j
  have hlt2 : packSum P.W P.slots fn < 2 ^ (P.W * P.slots) :=
    packSum_lt P.W P.slots fn fun j _ => hfibB cn hcnB j
  have heq : packSum P.W P.slots fp = packSum P.W P.slots fn := by
    have h1 : (packSum P.W P.slots fp : ℤ) ≡ packSum P.W P.slots fn [ZMOD (2 : ℤ) ^ Mb P] := by
      have := h0
      rw [hev] at this
      exact Int.modEq_iff_dvd.mpr (by
        have h2 := Int.modEq_zero_iff_dvd.mp this
        have h3 : (packSum P.W P.slots fn : ℤ) - packSum P.W P.slots fp
            = -((packSum P.W P.slots fp : ℤ) - packSum P.W P.slots fn) := by ring
        rw [h3]; exact (dvd_neg).mpr h2)
    have h2 : packSum P.W P.slots fp ≡ packSum P.W P.slots fn [MOD 2 ^ Mb P] := by
      rw [← Int.natCast_modEq_iff]; exact_mod_cast h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 hlt1 hlt2
  have hslots := packSum_injective P.W P.slots fp fn (fun j _ => hfibB cp hcpB j)
    (fun j _ => hfibB cn hcnB j) heq
  rw [← support_eq_empty]
  by_contra hne
  obtain ⟨m, hm⟩ := nonempty_iff_ne_empty.mpr hne
  have h1 := hslots (pos P m) (hpos m hm)
  rw [hfp, hfn] at h1
  simp only at h1
  rw [hfib cp m hm, hfib cn m hm] at h1
  have h2 := hc m
  rw [h1, sub_self] at h2
  exact (mem_support_iff.mp hm) h2

end CAP.Wsos
