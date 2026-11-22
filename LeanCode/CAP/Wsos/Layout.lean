module

public import CAP.Wsos.Kron

/-!
# The layouts in use

The map `x ^ a * y ^ b * z ^ c ↦ a + k1 * b + k2 * c` is injective on the monomials of total degree
at most `D` for `(D, k1, k2) = (8, 37, 45), (10, 56, 66), (12, 79, 91), (16, 137, 153)`: the layouts that
`certgen/s3n9_box.py` chooses (the pair with the smallest `k2`).

For given `(b, c) ≠ (b', c')` the equation `a + k1 * b + k2 * c = a' + k1 * b' + k2 * c'` fixes
`a - a'`. The Boolean function `layoutOk` tests, for all `b, c, b', c'`, that this difference is too
large for `a ≤ D - b - c` and `a' ≤ D - b' - c'`; the kernel evaluates it for the three layouts.
-/

@[expose] public section

namespace CAP.Wsos

/-- The exponents `(b, c)` and `(b', c')` of `y` and `z` cannot occur in two monomials with the same slot. -/
def LayoutCase (D k1 k2 b c b' c' : ℕ) : Prop :=
  b + c ≤ D → b' + c' ≤ D → (b ≠ b' ∨ c ≠ c') →
    (k1 * b + k2 * c ≤ k1 * b' + k2 * c' → D - (b + c) < k1 * b' + k2 * c' - (k1 * b + k2 * c)) ∧
    (k1 * b' + k2 * c' < k1 * b + k2 * c → D - (b' + c') < k1 * b + k2 * c - (k1 * b' + k2 * c'))

instance (D k1 k2 b c b' c' : ℕ) : Decidable (LayoutCase D k1 k2 b c b' c') := by
  unfold LayoutCase
  infer_instance

/-- The test of a layout. -/
def layoutOk (D k1 k2 : ℕ) : Bool :=
  (List.range (D + 1)).all fun b => (List.range (D + 1)).all fun c => (List.range (D + 1)).all fun b' =>
    (List.range (D + 1)).all fun c' => decide (LayoutCase D k1 k2 b c b' c')

theorem layoutInj_of_ok {D k1 k2 : ℕ} (h : layoutOk D k1 k2 = true) : LayoutInj D k1 k2 := by
  intro a b c a' b' c' h1 h2 he
  have hall : LayoutCase D k1 k2 b c b' c' := by
    unfold layoutOk at h
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h b (by omega) c (by omega) b' (by omega) c' (by omega)
  unfold LayoutCase at hall
  by_cases hbc : b = b' ∧ c = c'
  · obtain ⟨rfl, rfl⟩ := hbc
    exact ⟨by omega, rfl, rfl⟩
  · have := hall (by omega) (by omega) (by omega)
    omega

set_option maxRecDepth 1000000 in
theorem layoutInj_8 : LayoutInj 8 37 45 := layoutInj_of_ok (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem layoutInj_10 : LayoutInj 10 56 66 := layoutInj_of_ok (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem layoutInj_12 : LayoutInj 12 79 91 := layoutInj_of_ok (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem layoutInj_16 : LayoutInj 16 137 153 := layoutInj_of_ok (by decide +kernel)

end CAP.Wsos
