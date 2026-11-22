module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.List
public import CAP.Wsos.Squares

/-!
# The sum over the weights

`weightsGo_exists`: the number that the checker forms for the weights of a triple type stands for a
polynomial `WP` with bounded coefficients, and every homomorphism to the real numbers under which
the generators are nonnegative maps `WP` to a nonnegative number: `WP` is a sum of products of
generators with sums of squares.
-/

@[expose] public section

namespace CAP.Wsos

open Finset MvPolynomial

variable {P : Params} {pM mM : ℕ}

theorem Rep.of_eq {n : ℕ} {F : Poly} (h : ((n : ℕ) : ℤ) = ev P F) : Rep P n F := by
  unfold Rep
  rw [h]

theorem sqAbs_cast (a b : ℕ) : ((sqAbs a b : ℕ) : ℤ) = ((a : ℤ) - b) ^ 2 := by
  show (((a - b + (b - a)) * (a - b + (b - a)) : ℕ) : ℤ) = _
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add]
    push_cast [Nat.cast_sub h]
    ring
  · rw [Nat.sub_eq_zero_of_le h, add_zero]
    push_cast [Nat.cast_sub h]
    ring

theorem sqSum_succ (allowed beta : ℕ) (col : ℕ → ℕ) (r : ℕ) :
    sqSum allowed beta col (r + 1) = sqSum allowed beta col r + sqAbs (col r &&& allowed) beta := rfl

/-- The sum of the squares of a weight is the value of a sum of squares of polynomials. -/
theorem sqSum_exists (P : Params) (hL : LayoutInj P.D P.k1 P.k2) (hk1 : 1 ≤ P.k1) (hk : P.k1 ≤ P.k2)
    (hs : P.k2 * P.D < P.slots) (hw1 : 1 ≤ P.w0) (hw : P.w0 ≤ P.W) {δ : ℕ} (hδ : δ ≤ P.D) (col : ℕ → ℕ) :
    ∀ r : ℕ, ∃ Sq : Poly,
      Bd Sq (r * ((nmon δ * 2 ^ (P.w0 - 1)) * (nmon δ * 2 ^ (P.w0 - 1)))) (δ + δ) ∧
      ((sqSum (mask P.w0 * monoN P δ) (2 ^ (P.w0 - 1) * monoN P δ) col r : ℕ) : ℤ) = ev P Sq ∧
      ∀ ρ : Poly →+* ℝ, 0 ≤ ρ Sq
  | 0 => ⟨0, by simpa using Bd.zero.mono (Nat.zero_le _) (Nat.zero_le _), by simp [sqSum], fun ρ => by simp⟩
  | r + 1 => by
    obtain ⟨Sq, hB, hev, hnn⟩ := sqSum_exists P hL hk1 hk hs hw1 hw hδ col r
    obtain ⟨ξ, hξB, hξ⟩ := masked_exists P hL hk1 hk hs hw1 hw hδ (col r)
    refine ⟨Sq + ξ ^ 2, ?_, ?_, fun ρ => ?_⟩
    · have := hB.add ((hξB.mul hξB).congr (by ring : ξ * ξ = ξ ^ 2))
      refine this.mono (le_of_eq ?_) le_rfl
      ring
    · rw [sqSum_succ, Nat.cast_add, hev, sqAbs_cast, map_add, map_pow, ← hξ]
    · rw [map_add, map_pow]
      exact add_nonneg (hnn ρ) (sq_nonneg _)

theorem weightOk_iff (P : Params) (w : Weight) :
    weightOk P w = true ↔ gensOk w.gens = true ∧ degSum w.gens + 2 * w.delta ≤ P.D := by
  unfold weightOk
  rw [Bool.and_eq_true, Nat.ble_eq]
  rfl

theorem gensV_nonneg {U V T : Poly} (ρ : Poly →+* ℝ) : ∀ (gens : List Gen),
    (∀ g ∈ gens, 0 ≤ ρ (genV (EP P) U V T g)) → 0 ≤ ρ (gensV (EP P) U V T gens)
  | [], _ => by simp [gensV]
  | g :: gens, h => by
    unfold gensV
    rw [List.map_cons, List.prod_cons, map_mul]
    exact mul_nonneg (h g (by simp)) (gensV_nonneg ρ gens fun g' hg' => h g' (by simp [hg']))

/-- The term of a weight. -/
theorem weightVal_exists (hM : Mod P pM mM) (hL : LayoutInj P.D P.k1 P.k2) (hk1 : 1 ≤ P.k1) (hk : P.k1 ≤ P.k2)
    (hs : P.k2 * P.D < P.slots) (hw1 : 1 ≤ P.w0) (hw : P.w0 ≤ P.W) (hD : P.D = 2 * P.d)
    {u v t : ℕ} {U V T : Poly} (hu : Rep P u U) (hv : Rep P v V) (ht : Rep P t T)
    (bu : Bd U (2 ^ P.m) 1) (bv : Bd V (2 ^ P.m) 1) (bt : Bd T (2 ^ P.m) 1) (w : Weight) (hok : weightOk P w = true) :
    ∃ WP : Poly,
      Rep P (weightVal P pM mM u v t
        (nth (monoGo P.W (Nat.mul P.W P.k1) (Nat.mul P.W P.k2) (Nat.succ P.d) 1 1 1) w.delta) w) WP ∧
      Bd WP (w.mul * nGens P w.gens * w.r * ((nmon w.delta * nmon w.delta) <<< (2 * P.w0 - 2))) P.D ∧
      ∀ ρ : Poly →+* ℝ, (∀ g ∈ w.gens, 0 ≤ ρ (genV (EP P) U V T g)) → 0 ≤ ρ WP := by
  obtain ⟨hgens, hdeg⟩ := (weightOk_iff P w).mp hok
  have hδd : w.delta < P.d + 1 := by omega
  have hδD : w.delta ≤ P.D := by omega
  obtain ⟨Sq, hB, hev, hnn⟩ := sqSum_exists P hL hk1 hk hs hw1 hw hδD w.col w.r
  refine ⟨C ((w.mul : ℕ) : ℤ) * (gensV (EP P) U V T w.gens * Sq), ?_, ?_, fun ρ hg => ?_⟩
  · unfold weightVal
    rw [nth_monos P hδd]
    have hsq : Rep P (sqSum (Nat.mul (mask P.w0) (monoN P w.delta)) (Nat.shiftLeft (monoN P w.delta) (Nat.pred P.w0))
        w.col w.r) Sq := by
      have e : Nat.shiftLeft (monoN P w.delta) (Nat.pred P.w0) = 2 ^ (P.w0 - 1) * monoN P w.delta := by
        show (monoN P w.delta) <<< (P.w0 - 1) = _
        rw [Nat.shiftLeft_eq, mul_comm]
      rw [e]
      exact Rep.of_eq hev
    have hg := gensGo_rep hM hu hv ht w.gens 1 1 Rep.one
    rw [one_mul] at hg
    exact Rep.smul _ (hg.mulM hM hsq)
  · have := Bd.smul w.mul ((gensV_bd bu bv bt w.gens hgens).mul hB)
    refine this.mono (le_of_eq ?_) (by omega)
    rw [Nat.shiftLeft_eq]
    have e : (2 : ℕ) ^ (2 * P.w0 - 2) = 2 ^ (P.w0 - 1) * 2 ^ (P.w0 - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e]
    ring
  · rw [map_mul, map_mul, C_natCast', map_natCast]
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (gensV_nonneg ρ w.gens hg) (hnn ρ))

theorem weightsGo_cons (u v t : ℕ) (monos : List ℕ) (w : Weight) (ws : List Weight) (acc : ℕ) :
    weightsGo P pM mM u v t monos (w :: ws) acc
      = weightsGo P pM mM u v t monos ws (Nat.add acc (weightVal P pM mM u v t (nth monos w.delta) w)) := rfl

theorem nWeightsGo_cons (w : Weight) (ws : List Weight) (acc : ℕ) :
    nWeightsGo P (w :: ws) acc = nWeightsGo P ws (Nat.add acc (Nat.mul (Nat.mul (Nat.mul w.mul (nGens P w.gens)) w.r)
      (Nat.shiftLeft (Nat.mul (nmon w.delta) (nmon w.delta)) (Nat.sub (Nat.mul 2 P.w0) 2)))) := rfl

theorem nWeightsGo_acc : ∀ (ws : List Weight) (acc : ℕ), nWeightsGo P ws acc = acc + nWeightsGo P ws 0
  | [], acc => rfl
  | w :: ws, acc => by
    rw [nWeightsGo_cons, nWeightsGo_cons, nWeightsGo_acc ws, nWeightsGo_acc ws (Nat.add 0 _)]
    show acc + _ + _ = acc + (0 + _ + _)
    ring

theorem weightsOk_cons (w : Weight) (ws : List Weight) :
    weightsOk P (w :: ws) = (weightOk P w && weightsOk P ws) := rfl

/-- **The sum over the weights.** -/
theorem weightsGo_exists (hM : Mod P pM mM) (hL : LayoutInj P.D P.k1 P.k2) (hk1 : 1 ≤ P.k1) (hk : P.k1 ≤ P.k2)
    (hs : P.k2 * P.D < P.slots) (hw1 : 1 ≤ P.w0) (hw : P.w0 ≤ P.W) (hD : P.D = 2 * P.d)
    {u v t : ℕ} {U V T : Poly} (hu : Rep P u U) (hv : Rep P v V) (ht : Rep P t T)
    (bu : Bd U (2 ^ P.m) 1) (bv : Bd V (2 ^ P.m) 1) (bt : Bd T (2 ^ P.m) 1) :
    ∀ (ws : List Weight), weightsOk P ws = true →
      ∃ WP : Poly,
        (∀ (acc : ℕ) (AF : Poly), Rep P acc AF →
          Rep P (weightsGo P pM mM u v t (monoGo P.W (Nat.mul P.W P.k1) (Nat.mul P.W P.k2) (Nat.succ P.d) 1 1 1) ws acc)
            (AF + WP)) ∧
        Bd WP (nWeightsGo P ws 0) P.D ∧
        ∀ ρ : Poly →+* ℝ, (∀ w ∈ ws, ∀ g ∈ w.gens, 0 ≤ ρ (genV (EP P) U V T g)) → 0 ≤ ρ WP
  | [], _ => ⟨0, fun acc AF h => by simpa [weightsGo] using h,
      by simpa [nWeightsGo] using Bd.zero.mono (Nat.zero_le _) (Nat.zero_le P.D), fun ρ _ => by simp⟩
  | w :: ws, hok => by
    rw [weightsOk_cons, Bool.and_eq_true] at hok
    obtain ⟨W1, hr1, hb1, hn1⟩ := weightVal_exists hM hL hk1 hk hs hw1 hw hD hu hv ht bu bv bt w hok.1
    obtain ⟨W2, hr2, hb2, hn2⟩ := weightsGo_exists hM hL hk1 hk hs hw1 hw hD hu hv ht bu bv bt ws hok.2
    refine ⟨W1 + W2, fun acc AF h => ?_, ?_, fun ρ hg => ?_⟩
    · rw [weightsGo_cons]
      exact (hr2 _ _ (h.add hr1)).congr (by ring)
    · rw [nWeightsGo_cons, nWeightsGo_acc]
      refine (hb1.add hb2).mono (le_of_eq ?_) le_rfl
      show w.mul * nGens P w.gens * w.r * ((nmon w.delta * nmon w.delta) <<< (2 * P.w0 - 2)) + nWeightsGo P ws 0
        = 0 + w.mul * nGens P w.gens * w.r * ((nmon w.delta * nmon w.delta) <<< (2 * P.w0 - 2)) + nWeightsGo P ws 0
      rw [zero_add]
    · rw [map_add]
      exact add_nonneg (hn1 ρ fun g hg' => hg w (by simp) g hg')
        (hn2 ρ fun w' hw' g hg' => hg w' (by simp [hw']) g hg')

end CAP.Wsos
