module

public import N11.Analytic.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases

/-!
# The theorem for 11 points, analytic part: alignment by an orthogonal map (row A6)

For two configurations `Y`, `P` of `ℝ³` let `alignF Y P U = ∑_a <P_a, U Y_a>` and
`alignS Y P U k l = ∑_a (U Y_a)_k P_{a l}`. The orthogonal group is compact (`isCompact_orth`), so `alignF Y P` has
a maximizer `U` on it. Then `alignF Y P (G U) = ∑_{k,m} G_km S_mk` with `S = alignS Y P U` for every matrix `G`.
Comparison with the rotations of the three coordinate planes shows that `S` is symmetric (`plane_zero`), and
comparison with the reflections `1 - 2 u uᵀ` that it is positive semidefinite (`exists_align`).

The symmetry of `S` is the condition of the gauge `∑_a P_a × U Y_a = 0`; the positivity is used in the
inequality of Procrustes type of `Procrustes.lean`.
-/

@[expose] public section

namespace N11.Analytic

open Finset Matrix

/-- The value of the alignment: `∑_a <P_a, U Y_a>`. -/
def alignF (Y P : Fin 11 → Fin 3 → ℝ) (U : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ a, ∑ k, P a k * U.mulVec (Y a) k

/-- The matrix `∑_a (U Y_a) P_aᵀ`. -/
def alignS (Y P : Fin 11 → Fin 3 → ℝ) (U : Matrix (Fin 3) (Fin 3) ℝ) (k l : Fin 3) : ℝ :=
  ∑ a, U.mulVec (Y a) k * P a l

theorem alignF_mul (Y P : Fin 11 → Fin 3 → ℝ) (G U : Matrix (Fin 3) (Fin 3) ℝ) :
    alignF Y P (G * U) = ∑ k, ∑ m, G k m * alignS Y P U m k := by
  unfold alignF alignS
  have e1 : ∀ a k, (G * U).mulVec (Y a) k = ∑ m, G k m * U.mulVec (Y a) m := by
    intro a k
    rw [← Matrix.mulVec_mulVec]
    rfl
  simp only [e1]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun k _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun m _ => sum_congr rfl fun a _ => ?_
  ring

theorem alignF_eq_trace (Y P : Fin 11 → Fin 3 → ℝ) (U : Matrix (Fin 3) (Fin 3) ℝ) :
    alignF Y P U = ∑ k, alignS Y P U k k := by
  have h := alignF_mul Y P 1 U
  rw [Matrix.one_mul] at h
  rw [h]
  refine sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (mem_univ k) h

/-! ## The orthogonal group is compact -/

theorem isCompact_orth : IsCompact {U : Matrix (Fin 3) (Fin 3) ℝ | U ∈ Matrix.orthogonalGroup (Fin 3) ℝ} := by
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin 3 => Set.pi Set.univ fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1
      : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hcl : IsClosed {U : Matrix (Fin 3) (Fin 3) ℝ | U ∈ Matrix.orthogonalGroup (Fin 3) ℝ} := by
    have e : {U : Matrix (Fin 3) (Fin 3) ℝ | U ∈ Matrix.orthogonalGroup (Fin 3) ℝ}
        = {U : Matrix (Fin 3) (Fin 3) ℝ | U * Uᵀ = 1} := by
      ext U
      exact Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ
    rw [e]
    exact isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_transpose) continuous_const
  refine IsCompact.of_isClosed_subset hbox hcl ?_
  intro U hU
  have h1 : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp hU
  refine Set.mem_univ_pi.mpr fun k => Set.mem_univ_pi.mpr fun m => ?_
  rw [Set.mem_Icc]
  have h2 : (U * Uᵀ) k k = 1 := by rw [h1, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at h2
  simp only [Matrix.transpose_apply] at h2
  have h3 : U k m ^ 2 ≤ 1 ^ 2 := by
    rw [one_pow, ← h2]
    have := single_le_sum (f := fun m => U k m * U k m) (fun m _ => mul_self_nonneg (U k m)) (mem_univ m)
    simpa [sq] using this
  exact abs_le.mp (abs_le_of_sq_le_sq h3 zero_le_one)

/-! ## Rotations and reflections -/

theorem plane_zero {A B : ℝ} (h : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → c * A + s * B ≤ A) : B = 0 := by
  by_contra hB
  have hpos : 0 < A ^ 2 + B ^ 2 := by positivity
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = Real.sqrt (A ^ 2 + B ^ 2) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; exact Real.sqrt_pos.mpr hpos
  have hρ2 : ρ ^ 2 = A ^ 2 + B ^ 2 := by rw [hρ]; exact Real.sq_sqrt hpos.le
  have h1 := h (A / ρ) (B / ρ) (by field_simp; linarith)
  have e : A / ρ * A + B / ρ * B = ρ := by
    field_simp
    linarith
  rw [e] at h1
  have hB2 : 0 < B ^ 2 := by positivity
  nlinarith

/-- The rotation of the coordinate plane `(0, 1)`. -/
def rot01 (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![c, -s, 0; s, c, 0; 0, 0, 1]

/-- The rotation of the coordinate plane `(0, 2)`. -/
def rot02 (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![c, 0, -s; 0, 1, 0; s, 0, c]

/-- The rotation of the coordinate plane `(1, 2)`. -/
def rot12 (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, c, -s; 0, s, c]

theorem rot01_mem {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : rot01 c s ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot01, Matrix.mul_apply, Fin.sum_univ_three] <;> first | linear_combination h | ring

theorem rot02_mem {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : rot02 c s ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot02, Matrix.mul_apply, Fin.sum_univ_three] <;> first | linear_combination h | ring

theorem rot12_mem {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : rot12 c s ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot12, Matrix.mul_apply, Fin.sum_univ_three] <;> first | linear_combination h | ring

/-- The reflection `1 - 2 u uᵀ`. -/
def refl (u : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun k m => (if k = m then 1 else 0) - 2 * u k * u m

theorem sum3 (f : Fin 3 → ℝ) : ∑ k, f k = f 0 + f 1 + f 2 := Fin.sum_univ_three f

theorem refl_mem {u : Fin 3 → ℝ} (h : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1) :
    refl u ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  have key : ∀ i j : Fin 3, (refl u * (refl u)ᵀ) i j
      = (if i = j then 1 else 0) + 4 * u i * u j * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 - 1) := by
    intro i j
    rw [Matrix.mul_apply, sum3]
    simp only [refl, Matrix.of_apply, Matrix.transpose_apply]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  ext i j
  rw [key, h, sub_self, mul_zero, add_zero, Matrix.one_apply]

/-- **Alignment.** There is an orthogonal map `U` for which `S = ∑_a (U Y_a) P_aᵀ` is symmetric and positive
semidefinite. -/
theorem exists_align (Y P : Fin 11 → Fin 3 → ℝ) :
    ∃ U ∈ Matrix.orthogonalGroup (Fin 3) ℝ,
      (∀ k l : Fin 3, alignS Y P U k l = alignS Y P U l k) ∧
      (∀ u : Fin 3 → ℝ, 0 ≤ ∑ k, ∑ l, u k * u l * alignS Y P U k l) := by
  have hcont : ContinuousOn (alignF Y P) {U : Matrix (Fin 3) (Fin 3) ℝ | U ∈ Matrix.orthogonalGroup (Fin 3) ℝ} := by
    refine Continuous.continuousOn ?_
    unfold alignF
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun k _ => continuous_const.mul ?_
    exact (continuous_apply k).comp (continuous_id.matrix_mulVec continuous_const)
  obtain ⟨U, hU, hmax⟩ := isCompact_orth.exists_isMaxOn ⟨1, Submonoid.one_mem (Matrix.orthogonalGroup (Fin 3) ℝ)⟩ hcont
  have hmax' := isMaxOn_iff.mp hmax
  set S := alignS Y P U with hS
  have hle : ∀ G : Matrix (Fin 3) (Fin 3) ℝ, G ∈ Matrix.orthogonalGroup (Fin 3) ℝ →
      ∑ k, ∑ m, G k m * S m k ≤ ∑ k, S k k := by
    intro G hG
    have h := hmax' (G * U) (Submonoid.mul_mem _ hG hU)
    rw [alignF_mul, alignF_eq_trace] at h
    exact h
  refine ⟨U, hU, ?_, ?_⟩
  · -- symmetry, from the three rotations
    have h01 : S 0 1 = S 1 0 := by
      have := plane_zero (A := S 0 0 + S 1 1) (B := S 0 1 - S 1 0) fun c s hcs => by
        have h := hle (rot01 c s) (rot01_mem hcs)
        simp [rot01, sum3] at h
        linarith
      linarith
    have h02 : S 0 2 = S 2 0 := by
      have := plane_zero (A := S 0 0 + S 2 2) (B := S 0 2 - S 2 0) fun c s hcs => by
        have h := hle (rot02 c s) (rot02_mem hcs)
        simp [rot02, sum3] at h
        linarith
      linarith
    have h12 : S 1 2 = S 2 1 := by
      have := plane_zero (A := S 1 1 + S 2 2) (B := S 1 2 - S 2 1) fun c s hcs => by
        have h := hle (rot12 c s) (rot12_mem hcs)
        simp [rot12, sum3] at h
        linarith
      linarith
    intro k l
    show S k l = S l k
    fin_cases k <;> fin_cases l
    · rfl
    · exact h01
    · exact h02
    · exact h01.symm
    · rfl
    · exact h12
    · exact h02.symm
    · exact h12.symm
    · rfl
  · -- positivity, from the reflections
    have hunit : ∀ u : Fin 3 → ℝ, u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 → 0 ≤ ∑ k, ∑ l, u k * u l * S k l := by
      intro u hu
      have h := hle (refl u) (refl_mem hu)
      have e : ∑ k, ∑ m, refl u k m * S m k = ∑ k, S k k - 2 * ∑ k, ∑ l, u k * u l * S l k := by
        simp only [refl, Matrix.of_apply, sum3]
        simp
        ring
      rw [e] at h
      have e2 : ∑ k, ∑ l, u k * u l * S l k = ∑ k, ∑ l, u k * u l * S k l := by
        rw [Finset.sum_comm]
        exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
      linarith
    intro u
    by_cases hu : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 0
    · have hu0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
      have hu1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
      have hu2 : u 2 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]
      simp [sum3, hu0, hu1, hu2]
    · have hpos : 0 < u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hu)
      obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) := ⟨_, rfl⟩
      have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.mpr hpos
      have hr2 : r ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by rw [hr]; exact Real.sq_sqrt hpos.le
      have h1 := hunit (fun k => u k / r) (by field_simp; linarith)
      have e : ∑ k, ∑ l, u k / r * (u l / r) * S k l = 1 / r ^ 2 * ∑ k, ∑ l, u k * u l * S k l := by
        rw [Finset.mul_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine sum_congr rfl fun l _ => ?_
        field_simp
      rw [e] at h1
      exact nonneg_of_mul_nonneg_right h1 (by positivity)

end N11.Analytic
