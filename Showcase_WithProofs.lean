import Mathlib
import Certificates.Theorem.T6A

/-!
# The Thomson problem for 11 points

The Thomson problem asks for the configurations of `N` points on the unit sphere of `ℝ³` that
minimize the Coulomb energy, the sum of the reciprocal distances over all pairs of points.
This file states its solution for `N = 11`: a minimizer exists, it is unique up to orthogonal
transformations and relabelling of the points, and its coordinates are given up to `10⁻¹⁰`.

All definitions needed to read the statement are included here.
This companion supplies the complete proof of the statement in `Showcase.lean`.
-/

noncomputable section

namespace Thomson11

/-! ## Configurations and Coulomb energy -/

/-- Three-dimensional Euclidean space. -/
abbrev Point := EuclideanSpace ℝ (Fin 3)

/-- Eleven distinct points on the unit sphere. -/
def IsConfiguration (Y : Fin 11 → Point) : Prop :=
  (∀ i, ‖Y i‖ = 1) ∧ Function.Injective Y

/-- The Coulomb energy, summed over the 55 unordered pairs of points.
(For two equal points Lean evaluates `1 / 0` to `0`; the theorem below concerns configurations
of distinct points only.) -/
def E (Y : Fin 11 → Point) : ℝ :=
  ∑ i : Fin 11, ∑ j : Fin 11 with i < j, 1 / ‖Y i - Y j‖

/-- `Y` arises from `Z` by an orthogonal transformation and a permutation of the labels.
Here `Point ≃ₗᵢ[ℝ] Point` is the type of the linear isometries of `ℝ³` onto itself, that is, of
the orthogonal transformations, and `Equiv.Perm (Fin 11)` is the type of the permutations of the
labels `0, …, 10`. -/
def Congruent (Y Z : Fin 11 → Point) : Prop :=
  ∃ (U : Point ≃ₗᵢ[ℝ] Point) (σ : Equiv.Perm (Fin 11)),
    ∀ i, Y i = U (Z (σ i))

/-- `Z` is a configuration that attains the global minimum of the energy, and equality occurs
exactly at its congruent copies. -/
def IsUniqueMinimizer (Z : Fin 11 → Point) : Prop :=
  IsConfiguration Z ∧ ∀ Y, IsConfiguration Y →
    E Z ≤ E Y ∧ (E Y = E Z ↔ Congruent Y Z)

/-! ## The coordinates of the minimizer -/

/-- Eleven points with explicit decimal coordinates, which approximate the minimizer. The
coordinates are exact rational numbers, not floating-point numbers.
Here `!₂[x, y, z]` is the Euclidean vector with coordinates `(x, y, z)`, and `![x₀, …, x₁₀]` is the
family with the entries `x₀, …, x₁₀`. -/
def X₀ : Fin 11 → Point :=
  ![!₂[ 0.313620689025589,  0.319317483958265,  0.894247397454238],
    !₂[ 0.122131934022939, -0.879707882375786,  0.459562653375714],
    !₂[ 0.836384234608648,  0.540732019932700,  0.089834819071496],
    !₂[-0.829513636587083, -0.542301295299786, -0.133478207330809],
    !₂[-0.566960498580477,  0.239819275605855, -0.788062502659060],
    !₂[ 0.061432238616290, -0.754530255111397, -0.653383634766071],
    !₂[-0.016529763516812,  0.987228274258469, -0.158452205483935],
    !₂[ 0.892049358244038, -0.450479658797258,  0.036276982596482],
    !₂[ 0.482848954144595,  0.189339586942292, -0.854989712393075],
    !₂[-0.513162273240149, -0.211638860342633,  0.831789320751279],
    !₂[-0.786447187737911,  0.558000050679941,  0.264833465295296]]

/-! ## The main theorem -/

/-! ## Translation to the coordinates of the proof

The proof in `LeanCode` describes a configuration by its coordinates `Fin 11 → Fin 3 → ℝ` and an
orthogonal transformation by its matrix. The lemmas of this section translate its statements to
the definitions above. -/

/-- The coordinates of a configuration. -/
private def coords (Y : Fin 11 → Point) : Fin 11 → Fin 3 → ℝ := N11.Analytic.ofE Y

private theorem toE_coords (Y : Fin 11 → Point) : N11.Analytic.toE (coords Y) = Y :=
  N11.Analytic.toE_ofE Y

private theorem isConfiguration_toE {x : Fin 11 → Fin 3 → ℝ} (hs : N11.OnSphere x)
    (hi : Function.Injective x) : IsConfiguration (N11.Analytic.toE x) :=
  ⟨N11.Analytic.norm_toE x hs, N11.Analytic.injective_toE x hi⟩

private theorem coords_of_isConfiguration {Y : Fin 11 → Point} (h : IsConfiguration Y) :
    N11.OnSphere (coords Y) ∧ Function.Injective (coords Y) := by
  refine ⟨N11.Analytic.onSphere_of_norm _ (by rw [toE_coords]; exact h.1), fun i j hij => h.2 ?_⟩
  rw [← toE_coords Y]
  unfold N11.Analytic.toE
  rw [hij]

private theorem E_toE (x : Fin 11 → Fin 3 → ℝ) : E (N11.Analytic.toE x) = N11.energy x :=
  N11.Analytic.circ_energy_toE x

private theorem E_eq (Y : Fin 11 → Point) : E Y = N11.energy (coords Y) := by
  rw [← E_toE, toE_coords]

/-- The table `X₀` is the candidate of the proof. -/
private theorem X₀_eq (i : Fin 11) (k : Fin 3) : X₀ i k = N11.Xdec i k := by
  fin_cases i <;> fin_cases k <;> norm_num [X₀, N11.Xdec, N11.XdecZ]

/-- The orthogonal transformation with a given orthogonal matrix. -/
private def isometryOfMatrix (U : Matrix (Fin 3) (Fin 3) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ) : Point ≃ₗᵢ[ℝ] Point :=
  LinearIsometry.toLinearIsometryEquiv
    ⟨Matrix.toEuclideanLin U, fun v => by
      have h := N11.Analytic.dot_mulVec U hU v.ofLp v.ofLp
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      congr 1
      simpa [sq] using h⟩ rfl

private theorem isometryOfMatrix_apply (U : Matrix (Fin 3) (Fin 3) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin 3) ℝ) (v : Point) :
    isometryOfMatrix U hU v = WithLp.toLp 2 (U.mulVec v.ofLp) := rfl

private theorem congruent_of_coords {x : Fin 11 → Fin 3 → ℝ} {Y : Fin 11 → Point}
    (h : N11.Congruent x (coords Y)) : Congruent Y (N11.Analytic.toE x) := by
  obtain ⟨U, hU, σ, hY⟩ := h
  refine ⟨isometryOfMatrix U hU, σ, fun i => ?_⟩
  rw [isometryOfMatrix_apply]
  exact congrArg (WithLp.toLp 2) (hY i)

/-- Congruent configurations have the same energy. -/
private theorem E_eq_of_congruent {Y Z : Fin 11 → Point} (h : Congruent Y Z) : E Y = E Z := by
  obtain ⟨U, σ, hY⟩ := h
  have hd : ∀ i j, ‖Y i - Y j‖ = ‖Z (σ i) - Z (σ j)‖ := fun i j => by
    rw [hY i, hY j, ← map_sub, LinearIsometryEquiv.norm_map]
  simp only [E, hd]
  exact N11.Analytic.pairsum_comp_perm (fun i j => 1 / ‖Z i - Z j‖)
    (fun i j => by rw [norm_sub_rev]) (fun i => by simp) σ

/-- **The Thomson problem for 11 points.** There is a configuration `X` with the following
properties.

* `X` is a configuration of 11 distinct points on the unit sphere, every such configuration `Y`
  satisfies `E(X) ≤ E(Y)`, and equality holds exactly when `Y` arises from `X` by an orthogonal
  transformation and a relabelling of the points.
* Every coordinate `X i k` of `X` agrees with the entry `X₀ i k` of the table up to `10⁻¹⁰`.
  Here `i` runs through the labels `0, …, 10` of the points and `k` through the coordinates
  `0, 1, 2`.
* The minimal energy `E(X)` lies in the interval `(40.59644951, 40.59645051]`. -/
theorem thomson_11_points :
    ∃ X : Fin 11 → Point,
      IsUniqueMinimizer X ∧
      (∀ i k, |X i k - X₀ i k| ≤ 1 / 10 ^ 10) ∧
      40.59644951 < E X ∧ E X ≤ 40.59645051 := by
  -- The theorem in the coordinates of the proof (`Certificates/Theorem/T6A.lean`), for a
  -- configuration `x` with coordinates `Fin 11 → Fin 3 → ℝ`.
  obtain ⟨x, hs, hi, hdec, hlo, hhi, hmin⟩ : N11.Thomson11 := N11.T6A.thomson11
  refine ⟨N11.Analytic.toE x, ⟨isConfiguration_toE hs hi, fun Y hY => ?_⟩, fun i k => ?_, ?_, ?_⟩
  · -- minimality and the case of equality
    obtain ⟨hYs, hYi⟩ := coords_of_isConfiguration hY
    obtain ⟨hle, heq⟩ := hmin (coords Y) hYs hYi
    rw [E_toE, E_eq Y]
    refine ⟨hle, fun h => congruent_of_coords (heq h), fun h => ?_⟩
    rw [← E_eq Y, ← E_toE]
    exact E_eq_of_congruent h
  · -- the coordinates
    rw [X₀_eq]
    exact hdec i k
  · -- the lower bound of the minimal energy
    rw [E_toE]
    norm_num at hlo ⊢
    exact hlo
  · -- the upper bound of the minimal energy
    rw [E_toE]
    norm_num at hhi ⊢
    exact hhi

end Thomson11

/-- info: 'Thomson11.thomson_11_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Thomson11.thomson_11_points
