import Mathlib

/-!
# The Thomson problem for 11 points

The Thomson problem asks for the configurations of `N` points on the unit sphere of `ℝ³` that
minimize the Coulomb energy, the sum of the reciprocal distances over all pairs of points.
This file states its solution for `N = 11`: a minimizer exists, it is unique up to orthogonal
transformations and relabelling of the points, and its coordinates are given up to `10⁻¹⁰`.

All definitions needed to read the statement are included here, and Mathlib is the only import.
The same statement, with its proof, appears in `Showcase_WithProofs.lean`.
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

/-- A table of eleven points with 15 decimal places, which approximates the minimizer. Its entries
are exact rational numbers, not floating-point numbers.
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
  sorry

end Thomson11
